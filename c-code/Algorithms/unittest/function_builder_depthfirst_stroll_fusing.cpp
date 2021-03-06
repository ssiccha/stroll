//#define BOOST_TEST_DYN_LINK
#define BOOST_TEST_MODULE algorithm_depthfirst_stroll_fusing

#include <boost/test/unit_test.hpp>
#include <iostream>

#include <baseaction_neu.hpp>
#include <labelled_branching.hpp>

#include <boost/container/vector.hpp>
#include <boost/bind.hpp>

#include <simpleYoungGroup/function_builder_depthfirst_stroll_fusing.hpp>
#include <Algorithms/algorithm_depthfirst_stroll_fusing.hpp>

#include <simpleYoungGroup/storage.hpp>


// testet fusing orbits algorithmus
// zuerst werden die Funktionen für den Algorithmus gebaut
// dann wird am Beispiel eines Würfels mit gefärbten Ecken geprüft:
//
//            4__________5
//           /|         /|
//          0__________1 |
//          | |        | |
//          | |        | |
//          | 7________|_6
//          | /        | /
//          3/_________2/
//          
//             __________o
//           /|         /|
//          o__________/ |
//          | |        | |
//          | |        | |
//          | |________|_|
//          | /        | /
//          |/_________o/
//          
//          
// In diesem Fusingschritt soll die oben im Würfel mit Kreisen markierte Partition der Würfelecken berechnet werden.
// Damit ist die Partition gemeint, bei der die markierten Ecken eine Menge bilden und die unmarkierten Ecken eine 
// weitere Menge, so dass der obige Würfel der Partition {{0,2,5}{1,3,4,6,7}} entspricht.
// Diese Partition kann unter Verwendung eines Homomorphismus von Gruppenoperationen aus jeder der drei Partitionen
// {{0,2}{5}{1,3,4,6,7}}, {{0,5}{2}{1,3,4,6,7}}, {{2,5}{0}{1,3,4,6,7}} berechnet werden.
// Im Allgemeinen können diese Partition im Urbild in verschiedenen Bahnen liegen. Im Algorithmus ist eine ausgewählte
// Ursprungspartition {{0,2}{5}{1,3,4,6,7}} vorgegeben. Der Algorithmus soll nur diejenigen Ursprungspartitionen 
// betrachten, die in der selben Bahn liegen, wie die gegebene ausgewählte Ursprungspartition.
// Um zu verhindern, dass die obige Partition {{0,2,5}{1,3,4,6,7}} mehrfach erzeugt wird, soll der Algorithmus genau
// eine Partition aus diesen drei auswählen und die obige Partition nur aus dieser einen ausgewählten Partition
// konstruieren.
//
// Wenn die Partition, die konstruiert werden soll, sowieso nur aus einer einzigen Ursprungspartition konstruiert werden
// kann, so wird diese Partition vom Algorithmus auch in jedem Fall nur ein einziges mal erzeugt. Um Rechenzeit
// einzusparen sollen diese Situationen im Algorithmus erkannt werden. 
// Dies kann durch Überprüfung der Größe des Stabilisators erfolgen: Ist der Stabilisator der Ursprungspartition 
// identisch mit dem Stabilisator derjenigen Partition, die daraus konstruiert werden soll, so enthält die Bahn dieser 
// Partition kein weiteres Urbild.




using namespace boost::unit_test;


static unsigned const N = 8;

template <class LABRA>
void print(typename LABRA::GROUP_element_type g, unsigned n = 8);

template <class LABRA, bool IsResult>
void PrintResults(typename LABRA::GROUP_element_type& g, 
                  typename LABRA::GROUP_element_type& b );

template <class LABRA>
bool Canonizer(typename LABRA::GROUP_element_type const& g, LABRA const& C, LABRA& D );



template <class LABRA>
struct Variables {
    typedef typename LABRA::GROUP_element_type   GRELM;
    GRELM   e1;
    GRELM   e2;
    GRELM   b1;
    GRELM   b2;
    LABRA   C1;
    LABRA   C2;
};


template <class LABRA>
struct CheckResults {

    typedef typename LABRA::GROUP_element_type  GRELM;
    typedef typename LABRA::SET_element_type    SETELM;
    typedef void                                result_type;

    CheckResults(GRELM& _e1, GRELM& _b1, unsigned _x, unsigned _n);

    void operator()(GRELM const& e1, GRELM const& b1, LABRA const& );

    GRELM a2;
    GRELM e1;
    GRELM b1;
    unsigned x;
    unsigned n;
    static unsigned counter1;
};

template <class T> unsigned CheckResults<T>::counter1 = 0;





BOOST_AUTO_TEST_CASE( fusing_orbits_algorithm_depthfirst_stroll )
{

// INIT BEGIN //////////////////////////
    using boost::container::vector;

    typedef   baseAction<N>               ACTION;
    typedef   neu::labra<ACTION>          LABRA;
    typedef   LABRA::GROUP_element_type   GRELM;
    typedef   LABRA::SET_element_type     SETELM;

    vector<SETELM> set2(8);
    for (unsigned i=0; i<N; ++i)
      set2[i] = SETELM(i);

    LABRA group(set2);
// INIT END //////////////////////////


    using laddergame::depthfirst::stroll::fusing_algorithm;
    using laddergame::SimpleLaddergameHomomorphisms;
    using laddergame::depthfirst::stroll::fusing_algorithm_builder;


    typedef fusing_algorithm_builder<LABRA>         BUILDER;
    typedef BUILDER::Algorithm                      ALGORITHM;

    static unsigned const n = 5;
    static unsigned const x = 3;


    laddergame::depthfirst::storage<LABRA> var(group,group);

    var.Set_C1(group);
    var.Set_C2(group);
    var.Set_D1(group);
    var.Set_D2(group);
    GRELM& e1 = var.Get_e1();
    GRELM& b1 = var.Get_b1();
    LABRA& C1 = var.Get_C1();
    LABRA& C2 = var.Get_C2();


    GRELM stabElm1("2,1,5,6,3,0,4,7");
    group.sift(stabElm1);
    group.make_strong();
    BOOST_CHECK( 3 == group.size());


    BUILDER FktBuilder(x,n,var);


    //generate function to find the stabilizer and calculate the minimal orbit representative
    using boost::bind;
    using boost::ref;
    bool (*can)(GRELM const&, LABRA const&, LABRA&) = &Canonizer<LABRA>;
    BUILDER::CHECKCAN CheckCanonical = bind(can,_1,ref(group),_2);


    FktBuilder.Set_CheckCanonical(CheckCanonical);
    FktBuilder.Set_StepUsual(CheckResults<LABRA>(e1,b1,x,n));


//////////////// TESTS  ///////////////////////////

    {
        C2 = group;
        e1 = GRELM("0,2,5,7,3,4,6,1");

        CheckResults<LABRA>::counter1 = 0;

        ALGORITHM algo = FktBuilder();
        algo();

        BOOST_CHECK( 1 == CheckResults<LABRA>::counter1 );
    }

    {
        C2 = group;
        e1 = GRELM("0,5,2,7,3,4,6,1");
    
        CheckResults<LABRA>::counter1 = 0;

        ALGORITHM algo = FktBuilder();
        algo();

        BOOST_CHECK( 0 == CheckResults<LABRA>::counter1 );
    }
    {
        C2 = group;
        e1 = GRELM("2,5,0,7,3,4,6,1");
    
        CheckResults<LABRA>::counter1 = 0;

        ALGORITHM algo = FktBuilder();
        algo();

        BOOST_CHECK( 0 == CheckResults<LABRA>::counter1 );
    }
    {
        C2 = group;
        e1 = GRELM("2,5,0,7,3,4,6,1");
        C1 = C2;

        CheckResults<LABRA>::counter1 = 0;

        ALGORITHM algo = FktBuilder();
        algo();

        BOOST_CHECK( 1 == CheckResults<LABRA>::counter1 );
    }

}


template <class LABRA>
void print(typename LABRA::GROUP_element_type g, unsigned n = 8) {

    typedef typename LABRA::SET_element_type    omega;
    for (unsigned i=0; i<n; ++i) {
      omega o(i);
      o = o<<g;
      cout <<o.getit()<<" ";
    }
}


template <class LABRA, bool IsResult>
void PrintResults(typename LABRA::GROUP_element_type& g, 
                  typename LABRA::GROUP_element_type& b ) {
    if ( IsResult )
      std::cout <<"gleich : e1 = ";
    if ( !IsResult )
      std::cout <<"kleiner: e1 = ";
    print<LABRA>(g,3);
    cout <<" und g*b = ";
    print<LABRA>(g*b,3);
    cout <<std::endl;
}

    template <class LABRA>
    CheckResults<LABRA>::CheckResults(GRELM& _e1, GRELM& _b1, unsigned _x, unsigned _n) 
        :   e1(_e1)
        ,   b1(_b1) 
        ,   x(_x)
        ,   n(_n) {}


    template <class LABRA>
    void CheckResults<LABRA>::operator()(GRELM const& e2, GRELM const& b2, LABRA const& ) {

        //gebe Ergebnisse aus
        counter1++;
    }


template <class LABRA>
bool Canonizer(typename LABRA::GROUP_element_type const& g, LABRA const& C, LABRA& D ) {
    typedef typename LABRA::SET_element_type    SETELM;
    SETELM e0(0);
    SETELM e1(1);
    SETELM e2(2);
    SETELM e3(3);
    SETELM e4(4);
    SETELM e5(5);
    SETELM e6(6);
    SETELM e7(7);
//    GRELM stabElm1("2,1,5,6,3,0,4,7");
//    D.sift(stabElm1);
//    D.make_strong();
    D = C;

    if (  e0 == e0<<g && e2 == e1<<g && e5 == e2<<g ) 
      return true;
    if (  e0 == e1<<g && e2 == e0<<g && e5 == e2<<g ) 
      return true;

    return false;
}

