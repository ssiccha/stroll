//#define BOOST_TEST_DYN_LINK
#define BOOST_TEST_MODULE algorithm_depthfirst_simple_fusing

#include <boost/test/unit_test.hpp>
#include <iostream>

#include <baseaction_neu.hpp>
#include <labelled_branching.hpp>

#include <boost/container/vector.hpp>

#include <younggroupmethods2/findOrbitRepConj_store.hpp>
#include <younggroupmethods2/compare.hpp>

#include <simpleYoungGroup/simpleLaddergameHomomorphisms.hpp>
//#include <simpleYoungGroup/storage.hpp>

#include <Algorithms/algorithm_depthfirst_simple_fusing.hpp>


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
// Diese Partition kann aus jeder der drei Partitionen berechnet werden, bei der genau eine der drei mit Kreisen 
// markierten Ecken anders markiert ist, das heißt eine weitere Menge der Partition bildet.
// Im Allgemeinen können diese Partition im Urbild in verschiedenen Bahnen liegen. Im Algorithmus ist eine ausgewählte
// Ursprungspartition {{0,2}{5}{1,3,4,6,7}} vorgegeben. Der Algorithmus soll nur diejenigen Ursprungspartitionen 
// betrachten, die in der selben Bahn liegen, wie die gegebene ausgewählte Ursprungspartition.
// In diesem Beispiel handelt es sich dabei um die drei Partitionen {{0,2}{5}{1,3,4,5,6}}, {{0,5}{2}{1,3,4,5,6} 
// und  {{0,5}{0}{1,3,4,5,6}.
// Um zu verhindern, dass die obige Partition {{0,2,5}{1,3,4,6,7}} mehrfach erzeugt wird, soll der Algorithmus genau
// eine Partition aus diesen drei auswählen und die obige Partition nur aus dieser einen ausgewählten Partition
// konstruieren.
//
// Wenn die Partition, die konstruiert werden soll, nur aus genau einer Partition konstruiert werden kann, so muss 
// der Algorithmus keine Auswahl mehr treffen. Um Rechenzeit einzusparen sollen diese Situationen im Algorithmus
// erkannt werden. 
// Dies kann durch Überprüfung der Größe des Stabilisators erfolgen: Ist der Stabilisator der Ursprungspartition 
// identisch mit dem Stabilisator derjenigen Partition, die daraus konstruiert werden soll, so enthält die Bahn dieser 
// Partition kein weiteres Urbild.




using namespace boost::unit_test;


static unsigned const N = 8;

template <class T>
bool ReturnTrue(T const& ) { return true; }


template <class LABRA>
void print(typename LABRA::GROUP_element_type g, unsigned n = 8);

template <class LABRA, bool IsResult>
void PrintResults(typename LABRA::GROUP_element_type& g, 
                  typename LABRA::GROUP_element_type& b );


template <class LABRA>
struct CheckResults {

    typedef typename LABRA::GROUP_element_type  GRELM;
    typedef typename LABRA::SET_element_type    SETELM;
    typedef void                                result_type;

    CheckResults(GRELM& _e1, GRELM& _b1, unsigned _x, unsigned _n);

    void operator()(GRELM& e1, GRELM& b1 );

//    GRELM a2;
    GRELM& e1;
    GRELM& b1;
    unsigned x;
    unsigned n;
    static unsigned counter1;
};

template <class T> unsigned CheckResults<T>::counter1 = 0;





BOOST_AUTO_TEST_CASE( fusing_orbits_algorithm_leiterspiel_light )
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

    static unsigned const n = 5;
    static unsigned const x = 3;

    using laddergame::depthfirst::simple::fusing_algorithm;
    using laddergame::SimpleLaddergameHomomorphisms;
    using laddergame::identity_function;
    using laddergame::depthfirst::findOrbitRepConjStore;
    using laddergame::depthfirst::CompareYoungGroup;
//    using laddergame::depthfirst::simple::storage;

    typedef SimpleLaddergameHomomorphisms<LABRA>    SQUARE;
    typedef fusing_algorithm<SQUARE>                ALGORITHM;



    ALGORITHM::VARPHIHOM VarphiHom = identity_function<GRELM>;


    SETELM omega(x-1);
    //index bezieht sich auf Leiterstufe
    unsigned index = x*2-1;


    //generate function to calculate the minimal orbit representative
    findOrbitRepConjStore<LABRA,true> findIt(omega);
    ALGORITHM::CANFKTCONJ FindOrbitRepConjugate = findIt;


    //generate descriptions for young groups
    vector<int> vint;
    vector<SETELM> vset;
    for (unsigned i=0; i<=index/2;++i) {
        vset.emplace_back(i);
        vint.push_back(0);
    }
    vint.back() = 1;

    //generate coset comparison function
    CompareYoungGroup<LABRA> cmpyg1(vset,vint);
    ALGORITHM::CMPFKT SmallerOrEqual = cmpyg1;



    GRELM stabElm1("2,1,5,6,3,0,4,7");
    group.sift(stabElm1);
    group.make_strong();
    BOOST_CHECK( 3 == group.size());


    GRELM e1,e2,b1,b2;
    LABRA C1(set2);
    LABRA C2(set2);


    ALGORITHM::Variables var = {e1,e2,b1,b2,C1,C2};

    ALGORITHM::STEPFKT NextStep = CheckResults<LABRA>(e1,b1,x,n);
    ALGORITHM::Functions f = {VarphiHom, FindOrbitRepConjugate, SmallerOrEqual, NextStep};



//////////////// TESTS  ///////////////////////////
    {
        C2 = group;
        e1 = GRELM("0,2,5,7,3,4,6,1");

        CheckResults<LABRA>::counter1 = 0;

        ALGORITHM algo;
        algo(var,f);


        BOOST_CHECK( 1 == CheckResults<LABRA>::counter1 );
    }

    {
        C2 = group;
        e1 = GRELM("0,5,2,7,3,4,6,1");

        CheckResults<LABRA>::counter1 = 0;

        ALGORITHM algo;
        algo(var,f);

        BOOST_CHECK( 0 == CheckResults<LABRA>::counter1 );
    }
    {
        C2 = group;
        e1 = GRELM("2,5,0,7,3,4,6,1");

        CheckResults<LABRA>::counter1 = 0;

        ALGORITHM algo;
        algo(var,f);

        BOOST_CHECK( 0 == CheckResults<LABRA>::counter1 );
    }
    {
        C2 = group;
        e1 = GRELM("2,5,0,7,3,4,6,1");
        C1 = C2;

        CheckResults<LABRA>::counter1 = 0;

        ALGORITHM algo;
        algo(var,f);

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
    void CheckResults<LABRA>::operator()(GRELM& e2, GRELM& b2 ) {

        //gebe Ergebnisse aus
        counter1++;
    }


