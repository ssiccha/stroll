//#define BOOST_TEST_DYN_LINK
#define BOOST_TEST_MODULE algorithm_depthfirst_stroll_splitting

#include <boost/test/unit_test.hpp>
#include <iostream>

#include <baseaction_neu.hpp>
#include <labelled_branching.hpp>

#include <simpleYoungGroup/function_builder_depthfirst_stroll_splitting.hpp>
#include <Algorithms/algorithm_depthfirst_stroll_splitting.hpp>

#include <simpleYoungGroup/storage.hpp>

// testet splitting orbits algorithmus
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
//            x__________x
//           /|         /|
//          o__________/ |
//          | |        | |
//          | |        | |
//          | x________|_|
//          | /        | /
//          x/_________o/
//          
//          
// Dieser Splittingschritt ist Teil eines größeren Algorithmus, bei dem der Stabilisator der Partition 
// {{0,2,3,4,5,7}{1,6}} berechnet wird.
// Die Ecken mit den Kreisen sind vorgegeben und werden nicht verändert (Partition {{0,2}{1,3,4,5,6,7}}).
// Im Splittingschritt berechnet die Funktion VarphiInv die entsprechenden Ecken, die mit einem x, aber 
// noch nicht mit einem Kreis markiert sind ( die Ecken {3,4,5,7}).
// Im Splittingschritt werden dann die vier Partitionen:
// {{0,2}{3}{1,4,5,6,7}}
// {{0,2}{4}{1,3,5,6,7}}
// {{0,2}{5}{1,3,4,6,7}}
// {{0,2}{7}{1,3,4,5,6}}
// konstruiert und einzeln mit der Partition {{0,2}{5}{1,3,4,6,7}} verglichen.
// Das Ergebnis wir im Unittest überprüft:
// Zwei der Partitionen liegen in der selben Bahn unter dem Stabilisator der Partition {{0,2}{1,3,4,5,6,7}} (step1).
// Zwei weitere Partitionen liegen nicht in der selben Bahn unter dem Stabilisator, sind aber kleiner, als
// die vorgegebene Partition (step2).




using namespace boost::unit_test;


static unsigned const N = 8;


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

    CheckResults(bool _IsResult, GRELM& _a1, GRELM& _e2, GRELM& _b2, unsigned _x, unsigned _n);

    void operator()(GRELM const& e1, GRELM const& b1, LABRA const& D1 );

    bool IsResult;
    GRELM& a1;
    GRELM& e2;
    GRELM& b2;
    unsigned x;
    unsigned n;
    static unsigned counter1;
    static unsigned counter2; 
};

template <class T> unsigned CheckResults<T>::counter1 = 0;
template <class T> unsigned CheckResults<T>::counter2 = 0;





BOOST_AUTO_TEST_CASE( splitting_orbits_algorithm_depthfirst_stroll )
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


    using laddergame::depthfirst::stroll::splitting_algorithm;
    using laddergame::SimpleLaddergameHomomorphisms;
    using laddergame::depthfirst::stroll::splitting_algorithm_builder;


    typedef splitting_algorithm_builder<LABRA>      BUILDER;
    typedef BUILDER::Algorithm                      Algorithm;

    static unsigned const n = 5;
    static unsigned const x = 3;


    laddergame::depthfirst::storage<LABRA> var(group,group);

    GRELM& e2 = var.Get_e2();
    GRELM& a1 = var.Get_a1();
    GRELM& b2 = var.Get_b2();
    LABRA& C2 = var.Get_C2();

    GRELM stabElm1("2,3,0,1,6,7,4,5");
    group.sift(stabElm1);
    group.make_strong();
    BOOST_CHECK_EQUAL( 2, group.size());

    C2 = group;

    BUILDER FktBuilder(x,n,var);

    FktBuilder.Set_StepUsual( CheckResults<LABRA>(true,a1,e2,b2,x,n) );
    FktBuilder.Set_StepSpezial( CheckResults<LABRA>(false,a1,e2,b2,x,n) );

    {
        a1 = GRELM("0,2,5,7,3,4,6,1");
        e2 = GRELM("0,2,7,5,3,4,6,1");

        CheckResults<LABRA>::counter1 = 0;
        CheckResults<LABRA>::counter2 = 0;


        Algorithm algo = FktBuilder();
        algo();

        BOOST_CHECK( 2 == CheckResults<LABRA>::counter1 );
        BOOST_CHECK( 2 == CheckResults<LABRA>::counter2 );
    }

    {
        a1 = GRELM("0,2,5,7,3,4,6,1");
        e2 = GRELM("7,5,2,0,3,4,6,1");
        b2 = GRELM("7,6,5,4,3,2,1,0");

        CheckResults<LABRA>::counter1 = 0;
        CheckResults<LABRA>::counter2 = 0;

        Algorithm algo = FktBuilder();
        algo();

        BOOST_CHECK( 2 == CheckResults<LABRA>::counter1 );
        BOOST_CHECK( 2 == CheckResults<LABRA>::counter2 );
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
    CheckResults<LABRA>::CheckResults(bool _IsResult, GRELM& _a1, GRELM& _e2, GRELM& _b2, unsigned _x, unsigned _n) 
        :   IsResult(_IsResult)
        ,   a1(_a1)
        ,   e2(_e2)
        ,   b2(_b2) 
        ,   x(_x)
        ,   n(_n) {}


    template <class LABRA>
    void CheckResults<LABRA>::operator()(GRELM const& e1, GRELM const& b1, LABRA const& D1 ) {
/*
        //gebe Ergebnisse aus
        if ( IsResult )
          PrintResults<LABRA,true>(e1,b1);
        else
          PrintResults<LABRA,false>(e1,b1);
*/
        //check e1*b1 = a1
        if ( IsResult ) {
            SETELM omega1(x-1);
            SETELM omega2(x-1);
            BOOST_CHECK( omega1<<e1*b1 == omega2<<a1 );
            counter1++;
        }
        else {
            SETELM omega1(x-1);
            SETELM omega2(x-1);
            BOOST_CHECK( omega1<<e1*b1 < omega2<<a1 );
            counter2++;
        }
        for (unsigned i=0; i<x-1;++i) {
            SETELM omega1(i);
            SETELM omega2(i);
            BOOST_CHECK( omega1<<e1 == omega2<<e2 );
        }
        for (unsigned i=0; i<N;++i) {
            SETELM omega1(i);
            SETELM omega2(x-1);
            if ( omega1<<e2 == omega2<<e1 )
                BOOST_CHECK( i <= n );
        }
    }


