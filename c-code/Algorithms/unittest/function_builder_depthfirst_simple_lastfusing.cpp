//#define BOOST_TEST_DYN_LINK
#define BOOST_TEST_MODULE algorithm_depthfirst_simple_lastfusing

#include <boost/test/unit_test.hpp>
#include <iostream>

#include <baseaction_neu.hpp>
#include <labelled_branching.hpp>


#include <simpleYoungGroup/function_builder_depthfirst_simple_lastfusing.hpp>

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
//          | o________|_|
//          | /        | /
//          |/_________o/
//          
//          
// In diesem letzten Fusingschritt soll der Stabilisator zu einer gegebenen Partition berechnet werden. Die gegebene
// Partition ist im obigen Würfel dargestellt: Diese besteht aus den Ecken des Würfels, wobei die  mit Kreisen 
// markierten Würfelecken in einer anderen Teilmenge als die unmarkierten Ecken liegen. Der oben dargestellte Würfel
// entspricht daher der Partition {{0,2,5,7}{1,3,4,6}}.



using namespace boost::unit_test;


static unsigned const N = 8;



template <class LABRA>
void print(typename LABRA::GROUP_element_type g, unsigned n = 8);

template <class LABRA, bool IsResult>
void PrintResults(typename LABRA::GROUP_element_type& g, 
                  typename LABRA::GROUP_element_type& b );




BOOST_AUTO_TEST_CASE( lastfusing_algorithm_leiterspiel_light )
{
// INIT BEGIN //////////////////////////
    using boost::container::vector;

    typedef   baseAction<N>               ACTION;
    typedef   neu::labra<ACTION>          LABRA;
    typedef   LABRA::GROUP_element_type   GRELM;
    typedef   LABRA::SET_element_type     SETELM;

    SETELM set2[8];
    for (unsigned i=0; i<N; ++i)
      set2[i] = SETELM(i);

    swap(set2[0],set2[7]);

    LABRA group(set2);
// INIT END //////////////////////////

    static unsigned const n = 3;
    static unsigned const x = 4;

    using laddergame::depthfirst::simple::lastFusingStep_algorithm;
    using laddergame::depthfirst::extendGroup;
    using laddergame::SimpleLaddergameHomomorphisms;
    using laddergame::depthfirst::CompareYoungGroup;
    using laddergame::depthfirst::simple::lastfusing_algorithm_builder;


    typedef lastfusing_algorithm_builder<LABRA>             BUILDER;
    typedef BUILDER::Algorithm                              ALGORITHM;


    laddergame::depthfirst::storage<LABRA> var(group,group);

    GRELM& a1 = var.Get_a1();
    GRELM& a2 = var.Get_a2();
    GRELM& b1 = var.Get_b1();
    GRELM& b2 = var.Get_b2();
    LABRA& C2 = var.Get_C2();

    GRELM stabElm1("2,1,5,6,3,0,4,7");
    group.sift(stabElm1);
    group.make_strong();
    BOOST_CHECK_EQUAL( 3, group.size());

    C2 = group;

    BUILDER Builder(x,n,var);



//////////////// TESTS  ///////////////////////////

    {
        a2 = GRELM("0,2,5,7,3,4,6,1");
        b1 = GRELM("1,5,6,2,0,4,7,3");

        ALGORITHM algo = Builder();
        algo();

        BOOST_CHECK( b2 == b1 );
        BOOST_CHECK_EQUAL( 3 , C2.size() );
    }

    {
        a2 = GRELM("0,2,5,7,3,4,6,1");
        b1 = GRELM("2,6,7,3,1,5,4,0");
        b2 = GRELM("1,5,6,2,0,4,7,3");
        b1 = b2*b1;

        ALGORITHM algo = Builder();
        algo();

        BOOST_CHECK_EQUAL( 12 , C2.size() );
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



