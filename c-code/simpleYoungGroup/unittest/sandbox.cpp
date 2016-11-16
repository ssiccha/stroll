//#define BOOST_TEST_DYN_LINK
#define BOOST_TEST_MODULE sandbox

#include <boost/test/unit_test.hpp>
#include <boost/function.hpp>
#include <iostream>
#include <iomanip>

#include <baseaction_neu.hpp>
#include <labelled_branching.hpp>
#include <boost/shared_ptr.hpp>

//#include <simpleYoungGroup/simpleLaddergameHomomorphisms.hpp>
//#include <Algorithms/algorithm_depthfirst_simple_laststep.hpp>
#include <simpleYoungGroup/function_builder_depthfirst_simple_lastfusing.hpp>
#include <simpleYoungGroup/laddergame_light.hpp>
#include <graphSpezial/calculate_complete_graph_group.hpp>

 

#define SINGLE
using namespace boost::unit_test;


template <class LABRA>
typename LABRA::GROUP_element_type findRightCosetRep(unsigned, typename LABRA::GROUP_element_type const& g);


BOOST_AUTO_TEST_CASE( smallest_right_coset_Representative )
{
    static unsigned const N =                       10;
//    static unsigned const S =                       N*(N-1)/2;
    static unsigned const GRAPHSIZE =               10;

    typedef calcGraphGroup<N>::LABRA                LABRA;
    typedef LABRA::GROUP_element_type               GRELM;
    typedef LABRA::SET_element_type                 SETELMNT;

    GRELM g("{(0,38,4,2,11,1)(3,35,10)(5,13,42)(6,18)(7,21)(8,28)(9,34)(12,39)(14,44)}");
    cout <<"       Kandidate is ";
    for ( unsigned i=0; i<GRAPHSIZE;++i) {
        if ( i != 0 )
            cout <<",";
        SETELMNT o(i);
        o = o<<g;
        cout <<std::setw(2)<<o.getit();
    }
    cout <<endl;

    g = findRightCosetRep<LABRA>(GRAPHSIZE,g);
    cout <<"Sorted Kandidate is ";
    for ( unsigned i=0; i<GRAPHSIZE;++i) {
        if ( i != 0 )
            cout <<",";
        SETELMNT o(i);
        o = o<<g;
        cout <<std::setw(2)<<o.getit();
    }
    cout <<endl;
}


#ifdef SINGLE
BOOST_AUTO_TEST_CASE( initialize_leiterspiel_light )
{

// INIT BEGIN //////////////////////////
    static unsigned const N =                       10;
    static unsigned const S =                       N*(N-1)/2;
    static unsigned const GRAPHSIZE =               15;

    typedef calcGraphGroup<N>::LABRA                LABRA;
    typedef LABRA::GROUP_element_type               GRELM;
//    typedef LABRA::SET_element_type                 SETELMNT;

    calcGraphGroup<N> groupGen;
    LABRA C = groupGen();

// INIT END //////////////////////////

    using laddergame::depthfirst::simple::laddergame_light;

    laddergame_light<LABRA> test(S,C);

    GRELM g1("{(0,1,2,4,11,38)(3,10,35)(5,13,42)(6,18)(7,21)(8,28)(9,34)(12,39)(14,44)}");
    GRELM g2 = g1;
    GRELM b;
    bool result = false;
    int counter = 0;
    while ( false == result ) {
        g2 = g2*b;
        g2 = findRightCosetRep<LABRA>(GRAPHSIZE,g2);
        b = GRELM();
        cout <<"Teste Kandidaten "<<g2<<endl; 
        result = test.IsSmallestOrbitRep(GRAPHSIZE,g2,b);
        cout <<"Ergebnis ist "<<result<<endl<<endl;
        counter++;
        if ( 100 == counter )
            break;
    }

}
#endif


template <class LABRA>
typename LABRA::GROUP_element_type findRightCosetRep(unsigned index, typename LABRA::GROUP_element_type const& g_) {

    typedef typename LABRA::GROUP_element_type      GRELM;
    typedef typename LABRA::SET_element_type        SETELM;
    GRELM g = g_;
    for (unsigned i=0; i<index; ++i) {
        unsigned k = i;
        for (unsigned j=i; j<index; ++j) {
            SETELM o1(k);
            SETELM o2(j);
            if ( o1<<g > o2<<g ) 
                k = j;
        }
        if ( i != k ) {
            GRELM c(laddergame::depthfirst::GetCycleInitString(i,k).c_str());
            g = ~c*g;
        }
    }
    return g;
}



