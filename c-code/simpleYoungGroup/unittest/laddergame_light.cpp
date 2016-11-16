//#define BOOST_TEST_DYN_LINK
#define BOOST_TEST_MODULE laddergame_light

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

 
using namespace boost::unit_test;

#ifndef  GRAPHSIZE 
#define GRAPHSIZE 4
#endif
#define TREE
#define SINGLE

template <class LABRA, unsigned N>
struct konstructor {
    typedef typename LABRA::GROUP_element_type GRELM;
    typedef boost::function<bool(unsigned,GRELM const&)> CANTEST;
    static unsigned const S =                       N*(N-1)/2;
    konstructor(CANTEST const& c) : test(c) {}
    void operator()();
    CANTEST test;
};


#ifdef SINGLE
BOOST_AUTO_TEST_CASE( initialize_leiterspiel_light )
{

// INIT BEGIN //////////////////////////
    static unsigned const N =                       GRAPHSIZE < 7? 7: GRAPHSIZE;
    static unsigned const S =                       N*(N-1)/2;

    typedef calcGraphGroup<N>::LABRA                LABRA;
    typedef LABRA::GROUP_element_type               GRELM;
//    typedef LABRA::SET_element_type                 SETELMNT;

    calcGraphGroup<N> groupGen;
    LABRA C = groupGen();

// INIT END //////////////////////////

    using laddergame::depthfirst::simple::laddergame_light;

    laddergame_light<LABRA> test(S,C);

    GRELM g("{(4,6,9,18)(5,7,12)(8,15)(10,20)}");
    bool result = test.IsSmallestOrbitRep(GRAPHSIZE,g);
    cout <<"Ergebnis ist "<<result<<endl;


}
#endif


#ifdef TREE
BOOST_AUTO_TEST_CASE( pure_simple_laddergame_test ) {

    static unsigned const N =                       GRAPHSIZE;
    static unsigned const S =                       N*(N-1)/2;

    using laddergame::depthfirst::simple::laddergame_light;
    using boost::bind;


    typedef calcGraphGroup<N>::LABRA                LABRA;
    typedef laddergame_light<LABRA>                 LADDERGAME;

    calcGraphGroup<N> groupGen;
    LABRA C = groupGen();
    LADDERGAME LadderGame(S,C);

    konstructor<LABRA,N> graphBuilder(bind(&LADDERGAME::IsSmallestOrbitRep,&LadderGame,_1,_2));

    graphBuilder();

}
#endif




template <class LABRA, unsigned N>
void konstructor<LABRA,N>::operator()() {

    unsigned counter2 = 0;
    unsigned counter1[S+1];
    for ( unsigned i=0; i<=S; ++i)
      counter1[i] = 0;
    counter1[0] = 1;
    counter2 = 1;
    cout <<"*";


    unsigned points[S];
    for (unsigned i=0; i<S; ++i)
      points[i] = i;
    unsigned perm[S+1];
    for (unsigned i=0; i<=S; ++i)
      perm[i] = i;



    //calculate all graphs
    unsigned i = 0;
    while ( S != perm[0] ) { 
      if ( S == perm[i] || i == S ) {
//      if ( S == perm[i] || i == 11 ) {
        --i;
        std::swap(points[i],points[perm[i]]);
        ++perm[i];
      }
      else {
        std::swap(points[i],points[perm[i]]);
        perm[i+1] = perm[i]+1;
        GRELM g(points);
        //////////////////////////////////////
        bool result = test(i+1,g);
        //////////////////////////////////////
        if ( false == result ) {
          std::swap(points[i],points[perm[i]]);
          ++perm[i];
          continue;
        }
        else {

            if ( 0 == counter2%5 ) 
              cout <<" ";
            if ( 0 == counter2%10 ) 
              cout <<" ";
            if ( 0 == counter2%50 ) 
              cout <<std::setw(10)<<counter2<<endl;
            if ( 0 == counter2%1000 )
              cout <<endl; 
            if ( 0 == counter2%500 ) 
              cout <<endl;
            if ( 0 == counter2%250 ) 
              cout <<endl;
            if ( 0 == counter2%10000 ) 
              cout <<"last Element was "<<GRELM(points)<<" in "<<i+1<<" points"<<endl<<endl;

            counter2++;
            counter1[i+1]++;

            cout <<"*"<<std::flush;

            ++i;
        }
      }
    }

    cout <<endl;


    cout <<"Anzahl der Konstruierten Graphen auf "<<N<<" Knoten: "<<counter2<<endl;
    for (unsigned i=0; i<S+1; ++i)
      cout <<"Anzahl der Graphen mit "<<std::setw(2)<<i<<" Kanten ist "<<counter1[i]<<endl;
    cout <<endl;
    long unsigned countall = 0;
    for (unsigned i=0; i<S+1; ++i)
      countall += counter1[i];
    cout <<endl<<"gesamte Anzahl aller erzeugten Graphen ist "<<countall<<endl;

    long graph[14] = {1, 1, 2, 4, 11, 34, 156, 1044, 12346, 274668, 12005168, 1018997864, 165091172592, 50502031367952};
    if ( N < 14 )
      BOOST_CHECK_EQUAL(countall,graph[N]);
    else {
      cout <<"Unit Test ist dafür noch nicht ausgebaut"<<endl;
      BOOST_CHECK_EQUAL(countall, 0);
    }
}

