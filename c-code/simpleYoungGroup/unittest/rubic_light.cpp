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

char setColor(unsigned color) {
        if ( 1 <= color && 9 >= color )
            return 'b';
        else if ( 10 <= color && 18 >= color )
            return 'e';
        else if ( 19 <= color && 27 >= color )
            return 'r';
        else if ( 28 <= color && 36 >= color )
            return 'g';
        else if ( 37 <= color && 45 >= color )
            return 't';
        else
            return 'c';
}


BOOST_AUTO_TEST_CASE( initialize_leiterspiel_light )
{
    using std::cout;
// INIT BEGIN //////////////////////////
    static unsigned const N =                       54;

    typedef calcGraphGroup<N>::LABRA                LABRA;
    typedef LABRA::GROUP_element_type               GRELM;
    typedef LABRA::SET_element_type                 SETELMNT;

    boost::container::vector<SETELMNT> Omega;
    for (unsigned i=0; i<N; ++i)
        Omega.emplace_back(i);

    LABRA C(Omega);
    GRELM g1("{(3,12,21,30)(6,15,24,33)(9,18,27,36)(46,52,0,48)(49,53,51,47)}");
    GRELM g2("{(1,37,27,46)(2,38,26,47)(3,39,25,48)(34,28,30,36)(35,31,29,33)}");
    GRELM g3("{(1,7,9,3)(2,4,8,6)(10,52,36,39)(11,49,35,42)(12,46,34,45)}");
    GRELM g4("{(1,10,19,28)(4,13,22,31)(7,16,25,34)(39,45,43,37)(42,44,40,38)}");
    GRELM g5("{(7,43,21,52)(8,44,20,53)(9,45,19,0)(10,16,18,12)(11,13,17,15)}");
    C.sift(g1);
    C.sift(g2);
    C.sift(g3);
    C.sift(g4);
    C.sift(g5);
    C.make_strong();

    unsigned visible[] = {1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,37,38,39,40,41,42,43,44,45};
    unsigned cross[] = {2,4,5,6,8,11,14,32,35,41,42,49,50};
    unsigned third[] = {0,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,37,40,43,48,51};
    bool obere2drittel[54];
    for (unsigned i=0; i<54;++i)
        obere2drittel[i] = 1;
    for (unsigned i=0; i<21;++i)
        obere2drittel[third[i]] = 0;
    bool kreuz[54];
    for (unsigned i=0; i<54;++i)
        kreuz[i] = 0;
    for (unsigned i=0; i<13;++i)
        kreuz[cross[i]] = 1;
    bool sichtbar[54];
    for (unsigned i=0; i<54;++i)
        sichtbar[i] = 0;
    for (unsigned i=0; i<27;++i)
        sichtbar[visible[i]] = 1;

    cout <<"\n Die Gruppe hat die Größe "<<std::fixed<<C.size()<<endl<<endl;
    cout <<"\n Die volle Gruppe hat die Größe "<<std::fixed<<C.size()*6*4<<endl<<endl;

    GRELM random = C.get_rand();
    for ( unsigned i=0;i<54;++i ) {
        if ( i && i<46 && ( i < 19 || i > 36 ))
            cout <<std::setw(3)<<i;
    }
    std::cout <<endl;
    for ( unsigned i=0;i<54;++i ) {
        SETELMNT o(i);
        o = o<<random;
        if ( i && i<46 && ( i < 19 || i > 36 ))
            cout <<std::setw(3)<<o.getit();
    }
    cout <<endl;
    for ( unsigned i=0;i<54;++i ) {
        SETELMNT o(i);
        o = o<<random;
        unsigned p = o.getit();
        if ( 0 == sichtbar[i] )
            continue;
        cout <<"  "<<setColor(p);
    }
    cout <<endl;
    for ( unsigned i=0;i<54;++i ) {
        SETELMNT o(i);
        o = o<<random;
        unsigned p = o.getit();
        if ( 0 == sichtbar[i] )
            continue;
        else if ( 0 == obere2drittel[p] )
            cout <<"  X";
        else
            cout <<"  "<<setColor(p);
    }
    cout <<endl;
    for ( unsigned i=0;i<54;++i ) {
        SETELMNT o(i);
        o = o<<random;
        unsigned p = o.getit();
        if ( 0 == sichtbar[i] )
            continue;
        else if ( 0 == kreuz[p] )
            cout <<"  X";
        else
            cout <<"  "<<setColor(p);
    }
    cout <<endl;
    cout <<endl;
// INIT END //////////////////////////
/*
    using laddergame::depthfirst::simple::laddergame_light;

    laddergame_light<LABRA> test(S,C);

    GRELM g("{(4,6,9,18)(5,7,12)(8,15)(10,20)}");
    bool result = test.IsSmallestOrbitRep(GRAPHSIZE,g);
    cout <<"Ergebnis ist "<<result<<endl;
*/

}






