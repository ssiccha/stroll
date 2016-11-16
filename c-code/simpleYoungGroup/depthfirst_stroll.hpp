#ifndef LADDER_ALGORITHM_DEPTHFIRST_STROLL
#define LADDER_ALGORITHM_DEPTHFIRST_STROLL

#include <iostream>
#include <boost/bind.hpp>
#include <boost/function.hpp>
#include <boost/shared_ptr.hpp>
#include <boost/scoped_ptr.hpp>
#include <boost/functional/value_factory.hpp>
#include <boost/container/vector.hpp>


#include <simpleYoungGroup/function_builder_depthfirst_stroll_splitting.hpp>
#include <simpleYoungGroup/function_builder_depthfirst_stroll_fusing.hpp>
#include <simpleYoungGroup/function_builder_depthfirst_simple_lastfusing.hpp>
#include <simpleYoungGroup/stair_connector.hpp>
#include <simpleYoungGroup/storage.hpp>
#include <younggroupmethods2/redustab.hpp>
#include <younggroupmethods2/findOrbitRep.hpp>
#include <loadBalance/stupid_load_balancer.hpp>
#include <younggroupmethods2/findOrbitRep.hpp>


namespace laddergame {

    namespace depthfirst {

        namespace stroll {

            template <class LABRA>
            void printAsPartition(typename LABRA::GROUP_element_type const& g, unsigned i) {
                for (unsigned j=0; j!=i; ++j) {
                    typename LABRA::SET_element_type omega(j);
                    omega = omega<<g;   
                    if ( 0 != j )
                        std::cout <<","<<std::setw(2)<<omega.getit();
                    else
                        std::cout <<std::setw(2)<<omega.getit();
                }
            }


            template <class _LABRA>
            struct OrbitTest {

                typedef _LABRA                                                  LABRA;
                typedef typename LABRA::SET_element_type                        SETELM;
                typedef typename LABRA::GROUP_element_type                      GRELM;

                OrbitTest(unsigned x, LABRA const& _C, GRELM const& b, GRELM const& a) 
                    : omega(x), C(_C), b2(b), a1(a) {}

                bool operator()(GRELM const& e1, GRELM const& b1) { 
                    unsigned debug = 0;
                    GRELM c = findOrbitRepresentative<LABRA>(C,omega,e1*b1*b2);
                    if ( 0 != debug ) {
                        cout <<"In Test Funktion"<<endl;
                        cout <<"a1 = "<<a1<<endl;
                        cout <<"b2 = "<<b2<<endl;
                        cout <<"b1 = "<<b1<<endl;
                        cout <<"c = "<<c<<endl;
                        cout <<"e1 = "<<e1<<endl;
                        cout <<"e1*b1 = "<<GRELM(e1*b1)<<endl;
                        cout <<"e1*b1*b2 = "<<GRELM(e1*b1*b2)<<endl;
                        cout <<"e1*b1*b2*c = "<<GRELM(e1*b1*b2*c)<<endl;
                        if ( debug == 2 )
                            cout <<"Labra = "<<C<<endl;
                    }
                    SETELM elm1 = omega<<a1;
                    SETELM elm2 = omega<<e1*b1*b2*c;
                    if ( elm2 != elm1 )
                        return false;
                    return true;
                }

                SETELM omega;
                LABRA const& C;
                GRELM const& b2;
                GRELM const& a1;
            };


            template <class _LABRA>
            class depthfirst_stroll {

              public:

                typedef _LABRA                                                  LABRA;
                typedef typename LABRA::GROUP_element_type                      GRELM;
                typedef boost::shared_ptr<LABRA>                                PLABRA;
                typedef storage<LABRA>                                          STORAGE;
                typedef boost::shared_ptr<depthfirst_stroll>                    LADDER;
                typedef simple::lastfusing_algorithm_builder<LABRA>             LASTBUILD;
                typedef splitting_algorithm_builder<LABRA>                      SPLITBUILD;
                typedef fusing_algorithm_builder<LABRA>                         FUSEBUILD;
                typedef stair_connector<LABRA>                                  CONNECTOR;
                typedef typename SPLITBUILD::TESTFKT                            TESTFKT; 
                typedef boost::container::vector<TESTFKT>                       TESTARRAY;
                typedef boost::container::vector<TESTARRAY>                     TESTMATRIX;
                typedef boost::container::vector<PLABRA>                        STABILIZERS;
                typedef boost::container::vector<STABILIZERS>                   STABMATRIX;
                
                typedef bool                                                    result_type;

                depthfirst_stroll(unsigned, LABRA const&, unsigned debug = 0);

                bool IsSmallestOrbitRep(unsigned, GRELM const& );
                bool IsSmallestOrbitRep(unsigned, GRELM const&, GRELM& c );
                bool IsSmallestOrbitRep(unsigned, GRELM const&, TESTARRAY& );
                bool IsSmallestOrbitRep(unsigned, GRELM const&, LABRA& );
                bool IsSmallestOrbitRep(unsigned, GRELM const&, GRELM&, LABRA& );
                bool IsSmallestOrbitRep(unsigned, GRELM const&, TESTARRAY&, LABRA& );
                bool IsSmallestOrbitRep(unsigned, GRELM const&, TESTARRAY& tests, GRELM& c );
                bool IsSmallestOrbitRep(unsigned, GRELM const&, TESTARRAY& tests, GRELM& c, LABRA& );

              private:


                inline void SmallStep(unsigned, GRELM const&, GRELM const&, LABRA const&);
                inline void SetcanElmnt(GRELM const& b1) { canonizing_elm = b1; result = false; }

                boost::container::vector<STORAGE>       speicher;

                STABMATRIX                              stabMatrix;
                STABILIZERS                             stabArray;
                boost::container::vector<FUSEBUILD>     fuseBuild;
                boost::container::vector<SPLITBUILD>    splitBuild;
                boost::container::vector<LASTBUILD>     lastbuild;
                TESTMATRIX                              CanonizerTests;
                TESTARRAY                               NoTestTests;
                LADDER                                  ladder;

                unsigned    max;
                unsigned    debug;
                bool        result;
                const bool  trueValue;
                GRELM       canonizing_elm;

            };


            template <class LABRA>
            bool canonizer(  unsigned level, 
                                typename LABRA::GROUP_element_type const& candidate, 
                                LABRA const& B, 
                                typename LABRA::GROUP_element_type& canonizing_elm, 
                                LABRA& stab,
                                typename depthfirst_stroll<LABRA>::TESTARRAY& tests);


            template <class LABRA>
            bool depthfirst_stroll<LABRA>::IsSmallestOrbitRep(unsigned _s, GRELM const& g, TESTARRAY& tests, GRELM& c, LABRA& S ) {

                typedef typename LABRA::SET_element_type    SETELM;
                using laddergame::depthfirst::ReduStab;
                using laddergame::depthfirst::findOrbitRepresentative;
                //this is necessary, because some tests depend on this value
                result = true;
                if ( _s > max ) {
                    std::cerr <<" canonizing laddergame light is too small for this work"<<std::endl;
                    exit(-1);
                }
/*
                else if ( 1 == stabArray[0]->size() ) {
                    c = GRELM();
                    S = *stabArray[0];
                    return true;
                }
*/
                else if ( 0 == _s )
                    return true;
                else if ( 1 == _s ) {
                    c = GRELM();
                    if ( false == tests[0](g,c) )
                        return true;
                    SETELM omega(0);
                    c = findOrbitRepresentative(*stabArray[0],omega,g);
                    if ( omega<<g*c != omega<<g )
                        return false;
                    *stabArray[1] = *stabArray[0];
                    ReduStab(g,omega,*stabArray[1]);
                    *stabMatrix[0][0] = *stabArray[1];
                    S = *stabArray[1];
                    return true;
                }
                else if ( _s < max )
                    return ladder->IsSmallestOrbitRep(_s,g,tests,c,S);
                //now _s == max
                else {
                    //make a recursive call
                    if ( false == ladder->IsSmallestOrbitRep(_s-1,g,tests,c,S) )
                        return false;
                    //calculate stabilizers
                    {   
//                        cout <<"Stabilisator von "<<_s-1<<" Punkten ist "<<S.size()<<endl<<endl;
                        //copy stabilizer from recursive call
                        for (unsigned i=0; i<2*max-2; ++i)
                            *stabArray[i] = *ladder->stabArray[i];
                        //calculate the next stabilizer
                        *stabArray[2*max-2] = *stabArray[2*max-3];
                        SETELM omega(_s-1);
                        ReduStab(g,omega,*stabArray[2*max-2]);
                        //initialize next stabilizer with the known subgroup
                        *stabArray[2*max-1] = *stabArray[2*max-2];
//                        cout <<"Stabilisator von "<<_s-1<<"+1 Punkten ist "<<stabArray[2*max-2]->size()<<endl<<endl;
                    }
                    {
                        //initialize stabilizer matrix
                        for (unsigned i=0; i<max-1; ++i) 
                            for (unsigned j=0; j<=i; ++j) 
                                *stabMatrix[i][j] = *ladder->stabMatrix[i][j];
                    }
                    speicher[0].Set_a2(g);
                    speicher[2*max-2].Set_b2(GRELM());
                    //this is necessary, because the groups (C_1,...,C_n) might have changed
                    for(unsigned i=0; i<max-2; ++i)
                      fuseBuild[i].Build_FindOrbitRepConj();
                    for(unsigned i=0; i<max; ++i) {
                      splitBuild[i].Build_FindOrbitRep1();
                      splitBuild[i].Set_ConstraintTest(tests[i]);
                    }
                    GRELM id;
                    SmallStep(0,g,id,*stabArray[2*max-2]);
                    //berechne Stabilisatoren für Tests auf anderen Ebenen
                    depthfirst_stroll<LABRA> stroll(max-1,*stabArray[2*max-1]);
                    stroll.IsSmallestOrbitRep(max-1,g,CanonizerTests[max-1],c,S);
                    *stabMatrix[max-1][0] = *stabArray[2*max-1];
                    *stabMatrix[max-1][max-1] = *stabArray[2*max-1];
                    for (unsigned i=1; i<max-1; ++i)
                        *stabMatrix[max-1][i] = *stroll.stabArray[2*i-1];
                    c = canonizing_elm;
                    S = *stabArray[2*max-1];
//                    cout <<"Stabilisator Ordnung ist "<<S.size()<<endl<<endl;
                    return result;
                }
            }


            template <class LABRA>
            depthfirst_stroll<LABRA>::depthfirst_stroll(unsigned _s, LABRA const& B, unsigned d)
                :   max(_s)
                ,   debug(d)
                ,   trueValue(true)
            {
                using boost::bind;
                using boost::function;
                using boost::ref;

                if ( 2 > max ) {
                    stabArray.resize(2);
                    stabArray[0] = PLABRA(new LABRA(B));
                    stabArray[1] = PLABRA(new LABRA(B.getOmega()));
                    stabMatrix.resize(1);
                    stabMatrix[0].push_back(new LABRA(B.getOmega()));
                }
                else {

                    //for rekursive calculation
                    ladder = LADDER(new depthfirst_stroll(max-1,B));


                    //initialize stabilizers
                    stabArray.resize(2*max);
                    stabArray[0] = PLABRA(new LABRA(B));
                    for (unsigned i=1; i<2*max; ++i)
                        stabArray[i] = PLABRA(new LABRA(B.getOmega()));


                    //initialize storages
                    GRELM id;
                    speicher.reserve(2*max-1);
                    boost::shared_ptr<GRELM> g(new GRELM());
                    for (unsigned i=0; i<2*max-1;++i) {
                        speicher.emplace_back();
                        if ( i == 0 || 1 == i%2 ) {
                            speicher[i].Set_C1(stabArray[i+1]);
                            speicher[i].Set_C2(stabArray[i]);
                        }
                        else {
                            speicher[i].Set_C1(stabArray[i]);
                            speicher[i].Set_C2(stabArray[i+1]);
                        }
                        speicher[i].Set_a1(g);
                        speicher[i].Set_a2(g);
                        speicher[i].Set_b1(id);
                        speicher[i].Set_b2(id);
                        speicher[i].Set_e1(id);
                        speicher[i].Set_e2(id);
                        speicher[i].Set_D1(LABRA(B.getOmega()));
                        speicher[i].Set_D2(LABRA(B.getOmega()));
                    }
                    speicher[0].Set_D2(stabArray[2*max-1]);


                    //initialize stabilizer matrix
                    stabMatrix.resize(max);
                    for (unsigned i=0; i<max-1; ++i) {
                        stabMatrix[i].reserve(i+1);
                        for (unsigned j=0; j<=i; ++j) 
                            stabMatrix[i].emplace_back(new LABRA(B.getOmega()));
                    }
                    stabMatrix[max-1].reserve(max);
                    for (unsigned i=0; i<max; ++i)
                        stabMatrix[max-1].emplace_back(new LABRA(B.getOmega()));


                    //Initialize tests
                    CanonizerTests.resize(max);
                    for (unsigned i=0; i<max;++i) {
                        for (unsigned j=0; j<=i; ++j) {
                            LABRA const& C2 = *stabMatrix[i][j];
                            GRELM const& a1 = speicher[j==0?0:2*j-1].Get_a1();
                            GRELM const& b1 = speicher[j==0?0:2*j-1].Get_b1();
                            TESTFKT test1 = OrbitTest<LABRA>(j,C2,b1,a1);
                            CanonizerTests[i].emplace_back(test1);
                        }
                        TESTFKT test2 = bind(&depthfirst_stroll<LABRA>::result,this);
                        NoTestTests.emplace_back(test2);
                    }


                    //Initialize fusing algorithms
                    fuseBuild.reserve(max);       //max-2?
                    for (unsigned i=0; i<max-2;++i) {
                        fuseBuild.emplace_back(i+2,max-1,speicher[i*2+2],debug);
                        typename FUSEBUILD::STEPFKT nextstep;
                        nextstep = bind(&depthfirst_stroll<LABRA>::SmallStep,this,2*i+3,_1,_2,_3);
                        fuseBuild[i].Set_StepUsual(nextstep);
                        typename FUSEBUILD::CHECKCAN canocheck;
                        GRELM tmp;
                        bool (*pcan) (unsigned, GRELM const&, LABRA const&, GRELM&, LABRA&, TESTARRAY&) = &canonizer<LABRA>;
                        canocheck = bind(pcan,i+2,_1,ref(*stabArray[2*max-1]),tmp,_2,ref(CanonizerTests[i+1]));
//                        canocheck = bind(&depthfirst_stroll<LABRA>::trueValue,this);
                        fuseBuild[i].Set_CheckCanonical(canocheck);
                    }


                    //Initialize splitting algorithms
                    splitBuild.reserve(max);
                    for (unsigned i=0; i<max;++i) {
                        splitBuild.emplace_back(i+1,max-1,speicher[i==0?0:2*i-1],debug);
                        typename SPLITBUILD::STEPFKT killit;
                        killit = bind(&depthfirst_stroll<LABRA>::SetcanElmnt,this,_2);
                        splitBuild[i].Set_StepSpezial(killit);
                        typename SPLITBUILD::STEPFKT nextstep;
                        nextstep = bind(&depthfirst_stroll<LABRA>::SmallStep,this,0==i?1:2*i,_1,_2,_3);
                        splitBuild[i].Set_StepUsual(nextstep);
                    }


                    //Initialize last fusing algorithm
                    lastbuild.emplace_back(max,max-1,speicher[2*max-2]);

                }

            }

            template <class LABRA>
            bool depthfirst_stroll<LABRA>::IsSmallestOrbitRep(unsigned _s, GRELM const& g) {
                return IsSmallestOrbitRep(_s,g,NoTestTests,canonizing_elm,*stabArray[2*max-1]);
            }


            template <class LABRA>
            bool depthfirst_stroll<LABRA>::IsSmallestOrbitRep(unsigned _s, GRELM const& g, TESTARRAY& tests) {
                return IsSmallestOrbitRep(_s,g,tests,canonizing_elm,*stabArray[2*max-1]);
            }


            template <class LABRA>
            bool depthfirst_stroll<LABRA>::IsSmallestOrbitRep(unsigned _s, GRELM const& g, GRELM& c ) {
                return IsSmallestOrbitRep(_s,g,NoTestTests,c,*stabArray[2*max-1]);
            }


            template <class LABRA>
            bool depthfirst_stroll<LABRA>::IsSmallestOrbitRep(unsigned _s, GRELM const& g, TESTARRAY& tests, GRELM& c) {
                return IsSmallestOrbitRep(_s,g,tests,canonizing_elm,*stabArray[2*max-1]);
            }


            template <class LABRA>
            bool depthfirst_stroll<LABRA>::IsSmallestOrbitRep(unsigned _s, GRELM const& g, LABRA& S) {
                bool result;
                result = IsSmallestOrbitRep(_s,g,NoTestTests,canonizing_elm,S);
                return result;
            }


            template <class LABRA>
            bool depthfirst_stroll<LABRA>::IsSmallestOrbitRep(unsigned _s, GRELM const& g, TESTARRAY& tests, LABRA& S) {
                return IsSmallestOrbitRep(_s,g,tests,canonizing_elm,S);
            }


            template <class LABRA>
            bool depthfirst_stroll<LABRA>::IsSmallestOrbitRep(unsigned _s, GRELM const& g, GRELM& c, LABRA& S ) {
                return IsSmallestOrbitRep(_s,g,NoTestTests,c,S);
            }

            template <class LABRA>
            void depthfirst_stroll<LABRA>::SmallStep(unsigned level, GRELM const& e, GRELM const& b, LABRA const& D) {

                CONNECTOR   connector;
/*
                if ( 0 == level ) 
                    cout <<"Führe einen Splittingschritt aus   "<<std::setw(2)<<level+1<<"/"<<std::setw(2)<<2*max-1;
                else if ( 2*max-2 == level ) 
                    cout <<"Führe den letzen Fusingschritt aus "<<std::setw(2)<<level+1<<"/"<<std::setw(2)<<2*max-1;
                else if ( 1 == level%2 ) 
                    cout <<"Führe einen Splittingschritt aus   "<<std::setw(2)<<level+1<<"/"<<std::setw(2)<<2*max-1;
                else 
                    cout <<"Führe einen Fusingschritt aus      "<<std::setw(2)<<level+1<<"/"<<std::setw(2)<<2*max-1;
                cout <<"\t\t";
                for (unsigned j=0;j<2*max-1;++j)
                    cout <<"=";
                cout <<"\t/\t";
                for (unsigned j=0;j<level+1;++j)
                    cout <<"*";
                cout <<endl;
                cout <<"\tKandidat ist ";
                printAsPartition<LABRA>(e,level==0?0:(level+2)/2);
                cout  <<std::endl;
                std::cout <<"\tb ist "<<b<<std::endl;
                std::cout <<"\tKandidat*b ist ";
                printAsPartition<LABRA>(e*b,level==0?1:(level+2)/2);
                cout  <<std::endl;
*/
                if ( 0 == level ) 
                    connector(splitBuild[0],e,b,D);
                else if ( 2*max-2 == level ) 
                    connector(lastbuild[0],e,b,D);
                else if ( 1 == level%2 ) 
                    connector(splitBuild[level/2+1],e,b,D);
                else 
                    connector(fuseBuild[level/2-1],e,b,D);

            }


            template <class LABRA>
            bool canonizer( unsigned level, 
                            typename LABRA::GROUP_element_type const& candidate, 
                            LABRA const& B, 
                            typename LABRA::GROUP_element_type& canonizing_elm, 
                            LABRA& stab,
                            typename depthfirst_stroll<LABRA>::TESTARRAY& tests) {
                depthfirst_stroll<LABRA> stroll(level,B);
/*
                cout <<"\nkanonisiere in Schritt "<<std::setw(2)<<2*level-1<<" den Kandidaten ";
                printAsPartition<LABRA>(candidate,level);
                cout <<endl;
                cout <<"der zugehörige Stabilisator hat die Ordnung "<<B.size()<<endl; 
*/
                bool result = stroll.IsSmallestOrbitRep(level, candidate, tests, canonizing_elm, stab);
//                std::cout <<"\tOrdnung des Stabilisators nach Kanonisierung ist "<<std::setw(12)<<stab.size()<<std::endl<<std::endl;
                return result;
            }


        } // end namespace stroll

    } // end namespace depthfirst

} // end namespace laddergame

#endif // LADDER_ALGORITHM_DEPTHFIRST_STROLL
