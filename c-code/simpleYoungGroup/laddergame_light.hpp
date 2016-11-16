#ifndef LADDER_ALGORITHM_DEPTHFIRST_SIMPLE
#define LADDER_ALGORITHM_DEPTHFIRST_SIMPLE

#include <iostream>
#include <boost/bind.hpp>
#include <boost/function.hpp>
#include <boost/shared_ptr.hpp>
#include <boost/scoped_ptr.hpp>
#include <boost/functional/value_factory.hpp>
#include <boost/container/vector.hpp>


#include <simpleYoungGroup/function_builder_depthfirst_simple_splitting.hpp>
#include <simpleYoungGroup/function_builder_depthfirst_simple_fusing.hpp>
#include <simpleYoungGroup/function_builder_depthfirst_simple_lastfusing.hpp>
#include <simpleYoungGroup/stair_connector.hpp>
#include <simpleYoungGroup/storage.hpp>
#include <younggroupmethods2/redustab.hpp>
#include <younggroupmethods2/findOrbitRep.hpp>



namespace laddergame {

    namespace depthfirst {

        namespace simple {



            template <class _LABRA>
            class laddergame_light {

              public:

                typedef _LABRA                                                  LABRA;
                typedef typename LABRA::GROUP_element_type                      GRELM;
                typedef boost::shared_ptr<LABRA>                                PLABRA;
                typedef storage<LABRA>                                          STORAGE;
                typedef boost::shared_ptr<laddergame_light>                     LADDER;
                typedef lastfusing_algorithm_builder<LABRA>                     LASTBUILD;
                typedef splitting_algorithm_builder<LABRA>                      SPLITBUILD;
                typedef fusing_algorithm_builder<LABRA>                         FUSEBUILD;
                typedef stair_connector<LABRA>                                  CONNECTOR;
                
                typedef bool                                                    result_type;

                laddergame_light(unsigned, LABRA const&, unsigned debug = 0);

                bool IsSmallestOrbitRep(unsigned, GRELM const& );
                bool IsSmallestOrbitRep(unsigned, GRELM const&, GRELM& c );
                bool IsSmallestOrbitRep(unsigned, GRELM const&, GRELM& c, LABRA& s );

              private:

                void smallStep(unsigned level, GRELM const& e, GRELM const& b);

                void SetcanElmnt(GRELM& b1) { canonizing_elm = b1; result = false; }

                boost::container::vector<STORAGE>       speicher;

                boost::container::vector<PLABRA>        stabArray;
                boost::container::vector<FUSEBUILD>     fuseBuild;
                boost::container::vector<SPLITBUILD>    splitBuild;
                boost::container::vector<LASTBUILD>     lastbuild;
                LADDER ladder;

                unsigned    max;
                unsigned    debug;
                bool        result;
                GRELM       canonizing_elm;

            };


            template <class LABRA>
            bool laddergame_light<LABRA>::IsSmallestOrbitRep(unsigned _s, GRELM const& g) {
                return IsSmallestOrbitRep(_s,g,canonizing_elm);
            }


            template <class LABRA>
            bool laddergame_light<LABRA>::IsSmallestOrbitRep(unsigned _s, GRELM const& g, GRELM& c) {
                LABRA tmp(*stabArray[0]);
                return IsSmallestOrbitRep(_s,g,c,tmp);
            }


            template <class LABRA>
            bool laddergame_light<LABRA>::IsSmallestOrbitRep(unsigned _s, GRELM const& g, GRELM& c, LABRA& S) {
                typedef typename LABRA::SET_element_type    SETELM;
                using laddergame::depthfirst::ReduStab;
                using laddergame::depthfirst::findOrbitRepresentative;
                if ( _s > max ) {
                    std::cerr <<" canonizing laddergame light is too small for this work"<<std::endl;
                    exit(-1);
                }
/*
                else if ( 1 == stabArray[0]->size() ) {
                    canonizing_elm = c = GRELM();
                    result = true;
                    //S = *stabArray[0];
                    return true;
                }
*/
                else if ( 0 == _s ) {
                    result = true;
                    c = GRELM();
                    S = *stabArray[0];
                }
                else if ( 1 == _s ) {
                    result = true;
                    SETELM omega(0);
                    c = findOrbitRepresentative(*stabArray[0],omega,g);
                    if ( omega<<g*c != omega<<g ) 
                        result = false;
                    else {
                      *stabArray[1] = *stabArray[0];
                      ReduStab(g,omega,*stabArray[1]);
                    }
                    S = *stabArray[1];
                }
                else if ( _s < max )
                    result = ladder->IsSmallestOrbitRep(_s,g,c,S);
                //now _s == max
                else {
                    result = ladder->IsSmallestOrbitRep(_s-1,g,c,S);
                    if ( false == result )
                        return false;
                    //calculate stabilizers
                    {   
                        //calculate the next stabilizer
                        *stabArray[2*max-2] = *stabArray[2*max-3];
                        SETELM omega(_s-1);
                        ReduStab(g,omega,*stabArray[2*max-2]);
                        //initialize next stabilizer with the known subgroup
                        *stabArray[2*max-1] = *stabArray[2*max-2];
                    }
                    speicher[0].Set_a2(g);
                    speicher[0].Set_e2(g);
                    speicher[2*max-2].Set_b2(GRELM());
                    //this is necessary, because the groups (C_1,...,C_n) might have changed
                    for(unsigned i=0; i<max-2; ++i)
                      fuseBuild[i].Build_FindOrbitRepConj();
                    for(unsigned i=0; i<max; ++i)
                      splitBuild[i].Build_FindOrbitRep();
                    GRELM id;
                    smallStep(0,g,id);
                    c = canonizing_elm;
                    S = *stabArray[2*max-1];
                    //cout <<"return von Ebene "<<_s<<" Stabilisator Ordnung "<<stabArray[2*max-1]->size()<<endl;
                }
                return result;
            }


            template <class LABRA>
            laddergame_light<LABRA>::laddergame_light(unsigned _s, LABRA const& B, unsigned d)
                :   max(_s)
                ,   debug(d)
            {
                using boost::bind;
                using boost::function;
                using boost::ref;

                if ( 2 > max ) {
                    stabArray.resize(2);
                    stabArray[0] = PLABRA(new LABRA(B));
                    stabArray[1] = PLABRA(new LABRA(B.getOmega()));
                }
                else {

                    //for rekursive calculation
                    ladder = LADDER(new laddergame_light(max-1,B));

                    //Initialize Stabilizers
                    stabArray.resize(2*max);
                    stabArray[2*max-2] = PLABRA(new LABRA(B.getOmega()));
                    stabArray[2*max-1] = PLABRA(new LABRA(B.getOmega()));
                    for (unsigned i=0; i<2*max-2; ++i)
                        stabArray[i] = ladder->stabArray[i];


                    //Initialize Storages
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
                    }


                    //Initialize splitting algorithms
                    splitBuild.reserve(max);
                    for (unsigned i=0; i<max;++i) {
                        splitBuild.emplace_back(i+1,max-1,speicher[i==0?0:2*i-1],debug);
                        typename SPLITBUILD::STEPFKT killit;
                        killit = bind(&laddergame_light<LABRA>::SetcanElmnt,this,_2);
                        splitBuild[i].Set_StepSpezial(killit);
                        typename SPLITBUILD::STEPFKT nextstep;
                        nextstep = bind(&laddergame_light<LABRA>::smallStep,this,0==i?1:2*i,_1,_2);
                        splitBuild[i].Set_StepUsual(nextstep);
                    }


                    //Initialize fusing algorithms
                    fuseBuild.reserve(max);       //max-2?
                    for (unsigned i=0; i<max-2;++i) {
                        fuseBuild.emplace_back(i+2,max-1,speicher[i*2+2],debug);
                        typename FUSEBUILD::STEPFKT nextstep;
                        nextstep = bind(&laddergame_light<LABRA>::smallStep,this,2*i+3,_1,_2);
                        fuseBuild[i].Set_StepUsual(nextstep);
                    }

                    //Initialize last fusing algorithm
                    lastbuild.emplace_back(max,max-1,speicher[2*max-2]);

                }

            }


            template <class LABRA>
            void laddergame_light<LABRA>::smallStep(unsigned i, GRELM const& e, GRELM const& b) {

                CONNECTOR   connector;
                if ( 0 == i )
                    connector(splitBuild[0],e,b);
                else if ( 2*max-2 == i )
                    connector(lastbuild[0],e,b);
                else if ( 1 == i%2 )
                    connector(splitBuild[i/2+1],e,b);
                else
                    connector(fuseBuild[i/2-1],e,b);
            }


        } // end namespace simple

    } // end namespace depthfirst

} // end namespace laddergame

#endif // LADDER_ALGORITHM_DEPTHFIRST_SIMPLE
