#ifndef LADDER_ALGORITHM_BREADTHFIRST_SIMPLE
#define LADDER_ALGORITHM_BREADTHFIRST_SIMPLE

#include <iostream>
#include <boost/bind.hpp>
#include <boost/function.hpp>
#include <boost/shared_ptr.hpp>
#include <boost/scoped_ptr.hpp>
#include <boost/functional/value_factory.hpp>
#include <boost/container/vector.hpp>
#include <boost/container/list.hpp>



#include <simpleYoungGroup/function_builder_depthfirst_simple_splitting.hpp>
#include <simpleYoungGroup/function_builder_depthfirst_simple_fusing.hpp>
#include <simpleYoungGroup/function_builder_depthfirst_simple_lastfusing.hpp>
#include <simpleYoungGroup/stair_connector.hpp>
#include <simpleYoungGroup/storage.hpp>
#include <younggroupmethods2/redustab.hpp>
#include <younggroupmethods2/findOrbitRep.hpp>
#include <younggroupmethods2/transversal_system.hpp>
#include <younggroupmethods2/addgenerator.hpp>



namespace laddergame {

    namespace breadthfirst {

        namespace simple {



            template <class _LABRA>
            class laddergame_light {

              public:

                typedef _LABRA                                                      LABRA;
                typedef typename LABRA::GROUP_element_type                          GRELM;
                typedef boost::shared_ptr<LABRA>                                    PLABRA;
                typedef storage<LABRA>                                              STORAGE;
                typedef boost::shared_ptr<laddergame_light>                         LADDER;

                typedef depthfirst::simple::lastfusing_algorithm_builder<LABRA>     LASTBUILD;
                typedef depthfirst::simple::splitting_algorithm_builder<LABRA>      SPLITBUILD;
                typedef depthfirst::simple::fusing_algorithm_builder<LABRA>         FUSEBUILD;
                typedef stair_connector<LABRA>                                      CONNECTOR;
                typedef typename transversalsystem<LABRA>::ELMNTMAP                 ELMNTMAP;

                typedef bool                                                        result_type;

                laddergame_light(unsigned, LABRA const&, unsigned debug = 0);

                inline bool IsSmallestOrbitRep  (unsigned, GRELM const& );
                inline bool IsSmallestOrbitRep  (unsigned, GRELM const&, GRELM& c );
                inline bool IsSmallestOrbitRep  (unsigned, GRELM const&, LABRA& S);
                inline bool IsSmallestOrbitRep  (unsigned, GRELM const&, GRELM& c, LABRA& S);
                inline bool MakeSmallestOrbitRep(unsigned, GRELM const& );
                inline bool MakeSmallestOrbitRep(unsigned, GRELM const&, GRELM& c );
                inline bool MakeSmallestOrbitRep(unsigned, GRELM const&, LABRA& S);
                inline bool MakeSmallestOrbitRep(unsigned, GRELM const&, GRELM& c, LABRA& S);

              private:

                bool SmallestOrbitRep(unsigned, GRELM const&, GRELM& c, LABRA& S, bool isCan);
                bool Canonizer(GRELM, GRELM& c, LABRA& S, bool isCan);
                void CalcStabilizer(unsigned _s, GRELM const& g);

                inline void smallStep(unsigned level, GRELM const& g, GRELM const& b);
                inline void storeForNextStep(unsigned level, GRELM const& g, GRELM const& b);
                inline void SetcanElmnt(unsigned level, GRELM const& g, GRELM& b);

                boost::container::vector<STORAGE>       speicher;

                boost::container::vector<PLABRA>        stabArray;
                boost::container::vector<FUSEBUILD>     fuseBuild;
                boost::container::vector<SPLITBUILD>    splitBuild;
                boost::container::vector<LASTBUILD>     lastbuild;
                LADDER                                  ladder;

                struct coin {
                    GRELM   g;
                    GRELM   b;
                };

                transversalsystem<LABRA>                keymaker;
                boost::container::list<coin>            candidates;
                unsigned                                max;
                unsigned                                debug;
                bool                                    result;
                GRELM                                   canonizing_elm;
                GRELM                                   orbit_rep;

            };


            template <class LABRA>
            bool laddergame_light<LABRA>::SmallestOrbitRep(unsigned s, GRELM const& g, GRELM& c, LABRA& S, bool isCan) {
                typedef typename LABRA::SET_element_type    SETELM;
                using laddergame::depthfirst::ReduStab;
                using laddergame::depthfirst::findOrbitRepresentative;
                if ( s > max ) {
                    std::cerr <<" canonizing laddergame light is too small for this work"<<std::endl;
                    exit(-1);
                }
                else if ( 0 == s ) {
                    c = GRELM();
                    S = *stabArray[0];
                    return true;
                }
                else if ( 1 == s ) {
                    result = true;
                    SETELM omega(0);
                    c = findOrbitRepresentative(*stabArray[0],omega,g);
                    if ( omega<<g*c != omega<<g ) 
                        return false;
                    else {
                      *stabArray[1] = *stabArray[0];
                      ReduStab(g,omega,*stabArray[1]);
                    }
                    S = *stabArray[1];
                    return true;
                }
                else if ( s < max )
                    return ladder->SmallestOrbitRep(s,g,c,S,isCan);
                else
                    return Canonizer(g,c,S,isCan);
                return true;
            }



            template <class LABRA>
            void laddergame_light<LABRA>::CalcStabilizer(unsigned i, GRELM const& g) {
                typedef typename LABRA::SET_element_type                    SETELM;
                typedef typename boost::container::list<coin>::iterator     iterator; 
                typedef typename transversalsystem<LABRA>::KEY              KEY; 
                using laddergame::depthfirst::ReduStab;
                using laddergame::depthfirst::extendGroup;
                if ( 0 == i || 1 == i%2 ) {
                    *stabArray[i+1] = *stabArray[i];
                    SETELM omega((i+1)/2);
                    ReduStab(g,omega,*stabArray[i+1]);
                }
                else {
                    *stabArray[i+1] = *stabArray[i];
                    extendGroup<LABRA> makeBig;
                    iterator it = candidates.begin();
                    iterator end = candidates.end();
                    KEY key1 = keymaker.keycalc(i+1,g);
                    while ( end != it ) {
                        KEY key2 = keymaker.keycalc(i+1,it->g);
                        if ( key1 == key2 )
                            makeBig(it->b,*stabArray[i+1]);
                        ++it;
                    }
                }
            }


            template <class LABRA>
            bool laddergame_light<LABRA>::Canonizer(GRELM g, GRELM& c, LABRA& S, bool canonizer) {
                typedef typename boost::container::list<coin>::iterator    iterator; 
                GRELM id;
                candidates.clear();
                c = id;
                speicher[0].Set_a2(g);
                speicher[0].Set_e2(g);
                speicher[2*max-2].Set_b2(id);
                //this is necessary, because the groups (C_1,...,C_n) might change
                for(unsigned i=0; i<max-2; ++i)
                  fuseBuild[i].Build_FindOrbitRepConj();
                for(unsigned i=0; i<max; ++i)
                  splitBuild[i].Build_FindOrbitRep();
                storeForNextStep(0,g,id);

                for (unsigned i=0; i<2*max-2; ++i) {
                    CalcStabilizer(i,g);
                    iterator it  = candidates.begin();
                    iterator end = candidates.end();
                    while ( end != it ) {
                        result = true;
                        smallStep(i,it->g,it->b);
                        if ( false == result ) {
                            c = canonizing_elm;
                            if ( false == canonizer )
                                return false;
                            g = orbit_rep;
                            speicher[0].Set_a2(g);
                            candidates.erase(candidates.begin(),it);
                            CalcStabilizer(i,g);
                        }
                        else
                          it = candidates.erase(it);
                    }
                }
                if ( id != c )
                    return false;
                S = *stabArray[2*max-1];
                return true;
            }


            template <class LABRA>
            laddergame_light<LABRA>::laddergame_light(unsigned _s, LABRA const& B, unsigned d)
                :   keymaker(2*_s)
                ,   max(_s)
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
                        killit = bind(&laddergame_light<LABRA>::SetcanElmnt,this,0==i?1:2*i,_1,_2);
                        splitBuild[i].Set_StepSpezial(killit);
                        typename SPLITBUILD::STEPFKT nextstep;
                        nextstep = bind(&laddergame_light<LABRA>::storeForNextStep,this,0==i?1:2*i,_1,_2);
                        splitBuild[i].Set_StepUsual(nextstep);
                    }


                    //Initialize fusing algorithms
                    fuseBuild.reserve(max);       //max-2?
                    for (unsigned i=0; i<max-2;++i) {
                        fuseBuild.emplace_back(i+2,max-1,speicher[i*2+2],debug);
                        typename FUSEBUILD::STEPFKT nextstep;
                        nextstep = bind(&laddergame_light<LABRA>::storeForNextStep,this,2*i+3,_1,_2);
                        fuseBuild[i].Set_StepUsual(nextstep);
                    }

                    //Initialize last fusing algorithm
                    lastbuild.emplace_back(max,max-1,speicher[2*max-2]);

                }

            }


            template <class LABRA>
            void laddergame_light<LABRA>::storeForNextStep(unsigned i, GRELM const& g, GRELM const& b) {
                coin c;
                c.g = g;
                c.b = b;
                candidates.push_front(c);
            }


            template <class LABRA>
            void laddergame_light<LABRA>::smallStep(unsigned i, GRELM const& g, GRELM const& b) {

                CONNECTOR   connector;
                if ( 0 == i )
                    connector(splitBuild[0],g,b);
                else if ( 2*max-2 == i )
                    connector(lastbuild[0],g,b);
                else if ( 1 == i%2 )
                    connector(splitBuild[i/2+1],g,b);
                else
                    connector(fuseBuild[i/2-1],g,b);
            }



            template <class LABRA>
            inline void laddergame_light<LABRA>::SetcanElmnt(unsigned level, GRELM const& e, GRELM& b) {
                canonizing_elm = b;
                orbit_rep = e*b;
                result = false;
            }


            template <class LABRA>
            bool laddergame_light<LABRA>::IsSmallestOrbitRep(unsigned s, GRELM const& g) {
                GRELM tmp1;
                LABRA tmp2(*stabArray[0]);
                return SmallestOrbitRep(s,g,tmp1,tmp2,false);
            }

            template <class LABRA>
            bool laddergame_light<LABRA>::IsSmallestOrbitRep(unsigned s, GRELM const& g, GRELM& c) {
                LABRA tmp(*stabArray[0]);
                return SmallestOrbitRep(s,g,c,tmp,false);
            }


            template <class LABRA>
            bool laddergame_light<LABRA>::IsSmallestOrbitRep(unsigned s, GRELM const& g, GRELM& c, LABRA& S) {
                return SmallestOrbitRep(s,g,c,S,false);
            }


            template <class LABRA>
            bool laddergame_light<LABRA>::IsSmallestOrbitRep(unsigned s, GRELM const& g, LABRA& S) {
                GRELM tmp;
                return SmallestOrbitRep(s,g,tmp,S,false);
            }


            template <class LABRA>
            bool laddergame_light<LABRA>::MakeSmallestOrbitRep(unsigned s, GRELM const& g) {
                GRELM tmp1;
                LABRA tmp2(*stabArray[0]);
                return SmallestOrbitRep(s,g,tmp1,tmp2,true);
            }


            template <class LABRA>
            bool laddergame_light<LABRA>::MakeSmallestOrbitRep(unsigned s, GRELM const& g, GRELM& c) {
                LABRA tmp(*stabArray[0]);
                return SmallestOrbitRep(s,g,c,tmp,true);
            }


            template <class LABRA>
            bool laddergame_light<LABRA>::MakeSmallestOrbitRep(unsigned s, GRELM const& g, LABRA& S) {
                GRELM tmp;
                return SmallestOrbitRep(s,g,tmp,S,true);
            }


            template <class LABRA>
            bool laddergame_light<LABRA>::MakeSmallestOrbitRep(unsigned s, GRELM const& g, GRELM& c, LABRA& S) {
                return SmallestOrbitRep(s,g,c,S,true);
            }


        } // end namespace simple

    } // end namespace breadthfirst

} // end namespace laddergame

#endif // LADDER_ALGORITHM_BREADTHFIRST_SIMPLE
