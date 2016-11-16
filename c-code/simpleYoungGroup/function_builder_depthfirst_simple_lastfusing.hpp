#ifndef LASTFUSING_ALGORITHM_BUILDER_DEPTHFIRST_SIMPLE
#define LASTFUSING_ALGORITHM_BUILDER_DEPTHFIRST_SIMPLE


#include <simpleYoungGroup/simpleLaddergameHomomorphisms.hpp>
#include <Algorithms/algorithm_depthfirst_simple_laststep.hpp>
#include <younggroupmethods2/addgenerator.hpp>
#include <younggroupmethods2/compare.hpp>
#include <simpleYoungGroup/storage.hpp>



namespace laddergame {

    namespace depthfirst {

        namespace simple {

            template <class _LABRA>
            class lastfusing_algorithm_builder {
    
                typedef _LABRA                                                                  LABRA;
                typedef SimpleLaddergameHomomorphisms<LABRA>                                    SQUARE;
                typedef lastFusingStep_algorithm<SQUARE>                                        FUSE;


                typedef typename SQUARE::GROUP_element_type                                     GRELM;
                typedef typename SQUARE::SET_element_type_ul                                    SETELM1;
                typedef typename SQUARE::SET_element_type_ur                                    SETELM2;
                typedef typename SQUARE::SET_element_type_ll                                    SETELM3;
                typedef typename SQUARE::SET_element_type_lr                                    SETELM4;

              public:    

                typedef boost::function< bool(SETELM4 const&,SETELM4 const&) >                  CMPFKT; 
                typedef boost::function< void(GRELM const&,LABRA&) >                            EXPANDSTAB;
                typedef storage<LABRA>                                                          VARIABLES;


                struct  Algorithm;
                typedef Algorithm&                                                              result_type;


                inline lastfusing_algorithm_builder(unsigned x, unsigned n, VARIABLES const&);

                inline Algorithm&   operator()() { return algo; }
                inline VARIABLES&   Get_Variables();

              private:

                inline void Build_SmallerOrEqual(unsigned);
                inline void Build_ExpandStab();

                Algorithm algo;
            };



            template <class LABRA>
            struct lastfusing_algorithm_builder<LABRA>::Algorithm {
                Algorithm(VARIABLES const& v) : var(v) {}
                void operator()();
                VARIABLES                           var;
                boost::shared_ptr<EXPANDSTAB>       ExpandStab;
                boost::shared_ptr<CMPFKT>           SmallerOrEqual;
            };


            template <class LABRA>
            void lastfusing_algorithm_builder<LABRA>::Algorithm::operator()() {
                typename FUSE::Functions f = {  *SmallerOrEqual
                                            ,   *ExpandStab };
                FUSE()(var,f);
            }


            template <class LABRA>
            lastfusing_algorithm_builder<LABRA>::lastfusing_algorithm_builder(unsigned x, unsigned n, VARIABLES const& v) 
                :   algo(v) {
                Build_SmallerOrEqual(x);
                Build_ExpandStab();
            }


            template <class LABRA>
            typename lastfusing_algorithm_builder<LABRA>::VARIABLES& lastfusing_algorithm_builder<LABRA>::Get_Variables() { 

                return algo.var;
            }


            template <class LABRA>
            void lastfusing_algorithm_builder<LABRA>::Build_ExpandStab() {
                algo.ExpandStab = boost::shared_ptr<EXPANDSTAB>(new EXPANDSTAB());
                *algo.ExpandStab = extendGroup<LABRA>();
            }


            template <class LABRA>
            void lastfusing_algorithm_builder<LABRA>::Build_SmallerOrEqual(unsigned x) {   
                typedef typename LABRA::SET_element_type SET_element_type;

                //generate descriptions for young groups
                vector<int> vint;
                vector<SET_element_type> vset;
                for (unsigned i=0; i!=x;++i) {
                  vset.emplace_back(i);
                  vint.push_back(0);
                }
                //vint.back() = 1;

                //generate coset comparison function
                //Attention: compares the domains cosets, not the ones of the image!
                algo.SmallerOrEqual = boost::shared_ptr<CMPFKT>(new CMPFKT());
                *algo.SmallerOrEqual = CompareYoungGroup<LABRA>(vset,vint);
            }


        } // end namespace simpleYoungGroup
    } // end namespace depthfirst
} // end namespace laddergame

#endif // LASTFUSING_ALGORITHM_BUILDER_DEPTHFIRST_SIMPLE
