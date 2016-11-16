#ifndef FUSING_ALGORITHM_BUILDER_DEPTHFIRST_STROLL
#define FUSING_ALGORITHM_BUILDER_DEPTHFIRST_STROLL


#include <simpleYoungGroup/simpleLaddergameHomomorphisms.hpp>
#include <Algorithms/algorithm_depthfirst_stroll_fusing.hpp>
#include <younggroupmethods2/findOrbitRepConj_store.hpp>
#include <younggroupmethods2/compare.hpp>
#include <simpleYoungGroup/storage.hpp>



namespace laddergame {

    namespace depthfirst {

        namespace stroll {


            template <class _LABRA>
            class fusing_algorithm_builder {
    
                typedef _LABRA                                                                  LABRA;
                typedef SimpleLaddergameHomomorphisms<LABRA>                                    SQUARE;
                typedef fusing_algorithm<SQUARE>                                                FUSE;

                typedef typename SQUARE::GROUP_element_type                                     GRELM;
                typedef typename SQUARE::SET_element_type_ul                                    SETELM1;
                typedef typename SQUARE::SET_element_type_ur                                    SETELM2;
                typedef typename SQUARE::SET_element_type_ll                                    SETELM3;
                typedef typename SQUARE::SET_element_type_lr                                    SETELM4;

              public:    

                typedef boost::function< SETELM2(SETELM1 const&) >                              VARPHIHOM;
                typedef boost::function< GRELM(SETELM1 const&,LABRA const&,GRELM const&)>       CANFKTCONJ; 
                typedef boost::function< bool(SETELM1 const&,SETELM1 const&) >                  CMPFKT; 
                typedef boost::function< bool(SETELM2 const&,LABRA&) >                          CHECKCAN;
                typedef boost::function< void(SETELM2 const&,GRELM const&,LABRA const&) >       STEPFKT;
                typedef storage<LABRA>                                                          VARIABLES;

                struct  Algorithm;
                typedef Algorithm&                                                              result_type;


                inline fusing_algorithm_builder(unsigned x, unsigned n, VARIABLES const&, unsigned debug = 0);

                inline Algorithm&   operator()(); 
                inline void         Set_StepUsual(STEPFKT const&);
                inline void         Build_FindOrbitRepConj();
                inline void         Set_CheckCanonical(CHECKCAN const&);
                inline VARIABLES&   Get_Variables();

              private:
                    
                inline void         Build_VarphiHom();
                inline void         Build_SmallerOrEqual(unsigned);

                Algorithm   algo;
                unsigned    x;
            };



            template <class LABRA>
            struct fusing_algorithm_builder<LABRA>::Algorithm {
                Algorithm(VARIABLES const& v, unsigned d) : var(v), debug(d) {}
                void operator()();
                VARIABLES   var;
                boost::shared_ptr<VARPHIHOM>        VarphiHom;
                boost::shared_ptr<CANFKTCONJ>       FindOrbitRepConjugate;
                boost::shared_ptr<CHECKCAN>         CheckCanonical;
                boost::shared_ptr<CMPFKT>           SmallerOrEqual;
                boost::shared_ptr<STEPFKT>          NextStep;
                unsigned debug;
            };



            template <class LABRA>
            void fusing_algorithm_builder<LABRA>::Algorithm::operator()() {
                typename FUSE::Functions f = {  *VarphiHom
                                            ,   *FindOrbitRepConjugate
                                            ,   *CheckCanonical
                                            ,   *SmallerOrEqual
                                            ,   *NextStep};
                FUSE()(var,f,debug);
            }


            template <class LABRA>
            fusing_algorithm_builder<LABRA>::fusing_algorithm_builder(unsigned _x, unsigned n, VARIABLES const& v, unsigned d ) 
                :   algo(v,d!=0?_x:0) 
                ,   x(_x-1) {
                Build_VarphiHom();
                Build_SmallerOrEqual(n);
                Build_FindOrbitRepConj();
            }


            template <class LABRA>
            typename fusing_algorithm_builder<LABRA>::VARIABLES& fusing_algorithm_builder<LABRA>::Get_Variables() { 

                return algo.var;
            }


            template <class LABRA>
            void fusing_algorithm_builder<LABRA>::Set_StepUsual(STEPFKT const& s) { 

                algo.NextStep = boost::shared_ptr<STEPFKT>(new STEPFKT());
                *algo.NextStep = s; 
            }


            template <class LABRA>
            void fusing_algorithm_builder<LABRA>::Set_CheckCanonical(CHECKCAN const& s) { 

                algo.CheckCanonical = boost::shared_ptr<CHECKCAN>(new CHECKCAN());
                *algo.CheckCanonical = s; 
            }


            template <class LABRA>
            void fusing_algorithm_builder<LABRA>::Build_VarphiHom() { 

                algo.VarphiHom = boost::shared_ptr<VARPHIHOM>(new VARPHIHOM());
                *algo.VarphiHom = identity_function<SETELM1>; 
            }


            template <class LABRA>
            void fusing_algorithm_builder<LABRA>::Build_FindOrbitRepConj() { 

                //generate function to calculate the minimal orbit representative
                typename LABRA::SET_element_type omega(x);

                algo.FindOrbitRepConjugate = boost::shared_ptr<CANFKTCONJ>(new CANFKTCONJ());
                *algo.FindOrbitRepConjugate = findOrbitRepConjStore<LABRA,true>(omega); 
            }

             
            template <class LABRA>
            void fusing_algorithm_builder<LABRA>::Build_SmallerOrEqual(unsigned n) {   
                typedef typename LABRA::SET_element_type SET_element_type;

                //generate descriptions for young groups
                vector<int> vint;
                vector<SET_element_type> vset;
                for (unsigned i=0; i<=x;++i) {
                  vset.emplace_back(i);
                  vint.push_back(0);
                }
                vint.back() = 1;

                //generate coset comparison function
                //Attention: compares the domains cosets, not the ones of the image!
                algo.SmallerOrEqual = boost::shared_ptr<CMPFKT>(new CMPFKT() );
                *algo.SmallerOrEqual = CompareYoungGroup<LABRA>(vset,vint);
            }



            template <class LABRA>
            typename fusing_algorithm_builder<LABRA>::Algorithm&
            fusing_algorithm_builder<LABRA>::operator()() {
                // build algorithm if everything is ready
                if ( 0 == algo.NextStep.get() || 0 == algo.CheckCanonical.get() ) {
                    std::cerr <<"In Function fusing_algorithm_builder::operator()"<<std::endl;
                    std::cerr <<"Some Variables have not yet been defined"<<std::endl;
                    exit(-1);
                }
                return algo;
            }
    
    
        } // end namespace stroll
    } // end namespace depthfirst
} // end namespace laddergame

#endif // FUSING_ALGORITHM_BUILDER_DEPTHFIRST_STROLL
