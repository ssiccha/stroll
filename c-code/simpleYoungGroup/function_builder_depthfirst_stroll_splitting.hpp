#ifndef SPLITTING_ALGORITHM_BUILDER_DEPTHFIRST_STROLL
#define SPLITTING_ALGORITHM_BUILDER_DEPTHFIRST_STROLL


#include <simpleYoungGroup/simpleLaddergameHomomorphisms.hpp>
#include <Algorithms/algorithm_depthfirst_stroll_splitting.hpp>
#include <younggroupmethods2/findOrbitRep_store.hpp>
#include <younggroupmethods2/findOrbitRep.hpp>
#include <younggroupmethods2/compare.hpp>
#include <younggroupmethods2/ladder_homomorphism.hpp>
#include <younggroupmethods2/redustab.hpp>
#include <simpleYoungGroup/storage.hpp>

#include <boost/bind.hpp>




namespace laddergame {

    namespace depthfirst {

        namespace stroll {

            template <class labra>
            class splitting_algorithm_builder {
    
                typedef labra                                                                   LABRA;
                typedef SimpleLaddergameHomomorphisms<LABRA>                                    SQUARE;
                typedef splitting_algorithm<SQUARE>                                             SPLIT;
                typedef typename SPLIT::RANGE                                                   RANGE;

                typedef typename SQUARE::GROUP_element_type                                     GRELM;
                typedef typename SQUARE::SET_element_type_ul                                    SETELM1;
                typedef typename SQUARE::SET_element_type_ur                                    SETELM2;
                typedef typename SQUARE::SET_element_type_ll                                    SETELM3;
                typedef typename SQUARE::SET_element_type_lr                                    SETELM4;

              public:


                typedef boost::function< SETELM3(SETELM1 const&) >                              PSI1;
                typedef boost::function< RANGE(SETELM2 const&) >                                SPLITHOM;
                typedef boost::function< GRELM(SETELM1 const&,LABRA const&)>                    CANFKT; 
                typedef boost::function< bool(SETELM3 const&,SETELM3 const&) >                  CMPFKT; 
                typedef boost::function< void(SETELM1 const&,LABRA&)>                           REDUKFT;
                typedef boost::function< bool(SETELM1 const&, GRELM const&) >                   TESTFKT;
                typedef boost::function< void(SETELM1 const&,GRELM const&,LABRA const&) >       STEPFKT;
                typedef storage<LABRA>                                                          VARIABLES;

                struct  Algorithm;
                typedef Algorithm&                                                              result_type;



                inline splitting_algorithm_builder(unsigned,unsigned,VARIABLES const&, unsigned debug = 0);

                inline Algorithm&   operator()(); 
                inline void         Set_ConstraintTest(TESTFKT const& t);
                inline void         Set_StepUsual(STEPFKT const& s);
                inline void         Set_StepSpezial(STEPFKT const& s);
                inline VARIABLES&   Get_Variables();
                inline void         Build_FindOrbitRep1();
                inline void         Build_Test();

              private:

                inline void         Build_Psi1();
                inline void         Build_VarphiInvers(unsigned);
                inline void         Build_SmallerOrEqual(unsigned);
                inline void         Build_ReduceStab();
                inline void         Build_FindOrbitRep2();

                Algorithm           algo;
                unsigned            x;
                unsigned            debug;
            };


            template <class LABRA>
            struct splitting_algorithm_builder<LABRA>::Algorithm {
                Algorithm(VARIABLES const& v, unsigned d) : var(v), debug(d) {}
                void operator()();
                VARIABLES   var;
                boost::shared_ptr<PSI1>         Psi1;
                boost::shared_ptr<SPLITHOM>     VarphiInv;
                boost::shared_ptr<CANFKT>       FindOrbitRep1;
                boost::shared_ptr<CANFKT>       FindOrbitRep2;
                boost::shared_ptr<TESTFKT>      test;
                boost::shared_ptr<CMPFKT>       SmallerOrEqual;
                boost::shared_ptr<REDUKFT>      ReduceStab;
                boost::shared_ptr<STEPFKT>      step1;
                boost::shared_ptr<STEPFKT>      step2;
                unsigned debug;
            };


            template <class LABRA>
            void splitting_algorithm_builder<LABRA>::Algorithm::operator()() {
                typename SPLIT::Functions f = { *Psi1
                                            ,   *VarphiInv
                                            ,   *FindOrbitRep1
                                            ,   *FindOrbitRep2
                                            ,   *test
                                            ,   *SmallerOrEqual
                                            ,   *ReduceStab
                                            ,   *step1
                                            ,   *step2};
                SPLIT()(var,f,debug);
            }


            template <class LABRA>
            splitting_algorithm_builder<LABRA>::splitting_algorithm_builder(unsigned _x, unsigned n, VARIABLES const& v, unsigned d) 
                :   algo(v,d!=0?_x:0) 
                ,   x(_x-1) {
                Build_Test();
                Build_Psi1();
                Build_VarphiInvers(n);
                Build_SmallerOrEqual(n);
                Build_ReduceStab();
                Build_FindOrbitRep1();
                Build_FindOrbitRep2();
            }


            template <class LABRA>
            typename splitting_algorithm_builder<LABRA>::VARIABLES& splitting_algorithm_builder<LABRA>::Get_Variables() { 

                return algo.var;
            }


            template <class LABRA>
            void splitting_algorithm_builder<LABRA>::Build_Test() {
                algo.test = boost::shared_ptr<TESTFKT>(new TESTFKT()); 
                *algo.test = ReturnTrue<SETELM1,GRELM>;
            }


            template <class LABRA>
            void splitting_algorithm_builder<LABRA>::Build_ReduceStab() {
                typename LABRA::SET_element_type omega(x);
                algo.ReduceStab = boost::shared_ptr<REDUKFT>(new REDUKFT());
                *algo.ReduceStab = boost::bind(ReduStab<LABRA>,_1,omega,_2);
            }


            template <class LABRA>
            void splitting_algorithm_builder<LABRA>::Build_Psi1() {
                algo.Psi1 = boost::shared_ptr<PSI1>(new PSI1()); 
                *algo.Psi1 = identity_function<SETELM1>;
            }

            template <class LABRA>
            void splitting_algorithm_builder<LABRA>::Set_ConstraintTest(TESTFKT const& t) {
                algo.test = boost::shared_ptr<TESTFKT>(new TESTFKT());
                *algo.test = t; 
            }

            template <class LABRA>
            void splitting_algorithm_builder<LABRA>::Set_StepUsual(STEPFKT const& s) { 
                algo.step1 = boost::shared_ptr<STEPFKT>(new STEPFKT()); 
                *algo.step1 = s; 
            }

            template <class LABRA>
            void splitting_algorithm_builder<LABRA>::Set_StepSpezial(STEPFKT const& s) { 
                algo.step2 = boost::shared_ptr<STEPFKT>(new STEPFKT()); 
                *algo.step2 = s; 
            }


            template <class LABRA>
            void splitting_algorithm_builder<LABRA>::Build_VarphiInvers(unsigned n) {

                //generate inverse homomorphism
                algo.VarphiInv = boost::shared_ptr<SPLITHOM>(new SPLITHOM());
                *algo.VarphiInv = homomorphism_generator<LABRA>(x,n);
            }


            template <class LABRA>
            void splitting_algorithm_builder<LABRA>::Build_FindOrbitRep1() {

              typename LABRA::SET_element_type omega(x);

              //generate function to calculate the minimal orbit representative
              algo.FindOrbitRep1 = boost::shared_ptr<CANFKT>(new CANFKT());
              *algo.FindOrbitRep1 = findOrbitRepresentativeStore<LABRA>(omega);
            }


            template <class LABRA>
            void splitting_algorithm_builder<LABRA>::Build_FindOrbitRep2() {

              typename LABRA::SET_element_type omega(x);

              //generate function to calculate the minimal orbit representative
              algo.FindOrbitRep2 = boost::shared_ptr<CANFKT>(new CANFKT());
              *algo.FindOrbitRep2 = boost::bind(findOrbitRepresentative<LABRA>,_2,omega,_1);
            }



            template <class LABRA>
            void splitting_algorithm_builder<LABRA>::Build_SmallerOrEqual(unsigned n) {

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
                algo.SmallerOrEqual = boost::shared_ptr<CMPFKT>(new CMPFKT());
                *algo.SmallerOrEqual = CompareYoungGroup<LABRA>(vset,vint);
            }


            template <class LABRA>
            typename splitting_algorithm_builder<LABRA>::Algorithm&
            splitting_algorithm_builder<LABRA>::operator()() {

                // build algorithm if everything is ready
                if ( 0 == algo.step1.get() || 0 == algo.step2.get() ) {
                    std::cerr <<"In Function splitting_algorithm_builder::operator()"<<std::endl;
                    std::cerr <<"Some VARIABLES have not yet been defined"<<std::endl;
                    exit(-1);
                }
                return algo;
            }

        } // end namespace stroll
    } // end namespace depthfirst
} // end namespace laddergame

#endif // SPLITTING_ALGORITHM_BUILDER_DEPTHFIRST_STROLL
