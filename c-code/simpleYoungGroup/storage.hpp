#ifndef STORAGE_SIMPLE_LADDERGAME_ALGORITHM
#define STORAGE_SIMPLE_LADDERGAME_ALGORITHM


#include <iostream>
#include <simpleYoungGroup/simpleLaddergameHomomorphisms.hpp>
#include <boost/shared_ptr.hpp>

#include <Algorithms/algorithm_depthfirst_simple_fusing.hpp>
#include <Algorithms/algorithm_depthfirst_simple_splitting.hpp>
#include <Algorithms/algorithm_depthfirst_simple_laststep.hpp>
#include <Algorithms/algorithm_depthfirst_stroll_splitting.hpp>
#include <Algorithms/algorithm_depthfirst_stroll_fusing.hpp>


namespace laddergame {



            template <class _LABRA>
            class storage {

                typedef _LABRA                                                                          LABRA;
                typedef SimpleLaddergameHomomorphisms<LABRA>                                            SQUARE;

                typedef typename SQUARE::GROUP_element_type                                             GRELM;
                typedef typename SQUARE::SET_element_type_ul                                            SETELM1;
                typedef typename SQUARE::SET_element_type_ur                                            SETELM2;
                typedef typename SQUARE::SET_element_type_ll                                            SETELM3;
                typedef typename SQUARE::SET_element_type_lr                                            SETELM4;

                typedef boost::shared_ptr<int>                                                          PINT;
                typedef boost::shared_ptr<GRELM>                                                        PGRELM;
                typedef boost::shared_ptr<LABRA>                                                        PLABRA;
                typedef boost::shared_ptr<SETELM1>                                                      PSETELM1;
                typedef boost::shared_ptr<SETELM2>                                                      PSETELM2;
                typedef boost::shared_ptr<SETELM3>                                                      PSETELM3;
                typedef boost::shared_ptr<SETELM4>                                                      PSETELM4;

              public:

                typedef typename depthfirst::simple::lastFusingStep_algorithm<SQUARE>::Variables        vartype1;
                typedef typename depthfirst::simple::fusing_algorithm<SQUARE>::Variables                vartype2;
                typedef typename depthfirst::simple::splitting_algorithm<SQUARE>::Variables             vartype3;
                typedef typename depthfirst::stroll::splitting_algorithm<SQUARE>::Variables             vartype4;
                typedef typename depthfirst::stroll::fusing_algorithm<SQUARE>::Variables                vartype5;


                inline storage();
                inline storage(LABRA&, LABRA&);
                inline storage(PLABRA const&, PLABRA const&);

                inline void     Set_e1(SETELM1 const& l) { if ( NULL == pe1.get() ) pe1.reset(new SETELM1(l)); else *pe1 = l; }
                inline void     Set_e2(SETELM2 const& l) { if ( NULL == pe2.get() ) pe2.reset(new SETELM2(l)); else *pe2 = l; }
                inline void     Set_a1(SETELM3 const& l) { if ( NULL == pa1.get() ) pa1.reset(new SETELM3(l)); else *pa1 = l; }
                inline void     Set_a2(SETELM4 const& l) { if ( NULL == pa2.get() ) pa2.reset(new SETELM4(l)); else *pa2 = l; }
                inline void     Set_b1(GRELM const& l)   { if ( NULL == pb1.get() ) pb1.reset(new GRELM(l)); else *pb1 = l; }
                inline void     Set_b2(GRELM const& l)   { if ( NULL == pb2.get() ) pb2.reset(new GRELM(l)); else *pb2 = l; }
                inline void     Set_C1(LABRA const& l)   { if ( NULL == pC1.get() ) pC1.reset(new LABRA(l)); else *pC1 = l; }
                inline void     Set_C2(LABRA const& l)   { if ( NULL == pC2.get() ) pC2.reset(new LABRA(l)); else *pC2 = l; }
                inline void     Set_D1(LABRA const& l)   { if ( NULL == pD1.get() ) pD1.reset(new LABRA(l)); else *pD1 = l; }
                inline void     Set_D2(LABRA const& l)   { if ( NULL == pD2.get() ) pD2.reset(new LABRA(l)); else *pD2 = l; }
                inline void     Set_result(int const& l) { if ( NULL == presult.get() ) presult.reset(new int(l)); else *presult = l; }

                inline void     Set_e1(PSETELM1 const& l) { pe1 = l; }
                inline void     Set_e2(PSETELM2 const& l) { pe2 = l; }
                inline void     Set_a1(PSETELM3 const& l) { pa1 = l; }
                inline void     Set_a2(PSETELM4 const& l) { pa2 = l; }
                inline void     Set_b1(PGRELM const& l) { pb1 = l; }
                inline void     Set_b2(PGRELM const& l) { pb2 = l; }
                inline void     Set_C1(PLABRA const& l) { pC1 = l; }
                inline void     Set_C2(PLABRA const& l) { pC2 = l; }
                inline void     Set_D1(PLABRA const& l) { pD1 = l; }
                inline void     Set_D2(PLABRA const& l) { pD2 = l; }
                inline void     Set_result(PINT const& l) { presult = l; }

                inline SETELM1& Get_e1() { if ( NULL == pe1.get() ) pe1.reset(new SETELM1); return *pe1; }
                inline SETELM1& Get_e2() { if ( NULL == pe2.get() ) pe2.reset(new SETELM2); return *pe2; }
                inline SETELM1& Get_a1() { if ( NULL == pa1.get() ) pa1.reset(new SETELM3); return *pa1; }
                inline SETELM1& Get_a2() { if ( NULL == pa2.get() ) pa2.reset(new SETELM4); return *pa2; }
                inline GRELM&   Get_b1() { if ( NULL == pb1.get() ) pb1.reset(new GRELM); return *pb1; }
                inline GRELM&   Get_b2() { if ( NULL == pb2.get() ) pb2.reset(new GRELM); return *pb2; }
                inline LABRA&   Get_C1() { if ( NULL == pC1.get() ) FailFkt(); return *pC1;}
                inline LABRA&   Get_C2() { if ( NULL == pC2.get() ) FailFkt(); return *pC2;}
                inline LABRA&   Get_D1() { if ( NULL == pD1.get() ) FailFkt(); return *pD1;}
                inline LABRA&   Get_D2() { if ( NULL == pD2.get() ) FailFkt(); return *pD2;}
                inline int&     Get_result() { if ( NULL == presult.get() ) presult.reset(new int); return *presult; }

                inline operator vartype1 ();
                inline operator vartype2 ();
                inline operator vartype3 ();
                inline operator vartype4 ();
                inline operator vartype5 ();

              private:

                inline void FailFkt()  { std::cout <<"returning uninitialized value is impossible (in class storage)"<<std::endl; exit(-1); }

                PSETELM1    pe1;
                PSETELM2    pe2;
                PSETELM3    pa1;
                PSETELM4    pa2;
                PGRELM      pb1;
                PGRELM      pb2;
                PLABRA      pC1;
                PLABRA      pC2;
                PLABRA      pD1;
                PLABRA      pD2;
                PINT        presult;

            };


            template <class LABRA>
            storage<LABRA>::storage(LABRA& C1, LABRA& C2)
                :   pe1()
                ,   pe2()
                ,   pa1()
                ,   pa2()
                ,   pb1()
                ,   pb2() 
                ,   pC1(new LABRA(C1))
                ,   pC2(new LABRA(C2)) 
                ,   pD1()
                ,   pD2() 
                ,   presult() {}


            template <class LABRA>
            storage<LABRA>::storage(PLABRA const& C1, PLABRA const& C2)
                :   pe1()
                ,   pe2()
                ,   pa1()
                ,   pa2()
                ,   pb1()
                ,   pb2() 
                ,   pC1(C1)
                ,   pC2(C2)
                ,   pD1()
                ,   pD2()
                ,   presult() {}


            template <class LABRA>
            storage<LABRA>::storage()
                :   pe1()
                ,   pe2()
                ,   pa1()
                ,   pa2()
                ,   pb1()
                ,   pb2() 
                ,   pC1()
                ,   pC2()
                ,   pD1()
                ,   pD2()
                ,   presult() {}


            template <class LABRA>
            storage<LABRA>::operator
            typename storage<LABRA>::vartype1 () {
                vartype1 var = {Get_a2(),Get_b1(),Get_b2(),Get_C2()};
                return var;
            }

            template <class LABRA>
            storage<LABRA>::operator
            typename storage<LABRA>::vartype2 () {
                vartype2 var = {Get_e1(),Get_e2(),Get_b1(),Get_b2(),Get_C1(),Get_C2()};
                return var;
            }

            template <class LABRA>
            storage<LABRA>::operator
            typename storage<LABRA>::vartype3 () {
                vartype3 var = {Get_e1(),Get_e2(),Get_a1(),Get_b1(),Get_b2(),Get_C1(),Get_C2()};
                return var;
            }

            template <class LABRA>
            storage<LABRA>::operator
            typename storage<LABRA>::vartype4 () {
                vartype4 var = {Get_e1(),Get_e2(),Get_a1(),Get_b1(),Get_b2(),Get_C1(),Get_C2(),Get_D1(),Get_D2()};
                return var;
            }

            template <class LABRA>
            storage<LABRA>::operator
            typename storage<LABRA>::vartype5 () {
                vartype5 var = {Get_e1(),Get_e2(),Get_b1(),Get_b2(),Get_C1(),Get_C2(),Get_D1(),Get_D2()};
                return var;
            }


} // end namespace laddergame

#endif // STORAGE_SIMPLE_LADDERGAME_ALGORITHM

