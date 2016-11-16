#ifndef LADDERGAME_DEPTHFIRST_STROLL_SPLITTING_ALGORITHM
#define LADDERGAME_DEPTHFIRST_STROLL_SPLITTING_ALGORITHM

#include <boost/function.hpp>
#include <iostream>




// G is a Group
// B < G    ( "<" means subgroup )
// A1 < A2 < G, A_k < G
//
// E_1 = A_1 \cap A_k (intersection of A_1 and A_k)
// E_2 = A_2 \cap A_k
//
// Group G operates on every set of rightcosets
// A_1/G, A_2/G, E_1/G, E_2/G by rightmultiplication
// Homomorphisms of Group Actions:
// \varphi: E_1 \ G \longrightarrow E_2 \ G;   \varphi(E_1g) = E_2g   \forall g \in G
// \psi_1:  E_1 \ G \longrightarrow A_1 \ G;    \psi_1(E_1g) = A_1g   \forall g \in G
// \psi_2:  E_2 \ G \longrightarrow A_2 \ G;    \psi_2(E_2g) = A_2g   \forall g \in G
// \nu:     A_1 \ G \longrightarrow A_2 \ G;       \nu(A_1g) = A_2g   \forall g \in G
//
//                \varphi
//      E_1 \ G   ------>   E_2 \ G
//
//          |                   |  
//          |                   |  
//       \psi_1               \psi_2
//          |                   |  
//          V      \nu          V
//      A_1 \ G  ------->   A_2 \ G                
//
// is a commutative diagram
// so that \psi_2 \circ \varphi = \nu \circ \psi_1
//
// a1 \in A_1 \ G
// a2 \in A_2 \ G
// e1 \in E_1 \ G
// e2 \in E_2 \ G
// b1  \in B
// b2  \in B
//
// a1 = \psi_1(e1*b1)
// a2 = \psi_2(e2*b2)
// a2 = \nu(a1)
// e2 = \varphi(e1)
//
// D1 = Stabilizer of E_1*e1 in B ( E_1*e1 is coset \in E_1 \ G )
// D2 = Stabilizer of E_2*e2 in B ( E_2*e2 is coset \in E_2 \ G )
// C1 = Stabilizer of A_1*a1 in B ( A_1*a1 is coset \in A_1 \ G )
// C2 = Stabilizer of A_2*a2 in B ( A_2*a2 is coset \in A_2 \ G )
//
//
// COMMUTATIVE_HOMOMORPHISM_SQUARE::SET_element_type_ul = E_1 \ G
// COMMUTATIVE_HOMOMORPHISM_SQUARE::SET_element_type_ur = E_2 \ G
// COMMUTATIVE_HOMOMORPHISM_SQUARE::SET_element_type_ll = A_1 \ G
// COMMUTATIVE_HOMOMORPHISM_SQUARE::SET_element_type_lr = A_2 \ G


namespace laddergame {

    namespace depthfirst {

        namespace stroll {



            namespace detail {

                template <class T>
                struct defaultRange {

                    typedef typename T::SET_element_type_ul                                     Value;
                    typedef boost::forward_traversal_tag                                        Traversal;
                    typedef typename T::SET_element_type_ul                                     Reference;
                    typedef std::ptrdiff_t                                                      Difference;
                    typedef boost::any_range<Value,Traversal,Reference,Difference>              type;

                };

            }   // end namespace detail



            template <class COMMUTATIVE_HOMOMORPHISM_SQUARE,
                      class Range = typename detail::defaultRange<COMMUTATIVE_HOMOMORPHISM_SQUARE>::type >
            class splitting_algorithm {

                typedef COMMUTATIVE_HOMOMORPHISM_SQUARE                                     SQUARE;
                typedef typename COMMUTATIVE_HOMOMORPHISM_SQUARE::LABRA                     LABRA;
                typedef typename COMMUTATIVE_HOMOMORPHISM_SQUARE::GROUP_element_type        GRELM;
                typedef typename COMMUTATIVE_HOMOMORPHISM_SQUARE::SET_element_type_ul       SETELM1;
                typedef typename COMMUTATIVE_HOMOMORPHISM_SQUARE::SET_element_type_ur       SETELM2;
                typedef typename COMMUTATIVE_HOMOMORPHISM_SQUARE::SET_element_type_ll       SETELM3;
                typedef typename COMMUTATIVE_HOMOMORPHISM_SQUARE::SET_element_type_lr       SETELM4;

              public: 

                typedef Range                                                               RANGE;
                typedef boost::function< SETELM3(SETELM1 const&) >                          PSI1;
                typedef boost::function< RANGE(SETELM2 const&) >                            SPLITHOM;
                typedef boost::function< GRELM(SETELM1 const&,LABRA const&)>                CANFKT; 
                typedef boost::function< bool(SETELM3 const&,SETELM3 const&) >              CMPFKT; 
                typedef boost::function< void(SETELM1 const&,LABRA&) >                      REDUKFT;
                typedef boost::function< bool(SETELM1 const&, GRELM const&) >               TESTFKT; 
                typedef boost::function< void(SETELM1 const&,GRELM const&,LABRA const&) >   STEPFKT;

                typedef void                                                                result_type;

                struct  Functions;
                struct  Variables;

                inline void operator() (Variables const& v, Functions& f, unsigned l) { level = l; (*this)(v,f); };
                inline void operator() (Variables const&, Functions&) const;
                inline void operator() (    SETELM1&        e1,
                                            SETELM2 const&  e2,
                                            SETELM3 const&  a1,
                                            GRELM&          b1,
                                            GRELM const&    b2,
                                            LABRA const&    C1,
                                            LABRA const&    C2,
                                            LABRA&          D1,
                                            LABRA const&    D2,
                                            PSI1&           Psi1,
                                            SPLITHOM&       VarphiInv,
                                            CANFKT&         FindOrbitRep1,
                                            CANFKT&         FindOrbitRep2,
                                            TESTFKT&        test,
                                            CMPFKT&         SmallerOrEqual,
                                            REDUKFT&        ReduceStab,
                                            STEPFKT&        step1,
                                            STEPFKT&        step2      ) const;

                unsigned level;

            };



            template <class SQUARE, class RANGE>
            struct splitting_algorithm<SQUARE,RANGE>::Functions {
                PSI1&           Psi1;
                SPLITHOM&       VarphiInv;
                CANFKT&         FindOrbitRep1;
                CANFKT&         FindOrbitRep2;
                TESTFKT&        test;
                CMPFKT&         SmallerOrEqual;
                REDUKFT&        ReduceStab;
                STEPFKT&        step1;
                STEPFKT&        step2;
            };


            template <class SQUARE, class RANGE>
            struct splitting_algorithm<SQUARE,RANGE>::Variables {
                SETELM1&        e1;
                SETELM2 const&  e2;
                SETELM3 const&  a1;
                GRELM&          b1;
                GRELM const&    b2;
                LABRA const&    C1;
                LABRA const&    C2;
                LABRA&          D1;
                LABRA const&    D2;
            };



            template <class SQUARE, class RANGE>
            void splitting_algorithm<SQUARE,RANGE>::operator () ( Variables const& v, Functions& f ) const {

                (*this)(v.e1,v.e2,v.a1,v.b1,v.b2,v.C1,v.C2,v.D1,v.D2,f.Psi1,f.VarphiInv,f.FindOrbitRep1,f.FindOrbitRep2,f.test,f.SmallerOrEqual,f.ReduceStab,f.step1,f.step2);
            }


            template <class SQUARE, class RANGE>
            void splitting_algorithm<SQUARE,RANGE>::operator () (   SETELM1&        e1,
                                                                    SETELM2 const&  e2,
                                                                    SETELM3 const&  a1,
                                                                    GRELM&          b1,
                                                                    GRELM const&    b2,
                                                                    LABRA const&    C1,
                                                                    LABRA const&    C2,
                                                                    LABRA&          D1,
                                                                    LABRA const&    D2,
                                                                    PSI1&           Psi1,
                                                                    SPLITHOM&       VarphiInv,
                                                                    CANFKT&         FindOrbitRep1,
                                                                    CANFKT&         FindOrbitRep2,
                                                                    TESTFKT&        test,
                                                                    CMPFKT&         SmallerOrEqual,
                                                                    REDUKFT&        ReduceStab,
                                                                    STEPFKT&        step1,
                                                                    STEPFKT&        step2      ) const 
            {


                foreach(e1, VarphiInv(e2) ) {

                    if ( false == test(e1,b2) )
                        continue;

                    else if ( C1.size() != C2.size() ) {

                        // check:   e1 = min_{x \in D2} e1*x 
                        GRELM d = FindOrbitRep2(e1,D2);

                        if ( !SmallerOrEqual(e1,e1<<d) ) 
                          continue;

                        // check:   a1 = min_{x \in C2} e1*b2*x 
                        b1 = b2*FindOrbitRep1(e1*b2,C2);
                    }

                    else    // C1.size() == C2.size()
                        b1 = b2;

                    // a1 < Psi1(e1*b1) ?
                    if ( false == SmallerOrEqual(Psi1(e1<<b1),a1) ) 
                        continue;

                    // calculate D1, the stabilizer of e1 ( is a subgroup of D2 )
                    D1 = D2;
//                    if ( C1.size() != C2.size() )
                        ReduceStab(e1,D1);

                    // Psi1(e1*b1) < a1 ?
                    if ( false == SmallerOrEqual(a1,Psi1(e1<<b1)) )
                        step2(e1,b1,D1);

                    // a1 == Psi1(e1*b1)
                    else    
                        step1(e1,b1,D1);

                }

            }

        } // end namespace stroll
    
    } // end namespace depthfirst

} // end namespace laddergame

#endif // LADDERGAME_DEPTHFIRST_STROLL_SPLITTING_ALGORITHM

