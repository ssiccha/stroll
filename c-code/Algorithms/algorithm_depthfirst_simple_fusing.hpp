#ifndef LADDERGAME_DEPTHFIRST_SIMPLE_FUSING_ALGORITHM
#define LADDERGAME_DEPTHFIRST_SIMPLE_FUSING_ALGORITHM

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

        namespace simple {


            template <class COMMUTATIVE_HOMOMORPHISM_SQUARE>
            class fusing_algorithm {
    
                typedef typename COMMUTATIVE_HOMOMORPHISM_SQUARE::LABRA                     LABRA;
                typedef typename COMMUTATIVE_HOMOMORPHISM_SQUARE::GROUP_element_type        GRELM;
                typedef typename COMMUTATIVE_HOMOMORPHISM_SQUARE::SET_element_type_ul       SETELM1;
                typedef typename COMMUTATIVE_HOMOMORPHISM_SQUARE::SET_element_type_ur       SETELM2;
                typedef typename COMMUTATIVE_HOMOMORPHISM_SQUARE::SET_element_type_ll       SETELM3;
                typedef typename COMMUTATIVE_HOMOMORPHISM_SQUARE::SET_element_type_lr       SETELM4;

              public: 

                typedef boost::function< SETELM2(SETELM1 const&) >                          VARPHIHOM;
                typedef boost::function< GRELM(SETELM1 const&,LABRA const&,GRELM const&)>   CANFKTCONJ; 
                typedef boost::function< bool(SETELM1 const&,SETELM1 const&) >              CMPFKT; 
                typedef boost::function< void(SETELM2&,GRELM&) >                            STEPFKT;

                typedef void                                                                result_type;

                struct  Functions;
                struct  Variables;

                inline void operator() (Variables const& v, Functions& f, unsigned l) { level = l; (*this)(v,f); };
                inline void operator() (Variables const&, Functions&) const;
                inline void operator() (    SETELM1 const&  e1,
                                            SETELM2&        e2,
                                            GRELM const&    b1,
                                            GRELM&          b2,
                                            LABRA const&    C1,
                                            LABRA const&    C2,
                                            VARPHIHOM&      VarphiHom,
                                            CANFKTCONJ&     FindOrbitRepConjugate,
                                            CMPFKT&         SmallerOrEqual,
                                            STEPFKT&        NextStep    ) const;

                unsigned level;
            };


            template <class SQUARE>
            struct fusing_algorithm<SQUARE>::Functions {
                VARPHIHOM&          VarphiHom;
                CANFKTCONJ&         FindOrbitRepConjugate;
                CMPFKT&             SmallerOrEqual;
                STEPFKT&            NextStep;
            };


            template <class SQUARE>
            struct fusing_algorithm<SQUARE>::Variables {
                SETELM1 const&      e1;
                SETELM2&            e2;
                GRELM const&        b1;
                GRELM&              b2;
                LABRA const&        C1;
                LABRA const&        C2;
            };


            template <class SQUARE>
            void fusing_algorithm<SQUARE>::operator () ( Variables const& v, Functions& f ) const {

                (*this)(v.e1,v.e2,v.b1,v.b2,v.C1,v.C2,f.VarphiHom,f.FindOrbitRepConjugate,f.SmallerOrEqual,f.NextStep);
            }


            template <class SQUARE>
            void fusing_algorithm<SQUARE>::operator () (    SETELM1 const&  e1,
                                                            SETELM2&        e2,
                                                            GRELM const&    b1,
                                                            GRELM&          b2,
                                                            LABRA const&    C1,
                                                            LABRA const&    C2,
                                                            VARPHIHOM&      VarphiHom,
                                                            CANFKTCONJ&     FindOrbitRepConjugate,
                                                            CMPFKT&         SmallerOrEqual,
                                                            STEPFKT&        NextStep    ) const {

                e2 = VarphiHom(e1);
                b2 = b1;

                if ( C1.size() == C2.size() ) 
                    NextStep(e2,b2);

                else {

                    // x = argmin_{x \in b1*C2*~b1} e1*x
                    GRELM x = FindOrbitRepConjugate(e1,C2,b1);
                
                    if ( true == SmallerOrEqual(e1,e1<<x) )
                        NextStep(e2,b2);                
                }
            }
    
        } // end namespace simple

    } // end namespace depthfirst

} // end namespace laddergame

#endif // LADDERGAME_DEPTHFIRST_SIMPLE_FUSING_ALGORITHM
