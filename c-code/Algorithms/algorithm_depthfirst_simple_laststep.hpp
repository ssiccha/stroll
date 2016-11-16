#ifndef LADDERGAME_DEPTHFIRST_SIMPLE_LASTFUSING_ALGORITHM
#define LADDERGAME_DEPTHFIRST_SIMPLE_LASTFUSING_ALGORITHM

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
//
// given that this is the last step, A_2 = A_k :
// E_1 = A_1 \cap A_k = A_1 ( A_1 is subgroup of A_2)
// E_2 = A_2 \cap A_k = A_2
// and
// \psi_1 = \psi_2 = id
// \nu = \varphi
// therefore
// a1 = e1*b1
// a2 = e2
// => a1*b1 = a1 => b1 \in C_2 (Stabilizer of A_k in B)

namespace laddergame {

    namespace depthfirst {

        namespace simple {


            template <class COMMUTATIVE_HOMOMORPHISM_SQUARE>
            class lastFusingStep_algorithm {

                typedef COMMUTATIVE_HOMOMORPHISM_SQUARE                                     SQUARE;
                typedef typename COMMUTATIVE_HOMOMORPHISM_SQUARE::LABRA                     LABRA;
                typedef typename COMMUTATIVE_HOMOMORPHISM_SQUARE::GROUP_element_type        GRELM;
                typedef typename COMMUTATIVE_HOMOMORPHISM_SQUARE::SET_element_type_ul       SETELM1;
                typedef typename COMMUTATIVE_HOMOMORPHISM_SQUARE::SET_element_type_ur       SETELM2;
                typedef typename COMMUTATIVE_HOMOMORPHISM_SQUARE::SET_element_type_ll       SETELM3;
                typedef typename COMMUTATIVE_HOMOMORPHISM_SQUARE::SET_element_type_lr       SETELM4;

              public: 

                typedef boost::function< bool(SETELM4 const&,SETELM4 const&) >              CMPFKT; 
                typedef boost::function< void(GRELM const&,LABRA&) >                        EXPANDSTAB;

                typedef void                                                                result_type;

                struct  Functions;
                struct  Variables;


                inline void operator() (Variables const&, Functions&) const;
                inline void operator() (    SETELM4 const&  a2,
                                            GRELM const&    b1,
                                            GRELM&          b2,
                                            LABRA&          C2,
                                            CMPFKT&         SmallerOrEqual,
                                            EXPANDSTAB&     ExpandStab ) const;

            };


            template <class SQUARE>
            struct lastFusingStep_algorithm<SQUARE>::Functions {
                CMPFKT&         SmallerOrEqual;
                EXPANDSTAB&     ExpandStab;
            };


            template <class SQUARE>
            struct lastFusingStep_algorithm<SQUARE>::Variables {
                SETELM4 const&  a2;
                GRELM const&    b1;
                GRELM&          b2;
                LABRA&          C2;
            };


            template <class SQUARE>
            void lastFusingStep_algorithm<SQUARE>::operator() (Variables const& v, Functions& f) const {

                (*this)(v.a2,v.b1,v.b2,v.C2,f.SmallerOrEqual,f.ExpandStab);
            }


            template <class SQUARE>
            void lastFusingStep_algorithm<SQUARE>::operator() (     SETELM4 const&  a2,
                                                                GRELM const&    b1,
                                                                GRELM&          b2,
                                                                LABRA&          C2,
                                                                CMPFKT&         SmallerOrEqual,
                                                                EXPANDSTAB&     ExpandStab ) const {

                if ( SmallerOrEqual(a2<<~b2*b1,a2) && SmallerOrEqual(a2,a2<<~b2*b1) )
                  ExpandStab(~b2*b1,C2);

                //Attention: b2 must be saved to make this algorithm work!
                else
                  b2 = b1;
            }
    
        } // end namespace simple

    } // end namespace depthfirst

} // end namespace laddergame

#endif // LADDERGAME_DEPTHFIRST_SIMPLE_LASTFUSING_ALGORITHM
