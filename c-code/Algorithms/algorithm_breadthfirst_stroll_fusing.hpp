#ifndef LADDERGAME_BREADTHFIRST_STROLL_FUSING_ALGORITHM
#define LADDERGAME_BREADTHFIRST_STROLL_FUSING_ALGORITHM

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

    namespace breadthfirst {

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
            class fusing_algorithm {

                typedef COMMUTATIVE_HOMOMORPHISM_SQUARE             SQUARE;
                typedef typename SQUARE::LABRA                      LABRA;
                typedef typename SQUARE::GROUP_element_type         GRELM;
                typedef typename SQUARE::SET_element_type_ul        SETELM1;
                typedef typename SQUARE::SET_element_type_ur        SETELM2;
                typedef typename SQUARE::SET_element_type_ll        SETELM3;
                typedef typename SQUARE::SET_element_type_lr        SETELM4;

              public: 

                typedef Range                                                               SET1RANGE;
                typedef boost::function< SET1RANGE(SETELM2 const&) >                        SPLITHOM;
                typedef boost::function< SETELM2(SETELM1 const&) >                          VARPHIHOM;
                typedef boost::function< GRELM(SETELM1 const&)>                             CANONIZER;
                typedef boost::function< GRELM(SETELM1 const&,LABRA const&)>                EASYCANON; 
                typedef boost::function< void(SETELM2 const&,GRELM const&) >                SETFUSELM;
                typedef boost::function< LABRA const&(GRELM const&) >                       GETSTAB;
                typedef boost::function< LABRA const&(GRELM const&,LABRA const&) >          EXTSTAB;
                typedef boost::function< bool(SETELM1 const&,SETELM1 const&) >              COMPARE; 
                typedef boost::function< void(SETELM2 const&,GRELM const&,LABRA const&) >   NEXTSTEP;

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
                                            LABRA const&    D1,
                                            LABRA&          D2,
                                            SPLITHOM&       VarphiInv,
                                            VARPHIHOM&      VarphiHom,
                                            CANONIZER&      FindCanon,
                                            EASYCANON&      FindOrbitRep,
                                            GETSTAB&        GetStabil,
                                            EXTSTAB&        ExtStabil,
                                            SETFUSELM&      SetFusElm,
                                            COMPARE&        SmallerOrEqual,
                                            STEPFKT&        NextStep    ) const;

                unsigned level;
            };


            template <class SQUARE, class RANGE>
            struct fusing_algorithm<SQUARE>::Functions {
                SPLITHOM&           VarphiInvers;
                VARPHIHOM&          VarphiHomomorphism;
                CANONIZER&          Canonizer;
                GETSTAB&            GetStabilizer;
                EXTSTAB&            ExtStabilizer;
                SETFUSELM&          SetFusingElmnt;
                COMPARE&            SmallerOrEqual;
                STEPFKT&            NextStep;
            };


            template <class SQUARE, class RANGE>
            struct fusing_algorithm<SQUARE>::Variables {
                SETELM1 const&      e1;
                SETELM2&            e2;
                GRELM const&        b1;
                GRELM&              b2;
                LABRA const&        C1;
                LABRA const&        C2;
                LABRA const&        D1;
                LABRA&              D2;
            };


            template <class SQUARE, class RANGE>
            void fusing_algorithm<SQUARE>::operator () ( Variables const& v, Functions& f ) const {

                (*this)(v.e1,v.e2,v.b1,v.b2,v.C1,v.C2,v.D1,v.D2,f.VarphiHom,f.FindOrbitRepConjugate,f.CheckCanonical,f.SmallerOrEqual,f.NextStep);
            }


            template <class SQUARE, class RANGE>
            void fusing_algorithm<SQUARE>::operator () (    SETELM1 const&  e1,
                                                            SETELM2&        e2,
                                                            GRELM const&    b1,
                                                            GRELM&          b2,
                                                            LABRA const&    C1,
                                                            LABRA const&    C2,
                                                            LABRA const&    D1,
                                                            LABRA&          D2,
                                                            VARPHIHOM&      VarphiHom,
                                                            CANFKTCONJ&     FindOrbitRepConjugate,
                                                            CHECKCAN&       CheckCanonical,
                                                            COMPARE&         SmallerOrEqual,
                                                            STEPFKT&        NextStep    ) const {


                //very fast check; if groups have same size, the image must be canonical
                if ( C1.size() == C2.size() ) {
                    e2 = VarphiHom(e1);
                    b2 = b1;
                    D2 = D1;
                    NextStep(e2,b2,D2);
                }

                else {
/*
                    // x = argmin_{x \in b1*C2*~b1} e1*x
                    GRELM x = EasyCanonConj(e1,C2,b1);

                    //quick check; must be true for all canonical representatives
                    if ( false == SmallerOrEqual(e1,e1<<x) )
                        return;   

                    e2 = VarphiHom(e1);
                    D2 = D1;
                    b2 = b1;

                    //calculate new stabilizer and fusing element of representative
                    bool result = CheckCanonical(e1,D2);

                    if ( true == result )
                        NextStep(e2,b2,D2);                
*/


                    using boost::container::list;

                    GRELM       fus_el;
                    SETELM1     can_rep(e1);
                    list<GRELM> rep_list;
                    list<GRELM> can_list;

 
                    //check if candidate is smallest orbit representative 
                    //in the preimage of phi(e1)
                    e2 = VarphiHomomorphism(e1);
                    foreach(SETELM1 const& o, VarphiInvers(e2) ) {  

                        SETELM1 p = o<<b1;
                        GRELM c = FindOrbitRep(p,C2);
                        p == p<<c;
                        //if this is true, then o is not in the orbit
                        //of a1 under the action of B.
                        //Be carefull to use the right compare Function!
                        if ( !leq1(p,a1) )
                            continue;
                        p = a1<<~c*~b1;
                        GRELM d = Canonizer(p);
                        rep_list.emplace_back(h1);
                        can_list.emplace_back(c);

                        //check, if a smaller orbit representative is found; 
                        //if not, go ahead and search for smallest
                        if ( !leq2(e1,h1*c) ) 
                            return;
                    }
/*
                    if ( leq2(can_rep,e1) && leq2(e1,can_rep) ) {

                        //calculate new stabilizer of smallest representative 
                        LABRA C2 = GetStabilizer(can_rep*fus_el);

                        foreach(GRELM& c, rep_list ) {

                            //extend Stabilizer, if it is in same orbit
                            if ( leq2(g*c,g*fus_el) )
                                extstab(~c*fus_el,C2);

                        }

                        step(g*fus_el,F);

                    }
*/
                    fuse(,fus_el);

                }

            }

        } // end namespace stroll

    } // end namespace breadthfirst

} // end namespace laddergame

#endif // LADDERGAME_BREADTHFIRST_STROLL_FUSING_ALGORITHM
