#ifndef SIMPLE_LADDERGAME_HOMOMORPHISMS
#define SIMPLE_LADDERGAME_HOMOMORPHISMS


namespace laddergame {


        template <class T>
        T identity_function( T const& t) { return t; }

        template <class T>
        bool ReturnTrue(T const&) { return true; }

        template <class T, class S>
        bool ReturnTrue(T const&, S const&) { return true; }

        template <class T>
        void DoNothing(T const&) { return; }


        template <class LabelledBranching>
        class SimpleLaddergameHomomorphisms {

          public:

            typedef LabelledBranching                   LABRA;
            typedef typename LABRA::GROUP_element_type  GROUP_element_type;
            typedef typename LABRA::GROUP_element_type  SET_element_type_ul;
            typedef typename LABRA::GROUP_element_type  SET_element_type_ur;
            typedef typename LABRA::GROUP_element_type  SET_element_type_ll;
            typedef typename LABRA::GROUP_element_type  SET_element_type_lr;

        };

} // end namespace laddergame

#endif // SIMPLE_LADDERGAME_HOMOMORPHISMS
