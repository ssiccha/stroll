#ifndef STAIR_CONNECTOR_DEPTHFIRST_SIMPLE_LADDERGAME
#define STAIR_CONNECTOR_DEPTHFIRST_SIMPLE_LADDERGAME

#include <boost/function.hpp>
#include <boost/bind.hpp>

#include <simpleYoungGroup/function_builder_depthfirst_simple_splitting.hpp>
#include <simpleYoungGroup/function_builder_depthfirst_simple_fusing.hpp>
#include <simpleYoungGroup/function_builder_depthfirst_simple_lastfusing.hpp>
#include <simpleYoungGroup/function_builder_depthfirst_stroll_splitting.hpp>
#include <simpleYoungGroup/function_builder_depthfirst_stroll_fusing.hpp>
#include <simpleYoungGroup/storage.hpp>


namespace laddergame {



            template <class _LABRA> 
            class stair_connector {

                typedef _LABRA                                                      LABRA;
                typedef typename LABRA::GROUP_element_type                          GRELM;
                typedef boost::function<void()>                                     TASK;
                typedef storage<LABRA>                                              STORAGE;
                typedef depthfirst::simple::lastfusing_algorithm_builder<LABRA>     BUILDER1;
                typedef depthfirst::simple::fusing_algorithm_builder<LABRA>         BUILDER2;
                typedef depthfirst::simple::splitting_algorithm_builder<LABRA>      BUILDER3;
                typedef depthfirst::stroll::fusing_algorithm_builder<LABRA>         BUILDER4;
                typedef depthfirst::stroll::splitting_algorithm_builder<LABRA>      BUILDER5;

              public:

                void operator()(BUILDER1& lastfuseBuild,GRELM const& e, GRELM const& b) {
                    STORAGE& var = lastfuseBuild.Get_Variables();
                    var.Set_e1(e);
                    var.Set_b1(b);
                    lastfuseBuild()();
                }

                void operator()(BUILDER2& fuseBuild,GRELM const& e, GRELM const& b) {
                    STORAGE& var = fuseBuild.Get_Variables();
                    var.Set_e1(e);
                    var.Set_b1(b);
                    fuseBuild()();
                }

                void operator()(BUILDER3& splitBuild,GRELM const& e, GRELM const& b) {
                    STORAGE& var = splitBuild.Get_Variables();
                    var.Set_e2(e);
                    var.Set_b2(b);
                    splitBuild()();
                }

                void operator()(BUILDER1& lastfuseBuild,GRELM const& e, GRELM const& b, LABRA const& stab) {
                    STORAGE& var = lastfuseBuild.Get_Variables();
                    var.Set_e1(e);
                    var.Set_b1(b);
                    var.Set_D1(stab);
                    lastfuseBuild()();
                }

                void operator()(BUILDER4& fuseBuild,GRELM const& e, GRELM const& b, LABRA const& stab) {
                    STORAGE& var = fuseBuild.Get_Variables();
                    var.Set_e1(e);
                    var.Set_b1(b);
                    var.Set_D1(stab);
                    fuseBuild()();
                }

                void operator()(BUILDER5& splitBuild,GRELM const& e, GRELM const& b, LABRA const& stab) {
                    STORAGE& var = splitBuild.Get_Variables();
                    var.Set_e2(e);
                    var.Set_b2(b);
                    var.Set_D2(stab);
                    splitBuild()();
                }

            };



} // end namespace laddergame



#endif // STAIR_CONNECTOR_DEPTHFIRST_SIMPLE_LADDERGAME
