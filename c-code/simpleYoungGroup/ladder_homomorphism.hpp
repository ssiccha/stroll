#ifndef LADDER_HOMOMORPHISM_DEPTHFIRST_HPP
#define LADDER_HOMOMORPHISM_DEPTHFIRST_HPP


#include <string>
#include <cstdio>
#include <utility>
#include <boost/shared_ptr.hpp>
#include <boost/container/vector.hpp>
#include <boost/shared_container_iterator.hpp>
#include <boost/iterator/transform_iterator.hpp>





namespace laddergame {

    namespace united {

    using std::string;
    using boost::container::vector;


    string GetCycleInitString(unsigned i, unsigned j) {
      string initstring;
      char zahl[8];
      initstring.push_back('{');
      initstring.push_back('(');
      for (unsigned k=i; k<=j; ++k) {
        sprintf(zahl,"%d",k);
        initstring.append(zahl);
        if ( k < j )
          initstring.push_back(',');
      }
      initstring.push_back(')');
      initstring.push_back('}');
      return initstring;
    }




    


    template <class LABRA>
    struct homomorphism_generator {

      private:

          typedef typename LABRA::GROUP_element_type    GROUPELM;
          typedef vector<GROUPELM>                      Container;
          struct Function;
          typedef typename boost::shared_container_iterator<Container>  shared_iterator;
          typedef boost::transform_iterator<Function, shared_iterator>  iterator;
          typedef std::pair<iterator,iterator>                          RANGE;

          struct Function {
            typedef GROUPELM result_type;
            Function() : g() {}
            Function(GROUPELM const& h) : g(h) {}
            GROUPELM operator()(GROUPELM const& h) const {
              return h*g;
            }
            GROUPELM const g; 
          };

   
      public:

          typedef RANGE                                                 result_type;
          

          homomorphism_generator(unsigned i, unsigned j) : pcosets(new Container) {
              GROUPELM g;
              GROUPELM c(GetCycleInitString(i,j).c_str());
              for (unsigned k=i; k<=j; ++k) {
                pcosets->push_back(g);
                g = g*c;
              }    
          }

          
          RANGE operator()(GROUPELM const& g) {
            shared_iterator sharedit1(pcosets->begin(),pcosets);
            shared_iterator sharedit2(pcosets->end(),pcosets);
            Function f1(g);
            Function f2(g);
            iterator it1(sharedit1,f1);
            iterator it2(sharedit2,f2);
            return RANGE(it1,it2);
          }

      
      private:
    
          boost::shared_ptr<Container> pcosets;

    };

    } // end namespace united

} // end namespace laddergame


#endif // LADDER_HOMOMORPHISM_DEPTHFIRST_HPP
