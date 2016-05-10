#PASS: (0) The first two slots are always different.
AG((x<*0*><2> ^ x<*1*><2>) | 
   (x<*0*><1> ^ x<*1*><1>) |
   (x<*0*><0> ^ x<*1*><0>)
)

#PASS: (1) It is always possible to return to the initial permutation.
AG EF (
  ~x<*0*><2> & ~x<*0*><1> & ~x<*0*><0> & 
  ~x<*1*><2> & ~x<*1*><1> &  x<*1*><0> &
  ~x<*2*><2> &  x<*2*><1> & ~x<*2*><0> &
  ~x<*3*><2> &  x<*3*><1> &  x<*3*><0> &
   x<*4*><2> & ~x<*4*><1> & ~x<*4*><0> &
   x<*5*><2> & ~x<*5*><1> &  x<*5*><0> &
   x<*6*><2> &  x<*6*><1> & ~x<*6*><0> &
   x<*7*><2> &  x<*7*><1> &  x<*7*><0>
)

#PASS: (2)It is always possible to have 0 in the first slot.
AG EF (~x<*0*><2> & ~x<*0*><1> & ~x<*0*><0>)
