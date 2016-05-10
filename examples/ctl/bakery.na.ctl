#FAIL: (0)
AG((~pc<*0*><3> & ~pc<*0*><2> & ~pc<*0*><1> & ~pc<*0*><0>) ->
  AF(pc<*0*><3> & ~pc<*0*><2> & ~pc<*0*><1> & ~pc<*0*><0>))
#FAIL: (1)
AG((~pc<*1*><3> & ~pc<*1*><2> & ~pc<*1*><1> & ~pc<*1*><0>) ->
  AF(pc<*1*><3> & ~pc<*1*><2> & ~pc<*1*><1> & ~pc<*1*><0>))
#FAIL: (2) This property states that the initial state is a reset state.
# It fails because on exit from the loop L4-L8, j==2, and it does not
# change until L4 is reached again.
AG EF(~ticket<*0*><1> & ~ticket<*0*><0> &
      ~ticket<*1*><1> & ~ticket<*1*><0> & 
      ~choosing<*0*> & ~choosing<*1*> &
      ~pc<*0*><3> & ~pc<*0*><2> & ~pc<*0*><1> & ~pc<*0*><0> &
      ~j<*0*><1> & ~j<*0*><0> &
      ~pc<*1*><3> & ~pc<*1*><2> & ~pc<*1*><1> & ~pc<*1*><0> &
      ~j<*1*><1> & ~j<*1*><0>)
