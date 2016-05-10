#FAIL: (0)
AG(~(opcodeEx<2> | opcodeEx<1> | opcodeEx<0>) & ~(destEx<1> | destEx<0>) & ~bubbleEx ->
   AF(~regFile<*0*><3> & ~regFile<*0*><2> & ~regFile<*0*><1> & regFile<*0*><0>))
#FAIL: (1)
AG(~opcodeEx<2> & ~opcodeEx<1> & opcodeEx<0> & ~(destEx<1> | destEx<0>) & ~bubbleEx ->
   AF(~regFile<*0*><3> & ~regFile<*0*><2> & ~regFile<*0*><1> & regFile<*0*><0>))

#PASS: (2) if the instruction in the execution stage is "load 1 in
# Register 0" and the pipeline has no bubble in that stage, eventually
# the 1 will show up in the destination register.
AG(~opcodeEx<2> & opcodeEx<1> & ~opcodeEx<0> & ~(destEx<1> | destEx<0>) & ~bubbleEx ->
   AF(~regFile<*0*><3> & ~regFile<*0*><2> & ~regFile<*0*><1> & regFile<*0*><0>))

#PASS: (3) if the instruction in the execution stage is "load 1 in
# Register 0," then if eventually we get no bubble in the execution
# stage, then eventually the 1 shows up in the destination register.
# This property relaxes a bit the previous one.

AG((~opcodeEx<2> & ~opcodeEx<1> & opcodeEx<0> & ~(destEx<1> | destEx<0>)) ->
 (EF(~bubbleEx) -> EF(~regFile<*0*><3> & ~regFile<*0*><2> & ~regFile<*0*><1> & regFile<*0*><0>)))

#PASS: (4) it is always possible for the bubble in the execution stage to
# disappear.
AG EF ~bubbleEx
