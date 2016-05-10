#PASS: (0) If no branch is taken, eventually the PC will attain any even value;
# for instance, 11110.
AG AF(
  ~IR<11> & IR<10> & ~IR<9> | PC<4> & PC<3> & PC<2> & PC<1> & ~PC<0>
)

#PASS: (1) The PC may attain any even value; for instance, 11110.
AG EF(
  PC<4> & PC<3> & PC<2> & PC<1> & ~PC<0>
)

#PASS: (2)
#A register only changes if it is the destination of an instruction.
AG((~Registers<*1*><4> & Registers<*1*><3> & ~Registers<*1*><2> & Registers<*1*><1> & ~Registers<*1*><0>) ->
   ~E ~(regRegALU & (~adFld3<1> & adFld3<0>) | ~regRegALU & (~adFld2<1> & adFld2<0>)) U
      ~(~Registers<*1*><4> & Registers<*1*><3> & ~Registers<*1*><2> & Registers<*1*><1> & ~Registers<*1*><0>))

