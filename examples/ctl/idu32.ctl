#PASS: (0)
AG(Work -> A Work U (EF (~Decode<1> & Decode<0>)))

#PASS: (1)
EF((OpCode<5> & ~OpCode<4> & ~OpCode<3> & ~OpCode<2> & OpCode<1> & ~OpCode<0>) -> A (OpCode<5> & ~OpCode<4> & ~OpCode<3> & ~OpCode<2> & OpCode<1> & ~OpCode<0>) U Decode<4>)

#PASS: (2)
AG(Work -> A Work U (EF Decode<1>))

#PASS: (3)
EF((OpCode<5> & ~OpCode<4> & ~OpCode<3> & ~OpCode<2> & OpCode<1> & ~OpCode<0>) -> A (OpCode<5> & ~OpCode<4> & ~OpCode<3> & ~OpCode<2> & OpCode<1> & ~OpCode<0>) U Decode<1>)

#PASS: (4)
A Decode<3> & (Insn<4> & Insn<3> & Insn<2> & Insn<1> & Insn<0>) U ~RegDest<5>

#FAIL: (5)
A (~(FctCode<6> ^ Insn<11>) & ~(FctCode<5> ^ Insn<10>) & ~(FctCode<4> ^ Insn<9>) & ~(FctCode<3> ^ Insn<8>) & ~(FctCode<2> ^ Insn<7>) & ~(FctCode<1> ^ Insn<6>) & ~(FctCode<0> ^ Insn<5>)) U (Decode<4> & ~Decode<1>)

