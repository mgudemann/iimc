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

#PASS: (6)
AG(~Work -> AG(~Decode<5> & ~Decode<4> & ~Decode<3>))

#PASS: (7)
#RegA[5] = RegA_int[5]  and RegA_int= Insn[25:21]
AG((Decode<4> & ~Decode<0>) | (Decode<5> & ~Decode<0>) -> AG(~(RegA<5> ^ Insn<25>)))

#PASS: (8)
AG(Decode<3> & Insn<12> -> AG(Const<21> & (~(Const<20> ^ Insn<20>) & ~(Const<19> ^ Insn<19>) & ~(Const<18> ^ Insn<18>) & ~(Const<17> ^ Insn<17>) & ~(Const<16> ^ Insn<16>) & ~(Const<15> ^ Insn<15>))))

#PASS: (9)
AG(Decode<4> & Decode<0> -> AG(~(Operand1<31> ^ RegAValue<31>) & ~(Operand1<30> ^ RegAValue<30>) & ~(Operand1<29> ^ RegAValue<29>) & ~(Operand1<28> ^ RegAValue<28>) & ~(Operand1<27> ^ RegAValue<27>) & ~(Operand1<26> ^ RegAValue<26>) & ~(Operand2<31> ^ PC<31>) & ~(Operand2<30> ^ PC<30>) & ~(Operand2<29> ^ PC<29>) & ~(Operand2<28> ^ PC<28>) & ~(Operand2<27> ^ PC<27>) & ~(Operand2<26> ^ PC<26>)))

