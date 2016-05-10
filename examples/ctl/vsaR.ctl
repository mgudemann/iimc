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

#PASS: (3)
#if the destination is R1 or R3, R2 is not affected by this instruction.
AG((!State<2> & !State<1> & State<0>) &
   (regRegALU & adFld3<0> | !regRegALU & adFld2<0>) &
   (Registers<*2*><4> & !Registers<*2*><3> & Registers<*2*><2> & !Registers<*2*><1> & Registers<*2*><0>) -> AX AX AX AX(Registers<*2*><4> & !Registers<*2*><3> & Registers<*2*><2> & !Registers<*2*><1> & Registers<*2*><0>))

#PASS: (4)
#The register file is only modified when transitioning from WB to IF.
AG((!State<2> & !State<1> & !State<0>) & (Registers<*1*><4> & !Registers<*1*><3> & Registers<*1*><2> & !Registers<*1*><1> & Registers<*1*><0>) & (!Registers<*2*><4> & Registers<*2*><3> & !Registers<*2*><2> & Registers<*2*><1> & !Registers<*2*><0>) & (Registers<*3*><4> & !Registers<*3*><3> & Registers<*3*><2> & !Registers<*3*><1> & Registers<*3*><0>) -> AX AX AX AX ((Registers<*1*><4> & !Registers<*1*><3> & Registers<*1*><2> & !Registers<*1*><1> & Registers<*1*><0>) & (!Registers<*2*><4> & Registers<*2*><3> & !Registers<*2*><2> & Registers<*2*><1> & !Registers<*2*><0>) & (Registers<*3*><4> & !Registers<*3*><3> & Registers<*3*><2> & !Registers<*3*><1> & Registers<*3*><0>)))

#PASS: (5)
#IR is only modified when transitioning from IF to ID.
AG((!State<2> & !State<1> & State<0>) & (IR<11> & !IR<10> & IR<9> & !IR<8> & IR<7> & !IR<6> & IR<5> & !IR<4> & IR<3> & !IR<2> & IR<1> & !IR<0>) -> AX AX AX AX (IR<11> & !IR<10> & IR<9> & !IR<8> & IR<7> & !IR<6> & IR<5> & !IR<4> & IR<3> & !IR<2> & IR<1> & !IR<0>))

#PASS: (6)
#NPC is only modified when transitioning from IF to ID.
AG((!State<2> & !State<1> & State<0>) & (NPC<4> & !NPC<3> & NPC<2> & !NPC<1> & NPC<0>) -> AX AX AX AX (NPC<4> & !NPC<3> & NPC<2> & !NPC<1> & NPC<0>))

#PASS: (7)
#A and B are only modified when transitioning from ID to EXE.
AG((!State<2> & State<1> & !State<0>) & (A<4> & !A<3> & A<2> & !A<1> & A<0>) & (!B<4> & B<3> & !B<2> & B<1> & !B<0>) -> AX AX AX AX ((A<4> & !A<3> & A<2> & !A<1> & A<0>) & (!B<4> & B<3> & !B<2> & B<1> & !B<0>)))

#PASS: (8)
#ALUOutput is only modified when transitioning from EXE to MEM.
AG((!State<2> & State<1> & State<0>) & (ALUOutput<4> & !ALUOutput<3> & ALUOutput<2> & !ALUOutput<1> & ALUOutput<0>) -> AX AX AX AX (ALUOutput<4> & !ALUOutput<3> & ALUOutput<2> & !ALUOutput<1> & ALUOutput<0>))

#PASS: (9)
#Cond is only modified when transitioning from EXE to MEM.
AG((!State<2> & State<1> & State<0>) & Cond -> AX AX AX AX (Cond))

#PASS: (10)
#LMD is only modified when transitioning from MEM to WB.
AG((State<2> & !State<1> & !State<0>) & (LMD<4> & !LMD<3> & LMD<2> & !LMD<1> & LMD<0>) -> AX AX AX AX(LMD<4> & !LMD<3> & LMD<2> & !LMD<1> & LMD<0>))

#PASS: (11)
#PC is only modified when transitioning from MEM to WB.
AG((State<2> & !State<1> & !State<0>) & (PC<4> & !PC<3> & PC<2> & !PC<1> & PC<0>) -> AX AX AX AX(PC<4> & !PC<3> & PC<2> & !PC<1> & PC<0>))

#PASS: (12)
#Only one register can change as a result of an instruction. The
# register that changes receives its value from either ALUOutput or LMD.
AG((!State<2> & !State<1> & !State<0>) & (!Registers<*1*><4> & !Registers<*1*><3> & !Registers<*1*><2> & !Registers<*1*><1> & Registers<*1*><0>) & (!Registers<*2*><4> & !Registers<*2*><3> & !Registers<*2*><2> & Registers<*2*><1> & !Registers<*2*><0>) & (!Registers<*3*><4> & !Registers<*3*><3> & !Registers<*3*><2> & Registers<*3*><1> & Registers<*3*><0>) ->
   AX AX AX AX AX((!Registers<*1*><4> & !Registers<*1*><3> & !Registers<*1*><2> & !Registers<*1*><1> & Registers<*1*><0>) & (!Registers<*2*><4> & !Registers<*2*><3> & !Registers<*2*><2> & Registers<*2*><1> & !Registers<*2*><0>) & ((!Registers<*3*><4> & !Registers<*3*><3> & !Registers<*3*><2> & Registers<*3*><1> & Registers<*3*><0>) | (!(Registers<*3*><4> ^ ALUOutput<4>) & !(Registers<*3*><3> ^ ALUOutput<3>) & !(Registers<*3*><2> ^ ALUOutput<2>) & !(Registers<*3*><1> ^ ALUOutput<1>) & !(Registers<*3*><0> ^ ALUOutput<0>)) | (!(Registers<*3*><4> ^ LMD<4>) & !(Registers<*3*><3> ^ LMD<3>) & !(Registers<*3*><2> ^ LMD<2>) & !(Registers<*3*><1> ^ LMD<1>) & !(Registers<*3*><0> ^ LMD<0>))) | (!Registers<*1*><4> & !Registers<*1*><3> & !Registers<*1*><2> & !Registers<*1*><1> & Registers<*1*><0>) & (!Registers<*3*><4> & !Registers<*3*><3> & !Registers<*3*><2> & Registers<*3*><1> & Registers<*3*><0>) & ((!Registers<*2*><4> & !Registers<*2*><3> & !Registers<*2*><2> & Registers<*2*><1> & !Registers<*2*><0>) | (!(Registers<*2*><4> ^ ALUOutput<4>) & !(Registers<*2*><3> ^ ALUOutput<3>) & !(Registers<*2*><2> ^ ALUOutput<2>) & !(Registers<*2*><1> ^ ALUOutput<1>) & !(Registers<*2*><0> ^ ALUOutput<0>)) | (!(Registers<*2*><4> ^ LMD<4>) & !(Registers<*2*><3> ^ LMD<3>) & !(Registers<*2*><2> ^ LMD<2>) & !(Registers<*2*><1> ^ LMD<1>) & !(Registers<*2*><0> ^ LMD<0>))) | (!Registers<*2*><4> & !Registers<*2*><3> & !Registers<*2*><2> & Registers<*2*><1> & !Registers<*2*><0>) & (!Registers<*3*><4> & !Registers<*3*><3> & !Registers<*3*><2> & Registers<*3*><1> & Registers<*3*><0>) & ((!Registers<*1*><4> & !Registers<*1*><3> & !Registers<*1*><2> & !Registers<*1*><1> & Registers<*1*><0>) | (!(Registers<*1*><4> ^ ALUOutput<4>) & !(Registers<*1*><3> ^ ALUOutput<3>) & !(Registers<*1*><2> ^ ALUOutput<2>) & !(Registers<*1*><1> ^ ALUOutput<1>) & !(Registers<*1*><0> ^ ALUOutput<0>)) | (!(Registers<*1*><4> ^ LMD<4>) & !(Registers<*1*><3> ^ LMD<3>) & !(Registers<*1*><2> ^ LMD<2>) & !(Registers<*1*><1> ^ LMD<1>) & !(Registers<*1*><0> ^ LMD<0>)))))

