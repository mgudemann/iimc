#FAIL: (0) If no branch is taken, eventually the PC will attain any even value;
# for instance, 111111111110.
AG AF(
  ~IR<11> & IR<10> & ~IR<9> | PC<11> & PC<10> & PC<9> & PC<8> &
  PC<7> & PC<6> & PC<5> & PC<4> & PC<3> & PC<2> & PC<1> & ~PC<0>
)

#PASS: (1) The PC may attain any even value; for instance, 111111111110.
AG EF(
  PC<11> & PC<10> & PC<9> & PC<8> & PC<7> & PC<6> & PC<5> &
  PC<4> & PC<3> & PC<2> & PC<1> & ~PC<0>
)

#PASS: (2) if the destination is R1 or R3, R2 is not affected by this instruction.
AG((~State<2> & ~State<1> & State<0> &
   (~IR<2> & IR<1> & IR<0> & IR<7> |
    ~(~IR<2> & IR<1> & IR<0>) & IR<5>) & 
   (~Registers<*2*><15> & ~Registers<*2*><14> & ~Registers<*2*><13> & 
    ~Registers<*2*><12> & ~Registers<*2*><11> & ~Registers<*2*><10> &
    ~Registers<*2*><9> & ~Registers<*2*><8> & ~Registers<*2*><7> &
    ~Registers<*2*><6> & ~Registers<*2*><5> & Registers<*2*><4> &
    ~Registers<*2*><3> & Registers<*2*><2> & ~Registers<*2*><1> &
    Registers<*2*><0>))
    -> AX(AX(AX(AX(
         ~Registers<*2*><15> & ~Registers<*2*><14> & ~Registers<*2*><13> & 
         ~Registers<*2*><12> & ~Registers<*2*><11> & ~Registers<*2*><10> &
         ~Registers<*2*><9> & ~Registers<*2*><8> & ~Registers<*2*><7> &
         ~Registers<*2*><6> & ~Registers<*2*><5> & Registers<*2*><4> &
         ~Registers<*2*><3> & Registers<*2*><2> & ~Registers<*2*><1> &
         Registers<*2*><0>)))))

#FAIL: (3) incorrect version of previous property
AG((~State<2> & ~State<1> & State<0> &
   (~IR<0> & IR<1> & IR<2> & IR<8> |
    ~(~IR<0> & IR<1> & IR<2>) & IR<6>) & 
   (~Registers<*2*><15> & ~Registers<*2*><14> & ~Registers<*2*><13> & 
    ~Registers<*2*><12> & ~Registers<*2*><11> & ~Registers<*2*><10> &
    ~Registers<*2*><9> & ~Registers<*2*><8> & ~Registers<*2*><7> &
    ~Registers<*2*><6> & ~Registers<*2*><5> & Registers<*2*><4> &
    ~Registers<*2*><3> & Registers<*2*><2> & ~Registers<*2*><1> &
    Registers<*2*><0>))
    -> AX(AX(AX(AX(
         ~Registers<*2*><15> & ~Registers<*2*><14> & ~Registers<*2*><13> & 
         ~Registers<*2*><12> & ~Registers<*2*><11> & ~Registers<*2*><10> &
         ~Registers<*2*><9> & ~Registers<*2*><8> & ~Registers<*2*><7> &
         ~Registers<*2*><6> & ~Registers<*2*><5> & Registers<*2*><4> &
         ~Registers<*2*><3> & Registers<*2*><2> & ~Registers<*2*><1> &
         Registers<*2*><0>)))))

#PASS: (4) A register only changes if it is the destination of an instruction.
AG(Registers<*1*><1> ->
   A (~IR<2> & IR<1> & IR<0> & ~IR<8> & IR<7> |
      ~(~IR<2> & IR<1> & IR<0>) & ~IR<6> & IR<5>) R Registers<*1*><1>)

#PASS: (5) Cond is only modified when transiting from EXE to MEM.
AG((~State<2> & State<1> & State<0> & Cond) -> AX(AX(AX(AX(Cond)))))
