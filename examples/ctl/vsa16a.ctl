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
