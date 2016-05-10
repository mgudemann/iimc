#PASS: (0) It is always possible to write 101010101010 in the fifth entry of
# the stack.
AG EF (
  reg_file<*5*><11> & ~reg_file<*5*><10> &
  reg_file<*5*><9> & ~reg_file<*5*><8> &
  reg_file<*5*><7> & ~reg_file<*5*><6> &
  reg_file<*5*><5> & ~reg_file<*5*><4> &
  reg_file<*5*><3> & ~reg_file<*5*><2> &
  reg_file<*5*><1> & ~reg_file<*5*><0>
)

#PASS: (1) It is always possible to write 101010101010 in the five usable
# entries of the stack and in RE, 010101010101 in uPC, and 3 in the stack
# pointer.
AG EF (
  ~reg_file<*0*><11> & ~reg_file<*0*><10> &
  ~reg_file<*0*><9> & ~reg_file<*0*><8> &
  ~reg_file<*0*><7> & ~reg_file<*0*><6> &
  ~reg_file<*0*><5> & ~reg_file<*0*><4> &
  ~reg_file<*0*><3> & ~reg_file<*0*><2> &
  ~reg_file<*0*><1> & ~reg_file<*0*><0> &
  reg_file<*1*><11> & ~reg_file<*1*><10> &
  reg_file<*1*><9> & ~reg_file<*1*><8> &
  reg_file<*1*><7> & ~reg_file<*1*><6> &
  reg_file<*1*><5> & ~reg_file<*1*><4> &
  reg_file<*1*><3> & ~reg_file<*1*><2> &
  reg_file<*1*><1> & ~reg_file<*1*><0> &
  reg_file<*2*><11> & ~reg_file<*2*><10> &
  reg_file<*2*><9> & ~reg_file<*2*><8> &
  reg_file<*2*><7> & ~reg_file<*2*><6> &
  reg_file<*2*><5> & ~reg_file<*2*><4> &
  reg_file<*2*><3> & ~reg_file<*2*><2> &
  reg_file<*2*><1> & ~reg_file<*2*><0> &
  reg_file<*3*><11> & ~reg_file<*3*><10> &
  reg_file<*3*><9> & ~reg_file<*3*><8> &
  reg_file<*3*><7> & ~reg_file<*3*><6> &
  reg_file<*3*><5> & ~reg_file<*3*><4> &
  reg_file<*3*><3> & ~reg_file<*3*><2> &
  reg_file<*3*><1> & ~reg_file<*3*><0> &
  reg_file<*4*><11> & ~reg_file<*4*><10> &
  reg_file<*4*><9> & ~reg_file<*4*><8> &
  reg_file<*4*><7> & ~reg_file<*4*><6> &
  reg_file<*4*><5> & ~reg_file<*4*><4> &
  reg_file<*4*><3> & ~reg_file<*4*><2> &
  reg_file<*4*><1> & ~reg_file<*4*><0> &
  reg_file<*5*><11> & ~reg_file<*5*><10> &
  reg_file<*5*><9> & ~reg_file<*5*><8> &
  reg_file<*5*><7> & ~reg_file<*5*><6> &
  reg_file<*5*><5> & ~reg_file<*5*><4> &
  reg_file<*5*><3> & ~reg_file<*5*><2> &
  reg_file<*5*><1> & ~reg_file<*5*><0> &
  RE<11> & ~RE<10> & RE<9> & ~RE<8> &
  RE<7> & ~RE<6> & RE<5> & ~RE<4> &
  RE<3> & ~RE<2> & RE<1> & ~RE<0> &
  ~uPC<11> & uPC<10> & ~uPC<9> & uPC<8> &
  ~uPC<7> & uPC<6> & ~uPC<5> & uPC<4> &
  ~uPC<3> & uPC<2> & ~uPC<1> & uPC<0> &
  ~sp<2> & sp<1> & sp<0>
)

#PASS: (2) The antecedent is never satisfied for the reachable states.
AG(sp<2> & sp<1> & ~sp<0> -> AX(sp<2> & sp<1> & sp<0>))

#PASS: (3)
#the contents of the fifth entry of the stack cannot change in the
# next clock cycle unless the stack pointer is either 4 or 5.
AG(!(sp<2> & !sp<1> & !sp<0>) & !(sp<2> & !sp<1> & sp<0>) &
   (reg_file<*5*><11> & !reg_file<*5*><10> & reg_file<*5*><9> & !reg_file<*5*><8> & reg_file<*5*><7> & !reg_file<*5*><6> & reg_file<*5*><5> & !reg_file<*5*><4> & reg_file<*5*><3> & !reg_file<*5*><2> & reg_file<*5*><1> & !reg_file<*5*><0>) ->
    AX(reg_file<*5*><11> & !reg_file<*5*><10> & reg_file<*5*><9> & !reg_file<*5*><8> & reg_file<*5*><7> & !reg_file<*5*><6> & reg_file<*5*><5> & !reg_file<*5*><4> & reg_file<*5*><3> & !reg_file<*5*><2> & reg_file<*5*><1> & !reg_file<*5*><0>))

#PASS: (4)
#The antecedent is never satisfied for the reachable states.
AG(!reg_file<*0*><11> & !reg_file<*0*><10> & !reg_file<*0*><9> & !reg_file<*0*><8> & !reg_file<*0*><7> & !reg_file<*0*><6> & !reg_file<*0*><5> & !reg_file<*0*><4> & !reg_file<*0*><3> & !reg_file<*0*><2> & reg_file<*0*><1> & !reg_file<*0*><0> -> AX(!reg_file<*0*><11> & !reg_file<*0*><10> & !reg_file<*0*><9> & !reg_file<*0*><8> & !reg_file<*0*><7> & !reg_file<*0*><6> & !reg_file<*0*><5> & !reg_file<*0*><4> & !reg_file<*0*><3> & !reg_file<*0*><2> & !reg_file<*0*><1> & reg_file<*0*><0>));

