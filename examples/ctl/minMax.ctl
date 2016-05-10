#PASS: (0)
#a specified reset state can eventually be reached from every state.
AG(EF(min<8> & min<7> & min<6> & min<5> & min<4> & min<3> & min<2> & min<1> & min<0> & !last<8> & !last<7> & !last<6> & !last<5> & !last<4> & !last<3> & !last<2> & !last<1> & !last<0> & !max<8> & !max<7> & !max<6> & !max<5> & !max<4> & !max<3> & !max<2> & !max<1> & !max<0>))

#PASS: (1)
#a specified reset state can be reached from all states in one cycle.
AG(EX(min<8> & min<7> & min<6> & min<5> & min<4> & min<3> & min<2> & min<1> & min<0> & !last<8> & !last<7> & !last<6> & !last<5> & !last<4> & !last<3> & !last<2> & !last<1> & !last<0> & !max<8> & !max<7> & !max<6> & !max<5> & !max<4> & !max<3> & !max<2> & !max<1> & !max<0>))

#FAIL: (2)
#a specified reset state must eventually be reached from every state.
# This formula fails in spite of the fairness conditions.
AG(AF(min<8> & min<7> & min<6> & min<5> & min<4> & min<3> & min<2> & min<1> & min<0> & !last<8> & !last<7> & !last<6> & !last<5> & !last<4> & !last<3> & !last<2> & !last<1> & !last<0> & !max<8> & !max<7> & !max<6> & !max<5> & !max<4> & !max<3> & !max<2> & !max<1> & !max<0>))

#PASS: (3)
#The non-reset states reachable in one clock cycle from the reset
# states have min == last == max.
AG(min<8> & min<7> & min<6> & min<5> & min<4> & min<3> & min<2> & min<1> & min<0> & !max<8> & !max<7> & !max<6> & !max<5> & !max<4> & !max<3> & !max<2> & !max<1> & !max<0> ->
   AX((min<8> & min<7> & min<6> & min<5> & min<4> & min<3> & min<2> & min<1> & min<0> & !max<8> & !max<7> & !max<6> & !max<5> & !max<4> & !max<3> & !max<2> & !max<1> & !max<0>) |
      (!(min<8> ^ last<8>) & !(min<7> ^ last<7>) & !(min<6> ^ last<6>) & !(min<5> ^ last<5>) & !(min<4> ^ last<4>) & !(min<3> ^ last<3>) & !(min<2> ^ last<2>) & !(min<1> ^ last<1>) & !(min<0> ^ last<0>) & !(last<8> ^ max<8>) & !(last<8> ^ max<8>) & !(last<7> ^ max<7>) & !(last<6> ^ max<6>) & !(last<5> ^ max<5>) & !(last<4> ^ max<4>) & !(last<3> ^ max<3>) & !(last<2> ^ max<2>) & !(last<1> ^ max<1>) & !(last<0> ^ max<0>))))

#PASS: (4)
#The non-reset states reachable in two clock cycles from the reset
# states have either min == last or last == max.
AG(min<8> & min<7> & min<6> & min<5> & min<4> & min<3> & min<2> & min<1> & min<0> & !max<8> & !max<7> & !max<6> & !max<5> & !max<4> & !max<3> & !max<2> & !max<1> & !max<0> ->
   AX AX((min<8> & min<7> & min<6> & min<5> & min<4> & min<3> & min<2> & min<1> & min<0> & !max<8> & !max<7> & !max<6> & !max<5> & !max<4> & !max<3> & !max<2> & !max<1> & !max<0>) |
        ((!(min<8> ^ last<8>) & !(min<7> ^ last<7>) & !(min<6> ^ last<6>) & !(min<5> ^ last<5>) & !(min<4> ^ last<4>) & !(min<3> ^ last<3>) & !(min<2> ^ last<2>) & !(min<1> ^ last<1>) & !(min<0> ^ last<0>)) | (!(last<8> ^ max<8>) & !(last<8> ^ max<8>) & !(last<7> ^ max<7>) & !(last<6> ^ max<6>) & !(last<5> ^ max<5>) & !(last<4> ^ max<4>) & !(last<3> ^ max<3>) & !(last<2> ^ max<2>) & !(last<1> ^ max<1>) & !(last<0> ^ max<0>)))))

