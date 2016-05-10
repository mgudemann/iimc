#FAIL: (0)
AG(q0.match -> AF((q0.storeaddr<1> ^ q0.readhead<1>) | (q0.storeaddr<0> ^ q0.readhead<0>)))
#PASS: (1)
AG EF q0.match
#PASS: (2)
AG EF q1.match
#PASS: (3)
AG(q0.match ->
   ~E (~(q0.storeaddr<1> ^ q0.readhead<1>) & ~(q0.storeaddr<0> ^ q0.readhead<0>)) U
      EG((~(q0.storeaddr<1> ^ q0.readhead<1>) & ~(q0.storeaddr<0> ^ q0.readhead<0>)) &
         ((readheadentry0<1> ^ writetailentry0<1>) | (readheadentry0<0> ^ writetailentry0<0>))
        )
     )
#FAIL: (4)
AG(q0.match -> AX(AG(~(q0.storeaddr<1> ^ q0.readhead<1>) & ~(q0.storeaddr<0> ^ q0.readhead<0>))))
#FAIL: (5)
AG(q1.match -> AX(AG(~(q1.storeaddr<1> ^ q1.readhead<1>) & ~(q1.storeaddr<0> ^ q1.readhead<0>))))
