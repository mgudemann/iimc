#PASS: (0)
AG(match ->
   ~E (~(storeaddr<1> ^ readhead<1>) & ~(storeaddr<0> ^ readhead<0>)) U
      EG((~(storeaddr<1> ^ readhead<1>) & ~(storeaddr<0> ^ readhead<0>)) &
         ((readheadentry<1> ^ writetailentry<1>) | (readheadentry<0> ^ writetailentry<0>))
        )
  )

#FAIL: (1)
AG(match -> AX(AG(~(storeaddr<1> ^ readhead<1>) & ~(storeaddr<0> ^ readhead<0>))))
