#PASS: (0) The processor freezes as soon as a value greater than 2**20 is
# stored in the program counter.
AG(
  (regfile<*3*><31> | regfile<*3*><30> | regfile<*3*><29> |
   regfile<*3*><28> | regfile<*3*><27> | regfile<*3*><26> |
   regfile<*3*><25> | regfile<*3*><24> | regfile<*3*><23> |
   regfile<*3*><22> | regfile<*3*><21> | regfile<*3*><20>) ->
  AG(
    regfile<*3*><31> | regfile<*3*><30> | regfile<*3*><29> |
    regfile<*3*><28> | regfile<*3*><27> | regfile<*3*><26> |
    regfile<*3*><25> | regfile<*3*><24> | regfile<*3*><23> |
    regfile<*3*><22> | regfile<*3*><21> | regfile<*3*><20>
  )
)

#PASS: (1) An illegal instruction causes STOP to be asserted.
AG(~IR<24> & ~(IR<27> & IR<26>) & IR<23> & IR<22> & (IR<21> | IR<20>) &
  ~(regfile<*3*><31> | regfile<*3*><30> | regfile<*3*><29> |
    regfile<*3*><28> | regfile<*3*><27> | regfile<*3*><26> |
    regfile<*3*><25> | regfile<*3*><24> | regfile<*3*><23> |
    regfile<*3*><22> | regfile<*3*><21> | regfile<*3*><20>) -> AX STOP)

#PASS: (2) Once STOP is asserted, it remains so.
AG(STOP -> AG STOP)
