#FAIL: (0) On all paths with two transitions, it is not possible to go through
# cell 13 in the second state and end in cell 16.
AX((~pos<4> & pos<3> & pos<2> & ~pos<1> & pos<0>) ->
  AX (~pos<4> | pos<3> | pos<2> | pos<1> | pos<0>)
)
