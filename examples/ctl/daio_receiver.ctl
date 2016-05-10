#PASS: (0)
~E ~load_A U load_B
#PASS: (1)
~E ~(~bit_count_A<6> & ~bit_count_A<5> & ~bit_count_A<4> & ~bit_count_A<3> & bit_count_A<2> & ~bit_count_A<1> & ~bit_count_A<0>) U (load_A | load_B | load_buff)
#FAIL: (2)
~E ~load_B U load_A
