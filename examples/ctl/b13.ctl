#PASS: (0)
#a certain signal is always asserted before another.
~E ~mux_en U soc
#PASS: (1)
~E ~soc U load_dato
#PASS: (2)
~E ~tx_end U confirm
#PASS: (3)
~E ~send_data U rdy
#PASS: (4)
~E ~rdy U shot
#PASS: (5)
~E ~shot U load
#PASS: (6)
~E ~load U send
#PASS: (7)
~E ~send U confirm
#PASS: (8)
~E ~load U error
#PASS: (9)
~E (~tx_conta<9> & ~tx_conta<8> & ~tx_conta<7> & ~tx_conta<6> & ~tx_conta<5> & ~tx_conta<4> & ~tx_conta<3> & ~tx_conta<2> & ~tx_conta<1> & ~tx_conta<0> ) U tx_end
