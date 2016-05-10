#PASS: (0)
#No PUSH commands are accpted if the heap is full.
AG((ready & (nitems<2> & ~nitems<1> & ~nitems<0>)) -> ~E ~(~state<2> & state<1> & state<0>) U (~state<2> & ~state<1> & state<0>))
#PASS: (1)
# No POP commands are accpted if the heap is empty.
AG((ready & (~nitems<2> & ~nitems<1> & ~nitems<0>)) -> ~E ~(~state<2> & ~state<1> & state<0>) U (~state<2> & state<1> & state<0>))

#PASS: (2) No PUSH commands are accpted if the heap is full.
AG((ready & (nitems<2> & ~nitems<1> & ~nitems<0>)) -> ~EX (~state<2> & ~state<1> & state<0>))
#PASS: (3) No POP commands are accpted if the heap is empty.
AG((ready & (~nitems<2> & ~nitems<1> & ~nitems<0>)) -> ~EX (~state<2> & state<1> & state<0>))

#PASS: (4-5) Yet another variation on the theme.
AG((ready & (nitems<2> & ~nitems<1> & ~nitems<0>)) -> AX((~state<2> & state<1> & state<0>) | (nitems<2> & ~nitems<1> & ~nitems<0>)))
AG((ready & (~nitems<2> & ~nitems<1> & ~nitems<0>)) -> AX((~state<2> & ~state<1> & state<0>) | (~nitems<2> & ~nitems<1> & ~nitems<0>)))


