#PASS: (0)
#If entry 0 is allocated, it is not allocated again until it is freed.
AG ((alloc & ~nack & ~alloc_addr<3> & ~alloc_addr<2> & ~alloc_addr<1> & ~alloc_addr<0>) -> ~EX E ~(free & ~free_addr<3> & ~free_addr<2> & ~free_addr<1> & ~free_addr<0>) U (~(free & ~free_addr<3> & ~free_addr<2> & ~free_addr<1> & ~free_addr<0>) & (alloc & ~nack & ~alloc_addr<3> & ~alloc_addr<2> & ~alloc_addr<1> & ~alloc_addr<0>)))
