#FAIL: (0)
permutation -> E permutation U identity 
#PASS: (1)
AG(permutation -> AX permutation);
#PASS: (2)
identity -> permutation
#PASS: (3)
(permutation & ~oddInversions) == EF identity
#PASS: (4)
permutation -> AG permutation
#PASS: (5)
(permutation & ~oddInversions) -> AG ~oddInversions
#PASS: (6)
permutation -> AG(oddInversions -> AX oddInversions)
#PASS: (7)
permutation -> AG(~oddInversions -> AX ~oddInversions)
