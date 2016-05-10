#FAIL: (0)
#There is no way to safely move all three passengers to the right side.
# The counterexample to this property provides an optimal strategy to do so.
~E safe U final

#PASS: (1)
#From any reachable safe state it is possible to complete successfully.
AG safe -> (E safe U final)


