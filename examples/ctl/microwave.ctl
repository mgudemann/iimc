#PASS: (0)
#The oven can't be heated if the door is not closed.
A ~Heat U Close

#PASS: (1)
#If an error condition occurs, it must be reset before the oven may heat.
AG ((~Close & Start) -> ~E Error U Heat)


