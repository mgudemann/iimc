#FAIL: (0-11)
AG EF (~board<*0*><2> & ~board<*0*><1> & ~board<*0*><0>)
AG EF (~board<*1*><2> & ~board<*1*><1> & ~board<*1*><0>)
AG EF (~board<*2*><2> & ~board<*2*><1> & ~board<*2*><0>)
AG EF (~board<*3*><2> & ~board<*3*><1> & ~board<*3*><0>)
AG EF (~board<*4*><2> & ~board<*4*><1> & ~board<*4*><0>)
AG EF (~board<*5*><2> & ~board<*5*><1> & ~board<*5*><0>)
AG EF (~board<*6*><2> & ~board<*6*><1> & ~board<*6*><0>)
AG EF (~board<*7*><2> & ~board<*7*><1> & ~board<*7*><0>)
AG EF (~board<*8*><2> & ~board<*8*><1> & ~board<*8*><0>)
AG EF (~board<*9*><2> & ~board<*9*><1> & ~board<*9*><0>)
AG EF (~board<*10*><2> & ~board<*10*><1> & ~board<*10*><0>)
AG EF (~board<*11*><2> & ~board<*11*><1> & ~board<*11*><0>)

#FAIL: (12-23)
AG EF (board<*20*><2> & ~board<*20*><1> & ~board<*20*><0>)
AG EF (board<*21*><2> & ~board<*21*><1> & ~board<*21*><0>)
AG EF (board<*22*><2> & ~board<*22*><1> & ~board<*22*><0>)
AG EF (board<*23*><2> & ~board<*23*><1> & ~board<*23*><0>)
AG EF (board<*24*><2> & ~board<*24*><1> & ~board<*24*><0>)
AG EF (board<*25*><2> & ~board<*25*><1> & ~board<*25*><0>)
AG EF (board<*26*><2> & ~board<*26*><1> & ~board<*26*><0>)
AG EF (board<*27*><2> & ~board<*27*><1> & ~board<*27*><0>)
AG EF (board<*28*><2> & ~board<*28*><1> & ~board<*28*><0>)
AG EF (board<*29*><2> & ~board<*29*><1> & ~board<*29*><0>)
AG EF (board<*30*><2> & ~board<*30*><1> & ~board<*30*><0>)
AG EF (board<*31*><2> & ~board<*31*><1> & ~board<*31*><0>)

#FAIL: (24-35)
AG EF board<*20*><2>
AG EF board<*21*><2>
AG EF board<*22*><2>
AG EF board<*23*><2>
AG EF board<*24*><2>
AG EF board<*25*><2>
AG EF board<*26*><2>
AG EF board<*27*><2>
AG EF board<*28*><2>
AG EF board<*29*><2>
AG EF board<*30*><2>
AG EF board<*31*><2>

#PASS: (36-47)
AG EF ~board<*0*><0>
AG EF ~board<*1*><0>
AG EF ~board<*2*><0>
AG EF ~board<*3*><0>
AG EF ~board<*4*><0>
AG EF ~board<*5*><0>
AG EF ~board<*6*><0>
AG EF ~board<*7*><0>
AG EF ~board<*8*><0>
AG EF ~board<*9*><0>
AG EF ~board<*10*><0>
AG EF ~board<*11*><0>


#FAIL: (48-49)
AG ~red
AG ~white

#PASS: (50-51)
AG(red -> AG red)
AG(white -> AG white)

#PASS: (52-55)
AG(board<*0*><2> | board<*0*><1> | board<*0*><0> -> AX (board<*0*><2> | board<*0*><1> | board<*0*><0>))
AG(board<*1*><2> | board<*1*><1> | board<*1*><0> -> AX (board<*1*><2> | board<*1*><1> | board<*1*><0>))
AG(board<*2*><2> | board<*2*><1> | board<*2*><0> -> AX (board<*2*><2> | board<*2*><1> | board<*2*><0>))
AG(board<*3*><2> | board<*3*><1> | board<*3*><0> -> AX (board<*3*><2> | board<*3*><1> | board<*3*><0>))

#PASS: (56-59)
AG (~board<*28*><2> | board<*28*><1> | board<*28*><0> -> AX (~board<*28*><2> | board<*28*><1> | board<*28*><0>))
AG (~board<*29*><2> | board<*29*><1> | board<*29*><0> -> AX (~board<*29*><2> | board<*29*><1> | board<*29*><0>))
AG (~board<*30*><2> | board<*30*><1> | board<*30*><0> -> AX (~board<*30*><2> | board<*30*><1> | board<*30*><0>))
AG (~board<*31*><2> | board<*31*><1> | board<*31*><0> -> AX (~board<*31*><2> | board<*31*><1> | board<*31*><0>))
