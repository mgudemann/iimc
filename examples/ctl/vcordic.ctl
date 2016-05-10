#PASS: (0)
AG(
  ~(Angle<15> | Angle<14> | Angle<13> | Angle<12> | Angle<11> |
    Angle<10> | Angle<9> |  Angle<8> | Angle<7> | Angle<6> | Angle<5> |
    Angle<4> | Angle<3> | Angle<2> | Angle<1> | Angle<0>) &
  ~iteration<3> & ~iteration<2> & ~iteration<1> & iteration<0> 
  ->
  AF (
    ~(iteration<3> | iteration<2> | iteration<1> | iteration<0>) |
    (~CosX<16> & CosX<15> & ~CosX<14> & CosX<13> & CosX<12> &
     ~CosX<11> & CosX<10> & ~CosX<9> & ~CosX<8> & ~CosX<7> & ~CosX<6> &
     ~CosX<5> & CosX<4> & ~CosX<3> & CosX<2> & CosX<1> & CosX<0>) |
    (~CosX<16> & ~CosX<15> & CosX<14> & CosX<13> & CosX<12> &
     ~CosX<11> & CosX<10> & CosX<9> & CosX<8> & ~CosX<7> & ~CosX<6> &
     CosX<5> & CosX<4> & ~CosX<3> & CosX<2> & ~CosX<1> & CosX<0>)
  )
)
