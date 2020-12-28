data Coordenates = XY Int Int
data State = S Int
data Celule = C Coordenates State
data World = Nil | W Celule World
​
createWorld : World
createWorld = W (C (XY 1 1) (S 0)) (W (C (XY 1 1) (S 0)) Nil)
​
main : World
main = createWorld
