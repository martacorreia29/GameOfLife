--Data Structores
data WorldList = Nil | Tile Int Bool WorldList

initWorld : Int -> WorldList
initWorld n = if n == 0
              then Nil
              else Tile n (semiRandomBool n) (initWorld (n-1))

semiRandomBool : Int -> Bool
semiRandomBool n = (mod n 2) == 0

printWorld: forall a:SL => WorldList -> Int -> ((Int, Int), Bool)
printWorld world n =
	case world of {
    Nil ->
      (((-1), (-1)), False),
    Tile x b l ->
      if x == n
      then ( (getCoors x 10) , b) -- 10 rows
      else printWorld[Skip] l n
    }

-- (Array index, array size) -> x pos
getX : Int -> Int -> Int
getX i n = mod i n

-- (Array index, array size) -> y pos
getY : Int -> Int -> Int
getY i n = i / n

getCoors : Int -> Int -> (Int, Int)
getCoors i n = let x = getX i n in
		       let y = getY i n in
		       (x,y)

main:((Int, Int), Bool)
main = printWorld[Skip] (initWorld 100) 23 -- 100 elements
