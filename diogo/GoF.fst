-- ##############################################################################################
-- Data Structores ##############################################################################
-- ##############################################################################################
data WorldList = Nil | Tile Int Bool WorldList

-- ##############################################################################################
-- Init world functions #########################################################################
-- ##############################################################################################

initWorld : Int -> WorldList
initWorld n = if n == 0
              then Nil
              else Tile n (semiRandomBool n) (initWorld (n-1))

-- TODO find a better way to randamize bools
semiRandomBool : Int -> Bool
semiRandomBool n = (mod n 13) == 0

-- ##############################################################################################
-- utils funtions ###############################################################################
-- ##############################################################################################

-- (Array index, array size) -> x pos
getX : Int -> Int -> Int
getX i n = mod i n

-- (Array index, array size) -> y pos
getY : Int -> Int -> Int
getY i n = i / n

-- returs the given index coords in (x,y)
getCoors : Int -> Int -> (Int, Int)
getCoors i n = let x = getX i n in
		       let y = getY i n in
		       (x,y)

-- returs a represetation of the tile in the given index in ((x,y), state)   --Not really useful
getTile: forall a:SL => WorldList -> Int -> ((Int, Int), Bool)
getTile world n =
	case world of {
    Nil ->
      (((-1), (-1)), False),
    Tile x b l ->
      if x == n
      then ( (getCoors x 10) , b) -- 10 rows
      else getTile[Skip] l n
    }


-- ##############################################################################################
-- funtions #####################################################################################
-- ##############################################################################################

-- Prints the world with chars
printWorld : forall a:SL => WorldList -> Int -> ()
printWorld world rowSize =
 case world of {
    Nil ->
       printChar '_',
    Tile i b l ->
       let _ = if b
               then printChar '#'
               else printChar '_' in
       let iMod = mod i rowSize in
       let _ = if iMod == 0 && i > 1
               then printUnitLn ()
               else ()
       in printWorld[a] l rowSize
    }


-- Aux funtion to countNeighbors
-- finds the tile with index i and verifies if it is alive, if so returns 1 else 0
getNeighborValue : forall a:SL => WorldList -> Int -> Int
getNeighborValue world i =
	case world of {
    Nil ->
      0,
    Tile x b l ->
      if x == i && b
      then 1
      else getNeighborValue[a] l i
    }



-- Returns the numeber of Neighbors of i that are alive
-- [a][b][c]
-- [d][i][e]
-- [f][g][h]
countNeighbors: WorldList -> Int -> Int -> Int
countNeighbors world i rowSize =
            let d = i-1 in
            let e = i+1 in
            let b = i - rowSize in
            let g = i + rowSize in
            let a = b - 1 in
            let c = b + 1 in
            let f = g - 1 in
            let h = g + 1 in
            let count = getNeighborValue[Skip] world d +
                        getNeighborValue[Skip] world e +
                        getNeighborValue[Skip] world b +
                        getNeighborValue[Skip] world g +
                        getNeighborValue[Skip] world a  +
                        getNeighborValue[Skip] world c  +
                        getNeighborValue[Skip] world f  +
                        getNeighborValue[Skip] world h  in
            count


-- ##############################################################################################
-- Main #########################################################################################
-- ##############################################################################################

main:((Int, Int), Bool)
main = getTile[Skip] (initWorld 100) 23 -- 100 elements
