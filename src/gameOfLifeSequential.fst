-- Represents a linked list of bools
data World = Nil | Tile Int Bool World

-- A simple linked int list, used to store the number of neighbors around a tile
data IntList = Nul | Number Int IntList

generations : Int -> Int -> Int -> World -> World
generations iterations size rowSize world =
	if iterations == 0
	then world
	else
		let (_ , newGen) = splitWork world Nul (size/rowSize) (size/rowSize) rowSize in
		printStringLn " ";
		printWorld newGen rowSize rowSize;
		printStringLn " ";
		generations (iterations-1) size rowSize newGen

-- [  top ]
-- [middle]
-- [bottom]
splitWork : World -> IntList -> Int -> Int -> Int -> (IntList, World)
splitWork world topRow index size rowSize =
	if index == size
	then
		-- TOP ROW
		let (row, tail) = splitRow world rowSize in
		let numNeighbors = countRowNeighbors Nil row False in
		let numNeighborsWithSelf = countRowNeighbors Nil row True in
		let (bottomRow, bottomWorld) = splitWork tail numNeighborsWithSelf (index - 1) size rowSize in
		let sumNeighbors = zipSumEdge numNeighbors bottomRow in
		let newWorld = gameOfLife row sumNeighbors in
		(numNeighborsWithSelf, concat newWorld bottomWorld)
	else
	-- BOTTOM ROW
		if index == 1
		then
			let (row, tail) = splitRow world rowSize in
			let numNeighbors = countRowNeighbors Nil row False in
			let numNeighborsWithSelf = countRowNeighbors Nil row True in
			let sumNeighbors = zipSumEdge topRow numNeighbors in
			let newWorld = gameOfLife row sumNeighbors in
	    (numNeighborsWithSelf, newWorld)
		else
			-- MIDDLE ROWS
	    let (row, tail) = splitRow world rowSize in
			let numNeighbors = countRowNeighbors Nil row False in
			let numNeighborsWithSelf = countRowNeighbors Nil row True in
			let (bottomRow, bottomWorld) = splitWork tail numNeighborsWithSelf (index - 1) size rowSize in
	    let sumNeighbors = zipSum topRow numNeighbors bottomRow in
			let newWorld = gameOfLife row sumNeighbors in
			(numNeighborsWithSelf, concat newWorld bottomWorld)

splitRow : World -> Int -> (World, World)
splitRow world rowSize =
		case world of {
			Nil -> (Nil, Nil),
			Tile index state next ->
				if rowSize == 1
				then
				 	( Tile index state Nil, next)
				else
					let (row, tail) = splitRow next (rowSize-1) in
					( Tile index state row, tail)
		}

concat : World -> World -> World
concat xs ys =
  case xs of {
    Nil -> ys,
    Tile i s xs' -> Tile i s (concat xs' ys)
  }

-- [l][i][r]
-- For each tile in the row, it will count if l i and r are alive and place that number in i
-- returns a list of all the alive tiles for each (l, i, r) group
countRowNeighbors : World -> World -> Bool -> IntList
countRowNeighbors left current countSelf =
		case left of {
			Nil -> -- FIRST COLUMN
				case current of {
					Nil -> Nul,
					Tile currentIndex currentState right ->
						case right of {
							Nil ->
								if currentState && countSelf
								then Number 1 Nul
								else Number 0 Nul,
							Tile rightIndex rightState rightNext ->
								if rightState
								then
										if currentState && countSelf
										then Number 2 $ countRowNeighbors current right countSelf
										else Number 1 $ countRowNeighbors current right countSelf
								else
										if currentState && countSelf
										then Number 1 $ countRowNeighbors current right countSelf
										else Number 0 $ countRowNeighbors current right countSelf
						}
				},
			Tile leftIndex leftState leftNext ->
				case current of {
					Nil -> Nul, -- when left is the last element
					Tile currentIndex currentState right ->
						case right of {
							Nil ->
								if leftState
								then
									if currentState && countSelf
									then Number 2 Nul
									else Number 1 Nul
								else
									if currentState && countSelf
									then Number 1 $ Nul
									else Number 0 $ Nul,
							Tile rightIndex rightState rightNext ->
							if leftState
							then
								if rightState
								then
									if currentState && countSelf
									then Number 3 $ countRowNeighbors current right countSelf
									else Number 2 $ countRowNeighbors current right countSelf
								else
									if currentState && countSelf
									then Number 2 $ countRowNeighbors current right countSelf
									else Number 1 $ countRowNeighbors current right countSelf
							else
								if rightState
								then
									if currentState && countSelf
									then Number 2 $ countRowNeighbors current right countSelf
									else Number 1 $ countRowNeighbors current right countSelf
								else
									if currentState && countSelf
									then Number 1 $ countRowNeighbors current right countSelf
									else Number 0 $ countRowNeighbors current right countSelf
						}
				}
		}

-- Takes 3 IntList zips them into 1 IntList, by suming all the same index values
zipSum : IntList -> IntList -> IntList -> IntList
zipSum top middle bottom =
	case top of {
		Nul -> Nul,
		Number topNumNeighbors topNext ->
			case middle of {
				Nul -> Nul,
				Number middleNumNeighbors middleNext ->
					case bottom of {
						Nul -> Nul,
						Number bottomNumNeighbors bottomNext ->
							let sum = topNumNeighbors + middleNumNeighbors + bottomNumNeighbors in
              Number sum (zipSum topNext middleNext bottomNext)
					}
			}
	}

--
zipSumEdge : IntList -> IntList -> IntList
zipSumEdge middle other =
	case other of {
		Nul -> Nul,
		Number otherNumNeighbors otherNext ->
			case middle of {
				Nul -> Nul,
				Number middleNumNeighbors middleNext ->
					let sum = otherNumNeighbors + middleNumNeighbors in
					Number sum (zipSumEdge middleNext otherNext)
			}
	}

-- Given a List of World tiles and a list of number of neighbors, both with the same size
-- Will calculete the next state of a tile acording to the same index number of neighbors
-- from the "numNeighborsList"
gameOfLife : World -> IntList -> World
gameOfLife row numNeighborsList =
		case row of{
			Nil -> Nil,
			Tile index state next ->
					case numNeighborsList of{
						Nul -> Nil,
						Number numNeighbors xs ->
								let newState = applyGoLRules numNeighbors state in
								let newNext = gameOfLife next xs in
								Tile index newState newNext
					}
		}

-- Applies the Game of life rules given a number of neighbors and current state
-- returs the next correct state
applyGoLRules : Int -> Bool -> Bool
applyGoLRules numNeighbors alive =
			if alive && numNeighbors < 2 then False            -- underpopulation
			else if alive && numNeighbors > 3 then False       -- overpopulation
			else if (not alive) && numNeighbors == 3 then True -- reproduction
			else alive


-- MAIN ----------------------------------------------------------------------------
main : String
main =
			let numOfGenerations = 1000 in
			let worldSize = 12000 in
			let rowSize = 200 in
			let world = initWorld worldSize in
			printWorld world rowSize rowSize;
			printStringLn " ";
			printStringLn " ";
			let _ = generations numOfGenerations worldSize rowSize (world) in
			" "

initWorld : Int -> World
initWorld n = if n == 0
              then Nil
              else Tile n (multiplesThree n) (initWorld (n-1))

multiplesThree : Int -> Bool
multiplesThree n = (mod n 3) == 0

printWorld : World -> Int -> Int -> ()
printWorld world rowSize i =
 case world of {
    Nil ->
       printString " ",
    Tile _ b l ->
       let _ = if b
               then printString "."
               else printString " " in
       let i = if i == 1
               then
                 let _ = printUnitLn () in
                 rowSize
               else i-1
       in printWorld l rowSize i
    }
