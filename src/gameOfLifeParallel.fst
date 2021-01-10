-- Represents a linked list of bools
data World = Nil | Tile Int Bool World

-- A simple linked int list, used to store the number of neighbors around a tile
data IntList = Nul | Number Int IntList

-- Channel used to transfer objects inside of World
type TileChannel : SL =
	&{ Index : !Int; TileChannel,
       State : !Bool; TileChannel,
       Next  : WorldChannel; TileChannel,
	   Exit  : Skip
	}

-- Channel used to transfer World
type WorldChannel : SL =
	+{ Tile: TileChannel,
       Nil : Skip
  	}

-- Channel used to pass key values and a world
type GameChannel : SL =
	+{ World : !Int; !Int; !Int; WorldChannel}

-- TBD
type ServerChannel : SL =
	+{ World : WorldChannel}

-- CLIENT --------------------------------------------------------------------
client : forall a:SL => GameChannel; a -> Int -> Int -> Int -> World -> a
client c iterations size rowSize world =
	        let c = select World c in
			let c = send iterations c in
      		let c = send size c in
      		let c = send rowSize c in
       		let c = clientWorld[a] c world in
      		c

clientWorld : forall a:SL => WorldChannel; a -> World -> a
clientWorld c world =
	case world of {
      Nil ->
      	select Nil c,
      Tile index state next ->
      	clientTile[a] (select Tile c) index state next
      }

clientTile : forall a:SL => TileChannel; a -> Int -> Bool -> World -> a
clientTile c index state next =
	match c with {
      Index c ->
      	clientTile[a] (send index c) index state next,
      State c ->
        clientTile[a] (send state c) index state next,
      Next c ->
      	let c = clientWorld[TileChannel;a] c next in
      	clientTile[a] c index state next,
	  Exit c ->
      	c
    }

-- SERVER ------------------------------------------------------------------------------
server : forall a:SL => dualof GameChannel; a -> a
server s =
	match s with {
        World s ->
      		let (iterations, s) = receive s in
      		let (size, s) = receive s in
      		let (rowSize, s) = receive s in
      		let (world, s) = serverWorld[a] s in
					let world = generations iterations size rowSize world in
      		s
   }

serverWorld : forall a:SL => dualof WorldChannel; a -> (World, a)
serverWorld s =
	match s	with {
      Nil s ->
      	(Nil, s),
      Tile s ->
      	let (world, s) = serverTile[a] s in
      	(world, s)
    }

serverTile : forall a:SL => dualof TileChannel; a -> (World, a)
serverTile s =
		let (index, s) = receive (select Index s) in
		let (state, s) = receive (select State s) in
		let c = (select Next s) in
		let (next, s) = serverWorld[dualof TileChannel; a] c in
        (Tile index state next, select Exit s)

-- SERVER FUNCTIONS --------------------------------------------------------------------
-- Parallelism -------------------------------------------------------------------------

-- iterations
generations : Int -> Int -> Int -> World -> World
generations iterations size rowSize world =
	if iterations == 1
	then world
	else
	  let (w, r) = new WorldChannel in
		let read = splitWork r world size size rowSize in
		let (newGen, _) = serverWorld[Skip] read in
		generations (iterations-1) size rowSize newGen

-- [  top ]
-- [middle]
-- [bottom]
splitWork : dualof WorldChannel -> World -> Int -> Int -> Int -> dualof WorldChannel
splitWork topRead world index size rowSize =
	if index == size
	then
		-- TOP ROW
		let (row, tail) = splitRow world rowSize in
		let (write, read) = new WorldChannel in
		let (write2, read2) = new WorldChannel in
		let bottomRead = splitWork read2 tail (index - 1) size rowSize in
		let _ = fork(subserverTop row bottomRead write write2) in
		read
	else
		if index == 0
		then
			-- BOTTOM ROW
			let (row, tail) = splitRow world rowSize in
	    let (write, read) = new WorldChannel in
	    let _ = fork(subserverBottom row topRead write) in
	    read
		else
			-- MIDDLE ROWS
	    let (row, tail) = splitRow world rowSize in
	    let (write, read) = new WorldChannel in
	    let (write2, read2) = new WorldChannel in
	    let bottomRead = splitWork read2 tail (index - 1) size rowSize in
	    let _ = fork(subserver row topRead bottomRead write write2) in
	    read

--
splitRow : World -> Int -> (World, World)
splitRow world rowSize =
		case world of {
			Nil -> (Nil, Nil),
			Tile index state next ->
				if rowSize == 1
				then
				 	( Tile index state Nil, Tile index state next)
				else
					let (row, tail) = splitRow next (rowSize-1) in
					( Tile index state row, tail)
		}

--
subserverTop : World -> dualof WorldChannel -> WorldChannel -> WorldChannel -> ()
subserverTop row bottomRead write write2 =
		let _ = clientWorld[Skip] write2 row in
		let (rowBottom, _) = serverWorld[Skip] bottomRead in
		let world = generateEdge row rowBottom in
		let (bottomWorld, _) = serverWorld[Skip] bottomRead in
		let _ = clientWorld[Skip] write (concat world bottomWorld) in
		()

subserver : World -> dualof WorldChannel -> dualof WorldChannel -> WorldChannel -> WorldChannel -> ()
subserver row topRead bottomRead write write2 =
		let _ = clientWorld[Skip] write row in
		let _ = clientWorld[Skip] write2 row in
		let (rowTop, _) = serverWorld[Skip] topRead in
		let (rowBottom, bottomRead) = serverWorld[Skip] bottomRead in
		let world = generateMiddle rowTop row rowBottom in
		let (bottomWorld, _) = serverWorld[Skip] bottomRead in
		let _ = clientWorld[Skip] write (concat world bottomWorld) in
		()

subserverBottom : World -> dualof WorldChannel -> WorldChannel -> ()
subserverBottom row topRead write =
		let _ = clientWorld[Skip] write row in
		let (rowTop, write) = serverWorld[Skip] topRead in
		let world = generateEdge rowTop row in
		let _ = clientWorld[Skip] write world in
		()

concat : World -> World -> World
concat xs ys =
  case xs of {
    Nil -> ys,
    Tile i s xs' -> Tile i s (concat xs' ys)
  }

generateEdge : World -> World -> World
generateEdge row otherRow =
		let numNeighborsMainList = countRowNeighbors Nil row False in
		let numNeighborsOtherList = countRowNeighbors Nil otherRow True in
		let numNeighborsList = zipSumEdge numNeighborsMainList numNeighborsOtherList in
		gameOfLife row numNeighborsList

-- Will calculate the next generation states of the Tiles in the "row" given
-- returns the next game of life middle row
-- Takes 3 list of World tiles of size n and will create a Intlist of the same size with
-- the number of neighbors of each tile
generateMiddle : World -> World -> World -> World
generateMiddle rowTop row rowBottom =
		let numNeighborsTopList = countRowNeighbors Nil rowTop True in
		let numNeighborsMainList = countRowNeighbors Nil row False in
		let numNeighborsBottomList = countRowNeighbors Nil rowBottom True in
		let numNeighborsList = zipSum numNeighborsTopList numNeighborsMainList numNeighborsBottomList in
		gameOfLife row numNeighborsList

-- [l][i][r]
-- For each tile in the row, it will count if l i and r are alive and place that number in i
-- returns a list of all the alive tiles for each (l, i, r) group
countRowNeighbors : World -> World -> Bool -> IntList
countRowNeighbors left current countSelf =
		case left of {
			Nil ->
				case current of {
					Nil -> Nul,
					Tile currentIndex currentState currentNext ->
						case currentNext of {
							Nil ->
								if currentState && countSelf
								then Number 1 Nul
								else Number 0 Nul,
							Tile rightIndex rightState rightNext ->
								if rightState
								then
										if currentState && countSelf
										then Number 2 $ countRowNeighbors current currentNext countSelf
										else Number 1 $ countRowNeighbors current currentNext countSelf
								else Number 0 $ countRowNeighbors current currentNext countSelf
						}
				},
			Tile leftIndex leftState leftNext ->
				case current of {
					Nil -> Nul, -- when left is the last element
					Tile currentIndex currentState currentNext ->
						case currentNext of {
							Nil ->
								if leftState
								then
									if currentState && countSelf
									then Number 2 Nul
									else Number 1 Nul
								else Number 0 Nul,
							Tile rightIndex rightState rightNext ->
							if leftState
							then
								if rightState
								then
									if currentState && countSelf
									then Number 3 $ countRowNeighbors current currentNext countSelf
									else Number 2 $ countRowNeighbors current currentNext countSelf
								else Number 1 $ countRowNeighbors current currentNext countSelf
							else Number 0 $ countRowNeighbors current currentNext countSelf
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
					Number sum (zipSum middleNext otherNext)
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
			else alive                                         -- live on

-- MAIN --------------------------------------------------------------------------------
main : ()
main =
  let (c, s) = new GameChannel in
  fork (sink (client[Skip] c 10 99 10 (initWorld 99)));
  sink(server[Skip] s)

initWorld : Int -> World
initWorld n = if n == 0
              then Nil
              else Tile n (semiRandomBool n) (initWorld (n-1))

semiRandomBool : Int -> Bool
semiRandomBool n = n == 45 || n == 46 || n == 47 || n == 56 || n == 36

-- Prints the world with chars
printWorld : forall a:SL => World -> Int -> ()
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

sink : Skip -> ()
sink _ = ()
