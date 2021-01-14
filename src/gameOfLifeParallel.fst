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

------------------------
type NumberChannel : SL =
	&{ Num : !Int; NumberChannel,
	   Next : +{ Number: NumberChannel,
	     Nul : Skip
		}; NumberChannel,
	   Exit : Skip
	}

type IntListChannel : SL =
	+{ Number: NumberChannel,
	     Nul : Skip
		}

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

clientList : forall a:SL => IntListChannel; a -> IntList -> a
clientList c numNeighbors =
	case numNeighbors of {
      Nul ->
      	select Nul c,
      Number num next ->
				clientNumber[a] (select Number c) num next
      }

clientNumber : forall a:SL => NumberChannel; a -> Int -> IntList -> a
clientNumber c num next =
	match c with {
      Num c ->
      	clientNumber[a] (send num c) num next,
      Next c ->
      	let c = clientList[NumberChannel;a] c next in
      	clientNumber[a] c num next,
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

serverList : forall a:SL => dualof IntListChannel; a -> (IntList, a)
serverList s =
	match s	with {
      Nul s ->
      	(Nul, s),
      Number s ->
      	let (list, s) = serverNumber[a] s in
      	(list, s)
    }

serverNumber : forall a:SL => dualof NumberChannel; a -> (IntList, a)
serverNumber s =
		let (num, s) = receive (select Num s) in
		let c = (select Next s) in
		let (next, s) = serverList[dualof NumberChannel; a] c in
        (Number num next, select Exit s)

-- SERVER FUNCTIONS --------------------------------------------------------------------
-- Parallelism -------------------------------------------------------------------------
-- iterations
generations : Int -> Int -> Int -> World -> World
generations iterations size rowSize world =
	if iterations == 0
	then world
	else
	  let (w, r) = new IntListChannel in
		let _ = select Nul w in -- TO USE LINEAR VAR
		let (read, read2) = splitWork r world (size/rowSize) (size/rowSize) rowSize in
		let (_,_) = serverList[Skip] read in
		let (newGen, _) = serverWorld[Skip] read2 in
		printStringLn " ";
		printWorld newGen 50 50;
		printStringLn " ";
		generations (iterations-1) size rowSize newGen

-- [  top ]
-- [middle]
-- [bottom]
splitWork : dualof IntListChannel -> World -> Int -> Int -> Int -> (dualof IntListChannel, dualof WorldChannel)
splitWork topRead world index size rowSize =
	if index == size
	then
		-- TOP ROW
		let (_, _) = serverList[Skip] topRead in -- TO USE LINEAR VAR
		let (row, tail) = splitRow world rowSize in
		let (write, read) = new IntListChannel in
		let (write2, read2) = new IntListChannel in
		let (write3, read3) = new WorldChannel in
		let (bottomRead, bottomRead2) = splitWork read2 tail (index - 1) size rowSize in
		let _ = subserverTop row bottomRead bottomRead2 write write2 write3 in
		(read, read3)
	else
	-- BOTTOM ROW
		if index == 1
		then
			let (row, tail) = splitRow world rowSize in
	    let (write, read) = new IntListChannel in
			let (write2, read2) = new WorldChannel in
	    let _ = fork(subserverBottom row topRead write write2) in
	    (read, read2)
		else
			-- MIDDLE ROWS
	    let (row, tail) = splitRow world rowSize in
	    let (write, read) = new IntListChannel in
	    let (write2, read2) = new IntListChannel in
			let (write3, read3) = new WorldChannel in
	    let (bottomRead, bottomRead2) = splitWork read2 tail (index - 1) size rowSize in
	    let _ = fork(subserver row topRead bottomRead bottomRead2 write write2 write3) in
	    (read, read3)

--
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

subserverTop : World -> dualof IntListChannel -> dualof WorldChannel -> IntListChannel -> IntListChannel -> WorldChannel -> ()
subserverTop row bottomRead bottomRead2 write write2 write3 =
		let _ = select Nul write in
		let numNeighbors = countRowNeighbors Nil row False in
		let numNeighborsWithSelf = countRowNeighbors Nil row True in
		let _ = clientList[Skip] write2 numNeighborsWithSelf in
		let (rowBottom, _) = serverList[Skip] bottomRead in
		let world = generateEdge numNeighbors rowBottom row in
		let (bottomWorld, _) = serverWorld[Skip] bottomRead2 in
		let _ = fork(sink(clientWorld[Skip] write3 (concat world bottomWorld))) in
		()

subserver : World -> dualof IntListChannel -> dualof IntListChannel -> dualof WorldChannel  -> IntListChannel -> IntListChannel -> WorldChannel -> ()
subserver row topRead bottomRead bottomRead2 write write2 write3 =
		let numNeighbors = countRowNeighbors Nil row False in
		let numNeighborsWithSelf = countRowNeighbors Nil row True in
		let (rowTop, _) = serverList[Skip] topRead in
		let _ = clientList[Skip] write2 numNeighborsWithSelf in
		let (rowBottom, _) = serverList[Skip] bottomRead in
		let _ = clientList[Skip] write numNeighborsWithSelf in
		let world = generateMiddle rowTop numNeighbors rowBottom row in
		let (bottomWorld, _) = serverWorld[Skip] bottomRead2 in
		let _ = clientWorld[Skip] write3 (concat world bottomWorld) in
		()

subserverBottom : World -> dualof IntListChannel -> IntListChannel -> WorldChannel -> ()
subserverBottom row topRead write write2 =
		let numNeighbors = countRowNeighbors Nil row False in
		let numNeighborsWithSelf = countRowNeighbors Nil row True in
		let (rowTop, _) = serverList[Skip] topRead in
		let _ = clientList[Skip] write numNeighborsWithSelf in
		let world = generateEdge rowTop numNeighbors row in
		let _ = clientWorld[Skip] write2 world in
		()


concat : World -> World -> World
concat xs ys =
  case xs of {
    Nil -> ys,
    Tile i s xs' -> Tile i s (concat xs' ys)
  }

generateEdge : IntList -> IntList -> World -> World
generateEdge numNeighbors otherRow row =
		let numNeighborsList = zipSumEdge numNeighbors otherRow in
		gameOfLife row numNeighborsList

-- Will calculate the next generation states of the Tiles in the "row" given
-- returns the next game of life middle row
-- Takes 3 list of World tiles of size n and will create a Intlist of the same size with
-- the number of neighbors of each tile
generateMiddle : IntList -> IntList -> IntList -> World -> World
generateMiddle rowTop numNeighbors rowBottom row =
		let numNeighborsList = zipSum rowTop numNeighbors rowBottom in
		gameOfLife row numNeighborsList

printList : IntList -> ()
printList numNeightbours =
	case numNeightbours of {
      Nul -> printString "()",
      Number num next ->
        printInt num;
        printList next
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
			else alive                                         -- live on

-- MAIN --------------------------------------------------------------------------------
main : String
main =
  let (c, s) = new GameChannel in
  let world = initWorld 1000 in
  printWorld world 50 50;
  printStringLn " ";
	printStringLn " ";
  fork (sink (client[Skip] c 1000 1000 50 (world)));
  sink(server[Skip] s);
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
               then printChar '#'
               else printChar '_' in
       let i = if i == 1
               then
                 let _ = printUnitLn () in
                 rowSize
               else i-1
       in printWorld l rowSize i
    }

printRow : World -> ()
printRow world =
 case world of {
    Nil ->
       printStringLn "()",
    Tile i b l ->
       let _ = if b
               then printChar '#'
               else printChar '_' in
       printRow l
    }

sink : Skip -> ()
sink _ = ()
