{-
-- Module      :  Conway's Game of Life
-- Description :  Parallelization of Conway's Game of Life algorithm
-- Authores    :  Diogo Soares Nº 44935; Marta Correia Nº 51022
--
-- The following it's a parallel way of implementating Conway's Game of Life algorithm by
-- dividing the world matrix in n rows and processing each row on a diffente thread.
-- Each thread will then apply the algorithm to each row individually, taking into account
-- it's neightbouring upper and bottom rows, and communicating with those threads via channels
-- to exchange their rows
 -}

-- Represents a linked list of Tiles, that represent a cell, which is made of an index (Int)
-- and a state (Bool)
data World = Nil | Tile Int Bool World

-- Represents a linked list of Numbers, that represent the number of neighbors of a cell
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

-- Channel used to transfer Ints inside of an IntList
type NumberChannel : SL =
	&{ Num : !Int; NumberChannel,
	   Next : +{ Number: NumberChannel,
	     Nul : Skip
		}; NumberChannel,
	   Exit : Skip
	}

-- Channel used to transfer an IntList
type IntListChannel : SL =
	+{ Number: NumberChannel,
	     Nul : Skip
		}

----------------------------------------------------------------------------------------
-- CHANNEL CLIENT END FUNCTIONS --------------------------------------------------------
----------------------------------------------------------------------------------------

---
-- It will iterate recursively over a World linked list,
-- callig clientTile for each tile in the list
---
clientWorld : forall a:SL => WorldChannel; a -> World -> a
clientWorld c world =
	case world of {
      Nil ->
      	select Nil c,
      Tile index state next ->
      	clientTile[a] (select Tile c) index state next
      }

---
-- For each TileChannel channel this function receives, it will send to the other
-- end of the channel the index and state that represent a World Tile
---
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

---
-- Similar to clientWorld but for IntLists linked lists
---
clientList : forall a:SL => IntListChannel; a -> IntList -> a
clientList c numNeighbors =
	case numNeighbors of {
      Nul ->
      	select Nul c,
      Number num next ->
				clientNumber[a] (select Number c) num next
      }

---
-- Similar to clientTile but passes to the other end of the channel an Int number
-- that represents a Number in the IntList
---
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

----------------------------------------------------------------------------------------
-- CHANNEL SERVER END FUNCTIONS --------------------------------------------------------
----------------------------------------------------------------------------------------

---
-- Depending o the state of the dualof channel received, if a Tile was send
-- through the channel, it will call serverTile to process it
-- Returns the complete received world
---
serverWorld : forall a:SL => dualof WorldChannel; a -> (World, a)
serverWorld s =
	match s	with {
      Nil s ->
      	(Nil, s),
      Tile s ->
      	let (world, s) = serverTile[a] s in
      	(world, s)
    }

---
-- Given a dualof TileChannel, it will wait to receive the index and state from
-- the other end of the channel and recursively reconstruct the world being
-- send through the channels
---
serverTile : forall a:SL => dualof TileChannel; a -> (World, a)
serverTile s =
		let (index, s) = receive (select Index s) in
		let (state, s) = receive (select State s) in
		let c = (select Next s) in
		let (next, s) = serverWorld[dualof TileChannel; a] c in
        (Tile index state next, select Exit s)

---
-- Similar to serverWorld but for IntLists linked lists
---
serverList : forall a:SL => dualof IntListChannel; a -> (IntList, a)
serverList s =
	match s	with {
      Nul s ->
      	(Nul, s),
      Number s ->
      	let (list, s) = serverNumber[a] s in
      	(list, s)
    }

---
-- Simillar to serverTile but it will recostruct an Intlist
---
serverNumber : forall a:SL => dualof NumberChannel; a -> (IntList, a)
serverNumber s =
		let (num, s) = receive (select Num s) in
		let c = (select Next s) in
		let (next, s) = serverList[dualof NumberChannel; a] c in
        (Number num next, select Exit s)

----------------------------------------------------------------------------------------
-- PARALLELISM FUNCTIONS ---------------------------------------------------------------
----------------------------------------------------------------------------------------

---
-- Given a number of generations (iterations), this function will call splitwork
-- to generate the next generation of the game of life
-- Returns the end result of each generate
---
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
		printWorld newGen rowSize rowSize;
		printStringLn " ";
		generations (iterations-1) size rowSize newGen

---
--[  top ]
--[middle]
--[middle]
--  ...
--[bottom]
--
-- This recursive function will split the given linked list world in n parts of rowSize. Each of these
-- n parts will be given to a subserver running on a new thread. It will also create 2 IntListChannels
-- and a WorldChannel for each subserver. The former are to pass information between subservers during
-- calculation, the later is used by each subserver to return the result world up the subserver chain.
-- These subservers are created recursively and are a chained linked by the channels
--
-- topRead: the receiving end of a IntListChannel created by the recursive parent of this current
-- recursive iteration
-- world: a world linked list
-- size: number of rows
-- rowSize: size of each row
-- Retuns a pair composed of the receiving end of bottom liked subserver IntListChannel and WorldChannel
---
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
		let _ = fork(subserverTop row bottomRead bottomRead2 write write2 write3) in
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

---
-- Given a linked list and a rowSize, this function will split the list at rowSize
-- Returs a pair containing a list of the first rowSize elements of world
-- and the remaing world list without those first rowSize elements
---
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

---
-- Subserver that will apply the Gol algorithm to the upper row of the world list,
-- after receiving the rowBottom (number neighbors list) from down the subserver chain
-- and sending numNeighborsWithSelf down the subserver chain with the IntListChannels.
-- It will call generateEdge to apply the rules of Gol to row. The result process row is then send
-- up the subserver chain using the WorldChannel (In this case, the main thread).
---
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

---
-- Subserver that will apply the Gol algorithm to the middle rows of the world list,
-- after receiving the IntLists topRow (number neighbors list) from up the subserver chain and
-- the rowBottom (number neighbors list) from down the subserver chain and sending numNeighborsWithSelf
-- up and down the subserver chain with the IntListChannels. It will then call generateMiddle to
-- apply the rules of Gol to row. The result process row is then send up the subserver
-- chain using the WorldChannel
---
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

---
-- Subserver that will apply the Gol algorithm to the bottom row of the world list,
-- after receiving the rowTop (number neighbors list) from up the subserver chain
-- and sending numNeighborsWithSelf up the subserver chain with the IntListChannels.
-- It will then call generateEdge to apply the rules of Gol to row. The result process
-- row is then send up the subserver chain using the WorldChanne
---
subserverBottom : World -> dualof IntListChannel -> IntListChannel -> WorldChannel -> ()
subserverBottom row topRead write write2 =
		let numNeighbors = countRowNeighbors Nil row False in
		let numNeighborsWithSelf = countRowNeighbors Nil row True in
		let (rowTop, _) = serverList[Skip] topRead in
		let _ = clientList[Skip] write numNeighborsWithSelf in
		let world = generateEdge rowTop numNeighbors row in
		let _ = clientWorld[Skip] write2 world in
		()

---
-- Simple function that concats two linked World lists
---
concat : World -> World -> World
concat xs ys =
  case xs of {
    Nil -> ys,
    Tile i s xs' -> Tile i s (concat xs' ys)
  }

---
-- It will zip sum these the 2 lists given and call gameOfLife function to apply the rules of Gol
-- to the row with that summed list of neighbors
---
generateEdge : IntList -> IntList -> World -> World
generateEdge numNeighbors otherRow row =
		let numNeighborsList = zipSumEdge numNeighbors otherRow in
		gameOfLife row numNeighborsList

---
-- It will zip sum these the 3 lists given and call gameOfLife function to apply the rules of Gol
-- to the row with that summed list of neighbors
---
generateMiddle : IntList -> IntList -> IntList -> World -> World
generateMiddle rowTop numNeighbors rowBottom row =
		let numNeighborsList = zipSum rowTop numNeighbors rowBottom in
		gameOfLife row numNeighborsList

---
--[l][i][r]
-- For each tile in the row, it will count if l, i and r are alive and place that number in i.
-- countSelf: If i is alive and this is true, i will be counted; otherwise, it will only counted
-- l and r as a neighbor to the cell
-- Returns a list of all the alive tiles for each (l, i, r) group
---
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

---
-- Takes 3 IntList and zips them into 1 IntList, by suming all the same index values
---
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

---
-- Takes 2 IntList and zips them into 1 IntList, by suming all the same index values
---
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

---
-- Given a List of World tiles and a list of number of neighbors, both with the same size,
-- it will calculate the next state of a tile acording to the same index number of neighbors
-- from the "numNeighborsList"
---
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

---
-- Applies the Game of life rules given a number of neighbors and current state
-- Returs the next correct state
---
applyGoLRules : Int -> Bool -> Bool
applyGoLRules numNeighbors alive =
			if alive && numNeighbors < 2 then False            -- underpopulation
			else if alive && numNeighbors > 3 then False       -- overpopulation
			else if (not alive) && numNeighbors == 3 then True -- reproduction
			else alive                                         -- live on

----------------------------------------------------------------------------------------
-- MAIN --------------------------------------------------------------------------------
----------------------------------------------------------------------------------------

----
-- Iniciates the world, prints the inicial worldSize and calls generations to apply
-- the algorithm
---
main : String
main =
	let numOfGenerations = 10 in
	let worldSize = 100 in
	let rowSize = 10 in
	let world = initWorld worldSize in
	printWorld world rowSize rowSize;
	printStringLn " ";
	printStringLn " ";
	let _ = generations numOfGenerations worldSize rowSize (world) in " "

----
-- Creates a linked list of size n, representing the world
---
initWorld : Int -> World
initWorld n = if n == 0
              then Nil
              else Tile n (multiplesThree n) (initWorld (n-1))

----
-- Used to randomize alive cells at the start of the simulation
-- Returns true if n is a multiple of 3
---
multiplesThree : Int -> Bool
multiplesThree n = (mod n 3) == 0

----
-- Prints a matrix representing the world
---
printWorld : World -> Int -> Int -> ()
printWorld world rowSize i =
 case world of {
    Nil ->
       printString " ",
    Tile _ b l ->
       let _ = if b
							 then printString "o"
							 else printString " " in
       let i = if i == 1
               then
                 let _ = printUnitLn () in
                 rowSize
               else i-1
       in printWorld l rowSize i
    }

----
-- Prints a single row of the world
---
printRow : World -> ()
printRow world =
 case world of {
    Nil ->
       printStringLn "()",
    Tile i b l ->
       let _ = if b
               then printString "o"
               else printString " " in
       printRow l
    }

----
-- Prints an IntList
---
printList : IntList -> ()
printList numNeightbours =
	case numNeightbours of {
      Nul -> printString "()",
      Number num next ->
        printInt num;
        printList next
	}

----
-- Transforms a Skip (SU) in to a ()(TU)
---
sink : Skip -> ()
sink _ = ()
