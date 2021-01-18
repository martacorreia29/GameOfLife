{-
-- Module      :  Conway's Game of Life
-- Description :  Parallelization of Conway's Game of Life algorithm
-- Authores    :  Diogo Soares Nº 44935; Marta Correia Nº 51022
--
-- The following is an attempt at parallazing Conway's Game of Life algorithm by
-- dividing the world matrix in partitions and processing each partition on
-- a diffente thread. Each thread will then divide the partition in rows
-- and apply the algorithm to each row individually, taking into account the
-- neightbouring upper and bottom rows.
 -}

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

-- Channel used to transfer Ints inside of a IntList
type NumberChannel : SL =
	&{ Num : !Int; NumberChannel,
	   Next : +{ Number: NumberChannel,
	     Nul : Skip
		}; NumberChannel,
	   Exit : Skip
	}

-- Channel used to transfer a IntList
type IntListChannel : SL =
	+{ Number: NumberChannel,
	     Nul : Skip
		}

----------------------------------------------------------------------------------------
-- CHANNEL CLIENT END FUNCTIONS --------------------------------------------------------
----------------------------------------------------------------------------------------

---
-- It will iterate recursively over a World linked list,
-- callig clietTile for each tile in the list
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
-- For each TileChannel channel this function receives it will send to the other
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
-- Simillar to clientWorld but for IntLists linked lists
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
-- Simillar to clientTile but passes to the other end of the channel a Int num
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
-- Depeding o the state of the dualof channel received if its a Tile was send
-- throw the channel it will call serverTile to process it.
-- returns the complet received world
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
-- Given a dualof TileChannel, it will wait to receive the index and state from the other end of the channel and
-- recursively recostruct the world being send throw the channels.
---
serverTile : forall a:SL => dualof TileChannel; a -> (World, a)
serverTile s =
		let (index, s) = receive (select Index s) in
		let (state, s) = receive (select State s) in
		let c = (select Next s) in
		let (next, s) = serverWorld[dualof TileChannel; a] c in
        (Tile index state next, select Exit s)

---
-- Simillar to serverWorld but for IntLists linked lists
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
-- Simillar to serverTile but it will recostruct a Intlist
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
-- to generate the next generation of the game of life,
-- if the cores == 1 then it will the the algorithm sequencially.
-- returns the end resulto of each generate.
---
generations : Int -> Int -> Int -> Int -> World -> World
generations iterations size rowSize cores world =
	if iterations == 0
	then world
	else
		let partitionSize = ((size/rowSize)/cores) in
		let numOfRows = (size/rowSize) in
		if partitionSize == numOfRows
		then
			-- Sequential
			let (_,newGen) = splitWorkSeq world Nul partitionSize partitionSize rowSize in
			generations (iterations-1) size rowSize cores newGen
		else
			-- Par
		  let (w, r) = new IntListChannel in
			let _ = select Nul w in -- TO USE LINEAR VAR
			let (read, read2) = splitWork r world numOfRows numOfRows rowSize partitionSize in
			let (_,_) = serverList[Skip] read in
			let (newGen, _) = serverWorld[Skip] read2 in
			generations (iterations-1) size rowSize cores newGen

---
-- [  top ]
-- [middle]
-- [middle]
--   ...
-- [bottom]
--
-- This recursive function will split the given linked list world in n parts of partitionSize * rowSize, each of these
-- n part will be given to a subserver running on a new thread, it will also create 2 IntListChannels and a WorldChannel
-- for each subserver, the former are to pass information between subserver during calculation, the latter is used by
-- each subserver to return the result world up the subserver chain. This subserver are created recursively and are chained linked
-- by the channels.
--
-- topRead: the receiving end of a IntListChannel created by the recursive parent of this current recursive iteration
-- world: a world liked list
-- size: number of row
-- rowSize: size of each row
-- partitionSize: number of row on a partition
-- retuns a pair composed of the receiving end of bottom liked subserver IntListChannel and WorldChannel
---
splitWork : dualof IntListChannel -> World -> Int -> Int -> Int -> Int -> (dualof IntListChannel, dualof WorldChannel)
splitWork topRead world index size rowSize partitionSize =
	if index == size
	then
		-- TOP ROW
		let (_, _) = serverList[Skip] topRead in -- TO USE LINEAR VAR
		let (partition, tail) = splitRow world (partitionSize*rowSize) in
		let (write, read) = new IntListChannel in
		let (write2, read2) = new IntListChannel in
		let (write3, read3) = new WorldChannel in
		let (bottomRead, bottomRead2) = splitWork read2 tail (index - partitionSize) size rowSize partitionSize in
		let _ = fork(subserverTop partition partitionSize partitionSize rowSize bottomRead bottomRead2 write write2 write3) in
		(read, read3)
	else
	-- BOTTOM ROW
		if index <= partitionSize
		then
			let leftOver = if (index == partitionSize) then partitionSize else index in
			let (partition, tail) = splitRow world (leftOver*rowSize) in
	    let (write, read) = new IntListChannel in
			let (write2, read2) = new WorldChannel in
	    let _ = fork(subserverBottom partition leftOver leftOver rowSize topRead write write2) in
	    (read, read2)
		else
			-- MIDDLE ROWS
	    let (partition, tail) = splitRow world (partitionSize*rowSize) in
	    let (write, read) = new IntListChannel in
	    let (write2, read2) = new IntListChannel in
			let (write3, read3) = new WorldChannel in
	    let (bottomRead, bottomRead2) = splitWork read2 tail (index - partitionSize) size rowSize partitionSize in
	    let _ = fork(subserver partition partitionSize partitionSize rowSize topRead bottomRead bottomRead2 write write2 write3) in
	    (read, read3)

---
-- Given a linked list and a rowSize this function will split the list at rowSize
-- returs a pair containing the a list of the first rowSize elemests of world
-- and the remaing world list without those first rowSize elemests
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
-- Subserver that will apply the Gol algorithm to the upper partition of the world list,
-- calls splitWorkSeqTop to process the partition, passing all the IntListChannels to it,
-- from down the chain reads the bottomRead WorldChannel to receive the processed bottom part of the world list
-- concats the process partition returned by splitWorkSeqTop to the processed bottom part of the world list
-- and sends it up the chain, in this case the main thread.
---
subserverTop : World -> Int -> Int -> Int -> dualof IntListChannel -> dualof WorldChannel -> IntListChannel -> IntListChannel -> WorldChannel -> ()
subserverTop partition index size rowSize bottomRead bottomRead2 write write2 write3 =
		let _ = select Nul write in
		let (intList, world) = splitWorkSeqTop partition Nul index size rowSize bottomRead write2  in
		let (bottomWorld, _) = serverWorld[Skip] bottomRead2 in
		let _ = clientWorld[Skip] write3 (concat world bottomWorld) in
		()

---
-- Subserver that will apply the Gol algorithm to the middle partitions of the world list,
-- calls splitWorkSeqMiddle to process the partition, passing all the IntListChannels to it,
-- from down the chain reads the bottomRead WorldChannel to receive the processed bottom part of the world list
-- concats the process partition returned by splitWorkSeqMiddle to the processed bottom part of the world list
-- and sends it up the chain.
---
subserver : World -> Int -> Int -> Int -> dualof IntListChannel -> dualof IntListChannel -> dualof WorldChannel  -> IntListChannel -> IntListChannel -> WorldChannel -> ()
subserver partition index size rowSize topRead bottomRead bottomRead2 write write2 write3 =
		let (intList, world) = splitWorkSeqMiddle partition Nul index size rowSize topRead bottomRead write write2  in
		let (bottomWorld, _) = serverWorld[Skip] bottomRead2 in
		let _ = clientWorld[Skip] write3 (concat world bottomWorld) in
		()

---
-- Subserver that will apply the Gol algorithm to the bottom partition of the world list,
-- calls splitWorkSeqBottom to process the partition, passing all the IntListChannels to it,
-- and sends process partition returned by splitWorkSeqMiddle up the subserver chain.
---
subserverBottom : World -> Int -> Int -> Int -> dualof IntListChannel -> IntListChannel -> WorldChannel -> ()
subserverBottom partition index size rowSize topRead write write2 =
		let (intList, world) = splitWorkSeqBottom partition Nul index size rowSize topRead write in
		let _ = clientWorld[Skip] write2 world in
		()

---
-- Receives the and process the upper partition of the main world list
-- This recursive function will divide the world linked list in rows of rowSize,
-- for each row it will calculate a Intlist that on each node on the list will
-- contain the number of alive neighbors (left and right and maybe self) that the node has.
-- On each row two of this IntLists will be created numNeighbors and numNeighborsWithSelf,
-- numNeighborsWithSelf will be send down and up the recursive call stack.
-- On each row after receiving the IntLists topRow (number neighbors list) from up the recursive call stack
-- and the rowBottom (number neighbors list) from down the recursive call stack it will
-- zip sum these 2 lists with numNeighbors and call gameOfLife function to apply the rules of Gol
-- to row given that sumed list of neighbors. The result process row is then send up the recursive call stack.
--
-- On the bottom row of this world list, there is need to communicate with subserver down the linked chain
-- using the IntListChannels to give the bottom's numNeighborsWithSelf and receive bottomRow from that subserver.
-- Note: if size == 1 there is no need for recursive calls
---
splitWorkSeqTop : World -> IntList -> Int -> Int -> Int -> dualof IntListChannel -> IntListChannel -> (IntList, World)
splitWorkSeqTop world topRow index size rowSize bottomRead write2 =
	-- only 1 ROW
	if size == 1
	then
		let (row, tail) = splitRow world rowSize in
		let numNeighbors = countRowNeighbors Nil row False in
		let numNeighborsWithSelf = countRowNeighbors Nil row True in
		let (rowBottom, _) = serverList[Skip] bottomRead in
		let _ = clientList[Skip] write2 numNeighborsWithSelf in
		let sumNeighbors = zipSumEdge numNeighbors rowBottom in
		let newWorld = gameOfLife row sumNeighbors in
		(numNeighborsWithSelf, newWorld)
	else
	if index == size
	then
		-- TOP ROW
		let (row, tail) = splitRow world rowSize in
		let numNeighbors = countRowNeighbors Nil row False in
		let numNeighborsWithSelf = countRowNeighbors Nil row True in
		let (bottomRow, bottomWorld) = splitWorkSeqTop tail numNeighborsWithSelf (index - 1) size rowSize bottomRead write2 in
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
			let (rowBottom, _) = serverList[Skip] bottomRead in
			let _ = clientList[Skip] write2 numNeighborsWithSelf in
			let sumNeighbors = zipSum topRow numNeighbors rowBottom in
			let newWorld = gameOfLife row sumNeighbors in
	    (numNeighborsWithSelf, newWorld)
		else
			-- MIDDLE ROWS
	    let (row, tail) = splitRow world rowSize in
			let numNeighbors = countRowNeighbors Nil row False in
			let numNeighborsWithSelf = countRowNeighbors Nil row True in
			let (bottomRow, bottomWorld) = splitWorkSeqTop tail numNeighborsWithSelf (index - 1) size rowSize bottomRead write2 in
	    let sumNeighbors = zipSum topRow numNeighbors bottomRow in
			let newWorld = gameOfLife row sumNeighbors in
			(numNeighborsWithSelf, concat newWorld bottomWorld)

---
-- Receives the and process the middle partitions of the main world list
-- This recursive function will divide the world linked list in rows of rowSize,
-- for each row it will calculate a Intlist that on each node on the list will
-- contain the number of alive neighbors (left and right and maybe self) that the node has.
-- On each row two of this IntLists will be created numNeighbors and numNeighborsWithSelf,
-- numNeighborsWithSelf will be send down and up the recursive call stack.
-- On each row after receiving the IntLists topRow (number neighbors list) from up the recursive call stack
-- and the rowBottom (number neighbors list) from down the recursive call stack it will
-- zip sum these 2 lists with numNeighbors and call gameOfLife function to apply the rules of Gol
-- to row given that sumed list of neighbors. The result process row is then send up the recursive call stack.
--
-- On the upper row of the world list, there is need to communicate with subserver up the linked chain
-- using the IntListChannels to give the upper row's numNeighborsWithSelf and receive rowTop from that subserver.
-- On the bottom row of the world list, there is need to communicate with subserver down the linked chain
-- using the IntListChannels to give the bottom row's numNeighborsWithSelf and receive bottomRow from that subserver.
-- Note: if size == 1 there is no need for recursive calls
---
splitWorkSeqMiddle : World -> IntList -> Int -> Int -> Int -> dualof IntListChannel -> dualof IntListChannel -> IntListChannel -> IntListChannel -> (IntList, World)
splitWorkSeqMiddle world topRow index size rowSize topRead bottomRead write write2 =
	-- only 1 ROW
	if size == 1
	then
		let (row, tail) = splitRow world rowSize in
		let numNeighbors = countRowNeighbors Nil row False in
		let numNeighborsWithSelf = countRowNeighbors Nil row True in
		let _ = clientList[Skip] write numNeighborsWithSelf in
		let (rowBottom, _) = serverList[Skip] bottomRead in
		let _ = clientList[Skip] write2 numNeighborsWithSelf in
		let (rowTop, _) = serverList[Skip] topRead in
		let sumNeighbors = zipSum rowTop numNeighbors rowBottom in
		let newWorld = gameOfLife row sumNeighbors in
		(numNeighborsWithSelf, newWorld)
	else
	if index == size
	then
		-- TOP ROW
		let (row, tail) = splitRow world rowSize in
		let numNeighbors = countRowNeighbors Nil row False in
		let numNeighborsWithSelf = countRowNeighbors Nil row True in
		let (c, s) = new IntListChannel in -- create dummy
		let _ = clientList[Skip] write numNeighborsWithSelf in
		let (bottomRow, bottomWorld) = splitWorkSeqMiddle tail numNeighborsWithSelf (index - 1) size rowSize s bottomRead c write2 in
		let (rowTop, _) = serverList[Skip] topRead in
		let sumNeighbors = zipSum rowTop numNeighbors bottomRow in
		let newWorld = gameOfLife row sumNeighbors in
		(numNeighborsWithSelf, concat newWorld bottomWorld)
	else
	-- BOTTOM ROW
		if index == 1
		then
			let _ = select Nul write in -- use Dummy
			let (_,_) = serverList[Skip] topRead in -- use Dummy
			let (row, tail) = splitRow world rowSize in
			let numNeighbors = countRowNeighbors Nil row False in
			let numNeighborsWithSelf = countRowNeighbors Nil row True in
			let (rowBottom, _) = serverList[Skip] bottomRead in
			let _ = clientList[Skip] write2 numNeighborsWithSelf in
			let sumNeighbors = zipSum topRow numNeighbors rowBottom in
			let newWorld = gameOfLife row sumNeighbors in
	    (numNeighborsWithSelf, newWorld)
		else
			-- MIDDLE ROWS
	    let (row, tail) = splitRow world rowSize in
			let numNeighbors = countRowNeighbors Nil row False in
			let numNeighborsWithSelf = countRowNeighbors Nil row True in
			let (bottomRow, bottomWorld) = splitWorkSeqMiddle tail numNeighborsWithSelf (index - 1) size rowSize topRead bottomRead write write2 in
	    let sumNeighbors = zipSum topRow numNeighbors bottomRow in
			let newWorld = gameOfLife row sumNeighbors in
			(numNeighborsWithSelf, concat newWorld bottomWorld)


---
-- Receives the and process the bottom partition of the main world list
-- This recursive function will divide the world linked list in rows of rowSize,
-- for each row it will calculate a Intlist that on each node on the list will
-- contain the number of alive neighbors (left and right and maybe self) that the node has.
-- On each row two of this IntLists will be created numNeighbors and numNeighborsWithSelf,
-- numNeighborsWithSelf will be send down and up the recursive call stack.
-- On each row after receiving the IntLists topRow (number neighbors list) from up the recursive call stack
-- and the rowBottom (number neighbors list) from down the recursive call stack it will
-- zip sum these 2 lists with numNeighbors and call gameOfLife function to apply the rules of Gol
-- to row given that sumed list of neighbors. The result process row is then send up the recursive call stack.
--
-- On the upper row of the world list, there is need to communicate with subserver up the linked chain
-- using the IntListChannels to give the upper row's numNeighborsWithSelf and receive rowTop from that subserver.
-- Note: if size == 1 there is no need for recursive calls
---
splitWorkSeqBottom : World -> IntList -> Int -> Int -> Int -> dualof IntListChannel -> IntListChannel -> (IntList, World)
splitWorkSeqBottom world topRow index size rowSize topRead write =
	-- only 1 ROW
	if size == 1
	then
		let (row, tail) = splitRow world rowSize in
		let numNeighbors = countRowNeighbors Nil row False in
		let numNeighborsWithSelf = countRowNeighbors Nil row True in
		let _ = clientList[Skip] write numNeighborsWithSelf in
		let (rowTop, _) = serverList[Skip] topRead in
		let sumNeighbors = zipSumEdge rowTop numNeighbors in
		let newWorld = gameOfLife row sumNeighbors in
		(numNeighborsWithSelf, newWorld)
	else
	if index == size
	then
		-- TOP ROW
		let (row, tail) = splitRow world rowSize in
		let numNeighbors = countRowNeighbors Nil row False in
		let numNeighborsWithSelf = countRowNeighbors Nil row True in
		let (c, s) = new IntListChannel in -- create dummy
		let _ = clientList[Skip] write numNeighborsWithSelf in
		let (bottomRow, bottomWorld) = splitWorkSeqBottom tail numNeighborsWithSelf (index - 1) size rowSize s c in
		let (rowTop, _) = serverList[Skip] topRead in
		let sumNeighbors = zipSum rowTop numNeighbors bottomRow in
		let newWorld = gameOfLife row sumNeighbors in
		(numNeighborsWithSelf, concat newWorld bottomWorld)
	else
	-- BOTTOM ROW
		if index == 1
		then
			let _ = select Nul write in -- use Dummy
			let (_,_) = serverList[Skip] topRead in -- use Dummy
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
			let (bottomRow, bottomWorld) = splitWorkSeqBottom tail numNeighborsWithSelf (index - 1) size rowSize topRead write in
	    let sumNeighbors = zipSum topRow numNeighbors bottomRow in
			let newWorld = gameOfLife row sumNeighbors in
			(numNeighborsWithSelf, concat newWorld bottomWorld)

---
-- This recursive function will divide the world linked list in rows of rowSize,
-- for each row it will calculate a Intlist that on each node on the list will
-- contain the number of alive neighbors (left and right and maybe self) that the node has.
-- On each row two of this IntLists will be created numNeighbors and numNeighborsWithSelf,
-- numNeighborsWithSelf will be send down and up the recursive call stack.
-- On each row after receiving the IntLists topRow (number neighbors list) from up the recursive call stack
-- and the rowBottom (number neighbors list) from down the recursive call stack it will
-- zip sum these 2 lists with numNeighbors and call gameOfLife function to apply the rules of Gol
-- to row given that sumed list of neighbors. The result process row is then send up the recursive call stack.
---
splitWorkSeq : World -> IntList -> Int -> Int -> Int -> (IntList, World)
splitWorkSeq world topRow index size rowSize =
	if index == size
	then
		-- TOP ROW
		let (row, tail) = splitRow world rowSize in
		let numNeighbors = countRowNeighbors Nil row False in
		let numNeighborsWithSelf = countRowNeighbors Nil row True in
		let (bottomRow, bottomWorld) = splitWorkSeq tail numNeighborsWithSelf (index - 1) size rowSize in
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
			let (bottomRow, bottomWorld) = splitWorkSeq tail numNeighborsWithSelf (index - 1) size rowSize in
	    let sumNeighbors = zipSum topRow numNeighbors bottomRow in
			let newWorld = gameOfLife row sumNeighbors in
			(numNeighborsWithSelf, concat newWorld bottomWorld)

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
-- [l][i][r]
-- For each tile in the row, it will count if l i and r are alive and place that number in i.
-- countSelf: If i is alive and this is true, i will be counted.
-- returns a list of all the alive tiles for each (l, i, r) group
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
-- Takes 3 IntList zips them into 1 IntList, by suming all the same index values
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
-- Creates a new linked list IntList that is the zip sum of two Intlist lists
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
-- Given a List of World tiles and a list of number of neighbors, both with the same size
-- Will calculete the next state of a tile acording to the same index number of neighbors
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
-- returs the next correct state
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
-- Main:
-- Iniciates the world
-- Prints the inicial worldSize
-- Calls generations to apply the algorithm
-- Prints the end result world
---
main : String
main =
	let cores = 4 in
	let numOfGenerations = 10 in
	let worldSize = 1000 in
	let rowSize = 100 in -- (worldSize/rowSize) / cores == whole number ?
  let world = initWorld worldSize in
  printWorld world rowSize rowSize;
  printStringLn " ";
	printStringLn " ";
  let world = generations numOfGenerations worldSize rowSize cores (world) in
	let _ = printWorld world rowSize rowSize in " "


----
-- Creates a liked list of size n, representing the world
---
initWorld : Int -> World
initWorld n = if n == 0
              then Nil
              else Tile n (multiplesThree n) (initWorld (n-1))

----
-- Returns true if n is a multiple of 3
-- used to randamize alive cells at the start of the simulatio
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
-- Prints a IntList
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
