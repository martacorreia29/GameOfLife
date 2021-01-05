

-- Represents a linked list of bools
data World = Nil | Tile Int Bool World

-- Represents a linked list of channels
data ChannelList = Nul | C (dualof ServerChannel) ChannelList


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
      		let (world, s) = serverWorld[a] s size rowSize in
      		let world = splitWork iterations size rowSize world in
      		s
   }

serverWorld : forall a:SL => dualof WorldChannel; a -> Int -> Int -> (World, a)
serverWorld s size rowSize =
	match s	with {
      Nil s ->
      	(Nil, s),
      Tile s ->
      	let (world, s) = serverTile[a] s size rowSize in
      	(world, s)
    }

serverTile : forall a:SL => dualof TileChannel; a -> Int -> Int -> (World, a)
serverTile s size rowSize =
		let (index, s) = receive (select Index s) in
		let (state, s) = receive (select State s) in
		let c = (select Next s) in
		let (next, s) = serverWorld[dualof TileChannel; a] c size rowSize in
        (Tile index state next, select Exit s)

subserver : forall a:SL => dualof ServerChannel; a -> World
subserver s =
	match s with {
        World s ->
      		let (iterations, s) = receive s in
      		let (size, s) = receive s in
      		let (rowSize, s) = receive s in
      		let (world, s) = serverWorld[a] s size rowSize in
      		let world = splitWork iterations size rowSize world in
      		s
   }

-- SERVER FUNCTIONS --------------------------------------------------------------------

-- Parallelism -------------------------------------------------------------------------
anotherWorld : Int -> Int -> Int -> World -> World
anotherWorld iterations size rowSize world =
	if iterations == 1
	then world
	else
		let newGen = splitWork size rowSize world Nul in
		iterate (iterations-1) size rowSize newGen

-- nextTile: the last after split
splitWork : Int -> Int -> Int -> World -> ChannelList -> World
splitWork size rowSize world channelList =
	case world of {
		Nil -> receiveWork channelList Nil,
		Tile index state next ->
				let (splitedWorld, nextTile) = split world rowSize in
				let (s1, s2) = new ServerChannel in
				let _ = fork(sink(subserver s1 splitedWorld rowSize)) in
				let channelList = (C s2 channelList) in
				splitWork size rowSize world channelList
	}

receiveWork : ChannelList -> World -> World
receiveWork channelList world =
	case channelList of {
		Nul ->
		 	world,
		C c next ->
		  let world = serverReceive c world in
			receiveWork c world
	}

serverReceive : forall a:SL => dualof ServerChannel; a -> World -> World
serverReceive s tail =
		match s with {
					World s ->
						let (world, s) = serverReceiveWorld[a] s tail in
						world
		 }

serverReceiveWorld : forall a:SL => dualof WorldChannel; a -> World -> (World, a)
serverReceiveWorld s tail =
	match s	with {
      Nil s ->
      	(tail, s),
      Tile s ->
      	let (world, s) = serverReceiveTile[a] s tail in
      	(world, s)
    }

serverReceiveTile : forall a:SL => dualof TileChannel; a -> (World, a)
serverReceiveTile s tail =
		let (index, s) = receive (select Index s) in
		let (state, s) = receive (select State s) in
		let c = (select Next s) in
		let (next, s) = serverReceiveWorld[dualof TileChannel; a] c tail in
        (Tile index state next, select Exit s)


split : forall a:SL => ServerChannel; a -> Int -> Int -> Int -> World -> World
split s1 size rowSize numLines world =
		case world of {
			Nil ->,
			Tile index state next ->
		}

-- GOF FUNCTIONS --------------------------------------------------------------------

generate : forall a:SL => World -> World -> Int -> World
generate world current rowSize =
		case current of {
    		Nil ->
      			Nil,
    		Tile x b l ->
      			let numberOfNeighbors = countNeighbors world x rowSize in
          		let newState =
          			if b && numberOfNeighbors < 2 then False            -- underpopulation
          			else if b && numberOfNeighbors > 3 then False       -- overpopulation
          			else if (not b) && numberOfNeighbors == 3 then True -- reproduction
                    else b in                                       -- live on
          		let newList = generate[a] world l rowSize in
          		Tile x newState newList
    	}

-- Aux funtion to countNeighbors
-- finds the tile with index i and verifies if it is alive, if so returns 1 else 0
getNeighborValue : forall a:SL => World -> Int -> Int
getNeighborValue world i =
	case world of {
    Nil ->
      0,
    Tile x b l ->
      if x == i && b
      then 1
      else getNeighborValue[a] l i
    }

-- Returns the number of Neighbors of i that are alive
-- [a][b][c]
-- [d][i][e]
-- [f][g][h]
countNeighbors: World -> Int -> Int -> Int
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
