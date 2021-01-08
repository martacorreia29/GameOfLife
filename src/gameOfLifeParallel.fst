

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
      		let (world, s) = serverWorld[a] s in
      		let world = splitWork iterations size rowSize world in
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
anotherWorld : Int -> Int -> Int -> World -> World
anotherWorld iterations size rowSize world =
	if iterations == 1
	then world
	else
	  let(w, r) = new WorldChannel in
		let newGen = splitWork r world size size rowSize in --TODO
		anotherWorld (iterations-1) size rowSize newGen

-- [  top ]
-- [middle]
-- [bottom]
splitWork : dualof WorldChannel -> World -> Int -> Int -> Int -> dualof WorldChannel
splitWork topRead world index size rowSize =
	if index == size
	then
		-- TOP ROW
		let (row, tail) = splitRow world rowSize in
		let (write2, read2) = new WorldChannel in
		let bottomRead = splitWork read2 tail in
		let _ = fork(subserverTop row bottomRead write2) in
		read2 -- to ignore
	else if index == 0
		then
			-- BOTTOM ROW
			let (row, tail) = splitRow world rowSize in
	    let (write, read) = new WorldChannel in
	    let _ = fork(subserverBotton row topRead write) in
	    read
		else
			-- MIDDLE ROWS
	    let (row, tail) = splitRow world rowSize in
	    let (write, read) = new WorldChannel in
	    let (write2, read2) = new WorldChannel in
	    let bottomRead = splitWork read2 tail in
	    let _ = fork(subserver row topRead bottomRead write write2) in
	    read

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

subserverTop : World -> dualof WorldChannel -> WorldChannel -> World
subserverTop row bottomRead write =
		let _ = clientWorld[Skip] write row in
		let (rowBottom, write) = serverWorld[Skip] bottomRead in
		generateTop row rowBottom

subserver : World -> dualof WorldChannel -> dualof WorldChannel -> WorldChannel -> WorldChannel -> World
subserver row topRead bottomRead write write2 =
		let _ = clientWorld[Skip] write row in
		let _ = clientWorld[Skip] write2 row in
		let (rowTop, write) = serverWorld[Skip] topRead in
		let (rowBottom, write) = serverWorld[Skip] bottomRead in
		generate rowTop row rowBottom

subserverBottom : World -> dualof WorldChannel -> WorldChannel -> World
subserverBottom row topRead write =
		let _ = clientWorld[Skip] write row in
		let (rowTop, write) = serverWorld[Skip] topRead in
		generateBottom rowTop row

-- TODO GENERATES

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
