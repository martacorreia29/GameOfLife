world : World
world = Tile 0 True ((Tile 1 True (Tile 2 False (Tile 3 False Nil))))

data World = Nil | Tile Int Bool World

type Game = Int -> Int -> World

type TileChannel : SL =
	&{ Index : !Int; TileChannel,
       State : !Bool; TileChannel,
       Next  : WorldChannel; TileChannel,
	   Exit  : Skip
	}

type WorldChannel : SL =
	+{ Tile: TileChannel,
       Nil : Skip
  	}

type GameChannel : SL =
	+{ World : !Int; !Int; WorldChannel}

client : forall a:SL => GameChannel; a -> Int -> Int -> World -> a
client c size rowSize world =
	        let c = select World c in
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
server : forall a:SL => dualof GameChannel; a -> (World, a)
server s =
	match s with {
        World s ->
      		let (size, s) = receive s in
      		let (rowSize, s) = receive s in
      		let (world, s) = serverWorld[a] s size rowSize in
      		let world = splitWork size rowSize world in
      		(world, s)
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

-- SERVER FUNCTIONS --------------------------------------------------------------------
splitWork : Int -> Int -> World -> World
splitWork size rowSize world =
  	generate[Skip] world world rowSize

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
                    else b in                                       -- Live on
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
  fork (sink (client[Skip] c 99 10 (initWorld 99)));
  let (world,s) = server[Skip] s in
  let _ = printWorld[Skip] world 10 in
  let _ = printUnitLn (); printUnitLn () in
  ()

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
