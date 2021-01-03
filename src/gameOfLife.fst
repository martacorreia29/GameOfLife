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

server : forall a:SL => dualof GameChannel; a -> (World, a)
server s =
	match s with {
        World s ->
      		let (size, s) = receive s in
      		let (rowSize, s) = receive s in
      		let (world, s) = serverWorld[a] s size rowSize in
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

main : World
main =
  let (c, s) = new GameChannel in
  fork (sink (client[Skip] c 10 10 world));
  let (world, s) = server[Skip] s in
  world

sink : Skip -> ()
sink _ = ()
