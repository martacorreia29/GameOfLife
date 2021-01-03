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

server : forall a:SL => dualof GameChannel; a -> a
server s =
	match s with {
        World s ->
      		let (size, s) = receive s in
      		let (rowSize, s) = receive s in
      		serverWorld[a] s size rowSize
   }

serverWorld : forall a:SL => dualof WorldChannel; a -> Int -> Int -> a
serverWorld s size rowSize =
	match s	with {
      Nil s ->
      	s,
      Tile s ->
      	serverTile[a] s size rowSize
    }

serverTile : forall a:SL => dualof TileChannel; a -> Int -> Int -> a
serverTile s size rowSize =
		let (index, s) = receive (select Index s) in
		let (state, s) = receive (select State s) in
		let s = serverWorld[dualof TileChannel; a] (select Next s) size rowSize in
		(select Exit s)--(Tile index state next, s)


main : ()
main =
  let (c, s) = new GameChannel in
  fork (sink (client[Skip] c 10 10 world));
  sink (server[Skip] s)

sink : Skip -> ()
sink _ = ()
