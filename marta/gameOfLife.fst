type Point = (Int, Int)
data Cell = Alive | Dead
type Grid = Point -> Cell
data World = Nil | W Point World

type GameOfLifeChannel : SL =
	+{ Play : !World, !Int, ?World; GameOfLife
  	, Quit : Skip
  	}

client : GameOfLifeChannel -> World
client c =
	let (w,r) = receive $ send  W ((0, 0)) (W ((0, 1)) Nil) $ send 2 $ select Play c in
	w

server : dualof GameOfLifeChannel -> ()
server c =
	match c with {
      Play c ->
      	let (w, c) = receive c in
      	let (n, c) = receive c in
      	let _ = send(w) c in
      	()
      }

main : ()
main =
  let (c, s) = new GameOfLifeChannel in
  fork (server s);
  client c
