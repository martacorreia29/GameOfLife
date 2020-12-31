--Data Structores
data WorldList = Nil | Tile Int Bool WorldList

aList : WorldList
aList = Tile 1 True (Tile 2 True (Tile 3 True (Cons True Nil)))

initWorld : Int -> WorldList
initWorld n = if n == 0
              then Nil
              else Tile n (semiRandomBool n) (initWorld (n-1))


-- utils funtions

-- TODO find a better way to randamize bools
semiRandomBool : Int -> Bool
semiRandomBool n = (mod n 2) == 0

-- (Array index, array size) -> x pos
getX : Int -> Int -> Int
getX i n = mod i n

-- (Array index, array size) -> y pos
getY : Int -> Int -> Int
getY i n = i / n

getCoors : Int -> Int -> (Int, Int)
getCoors i n = let x = getX i n in
		       let y = getY i n in
		       (x,y)


-- Not finished
printWorld : forall a:SL => WorldList -> ()
printWorld world =
 case world of {
    Nil ->
      printCharLn 'E',
    Tile x b l ->
      printIntLn x;
      printWorld[a] l
    }




-- The code below needs to be adpted
type WorldChan : SL = +{Nil: Skip,
                        Tile: TileChan}


type TileChan : SL = &{
  State: !Bool;TileChan,
  List: WorldChan; TileChan,
  Exit : skips
}

type XploreConsChan : SL = &{
   Value : !Point;XploreConsChan ,
   List : XploreListChan ; XploreConsChan ,
   Exit : Skip
 }

-- The client.
exploreList : forall a:SL => XploreListChan;a -> WorldList -> a
exploreList c list =
  case list of {
    Nil ->
      select Nil c,
    Cons x l ->
      exploreCons[a] (select Cons c) x l
    }

exploreCons : forall a:SL => XploreConsChan;a -> Int -> WorldList -> a
exploreCons c x l =
  match c with {
    Value c ->
      exploreCons[a] (send x c) x l,
    List c ->
      let c = exploreList[XploreConsChan;a] c l in
      exploreCons[a] c x l,
    Exit c ->
      c
  }

-- The server
server : forall a:SL => dualof XploreListChan;a -> Int -> (a, Int)
server c1 n =
  match c1 with {
    Nil c1 ->
      (c1, n),
    Cons c1 ->
      serverCons[a] c1 n
  }

serverCons : forall a:SL => dualof XploreConsChan;a -> Int -> (a, Int)
serverCons c n =
  let (m, c) = receive (select Value c) in
  if m == 0
  then (select Exit c, 0)
  else
    let c = select List c in
	let _ = printIntLn m in
    let (c, m) = server[dualof XploreConsChan;a] c m in
    (select Exit c, m)

main : ()
main =
  let (writer, reader) = new XploreListChan in
  let _ = fork (sink (exploreList[Skip] writer aList)) in
  let (_, n) = server[Skip] reader 0 in
  let n = () in n

-- Auxiliary function because of fork : () -> ()
sink : Skip -> ()
sink _ = ()
