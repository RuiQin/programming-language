import System.IO.Unsafe
import System.Random
import Data.List

type Strategy s = s -> s 
type Trace s = [s]
type GState s = s
type Player s = s
type Result s = s 
type GameOver s = s -> Bool
type Score = Int

data Game s = Extensive s [Strategy s] (GameOver s) | Normal [s] [Strategy s]

trace :: Game s -> Trace s
trace (Extensive s (f:fs) p)   | p s = [s]
                               | otherwise = s:trace (Extensive (f s) (fs++[f]) p)
trace (Normal [] [])           = []
trace (Normal (s1:s1s) (f:fs)) = (f s1) : trace (Normal s1s fs)  

----run multiply games 
runGames :: (Game s -> Trace s) -> [Game s] -> [Trace s]
runGames _ []         = [] 
runGames trace (g:gs) = trace g : runGames trace gs

----find who is the winner according to the game definition
winners :: Trace s -> Result s
winners = undefined

----compare the two traces
isLongerThan :: Trace s -> Trace s -> Bool
isLongerThan t1 t2  = length t1 > length t2 

------ Nim --------------

--- Strategy fot Nim: leave your opponent with an exact multiple of 3
mod3 n | mod n 3 == 1  = n-1
       | mod n 3 == 2  = n-2
       | otherwise     = n-1

----return last state
lastState :: Trace s -> GState s
lastState t = last t

----find who plays last
playsLast :: Trace s -> [Player p] -> Player p
playsLast t ps | (mod (lT-1) lP) == 0 = last ps 
	       | otherwise            = ps !! ((mod (lT-1) lP)-1)
		where lT = length t
		      lP = length ps

e1 :: Game Int
e1 = Extensive 21 [pred,mod3] (<=0)

e2 :: Game Int
e2 = Extensive 7 [pred,mod3] (<=0)

players = ["Tom","Jerry"]

p = playsLast (trace e1) players

nims = runGames trace [e1,e2]

------- Maze --------------
type Maze = [[Int]]
type Pos = (Int,Int) 
data SuccOrFail = Fail | Succ deriving (Eq,Show)
type MazeRes = (SuccOrFail,Int)
type MState = (Pos,Score)

maze :: Maze
maze = [[0,1,2,2],[1,-10,2,1],[0,2,1,10]]
{-
  mouse 1    2    2
    1  trap  2    1
    0   2    1   exit
-}

------------ Strategies --------
rightAndDown :: MState -> MState
rightAndDown state
	| y < ((length $ head maze)-1) = ((x,y+1),score + element (x,y+1))
	| x < ((length maze)-1)        = ((x+1,y),score + element (x+1,y))
	where x = fst $ fst state
	      y = snd $ fst state
	      score = snd state

randRAndD :: MState -> MState
randRAndD state | x < ((length maze)-1) && v == 1        = ((x+1,y),score + element (x+1,y))
		| x >= ((length maze)-1) && v == 1       = ((x,y+1),score + element (x,y+1))
                | y < ((length $ head maze)-1) && v == 2 = ((x,y+1),score + element (x,y+1))
		| y >=((length $ head maze)-1) && v == 2 = ((x+1,y),score + element (x+1,y))
		  where x = fst $ fst state
			y = snd $ fst state
			score = snd state
			v = randInRange 1 2  
---------------------------------
element :: Pos -> Int
element (x,y) = maze !! x !! y

isOver :: MState -> Bool
isOver s = p == (2,3) || p == (1,1)  -- find the exit or got by a trap
	where p = fst s

mazeResult :: Trace MState -> Result MazeRes
mazeResult g | (element $ fst lastS) == -10 = (Fail,score)
	     | (element $ fst lastS) == 10  = (Succ,score)
		where lastS = last g
		      score = snd lastS

mazeResults :: Game MState -> Int -> [Result MazeRes]
mazeResults _ 0 = []
mazeResults s n = (mazeResult $ trace s) : (mazeResults s (n-1))

everyFirst :: [Result MazeRes] -> [SuccOrFail]
everyFirst [] = []
everyFirst (x:xs) = (fst x) : (everyFirst xs)

everySec :: [Result MazeRes] -> [Int]
everySec [] = []
everySec (x:xs) = (snd x) : (everySec xs)

sum' :: [Int] -> [Int] -> Int
sum' [] _ = 0
sum' (x:xs) l = (l !! x) + (sum' xs l)

sumUp :: SuccOrFail -> [SuccOrFail] -> [Int] -> Int
sumUp t ten score = sum' (elemIndices t ten) score

mazeSimulate :: Game MState -> Int -> IO ()
mazeSimulate state n = do 
  let game = mazeResults state n
  let ten = everyFirst game 
  let score = everySec game
  let sumUp t = sum' (elemIndices t ten) score
  let count t = length $ filter (==t) ten

  let succCount  = count Succ
  let failCount = count Fail

  let succAvg = fromIntegral (sumUp Succ) / (fromIntegral succCount)
  let failAvg = fromIntegral (sumUp Fail) / (fromIntegral failCount)

  putStrLn $ "Successes: "   ++ show succCount ++ "   Average score: " ++ show succAvg
  putStrLn $ "Fails: "       ++ show failCount ++ "   Average score: " ++ show failAvg

e3 :: Game MState
e3 = Extensive ((0,0),0) [rightAndDown] isOver

e4 :: Game MState
e4 = Extensive ((0,0),0) [randRAndD] isOver

mazeSim :: IO ()
mazeSim = mazeSimulate e4 100

------Rock Paper Scissors-------
data RPS = Rock | Paper | Scissors deriving (Enum, Eq, Show)

data RPSres = Win | Lose | Tie
            deriving (Show, Eq)

------------- Strategies-------------
rock :: RPS -> RPS
rock _ = Rock

paper :: RPS -> RPS
paper _ = Paper

scissors :: RPS -> RPS
scissors _ = Scissors

randRPS :: RPS -> RPS
randRPS  s  | v == 1 = Rock
            | v == 2 = Paper
            | otherwise = Scissors
	    where v = randInRange 1 3   

---------------------------------------
randInRange :: Int -> Int -> Int
randInRange a b = unsafePerformIO (getStdRandom (randomR (a, b))) 

eval :: RPS -> RPS -> Result RPSres
eval Rock Scissors  = Win
eval Rock Paper     = Lose
eval Scissors Rock  = Lose
eval Scissors Paper = Win
eval Paper Rock     = Win
eval Paper Scissors = Lose
eval _ _            = Tie

rpsResult :: Trace RPS -> Result RPSres
rpsResult g = eval (head g) (last g)

rpsResults :: Game RPS -> Int -> [Result RPSres]
rpsResults _ 0 = []
rpsResults rps n = (rpsResult $ trace rps) : (rpsResults rps (n-1))

rpsSimulate :: Game RPS -> Int -> IO ()
rpsSimulate rps n = do 
  let ten = rpsResults rps n
  let count t = length $ filter (==t) ten
  let winCount  = count Win
  let loseCount = count Lose
  let tieCount  = count Tie
  putStrLn $ "Wins: "   ++ show winCount
  putStrLn $ "Losses: " ++ show loseCount
  putStrLn $ "Ties: "   ++ show tieCount 

e5 :: Game RPS
e5 = Normal [Rock,Rock] [rock,randRPS]

e6 :: Game RPS
e6 = Normal [Rock,Rock] [randRPS,paper]

t = trace e5    -- [Rock,Paper]
r = rpsResult t    -- Lose

rpss = runGames trace [e5,e6]   -- [[Rock,Scissors],[Paper,Scissors]]

rpsSim :: IO ()
rpsSim = rpsSimulate e5 100

