module HW1 where

import Data.List 
import Char


----Exercise 1----------------------------------------------------
type Bag a = [(a,Int)] 

--(a)--
ins :: (Eq a) => a -> Bag a -> Bag a
ins x [] = [(x,1)]
ins x (x':xs)      
    | x == fst x' =  (x, snd x'+1) : xs  
    | otherwise = x' : ins x xs 


del :: Eq a => a -> Bag a -> Bag a
del x [] = error "x is not in the bag"
del x (x':xs)
    | x == fst x' = if snd x'> 1 then (x, snd x'-1) : xs else delete x' (x':xs)
    | otherwise = x' : del x xs


--(b)--
bag :: Eq a => [a] -> Bag a
bag [] = []
bag (x:xs) = ins x (bag xs)  


--(c)--
subbag :: Eq a => Bag a -> Bag a -> Bool
subbag [] _ = True
subbag _ [] = False
subbag (x1:y1) (x2:y2)
    | fst x1 == fst x2 = if snd x1 > snd x2 then False else subbag y1 y2
    | otherwise = subbag [x1] y2 && subbag y1 (x2:y2)


--(d)--
isbag :: Eq a => Bag a -> Bag a -> Bag a
isbag [] _ = []
isbag _ [] = []
isbag ((x,xs):y) ys = (isbag' (x,xs) ys) ++ (isbag y ys)

isbag' :: Eq a => (a, Int) -> Bag a -> Bag a
isbag' _ [] = []
isbag' (x1,y1) ((x2,y2):xs)
    | x1 == x2 = [(x1, min y1 y2)]
    | otherwise = isbag' (x1,y1) xs


--(e)--
size :: Bag a -> Int
size [] = 0
size (x:xs) = snd x + size xs



----Exercise 2-------------------------------------------------------
hist :: Bag Int -> String
hist x = output (reverse(rows x)) ++ " " ++ (map intToDigit [1..m]) ++ "\n"
    where (m,_) = maximum x

-- generate the rows of the histogram from the multiset
rows :: Bag Int -> [Bag Int]
rows [] = []
rows x = y : rows (tier x y)
    where y = one x

-- bar of intersection
tier :: Eq a => Bag a -> Bag a -> Bag a
tier [] [] = []
tier ((x1,c1):l) ((x2,1):s)
    | x1 /= x2 = error "not match."
    | c1 == 1  = tier l s
    | c1 > 1   = (x1,c1-1) : (tier l s)
tier _ _ = error " not match!"

-- take each one element from the tuple in the bag
one :: Eq a => Bag a -> Bag a
one [] = []
one ((x,xs):s) = (x,1) : (one s)

output :: [Bag Int] -> String
output [] = []
output t = intToDigit l : output' (head t) ++ "\n" ++ output (tail t)
    where l = length t

-- output one line of the histogram
output' :: Bag Int -> String
output' [] = []
output' ((n,c):h) = replace n 'x' $ (output' h) ++ (replicate (m-1) ' ')
    where (m,_) = maximum ((n,c):h)
          l = length (output' h)

-- replace id's element with n in the l list
replace :: Int -> a -> [a] -> [a]
replace id n l = take (id-1) l ++ [n] ++ (drop id l)

ph :: Bag Int -> IO ()
ph = putStr . hist


xs,ys :: [Int]
xs = reverse [5,7,2,3,7,8,3,7]
ys = reverse [5,5,7,8,3,8,7]

lx = bag xs
ly = bag ys
lz = del 8 ly
la = del 5 lz
lb = del 3 la



----- Exercise 3----------------------------------------------------------
type Number = Int

type Point = (Number,Number)
type Length = Number

data Shape = Pt Point
           | Circle Point Length
           | Rect Point Length Length
           deriving Show

type Figure = [Shape]

type BBox = (Point,Point)


--(a)--
width :: Shape -> Length
width (Pt _) = 0
width (Circle _ r) = 2*r
width (Rect _ w _)  = w

bbox :: Shape -> BBox
bbox (Pt p) = (p,p)
bbox (Circle (x, y) r) = ((x-r, y-r), (x+r, y+r))
bbox (Rect (x, y) w h) = ((x, y), (x+w, y+h))

minX :: Shape -> Number
minX (Pt (x,y)) = x
minX (Circle (x,y) r) = x-r
minX (Rect (x,y) _ _) = x


--(b)--
move :: Shape -> Point -> Shape
move (Pt p) mp =  Pt (addPnt p mp)
move (Circle p r) mp =  Circle (addPnt p mp) r  
move (Rect p w h) mp =  Rect (addPnt p mp) w h 

addPnt :: Point -> Point -> Point
addPnt (x,y) (mx,my) = (x+mx, y+my)


--(c)--
alignLeft :: Figure -> Figure
alignLeft [] = []
alignLeft (s:fs)= moveToX minx s : (alignRestLeft minx fs)
          where minx = minimum (map minX (s:fs))

alignRestLeft :: Int -> Figure -> Figure
alignRestLeft  x [] = []
alignRestLeft  x (s:fs) = moveToX x s : (alignRestLeft x fs) 

moveToX :: Number -> Shape -> Shape
moveToX n (Pt (x,y)) = Pt (n, y)
moveToX n (Circle (x,y) r) = Circle (n+r, y) r
moveToX n (Rect (x,y) w h) = Rect (n, y) w h


--(d)--
inside :: Shape -> Shape -> Bool
inside s1 (Pt (x,y)) = compBBox (bbox s1) (bbox (Pt (x,y)) )
inside (Pt (x1,y1)) (Rect (x2,y2) w h) = compBBox (bbox (Pt (x1,y1))) (bbox (Rect (x2,y2) w h))
inside (Rect (x1,y1) w1 h1) (Rect (x2,y2) w2 h2) = compBBox (bbox (Rect (x1,y1) w1 h1)) (bbox (Rect (x2,y2) w2 h2))
inside (Circle (x1,y1) r) (Rect (x2,y2) w h) 
         | ((x1-r)>= x2) && ((x1+r)<= (x2+w)) && ((y1-r)>= y2) && ((y1+r)<=(y2+h)) = True
         | otherwise = False
inside (Pt (x,y)) (Circle (cx,cy) r) = ptInCircle (Pt (x,y)) (Circle (cx,cy) r)
inside (Rect (x,y) w h) (Circle (cx,cy) r)
         | (ptInCircle (Pt (x,y)) s2) && (ptInCircle (Pt (x,y+h)) s2) && (ptInCircle (Pt (x+w,y)) s2) && (ptInCircle (Pt (x+w,y+h)) s2) = True
         | otherwise = False
          where s2 = (Circle (cx,cy) r)
inside (Circle (x1,y1) r1) (Circle (x2,y2) r2) 
         | (ptDist (Pt (x1,y1)) (Pt (x2,y2))) + (fromIntegral r1) <= (fromIntegral r2) = True
         | otherwise = False


compBBox :: BBox -> BBox -> Bool
compBBox ((a1,b1), (a2,b2)) ( (c1,d1), (c2,d2 ))  
           | (a1 >= c1) && (b1 >= d1) && (a2 <= c2) && (b2 <= d2) = True 
           | otherwise = False

ptInCircle :: Shape -> Shape -> Bool
ptInCircle (Pt (x,y)) (Circle (cx,cy) r)  
           | ptDist (Pt (x,y)) (Pt (cx,cy)) <= (fromIntegral r) = True
           | otherwise = False

ptDist :: Shape -> Shape -> Double 
ptDist (Pt (x1,y1)) (Pt (x2,y2)) = sqrt (fromIntegral ((x1-x2)^2 + (y1-y2)^2) )


--Test--
f = [ Pt (4,4), Circle (5,5) 3, Rect (3,3) 7 2 ]

wf = map width f
bf = map bbox f
mf = map minX f

m1 = move (Pt (4,4)) (1,2) 
m2 = move (Circle (5,5) 3) (1,2) 
m3 = move (Rect (3,3) 7 2) (1,2) 

af = alignLeft f

in1 =  inside (Pt (4,4)) (Pt (2,4))
in2 =  inside (Pt (4,4)) (Pt (4,4))
in3 =  inside (Pt (1,4)) (Circle (5,5) 3)
in4 =  inside (Pt (4,4)) (Circle (5,5) 3)
in5 =  inside (Pt (2,4)) (Rect (3,3) 7 2)
in6 =  inside (Pt (4,4)) (Rect (3,3) 7 2)
in7 =  inside (Circle (5,5) 3) (Rect (3,3) 7 2)
in8 =  inside (Circle (5,5) 1) (Rect (3,3) 7 7)
in9 =  inside (Rect (3,3) 7 2) (Circle (5,5) 3)
in10 =  inside (Rect (3,3) 1 2) (Circle (5,5) 3) 
in11 =  inside (Circle (4,4) 1 ) (Circle (5,5) 3) 
in12 =  inside (Circle (4,4) 5 ) (Circle (5,5) 3) 
