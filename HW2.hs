module HW2 where

----Ex1--------------------------------------------------------------------
----(a)-------------
type NonTerm = String
type Term = String

type Gram = [Def]
data Def = Defs NonTerm [[Rhs]]
data Rhs = NT NonTerm
         | T Term

----(b)-------------
type Name = String
type Constr = String

data D = Data Name Cs
data Cs =  Concat  Constr [Type]
        | Seq Constr [Type] Cs
data Type = N Name
          | List Type


----Ex2---------------------------------------------------------------------
----(a)-------------
type A = (Int,Int)
type S = [C]

-- Haskell data definitions for R, E, C that correspond to r, e, and c, respectively
data R = Span A A | Elist [E]
         deriving Show

data E = I Int | Plus E E | Sum R | Ref A
         deriving Show

type C = (A,E)


------(b)--------------
spanRefs :: A-> A-> [A]
spanRefs (x1,y1) (x2,y2) 
    | x1 == x2 = spanLine x1 y1 y2 
    | otherwise = spanLine (min x1 x2) y1 y2 ++ spanRefs ((min x1 x2)+1, (min y1 y2))((max x1 x2), (max y1 y2))     
---- auxiliary function: span one line 
spanLine :: Int -> Int -> Int -> [(Int,Int)]
spanLine x y1 y2
    | y1 == y2  = [(x,y1)]
    | otherwise = [(x,min y1 y2)] ++ spanLine x ((min y1 y2)+1) (max y1 y2)


----(c)--------------
refs :: E -> [A]
refs (I _) = []
refs (Plus e e') = refs e ++ refs e'
refs (Sum (Span a a')) = spanRefs a a'
refs (Sum (Elist es)) = concat[refs e | e <- es]
refs (Ref a) = [a] 


----(d)--------------
semE :: E -> S -> Int
semE (I i) s = i
semE (Plus e e') s = (semE e s) + (semE e' s)
semE (Sum (Span a a')) s = sum ( semE' es s)
                 where es = lookupList (spanRefs a a') s
semE (Sum (Elist es)) s = sum (semE' es s)
semE (Ref a) s = semE (lookUp a s) s

-- evaluation of a list of expressions --
semE' :: [E] -> S -> [Int]
semE' [] s = []
semE' (e:es) s = semE e s : (semE' es s)

-- retrieve expression from one address --
lookUp :: A -> S -> E
lookUp a ((a1, e): ss)
       | a1 == a  = e
       | otherwise = lookUp a ss

-- retrieve expression from a list of addresses --
lookupList :: [A] -> S -> [E]
lookupList [] s = []
lookupList (a:as) s = lookUp a s : lookupList as s


semS :: S -> S
semS s  = findsemS ds (semE' (lookupList ds s) s)  
         where ds = domain s

-- find domain of s -- 
domain :: S -> [A]
domain s = map fst s

findsemS :: [A] -> [Int] -> S
findsemS [] [] = []
findsemS (a:as) (i:is) = (a, I i) : (findsemS as is)



------for test------
r1 = spanRefs (2,2) (3,4)
r2 = spanRefs (3,4) (2,2)

s::S
s = [((1,1),I 3), ((2,1),I 5),
    ((3,1),Plus (Ref(1,1)) (Ref(2,1))),
    ((1,2),Plus (Ref(1,1))(I 1)),
    ((2,2),Sum (Elist [Ref (2,1),Ref(1,2),I 100])),
    ((3,2),Sum (Span (1,1) (2,2)))]

sems = semS s

b = Sum (Elist [Ref (2,1),Ref(1,2),I 100])
rb = refs b

semb = semE b s



