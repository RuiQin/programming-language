module HW4-Minicel where

open import 5-Basics hiding (plus; Bool)

max : ℕ → ℕ → ℕ
max zero    n       = n
max (suc m) zero    = suc m
max (suc m) (suc n) = suc (max m n)


---------------------------------- Ex. 1 -----------------------------------------

-- Small spreadsheet language

-- Formulas, or Expressions
--
Addr = ℕ

data Exp : Set where
  num  : ℕ → Exp
  plus : Exp → Exp → Exp
  _>_  : Exp → Exp → Exp
  not  : Exp → Exp
  ref  : Addr → Exp


-- A spreadsheet is a list of formulas. 
-- Cell addresses are given by list positions (first cell has address 0).
--
Sheet = List Exp

-- Cell lookup
--
infix 3 _!_↣_

data _!_↣_ : Sheet → Addr → Exp → Set where
  ↣Zero : ∀ {e s} → 
            e ∷ s ! 0 ↣ e

  ↣Suc : ∀ {s a e e'} → 
                 s ! a ↣ e     → 
            -------------------  
            e' ∷ s ! suc a ↣ e


-- Type language
--
data Type : Set where
  Int Bool : Type

infix 6 _⊢_：_

-- Type system
--
-- Note the unicode for ： is FF1A

-- 1(a)
--
data _⊢_：_ : Sheet → Exp → Type → Set where
  ⊢num  : ∀ {s i} → s ⊢ num i ： Int

  ⊢plus : ∀ {s e e'} →     s ⊢ e ： Int →     s ⊢ e' ： Int   →
                           ------------------------------------
                                 s ⊢ plus e e' ： Int

  ⊢>    : ∀ {s e e'} →     s ⊢ e ： Int →    s ⊢ e' ： Int    →
                           ------------------------------------
                                   s ⊢ e > e' ： Bool

  ⊢not  : ∀ {s e} →      s ⊢ e ： Bool →
                         -----------------
                         s ⊢ not e ： Bool

  ⊢ref  : ∀ {s e a T} →     s ! a ↣ e →     s ⊢ e ： T   →
                            --------------------------------
                                      s ⊢ ref a ： T  


-- 1(b)
{- The parameter s is needed in the ref operation to retrieve expression e 
from the spredsheet according to its address a.
-}


infix 3 _⊢_
-- 1(c)
--

data _⊢_ : Sheet → Sheet → Set where
  ⊢Done : ∀ {s} → s ⊢ []

  ⊢NUM  : ∀ {s i s'} →   s ⊢ num i ： Int  →      s ⊢ s'     →
                         --------------------------------------
                                   s ⊢ num i ∷ s'

  ⊢PLUS : ∀ {s e e' s'} →     s ⊢ plus e e' ： Int   →     s ⊢ s'   →
                              --------------------------------------
                                         s ⊢ plus e e' ∷ s'

  ⊢COMP : ∀ {s e e' s'} →    s ⊢ e > e' ： Bool  →      s ⊢ s'    →
                            ---------------------------------------
                                         s ⊢ e > e' ∷ s' 

  ⊢NOT  : ∀ {s e s'} →   s ⊢ not e ： Bool  →      s  ⊢ s'    →
                         ----------------------------------------
                                     s  ⊢ not e ∷ s'

  ⊢REF  : ∀ {s a T s'} →       s ⊢ ref a ： T  →      s ⊢ s'     →
                              ------------------------------------
                                        s  ⊢ ref a ∷ s'
 

data ⊢_ : Sheet → Set where
  ⊢Sheet : ∀ {s} → s ⊢ s → ⊢ s


-- 1(d)
--
s1 : Sheet
s1 = num 3 ∷ plus (ref 0) (num 2) ∷ []

t1 : ⊢ s1
t1 =  ⊢Sheet ( ⊢NUM  ⊢num  (⊢PLUS (⊢plus (⊢ref ↣Zero ⊢num) ⊢num)  ⊢Done) )



---------------------------------- Ex. 2 -----------------------------------------

infix 5 _<_ _^_

data Shape : Set where
  □ : Shape
  _^_  : Shape → Shape → Shape
  _<_  : Shape → Shape → Shape

infix 5 [_,_]

data BBox : Set where
  [_,_] : ℕ → ℕ → BBox

infix 4 _：B_
infix 4 _：R_


-- 2(a)
--
data _：B_ : Shape → BBox → Set where
  Bbox   :   □ ：B [ 1 , 1 ]

  Bnext  : ∀ { x1 x2 y1 y2 s1 s2 } →  
                            s1 ：B [ x1 , y1 ] →      s2 ：B [ x2 , y2 ]  →
                           ---------------------------------------------------
                                  s1 < s2 ：B [ x1 + x2 , ( max y1 y2 ) ]

  Babove : ∀ { x1 x2 y1 y2 s1 s2 } → 
                            s1 ：B [ x1 , y1 ] →       s2 ：B [ x2 , y2 ] →
                          ----------------------------------------------------
                                  s1 ^ s2 ：B [ (max x1 x2) , y1 + y2 ]


-- 2(b)
--
data _：R_ : Shape → BBox → Set where
  Rbox   : □ ：R [ 1 , 1 ]

  Rnext  : ∀ { x1 x2 y s1 s2 } → 
                         s1 ：R [ x1 , y ] →     s2 ：R [ x2 , y ]   → 
                       -----------------------------------------------
                                s1 < s2 ：R [ x1 + x2 , y ]

  Rabove : ∀ { x y1 y2 s1 s2 } →
                         s1 ：R [ x , y1 ] →     s2 ：R [ x , y2 ]   →
                       -----------------------------------------------
                                s1 ^ s2 ：R [ x , y1 + y2 ]


-- 2(c)
--
r21 : □ ^ □ ：R [ 1 , 2 ]
r21 = Rabove Rbox Rbox

r22 : (□ ^ □) < (□ ^ □) ：R [ 2 , 2 ]
r22 = Rnext r21 r21