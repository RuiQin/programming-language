module HW3-Minicel where

-- Small spreadsheet language

open import 5-Basics hiding (plus)



-- Formulas, or Expressions
--
Addr = ℕ

data Exp : Set where
  num  : ℕ → Exp
  plus : Exp → Exp → Exp
  ref  : Addr → Exp


-- Spreadsheet is simply a list of formulas. 
-- Cell addresses are given by list positions (first cell has address 0).
--
Sheet = List Exp
Numbers = List ℕ


-- Big-step operational semantics
--
-- Three relations:
--  s ! a ↣ e   finds expression e in a spreadsheet s at address a
--  s ! e ⇓ n    evaluates the expression e in the context of s to a number n
--  s ! s' ⇓* ns  evaluates a list of cells s' in the context of a spreadsheet
--                to a list of numbers ns

infix 3 _!_↣_
infix 3 _!_⇓_ 
infix 3 _!_⇓*_

-- 2(a)
--
data _!_↣_ : Sheet → Addr → Exp → Set where
   ↣match  : ∀ {x s} → (x ∷ s)! 0 ↣ x
   ↣search : ∀ {x x' s n} → s ! n ↣ x → (x' ∷ s) ! suc n ↣ x

-- 2(b)
--
data _!_⇓_ : Sheet → Exp → ℕ → Set where
   ⇓num  : ∀ {n s} → s ! num n ⇓ n
   ⇓plus : ∀ {s e e' n m} → s ! e ⇓ n → s ! e' ⇓ m → s ! plus e e' ⇓ n + m
   ⇓ref  : ∀ {s e n m} → s ! n ↣ e → s ! e ⇓ m → s ! ref n ⇓ m

-- 2(c)
--
data _!_⇓*_ : Sheet → Sheet → Numbers → Set where 
   refl   : ∀ {s} → s ! [] ⇓* []
   _then_ : ∀ {s s' ss n ns} → s ! s' ⇓ n → s ! ss ⇓* ns → s ! s' ∷ ss ⇓* n ∷ ns  
  

-- Auxiliary definitions: References to specific cells
--

-- 2(d)
--
↣0 : ∀ {e s} → e ∷ s ! 0 ↣ e
↣0 = ↣match

↣1 : ∀ {s e e'} → e' ∷ e ∷ s ! 1 ↣ e
↣1 = ↣search ↣match

↣2 : ∀ {s e e' e''} → e'' ∷ e' ∷ e ∷ s ! 2 ↣ e
↣2 = ↣search (↣search ↣match)


-- Example spreadhseets and their results
--

-- 2(e)
--
s : Sheet
s = num 3 ∷ plus (ref 0) (num 2) ∷ []
--
ns : Numbers
ns = 3 ∷ 5 ∷ []
--
eval : s ! s ⇓* ns
eval = ⇓num then (⇓plus (⇓ref ↣0 ⇓num) ⇓num then refl)

-- 2(f)
--
s' : Sheet
s' = num 3 ∷ plus (ref 0) (num 1) ∷ plus (ref 0) (ref 1) ∷ []
--
ns' : Numbers
ns' = 3 ∷ 4 ∷ 7 ∷ []
--
eval' : s' ! s' ⇓* ns'
eval' = ⇓num then ((⇓plus (⇓ref ↣0 ⇓num) ⇓num) then ((⇓plus (⇓ref ↣0 ⇓num) (⇓ref ↣1 (⇓plus (⇓ref ↣0 ⇓num) ⇓num))) then refl))

-- 2(g)
--
l : Sheet
l = ref 0 ∷ []

c : Sheet
c = ref 1 ∷ ref 0 ∷ []

{-
All experisions in l and c are references to other addresses. 
In l, the expression ref 0 references to itself, which will lead to infinite cell references.
In c, the expression in address 0 refers to address 1 and the expression in address 0 refers to address 0. 
This forms a cycle and will also lead to infinite cell references.
So, neither of them can be proved by the data type we defined above by Agda.
-}

