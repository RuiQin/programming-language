module HW3-Stack where

-- a language for manipulating stacks of natural numbers

open import 5-Basics


-- syntax of stack programs
--
data Op : Set where
  push : ℕ → Op
  pop add swap dup : Op
  loop : ℕ → List Op → Op

Prog : Set
Prog = List Op


-- example programs
--
a35 : Prog
a35 = push 3 ∷ push 5 ∷ add ∷ []
 

-- machine state for small-step semantics
--
Stack = List ℕ

data State : Set where
  _<_> : Prog → Stack → State

infix 3 _<_>


-- example state
--
state1 : State
state1 = add ∷ dup  ∷ [] < 3 ∷ 4 ∷ [] >


-- two reduction relations: final step & intermediate transitions
-- plus a transitive closure reduction relation
---- 

infix 3 _↦_
infix 3 _↦*_ 

-- 1(a)(e)
--
data _↦_ : State → State → Set where
   Push_ :  ∀ {p n xs}     →  push n ∷ p < xs > ↦ p < n ∷ xs >
   Pop   :  ∀ {p n xs}     →  pop ∷  p < n ∷ xs >  ↦ p < xs >
   Add   :  ∀ {p m n xs}   →  add ∷  p < m ∷ n ∷ xs >  ↦ p < m + n ∷ xs >
   Swap  :  ∀ {p m n xs}   →  swap ∷  p < m ∷ n ∷ xs > ↦ p < n ∷  m ∷ xs >
   Dup   :  ∀ {p n xs}     →  dup ∷  p < n ∷ xs > ↦ p < n ∷ n ∷ xs >
   Loop_ :  ∀ {p n ps xs}  →  loop (suc n) (ps ∷ []) ∷ p  < xs >  ↦ ps ∷ loop n (ps ∷ []) ∷ p < xs >


infixr 5 _then_

data _↦*_ : State → State → Set where
   refl   : ∀ {s} → s ↦* s
   _then_ : ∀ {s₁ s₂ s₃} → s₁ ↦ s₂ → s₂ ↦* s₃ → s₁ ↦* s₃


-- properties of the language
--

-- 1(b)(c)(d)
--
lemma-1b : state1 ↦* [] < 7 ∷ 7 ∷ [] >
--lemma-1b : add ∷ dup ∷ [] < 3 ∷ 4 ∷ [] > ↦* [] < 7 ∷ 7 ∷ [] >
lemma-1b = Add then Dup then refl

lemma-1c : ∀ {xs}  → a35 < xs > ↦* [] < 8 ∷ xs > 
--lemma-1c : ∀ {xs}  → push 3 ∷ push 5 ∷ add ∷ [] < xs > ↦* [] < 8 ∷ xs > 
lemma-1c = Push_ then Push_ then Add then refl

lemma-1d : ∀{xs n p} → push n ∷ pop ∷ p < xs > ↦* p < xs >
lemma-1d = Push_ then Pop then refl

-- 1(f)
--
mult : ℕ → ℕ → Prog
mult zero _  = push zero ∷ [] 
mult _ zero  = push zero ∷ [] 
mult m (suc n) = push m ∷ dup ∷ loop n (add ∷ push m ∷ []) ∷ pop ∷ []

