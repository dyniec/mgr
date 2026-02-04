module mgr.Machine where

open import Data.Nat
open import Data.List
open import Data.Product using (_×_;_,′_)
--open import mgr.Types

data Erased : Set where
  var : ℕ → Erased
  lam : Erased → Erased
  app : Erased → Erased → Erased
  new : Erased → Erased
  shift₀ : Erased → Erased → Erased
  reset₀ : Erased → Erased → Erased → Erased
  
  

Env : Set
data Val : Set
data Context : Set
MetaContext : Set

Counter = ℕ --label allocator
Env = (List Val) × Counter
data Val where
  thunk : Erased → Env → Val
  kont :  Context → Val
  label : ℕ → Val
data Context where
  end : Context
  app₁ : Erased → Env → Context → Context
  app₂ : Val → Context
  reset₀-label : Erased → Erased → Context
  shift₀-label : Erased → Context
MetaContext = List Context

data State : Set where
  eval : Erased → Env → MetaContext → State
  cont : Context → Val → State
  
init : Erased → State
init e = eval e ([] ,′ zero) (end ∷ [])
