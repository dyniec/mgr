```
module Machine where

open import Data.Nat
open import Data.List
open import Data.Product using (_×_;_,′_)
open import Runtime

data Erased : Set where
  var : ℕ → Erased
  lam : Erased → Erased
  app : Erased → Erased → Erased
  new : Erased → Erased
  shift₀ : Erased → Erased → Erased
  reset₀ : Erased → Erased → Erased → Erased
  label : ℕ → Erased

erased : Runtime.RuntimeExpr.RExpr → Erased
erased (RuntimeExpr.var x) = var x
erased (RuntimeExpr.lam x) = lam (erased x)
erased (RuntimeExpr.app x x₁) = app (erased x) (erased x₁)
erased (RuntimeExpr.tlam x x₁) = lam (erased x₁)
erased (RuntimeExpr.tapp x x₁) = app (erased x) (lam (var 0))
erased (RuntimeExpr.new x) = new (erased x)
erased (RuntimeExpr.new' x x₁) = erased x₁
erased (RuntimeExpr.shift₀ x x₁) = shift₀ (erased x) (erased x₁)
erased (RuntimeExpr.reset₀ x x₁ x₂) = reset₀ (erased x) (erased x₁) (erased x₂)
erased (RuntimeExpr.label x) = label x
  

Env : Set
data Val : Set
data Context : Set
MetaContext : Set

Counter = ℕ --label allocator
Env = List Val
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
  eval : Erased → Env → MetaContext → Counter → State
  cont : Context → Val → Counter → State
  
init : Erased → State
init e = eval e []  (end ∷ []) zero
```
