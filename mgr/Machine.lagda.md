\iffalse

```
module Machine where

open import Data.Nat
open import Data.List hiding (lookup) 
open import Data.Product using (_×_;_,′_;proj₁;proj₂)
open import Runtime
open import Data.Maybe using (Maybe)
```
\fi
Here we define type erased expressions. And translation from previous `RExpr` type.
Type abstraction is translated to normal abstraction, and type application is translated to application
of identity function (it won't be used regardless of value).
```
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
```
Here we present draft of machine, together with draft of evaluation function.
```
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
data Context  where
  end : Context
  app₁ : Erased → Env → Context → Context
  app₂ : Val → Context → Context
  reset₀-label : Erased → Erased → Context → Context
  shift₀-label : Erased → Context → Context
MetaContext = List (Context × Maybe ℕ)

data State : Set where
  eval : Erased → Env → MetaContext → Counter → State
  cont : Context → MetaContext → Val → Counter → State
  val : Val → State
  err : State
  
init : Erased → State
init e = eval e []  ( (end ,′ Maybe.nothing) ∷ []) zero
{-
lookup : ∀ {A} ℕ → List A → Maybe A
lookup n xs = head(drop n xs) 
move : State → State
move (eval (var x) ρ [] cnt) = err
move (eval (var x) ρ (x₁ ∷ mc) cnt) with lookup x ρ
... | Maybe.just v = cont (proj₁ x₁) mc (v) cnt
... | Maybe.nothing = err
move (eval (lam x) ρ [] cnt) = err
move (eval (lam x) ρ (x₁ ∷ mc) cnt) = cont (proj₁ x₁) mc (thunk x ρ) cnt
move (eval (app x x₁) ρ (c ∷ mc) cnt) = eval x ρ ( (app₁ x₁ ρ  (proj₁ c) ,′ Maybe.nothing) ∷ mc) cnt
move (eval (app x x₁) ρ [] cnt) = err
move (eval (new x) ρ mc cnt) = {!!}
move (eval (shift₀ x x₁) ρ mc cnt) = {!!}
move (eval (reset₀ x x₁ x₂) ρ mc cnt) = {!!}
move (eval (label x) ρ mc cnt) = {!!}
move (cont end mc v cnt) = cont end mc v cnt
move (cont (app₁ x x₁ c) mc v cnt) = eval x x₁ ((app₂ v c ,′ Maybe.nothing)∷ mc) cnt
move (cont (app₂ x c) mc v cnt) = {!!} 
move (cont (reset₀-label x x₁ c) mc v cnt) = {!!}
move (cont (shift₀-label x c) mc v cnt) = {!!}
move err = err
move (val v) = (val v)

-}
```
