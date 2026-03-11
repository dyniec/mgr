\iffalse
```
module Types where

open import Data.Nat
open import Data.List using (List;_∷_;map) renaming ([] to nil)
open import Relation.Binary.PropositionalEquality using (_≡_;refl;_≢_)
```
\fi

# Syntax
We start with presenting the syntax of the surface language. We use kinds to distinguish between types and effects.
```
data Kind : Set where
    T : Kind
    E : Kind 
```
Types  and Effects are defined mutally recursive.Type is either variable, arrow, forall or label.
We represent variables and type variables with de Bruijn indices.
Effect is list of types, it's used in arrow and forall constructors of type to keep effects of computation underneath and it will be used in typing judgement. Label contructor just stores type variable bound to effect represented by the label and then Type and Effect of delimited computation.
```
module Types where
    Id : Set
    Id = ℕ
    data Type : Set
    Effects : Set
    data Type  where
        ttv : Id → Type
        _-_>_ : Type → Effects → Type → Type
        forallt : Kind → Type → Effects →  Type
        L_at_/_ : Type → Type → Effects → Type
    Effects = List Type
open Types
```
Constructors of expressions such as `var`, `lam`, `app`, `tlam`, `tapp` behave as usual.
`var` is de Bruijn indexed variable, `lam` is lambda abstraction, `app` is function application, `tlam` is type abstraction, but it stores Kind of abstracted type and `tapp` is type application.
The rest of constructors are responsible for continuations and labels. Constructor `new` bind label that is used by shift₀ and reset₀ constructors to pair up. `shift₀` stores label and expression (parametrized by continuation) that replaces whole delimited computation. Last constructor of expressions is `reset₀` which has 3 fields, last one is label that is used to match up reset with shifts. First argument is delimited computation where `shift₀` can be used. So when `shift₀ k.e` is being evaluated it aborts enclosing corresponding reset, instead of it now `e` is being evaluated with `k` bound to continuation representing evaluation context between shift and it's reset.
Second field `x. en` is used when during evaluation of first expression no corresponding shift aborts, and just yields value `v` - then whole reset₀ evaluates to `en` where `x` is bound to `v`.


```
module Expr where
    data Expr : Set where
        var : ℕ → Expr
        lam : Expr → Expr
        app : Expr → Expr → Expr
        tlam : Kind → Expr → Expr
        tapp : Expr -> Type -> Expr
        new : Expr → Expr
        shift₀ : Expr → Expr → Expr
        reset₀ : Expr → Expr → Expr → Expr 
open Expr
```

\iffalse

```
module TypeSubst where
    Rename = ℕ → ℕ
    Subst = ℕ → Type
    ext : Rename → Rename
    ext ρ zero = zero
    ext ρ (suc x) = suc (ρ x)

    rename : Rename → (Type → Type)
    rename' : Rename → (Effects → Effects)
    rename ρ (ttv x) = ttv (ρ x)
    rename ρ (x - effs > x₁) = rename ρ x -  rename' ρ effs > rename ρ x₁
    rename ρ (forallt k x e) = forallt k (rename (ext ρ) x) (rename' ρ e)
    rename ρ (L x at x₁ / effs) =  L  rename ρ x at  rename ρ x₁ / rename' ρ effs
    rename' ρ nil = nil
    rename' ρ (x ∷ xs) = rename ρ x ∷ rename' ρ xs
    bump = rename suc
    bump' = rename' suc

    exts : Subst → Subst
    exts ρ zero = ttv zero
    exts ρ (suc x) = rename suc (ρ x)

    subst : Subst → ( Type → Type)
    subst' : Subst → ( Effects → Effects)
    subst ρ (ttv x) = ρ x
    subst ρ (t - x > t₁) =  subst ρ t - subst' ρ x > subst ρ t₁
    subst ρ (forallt k t e) = forallt k (subst (exts ρ) t) (subst' ρ e)
    subst ρ (L x at t / x₁) = L subst ρ x at subst ρ t / subst' ρ x₁
    subst' ρ nil = nil
    subst' ρ (x ∷ x₁) = subst ρ x ∷ subst' ρ x₁

    subst-zero : Type → Subst
    subst-zero t zero = t
    subst-zero t (suc x) = ttv x

    subst-in-expr : Subst → Expr → Expr
    subst-in-expr ρ (tlam k e) = tlam k (subst-in-expr (exts ρ) e)
    subst-in-expr ρ (new e) =  new (subst-in-expr (exts ρ) e)
    subst-in-expr ρ (tapp e t) = tapp (subst-in-expr ρ e) (subst ρ t)
    subst-in-expr ρ (var x) = var x
    subst-in-expr ρ (lam e) =  lam (subst-in-expr ρ e)
    subst-in-expr ρ (app e e₁) =  app (subst-in-expr ρ e) (subst-in-expr ρ e₁)
    subst-in-expr ρ (shift₀ e e₁) =  shift₀ (subst-in-expr ρ e) (subst-in-expr ρ e₁)
    subst-in-expr ρ (reset₀ e e₁ e₂) = reset₀ (subst-in-expr ρ e) (subst-in-expr ρ e₁) (subst-in-expr ρ e₂)

    _[_] : Type → Type → Type
    M [ N ] = subst (subst-zero N) M
    _e[t_] : Expr → Type → Expr
    M e[t t ] = subst-in-expr (subst-zero t) M
    _effs[t_] : Effects → Type → Effects
    nil effs[t t ] = nil
    (x ∷ xs) effs[t t ] = (x [ t ])∷ xs effs[t t ]
```

\fi
# Typing judgements
Typing Contexts are represented as list of types, and type contexts are represented as lists of kinds. Judgements for membership of types have Peano numbers structure.
```
module Typing where
    infixl 5  _,_
    data Context : Set where
        ∅ : Context
        _,_ : Context → Type → Context

    data TContext : Set where
        ∅ : TContext
        _,_ : TContext → Kind → TContext
```
\iffalse
```
    infix  4  _∋_⦂_
    data _∋_⦂_ : Context → Id → Type → Set where
        Z : ∀ {Γ  A}
            → (Γ , A)  ∋ zero ⦂ A

        S : ∀ {Γ x y A}
            → Γ ∋ x ⦂ A
            → (Γ , y)  ∋ (suc x) ⦂ A

    data _∋t_⦂_ : TContext → Id → Kind → Set where
        Z : ∀ {Δ k}
            → (Δ , k)  ∋t zero ⦂ k

        S : ∀ {Δ x y k}
            → Δ ∋t x ⦂ k
            → (Δ , y)  ∋t (suc x) ⦂ k

    data _⊢_⦂e : TContext → Type → Set where
        ⊢ttv : ∀ {Δ n}
            → Δ ∋t n ⦂ E
            → Δ ⊢ ttv n ⦂e 
    data _⊢_⦂t : TContext → Type → Set
    data _⊢_⦂effs : TContext → Effects → Set
    data _⊢_⦂t where
        ⊢ttv : ∀ {Δ n }
            → Δ ∋t n ⦂ T 
            → Δ ⊢ ttv n ⦂t
        ⊢-> : ∀ {Δ t1 effs t2}
            → Δ ⊢ t1 ⦂t 
            → Δ ⊢ effs ⦂effs
            → Δ ⊢ t2 ⦂t 
            → Δ ⊢ t1 - effs > t1 ⦂t 
        ⊢forall : ∀ {Δ k t effs}
            → (Δ , k) ⊢ t ⦂t 
            → Δ ⊢ effs ⦂effs
            → Δ ⊢ forallt k t effs ⦂t
        ⊢label : ∀ {Δ e t effs}
            → Δ ⊢ e ⦂e
            → Δ ⊢ t ⦂t
            → Δ ⊢ effs ⦂effs
            → Δ ⊢ L e at t / effs ⦂t 
    data _⊢_⦂effs where
        ⊢nil : ∀ {Δ}
            → Δ ⊢ nil ⦂effs
        ⊢cons : ∀ {Δ e effs}
            → Δ ⊢ e ⦂e 
            → Δ ⊢ effs ⦂effs
            → Δ ⊢ e ∷ effs ⦂effs
    data _⊢_<⦂_ : TContext → Effects → Effects → Set where
        Z : ∀ {Δ}
            → Δ ⊢ nil <⦂ nil
        S : ∀ {Δ e E1 E2 }
            → Δ ⊢ E1 <⦂ E2
            → Δ ⊢ (e ∷ E1) <⦂ (e ∷ E2)
        S' : ∀ {Δ e E1 E2 }
            → Δ ⊢ E1 <⦂ E2
            → Δ ⊢ E1 <⦂ (e ∷ E2)

    nil<⦂⊥ : ∀ {Δ E } → Δ ⊢ E <⦂ nil → E ≡ nil
    nil<⦂⊥ (Z) = refl

    data _⊢_<t⦂_ : TContext → Type → Type → Set where

        <⦂refl : ∀ {Δ A} → Δ ⊢ A <t⦂ A

        <⦂→ : ∀ {Δ A1 A2 B1 B2 E1 E2} 
            → Δ ⊢ E1 <⦂ E2
            → Δ ⊢ A1 <t⦂ A2
            → Δ ⊢ B1 <t⦂ B2 
            → Δ ⊢ (A2 - E1 > B1) <t⦂ (A1 - E2 > B2)

        <⦂forall : ∀ {Δ A1 A2 k E1 E2}
            → (Δ , k) ⊢ A1 <t⦂ A2
            → Δ ⊢ E1 <⦂ E2
            → Δ ⊢ forallt k A1 E1 <t⦂ forallt k A2 E2
```
\fi

Expressions are extrinsically typed, thus typing judgements are represented separately.
Typing rules for `var`, `lam`, `app`, `tlam`, `tapp` are defined mostly as usual. The noticable difference is that expressions for values are generic over effect they execute.
```
    data _,_⊢_⦂_/_ : TContext → Context → Expr → Type → Effects → Set where
        ⊢var : ∀ {Γ Δ x A E}
            → Γ ∋ x ⦂ A
            -----------------------
            → Δ , Γ ⊢ var x ⦂ A / E

        ⊢lam : ∀ {Γ Δ e A B E F}
            → Δ , (Γ , A) ⊢ e ⦂ B / E
            ---------------------------------
            → Δ , Γ ⊢ lam e ⦂ A - E > B / F

        ⊢weak : ∀ {Γ Δ e A A' E E'}
            → Δ ⊢  A <t⦂ A'
            → Δ ⊢  E <⦂ E'
            → Δ , Γ ⊢ e ⦂ A / E
            ---------------------
            → Δ , Γ ⊢ e ⦂ A' / E' 

        ⊢app : ∀ {Γ Δ e1 e2 A B E}
            → Δ , Γ ⊢ e1 ⦂ A - E > B / E
            → Δ , Γ ⊢ e2 ⦂ A / E
            -----------------------------
            → Δ , Γ ⊢ app e1 e2  ⦂ B / E 

        ⊢forall : ∀ {Γ Δ e k A E F}
            → (Δ , k) , Γ  ⊢ e ⦂ TypeSubst.bump A /  TypeSubst.bump' E
            --------------------------------------
            → Δ , Γ ⊢ tlam k e ⦂ forallt k A E / F

        ⊢tapp : ∀ {Γ Δ e k A T E}
            → Δ ⊢ T ⦂t
            → Δ , Γ ⊢ e ⦂ forallt k A E / E
            ---------------------------------------------------
            → Δ  , Γ ⊢ tapp e T ⦂ A TypeSubst.[ T ] / (E TypeSubst.effs[t T ])
```
The `new` construct introduces new type variable, and variable that represent respectively effect and label. Type of label stores effect bound by label (here `ttv zero`). `A1` / `A2` represent type and effect of delimited computation.
```
        ⊢new : ∀ {Γ Δ e  A A1 E E1}
            → (Δ , Kind.E) , (Γ , (L ttv zero at A1 / E1))  ⊢ e ⦂ TypeSubst.bump A / TypeSubst.bump' E
            -----------------------
            → Δ , Γ ⊢ new e ⦂ A / E
```
Constructor `shift₀` uses only one effect `ttv n` that's represented by label. For it to be properly typed expression inside shift bind extra variable - where continuation will be plugged into. So type of this expression should take continuation and returns same type as reset, with effects visible in reset. And continuation itself should be an arrow from type of shift to type of whole delimited computation with effects of same computation.  Since continuation passed there will have `reset₀`, that `reset₀`  will introduce effect `ttv n`, so it shouldn't be represented in type of argument.

```
        ⊢shift₀ : ∀ {Γ Δ e e' A A' n E'}
            → Δ ⊢ ttv n ⦂e
            → Δ , Γ ⊢ e' ⦂ (L ttv n at  A' / E') / nil 
            → Δ , (Γ , A - E' > A' )  ⊢ e ⦂ A' / E'
            -----------------------------------------
            → Δ , Γ ⊢ shift₀ e' e ⦂ A / (ttv n ∷ nil)

```
The `reset₀` constructor has three parameters, first is expression that will have access to effect, so its list of effects is expanded. Second is continuation that will handle value returned from first argument. And third is label, which type stores type and effects of whole expression.
```
        ⊢reset₀ : ∀ {Γ Δ e e' en A A' n E'}
            → Δ ⊢ ttv n ⦂e
            → Δ , Γ   ⊢ e ⦂ A / (ttv n ∷ E')
            → Δ , (Γ , A)   ⊢ en ⦂ A' /  E'
            → Δ , Γ ⊢ e' ⦂ (L ttv n at  A' / E') / nil 
            ------------------------------------
            → Δ , Γ   ⊢ reset₀ e en e' ⦂ A' / E'
        
```
% TODO close chapter

\iffalse
```
module ExprSubst where
    open Types
    Rename = ℕ → ℕ

    Subst = ℕ → Expr
    ext : Rename → Rename 
    ext ρ zero    = zero
    ext ρ (suc x) = suc (ρ x)

    rename : Rename → (Expr → Expr)
    rename ρ (var x₁) = var (ρ x₁)
    rename ρ (lam x₁) = lam (rename (ext ρ) x₁)
    rename ρ (app x₁ x₂) = app (rename ρ x₁) (rename ρ x₂)
    rename ρ (tlam k x) = tlam k (rename ρ x)
    rename ρ (tapp x₁ x₂) = tapp (rename ρ x₁)  x₂
    rename ρ (new x₁) = new (rename (ext ρ) x₁)
    rename ρ (shift₀ x₁ x₂) = shift₀ (rename ρ x₁) (rename (ext ρ) x₂)
    rename ρ (reset₀ x₁ x₂ x₃) = reset₀ (rename ρ x₁) (rename (ext ρ) x₂) (rename ρ x₃)

    exts :  Subst → Subst 
    exts ρ zero    = var zero
    exts ρ (suc x) = rename suc (ρ x)

    subst : Subst → (Expr -> Expr) 
    subst ρ (var x) = ρ x
    subst ρ (lam y) = lam (subst (exts ρ) y)
    subst ρ (app y y₁) = app (subst ρ y) (subst ρ y₁)
    subst ρ (tlam k x) = tlam k (subst ρ x)
    subst ρ (tapp x₁ x₂) = tapp (subst ρ x₁) x₂
    subst ρ (new y) = new (subst (exts ρ) y)
    subst ρ (shift₀ y y₁) = shift₀ (subst ρ y)  (subst (exts ρ) y₁)
    subst ρ (reset₀ y y₁ y₂) = reset₀ (subst ρ y) (subst (exts ρ) y₁) (subst ρ y₂)

    subst-zero :  Expr  → Subst
    subst-zero e zero    = e
    subst-zero e (suc x) = var x

    infix 8 _[_]

    _[_] :  Expr -> Expr -> Expr
    M [ N ] = subst (subst-zero N) M

    _ : var zero [ lam (new (var zero)) ] ≡ lam (new (var zero))
    _ = refl
    _ : lam (var zero) [ var 555 ] ≡ lam  (var zero)
    _ = refl
```
\fi
