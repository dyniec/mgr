# Runtime language
Grammar of terms we defined previously doesn't have any expression that would have type of label, and shift and reset require the same labels. That means that to define reduction relation we would need to either go under `new` binders or introduce label expressions. We decided to define another runtime expression language expanded by the notion of label values.

When `new` expression is evaluated then all occurrences of variables bound by it would have it replaced with newly allocated label value. That means evaluation would need to keep a state for the allocator.

To ensure type safety we will expand syntax of types with allocated effects, and add new effect context to typing judgments, that maps allocations to type and effect of delimiter.

\iffalse
```
module Runtime where
open import Types using (Kind)

open import Data.Nat using (ℕ;zero;suc;_+_;_≤_;_<_)
open import Data.List using (List;_∷_;map) renaming ([] to nil)
import Data.Vec
import Data.Fin
open import Relation.Binary.PropositionalEquality using (_≡_;refl;_≢_)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Data.Product using (_×_;_,′_;Σ-syntax) renaming (_,_ to _,,_) using (proj₁;proj₂)
import Data.Maybe
```
\fi
```
module Types_ where
    Id : Set
    Id = ℕ
    Label = ℕ
    data Type : Set
    Effects : Set
    data Type  where
        ttv : Id → Type
        _-_>_ : Type → Effects → Type → Type
        forallt : Kind → Type → Effects →  Type
        L_at_/_ : Type → Type → Effects → Type
        Effect : Label → Type
    Effects = List Type
open Types_
```
\iffalse
```
module TypeSubst where
    Rename = ℕ → ℕ
    Subst = ℕ → Type
    ext = Types.TypeSubst.ext

    rename : Rename → (Type → Type)
    rename' : Rename → (Effects → Effects)
    rename ρ (ttv x) = ttv (ρ x)
    rename ρ (x - effs > x₁) = rename ρ x -  rename' ρ effs > rename ρ x₁
    rename ρ (forallt k x e) = forallt k (rename (ext ρ) x) (rename' ρ e)
    rename ρ (L x at x₁ / effs) =  L  rename ρ x at  rename ρ x₁ / rename' ρ effs
    rename ρ (Effect x) = Effect x
    rename' ρ nil = nil
    rename' ρ (x ∷ xs) = rename ρ x ∷ rename' ρ xs
    bump = rename suc
    bump' = rename' suc

    exts : Subst → Subst
    exts σ zero = ttv zero
    exts σ (suc x) = rename suc (σ x)

    subst : Subst → ( Type → Type)
    subst' : Subst → ( Effects → Effects)
    subst σ (ttv x) = σ x
    subst σ (t - x > t₁) =  subst σ  t - subst' σ x > subst σ t₁
    subst σ (forallt k t e) = forallt k (subst (exts σ) t) (subst' σ e)
    subst σ (L x at t / x₁) = L subst σ x at subst σ t / subst' σ x₁
    subst σ (Effect x) = Effect x
    subst' σ nil = nil
    subst' σ (x ∷ x₁) = subst σ x ∷ subst' σ x₁

    subst-zero : Type → Subst
    subst-zero t zero = t
    subst-zero t (suc x) = ttv x


    _[_] : Type → Type → Type
    M [ N ] = subst (subst-zero N) M
    _effs[t_] : Effects → Type → Effects
    nil effs[t t ] = nil
    (x ∷ xs) effs[t t ] = (x [ t ])∷ xs effs[t t ]
```

\fi
Most of the constructors in `RExpr` are the same as in `Expr`. Labels runtime values are represented by natural numbers.

```
module RuntimeExpr where
    data RExpr : Set where --runtime version
        var : ℕ → RExpr
        lam : RExpr → RExpr
        app : RExpr → RExpr → RExpr
        tlam : Kind → RExpr → RExpr
        tapp : RExpr -> Type -> RExpr
        new : RExpr → RExpr
        shift₀ : RExpr → RExpr → RExpr
        reset₀ : RExpr → RExpr → RExpr → RExpr
```
And here we have a separate term for the label, it just stores the allocated label identifier. 
```
        label : Label → RExpr 
```
\iffalse
```

    module RExprSubst where
        open TypeSubst
        substT-in-rexpr : Subst → RExpr → RExpr
        substT-in-rexpr ρ (tlam k e) = tlam k (substT-in-rexpr (TypeSubst.exts ρ) e)
        substT-in-rexpr ρ (new e) =  new (substT-in-rexpr (TypeSubst.exts ρ) e)
        
        substT-in-rexpr ρ (tapp e t) = tapp (substT-in-rexpr ρ e) (TypeSubst.subst ρ t)
        substT-in-rexpr ρ (var x) = var x
        substT-in-rexpr ρ (lam e) =  lam (substT-in-rexpr ρ e)
        substT-in-rexpr ρ (app e e₁) =  app (substT-in-rexpr ρ e) (substT-in-rexpr ρ e₁)
        substT-in-rexpr ρ (shift₀ e e₁) =  shift₀ (substT-in-rexpr ρ e) (substT-in-rexpr ρ e₁)
        substT-in-rexpr ρ (reset₀ e e₁ e₂) = reset₀ (substT-in-rexpr ρ e) (substT-in-rexpr ρ e₁) (substT-in-rexpr ρ e₂)
        substT-in-rexpr ρ (label l) = label l

        _e[t_] : RExpr → Type → RExpr
        M e[t t ] = substT-in-rexpr (TypeSubst.subst-zero t) M


```
\fi
Since the grammar of types has changed, we need to redefine contexts. That means almost all of the typing judgements need to be redefined.
Here we also introduce a new context for effects that maps label values to type and effect of delimiter. Such technique of store typing is described by Pierce\cite{tapl} where to ensure type safety of allocations, typing rules take maps from locations to types. It's represented by a finite vector of types and effects. Since they are only used during evaluation, the types and effects have no free variables.
```
module Typing where
    open RuntimeExpr
    infixl 5  _,_
    data Context : Set where
        ∅ : Context
        _,_ : Context → Type → Context

    data TContext : Set where
        ∅ : TContext
        _,_ : TContext → Kind → TContext

    push : Kind → TContext → TContext
    push k Δ = Δ , k 
    EContext = Σ[ n ∈ ℕ ] Data.Vec.Vec (Type × Effects) n
    pattern ∅' = 0 ,, Data.Vec.[]
```
\iffalse
```
    infix 4 _∋_⦂_
    data _∋_⦂_ : Context → Id → Type → Set where
        Z : ∀ {Γ  A}
            → (Γ , A)  ∋ zero ⦂ A

        S : ∀ {Γ x y A}
            → Γ ∋ x ⦂ A
            → (Γ , y)  ∋ (suc x) ⦂ A
    infix  4  _∋t_⦂_
    data _∋t_⦂_ : TContext → Id → Kind → Set where
        Z : ∀ {Δ k}
            → Δ , k   ∋t zero ⦂ k
        S : ∀ {Δ k x y}
            → Δ    ∋t x ⦂ k
            → Δ , y   ∋t suc(x) ⦂ k

    infix  4  _∋l_⦂_/_
    data _∋l_⦂_/_ : EContext → Label → Type → Effects → Set where
      ∋label : ∀ {Θ n} 
        → (t : n < proj₁ Θ)
        → Θ ∋l n ⦂ Data.Vec.lookup ( Θ .proj₂ )(Data.Fin.fromℕ< t) .proj₁ / Data.Vec.lookup ( Θ .proj₂ )(Data.Fin.fromℕ< t) .proj₂
        
    infix  4  _⨾_⊢_⦂e
    data _⨾_⊢_⦂e : TContext → EContext → Type → Set where
        ⊢ttv : ∀ {Δ Θ n}
            → Δ ∋t n ⦂ Kind.E
            → Δ ⨾ Θ ⊢ ttv n ⦂e
        ⊢alloc : ∀ {Δ Θ n A E}
            → Θ ∋l n ⦂ A / E
            → Δ ⨾ Θ ⊢ Effect n  ⦂e
    infix  4  _⨾_⊢_⦂t
    infix  4  _⨾_⊢_⦂effs
    data _⨾_⊢_⦂t : TContext → EContext → Type → Set
    data _⨾_⊢_⦂effs : TContext → EContext → Effects → Set
    data _⨾_⊢_⦂t where
        ⊢ttv : ∀ {Δ Θ n }
            → Δ ∋t n ⦂ Kind.T
            → Δ ⨾ Θ ⊢ ttv n ⦂t
        ⊢-> : ∀ {Δ Θ t1 effs t2}
            → Δ ⨾ Θ ⊢ t1 ⦂t
            → Δ ⨾ Θ ⊢ effs ⦂effs
            → Δ ⨾ Θ ⊢ t2 ⦂t
            → Δ ⨾ Θ ⊢ t1 - effs > t1 ⦂t
        ⊢forall : ∀ {Δ Θ k t effs}
            → (push k Δ) ⨾ Θ ⊢ t ⦂t
            → Δ ⨾ Θ ⊢ effs ⦂effs
            → Δ ⨾ Θ ⊢ forallt k t effs ⦂t
        ⊢label : ∀ {Δ Θ e t effs}
            → Δ ⨾ Θ ⊢ e ⦂e
            → Δ ⨾ Θ ⊢ t ⦂t
            → Δ ⨾ Θ ⊢ effs ⦂effs
            → Δ ⨾ Θ ⊢ L e at t / effs ⦂t
    data _⨾_⊢_⦂te : TContext → EContext → Type → Set where
      ⊢e : ∀{Δ Θ t}
        → Δ ⨾ Θ ⊢ t ⦂e
        → Δ ⨾ Θ ⊢ t ⦂te
      ⊢t : ∀{Δ Θ t}
        → Δ ⨾ Θ ⊢ t ⦂t
        → Δ ⨾ Θ ⊢ t ⦂te
    data _⨾_⊢_⦂effs where
        ⊢nil : ∀ {Δ Θ}
            → Δ ⨾ Θ ⊢ nil ⦂effs
        ⊢cons : ∀ {Δ Θ e effs}
            → Δ ⨾ Θ ⊢ e ⦂e
            → Δ ⨾ Θ ⊢ effs ⦂effs
            → Δ ⨾ Θ ⊢ e ∷ effs ⦂effs

    infix  4  _⊢_<⦂_
    data _⊢_<⦂_ : TContext → Effects → Effects → Set where
        Z : ∀ {Δ}
            → Δ ⊢ nil <⦂ nil
        S : ∀ {Δ e E1 E2 }
            → Δ ⊢ E1 <⦂ E2
            → Δ ⊢ (e ∷ E1) <⦂ (e ∷ E2)
        S' : ∀ {Δ e E1 E2 }
            → Δ ⊢ E1 <⦂ E2
            → Δ ⊢ E1 <⦂ (e ∷ E2)
    <⦂e-refl : ∀ {Δ E} → Δ ⊢ E <⦂ E
    <⦂e-refl {Δ} {nil} = Z
    <⦂e-refl {Δ} {x ∷ E₁} = S <⦂e-refl

    infix  4  _⊢_<t⦂_
    data _⊢_<t⦂_ : TContext → Type → Type → Set where
        <⦂refl : ∀ {Δ A} → Δ ⊢ A <t⦂ A
        <⦂→ : ∀ {Δ A1 A2 B1 B2 E1 E2}
            → Δ ⊢ E1 <⦂ E2
            → Δ ⊢ A1 <t⦂ A2
            → Δ ⊢ B1 <t⦂ B2
            → Δ ⊢ (A2 - E1 > B1) <t⦂ (A1 - E2 > B2)
        <⦂forall : ∀ {Δ A1 A2 k E1 E2}
            → (push k Δ) ⊢ A1 <t⦂ A2
            → Δ ⊢ E1 <⦂ E2
            → Δ ⊢ forallt k A1 E1 <t⦂ forallt k A2 E2

```
\fi
Most of the typing judgements are working as before. We omit ones that show up in surface language, as they just pass extra context for effects throughout.
```
    private
      variable
         Γ : Context
         Δ : TContext
         Θ : EContext
         e e1 e2 : RExpr
         A B : Type
         E E' F : Effects
         k : Kind
    infix  4  _⨾_⨾_⊢_⦂_/_
    data _⨾_⨾_⊢_⦂_/_ : TContext → EContext → Context → RExpr → Type → Effects → Set where
```
\iffalse
```

        ⊢var : ∀ {x }
            → Γ ∋ x ⦂ A
            -----------------------
            → Δ ⨾ Θ ⨾ Γ ⊢ var x ⦂ A / E

        ⊢lam : 
            Δ ⨾ Θ ⨾ (Γ , A) ⊢ e ⦂ B / E
            -------------------------------
            → Δ ⨾ Θ ⨾ Γ ⊢ lam e ⦂ A - E > B / F
        ⊢weak : ∀ {A'}
            → Δ ⊢  A <t⦂ A'
            → Δ ⊢  E <⦂ E'
            → Δ ⨾ Θ ⨾ Γ ⊢ e ⦂ A / E
            ---------------------
            → Δ ⨾ Θ ⨾ Γ ⊢ e ⦂ A' / E'
        ⊢app :
            Δ ⨾ Θ ⨾ Γ ⊢ e1 ⦂ A - E > B / E
            → Δ ⨾ Θ ⨾ Γ ⊢ e2 ⦂ A / E
            ----------------------------
            → Δ ⨾ Θ ⨾ Γ ⊢ app e1 e2  ⦂ B / E

        ⊢forall :
            Δ , k ⨾ Θ ⨾ Γ  ⊢ e ⦂ TypeSubst.bump A / TypeSubst.bump' E
            ----------------------------------
            → Δ ⨾ Θ ⨾ Γ ⊢ tlam k e ⦂ forallt k A E / F

        ⊢tapp : 
            Δ ⨾ Θ  ⊢ B ⦂te
            → Δ ⨾ Θ ⨾ Γ ⊢ e ⦂ forallt k A E / E
            ---------------------------------------------------------------
            → Δ ⨾ Θ ⨾ Γ ⊢ tapp e B ⦂ A TypeSubst.[ B ] / (E TypeSubst.effs[t B ])

        ⊢new : 
            Δ ⨾ Θ ⊢ B ⦂t
            → Δ ⨾ Θ ⊢ E' ⦂effs
            → (Δ , Kind.E) ⨾ Θ ⨾ (Γ , (L ttv zero at B / E'))  ⊢ e ⦂ TypeSubst.bump A / TypeSubst.bump' E
            ----------------------
            → Δ ⨾ Θ ⨾ Γ ⊢ new e ⦂ A / E

        ⊢shift₀ : ∀ {e' T}
            → Δ ⨾ Θ ⊢ T ⦂e
            → Δ ⨾ Θ ⨾ Γ ⊢ e' ⦂ (L T at  B / E') / nil
            → Δ ⨾ Θ ⨾ (Γ , A - E' > B )  ⊢ e ⦂ B / E'
            -----------------------------------------
            → Δ ⨾ Θ ⨾ Γ ⊢ shift₀ e' e ⦂ A / (T ∷ nil)

        ⊢reset₀ : ∀ {en e' T}
            → Δ ⨾ Θ  ⊢ T ⦂e
            → Δ ⨾ Θ ⨾ Γ       ⊢ e' ⦂ (L T at  B / E') / nil
            → Δ ⨾ Θ ⨾ Γ       ⊢ e  ⦂ A / (T ∷ E')
            → Δ ⨾ Θ ⨾ (Γ , A) ⊢ en ⦂ B /  E'
            ------------------------------------
            → Δ ⨾ Θ ⨾ Γ   ⊢ reset₀ e en e' ⦂ B / E'

```
\fi
Since labels are represented by natural numbers, ensuring type of label is just a lookup in appropriate context.
```
        ⊢label : ∀ {n }
            → Θ ∋l n ⦂ A / E
            --------------------------------------------
            → Δ ⨾ Θ ⨾ Γ ⊢ label n ⦂ (L (Effect n) at A / E) / F

```
\pagebreak
# Runtime embedding
We defined embedding of the original language in the current one, and proof that such embedding preserves typing judgements.
Most of the proof is omitted as it goes through almost all judgement types. We present only the type of main proof.

\iffalse
```
module Transform where
        open Types.Typing
        open Types.Expr
        open RuntimeExpr
        open Typing
        rt-t : Types.Types.Type → Type 
        rt-t' : Types.Types.Effects → Effects
        rt-t (Types.Types.ttv x) = ttv x
        rt-t (x Types.Types.- x₁ > x₂) = rt-t x - rt-t' x₁ > rt-t x₂
        rt-t (Types.Types.forallt k x ef) = forallt k (rt-t x) (rt-t' ef)
        rt-t (Types.Types.L l at x / ef) = L  rt-t l at  rt-t x / rt-t' ef
        rt-t' nil = nil
        rt-t' (x ∷ xs) = rt-t x ∷ rt-t' xs
        runtime : Types.Expr.Expr → RExpr
        runtime (var x) = var x
        runtime (lam x) = lam (runtime x)
        runtime (app x x₁) = app (runtime x) (runtime x₁)
        runtime (tlam x x₁) =  tlam x (runtime x₁)
        runtime (tapp x x₁) = tapp (runtime x) (rt-t x₁)
        runtime (new x) = new (runtime x)
        runtime (shift₀ x x₁) =  shift₀ (runtime x) (runtime x₁)
        runtime (reset₀ x x₁ x₂) = reset₀ (runtime x) (runtime x₁) (runtime x₂)

        runtimeΔ : Types.Typing.TContext → Typing.TContext
        runtimeΔ ∅ = ∅
        runtimeΔ (Δ , k) = runtimeΔ Δ , k
        runtimeΓ : Types.Typing.Context → Typing.Context
        runtimeΓ ∅ = ∅
        runtimeΓ (Γ , T) = runtimeΓ Γ , rt-t T

        runtime∋t : ∀ {Δ n k}
          → Δ Types.Typing.∋t n ⦂ k → (runtimeΔ Δ)  Typing.∋t n ⦂ k
        runtime∋t Z = Z
        runtime∋t (S z) = S (runtime∋t z)
        runtime∋ : ∀ {Γ n T}
          → Γ Types.Typing.∋ n ⦂ T → (runtimeΓ Γ)  Typing.∋ n ⦂ rt-t T
        runtime∋ Z = Z
        runtime∋ (S z) = S (runtime∋ z)
        
        runtime⊢e : ∀ {Δ T}
          → Δ Types.Typing.⊢ T ⦂e → (runtimeΔ Δ) ⨾ ∅' ⊢ rt-t T ⦂e
        runtime⊢e  (⊢ttv x) = ⊢ttv (runtime∋t x)
        runtime⊢t : ∀ {Δ T}
          → Δ Types.Typing.⊢ T ⦂t → (runtimeΔ Δ) ⨾ ∅' ⊢ rt-t T ⦂t
        runtime⊢effs : ∀ {Δ T}
          → Δ Types.Typing.⊢ T ⦂effs → (runtimeΔ Δ) ⨾ ∅' ⊢ rt-t' T ⦂effs
        runtime⊢t (⊢ttv x) = ⊢ttv (runtime∋t x)
        runtime⊢t (⊢-> x x₁ x₂) = ⊢-> (runtime⊢t x)
          (runtime⊢effs x₁) (runtime⊢t x)
        runtime⊢t (⊢forall x x₁) = ⊢forall (runtime⊢t x)
          (runtime⊢effs x₁)
        runtime⊢t (⊢label x x₁ x₂) = ⊢label (runtime⊢e x)
          (runtime⊢t x₁) (runtime⊢effs x₂)
        runtime⊢effs ⊢nil = ⊢nil
        runtime⊢effs (⊢cons x x₁) = ⊢cons (runtime⊢e x) (runtime⊢effs x₁)
        runtime⊢te : ∀ {Δ T}
          → Δ Types.Typing.⊢ T ⦂te → (runtimeΔ Δ) ⨾ ∅' ⊢ rt-t T ⦂te
        runtime⊢te (⊢e x) = ⊢e (runtime⊢e x)
        runtime⊢te (⊢t x) = ⊢t (runtime⊢t x)
        runtime<⦂ : ∀ {Δ E1 E2}
          → Δ Types.Typing.⊢ E1 <⦂ E2
          → (runtimeΔ Δ) Typing.⊢ rt-t' E1 <⦂ rt-t' E2
        runtime<⦂ (Z ) = Z
        runtime<⦂ (S x) = S (runtime<⦂ x)
        runtime<⦂ (S' x) = S' (runtime<⦂ x)
        runtime<t⦂ : ∀ {Δ T1 T2}
          → Δ Types.Typing.⊢ T1 <t⦂ T2
          → (runtimeΔ Δ) Typing.⊢ rt-t T1 <t⦂ rt-t T2
        runtime<t⦂ <⦂refl = <⦂refl
        runtime<t⦂ (<⦂→ x x₁ x₂) = <⦂→ (runtime<⦂ x)
          (runtime<t⦂ x₁) (runtime<t⦂ x₂)
        runtime<t⦂ (<⦂forall x x₁) = <⦂forall
          (runtime<t⦂ x) (runtime<⦂ x₁)
        rt-bump-t : ∀ ρ A → rt-t (Types.TypeSubst.rename ρ A)
          ≡ TypeSubst.rename ρ (rt-t A)
        rt-bump-e : ∀ ρ Ef → rt-t' (Types.TypeSubst.rename' ρ Ef)
          ≡ TypeSubst.rename' ρ (rt-t' Ef)
        rt-bump-t ρ (Types.Types.ttv x) = refl
        rt-bump-t ρ (A Types.Types.- Ef > B) rewrite (rt-bump-t ρ A) rewrite rt-bump-e ρ Ef rewrite rt-bump-t ρ B = refl
        rt-bump-t ρ (Types.Types.forallt k A Ef) rewrite rt-bump-e ρ Ef rewrite rt-bump-t (TypeSubst.ext ρ) A =  refl
        rt-bump-t ρ (Types.Types.L A at A2 / Ef) rewrite rt-bump-t ρ A rewrite rt-bump-t ρ A2 rewrite rt-bump-e ρ Ef = refl
        rt-bump-e ρ nil = refl
        rt-bump-e ρ (x ∷ ef) rewrite rt-bump-t ρ x rewrite rt-bump-e ρ ef = refl
        postulate
          rt-t-subst : ∀ A B → ((rt-t A) TypeSubst.[ rt-t B ] ) ≡
            (rt-t (A Types.TypeSubst.[ B ] ))
          rt-t'-subst : ∀ A B → ((rt-t' A) TypeSubst.effs[t rt-t B ] ) ≡
            (rt-t' (A Types.TypeSubst.effs[t B ] ))
          rt-tapp : ∀ {Δ Γ e A B E}
           → runtimeΔ Δ ⨾ ∅' ⨾ runtimeΓ Γ ⊢ tapp (runtime e) (rt-t B) ⦂
           (rt-t A) TypeSubst.[ rt-t B ] / (rt-t' E TypeSubst.effs[t rt-t B ])
           → runtimeΔ Δ ⨾ ∅' ⨾ runtimeΓ Γ ⊢ tapp (runtime e) (rt-t B) ⦂
           rt-t (A Types.TypeSubst.[ B ]) /
           rt-t' (E Types.TypeSubst.effs[t B ])

        rt-bump : ∀ {Δ Γ e A E k}
          → (runtimeΔ Δ , k  ⨾ ∅' ⨾ runtimeΓ Γ ⊢ runtime e ⦂
          rt-t (Types.TypeSubst.bump A) /
          rt-t' (Types.TypeSubst.bump' E))
          → (runtimeΔ Δ , k  ⨾ ∅' ⨾ runtimeΓ Γ ⊢ runtime e ⦂
          TypeSubst.bump (rt-t A) / TypeSubst.bump' (rt-t' E))
        rt-bump {A = A} {E = E} t rewrite rt-bump-t suc A rewrite rt-bump-e suc E = t
```
\fi
```
        runtime-types : ∀ {Δ Γ  e T E}
          → Δ Types.Typing., Γ ⊢ e ⦂ T / E → (runtimeΔ Δ ⨾ ∅' ⨾ runtimeΓ Γ ⊢ (runtime e) ⦂ rt-t T / rt-t' E)
```
\iffalse
```
        runtime-types (⊢var x) = ⊢var ( runtime∋ x )
        runtime-types (⊢lam t) = ⊢lam (runtime-types t)
        runtime-types (⊢weak x x₁ t) = ⊢weak (runtime<t⦂ x) (runtime<⦂ x₁) (runtime-types t)
        runtime-types (⊢app t t₁) = ⊢app (runtime-types t) (runtime-types t₁)
        runtime-types (⊢forall t) = ⊢forall (rt-bump (runtime-types t))
        runtime-types (⊢tapp {A = A} x t)  = rt-tapp {A = A} (⊢tapp (runtime⊢te x) (runtime-types t)) 
        runtime-types (⊢new tt te t) =  ⊢new (runtime⊢t tt) (runtime⊢effs te) (rt-bump( runtime-types t))
        runtime-types (⊢shift₀ x t t₁) = ⊢shift₀ ((runtime⊢e x)) (runtime-types t) (runtime-types t₁)
        runtime-types (⊢reset₀ x t t₁ t₂) = ⊢reset₀ (runtime⊢e x) (runtime-types t₂) (runtime-types t) (runtime-types t₁)

open Typing
_⧺_ : Typing.Context → Typing.Context → Typing.Context
y ⧺ ∅ = y
y ⧺ (xs , x) = (y ⧺ xs) , x
∋↑ : ∀ {Γ x A Γ'}
    → Γ ∋ x ⦂ A
    → Γ' ⧺ Γ ∋ x ⦂ A
e↑ : ∀ {Δ Θ Γ e T E Γ'}
    → Δ ⨾ Θ ⨾ Γ ⊢ e ⦂ T / E
    → Δ ⨾ Θ ⨾ (Γ' ⧺ Γ) ⊢ e ⦂ T / E
∋↑ {Γ = ∅} ()
∋↑ {Γ = Γ , x} Z = Z
∋↑ {Γ = Γ , x} (S t) =  S (∋↑ t)
e↑ (⊢var x) = ⊢var (∋↑ x)
e↑ (⊢lam t) = ⊢lam (e↑ t)
e↑ (⊢weak x x₁ t) = ⊢weak x x₁ (e↑ t)
e↑ (⊢app t t₁) = ⊢app (e↑ t) (e↑ t₁)
e↑ (⊢forall t) = ⊢forall (e↑ t)
e↑ (⊢tapp x t) = ⊢tapp x (e↑ t)
e↑ (⊢new tt te t) = ⊢new tt te (e↑ t)
e↑ (⊢shift₀ x t t₁) = ⊢shift₀ x (e↑ t) (e↑ t₁)
e↑ (⊢reset₀ x t t₁ t₂) = ⊢reset₀ x (e↑ t) (e↑ t₁) (e↑ t₂)
e↑ (⊢label x) = ⊢label x


module RExprSubstTyped where
    open RuntimeExpr
    ext : ∀ {Γ Γ' }
        → (∀ {A n } → Γ ∋ n ⦂ A → Σ[ m ∈ ℕ ] Γ' ∋ m ⦂ A)
        → (∀ {A B n} → (Γ , B) ∋ n ⦂ A → Σ[ m ∈ ℕ ] (Γ' , B) ∋ m ⦂ A)
    rename : ∀ {Γ Γ'}
        → (∀ {A n } → Γ ∋ n ⦂ A → Σ[ m ∈ ℕ ] Γ' ∋ m ⦂ A)
        → (∀ {Δ Θ A e E} → Δ ⨾ Θ ⨾ Γ ⊢ e ⦂ A / E →  Σ[ e' ∈ RExpr ] Δ ⨾ Θ ⨾ Γ' ⊢ e' ⦂ A / E)
    exts : ∀ {Γ Γ' Δ Θ}
        → (∀ {n A E} →  Γ ∋ n ⦂ A  → Σ[ e ∈ RExpr ] Δ ⨾ Θ ⨾ Γ' ⊢ e ⦂ A / E)
        → (∀ {n A B E} → Γ , B ∋ n ⦂ A  → Σ[ e ∈ RExpr ] Δ ⨾ Θ ⨾ Γ' , B ⊢ e ⦂ A / E)
    subst : ∀ {Δ Γ Γ' Θ}
        → (∀ {n A E} →  Γ ∋ n ⦂ A  → Σ[ e ∈ RExpr ] Δ ⨾ Θ ⨾ Γ' ⊢ e ⦂ A / E)
        → (∀ {e A E} → Δ ⨾ Θ ⨾ Γ  ⊢ e ⦂ A / E → Σ[ e ∈ RExpr ] Δ ⨾ Θ ⨾ Γ'  ⊢ e ⦂ A / E)

    _[_] : ∀ {Δ Θ Γ A B E1}
        → (e e1 : RExpr)
        → {te : Δ ⨾ Θ ⨾ Γ , A ⊢ e ⦂ B / E1}
        → {te1 : ∀ {E } → Δ ⨾ Θ ⨾ Γ ⊢ e1 ⦂ A / E}
        → Σ[ e' ∈ RExpr ] Δ ⨾ Θ ⨾ Γ ⊢ e' ⦂ B / E1
    _[_] {Δ}{Θ}{Γ}{A}{B}{E1}e e1 {te}{te1} = subst {Δ}{Γ , A}{Γ} σ  te
        where
        σ : (∀ {B n E} →  Γ , A ∋ n ⦂ B  → Σ[ e ∈ RExpr ] Δ ⨾ Θ ⨾ Γ ⊢ e ⦂ B / E)
        σ {E = E'} Z = e1 ,, (te1 {E'})
        σ {n = suc n} (S x) = var n ,, ⊢var x

    ext ρ Z = zero ,, Z
    ext ρ (S x) = suc (ρ x .proj₁) ,, S (ρ x .proj₂)

    rename ρ (⊢var { x = n } x) = (var (ρ x .proj₁)) ,, (⊢var (ρ x .proj₂) )
    rename ρ (⊢lam x) = (lam (rename (ext ρ) x .proj₁)) ,, (⊢lam (proj₂ (rename (ext ρ) x) ) )
    rename ρ (⊢weak x x₁ x₂ ) = (rename ρ x₂ .proj₁) ,, ⊢weak x x₁ (rename ρ x₂ .proj₂)
    rename ρ (⊢app x x₁) = app (rename ρ x .proj₁) (rename ρ x₁ .proj₁) ,, ⊢app (rename ρ x .proj₂) (rename ρ x₁ .proj₂)
    rename ρ (⊢forall {k = k} x) = tlam k (rename ρ x .proj₁) ,, ⊢forall (rename ρ x .proj₂)
    rename ρ (⊢tapp x x₁) = tapp (rename ρ x₁ .proj₁) _ ,, ⊢tapp x (rename ρ x₁ .proj₂)
    rename ρ (⊢new tt te x) = new (rename (ext ρ) x .proj₁) ,, ⊢new tt te (rename (ext ρ) x .proj₂)
    rename ρ (⊢shift₀ x x₁ x₂) = shift₀ (rename ρ x₁ .proj₁) ( rename (ext ρ) x₂ .proj₁)
        ,, ⊢shift₀ x (rename ρ x₁ .proj₂) (rename (ext ρ) x₂ .proj₂)
    rename ρ (⊢reset₀ x x₁ x₂ x₃) = reset₀ (rename ρ x₂ .proj₁) (rename (ext ρ) x₃ .proj₁) (rename ρ x₁ .proj₁)
        ,,
        ⊢reset₀ x (rename ρ x₁ .proj₂) (rename ρ x₂ .proj₂) (rename (ext ρ) x₃ .proj₂)
    rename ρ (⊢label x ) = _ ,, ⊢label x
    postulate
        pushΔ :  ∀ {Γ Γ' Δ k Θ}
            → (∀ {n A E} →  Γ ∋ n ⦂ A  → Σ[ e ∈ RExpr ] Δ ⨾ Θ ⨾ Γ' ⊢ e ⦂ A / E)
            → (∀ {n A E} →  Γ ∋ n ⦂ A  → Σ[ e ∈ RExpr ] (push k Δ)⨾ Θ ⨾ Γ' ⊢ e ⦂ A / E)
        eΔ :  ∀ {Γ Γ' Δ k Θ}
            → (∀ {n A E} →  Γ ∋ n ⦂ A  → Σ[ e ∈ RExpr ] Δ ⨾ Θ ⨾ Γ' ⊢ e ⦂ A / E)
            → (∀ {n A E} →  Γ ∋ n ⦂ A  → Σ[ e ∈ RExpr ]  Δ , k ⨾ Θ ⨾ Γ' ⊢ e ⦂ A / E)
    exts ρ Z = (var zero) ,, (⊢var Z) 
    exts ρ (S x)  = rename (λ {A = A₁} {n} z → suc n ,, S z) (ρ x .proj₂)

    subst σ (⊢var x) = σ x
    subst σ (⊢lam x) = lam (subst (exts σ) x .proj₁) ,, ⊢lam (subst (exts σ) x .proj₂)
    subst σ (⊢weak x x₁ x₂) = subst σ x₂ .proj₁ ,, ⊢weak x x₁ (subst σ x₂ .proj₂)
    subst σ (⊢app x x₁) = app (subst σ x .proj₁) (subst σ x₁ .proj₁) ,, ⊢app (subst σ x .proj₂) (subst σ x₁ .proj₂)
    subst σ (⊢forall {k = k} x) = tlam k (subst (pushΔ σ) x .proj₁) ,, ⊢forall (subst (pushΔ σ) x .proj₂)
    subst σ (⊢tapp x x₁) = tapp (subst σ x₁ .proj₁) _ ,, ⊢tapp x (subst σ x₁ .proj₂)
    subst σ (⊢new tt te x) = new (subst (pushΔ (exts σ))  x .proj₁)
        ,,  ⊢new tt te (subst (pushΔ (exts σ))  x .proj₂)
    subst σ (⊢shift₀ x x₁ x₂) = shift₀ (subst σ x₁ .proj₁) (subst (exts σ) x₂ .proj₁)
        ,, ⊢shift₀ x (subst σ x₁ .proj₂) (subst (exts σ) x₂ .proj₂)
    subst σ (⊢reset₀ x x₁ x₂ x₃) = reset₀ (subst σ x₂ .proj₁) ( subst (exts σ) x₃ .proj₁) (subst σ x₁ .proj₁)
        ,, ⊢reset₀ x (subst σ x₁ .proj₂) (subst σ x₂ .proj₂) (subst (exts σ) x₃ .proj₂)
    subst σ (⊢label {n = n} x) = label n ,, ⊢label x
```
\fi
