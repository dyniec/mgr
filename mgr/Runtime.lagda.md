# Runtime
Since grammar of terms doesn't have any expression that would have type of label, and shift and reset require same labels, that would mean that reduction relation would need to go under `new` binders. Instead we will define another expression language expanded by notion of label values.

When `new` expression is evaluated then all occurences of variables bound by it would have it replaced with newly allocated label value. That means evaluation would need to keep a state for allocator.

Since `new` binds type variables that represent effects, and those type variables are present in typing judgements of subexpressions, complete removal of `new` during evaluation would break type preservation. Thus we introduce `new'` that just binds type variables, and stores allocated label.

To make sure that label values bound to same type variable have same values, we change typing context so it stores label bound to that type variable.
```
module Runtime where
```

\iffalse
```
open import Types hiding (TContext;_⊢_⦂e;_⊢_⦂effs;_⊢_⦂t;_⊢_<⦂_;_⊢_<t⦂_;_∋t_⦂_ )

open import Data.Nat using (ℕ;zero;suc;_+_)
open import Data.List using (List;_∷_;map) renaming ([] to nil)
open import Relation.Binary.PropositionalEquality using (_≡_;refl;_≢_)
open import Data.Product using (_×_;_,′_;Σ-syntax) renaming (_,_ to _,,_) using (proj₁;proj₂)
import Data.Maybe
open Types.Types


module ExprSubst where
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
Most of constructors in `RExpr` are the same as in `Expr`. Labels runtime values are represented by Natural numbers.

```

module RuntimeExpr where
    Label = ℕ
    data RExpr : Set where --runtime version
        var : ℕ → RExpr
        lam : RExpr → RExpr
        app : RExpr → RExpr → RExpr
        tlam : Kind → RExpr → RExpr
        tapp : RExpr -> Type -> RExpr
        new : RExpr → RExpr
```
We are using `new'` to hold allocation of labels.
```
        new' : Label → RExpr → RExpr
        shift₀ : RExpr → RExpr → RExpr
        reset₀ : RExpr → RExpr → RExpr → RExpr
```
And here we have separate term for labels, it just stores label identifier. 
```
        label : Label → RExpr 
```
Typing Context now has different representation, because we store labels for typing variables bound by `new'`.
Thus all of judgements using them need to be redefined for the runtime language.
```
    data TContext : Set where
      ∅ : TContext
      `t : TContext → TContext
      `e : Data.Maybe.Maybe Label → TContext → TContext
    push : Kind → TContext → TContext
    push E xs = `e Data.Maybe.nothing xs
    push T xs = `t xs
    data _∋t_⦂_ : TContext → Id → Kind → Set where
        Zt : ∀ {Δ }
            → `t Δ   ∋t zero ⦂ T

        Ze : ∀ {Δ l }
            → `e l Δ   ∋t zero ⦂ E

        St : ∀ {Δ x k}
            → Δ ∋t x ⦂ k
            → `t Δ   ∋t (suc x) ⦂ k
        Se : ∀ {Δ x l k}
            → Δ ∋t x ⦂ k
            → `e l Δ  ∋t (suc x) ⦂ k

    data _∋l_⦂_ : TContext → Id → Label → Set where
        Z : ∀ {Δ l }
            → `e (Data.Maybe.just l) Δ   ∋l zero ⦂ l
        St : ∀ {Δ x l}
            → Δ ∋l x ⦂ l
            → `t Δ   ∋l (suc x) ⦂ l
        Se : ∀ {Δ x l l'}
            → Δ ∋l x ⦂ l
            → `e l' Δ  ∋l (suc x) ⦂ l
    data _⊢_⦂e : TContext → Type → Set where
        ⊢ttv : ∀ {Δ n}
            → Δ ∋t n ⦂ E
            → Δ ⊢ ttv n ⦂e
```
\iffalse
```
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
            → (push k Δ) ⊢ t ⦂t
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
```
\fi
```
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

    module RExprSubst where
```

Substitution of types in expressions is needed for evaluation of type application.
```  
        substT-in-rexpr : TypeSubst.Subst → RExpr → RExpr
        substT-in-rexpr ρ (tlam k e) = tlam k (substT-in-rexpr (TypeSubst.exts ρ) e)
        substT-in-rexpr ρ (new e) =  new (substT-in-rexpr (TypeSubst.exts ρ) e)
        substT-in-rexpr ρ (new' l e) =  new' l  (substT-in-rexpr (TypeSubst.exts ρ) e)
        
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
Most of typing judgement are working as before.
```
    data _⨾_⊢_⦂_/_ : TContext → Context → RExpr → Type → Effects → Set where

        ⊢var : ∀ {Γ Δ x A E}
            → Γ ∋ x ⦂ A
            -----------------------
            → Δ ⨾ Γ ⊢ var x ⦂ A / E

        ⊢lam : ∀ {Γ Δ e A B E F}
            → Δ ⨾ (Γ , A) ⊢ e ⦂ B / E
            -------------------------------
            → Δ ⨾ Γ ⊢ lam e ⦂ A - E > B / F
        ⊢weak : ∀ {Γ Δ e A A' E E'}
            → Δ ⊢  A <t⦂ A'
            → Δ ⊢  E <⦂ E'
            → Δ ⨾ Γ ⊢ e ⦂ A / E
            ---------------------
            → Δ  ⨾ Γ ⊢ e ⦂ A' / E'
        ⊢app : ∀ {Γ Δ e1 e2 A B E}
            → Δ ⨾ Γ ⊢ e1 ⦂ A - E > B / E
            → Δ ⨾ Γ ⊢ e2 ⦂ A / E
            ----------------------------
            → Δ ⨾ Γ ⊢ app e1 e2  ⦂ B / E

        ⊢forall : ∀ {Γ Δ e k A E F}
            → (push k Δ ) ⨾ Γ  ⊢ e ⦂ TypeSubst.bump A / TypeSubst.bump' E
            ----------------------------------
            → Δ ⨾ Γ ⊢ tlam k e ⦂ forallt k A E / F

        ⊢tapp : ∀ {Γ Δ e k A T E}
            → Δ ⊢ T ⦂t
            → Δ ⨾ Γ ⊢ e ⦂ forallt k A E / E
            ---------------------------------------------------------------
            → Δ ⨾ Γ ⊢ tapp e T ⦂ A TypeSubst.[ T ] / (E TypeSubst.effs[t T ])

        ⊢new : ∀ {Γ  Δ e  A A1 E E1}
            → (push Kind.E Δ)  ⨾ (Γ , (L ttv zero at A1 / E1))  ⊢ e ⦂ TypeSubst.bump A / TypeSubst.bump' E
            ----------------------
            → Δ ⨾ Γ ⊢ new e ⦂ A / E
```
`new'` stores label id in typing context so it can verify correctness of all label values.
```
        ⊢new' : ∀ {Γ Δ e l A E l'}
            → (`e (Data.Maybe.just l) Δ)  ⨾ Γ  ⊢ e ⦂ TypeSubst.bump A / TypeSubst.bump' E
            ---------------------------
            → Δ  ⨾ Γ ⊢ new' l' e ⦂ A / E

        ⊢shift₀ : ∀ {Γ Δ e e' A A' n E'}
            → Δ ⊢ ttv n ⦂e
            → Δ ⨾ Γ ⊢ e' ⦂ (L ttv n at  A' / E') / nil
            → Δ ⨾ (Γ , A - E' > A' )  ⊢ e ⦂ A' / E'
            -----------------------------------------
            → Δ ⨾ Γ ⊢ shift₀ e' e ⦂ A / (ttv n ∷ nil)

        ⊢reset₀ : ∀ {Γ Δ e e' en A A' n E'}
            → Δ ⊢ ttv n ⦂e
            → Δ ⨾ Γ ⊢ e' ⦂ (L ttv n at  A' / E') / nil
            → Δ ⨾ Γ   ⊢ e ⦂ A / (ttv n ∷ E')
            → Δ ⨾ (Γ , A)   ⊢ en ⦂ A' /  E'
            ------------------------------------
            → Δ ⨾ Γ   ⊢ reset₀ e en e' ⦂ A' / E'
```
Best we can do statically here is checking that label value really corresponds.
To prove prove safety we need to add extra conditions on label expressions. That is every label with same value needs to have same type (modulo type indices). Such extra condition would have to be passed to progress, and preservation would need to also prove that such condition is kept.
```
        ⊢label : ∀ {Γ Δ n l A E F}
            → Δ ∋l n ⦂ l
            --------------------------------------------
            → Δ ⨾ Γ ⊢ label l ⦂ (L (ttv n) at A / E) / F
```
# Runtime embedding
We defined embedding of original language in current one, and proof that such embedding preserves typing judgements.
Part of proof is skipped as it goes through almost all judgement types.
```
    runtime : Expr → RExpr
    runtime (var x) = var x
    runtime (lam x) = lam (runtime x)
    runtime (app x x₁) = app (runtime x) (runtime x₁)
    runtime (tlam x x₁) =  tlam x (runtime x₁)
    runtime (tapp x x₁) = tapp (runtime x) x₁
    runtime (new x) = new (runtime x)
    runtime (shift₀ x x₁) =  shift₀ (runtime x) (runtime x₁)
    runtime (reset₀ x x₁ x₂) = reset₀ (runtime x) (runtime x₁) (runtime x₂)
    runtimeΔ : Types.TContext → TContext
    runtimeΔ ∅ = ∅
    runtimeΔ (Δ , k) = push k (runtimeΔ Δ)
    
```
\iffalse
```
    runtime∋t : ∀ {Δ n k}
      → Δ Types.∋t n ⦂ k → (runtimeΔ Δ) ∋t n ⦂ k
    runtime∋t {Δ} {n} {T} Z = Zt
    runtime∋t {Δ} {n} {E} Z = Ze
    runtime∋t {Δ = Δ , x , T} (S z) = St (runtime∋t z)
    runtime∋t {Δ = Δ , x , E} (S z) = Se (runtime∋t z)
    runtime⊢e : ∀ {Δ T}
      → Δ Types.⊢ T ⦂e → (runtimeΔ Δ) ⊢ T ⦂e
    runtime⊢e  (⊢ttv x) = ⊢ttv (runtime∋t x)
    runtime⊢t : ∀ {Δ T}
      → Δ Types.⊢ T ⦂t → (runtimeΔ Δ) ⊢ T ⦂t
    runtime⊢effs : ∀ {Δ T}
      → Δ Types.⊢ T ⦂effs → (runtimeΔ Δ) ⊢ T ⦂effs
    runtime⊢t (⊢ttv x) = ⊢ttv (runtime∋t x)
    runtime⊢t (⊢-> x x₁ x₂) = ⊢-> (runtime⊢t x) (runtime⊢effs x₁) (runtime⊢t x)
    runtime⊢t (⊢forall x x₁) = ⊢forall (runtime⊢t x) (runtime⊢effs x₁)
    runtime⊢t (⊢label x x₁ x₂) = ⊢label (runtime⊢e x) (runtime⊢t x₁) (runtime⊢effs x₂)
    runtime⊢effs ⊢nil = ⊢nil
    runtime⊢effs (⊢cons x x₁) = ⊢cons (runtime⊢e x) (runtime⊢effs x₁)
    runtime<⦂ : ∀ {Δ E1 E2}
      → Δ Types.⊢ E1 <⦂ E2
      → (runtimeΔ Δ) ⊢ E1 <⦂ E2
    runtime<⦂ (Z ) = Z
    runtime<⦂ (S x) = S (runtime<⦂ x)
    runtime<⦂ (S' x) = S' (runtime<⦂ x)
    runtime<t⦂ : ∀ {Δ T1 T2}
      → Δ Types.⊢ T1 <t⦂ T2
      → (runtimeΔ Δ) ⊢ T1 <t⦂ T2
    runtime<t⦂ <⦂refl = <⦂refl
    runtime<t⦂ (<⦂→ x x₁ x₂) = <⦂→ (runtime<⦂ x) (runtime<t⦂ x₁) (runtime<t⦂ x₂)
    runtime<t⦂ (<⦂forall x x₁) = <⦂forall (runtime<t⦂ x) (runtime<⦂ x₁)
```
\fi

```
    runtime-types : ∀ {Δ Γ  e T E}
      → Δ , Γ ⊢ e ⦂ T / E → (runtimeΔ Δ ⨾ Γ ⊢ (runtime e) ⦂ T / E)
    runtime-types {Δ} {Γ} {e} {T₁} {E₁} (⊢var x) = ⊢var x
    runtime-types {Δ} {Γ} {e} {T₁} {E₁} (⊢lam t) = ⊢lam (runtime-types t)
    runtime-types {Δ} {Γ} {e} {T₁} {E₁} (⊢weak x x₁ t) = ⊢weak (runtime<t⦂ x) (runtime<⦂ x₁) (runtime-types t)
    runtime-types {Δ} {Γ} {e} {T₁} {E₁} (⊢app t t₁) = ⊢app (runtime-types t) (runtime-types t₁)
    runtime-types {Δ} {Γ} {e} {T₁} {E₁} (⊢forall t) = ⊢forall (runtime-types t)
    runtime-types {Δ} {Γ} {e} {T₁} {E₁} (⊢tapp x t) = ⊢tapp (runtime⊢t x) (runtime-types t)
    runtime-types {Δ} {Γ} {e} {T₁} {E₁} (⊢new t) = ⊢new (runtime-types t)
    runtime-types {Δ} {Γ} {e} {T₁} {E₁} (⊢shift₀ x t t₁) = ⊢shift₀ ((runtime⊢e x)) (runtime-types t) (runtime-types t₁)
    runtime-types {Δ} {Γ} {e} {T₁} {E₁} (⊢reset₀ x t t₁ t₂) = ⊢reset₀ (runtime⊢e x) (runtime-types t₂) (runtime-types t) (runtime-types t₁)
        
```
Small lemma about lifting context and that it keeps type safety.
```
    _⧺_ : Context → Context → Context
    y ⧺ ∅ = y
    y ⧺ (xs , x) = (y ⧺ xs) , x
    ∋↑ : ∀ {Γ x A Γ'}
      → Γ ∋ x ⦂ A
      → Γ' ⧺ Γ ∋ x ⦂ A
    ∋↑ {Γ = ∅} ()
    ∋↑ {Γ = Γ , x} Z = Z
    ∋↑ {Γ = Γ , x} (S t) =  S (∋↑ t)
    e↑ : ∀ {Δ Γ e T E Γ'}
      → Δ ⨾ Γ ⊢ e ⦂ T / E
      → Δ ⨾ (Γ' ⧺ Γ) ⊢ e ⦂ T / E
    e↑ (⊢var x) = ⊢var (∋↑ x)
    e↑ (⊢lam t) = ⊢lam (e↑ t)
    e↑ (⊢weak x x₁ t) = ⊢weak x x₁ (e↑ t)
    e↑ (⊢app t t₁) = ⊢app (e↑ t) (e↑ t₁)
    e↑ (⊢forall t) = ⊢forall (e↑ t)
    e↑ (⊢tapp x t) = ⊢tapp x (e↑ t)
    e↑ (⊢new t) = ⊢new (e↑ t)
    e↑ (⊢new' t) = ⊢new' (e↑ t)
    e↑ (⊢shift₀ x t t₁) = ⊢shift₀ x (e↑ t) (e↑ t₁)
    e↑ (⊢reset₀ x t t₁ t₂) = ⊢reset₀ x (e↑ t) (e↑ t₁) (e↑ t₂)
    e↑ (⊢label x) = ⊢label x
```
Substitution and proof relating typing judgement of inputs and result are defined together inductively.
```
    module RExprSubstTyped where
        ext : ∀ {Γ Γ' }
            → (∀ {A n } → Γ ∋ n ⦂ A → Σ[ m ∈ ℕ ] Γ' ∋ m ⦂ A)
            → (∀ {A B n} → (Γ , B) ∋ n ⦂ A → Σ[ m ∈ ℕ ] (Γ' , B) ∋ m ⦂ A)
        ext ρ Z = zero ,, Z
        ext ρ (S x) = suc (ρ x .proj₁) ,, S (ρ x .proj₂)

        rename : ∀ {Γ Γ'}
            → (∀ {A n } → Γ ∋ n ⦂ A → Σ[ m ∈ ℕ ] Γ' ∋ m ⦂ A)
            → (∀ {Δ A e E} → Δ ⨾ Γ ⊢ e ⦂ A / E →  Σ[ e' ∈ RExpr ] Δ ⨾ Γ' ⊢ e' ⦂ A / E)
        rename ρ (⊢var { x = n } x) = (var (ρ x .proj₁)) ,, (⊢var (ρ x .proj₂) )
        rename ρ (⊢lam x) = (lam (rename (ext ρ) x .proj₁)) ,, (⊢lam (proj₂ (rename (ext ρ) x) ) )
        rename ρ (⊢weak x x₁ x₂ ) = (rename ρ x₂ .proj₁) ,, ⊢weak x x₁ (rename ρ x₂ .proj₂)
        rename ρ (⊢app x x₁) = app (rename ρ x .proj₁) (rename ρ x₁ .proj₁) ,, ⊢app (rename ρ x .proj₂) (rename ρ x₁ .proj₂)
        rename ρ (⊢forall {k = k} x) = tlam k (rename ρ x .proj₁) ,, ⊢forall (rename ρ x .proj₂)
        rename ρ (⊢tapp x x₁) = tapp (rename ρ x₁ .proj₁) _ ,, ⊢tapp x (rename ρ x₁ .proj₂)
        rename ρ (⊢new x) = new (rename (ext ρ) x .proj₁) ,, ⊢new (rename (ext ρ) x .proj₂)
        rename ρ (⊢new' {l = l} x) = new' l (rename ρ x .proj₁)
          ,, ⊢new' (rename ρ x .proj₂)
        rename ρ (⊢shift₀ x x₁ x₂) = shift₀ (rename ρ x₁ .proj₁) ( rename (ext ρ) x₂ .proj₁)
          ,, ⊢shift₀ x (rename ρ x₁ .proj₂) (rename (ext ρ) x₂ .proj₂)
        rename ρ (⊢reset₀ x x₁ x₂ x₃) = reset₀ (rename ρ x₂ .proj₁) (rename (ext ρ) x₃ .proj₁) (rename ρ x₁ .proj₁)
          ,,
          ⊢reset₀ x (rename ρ x₁ .proj₂) (rename ρ x₂ .proj₂) (rename (ext ρ) x₃ .proj₂)
        rename ρ (⊢label x ) = _ ,, ⊢label x
        postulate
            pushΔ :  ∀ {Γ Γ' Δ k}
                → (∀ {n A E} →  Γ ∋ n ⦂ A  → Σ[ e ∈ RExpr ] Δ ⨾ Γ' ⊢ e ⦂ A / E)
                → (∀ {n A E} →  Γ ∋ n ⦂ A  → Σ[ e ∈ RExpr ] (push k Δ) ⨾ Γ' ⊢ e ⦂ A / E)
            eΔ :  ∀ {Γ Γ' Δ k}
                → (∀ {n A E} →  Γ ∋ n ⦂ A  → Σ[ e ∈ RExpr ] Δ ⨾ Γ' ⊢ e ⦂ A / E)
                → (∀ {n A E} →  Γ ∋ n ⦂ A  → Σ[ e ∈ RExpr ] (`e k Δ) ⨾ Γ' ⊢ e ⦂ A / E)
        exts : ∀ {Γ Γ' Δ}
            → (∀ {n A E} →  Γ ∋ n ⦂ A  → Σ[ e ∈ RExpr ] Δ ⨾ Γ' ⊢ e ⦂ A / E)
            → (∀ {n A B E} → Γ , B ∋ n ⦂ A  → Σ[ e ∈ RExpr ] Δ ⨾ Γ' , B ⊢ e ⦂ A / E)
        exts ρ Z = (var zero) ,, (⊢var Z) 
        exts ρ (S x)  = rename (λ {A = A₁} {n} z → suc n ,, S z) (ρ x .proj₂)
        
        subst : ∀ {Δ Γ Γ'}
            → (∀ {n A E} →  Γ ∋ n ⦂ A  → Σ[ e ∈ RExpr ] Δ ⨾ Γ' ⊢ e ⦂ A / E)
            → (∀ {e A E} → Δ ⨾ Γ  ⊢ e ⦂ A / E → Σ[ e ∈ RExpr ] Δ ⨾ Γ'  ⊢ e ⦂ A / E)
        subst σ (⊢var x) = σ x
        subst σ (⊢lam x) = lam (subst (exts σ) x .proj₁) ,, ⊢lam (subst (exts σ) x .proj₂)
        subst σ (⊢weak x x₁ x₂) = subst σ x₂ .proj₁ ,, ⊢weak x x₁ (subst σ x₂ .proj₂)
        subst σ (⊢app x x₁) = app (subst σ x .proj₁) (subst σ x₁ .proj₁) ,, ⊢app (subst σ x .proj₂) (subst σ x₁ .proj₂)
        subst σ (⊢forall {k = k} x) = tlam k (subst (pushΔ σ) x .proj₁) ,, ⊢forall (subst (pushΔ σ) x .proj₂)
        subst σ (⊢tapp x x₁) = tapp (subst σ x₁ .proj₁) _ ,, ⊢tapp x (subst σ x₁ .proj₂)
        subst σ (⊢new x) = new (subst (pushΔ (exts σ))  x .proj₁)
          ,,  ⊢new (subst (pushΔ (exts σ))  x .proj₂)
        subst σ {e = new' l _}(⊢new' x) = new' l (subst (eΔ σ) x .proj₁)
          ,, ⊢new' (subst (eΔ σ) x .proj₂)
        subst σ (⊢shift₀ x x₁ x₂) = shift₀ (subst σ x₁ .proj₁) (subst (exts σ) x₂ .proj₁)
          ,, ⊢shift₀ x (subst σ x₁ .proj₂) (subst (exts σ) x₂ .proj₂)
        subst σ (⊢reset₀ x x₁ x₂ x₃) = reset₀ (subst σ x₂ .proj₁) ( subst (exts σ) x₃ .proj₁) (subst σ x₁ .proj₁)
          ,, ⊢reset₀ x (subst σ x₁ .proj₂) (subst σ x₂ .proj₂) (subst (exts σ) x₃ .proj₂)
        subst σ (⊢label {l = l} x) = label l ,, ⊢label x

        _[_] : ∀ {Δ Γ A B E1}
            → (e e1 : RExpr)
            → {te : Δ ⨾ Γ , A ⊢ e ⦂ B / E1}
            → {te1 : ∀ {E } → Δ ⨾ Γ ⊢ e1 ⦂ A / E}
            → Σ[ e' ∈ RExpr ] Δ ⨾ Γ ⊢ e' ⦂ B / E1
        _[_] {Δ}{Γ}{A}{B}{E1}e e1 {te}{te1} = subst {Δ}{Γ , A}{Γ} σ  te
          where
            σ : (∀ {B n E} →  Γ , A ∋ n ⦂ B  → Σ[ e ∈ RExpr ] Δ ⨾ Γ ⊢ e ⦂ B / E)
            σ {E = E'} Z = e1 ,, (te1 {E'})
            σ {n = suc n} (S x) = var n ,, ⊢var x
```

