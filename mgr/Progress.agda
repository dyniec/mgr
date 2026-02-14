module mgr.Progress where


open import mgr.Types hiding (TContext;_⊢_⦂e;_⊢_⦂effs;_⊢_⦂t;_⊢_<⦂_;_⊢_<t⦂_;_∋t_⦂_ )

open import Data.Nat
import Data.Nat.Properties
import Relation.Binary.Definitions
open import Data.List using (List;_∷_;map) renaming ([] to nil)
import Data.Maybe
open import Relation.Binary.PropositionalEquality using (_≡_;refl;_≢_)
open import Data.Product using (_×_;_,′_;Σ-syntax) renaming (_,_ to _,,_)



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

module Runtime where
    Label = ℕ
    data RExpr : Set where --runtime version
        var : ℕ → RExpr
        lam : RExpr → RExpr
        app : RExpr → RExpr → RExpr
        tlam : Kind → RExpr → RExpr
        tapp : RExpr -> Type -> RExpr
        new : RExpr → RExpr
        new' : Label → RExpr → RExpr -- label is already assigned, keeping shape of new to prove preservation
        shift₀ : RExpr → RExpr → RExpr
        reset₀ : RExpr → RExpr → RExpr → RExpr
        label : Label → RExpr -- label for effects
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
            → `e l Δ   ∋t zero ⦂ T

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
        ⊢forall : ∀ {Δ k t}
            → (push k Δ) ⊢ t ⦂t
            → Δ ⊢ forallt k t ⦂t
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
        Z : ∀ {Δ E}
            → Δ ⊢ E ⦂effs
            → Δ ⊢ nil <⦂ nil
        S : ∀ {Δ e E1 E2 }
            → Δ ⊢ E1 <⦂ E2
            → Δ ⊢ e ⦂e
            → Δ ⊢ (e ∷ E1) <⦂ (e ∷ E2)
        S' : ∀ {Δ e E1 E2 }
            → Δ ⊢ E1 <⦂ E2
            → Δ ⊢ e ⦂e
            → Δ ⊢ E1 <⦂ (e ∷ E2)

    data _⊢_<t⦂_ : TContext → Type → Type → Set where
        <⦂refl : ∀ {Δ A} → Δ ⊢ A <t⦂ A
        <⦂→ : ∀ {Δ A1 A2 B1 B2 E1 E2}
            → Δ ⊢ E1 <⦂ E2
            → Δ ⊢ A1 <t⦂ A2
            → Δ ⊢ B1 <t⦂ B2
            → Δ ⊢ (A2 - E1 > B1) <t⦂ (A1 - E2 > B2)
        <⦂forall : ∀ {Δ A1 A2 k}
            → (push k Δ) ⊢ A1 <t⦂ A2
            → Δ ⊢ forallt k A1 <t⦂ forallt k A2
    module RExprSubst where
        Rename = ℕ → ℕ

        Subst = ℕ → RExpr

        ext : Rename → Rename 
        ext ρ zero    = zero
        ext ρ (suc x) = suc (ρ x)

        rename : Rename → (RExpr → RExpr)
        rename ρ (var x₁) = var (ρ x₁)
        rename ρ (lam x₁) = lam (rename (ext ρ) x₁)
        rename ρ (app x₁ x₂) = app (rename ρ x₁) (rename ρ x₂)
        rename ρ (tlam k x) = tlam k (rename ρ x)
        rename ρ (tapp x₁ x₂) = tapp (rename ρ x₁)  x₂
        rename ρ (new x₁) = new (rename (ext ρ) x₁)
        rename ρ (new' l x₁) = new' l (rename ρ x₁)
        rename ρ (shift₀ x₁ x₂) = shift₀ (rename ρ x₁) (rename (ext ρ) x₂)
        rename ρ (reset₀ x₁ x₂ x₃) = reset₀ (rename ρ x₁) (rename (ext ρ) x₂) (rename ρ x₃)
        rename ρ (label l) = label l

        exts :  Subst → Subst 
        exts ρ zero    = var zero
        exts ρ (suc x) = rename suc (ρ x)

        subst : Subst → (RExpr -> RExpr) 
        subst ρ (var x) = ρ x
        subst ρ (lam y) = lam (subst (exts ρ) y)
        subst ρ (app y y₁) = app (subst ρ y) (subst ρ y₁)
        subst ρ (tlam k x) = tlam k (subst ρ x)
        subst ρ (tapp x₁ x₂) = tapp (subst ρ x₁) x₂
        subst ρ (new y) = new (subst (exts ρ) y)
        subst ρ (new' l y) = new' l (subst ρ y)
        subst ρ (shift₀ y y₁) = shift₀ (subst ρ y)  (subst (exts ρ) y₁)
        subst ρ (reset₀ y y₁ y₂) = reset₀ (subst ρ y) (subst (exts ρ) y₁) (subst ρ y₂)
        subst ρ (label l) = label l

        subst-zero :  RExpr  → Subst
        subst-zero e zero    = e
        subst-zero e (suc x) = var x
        
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

        _[_] :  RExpr -> RExpr -> RExpr
        M [ N ] = subst (subst-zero N) M
        _e[t_] : RExpr → Type → RExpr
        M e[t t ] = substT-in-rexpr (TypeSubst.subst-zero t) M

        _ : var zero [ lam (new (var zero)) ] ≡ lam (new (var zero))
        _ = refl
        _ : lam (var zero) [ var 555 ] ≡ lam  (var zero)
        _ = refl
    open RExprSubst

    data _⨾_⊢_⦂_/_ : TContext → Context → RExpr → Type → Effects → Set where

        ⊢var : ∀ {Γ Δ x A E}
            → Γ ∋ x ⦂ A
            → Δ ⊢ E ⦂effs
            → Δ ⨾ Γ ⊢ var x ⦂ A / E


        ⊢lam : ∀ {Γ Δ e A B E}
            → Δ ⨾ (Γ , A) ⊢ e ⦂ B / E
            → Δ ⨾ Γ ⊢ lam e ⦂ A - E > B / nil
        ⊢weak : ∀ {Γ Δ e A A' E E'}
            → Δ ⊢ E' ⦂effs
            → Δ ⊢  A <t⦂ A'
            → Δ ⊢  E <⦂ E'
            → Δ ⨾ Γ ⊢ e ⦂ A / E
            → Δ  ⨾ Γ ⊢ e ⦂ A' / E'
        ⊢app : ∀ {Γ Δ e1 e2 A B E}
            → Δ ⨾ Γ ⊢ e1 ⦂ A - E > B / E
            → Δ ⨾ Γ ⊢ e2 ⦂ A / E
            → Δ ⨾ Γ ⊢ app e1 e2  ⦂ B / E
        ⊢forall : ∀ {Γ Δ e k A E}
            → (push k Δ ) ⨾ Γ  ⊢ e ⦂ TypeSubst.bump A / TypeSubst.bump' E
            → Δ ⨾ Γ ⊢ tlam k e ⦂ forallt k A / E

        ⊢tapp : ∀ {Γ Δ e k A T E}
            → Δ ⊢ T ⦂t
            → Δ ⨾ Γ ⊢ e ⦂ forallt k A / E
            → (push k Δ)  ⨾ Γ ⊢ tapp e T ⦂ A TypeSubst.[ T ] / (E TypeSubst.effs[t T ])

        ⊢new : ∀ {Γ  Δ e  A A1 E E1}
            → (push Kind.E Δ)  ⨾ (Γ , (L ttv zero at A1 / E1))  ⊢ e ⦂ TypeSubst.bump A / TypeSubst.bump' E
            → Δ ⨾ Γ ⊢ new e ⦂ A / E
            
        ⊢new' : ∀ {Γ Δ e l A E}
            → (`e (Data.Maybe.just l) Δ)  ⨾ Γ  ⊢ e ⦂ TypeSubst.bump A / TypeSubst.bump' E
            → Δ  ⨾ Γ ⊢ new' l e ⦂ A / E

        ⊢shift₀ : ∀ {Γ Δ e e' A A' n E'}
            → Δ ⊢ ttv n ⦂e
            → Δ ⨾ Γ ⊢ e' ⦂ (L ttv n at  A' / E') / nil
            → Δ ⨾ (Γ , A - E' > A' )  ⊢ e ⦂ A' / E'
            → Δ ⨾ Γ ⊢ shift₀ e' e ⦂ A / (ttv n ∷ nil)

        ⊢reset₀ : ∀ {Γ Δ e e' en A A' n E'}
            → Δ ⊢ ttv n ⦂e
            → Δ ⨾ Γ ⊢ e' ⦂ (L ttv n at  A' / E') / nil
            → Δ ⨾ Γ   ⊢ e ⦂ A / (ttv n ∷ E')
            → Δ ⨾ (Γ , A)   ⊢ en ⦂ A' /  E'
            → Δ ⨾ Γ   ⊢ reset₀ e en e' ⦂ A' / E'

        ⊢label : ∀ {Γ Δ n l A E}
            → Δ ⊢ A ⦂t
            → Δ ⊢ E ⦂effs
            → Δ ∋l n ⦂ l
            → Δ ⨾ Γ ⊢ label l ⦂ (L (ttv n) at A / E) / nil

    runtime : Expr → RExpr
    runtime (var x) = var x
    runtime (lam x) = lam (runtime x)
    runtime (app x x₁) = app (runtime x) (runtime x₁)
    runtime (tlam x x₁) =  tlam x (runtime x₁)
    runtime (tapp x x₁) = tapp (runtime x) x₁
    runtime (new x) = new (runtime x)
    runtime (shift₀ x x₁) =  shift₀ (runtime x) (runtime x₁)
    runtime (reset₀ x x₁ x₂) = reset₀ (runtime x) (runtime x₁) (runtime x₂)
    runtimeΔ : mgr.Types.TContext → TContext
    runtimeΔ ∅ = ∅
    runtimeΔ (Δ , T) = `t (runtimeΔ Δ)
    runtimeΔ (Δ , E) = `e (Data.Maybe.nothing) (runtimeΔ Δ)
    {-
    runtime-types : ∀ {Δ Γ  e T E}
      → Δ , Γ ⊢ e ⦂ T / E → (runtimeΔ Δ ⨾ Γ ⊢ (runtime e) ⦂ T / E)
    runtime-types (⊢var x x₁) = ⊢var {!!} {!!}
    runtime-types (⊢lam x) = ⊢lam (runtime-types x)
    runtime-types (⊢app x x₁) = ⊢app (runtime-types x) (runtime-types x₁) 
    runtime-types (⊢weak x x₁ x₂ x₃) = ⊢weak x x₁ x₂ (runtime-types x₃)
    runtime-types (⊢forall x) = ⊢forall (runtime-types x)
    runtime-types (⊢tapp x x₁) = ⊢tapp x (runtime-types x₁)
    runtime-types (⊢new x) = ⊢new (runtime-types x)
    runtime-types (⊢shift₀ x x₁ x₂) = ⊢shift₀ x (runtime-types x₁) (runtime-types x₂)
    runtime-types (⊢reset₀ x x₁ x₂ x₃) = ⊢reset₀ x (runtime-types x₁) (runtime-types x₂) (runtime-types x₃)
    -}
        

open Runtime

data Value : RExpr -> Set where
    vlam : ∀ { e } → Value (lam e)
    vLam : ∀ { k e } → Value (tlam k e)
    vlab : ∀ { n } → Value (label n)


-- typed frames
-- it would be normally named Context, but that's taken by Context used in typing
data Frame (Δ : TContext) (T : Type) (Eff : Effects) : Type → Effects → TContext → ℕ →  Set where
  -- parametrized by: Δ Γ - typing context outside of frame
  -- T - type of the hole (deBruijn indexes of types are with respect of the hole (so well typed in Δ')
  -- Eff - effects of frame - indexed with respect of whole frame
  -- indexed by Type - returned type of frame if plugged correctly
  -- indexed by Effects - effects of hole, indices respective to hole
  -- indexed by Tcontext - typing context of the hole, should be the same as n elements longer than Δ
  -- indexed by ℕ - amount of new' constructors - means how typing context changed between hole and whole frame
  fempty : Frame Δ T Eff T Eff Δ zero
  fapp₁ : ∀ {A B n Δ'  E} → Frame Δ T Eff (A - Eff > B) E Δ' n → (e : RExpr)  → { Δ ⨾ ∅ ⊢ e ⦂ A / Eff  } → Frame Δ T Eff B E Δ' n
  fapp₂ : ∀ {A B n Δ' E} → (e : RExpr) → { v : Value e} → { Δ ⨾ ∅ ⊢ e ⦂ ( A - Eff > B) / Eff } -> Frame Δ T Eff A E Δ'  n  -> Frame Δ T Eff B E Δ' n
  fnew' : ∀ {A n Δ' E} → (l : Label) → Frame (`e (Data.Maybe.just l) Δ) T (TypeSubst.bump' Eff) (TypeSubst.bump A) E Δ' n → Frame Δ T Eff A E Δ' (suc n)


plug : ∀ {Δ Δ' T Eff A n E} → Frame Δ T Eff A E Δ' n → (e : RExpr) → Δ' ⨾ ∅ ⊢ e ⦂ T / E  →  Σ[ res ∈ RExpr ] (Δ ⨾ ∅ ⊢ res ⦂ A / Eff)
plug fempty e t = e ,, t
plug (fapp₁ f e₁ {te₁}) e t  with (plug f e t)
... | (res ,, tt) =  app res  e₁ ,, (⊢app tt te₁)
plug (fapp₂ e₁ {_} {te₁} f) e t with (plug f e t)
... | (res ,, tt ) =  app e₁ res ,, ⊢app te₁ tt
plug (fnew' l f) e t with (plug f e t)
... | (res ,, tt) = new' l res ,, ⊢new' tt 

_∘f_ : ∀ {Δ Δ' Δ'' Eff Eff' Eff'' A B C n m} → Frame Δ B Eff A Eff' Δ' n → Frame Δ' C Eff' B Eff'' Δ''  m → Frame Δ C Eff A Eff'' Δ'' (n + m)
fempty ∘f F = F
fapp₁ f e {t} ∘f F = fapp₁ (f ∘f F )  e {t} 
fapp₂ e {v} {t} f ∘f F = fapp₂ e {v} {t} (f ∘f F)
fnew' l f ∘f F = fnew' l (f ∘f F)

∘f-lemma : ∀ {Δ Δ' Δ'' Eff Eff' Eff'' A B C n m} → (f1 : Frame Δ B Eff A Eff' Δ' n) → (f2 : Frame Δ' C Eff' B Eff'' Δ''  m) → (e : RExpr) → (t : Δ'' ⨾ ∅ ⊢ e ⦂ C / Eff'')
         → plug ( f1 ∘f f2)  e t ≡ ((λ x → plug f1 (Data.Product.proj₁ x) (Data.Product.proj₂ x))(plug f2 e t))
∘f-lemma fempty f2 e t = refl
∘f-lemma (fapp₁ f1 e₁) f2 e t rewrite ∘f-lemma f1 f2 e t = refl
∘f-lemma (fapp₂ e₁ f1) f2 e t rewrite ∘f-lemma f1 f2 e t = refl
∘f-lemma (fnew' x f1) f2 e t rewrite ∘f-lemma f1 f2 e t = refl

data Metaframe (Δ : TContext) (T : Type) (Eff : Effects) : Type → Effects → TContext → ℕ → Set where
  -- Metaframe splits evaluation context into frames separated by resets
  -- type parameters and indices work the same as in frame
  -- since Eff can (now) grow, Eff and Effects index
  -- might have different lenghts, and their difference (modulo debrujin indices, which difference we know thanks to ℕ index) represents list of effects handled by metaframe
  mfempty : Metaframe Δ T Eff T Eff Δ zero
  mfreset : ∀ {Δ' A B Eff' n l'}
    → (l : Label)  → Δ ⊢ ttv l' ⦂e → Δ ⨾ ∅ ⊢ label l ⦂ (L ttv l' at B / Eff) / nil
    → (e : RExpr) → (Δ ⨾ ∅ , A ⊢ e ⦂ B / Eff)
    → Metaframe Δ T (ttv l' ∷ Eff) A Eff' Δ' n
    → Metaframe Δ T Eff B Eff' Δ' n
  mframe : ∀ {A Eff' Δ' n B Eff'' Δ'' m}
    → Frame     Δ  A Eff B Eff' Δ' n
    → Metaframe Δ' T Eff' A Eff'' Δ'' m
    → Metaframe Δ T Eff B  Eff'' Δ''  (n + m)

mplug : ∀ {Δ Δ' T Eff A n E} → Metaframe Δ T Eff A E Δ' n → (e : RExpr) → Δ' ⨾ ∅ ⊢ e ⦂ T / E  →  Σ[ res ∈ RExpr ] (Δ ⨾ ∅ ⊢ res ⦂ A / Eff)
mplug mfempty e t = e ,, t
mplug (mfreset l lt ltt e₁ x₁ f) e t with (mplug f e t)
... | (res ,, tt) = reset₀ res e₁ (label l) ,, ⊢reset₀ lt ltt tt x₁
mplug (mframe x f) e t with (mplug f e t)
... | (res ,, tt) = plug x res tt

_∘m_ : ∀ {Δ Δ' Δ'' Eff Eff' Eff'' A B C n m} → Metaframe Δ B Eff A Eff' Δ' n → Metaframe Δ' C Eff' B Eff'' Δ''  m → Metaframe Δ C Eff A Eff'' Δ'' (n + m)
mfempty ∘m m2 = m2
mfreset l x x₁ e x₂ m1 ∘m m2 = mfreset l x x₁ e x₂ (m1 ∘m m2)
_∘m_ {n = n} {m = m'} (mframe {n = n1} {m = m''} x m1) m2 = math n1 m'' m' (mframe x (m1 ∘m m2))
  where math : ∀ {Δ Δ' A B Eff Eff' } → ∀ (n n1 m : ℕ)→ Metaframe Δ A Eff B Eff' Δ' (n + (n1 + m)) → Metaframe Δ A Eff B Eff' Δ' (n + n1 + m)
        math n n1 m mf rewrite Relation.Binary.PropositionalEquality.sym (Data.Nat.Properties.+-assoc n n1 m) = mf
_f∘m_ : ∀ {Δ Δ' Δ'' Eff Eff' Eff'' A B C n m} → Frame Δ B Eff A Eff' Δ' n → Metaframe Δ' C Eff' B Eff'' Δ''  m → Metaframe Δ C Eff A Eff'' Δ'' (n + m)
f f∘m mfempty = mframe f mfempty
f f∘m m@(mfreset l x x₁ e x₂ m') = mframe f m
_f∘m_ {n = n} f (mframe {n = n1} {m = m1} f' m) = assoc {n = n} {n1 = n1} {m = m1} (mframe (f ∘f f') m)
  where assoc : ∀ {Δ Δ' A B Eff Eff' n n1 m} → Metaframe Δ A Eff B Eff' Δ' (n + n1 + m) → Metaframe Δ A Eff B Eff' Δ' (n + (n1 + m))
        assoc {n = n} { n1 = n1} {m = m} mf rewrite Data.Nat.Properties.+-assoc n n1 m = mf

infix 2 _↦_
State = ℕ
-- evaluation state, represents next label to be assigned
data _↦_ : RExpr × State → RExpr × State → Set where
--only redexes
  
 ↦new : ∀ {e s}
  → new e ,′ s  ↦ new' s (e RExprSubst.[ label s ]) ,′ suc s

 β-lam-app : ∀ {e V s}
  → Value (lam e)
  → Value V
  → app (lam e) V ,′ s ↦ e RExprSubst.[ V ] ,′ s

 β-tlam-tapp : ∀ {k e T s}
   → Value (tlam k e)
   → tapp (tlam k e) T ,′ s ↦ e RExprSubst.e[t T ]  ,′ s

 β-reset₀-vl : ∀ {v e' en s}
   → Value v
   → reset₀ v en e' ,′ s ↦ en RExprSubst.[ v ] ,′ s

 Β-reset₀-k : ∀ {es en e' e s n Δ Δ' A T Eff Eff' t'} → { f : Metaframe Δ T Eff A Eff' Δ' n } → {t : Δ' ⨾ ∅ ⊢ (shift₀ e' es) ⦂ T / Eff'}
   → (Data.Product.proj₁ (mplug  f (shift₀ e' es) t)) ≡ e
   → reset₀ e en e' ,′ s ↦ es RExprSubst.[ lam (reset₀ (Data.Product.proj₁ (mplug f (var 0) t')) en e')  ]  ,′ s

infix 2 _-→_
data _-→_ : RExpr × State → RExpr × State → Set where
  -→frame : ∀ {e1 e1' e2 e2' s s' n Δ Δ' A T Eff Eff' t1 t2} → (f : Metaframe Δ T Eff A Eff' Δ' n)
    → e1' ,′ s ↦ e2' ,′ s'
    → Data.Product.proj₁ (mplug f e1' t1) ≡ e1
    → Data.Product.proj₁ (mplug f e2' t2) ≡ e2
    →  (e1 ,′ s) -→ (e2 ,′ s')

data Decompose : ∀ {Δ A Effs} → State → (e : RExpr) → (Δ ⨾ ∅ ⊢ e ⦂ A / Effs) → Set where
  de-simpl-redex : ∀ {e e2 s s' n Δ Δ' A T Eff Eff'} 
    → (f : Metaframe Δ T Eff A Eff' Δ' n)
    → (e ,′ s) -→ (e2 ,′ s')
    → (t : Δ ⨾ ∅ ⊢ e ⦂ A / Eff)
    → Decompose s e t
  de-shift : ∀ {s Δ Δ' T Eff A n Eff' es es' e l t} 
    → (f : Metaframe Δ T Eff A Eff' Δ' n)
    →  shift₀ (label l) es' ≡ es
    → Data.Product.proj₁ (mplug f es t) ≡ e
    --→ (e ,′ s) -→ (e2 ,′ s')
    → (t : Δ ⨾ ∅ ⊢ e ⦂ A / Eff)
    → (ts : Δ ⨾ ∅ ⊢ es ⦂ T / Eff')
    → Decompose s e t
  de-val : ∀ {Δ Eff A s e} → { t : Δ ⨾ ∅ ⊢ e ⦂ A / Eff}
    -> Value e
    → Decompose s e t
  

decompose : ∀ {A Δ Effs} → (s : State) → (e : RExpr) → (t : Δ ⨾ ∅ ⊢ e ⦂ A / Effs) → Decompose s e t
decompose s (lam e) (⊢lam t) = de-val vlam
decompose s e (⊢forall t) = de-val vLam
decompose s e (⊢label x x₁ x₂) = de-val vlab
--decompose s e (⊢new t) = de-simpl-redex mfempty (-→frame mfempty ↦new refl refl) (⊢new t)
decompose s e (⊢new {Δ = Δ} {A = A} {E = Eff} t) = de-simpl-redex mfempty ( -→frame {Δ = Δ} {A = A} {Eff = Eff} {t1 = ⊢new t} {t2 = {!{-todo lemma-}!}}  mfempty ↦new refl refl ) (⊢new t)
decompose s e (⊢weak x x₁ x₂ t) = {!!}
decompose s e (⊢app t t₁) = {!!}
decompose s e (⊢tapp x t) = {!!}
decompose s e (⊢new' t) = {!!}
decompose s e (⊢shift₀ x t t₁) = de-shift mfempty refl {!!} (⊢shift₀ x t t₁) {!!}
decompose s e (⊢reset₀ x t t₁ t₂) = {!!}

{-
data Progress (E : Expr) (S : State) : Set where
 step : ∀ {E' S'}
   → E ,′ S -→ E' ,′ S'
   → Progress E S
 done : Value E
   → Progress E S
data _⊢s_ : State → Expr → Set where
  -- represents proof that all labels are obtainable in current state
  -- that is they are smaller than state
  --TODO all constructors
progress : ∀ {E A  S }→ {S ⊢s E}
  → ∅ , ∅ ⊢ E ⦂ A / nil
  → Progress E S
progress  (⊢var {x = x₁ } x _) = {!!}
progress (⊢lam x) = done vlam
progress (⊢app x x₁) = {!!}
progress (⊢forall x) = done vLam
progress (⊢new x) = {!!}
progress (⊢reset₀ _ x x₁ x₂) = {!!}

progress (⊢label _ _) = done vlab

-}
