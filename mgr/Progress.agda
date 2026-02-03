module mgr.Progress where


open import mgr.Types renaming (_,_⊢_⦂_/_ to _,e_⊢_⦂_/_)

open import Data.Nat
open import Data.List using (List;_∷_;map) renaming ([] to nil)
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
{- typed frames
data Frame (Δ : TContext) (Γ : Context) (T : Type) (Eff : Effects) : Type → Effects →   Set where
  fempty : Frame Δ Γ T Eff T Eff
  fapp₁ : ∀ {A B E } → {  e : Expr } → { Δ , Γ ⊢ e ⦂ A / E  } → Frame Δ Γ T Eff (A - E > B) E → Frame Δ Γ T Eff B E
  fapp₂ : ∀ {A B E} → {e : Expr} → { v : Value e} → { Δ , Γ ⊢ e ⦂ ( A - E > B) / E } -> Frame Δ Γ T Eff A E  -> Frame Δ Γ T Eff B E
  freset₀ :
-}

module Runtime where
    data RExpr : Set where --runtime version
        var : ℕ → RExpr
        lam : RExpr → RExpr
        app : RExpr → RExpr → RExpr
        tlam : Kind → RExpr → RExpr
        tapp : RExpr -> Type -> RExpr
        new : RExpr → RExpr
        new' : ℕ → RExpr → RExpr -- label is already assigned, keeping shape of new to prove preservation
        shift₀ : RExpr → RExpr → RExpr
        reset₀ : RExpr → RExpr → RExpr → RExpr
        label : ℕ → RExpr -- label for effects

    
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
    data _,_⊢_⦂_/_ : TContext → Context → RExpr → Type → Effects → Set where

        ⊢var : ∀ {Γ Δ x A E}
            → Γ ∋ x ⦂ A
            → Δ ⊢ E ⦂effs
            → Δ , Γ ⊢ var x ⦂ A / E


        ⊢lam : ∀ {Γ Δ e A B E}
            → Δ , (Γ , A) ⊢ e ⦂ B / E
            → Δ , Γ ⊢ lam e ⦂ A - E > B / E

        ⊢app : ∀ {Γ Δ e1 e2 A1 A2 B  A' B' E1 E2 E'}
            → Δ , Γ ⊢ e1 ⦂ A1 - E1 > B / E1
            → Δ , Γ ⊢ e2 ⦂ A2 / E2
            → Δ ⊢ E' ⦂effs
            → Δ ⊢ (A1 - E1 > B) <t⦂ (A' - E' > B')
            → Δ ⊢ E1 <⦂ E' -- implied implicitly by above
            → Δ ⊢ A2 <t⦂ A'
            → Δ ⊢ E2 <⦂ E'
            → Δ , Γ ⊢ app e1 e2  ⦂ B' / E' 

        ⊢forall : ∀ {Γ Δ e k A E}
            → (Δ , k) , Γ  ⊢ e ⦂ TypeSubst.rename suc A / map (TypeSubst.rename suc) E
            → Δ , Γ ⊢ tlam k e ⦂ forallt k A / E

        ⊢tapp : ∀ {Γ Δ e k A T E}
            → Δ ⊢ T ⦂t
            → Δ , Γ ⊢ e ⦂ forallt k A / E
            → (Δ , k) , Γ ⊢ tapp e T ⦂ A TypeSubst.[ T ] / (E TypeSubst.effs[t T ])

        ⊢new : ∀ {Γ Δ e  A A1 E E1}
            → (Δ , Kind.E) , (Γ , (L ttv zero at A1 / E1))  ⊢ e ⦂ TypeSubst.rename suc A / map (TypeSubst.rename suc) E
            → Δ , Γ ⊢ new e ⦂ A / E
            
        ⊢new' : ∀ {Γ Δ e l A A1 E E1}
            → (Δ , Kind.E) , (Γ , (L ttv zero at A1 / E1))  ⊢ e ⦂ TypeSubst.rename suc A / map (TypeSubst.rename suc) E 
            → Δ , Γ ⊢ new' l e ⦂ A / E

        ⊢shift₀ : ∀ {Γ Δ e e' A A' n E'}
            → Δ ⊢ ttv n ⦂e
            → Δ , Γ ⊢ e' ⦂ (L ttv n at  A' / E') / nil 
            → Δ , (Γ , A - E' > A' )  ⊢ e ⦂ A' / E'
            → Δ , Γ ⊢ shift₀ e' e ⦂ A / (ttv n ∷ nil)

        ⊢reset₀ : ∀ {Γ Δ e e' en A A' n E'}
            → Δ ⊢ ttv n ⦂e
            → Δ , Γ ⊢ e' ⦂ (L ttv n at  A' / E') / nil 
            → Δ , Γ   ⊢ e ⦂ A / (ttv n ∷ E')
            → Δ , (Γ , A)   ⊢ en ⦂ A' /  E'
            → Δ , Γ   ⊢ reset₀ e en e' ⦂ A' / E'

        ⊢label : ∀ {Γ Δ n l A E}
            → Δ ⊢ A ⦂t
            → Δ ⊢ E ⦂effs
            → Δ , Γ ⊢ label l ⦂ (L n at A / E) / nil

    runtime : Expr → RExpr
    runtime (var x) = var x
    runtime (lam x) = lam (runtime x)
    runtime (app x x₁) = app (runtime x) (runtime x₁)
    runtime (tlam x x₁) =  tlam x (runtime x₁)
    runtime (tapp x x₁) = tapp (runtime x) x₁
    runtime (new x) = new (runtime x)
    runtime (shift₀ x x₁) =  shift₀ (runtime x) (runtime x₁)
    runtime (reset₀ x x₁ x₂) = reset₀ (runtime x) (runtime x₁) (runtime x₂)

    runtime-types : ∀ {Δ Γ e T E}
      → Δ ,e Γ ⊢ e ⦂ T / E → (Δ , Γ ⊢ (runtime e) ⦂ T / E)
    runtime-types (⊢var x x₁) = ⊢var x x₁
    runtime-types (⊢lam x) = ⊢lam (runtime-types x)
    runtime-types (⊢app x x₁ x₂ x₃ x₄ x₅ x₆) = ⊢app (runtime-types x) (runtime-types x₁) x₂ x₃ x₄ x₅ x₆
    runtime-types (⊢forall x) = ⊢forall (runtime-types x)
    runtime-types (⊢tapp x x₁) = ⊢tapp x (runtime-types x₁)
    runtime-types (⊢new x) = ⊢new (runtime-types x)
    runtime-types (⊢shift₀ x x₁ x₂) = ⊢shift₀ x (runtime-types x₁) (runtime-types x₂)
    runtime-types (⊢reset₀ x x₁ x₂ x₃) = ⊢reset₀ x (runtime-types x₁) (runtime-types x₂) (runtime-types x₃)
        

open Runtime

data Value : RExpr -> Set where
    vlam : ∀ { e } → Value (lam e)
    vLam : ∀ { k e } → Value (tlam k e)
    vlab : ∀ { n } → Value (label n)

data Frame  : Set where
  fempty : Frame
  fapp₁ : Frame → ( e : RExpr ) → Frame
  fapp₂ : (e : RExpr) →  (v : Value e) -> Frame  -> Frame
  freset₀ : Frame → (en : RExpr) → (e' : RExpr) -> Frame
  fnew' : ℕ → Frame → Frame
plug : Frame → RExpr → RExpr
plug fempty e = e
plug (fapp₁ f e₁) e =  app (plug f e) e₁
plug (fapp₂ e₁ v f) e =  app e₁ (plug f e)
plug (freset₀ f en e') e =  reset₀ (plug f e) en e'
plug (fnew' l f) e = new' l (plug f e)

_∘f_ : Frame → Frame → Frame
fempty ∘f F = F
fapp₁ N e ∘f F = fapp₁ (N ∘f F) e 
fapp₂ e v N ∘f F = fapp₂ e v (N ∘f F)
freset₀ N en e' ∘f F = freset₀ (N ∘f F) en e'
fnew' x N ∘f F = fnew' x (N ∘f F)

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

 Β-reset₀-k : ∀ {f es en e' e s}
   → (plug f (shift₀ e' es)) ≡ e
   → reset₀ e en e' ,′ s ↦ es RExprSubst.[ lam (reset₀ (plug f (var 0)) en e')  ]  ,′ s
infix 2 _-→_
data _-→_ : RExpr × State → RExpr × State → Set where
  -→frame : ∀ {f e1 e1' e2 e2' s s' }
    → e1' ,′ s ↦ e2' ,′ s'
    → plug f e1' ≡ e1
    → plug f e2' ≡ e2
    →  (e1 ,′ s) -→ (e2 ,′ s')
{-
decompose : ∀ {A Effs} → (e : Expr) → (∅ , ∅ ⊢ e ⦂ A / Effs) → Σ[ f ∈ Frame ]  ( Σ[ e' ∈ Expr ] (plug f e' ≡ e))
decompose (lam e) (⊢lam x) =    fempty ,,  (lam e) ,, refl
decompose (app e e₁) (⊢app x x₁) = {!!}
decompose (tlam x e) (⊢forall x₁) = fempty ,, (tlam x e) ,, refl
decompose (new e) (⊢new x) = fempty ,, (new e) ,, refl
decompose (shift₀ e e₁) (⊢shift₀ x x₁ x₂) = fempty ,, (shift₀ e e₁) ,, refl
decompose (reset₀ e e₁ e₂) (⊢reset₀ x x₁ x₂ x₃) = {!!}
decompose (label x) (⊢label x₁ x₂) = fempty ,, (label x) ,, refl

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
