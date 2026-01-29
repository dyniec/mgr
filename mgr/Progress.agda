module mgr.Progress where


open import mgr.Types hiding (Rename;Subst;ext;rename;exts;subst;subst-zero;_[_])

open import Data.Nat
open import Data.List using (List;_∷_) renaming ([] to nil)
open import Relation.Binary.PropositionalEquality using (_≡_;refl;_≢_)
open import Data.Product using (_×_;_,′_)

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
rename ρ (label n) = label n

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
subst ρ (label n) = label n

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



data Value : Expr -> Set where
    vlam : ∀ { e } → Value (lam e)
    vLam : ∀ { k e } → Value (tlam k e)
    llab : ∀ { n } → Value (label n)
--    vvar : ∀ {n} → Value (var n)
--    vshift : ∀ { e e' } -> Value (shift₀ e' e)

data Frame  : Set where
  fempty : Frame
  fapp₁ : Frame → ( e : Expr ) → Frame
  fapp₂ : (e : Expr) →  (v : Value e) -> Frame  -> Frame
  freset₀ : Frame → (en : Expr) → (e' : Expr) -> Frame

{- typed frames
data Frame (Δ : TContext) (Γ : Context) (T : Type) (Eff : Effects) : Type → Effects →   Set where
  fempty : Frame Δ Γ T Eff T Eff
  fapp₁ : ∀ {A B E } → {  e : Expr } → { Δ , Γ ⊢ e ⦂ A / E  } → Frame Δ Γ T Eff (A - E > B) E → Frame Δ Γ T Eff B E
  fapp₂ : ∀ {A B E} → {e : Expr} → { v : Value e} → { Δ , Γ ⊢ e ⦂ ( A - E > B) / E } -> Frame Δ Γ T Eff A E  -> Frame Δ Γ T Eff B E
  freset₀ :
-}

plug : Frame → Expr → Expr
plug fempty e = e
plug (fapp₁ f e₁) e =  app (plug f e) e₁
plug (fapp₂ e₁ v f) e =  app e₁ (plug f e)
plug (freset₀ f en e') e =  reset₀ (plug f e) en e'

infix 2 _↦_
State = ℕ
data _↦_ : Expr × State → Expr × State → Set where
--only redexes
  
 ↦new : ∀ {e s}
  → new e ,′ s  ↦ e [ label s ] ,′ suc s

 β-lam-app : ∀ {e V s}
  → Value (lam e)
  → Value V
  → app (lam e) V ,′ s ↦ e [ V ] ,′ s

 β-tlam-tapp : ∀ {k e T s}
   → Value (tlam k e)
   → tapp (tlam k e) T ,′ s ↦ e e[t T ]  ,′ s


 β-reset₀-vl : ∀ {v e' en s}
   → Value v
   → reset₀ v en e' ,′ s ↦ en [ v ] ,′ s

 Β-reset₀-k : ∀ {f es en e' e s}
   → (plug f (shift₀ e' es)) ≡ e
   → reset₀ e en e' ,′ s ↦ es [ lam (reset₀ (plug f (var 0)) en e')  ]  ,′ s
infix 2 _-→_
data _-→_ : Expr × State → Expr × State → Set where
  -→frame : ∀ {f e1 e1' e2 e2' s s' }
    → e1' ,′ s ↦ e2' ,′ s'
    → plug f e1' ≡ e1
    → plug f e2' ≡ e2
    →  (e1 ,′ s) -→ (e2 ,′ s')

{-
data Progress (E : Expr) : Set where
 step : ∀ {E'}
   → E -→ E'
   → Progress E
 done : Value E
   → Progress E

progress : ∀ {Δ Γ E A Eff}
  → ∅ , ∅ ⊢ E ⦂ A / nil
  → Progress E
progress  (⊢var {x = x₁ } x _) = {!!}
progress (⊢weak _ x x₁ x₂) with nil<⦂⊥ x₁
... | refl = progress x₂
progress (⊢lam x) = done vlam
progress (⊢app x x₁) with progress x 
... | step (x1-→x2) = step  (ξ-app₁ x1-→x2)
... | done vlam with progress x₁
...     | step (y1-→y2) = step (ξ-app₂ vlam y1-→y2)
...     | done v2 = step ( (β-lam-app vlam v2) )

progress (⊢forall x) = done vLam
--progress (⊢new x) with progress x
--... | step (x1-→x2) = step (ξ-new x1-→x2)
--... | done v = step (β-new v)
progress (⊢reset₀ _ x x₁ x₂) with progress x₁
... | step (x1-→x2) = step (ξ-reset₀ x1-→x2)
... | done v = step (β-reset₀-vl  v)

progress (⊢shift₀ x x₁) = {! progress x!}
-}
