module mgr.Progress where


open import mgr.Types hiding (Rename;Subst;ext;rename;exts;subst;subst-zero)

open import Data.Nat
open import Data.List using (List;_∷_) renaming ([] to nil)
open import Relation.Binary.PropositionalEquality using (_≡_;refl;_≢_)

Rename = ℕ → ℕ

Subst = ℕ → Expr

ext : Rename → Rename 
ext ρ zero    = zero
ext ρ (suc x) = suc (ρ x)

rename : Rename → (Expr → Expr)
rename ρ (var x₁) = var (ρ x₁)
rename ρ (lam x₁) = lam (rename (ext ρ) x₁)
rename ρ (app x₁ x₂) = app (rename ρ x₁) (rename ρ x₂)
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



data Value : Expr -> Set where
    vlam : ∀ { e } → Value (lam e)
    vLam : ∀ { k e } → Value (tlam k e)
--    llab : ∀ { n } → Value (label n)  
--    vvar : ∀ {n} → Value (var n)
--    vshift : ∀ { e e' } -> Value (shift₀ e' e)

data Frame  : Set where
  fempty : Frame
  fapp₁ : Frame → ( e : Expr ) → Frame
  fapp₂ : (e : Expr) →  (v : Value e) -> Frame  -> Frame
  fnew :   Frame → Frame
  freset₀ : Frame → (en : Expr) → (e' : Expr) -> Frame

{- typed frames
data Frame (Δ : TContext) (Γ : Context) (T : Type) (Eff : Effects) : Type → Effects →   Set where
  fempty : Frame Δ Γ T Eff T Eff
  fapp₁ : ∀ {A B E } → {  e : Expr } → { Δ , Γ ⊢ e ⦂ A / E  } → Frame Δ Γ T Eff (A - E > B) E → Frame Δ Γ T Eff B E
  fapp₂ : ∀ {A B E} → {e : Expr} → { v : Value e} → { Δ , Γ ⊢ e ⦂ ( A - E > B) / E } -> Frame Δ Γ T Eff A E  -> Frame Δ Γ T Eff B E
  fnew : ∀ {A E} →  Frame Δ Γ T Eff A E → Frame Δ Γ T Eff A E
  freset₀ :
-}

plug : Frame → Expr → Expr
plug fempty e = e
plug (fapp₁ f e₁) e =  app (plug f e) e₁
plug (fapp₂ e₁ v f) e =  app e₁ (plug f e)
plug (fnew f) e =  new (plug f e)
plug (freset₀ f en e') e =  reset₀ (plug f e) en e'

infix 2 _-→_

data _-→_ : Expr -> Expr → Set where
  
 ξ-app₁ : ∀ {e e' e2}
  → e -→ e'
  → app e e2 -→ app e' e2
  
 ξ-app₂ : ∀ {V e2 e2'}
  → Value V
  → e2 -→ e2'
  → app V e2 -→ app V e2'

 ξ-new : ∀ {e e'}
  → e -→ e'
  → new e -→ new e'

 β-lam-app : ∀ {e V}
  → Value (lam e)
  → Value V
  → app (lam e) V -→ e [ V ]

 β-new : ∀ {V}
  → Value V
  → new V -→ V
  
 ξ-reset₀ : ∀ {e e' e'' en}
  → e -→ e'
  → reset₀ e en e'' -→ reset₀ e' en e''

 β-reset₀-k : ∀ { e e' en}
   → reset₀ (shift₀ e' e) en e' -→ en [ e ]
  
 β-reset₀-vl : ∀ {v e' en}
   → Value v
   → reset₀ v en e' -→ en [ v ]
 

data Progress (E : Expr) : Set where
 step : ∀ {E'}
   → E -→ E'
   → Progress E
 done : Value E
   → Progress E

progress : ∀ {Δ Γ E A Eff}
--  → Δ , Γ ⊢ E ⦂ A / Eff
-- I was hoping to prove something like this
  → ∅ , ∅ ⊢ E ⦂ A / nil
-- but ⊢new requires larger Δ and Γ
-- and ⊢shift₀ requires larger Eff
  → Progress E
progress  (⊢var {x = x₁ } x) = {!!}
--progress (⊢weak x x₁ x₂)  = progress x₂
progress (⊢lam x) = done vlam
progress (⊢app x x₁) with progress x 
... | step (x1-→x2) = step  (ξ-app₁ x1-→x2)
... | done vlam with progress x₁
...     | step (y1-→y2) = step (ξ-app₂ vlam y1-→y2)
...     | done v2 = step ( (β-lam-app vlam v2) )

progress (⊢forall x) = done vLam
progress (⊢new x) with progress x
... | step (x1-→x2) = step (ξ-new x1-→x2)
... | done v = step (β-new v)
progress (⊢reset₀ x x₁ x₂) with progress x₁
... | step (x1-→x2) = step (ξ-reset₀ x1-→x2)
... | done v = step (β-reset₀-vl  v)

progress (⊢shift₀ x x₁) = {! progress x!}
