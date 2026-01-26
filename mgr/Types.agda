module mgr.Types where

open import Data.Nat
open import Data.List using (List;_∷_;map) renaming ([] to nil)


data Kind : Set where
    T : Kind
    E : Kind
 
Id : Set
Id = ℕ

Effect = ℕ

Effects = List Effect

data Type : Set where
    ttv : ℕ → Type
    _-_>_ : Type → Effects → Type → Type
    forallt : Kind → Type →  Type
    L_at_/_ : ℕ → Type → Effects → Type

data Expr : Set where
    var : ℕ → Expr
    lam : Expr → Expr
    app : Expr → Expr → Expr
    tlam : Kind → Expr → Expr
    tapp : Expr -> Type -> Expr
    new : Expr → Expr
    shift₀ : Expr → Expr → Expr
    reset₀ : Expr → Expr → Expr → Expr

Rename = ℕ → ℕ
Subst = ℕ → Type
ext : Rename → Rename
ext ρ zero = zero
ext ρ (suc x) = suc (ρ x)

rename : Rename → (Type → Type)
rename ρ (ttv x) = ttv (ρ x)
rename ρ (x - effs > x₁) = rename ρ x -  map ρ effs > rename ρ x₁
rename ρ (forallt k x) = forallt k (rename (ext ρ) x)
rename ρ (L x at x₁ / effs) =  L   ρ x at  rename ρ x₁ /   effs

exts : Subst → Subst
exts ρ zero = ttv zero
exts ρ (suc x) = rename suc (ρ x)
subst : Subst → ( Type → Type)
--not really ok because type vars in effects and labels are not replaced correctly
-- they would need to be proper Type(likes)
subst ρ (ttv x) = ρ x
subst ρ (t - x > t₁) =  subst ρ t -  x > subst ρ t₁
subst ρ (forallt k t) = forallt k (subst (exts ρ) t)
subst ρ (L x at t / x₁) = L x at subst ρ t  /  x₁ 

subst-zero : Type → Subst
subst-zero t zero = t
subst-zero t (suc x) = ttv x

infixl 5  _,_
data Context : Set where
    ∅ : Context
    _,_ : Context → Type → Context

data TContext : Set where
    ∅ : TContext
    _,_ : TContext → Kind → TContext


data _⊢_<⦂_ : TContext → Effects → Effects → Set where
  Z : ∀ {Δ E}
    → Δ ⊢ nil <⦂ E 
  S : ∀ {Δ e E1 E2 }
    → Δ ⊢ E1 <⦂ E2
    → Δ ⊢ (e ∷ E1) <⦂ (e ∷ E2)

data _⊢_<t⦂_ : TContext → Type → Type → Set where

    <⦂refl : ∀ {Δ A} → Δ ⊢ A <t⦂ A

    <⦂→ : ∀ {Δ A1 A2 B1 B2 E1 E2} 
        → Δ ⊢ E1 <⦂ E2
        → Δ ⊢ A1 <t⦂ A2
        → Δ ⊢ B1 <t⦂ B2 
        → Δ ⊢ (A2 - E1 > B1) <t⦂ (A1 - E2 > B2)

infix  4  _∋_⦂_

data _∋_⦂_ : Context → Id → Type → Set where
  Z : ∀ {Γ  A}
    → (Γ , A)  ∋ zero ⦂ A

  S : ∀ {Γ x y A}
    → Γ ∋ x ⦂ A
    → (Γ , y)  ∋ (suc x) ⦂ A

-- data _∋_ : Context  → Type → Set where
--   Z : ∀ {Γ  A}
--     → (Γ , A)  ∋  A

--   S : ∀ {Γ x y A}
--     → Γ ∋ x ⦂ A
--     → (Γ , y)  ∋  A

data _∋t_⦂_ : TContext → Id → Kind → Set where
  Z : ∀ {Δ k}
    → (Δ , k)  ∋t zero ⦂ k

  S : ∀ {Δ x y k}
    → Δ ∋t x ⦂ k
    → (Δ , y)  ∋t (suc x) ⦂ k

data _,_⊢_⦂_/_ : TContext → Context → Expr → Type → Effects → Set where

    ⊢var : ∀ {Γ Δ x A E}
        → Γ ∋ x ⦂ A
        → Δ , Γ ⊢ var x ⦂ A / E
    
--    ⊢weak : ∀ {Γ Δ e A A' E E'}
--        → Δ ⊢  A <t⦂ A'
--        → Δ ⊢  E <⦂ E'
--        → Δ , Γ ⊢ e ⦂ A / E
--        → Δ , Γ ⊢ e ⦂ A' / E'
    
    ⊢lam : ∀ {Γ Δ e A B E}
        → Δ , (Γ , A) ⊢ e ⦂ B / E
        → Δ , Γ ⊢ lam e ⦂ A - E > B / E

    ⊢app : ∀ {Γ Δ e1 e2 A B E}
        → Δ , Γ ⊢ e1 ⦂ A - E > B / E
        → Δ , Γ ⊢ e2 ⦂ A / E
        → Δ , Γ ⊢ app e1 e2  ⦂ B / E 

    ⊢forall : ∀ {Γ Δ e k A}
        → (Δ , k) , Γ  ⊢ e ⦂ A / nil
        → Δ , Γ ⊢ tlam k e ⦂ forallt k A / nil

    {- ⊢tapp : ∀ {Γ Δ e k A T}
      → -- T is well formed in Δ
      → Δ , Γ ⊢ e ⦂ forall k A /E
      → (Δ , k) , Γ ⊢ e ⦂ A[T] / E[T]
     -}

    ⊢new : ∀ {Γ Δ e  A A1 E E1}
        → (Δ , Kind.E) , (Γ , (L zero at A1 / E1))  ⊢ e ⦂ A / E
        → Δ , Γ ⊢ new e ⦂ A / E

    ⊢shift₀ : ∀ {Γ Δ e e' A A' n E'}
        → Δ , Γ ⊢ e' ⦂ (L n at  A' / E') / nil 
        → Δ , (Γ , A - E' > A' )  ⊢ e ⦂ A' / E'
        → Δ , Γ ⊢ shift₀ e' e ⦂ A / (n ∷ nil)

    ⊢reset₀ : ∀ {Γ Δ e e' en A A' n E'}
        → Δ , Γ ⊢ e' ⦂ (L n at  A' / E') / nil 
        → Δ , Γ   ⊢ e ⦂ A / (n ∷ E')
        → Δ , (Γ , A)   ⊢ en ⦂ A' /  E'
        → Δ , Γ   ⊢ reset₀ e en e' ⦂ A' / E'
        
--    ⊢label : ∀ {Γ Δ n n' A E}
--      → Γ , Δ ⊢ label n ⦂ (L n' at A / E) / nil 
