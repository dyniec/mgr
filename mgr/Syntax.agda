module mgr.Syntax where

open import Data.Nat
open import Data.List 

data Kind : Set where
    T : Kind
    E : Kind
-- uhh both variables and type variables are deBruijn indexed
Id : Set
Id = ℕ

Effect = ℕ

Effects = List Effect

data Type : Set where
    ttv : ℕ → Type
    _-_>_ : Type → Effects → Type → Type
    forallt : Kind → Type →  Type
    L_at_/_ : ℕ → Type → Effects → Type

infixl 5  _,_
data Context : Set where
    ∅ : Context
    _,_ : Context → Type → Context

data TContext : Set where
    ∅ : TContext
    _,_ : TContext → Kind → TContext

data Expr : Set where
    var : ℕ → Expr
    lam : Expr → Expr
    app : Expr → Expr → Expr
    new : Expr → Expr
    shift₀ : Expr → Expr → Expr
    reset₀ : Expr → Expr → Expr → Expr


data _⊢_<⦂_ : TContext → Effects → Effects → Set where
  Z : ∀ {Δ E}
    → Δ ⊢ [] <⦂ E 
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
    
    ⊢weak : ∀ {Γ Δ e A A' E E'}
        → Δ ⊢  A <t⦂ A'
        → Δ ⊢  E <⦂ E'
        → Δ , Γ ⊢ e ⦂ A / E
        → Δ , Γ ⊢ e ⦂ A' / E'
    
    ⊢lam : ∀ {Γ Δ e A B E}
        → Δ , (Γ , A) ⊢ e ⦂ B / E
        → Δ , Γ ⊢ lam e ⦂ A - E > B / E

    ⊢app : ∀ {Γ Δ e1 e2 A B E}
        → Δ , Γ ⊢ e1 ⦂ A - E > B / E
        → Δ , Γ ⊢ e2 ⦂ A / E
        → Δ , Γ ⊢ app e1 e2  ⦂ B / E 

    ⊢forall : ∀ {Γ Δ e k A}
        → (Δ , k) , Γ  ⊢ e ⦂ A / []
        → Δ , Γ ⊢ e ⦂ forallt k A / []
        

    ⊢new : ∀ {Γ Δ e  A A1 E E1}
        → (Δ , Kind.E) , (Γ , (L zero at A1 / E1))  ⊢ e ⦂ A / E
        → Δ , Γ ⊢ new e ⦂ A / E

    ⊢shift₀ : ∀ {Γ Δ e e' A A' n E'}
        → Δ , Γ ⊢ e' ⦂ (L n at  A' / E') / [] -- ??
        → Δ , (Γ , A - E' > A' )  ⊢ e ⦂ A' / E'
        → Δ , Γ ⊢ shift₀ e' e ⦂ A / (n ∷ [])

    ⊢reset₀ : ∀ {Γ Δ e e' en A A' n E'}
        → Δ , Γ ⊢ e' ⦂ (L n at  A' / E') / [] 
        → Δ , Γ   ⊢ e ⦂ A / (n ∷ E')
        → Δ , (Γ , A)   ⊢ en ⦂ A' /  E'
        → Δ , Γ   ⊢ reset₀ e en e' ⦂ A' / E'



data Value : Expr -> Set where
    vlam : ∀ {e } → Value (lam e)

ext : ∀ {Γ Γ'}
  → (∀ {A n} →       Γ ∋ n ⦂ A →     Γ' ∋ n ⦂ A)
  → (∀ {A B n} → Γ , B ∋ n ⦂ A → Γ' , B ∋ n ⦂ A)
ext x Z = Z
ext x (S x₁) = S (x x₁)

rename : ∀ {Γ Δ E Γ'}
  → (∀ {A n} →  Γ ∋ n ⦂ A → Γ' ∋ n ⦂ A)
  → (∀ {A e } → Δ , Γ ⊢ e ⦂ A / E → Δ , Γ' ⊢ e ⦂ A / E)

rename x (⊢var x₁) = ⊢var (x x₁)
rename x (⊢weak x₁ x₂ x₃) = ⊢weak x₁ x₂ (rename x x₃)
rename x (⊢lam x₁) = ⊢lam (rename (ext x) x₁)
rename x (⊢app x₁ x₂) = ⊢app (rename x x₁) (rename x x₂)
rename x (⊢forall x₁) = ⊢forall (rename x x₁)
rename x (⊢new x₁) = ⊢new (rename (ext x) x₁)
rename x (⊢shift₀ x₁ x₂) = ⊢shift₀ (rename x x₁) (rename ((ext x)) x₂)
rename x (⊢reset₀ x₁ x₂ x₃) = ⊢reset₀ (rename x x₁) (rename x x₂) (rename ((ext x)) x₃)

