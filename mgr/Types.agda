module mgr.Types where

open import Data.Nat
open import Data.List using (List;_∷_;map) renaming ([] to nil)
open import Relation.Binary.PropositionalEquality using (_≡_;refl;_≢_)


data Kind : Set where
    T : Kind
    E : Kind 
Id : Set
Id = ℕ

data Type : Set
Effects : Set
data Type  where
    ttv : Id → Type
    _-_>_ : Type → Effects → Type → Type
    forallt : Kind → Type →  Type
    L_at_/_ : Type → Type → Effects → Type
Effects = List Type

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
rename' : Rename → (Effects → Effects)
rename ρ (ttv x) = ttv (ρ x)
rename ρ (x - effs > x₁) = rename ρ x -  rename' ρ effs > rename ρ x₁
rename ρ (forallt k x) = forallt k (rename (ext ρ) x)
rename ρ (L x at x₁ / effs) =  L  rename ρ x at  rename ρ x₁ / rename' ρ effs
-- doing mutal recursion because I couldn't convice termination checker that calling map is productive
rename' ρ nil = nil
rename' ρ (x ∷ xs) = rename ρ x ∷ rename' ρ xs

exts : Subst → Subst
exts ρ zero = ttv zero
exts ρ (suc x) = rename suc (ρ x)

subst : Subst → ( Type → Type)
subst' : Subst → ( Effects → Effects)
subst ρ (ttv x) = ρ x
subst ρ (t - x > t₁) =  subst ρ t - subst' ρ x > subst ρ t₁
subst ρ (forallt k t) = forallt k (subst (exts ρ) t)
subst ρ (L x at t / x₁) = L subst ρ x at subst ρ t / subst' ρ x₁
subst' ρ nil = nil
subst' ρ (x ∷ x₁) = subst ρ x ∷ subst' ρ x₁

subst-zero : Type → Subst
subst-zero t zero = t
subst-zero t (suc x) = ttv x

subst-in-expr : Subst → Expr → Expr
subst-in-expr ρ (tlam k e) = tlam k (subst-in-expr (exts ρ) e)
subst-in-expr ρ (new e) =  new (subst-in-expr (exts ρ) e)
subst-in-expr ρ (tapp e t) = tapp e (subst ρ t)
subst-in-expr ρ (var x) = var x
subst-in-expr ρ (lam e) =  lam (subst-in-expr ρ e)
subst-in-expr ρ (app e e₁) =  app (subst-in-expr ρ e) (subst-in-expr ρ e₁)
subst-in-expr ρ (shift₀ e e₁) =  shift₀ (subst-in-expr ρ e) (subst-in-expr ρ e₁)
subst-in-expr ρ (reset₀ e e₁ e₂) = reset₀ (subst-in-expr ρ e) (subst-in-expr ρ e₁) (subst-in-expr ρ e₂)

infix 8 _[_]
_[_] : Type → Type → Type
M [ N ] = subst (subst-zero N) M
_e[t_] : Expr → Type → Expr
M e[t t ] = subst-in-expr (subst-zero t) M
_effs[t_] : Effects → Type → Effects
nil effs[t t ] = nil
(x ∷ xs) effs[t t ] = (x [ t ])∷ xs effs[t t ]

infixl 5  _,_
data Context : Set where
    ∅ : Context
    _,_ : Context → Type → Context

data TContext : Set where
    ∅ : TContext
    _,_ : TContext → Kind → TContext

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
    → (Δ , k) ⊢ t ⦂t 
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
    → Δ ⊢ nil <⦂ E 
  S : ∀ {Δ e E1 E2 }
    → Δ ⊢ E1 <⦂ E2
    → Δ ⊢ e ⦂e
    → Δ ⊢ (e ∷ E1) <⦂ (e ∷ E2)

nil<⦂⊥ : ∀ {Δ E } → Δ ⊢ E <⦂ nil → E ≡ nil
nil<⦂⊥ (Z _) = refl

data _⊢_<t⦂_ : TContext → Type → Type → Set where

    <⦂refl : ∀ {Δ A} → Δ ⊢ A <t⦂ A

    <⦂→ : ∀ {Δ A1 A2 B1 B2 E1 E2} 
        → Δ ⊢ E1 <⦂ E2
        → Δ ⊢ A1 <t⦂ A2
        → Δ ⊢ B1 <t⦂ B2 
        → Δ ⊢ (A2 - E1 > B1) <t⦂ (A1 - E2 > B2)

    <⦂forall : ∀ {Δ A1 A2 k}
        → (Δ , k) ⊢ A1 <t⦂ A2
        → Δ ⊢ forallt k A1 <t⦂ forallt k A2


data _,_⊢_⦂_/_ : TContext → Context → Expr → Type → Effects → Set where

    ⊢var : ∀ {Γ Δ x A E}
        → Γ ∋ x ⦂ A
        → Δ ⊢ E ⦂effs
        → Δ , Γ ⊢ var x ⦂ A / E
    
    ⊢weak : ∀ {Γ Δ e A A' E E'}
        → Δ ⊢ E' ⦂effs
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

    ⊢forall : ∀ {Γ Δ e k A E}
        → (Δ , k) , Γ  ⊢ e ⦂ rename suc A / map (rename suc) E
        → Δ , Γ ⊢ tlam k e ⦂ forallt k A / E

    ⊢tapp : ∀ {Γ Δ e k A T E}
        → Δ ⊢ T ⦂t
        → Δ , Γ ⊢ e ⦂ forallt k A / E
        → (Δ , k) , Γ ⊢ tapp e T ⦂ A [ T ] / (E effs[t T ])

    ⊢new : ∀ {Γ Δ e  A A1 E E1}
        → (Δ , Kind.E) , (Γ , (L ttv zero at A1 / E1))  ⊢ e ⦂ rename suc A / map (rename suc) E
        → Δ , Γ ⊢ new e ⦂ A / E

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
        
--    ⊢label : ∀ {Γ Δ n n' A E}
--      → Γ , Δ ⊢ label n ⦂ (L n' at A / E) / nil 
