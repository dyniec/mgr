module mgr.Syntax where

open import Data.Nat

data Kind : Set where
    T : Kind
    E : Kind
-- uhh both variables and type variables are deBruijn indexed
data TypeVar : Set where
    Tv : Kind -> TypeVar

data Effect : Set where
    ε : Effect
    _·_ : Effect -> Effect -> Effect
    etv : ℕ -> Effect

data Type : Set where
    ttv : ℕ -> Type
    _-_>_ : Type -> Effect -> Type -> Type
    forallt : Kind ->  Type
    L_/_ : Type -> Effect -> Type

data Context : Set where
    ∅ : Context
    _,_ : Context -> Type -> Context

data TContext : Set where
    ∅ : TContext
    _,_ : TContext -> Kind -> TContext

data Expr : Set where
    var : ℕ -> Expr
    lam : Expr -> Expr
    app : Expr -> Expr -> Expr
    tlam : Kind ->  Expr
    tapp : Expr -> Type -> Expr
    new : Expr -> Expr
    shift₀ : Expr -> Expr -> Expr
    reset₀ : Expr -> Expr -> Expr -> Expr
