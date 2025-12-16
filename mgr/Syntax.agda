module mgr.Syntax where

open import Data.Nat

data Kind : Set where
    T : Kind
    E : Kind

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



