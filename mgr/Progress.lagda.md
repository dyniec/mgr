\iffalse
```
module Progress where 
open import Data.Nat using (ℕ;zero;suc;_+_)
open import Types using (Kind)
open import Runtime
open  Runtime.RuntimeExpr
open RExprSubstTyped 
open RExprSubst
open Runtime.Types_
open Runtime.Typing

import Data.Maybe
open import Data.Product using (_×_;_,′_;Σ-syntax) renaming (_,_ to _,,_) using (proj₁;proj₂)
open import Data.List using (List;_∷_;map) renaming ([] to nil)
open import Relation.Binary.PropositionalEquality using (_≡_;refl;_≢_)
import Data.Vec
import Data.Fin

import Data.Nat.Properties
```
\fi
This chapter defines reduction relation and show its soundness.

# Values
Only abstractions, type abstractions and labels are considered values.
Since the values themselves do not perform any effects, they have a `nil` effect. But rules for all of them have a built-in weakening.
We can use that to generalize their type and perform a substitution  where any effect is expected.
```
data Value : RExpr -> Set where
    vlam : ∀ { e } → Value (lam e)
    vLam : ∀ { k e } → Value (tlam k e)
    vlab : ∀ { n } → Value (label n)
gvalue : ∀ {Δ Θ Γ T E e} → (Value e) → (Δ ⨾ Θ ⨾  Γ ⊢ e ⦂ T / E) → ∀ {F} → (Δ ⨾ Θ ⨾ Γ ⊢ e ⦂ T / F)
gvalue vlam (⊢lam t) = ⊢lam t
gvalue vLam (⊢forall t) = ⊢forall t
gvalue vlab (⊢label x) = ⊢label x
gvalue {Δ} v (⊢weak x x₁ x₂) {F} = (⊢weak x ( <⦂e-refl {Δ} {F}) (gvalue v x₂))
```
# Frames
In this thesis, the term "frame" stands for what is usually evaluation context in literature. This term was
sellected to be sufficiently different from typing context.
The frame represents parts between `reset₀`s, or between `reset₀` and `shift₀`.
Frame type is parametrized by Θ Γ, that is, the typing context outside of frame, a T type of the hole.
It's also indexed by whole frame type and effects, and  the effects of the hole, .
Frames  are intrinsically typed, thus they also store type judgements of subexpressions.
They are defined in such a way to reduce repetition. Otherwise we would need to introduce typing judgements for frames, and then prove type preservation for every operation such as plugging or composition.

```
data Frame (Θ : EContext) (Γ : Context) (T : Type) : Effects → Type → Effects →  Set where
  fempty : ∀ {Eff}
  -----------------------------
    → Frame Θ Γ T Eff T Eff 
  fapp₁ : ∀ {A B  Eff E} → Frame Θ Γ T Eff (A - Eff > B) E 
    → (e : RExpr)  → { ∅ ⨾ Θ ⨾ Γ ⊢ e ⦂ A / Eff  }
    --------------------------
    → Frame Θ Γ T Eff B E
  fapp₂ : ∀ {A B  Eff E} → (e : RExpr) → { v : Value e}
    → { ∅ ⨾ Θ ⨾ Γ ⊢ e ⦂ ( A - Eff > B) / Eff }
    → Frame Θ Γ T Eff A E
    --------------------------------------------------------
    → Frame Θ Γ T Eff B E 
  ftapp : ∀ {A B  Eff E k}
    → ∅ ⨾ Θ ⊢ B ⦂te k
    --------------------------------------------------------
    → Frame Θ Γ T Eff (forallt k A Eff) E
    → Frame Θ Γ T (Eff TypeSubst.effs[t B ]) (A TypeSubst.[ B ] ) E 
  freset-label : ∀ {A E  A' Eff C}
    → (e en : RExpr)
    → ∅ ⨾ Θ  ⊢ C ⦂e
    → ∅ ⨾ Θ ⨾ Γ   ⊢ e ⦂ A' / (C ∷ Eff)
    → ∅ ⨾ Θ ⨾ (Γ , A')   ⊢ en ⦂ A /  Eff
    → Frame Θ Γ T nil (L C at A / Eff) E 
    --------------------------
    → Frame Θ Γ T Eff A E
  fshift-label : ∀ {A E  A' E' C}
    → (e : RExpr)
    → ∅ ⨾ Θ ⊢ C ⦂e
    → ∅ ⨾ Θ ⨾ (Γ , A - E' > A' )  ⊢ e ⦂ A' / E'
    → Frame Θ Γ  T nil (L C at A' / E') E 
    -------------------------------------
    → Frame Θ Γ T (C ∷ nil) A E 

```
Definition and types for frame plugging and composition:
```
plug : ∀ {Θ Γ  T Eff A  E}
  → Frame Θ Γ T Eff A E 
  → (e : RExpr) → ∅  ⨾ Θ ⨾ Γ ⊢ e ⦂ T / E
  →  Σ[ res ∈ RExpr ] (∅ ⨾ Θ ⨾ Γ ⊢ res ⦂ A / Eff)
_∘f_ : ∀ {Γ Θ Eff Eff' Eff'' A B C }
  → Frame Θ Γ B Eff A Eff' 
  → Frame Θ Γ C Eff' B Eff'' 
  → Frame Θ Γ C Eff A Eff'' 
```
\iffalse
```
plug fempty e t = e ,, t
plug (fapp₁ f e₁ {te₁}) e t  with (plug f e t)
... | (res ,, tt) =  app res  e₁ ,, (⊢app tt te₁)
plug (fapp₂ e₁ {_} {te₁} f) e t with (plug f e t)
... | (res ,, tt ) =  app e₁ res ,, ⊢app te₁ tt
plug (ftapp {B = B} x f) e t with (plug f e t)
... | (res ,, tt) = tapp res B ,, ⊢tapp x tt
plug (freset-label ee en x x₁ x₂ f) e t with (plug f e t)
... | (res ,, tt) = (reset₀ ee en res) ,, ⊢reset₀ x tt x₁ x₂
plug (fshift-label e₁ x x₁ f) e t with (plug f e t)
... | (res ,, tt) = (shift₀ res e₁) ,, ⊢shift₀ x tt x₁
fempty ∘f F = F
fapp₁ f e {t} ∘f F = fapp₁ (f ∘f F )  e {t}
fapp₂ e {v} {t} f ∘f F = fapp₂ e {v} {t} (f ∘f F)
ftapp x f ∘f F = ftapp x (f ∘f F)
freset-label e en x x₁ x₂ f ∘f F = freset-label e en x x₁ x₂ (f ∘f F)
fshift-label e x x₁ f ∘f F = fshift-label e x x₁ (f ∘f F)
```
\fi
We can prove how plugging and composition relate.
Plugging an expression into one frame and result of that into another frame results in the same value and type
as plugging the very same expression into a composition of two frames.
```
∘f-lemma : ∀ {Γ Θ  Eff Eff' Eff'' A B C }
  → (f1 : Frame Θ Γ B Eff A Eff' )
  → (f2 : Frame Θ Γ C Eff' B Eff'' )
  → (e : RExpr) → (t : ∅ ⨾ Θ ⨾ Γ ⊢ e ⦂ C / Eff'')
  → plug ( f1 ∘f f2)  e t
  ≡ ((λ x → plug f1 (Data.Product.proj₁ x) (Data.Product.proj₂ x))(plug f2 e t))
```
\iffalse
```
∘f-lemma fempty f2 e t = refl
∘f-lemma (fapp₁ f1 e₁) f2 e t rewrite ∘f-lemma f1 f2 e t = refl
∘f-lemma (fapp₂ e₁ f1) f2 e t rewrite ∘f-lemma f1 f2 e t = refl
∘f-lemma (ftapp x f1) f2 e t rewrite ∘f-lemma f1 f2 e t = refl
∘f-lemma (freset-label ee en x x₁ x₂ f) f2 e t rewrite ∘f-lemma f f2 e t = refl
∘f-lemma (fshift-label e₁ x x₁ f) f2 e t rewrite ∘f-lemma f f2 e t = refl
↑f : forall { Θ A B Eff Eff'  Γ' Γ}
  → Frame Θ Γ      A Eff B Eff' 
  → Frame Θ  (Γ' ⧺ Γ) A Eff B Eff' 
↑f fempty = fempty
↑f (fapp₁ f e {t}) = fapp₁ (↑f f) e {e↑ t}
↑f (fapp₂ e {v} {t} f) = fapp₂ e {v} {e↑ t} (↑f f)
↑f (ftapp t f) = ftapp t ( (↑f f ) ) 
↑f (freset-label e en x x₁ x₂ f) = freset-label e en x (e↑ x₁) (e↑ x₂) (↑f f)
↑f (fshift-label e x x₁ f) = fshift-label e x (e↑ x₁) (↑f f)
```
\fi
A metaframe stores the whole evaluation context, split into frames separated by resets.
Type parameters and indices work in the same way as in the frame.
Unlike the frame, however the metaframe now stores `reset₀`s, so the lists of effects inside and outside the frame
may differ. This means that their difference represents a list of effects handled by the frame.
This observation can be used to prove that for well-typed expressions they decompose into
metaframe and `shift₀` expression, and that metaframe should handle effect of the `shift₀`.
This is true provided that typing context is empty.
This metaframe then decomposes into two two further metaframes  separated by `reset₀` which has the same label
as above-mentioned `shift₀`.

```
data Metaframe (Θ : EContext) (Γ : Context) (T : Type) (Eff : Effects)
  : Type → Effects  → Set where
  mfempty : Metaframe Θ Γ T Eff T Eff 
  mfreset : ∀ { A B C Eff' }
    → (l : Label)
    → ∅ ⨾ Θ  ⊢ C ⦂e
    → ∅ ⨾ Θ ⨾ Γ ⊢ label l ⦂ (L C at B / Eff) / nil
    → (e : RExpr) → (∅ ⨾ Θ ⨾ Γ , A ⊢ e ⦂ B / Eff)
    → Metaframe Θ Γ T (C ∷ Eff) A Eff' 
    ---------------------------------
    → Metaframe Θ Γ T Eff B Eff' 
  mframe : ∀ {A Eff'  B Eff'' }
    → Frame     Θ  Γ A Eff  B Eff'  
    → Metaframe Θ Γ T Eff' A Eff'' 
    -------------------------------------------
    → Metaframe Θ  Γ T Eff  B Eff'' 
```
Similarly to frames, metaframes can be lifted and plugged into arbitrary contexts.
They can also be composed with simple frames.
```
↑m : forall {Θ  A B Eff Eff'  Γ' Γ}
  → Metaframe Θ  Γ      A Eff B Eff' 
  → Metaframe Θ (Γ' ⧺ Γ) A Eff B Eff' 
mplug : ∀ {Θ Γ T Eff A  E}
  → Metaframe Θ Γ T Eff A E 
  → (e : RExpr) → ∅ ⨾ Θ ⨾ Γ ⊢ e ⦂ T / E
  →  Σ[ res ∈ RExpr ] (∅ ⨾ Θ ⨾ Γ ⊢ res ⦂ A / Eff)
_∘m_ : ∀ {Γ Θ  Eff Eff' Eff'' A B C }
  → Metaframe Θ Γ B Eff A Eff' 
  → Metaframe Θ Γ C Eff' B Eff'' 
  → Metaframe Θ Γ C Eff A Eff'' 
_f∘m_ : ∀ {Γ Θ  Eff Eff' Eff'' A B C }
  → Frame Θ Γ B Eff A Eff' 
  → Metaframe Θ Γ C Eff' B Eff'' 
  → Metaframe Θ Γ C Eff A Eff'' 
```
\iffalse
```
↑m mfempty = mfempty
↑m (mfreset l x x₁ e x₂ mf) = mfreset l x (e↑ x₁) e (e↑ x₂) (↑m mf)
↑m (mframe x mf) = mframe (↑f x) (↑m mf)

mplug mfempty e t = e ,, t
mplug (mfreset l lt ltt e₁ x₁ f) e t with (mplug f e t)
... | (res ,, tt) = reset₀ res e₁ (label l) ,, ⊢reset₀ lt ltt tt x₁
mplug (mframe x f) e t with (mplug f e t)
... | (res ,, tt) = plug x res tt

mfempty ∘m m2 = m2
mfreset l x x₁ e x₂ m1 ∘m m2 = mfreset l x x₁ e x₂ (m1 ∘m m2)
_∘m_  (mframe  x m1) m2 = mframe x (m1 ∘m m2)
f f∘m mfempty = mframe f mfempty
f f∘m m@(mfreset l x x₁ e x₂ m') = mframe f m
_f∘m_ f (mframe  f' m) = mframe (f ∘f f') m
```
\fi

# Reduction
Since labels need to be allocated, the reduction relation is defined in terms of the expression and state. The state itself is just the next label to be allocated.
As metaframes are intrinsically typed, we need to provide judgments representing expressions well-typedness.
\iffalse
```
pb-v : ∀ {n} {A : Set} → Data.Vec.Vec A n → A → Data.Vec.Vec A (suc n)
pb-v {n} xs x rewrite Data.Nat.Properties.+-comm 1 n = Data.Vec._++_ xs  (Data.Vec.[_] x)
pb : EContext → (Type × Effects) → EContext
pb (n ,, v) x = suc n ,, pb-v v x
pb-len : ∀ Θ x → suc (proj₁ Θ) ≡ pb Θ x .proj₁
pb-len Θ x = refl
postulate
    pb-lookup : ∀ Θ x i → (t : i Data.Nat.< (Θ .proj₁) )
     → Data.Vec.lookup (Θ .proj₂)
        (Data.Fin.fromℕ< t)
     ≡ Data.Vec.lookup ( (pb Θ x) .proj₂)
        (Data.Fin.fromℕ< (Data.Nat.s≤s t))
    ↑Θ∋l : ∀ {Θ n T E x} →  Θ ∋l n ⦂ T / E  →  pb Θ x ∋l n ⦂ T / E
-- pb-lookup Θ x i t rewrite pb-len Θ x = {!!}
-- ↑Θ∋l {Θ} {n} {T} {E} {x} (∋label t) rewrite pb-lookup Θ x n t rewrite pb-len Θ x = {!∋label {Θ = pb Θ x} t!}
--∋label {Θ = pb Θ x} {!  (Data.Nat.s≤s t)!}
-- ∋label {! t!}
↑Θ⊢e : ∀ {Δ Θ x T} → Δ ⨾ Θ ⊢ T ⦂e → Δ ⨾ pb Θ x ⊢ T ⦂e
↑Θ⊢e (⊢ttv x) = ⊢ttv x
↑Θ⊢e (⊢alloc x) = ⊢alloc (↑Θ∋l x)
↑Θ⊢effs : ∀ {Δ Θ x T} → Δ ⨾ Θ ⊢ T ⦂effs → Δ ⨾ pb Θ x ⊢ T ⦂effs
↑Θ⊢effs ⊢nil = ⊢nil
↑Θ⊢effs (⊢cons x x₁) = ⊢cons (↑Θ⊢e x) (↑Θ⊢effs x₁)
↑Θ⊢t : ∀ {Δ Θ x T} → Δ ⨾ Θ ⊢ T ⦂t → Δ ⨾ pb Θ x ⊢ T ⦂t
↑Θ⊢t (⊢ttv x) = ⊢ttv x
↑Θ⊢t (⊢-> x x₁ x₂) = ⊢-> (↑Θ⊢t x) (↑Θ⊢effs x₁) (↑Θ⊢t x)
↑Θ⊢t (⊢forall x x₁) = ⊢forall (↑Θ⊢t x) (↑Θ⊢effs x₁)
↑Θ⊢t (⊢label x x₁ x₂) = ⊢label (↑Θ⊢e x) (↑Θ⊢t x₁) (↑Θ⊢effs x₂)
↑Θ⊢te : ∀ {Δ Θ x T k} → Δ ⨾ Θ ⊢ T ⦂te k → Δ ⨾ pb Θ x ⊢ T ⦂te k
↑Θ⊢te (⊢e x) = ⊢e (↑Θ⊢e x)
↑Θ⊢te (⊢t x) = ⊢t (↑Θ⊢t x)
↑Θ : ∀ { e Δ Θ Γ A E x} →  Δ ⨾ Θ ⨾ Γ ⊢ e ⦂ A / E → Δ ⨾ pb Θ x ⨾ Γ ⊢ e ⦂ A / E
↑Θ (⊢var x) = ⊢var x
↑Θ (⊢lam t) = ⊢lam (↑Θ t)
↑Θ (⊢weak x x₁ t) = ⊢weak x x₁ (↑Θ t)
↑Θ (⊢app t t₁) = ⊢app (↑Θ t) (↑Θ t₁)
↑Θ (⊢forall t) = ⊢forall (↑Θ t)
↑Θ (⊢tapp x t) = ⊢tapp (↑Θ⊢te x) (↑Θ t)
↑Θ (⊢new tt te t) = ⊢new (↑Θ⊢t tt) (↑Θ⊢effs te) (↑Θ t)
↑Θ (⊢shift₀ x t t₁) = ⊢shift₀ (↑Θ⊢e x) (↑Θ t) (↑Θ t₁)
↑Θ (⊢reset₀ x t t₁ t₂) = ⊢reset₀ (↑Θ⊢e x ) (↑Θ t) (↑Θ t₁) (↑Θ t₂)
↑Θ (⊢label x) = ⊢label (↑Θ∋l x)
postulate
  pb-v-last : ∀ {n} {A : Set} → (xs : Data.Vec.Vec A n) → (x : A) → Data.Vec.lookup (pb-v xs x) (Data.Fin.fromℕ n) ≡ x
  pb-last : ∀ { Θ x }
    → (pb Θ x) ∋l (Θ .proj₁) ⦂ Data.Vec.lookup (pb Θ x .proj₂) (Data.Fin.fromℕ (Θ .proj₁)) .proj₁ / Data.Vec.lookup (pb Θ x .proj₂) (Data.Fin.fromℕ (Θ .proj₁)) .proj₂
  e[t]-types : ∀ {Θ  T E k }
    → Σ[ e ∈ RExpr ] (∅ , k) ⨾ Θ ⨾ ∅ ⊢ e ⦂ TypeSubst.bump T /  TypeSubst.bump' E
    → Σ[ e' ∈ RExpr ] ∅ ⨾ Θ ⨾ ∅ ⊢ ( e' ) ⦂ T  / E
  e[t]-types2 : ∀ {Θ Γ T E e k }
    → (∅ , k) ⨾ Θ ⨾ Γ ⊢ e ⦂ T / E
    → ∅ ⨾ Θ ⨾ Γ ⊢ e  ⦂ T  / E 
  new-subst : ∀ {e Θ A1 E1  T E}
    → ( ∅ , Kind.E) ⨾ Θ ⨾ ( ∅ , L ttv zero at A1 / E1) ⊢ e ⦂ TypeSubst.bump T / TypeSubst.bump' E
    → ∅ ⨾ Θ ⨾ ∅ ⊢ new e ⦂ T / E 
    → Σ[ e' ∈ RExpr ] (∅ ⨾ pb Θ (A1 ,′ E1) ⨾ ∅ ⊢ e' ⦂ T / E)
  tapp-subst : ∀ { Θ e k T A E}
    → (tt : ∅ ⨾ Θ  ⊢ T ⦂te k)
    → (tv : ∅ ⨾ Θ ⨾ ∅ ⊢ (tlam k e) ⦂ forallt k A E / E)
    → ∅ ⨾ Θ ⨾ ∅ ⊢ e RExprSubst.e[t T ]
    ⦂ A TypeSubst.[ T ] / E TypeSubst.effs[t T ]
  
    --new-subst {e} {Θ} t tn = (RExprSubstTyped._[_]  (e e[t Effect (Θ .proj₁) ])  (label (Θ .proj₁)) {te = e[t]-types2 (↑Θ t)} {te1 = {!⊢label!}})
--pb-v-last {zero} Data.Vec.[] x = refl
--pb-v-last {suc n} (x₁ Data.Vec.∷ xs) x rewrite pb-v-last xs x  = refl
--pb-last = {!!}
  
```
\fi
```
State = EContext
private
    variable
        A B : Type
        E E' : Effects
        Θ  : EContext
data _⨾_↦_⨾_⨾_ : (e : RExpr) → (∅ ⨾ Θ ⨾ ∅ ⊢ e ⦂ A / E) → (Θ' : EContext) →(e' : RExpr) → (∅ ⨾ Θ' ⨾ ∅ ⊢ e' ⦂ A / E) → Set where
 ↦new : ∀ {e Θ  E T A1 E1}
  → {te : (∅ , Kind.E) ⨾ Θ ⨾(∅ , L ttv zero at A1 / E1)  ⊢ e ⦂ TypeSubst.bump T / TypeSubst.bump' E}
  → {tn : ∅ ⨾ Θ ⨾ ∅  ⊢ new e ⦂ T / E}
  → new e ⨾ tn  ↦   pb Θ (A1 ,′ E1) ⨾ (new-subst te tn) .proj₁  ⨾ new-subst te tn .proj₂
  
 β-lam-app : ∀ {e V Θ A B E }
  → {te : ∅ ⨾ Θ ⨾ (∅ , A) ⊢ e ⦂ B / E}
  → {tv : ∅ ⨾ Θ ⨾ ∅ ⊢ V ⦂ A / E}
  → Value (lam e)
  → (v : Value V)
  → app (lam e) V ⨾ ⊢app (⊢lam te) tv ↦ Θ ⨾  (RExprSubstTyped._[_] e V {te = te} {te1 = (gvalue v tv)}) .proj₁ ⨾ (RExprSubstTyped._[_] e V {te = te} {te1 = (gvalue v tv)})  .proj₂ 

 β-tlam-tapp : ∀ {k e T  }
   → Value (tlam k e)
    → (tt : ∅ ⨾ Θ  ⊢ T ⦂te k)
    → (tv : ∅ ⨾ Θ ⨾ ∅ ⊢ (tlam k e) ⦂ forallt k A E / E)
   → tapp (tlam k e) T ⨾ ⊢tapp tt tv ↦ Θ ⨾ e RExprSubst.e[t T ]  ⨾ tapp-subst tt tv

 reset₀-vl : ∀ {V e' en  Θ  A B E T }
  → ( v : Value V)
  → {tt : ∅ ⨾ Θ  ⊢ T ⦂e }
  → {tv : ∅ ⨾ Θ ⨾ ∅ ⊢ V ⦂ A / T ∷ E}
  → {ten : ∅ ⨾ Θ ⨾ (∅ , A) ⊢ en ⦂ B / E}
  → {tl : ∅ ⨾ Θ ⨾ ∅  ⊢ e' ⦂ (L T at  B / E) / nil }
  → reset₀ V en e' ⨾ (⊢reset₀ tt tl tv ten) ↦ Θ ⨾ RExprSubstTyped._[_] en V {te = ten} {te1 = (gvalue v tv)} .proj₁ ⨾ RExprSubstTyped._[_] en V {te = ten} {te1 = (gvalue v tv)} .proj₂

 reset₀-l : ∀ {Θ es e' El A B C E' e en}
    → {elabel : ∅ ⨾ Θ ⊢ El ⦂e }
    → {tlabel : ∅ ⨾ Θ ⨾ ∅ ⊢ e' ⦂ (L El at  B / E') / nil }
    → {tes : ∅ ⨾ Θ ⨾ (∅ , A - E' > B )  ⊢ es ⦂ B / E' }
    → {tshift : ∅ ⨾ Θ ⨾ ∅ ⊢ shift₀ e' es ⦂ A / (El ∷ nil)}
    → {f : Metaframe Θ ∅ A  (El ∷ E') C  (El ∷ nil)  }
    → e ≡ mplug f (shift₀ e' es) tshift .proj₁
    → {te : ∅ ⨾ Θ ⨾ ∅ ⊢ e ⦂ C / (El ∷ E') }
    → {ten : ∅ ⨾ Θ ⨾ (∅ , C) ⊢ en ⦂ B / ( E') }
    →  reset₀ e en e' ⨾ ⊢reset₀ elabel tlabel te ten
    ↦ Θ ⨾ (RExprSubstTyped._[_] es
    (lam (reset₀ ((mplug (↑m {Γ' = ∅ , A} f) (var 0 ) (⊢var Z)) .proj₁) en  e'))
    {te = tes} {te1 = gvalue {E = E'} vlam (⊢lam (⊢reset₀ elabel (e↑ tlabel)
      (e↑ (mplug (↑m f) (var 0) (⊢var Z) .proj₂)) (e↑ ten)))} .proj₁)
    ⨾  (RExprSubstTyped._[_] es
    (lam (reset₀ ((mplug (↑m {Γ' = ∅ , A} f) (var 0 ) (⊢var Z)) .proj₁) en  e'))
    {te = tes} {te1 = gvalue {E = E'} vlam (⊢lam (⊢reset₀ elabel (e↑ tlabel)
      (e↑ (mplug (↑m f) (var 0) (⊢var Z) .proj₂)) (e↑ ten)))} .proj₂)



```
 Since the simple reduction above is defined directly on redexes, we introduce -→ that represents the reduction within the metaframe.
 As only whole typed expressions are considered, an empty context is used instead of Γ.
```
data _⨾_⟶_⨾_⨾_ : (e : RExpr) → (∅ ⨾ Θ ⨾ ∅ ⊢ e ⦂ A / E) → (Θ' : EContext) →(e' : RExpr) → (∅ ⨾ Θ' ⨾ ∅ ⊢ e' ⦂ A / E) → Set where
  ⟶frame : ∀ { Θ' e e' e1 e1'  A T Eff  } → (f : Metaframe Θ ∅ A   Eff T  E)
    → (t1 : ∅ ⨾ Θ ⨾ ∅ ⊢ e1 ⦂ A / E )
    → (t1' : ∅ ⨾ Θ' ⨾ ∅ ⊢ e1' ⦂ A / E )
    → e1 ⨾ t1   ↦ Θ' ⨾ e1' ⨾ t1'
    → (Θstep : ∀ {A E B Eff} → Metaframe Θ ∅ A E B Eff → Metaframe Θ' ∅ A E B Eff )
    → (mplug f e1 t1) .proj₁ ≡ e
    → (te : ∅ ⨾ Θ ⨾ ∅ ⊢ e ⦂ A / E)
    →  (mplug (Θstep f) e1' t1') .proj₁ ≡ e'
    → (te' : ∅ ⨾ Θ' ⨾ ∅ ⊢ e' ⦂ A / E)
    →  e ⨾ te ⟶ Θ' ⨾ e' ⨾ te'
```
# Progress

```
{-
data Decompose : State → (e : RExpr)  → Set where
  de-simpl-redex : ∀ {e e2 s s' n Δ Δ' A T Eff Eff'} 
    → (f : Metaframe Δ ∅ T Eff A Eff' Δ' n)
    → (e ,′ s) -→ (e2 ,′ s')
    → (t : Δ ⨾ ∅ ⊢ e ⦂ A / Eff)
    → Decompose s e 
  de-shift : ∀ {s Δ Δ' T Eff A n Eff' es es' e l t} 
    → (f : Metaframe Δ ∅ T Eff A Eff' Δ' n)
    →  shift₀ (label l) es' ≡ es
    → Data.Product.proj₁ (mplug f es t) ≡ e
    → (t : Δ ⨾ ∅ ⊢ e ⦂ A / Eff)
    → (ts : Δ ⨾ ∅ ⊢ es ⦂ T / Eff')
    → Decompose s e 
  de-val : ∀ {Δ Eff A s e} → { t : Δ ⨾ ∅ ⊢ e ⦂ A / Eff}
    -> Value e
    → Decompose s e 
data Progress : State → RExpr → Set where
  done : ∀ {e s} →  Value e → Progress s e
  step : ∀ {e1 s1 e2 s2}
    → ( e1 ,′ s1 ) -→ ( e2 ,′ s2)
    → Progress s1 e1
-}
```

Proof of progress would have a type of
`progress : ∀ {A Δ Effs} → (s : State) → (e : RExpr) → (t : Δ ⨾ ∅ ⊢ e ⦂ A / Effs) → Progress s e`.
In such proof We would use auxiliary struct `Decompose` which builder would  walk down well typed expression recursively
  until it has reached either value, simple reduction (app, tapp, new), or shift, and return it with the surrounding metaframe.

In case of shift, such a metaframe by construction should have an effect handler that has the same effect as shift.
So we can construct `rest₀-k` and surrounding metaframe. Other cases would either be immediate value, or simple reduction in
context.

## Preservation
Current definition of reduction relation would yield proof of preservation immediately if progress was given since, frames and expressions are well typed,
and reduction relation requires proofs to plug into metaframes or substitution.

\iffalse
```
{-
decompose : ∀ {A Δ Effs} → (s : State) → (e : RExpr) → (t : Δ ⨾ ∅ ⊢ e ⦂ A / Effs) → Decompose s e
decompose s (lam e) (⊢lam t) = de-val vlam
decompose s e (⊢forall t) = de-val vLam
decompose s e (⊢label x) = de-val vlab
decompose s e (⊢weak x x₁ t) = decompose s e t
decompose s e (⊢tapp x t) = {!!}
--decompose s e (⊢new t) = de-simpl-redex mfempty (-→frame mfempty ↦new refl refl) (⊢new t)
decompose s e (⊢new {Δ = Δ} {A = A} {E = Eff} t) = de-simpl-redex mfempty ( -→frame {Δ = Δ} {A = A} {Eff = Eff} {t1 = ⊢new t} {t2 = {!!}}  mfempty ↦new refl refl ) (⊢new t)
decompose s e (⊢app t t₁) = {!!}
--decompose s e (⊢tapp x t) = {!!}
decompose s e (⊢new' t) = {!!}
decompose s e (⊢shift₀ x t t₁) = de-shift mfempty refl {!!} (⊢shift₀ x t t₁) {!!}
decompose s e (⊢reset₀ x t t₁ t₂) = {!!}
-}
```
\fi
