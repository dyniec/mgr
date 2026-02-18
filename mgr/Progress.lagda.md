module Progress
## Values

```
open import Data.Nat using (ℕ;zero;suc;_+_)
open import Types using (Context;∅;_,_;_∋_⦂_;Z;S)
open import Runtime
open  Runtime.RuntimeExpr
open Types.Types
open Runtime.RuntimeExpr
module TypeSubst = Types.TypeSubst

import Data.Maybe
open import Data.Product using (_×_;_,′_;Σ-syntax) renaming (_,_ to _,,_) using (proj₁;proj₂)
open import Data.List using (List;_∷_;map) renaming ([] to nil)
open import Relation.Binary.PropositionalEquality using (_≡_;refl;_≢_)

import Data.Nat.Properties

data Value : RExpr -> Set where
    vlam : ∀ { e } → Value (lam e)
    vLam : ∀ { k e } → Value (tlam k e)
    vlab : ∀ { n } → Value (label n)
gvalue : ∀ {Δ Γ T E e} → (Value e) → (Δ ⨾ Γ ⊢ e ⦂ T / E) → ∀ {F} → (Δ ⨾ Γ ⊢ e ⦂ T / F)
--generalize value to any effect
gvalue vlam (⊢lam t) = ⊢lam t
gvalue vLam (⊢forall t) = ⊢forall t
gvalue vlab (⊢label x) = ⊢label x
gvalue {Δ} v (⊢weak x x₁ x₂) {F} = (⊢weak x ( <⦂e-refl {Δ} {F}) (gvalue v x₂))



-- typed frames
-- it would be normally named Context, but that's taken by Context used in typing
data Frame (Δ : TContext) (Γ : Context) (T : Type) : Effects → Type → Effects → TContext → ℕ →  Set where
  -- parametrized by: Δ Γ - typing context, and context outside of frame
  -- T - type of the hole (deBruijn indexes of types are with respect of the hole (so well typed in Δ')
  -- Eff - effects of frame - indexed with respect of whole frame
  -- indexed by Type - returned type of frame if plugged correctly
  -- indexed by Effects - effects of hole, indices respective to hole
  -- indexed by Tcontext - typing context of the hole, should be the same as n elements longer than Δ
  -- indexed by ℕ - amount of new' constructors - means how typing context changed between hole and whole frame
  fempty : ∀ {Eff} → Frame Δ Γ T Eff T Eff Δ zero
  fapp₁ : ∀ {A B n Δ' Eff E} → Frame Δ Γ T Eff (A - Eff > B) E Δ' n → (e : RExpr)  → { Δ ⨾ Γ ⊢ e ⦂ A / Eff  } → Frame Δ Γ T Eff B E Δ' n
  fapp₂ : ∀ {A B n Δ' Eff E} → (e : RExpr) → { v : Value e} → { Δ ⨾ Γ ⊢ e ⦂ ( A - Eff > B) / Eff } -> Frame Δ Γ T Eff A E Δ'  n  -> Frame Δ Γ T Eff B E Δ' n
  fnew' : ∀ {A n Δ' Eff E} → (l : Label) → Frame (`e (Data.Maybe.just l) Δ) Γ T (TypeSubst.bump' Eff) (TypeSubst.bump A) E Δ' n → Frame Δ Γ T Eff A E Δ' (suc n)
  freset-label : ∀ {A n Δ' E l' A' Eff}
    → (e en : RExpr)
    → Δ ⊢ ttv l' ⦂e
    → Δ ⨾ Γ   ⊢ e ⦂ A' / (ttv l' ∷ Eff)
    → Δ ⨾ (Γ , A')   ⊢ en ⦂ A /  Eff
    → Frame Δ Γ T nil (L ttv l' at A / Eff) E Δ' n
    → Frame Δ Γ T Eff A E Δ' n
  fshift-label : ∀ {A n Δ' E l' A' E'}
    → (e : RExpr)
            → Δ ⊢ ttv l' ⦂e
            → Δ ⨾ (Γ , A - E' > A' )  ⊢ e ⦂ A' / E'
    → Frame Δ Γ  T nil (L ttv l' at A' / E') E Δ' n
    → Frame Δ Γ T (ttv l' ∷ nil) A E Δ' n


plug : ∀ {Δ Δ' Γ  T Eff A n E} → Frame Δ Γ T Eff A E Δ' n → (e : RExpr) → Δ' ⨾ Γ ⊢ e ⦂ T / E  →  Σ[ res ∈ RExpr ] (Δ ⨾ Γ ⊢ res ⦂ A / Eff)
plug fempty e t = e ,, t
plug (fapp₁ f e₁ {te₁}) e t  with (plug f e t)
... | (res ,, tt) =  app res  e₁ ,, (⊢app tt te₁)
plug (fapp₂ e₁ {_} {te₁} f) e t with (plug f e t)
... | (res ,, tt ) =  app e₁ res ,, ⊢app te₁ tt
plug (fnew' l f) e t with (plug f e t)
... | (res ,, tt) = new' l res ,, ⊢new' tt 
plug (freset-label ee en x x₁ x₂ f) e t with (plug f e t)
... | (res ,, tt) = (reset₀ ee en res) ,, ⊢reset₀ x tt x₁ x₂
plug (fshift-label e₁ x x₁ f) e t with (plug f e t)
... | (res ,, tt) = (shift₀ res e₁) ,, ⊢shift₀ x tt x₁

_∘f_ : ∀ {Γ Δ Δ' Δ'' Eff Eff' Eff'' A B C n m} → Frame Δ Γ B Eff A Eff' Δ' n → Frame Δ' Γ C Eff' B Eff'' Δ''  m → Frame Δ Γ C Eff A Eff'' Δ'' (n + m)
fempty ∘f F = F
fapp₁ f e {t} ∘f F = fapp₁ (f ∘f F )  e {t} 
fapp₂ e {v} {t} f ∘f F = fapp₂ e {v} {t} (f ∘f F)
fnew' l f ∘f F = fnew' l (f ∘f F)
freset-label e en x x₁ x₂ f ∘f F = freset-label e en x x₁ x₂ (f ∘f F)
fshift-label e x x₁ f ∘f F = fshift-label e x x₁ (f ∘f F)

∘f-lemma : ∀ {Γ Δ Δ' Δ'' Eff Eff' Eff'' A B C n m} → (f1 : Frame Δ Γ B Eff A Eff' Δ' n) → (f2 : Frame Δ' Γ C Eff' B Eff'' Δ''  m) → (e : RExpr) → (t : Δ'' ⨾ Γ ⊢ e ⦂ C / Eff'')
         → plug ( f1 ∘f f2)  e t ≡ ((λ x → plug f1 (Data.Product.proj₁ x) (Data.Product.proj₂ x))(plug f2 e t))
∘f-lemma fempty f2 e t = refl
∘f-lemma (fapp₁ f1 e₁) f2 e t rewrite ∘f-lemma f1 f2 e t = refl
∘f-lemma (fapp₂ e₁ f1) f2 e t rewrite ∘f-lemma f1 f2 e t = refl
∘f-lemma (fnew' x f1) f2 e t rewrite ∘f-lemma f1 f2 e t = refl
∘f-lemma (freset-label ee en x x₁ x₂ f) f2 e t rewrite ∘f-lemma f f2 e t = refl
∘f-lemma (fshift-label e₁ x x₁ f) f2 e t rewrite ∘f-lemma f f2 e t = refl

↑f : forall { Δ A B Eff Eff' Δ' n Γ' Γ}
  → Frame Δ  Γ      A Eff B Eff' Δ' n
  → Frame Δ (Γ' ⧺ Γ) A Eff B Eff' Δ' n
↑f fempty = fempty
↑f (fapp₁ f e {t}) = fapp₁ (↑f f) e {e↑ t}
↑f (fapp₂ e {v} {t} f) = fapp₂ e {v} {e↑ t} (↑f f)
↑f (fnew' l f) = fnew' l (↑f f)
↑f (freset-label e en x x₁ x₂ f) = freset-label e en x (e↑ x₁) (e↑ x₂) (↑f f)
↑f (fshift-label e x x₁ f) = fshift-label e x (e↑ x₁) (↑f f)
  

data Metaframe (Δ : TContext) (Γ : Context) (T : Type) (Eff : Effects) : Type → Effects → TContext → ℕ → Set where
  -- Metaframe splits evaluation context into frames separated by resets
  -- type parameters and indices work the same as in frame
  -- since Eff can (now) grow, Eff and Effects index
  -- might have different lenghts, and their difference (modulo debrujin indices, which difference we know thanks to ℕ index) represents list of effects handled by metaframe
  mfempty : Metaframe Δ Γ T Eff T Eff Δ zero
  mfreset : ∀ {Δ' A B Eff' n l'}
    → (l : Label)  → Δ ⊢ ttv l' ⦂e → Δ ⨾ Γ ⊢ label l ⦂ (L ttv l' at B / Eff) / nil
    → (e : RExpr) → (Δ ⨾ Γ , A ⊢ e ⦂ B / Eff)
    → Metaframe Δ Γ T (ttv l' ∷ Eff) A Eff' Δ' n
    → Metaframe Δ Γ T Eff B Eff' Δ' n
  mframe : ∀ {A Eff' Δ' n B Eff'' Δ'' m}
    → Frame     Δ  Γ A Eff  B Eff'  Δ'  n
    → Metaframe Δ' Γ T Eff' A Eff'' Δ'' m
    → Metaframe Δ  Γ T Eff  B Eff'' Δ'' (n + m)
    
↑m : forall { Δ A B Eff Eff' Δ' n Γ' Γ}
  → Metaframe Δ  Γ      A Eff B Eff' Δ' n
  → Metaframe Δ (Γ' ⧺ Γ) A Eff B Eff' Δ' n
↑m mfempty = mfempty
↑m (mfreset l x x₁ e x₂ mf) = mfreset l x (e↑ x₁) e (e↑ x₂) (↑m mf)
↑m (mframe x mf) = mframe (↑f x) (↑m mf)

mplug : ∀ {Γ Δ Δ' T Eff A n E} → Metaframe Δ Γ T Eff A E Δ' n → (e : RExpr) → Δ' ⨾ Γ ⊢ e ⦂ T / E  →  Σ[ res ∈ RExpr ] (Δ ⨾ Γ ⊢ res ⦂ A / Eff)
mplug mfempty e t = e ,, t
mplug (mfreset l lt ltt e₁ x₁ f) e t with (mplug f e t)
... | (res ,, tt) = reset₀ res e₁ (label l) ,, ⊢reset₀ lt ltt tt x₁
mplug (mframe x f) e t with (mplug f e t)
... | (res ,, tt) = plug x res tt

_∘m_ : ∀ {Γ Δ Δ' Δ'' Eff Eff' Eff'' A B C n m} → Metaframe Δ Γ B Eff A Eff' Δ' n → Metaframe Δ' Γ C Eff' B Eff'' Δ''  m → Metaframe Δ Γ C Eff A Eff'' Δ'' (n + m)
mfempty ∘m m2 = m2
mfreset l x x₁ e x₂ m1 ∘m m2 = mfreset l x x₁ e x₂ (m1 ∘m m2)
_∘m_ {n = n} {m = m'} (mframe {n = n1} {m = m''} x m1) m2 = math n1 m'' m' (mframe x (m1 ∘m m2))
  where math : ∀ {Δ Δ' Γ A B Eff Eff' } → ∀ (n n1 m : ℕ)→ Metaframe  Δ Γ A Eff B Eff' Δ' (n + (n1 + m)) → Metaframe Δ Γ A Eff B Eff' Δ' (n + n1 + m)
        math n n1 m mf rewrite Relation.Binary.PropositionalEquality.sym (Data.Nat.Properties.+-assoc n n1 m) = mf
_f∘m_ : ∀ {Γ Δ Δ' Δ'' Eff Eff' Eff'' A B C n m} → Frame Δ Γ B Eff A Eff' Δ' n → Metaframe Δ' Γ C Eff' B Eff'' Δ''  m → Metaframe Δ Γ C Eff A Eff'' Δ'' (n + m)
f f∘m mfempty = mframe f mfempty
f f∘m m@(mfreset l x x₁ e x₂ m') = mframe f m
_f∘m_ {n = n} f (mframe {n = n1} {m = m1} f' m) = assoc {n = n} {n1 = n1} {m = m1} (mframe (f ∘f f') m)
  where assoc : ∀ {Γ Δ Δ' A B Eff Eff' n n1 m} → Metaframe Δ Γ A Eff B Eff' Δ' (n + n1 + m) → Metaframe Δ Γ A Eff B Eff' Δ' (n + (n1 + m))
        assoc {n = n} { n1 = n1} {m = m} mf rewrite Data.Nat.Properties.+-assoc n n1 m = mf

infix 2 _↦_
State = ℕ
-- evaluation state, represents next label to be assigned
data _↦_ : RExpr × State → RExpr × State → Set where
--only redexes
  
 ↦new : ∀ {e s Δ Γ E T A1 E1}
  → {te : `e (Data.Maybe.just s) Δ ⨾(Γ , L ttv zero at A1 / E1)  ⊢ e ⦂ E / T}
  → new e ,′ s  ↦ new' s ( RExprSubstTyped._[_] e (label s) {te = te} {te1 = ⊢label Z} .proj₁ ) ,′ suc s

 β-lam-app : ∀ {e V s Δ Γ A B E}
  → {te : Δ ⨾ (Γ , A) ⊢ e ⦂ B / E}
  → {tv : Δ ⨾ Γ ⊢ V ⦂ A / E}
  → Value (lam e)
  → (v : Value V)
  → app (lam e) V ,′ s ↦ (proj₁ (RExprSubstTyped._[_] e V {te = te} {te1 = (gvalue v tv)})) ,′ s

 β-tlam-tapp : ∀ {k e T s}
   → Value (tlam k e)
   → tapp (tlam k e) T ,′ s ↦ e RExprSubst.e[t T ]  ,′ s

 β-reset₀-vl : ∀ {V e' en s Δ Γ A B E }
   → ( v : Value V)
  → {tv : Δ ⨾ Γ ⊢ V ⦂ A / E}
  → {ten : Δ ⨾ (Γ , A) ⊢ en ⦂ B / E}
   → reset₀ V en e' ,′ s ↦ (RExprSubstTyped._[_] en V {te = ten} {te1 = (gvalue v tv)} .proj₁) ,′ s

 β-reset₀-k : ∀ {es en e' e s n Δ Δ' A T Eff Eff' B A' E' ls lr}
   → { f : Metaframe Δ ∅ T Eff A Eff' Δ' n }
   -> Value (e')
   --shift
   → {ts : Δ' ⨾ ∅ ⊢ (shift₀ e' es) ⦂ T / Eff'}
   → {tes : Δ' ⨾ (∅ , T - Eff' > B) ⊢ es ⦂ B / Eff' }
   → {tls : Δ' ⨾ ∅ ⊢ e' ⦂ (L ttv ls at B / Eff') /  nil }
   → {tlvs : Δ'  ⊢  ttv lr ⦂e }
   --reset
   → {te : Δ ⨾ ∅ ⊢ e ⦂ A' / (ttv lr ∷ E') }
   → {ten : Δ ⨾ ∅ , A' ⊢ en ⦂ T / Eff }
   → {tlr : Δ ⨾ ∅ ⊢ e' ⦂ (L ttv lr at T / Eff) /  nil }
   → {tlvr : Δ  ⊢  ttv lr ⦂e }
   → (proj₁ (mplug  f (shift₀ e' es) ts)) ≡ e
   → reset₀ e en e' ,′ s ↦ RExprSubstTyped._[_] es (lam (reset₀ (proj₁ (mplug (↑m {Γ' = ∅ , T} f) (var 0) (⊢var Z))) en e')) {te = tes} {te1 = gvalue vlam (⊢lam (⊢reset₀ tlvs ( {!!}) {!!} {!!}))} .proj₁  ,′ s
 --  → reset₀ e en e' ,′ s ↦ RExprSubstTyped._[_] es (lam (reset₀ (proj₁ (mplug (↑m {Γ' = ∅ , T} f) (var 0) (⊢var Z))) en e')) {te = tes} {te1 =  gvalue vlam  (⊢lam (⊢reset₀ tl' (e↑ te') {! (proj₂ (mplug (↑m {Γ' = ∅ , T} f) (var 0) (⊢var Z)))!} (e↑ ten)))} .proj₁  ,′ s

infix 2 _-→_
data _-→_ : RExpr × State → RExpr × State → Set where
  -→frame : ∀ {e1 e1' e2 e2' s s' n Δ Δ' A T Eff Eff' t1 t2} → (f : Metaframe Δ ∅ T Eff A Eff' Δ' n)
    → e1' ,′ s ↦ e2' ,′ s'
    → Data.Product.proj₁ (mplug f e1' t1) ≡ e1
    → Data.Product.proj₁ (mplug f e2' t2) ≡ e2
    →  (e1 ,′ s) -→ (e2 ,′ s')

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
    --→ (e ,′ s) -→ (e2 ,′ s')
    → (ts : Δ ⨾ ∅ ⊢ es ⦂ T / Eff')
    → Decompose s e 
  de-val : ∀ {Δ Eff A s e} → { t : Δ ⨾ ∅ ⊢ e ⦂ A / Eff}
    -> Value e
    → Decompose s e 
  

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
