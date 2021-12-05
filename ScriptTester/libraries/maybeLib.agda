module libraries.maybeLib  where

open import Data.Maybe
open import Data.Bool
open import Data.Empty
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; module ≡-Reasoning; sym)
open ≡-Reasoning
open import Agda.Builtin.Equality
open import Relation.Nullary
--open import Agda.Builtin.Equality.Rewrite

{-
data Maybe (a : Set) : Set where
  nothing : Maybe a
  just    : a -> Maybe a
-}

{-
lift2Maybe : {A : Set} (f : A → Maybe A ) → Maybe A → Maybe A
lift2Maybe f s = s >>= f
{-
lift2Maybe f nothing = nothing
lift2Maybe f (just x) = f x
-}
-}

liftJustIsIdLem : {A : Set} → (B : Maybe A → Set)→ (ma : Maybe A) → B ma → B (ma >>= just )
liftJustIsIdLem B nothing b = b
liftJustIsIdLem B (just x) b = b


liftJustIsIdLem2 : {A : Set} → (B : Maybe A → Set)→ (ma : Maybe A) → B (ma >>= just) → B ma
liftJustIsIdLem2 B nothing b = b
liftJustIsIdLem2 B (just x) b = b

-- Lift an arbitrary function of type (A → Set) to  (Maybe A → Set)
liftPred2Maybe : {A : Set}→ (A →  Set)  →  Maybe A → Set
liftPred2Maybe p nothing = ⊥
liftPred2Maybe p (just x) = p x


lemmaEqualLift2Maybe : {A : Set}(f f' : A → Maybe A)(cor : (a : A) → f a ≡ f' a)
                                    → (a : Maybe A) → (a >>= f) ≡ (a >>= f')
lemmaEqualLift2Maybe f f' p (just x) = p x
lemmaEqualLift2Maybe f f' p nothing = refl


liftJustEqLem : {A : Set}(s : Maybe A) → (s >>= just) ≡ s
liftJustEqLem nothing = refl
liftJustEqLem (just x) = refl

liftJustEqLem2 : {A : Set}(s : Maybe A) → s ≡ (s >>= just)
liftJustEqLem2 nothing = refl
liftJustEqLem2 (just x) = refl

{-
lifttoMaybeSet : {A : Set} → (A → Set) → Maybe A → Set
lifttoMaybeSet  P nothing = ⊥
lifttoMaybeSet  P (just x) = P x
-}

_⁺ : {A : Set} → (A → Set) → Maybe A → Set
(P ⁺) nothing  = ⊥
(P ⁺) (just x) = P x

{-
lifttoMaybeBool : {A : Set} → (A → Bool) →  (Maybe A → Bool)
lifttoMaybeBool p nothing = false
lifttoMaybeBool p (just x) = p x
-}

_⁺ᵇ : {A : Set} → (A → Bool) →  (Maybe A → Bool)
(p ⁺ᵇ) nothing  =  false
(p ⁺ᵇ) (just x) =  p x

predicateLiftToMaybe : {A : Set}(P : A → Set)(s : A)
                       → P s → (P ⁺) (just s)
predicateLiftToMaybe P s a = a


liftPredtransformerMaybe : {A : Set}
                           (φ ψ : A → Set)
                           (f : (s : A) → φ s → ψ s)
                           → (s : Maybe A) → (φ ⁺) s → (ψ ⁺) s
liftPredtransformerMaybe φ ψ f (just s) p = f s p


liftToMaybeLemma⊥  : {S : Set} → (s : Maybe S) → ¬ ( (λ s → ⊥ ) ⁺) s
liftToMaybeLemma⊥ nothing p = p
liftToMaybeLemma⊥ (just x) p = p
