module libraries.natLib where

open import Data.Nat  hiding (_≤_ ; _<_ )
open import Data.Bool  hiding (_≤_ ; _<_ ; if_then_else_ ) renaming (_∧_ to _∧b_ ; _∨_ to _∨b_ ; T to True)
open import Data.Unit 
open import Data.Empty
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; module ≡-Reasoning; sym)
open ≡-Reasoning
open import Agda.Builtin.Equality

open import libraries.boolLib

_≡ℕb_ : ℕ → ℕ → Bool
zero ≡ℕb zero = true
zero ≡ℕb suc m = false
suc n ≡ℕb zero = false
suc n ≡ℕb suc m = n ≡ℕb m

_≡ℕ_ : ℕ → ℕ → Set
n ≡ℕ m = True (n ≡ℕb m)

_≤b_ : ℕ → ℕ → Bool
0 ≤b n             = true
(suc n) ≤b 0       = false
(suc n) ≤b (suc m) = n ≤b m

_≤_ : ℕ → ℕ → Set
n ≤ m = True (n  ≤b m)


_==b_ : ℕ → ℕ → Bool
0  ==b 0  = true
suc n ==b suc m = n ==b m
_ ==b _     = false

nat2TrueFalse : ℕ → ℕ
nat2TrueFalse 0 = 0
nat2TrueFalse (suc n) = 1

boolToNat : Bool → ℕ
boolToNat true = 1
boolToNat false = 0


_<b_ : ℕ → ℕ → Bool
n <b m = suc n ≤b m



isTrueNat : ℕ  →  Set
isTrueNat zero = ⊥
isTrueNat (suc m) = ⊤


compareNaturals : ℕ → ℕ → ℕ
compareNaturals 0 0 = 1
compareNaturals 0 (suc m) = 0
compareNaturals(suc n) 0 = 0
compareNaturals(suc n) (suc m) = compareNaturals n m

compareNaturalsSet : ℕ → ℕ → Bool
compareNaturalsSet 0 0 = true
compareNaturalsSet 0 (suc m) = false
compareNaturalsSet (suc n) 0 = false
compareNaturalsSet (suc n) (suc m) = n ==b m

notFalse : ℕ → Bool
notFalse  zero = false
notFalse  (suc x) = true

NotFalse : ℕ → Set
NotFalse  zero = ⊥
NotFalse  (suc x) = ⊤



compareNatToEq : (x y : ℕ) → isTrueNat (compareNaturals x y) → x ≡ y
compareNatToEq zero zero t = refl
compareNatToEq (suc x) (suc y) t = cong suc (compareNatToEq x y t)

lemmaCompareNat : ( x : ℕ ) → compareNaturals x x ≡ 1
lemmaCompareNat zero = refl
lemmaCompareNat (suc n) = lemmaCompareNat n

boolToNatNotFalseLemma : (b : Bool) → True b → NotFalse (boolToNat b)
boolToNatNotFalseLemma true p = tt

boolToNatNotFalseLemma2 : (b : Bool) → NotFalse (boolToNat b) → True b
boolToNatNotFalseLemma2 true p = tt

leqSucLemma : (n m : ℕ) → n ≤ m → n ≤ suc m
leqSucLemma zero zero p = tt
leqSucLemma zero (suc m) p = tt
leqSucLemma (suc n) (suc m) p = leqSucLemma n m p
