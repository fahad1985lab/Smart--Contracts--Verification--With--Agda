module libraries.equalityLib where
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; module ≡-Reasoning; sym)
open ≡-Reasoning

transfer : {A : Set}(B : A → Set) {a a' : A} → a ≡ a' → B a → B a'
transfer B refl b = b
