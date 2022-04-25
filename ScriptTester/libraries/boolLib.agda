module libraries.boolLib where
open import Data.Bool  hiding (_≤_ ; _<_ ; if_then_else_ ) renaming (_∧_ to _∧b_ ; _∨_ to _∨b_ ; T to True)
open import Data.Unit  hiding (_≤_)
open import Data.Empty
open import Relation.Nullary

if_then_else_ : {A : Set }→ Bool →  A → A → A
if true  then n else m = n
if false then n else m =  m

∧bproj₁ : {b b' : Bool} → True (b ∧b b') → True b
∧bproj₁ {true} {true} tt = tt

∧bproj₂ : {b b' : Bool} → True (b ∧b b') → True b'
∧bproj₂ {true} {true} tt = tt

∧bIntro : {b b' : Bool} → True b → True b' → True (b ∧b b')
∧bIntro {true} {true} tt tt = tt

¬bLem : {b : Bool} → True (not b) → ¬ (True b)
¬bLem {false} x ()


