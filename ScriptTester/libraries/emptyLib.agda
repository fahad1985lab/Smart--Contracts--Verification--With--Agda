module libraries.emptyLib where

open import Data.Empty


efq : {A : Set} → ⊥ → A
efq ()
