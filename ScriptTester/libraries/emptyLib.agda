module libraries.emptyLib where

open import Data.Empty

{-
data ⊥ : Set where
-}

efq : {A : Set} → ⊥ → A
efq ()
