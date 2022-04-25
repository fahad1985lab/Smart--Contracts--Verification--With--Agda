module stack where

open import Data.Nat  hiding (_≤_)
open import Data.List hiding (_++_)
open import Data.Unit  hiding (_≤_)
open import Data.Empty
open import Data.Maybe
open import Data.Bool  hiding (_≤_ ; if_then_else_ ) renaming (_∧_ to _∧b_ ; _∨_ to _∨b_ ; T to True)
open import Data.Bool.Base hiding (_≤_ ; if_then_else_ ) renaming (_∧_ to _∧b_ ; _∨_ to _∨b_ ; T to True)
open import Data.Product renaming (_,_ to _,,_ )
open import Data.Nat.Base hiding (_≤_)
open import Data.List.NonEmpty hiding (head)

open import libraries.listLib
open import libraries.natLib
open import libraries.boolLib

open import libraries.andLib
open import libraries.maybeLib

open import basicBitcoinDataType


Stack : Set
Stack = List ℕ


stackHasSingletonTop  : ℕ →   Maybe Stack →  Bool
stackHasSingletonTop l nothing = false
stackHasSingletonTop l (just []) = false
stackHasSingletonTop l (just (z ∷ y)) =  l  ==b z


stackHasTop  :   List ℕ →  Maybe  Stack → Set
stackHasTop [] m = ⊤
stackHasTop (y ∷ n) m = True(stackHasSingletonTop y m)

stackAuxFunction :  Stack → Bool → Maybe Stack
stackAuxFunction s b = just (boolToNat b ∷ s)


-- Stack transformer
StackTransformer : Set
StackTransformer = Time → Msg → Stack → Maybe Stack

-- function that checking if the stack is empty or the top element is false
checkStackAux : Stack → Bool
checkStackAux []  = false
checkStackAux (zero ∷ bitcoinStack₁)  = false
checkStackAux (suc x ∷ bitcoinStack₁)  = true

-- lifting the checkStackAux to Maybe StackIfStack data type
checkStack :  Maybe Stack   → Bool
checkStack nothing = false
checkStack (just x) = checkStackAux x
