open import basicBitcoinDataType

module verificationStackScripts.semanticsStackInstructions (param : GlobalParameters) where



open import Data.Nat  hiding (_≤_)
open import Data.List hiding (_++_)
open import Data.Unit  
open import Data.Empty
open import Data.Bool  hiding (_≤_ ; if_then_else_ ) renaming (_∧_ to _∧b_ ; _∨_ to _∨b_ ; T to True)
open import Data.Product renaming (_,_ to _,,_ )
open import Data.Nat.Base hiding (_≤_)
open import Data.Maybe
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; module ≡-Reasoning; sym)
open ≡-Reasoning
open import Agda.Builtin.Equality


--our libraries
open import libraries.listLib
open import libraries.natLib
open import libraries.boolLib
open import libraries.andLib
open import libraries.maybeLib

open import stack
open import semanticBasicOperations param
open import instructionBasic
open import verificationStackScripts.stackState
open import verificationStackScripts.sPredicate
open import verificationStackScripts.stackSemanticsInstructionsBasic param



⟦_⟧ₛ : InstructionBasic → StackState → Maybe StackState
⟦ op ⟧ₛ   = liftStackFun2StackState ⟦ op ⟧ₛˢ



⟦_⟧ₛ⁺ : InstructionBasic → Maybe StackState → Maybe StackState
⟦ op ⟧ₛ⁺ t = t >>= ⟦ op ⟧ₛ



⟦_⟧ : BitcoinScriptBasic → StackState → Maybe StackState
⟦ []  ⟧  = just
⟦ op ∷ []  ⟧  = ⟦ op ⟧ₛ
⟦ op ∷ p   ⟧  s = ⟦ op ⟧ₛ s >>=  ⟦ p ⟧

⟦_⟧⁺ : BitcoinScriptBasic → Maybe StackState → Maybe StackState
⟦ p ⟧⁺ s = s >>= ⟦ p ⟧


validStackAux : (pbkh : ℕ) →  (msg : Msg) →  Stack →  Bool
validStackAux pkh msg[]  []  = false
validStackAux pkh msg (pbk ∷ []) = false
validStackAux pkh msg (pbk ∷ sig ∷ s) = hashFun pbk  ==b pkh ∧b isSigned  msg sig pbk

validStack : (pkh : ℕ) →  BStackStatePred
validStack pkh ⟨ time , msg₁ , stack₁ ⟩ = validStackAux  pkh   msg₁  stack₁
