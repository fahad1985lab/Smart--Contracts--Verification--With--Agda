open import basicBitcoinDataType

module exampleGeneratedWeakPreCond (param : GlobalParameters) where

open import libraries.listLib
open import Data.List.Base
open import libraries.natLib
open import Data.Nat  renaming (_≤_ to _≤'_ ; _<_ to _<'_)
open import Data.List hiding (_++_)
open import Data.Unit  
open import Data.Empty
open import Data.Maybe
open import Data.Bool  hiding (_≤_ ; _<_ ; if_then_else_ ) renaming (_∧_ to _∧b_ ; _∨_ to _∨b_ ; T to True)
open import Data.Product renaming (_,_ to _,,_ )
open import Data.Nat.Base hiding (_≤_ ; _<_)
open import Data.List.NonEmpty hiding (head; [_])
open import Data.Nat using (ℕ; _+_; _≥_; _>_; zero; suc; s≤s; z≤n)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; module ≡-Reasoning; sym)
open ≡-Reasoning
open import Agda.Builtin.Equality


--our libraries
open import libraries.andLib
open import libraries.maybeLib
open import libraries.boolLib

open import stack
open import stackPredicate
open import semanticBasicOperations param
open import instructionBasic
open import verificationP2PKHbasic param

open import verificationStackScripts.stackHoareTriple param
open import verificationStackScripts.stackState
open import verificationStackScripts.sPredicate
open import verificationStackScripts.semanticsStackInstructions param
open import verificationStackScripts.stackVerificationLemmas param



weakestPreCondˢ : BitcoinScriptBasic → StackStatePred → StackStatePred
weakestPreCondˢ p φ s = (φ ⁺) (⟦ p ⟧ s)


testprog : BitcoinScriptBasic
testprog = opDrop ∷ opDrop ∷ [ opDrop ]

weakestPreCondTestProg : StackStatePred
weakestPreCondTestProg = weakestPreCondˢ testprog acceptState



weakestPreCondTestProgNormalised : StackStatePred
weakestPreCondTestProgNormalised s =
  (stackPred2SPred acceptStateˢ ⁺)
   (stackState2WithMaybe ⟨ currentTime s , msg s , executeStackDrop (stack s) ⟩
   >>=  (λ s₁ → stackState2WithMaybe  ⟨ currentTime s₁ , msg s₁ , executeStackDrop (stack s₁) ⟩
                 >>=  liftStackFun2StackState  (λ time₁ msg₁ → executeStackDrop)))

