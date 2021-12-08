open import basicBitcoinDataType
module verificationStackScripts.demoEqualityReasoning (param : GlobalParameters) where

open import Data.List.Base hiding (_++_ )
open import Data.Nat  renaming (_≤_ to _≤'_ ; _<_ to _<'_)
open import Data.List hiding (_++_  )
open import Data.Sum
open import Data.Unit  hiding (_≤_)
open import Data.Empty
open import Data.Maybe
open import Data.Bool  hiding (_≤_ ; _<_ ; if_then_else_  )  renaming (_∧_ to _∧b_ ; _∨_ to _∨b_ ; T to True)
open import Data.Product renaming (_,_ to _,,_ )
open import Data.Nat.Base hiding (_≤_ ; _<_)
open import Data.List.NonEmpty hiding (head; [_])
open import Data.Nat using (ℕ; _+_; _≥_; _>_; zero; suc; s≤s; z≤n)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; module ≡-Reasoning; sym)
open ≡-Reasoning
open import Agda.Builtin.Equality


--our libraries
open import libraries.listLib
open import libraries.emptyLib
open import libraries.natLib
open import libraries.boolLib
open import libraries.equalityLib
open import libraries.andLib
open import libraries.miscLib
open import libraries.maybeLib
open import stack
open import stackPredicate
open import semanticBasicOperations param
open import instructionBasic
open import verificationMultiSig param
open import verificationStackScripts.semanticsStackInstructions param
open import verificationStackScripts.stackVerificationLemmas param
open import verificationStackScripts.stackHoareTriple param
open import verificationStackScripts.sPredicate
open import verificationStackScripts.hoareTripleStackBasic param
open import verificationStackScripts.stackState
open import verificationStackScripts.stackSemanticsInstructionsBasic param
open import verificationStackScripts.verificationMultiSigBasic param


-- postulate time₁ : Time
-- postulate pbk1 pbk2 pbk3 pbk4 : ℕ

postulate

  precondition : StackStatePred


  postcondition : StackStatePred


  intermediateCond1 : StackStatePred


  intermediateCond2 : StackStatePred


  intermediateCond3 : StackStatePred

-- programs
  prog1 : BitcoinScriptBasic

  prog2 prog3 : BitcoinScriptBasic


--proofs
  proof1 : < precondition >iff prog1  < intermediateCond1 >
  proof2 : < intermediateCond1 >iff prog2 < intermediateCond2 >
  proof3 : intermediateCond2 <=>p intermediateCond3
  proof4 : < intermediateCond3 >iff prog3 < postcondition >


theorem : < precondition >iff prog1 ++ (prog2 ++ prog3)  <  postcondition >
theorem =  precondition       <><>⟨  prog1   ⟩⟨  proof1  ⟩
           intermediateCond1  <><>⟨  prog2   ⟩⟨  proof2  ⟩
           intermediateCond2  <=>⟨   proof3  ⟩
           intermediateCond3  <><>⟨  prog3   ⟩⟨  proof4  ⟩e   postcondition  ∎p

