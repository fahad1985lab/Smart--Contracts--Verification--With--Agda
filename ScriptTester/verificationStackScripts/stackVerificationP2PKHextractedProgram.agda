open import basicBitcoinDataType

module verificationStackScripts.stackVerificationP2PKHextractedProgram (param : GlobalParameters)  where



open import Data.Nat  hiding (_≤_)
open import Data.List hiding (_++_)
open import Data.Unit  
open import Data.Empty
open import Data.Sum
open import Data.Bool  hiding (_≤_ ; if_then_else_ ) renaming (_∧_ to _∧b_ ; _∨_ to _∨b_ ; T to True)
open import Data.Product renaming (_,_ to _,,_ )
open import Data.Nat.Base hiding (_≤_)
open import Data.List.NonEmpty hiding (head ; [_] )
open import Data.Maybe
open import Relation.Nullary

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; module ≡-Reasoning; sym)
open ≡-Reasoning
open import Agda.Builtin.Equality


--our libraries
open import libraries.listLib
open import libraries.equalityLib
open import libraries.natLib
open import libraries.boolLib
open import libraries.emptyLib
open import libraries.andLib
open import libraries.maybeLib

open import stack
open import stackPredicate
open import semanticBasicOperations param
open import hoareTripleStack param
open import instruction
open import stackSemanticsInstructions param
open import verificationP2PKHbasic param
open import verificationStackScripts.stackState
open import verificationStackScripts.sPredicate
open import verificationStackScripts.stackHoareTriple param
open import verificationStackScripts.stackVerificationLemmas param
open import verificationStackScripts.stackSemanticsInstructionsBasic param
open import verificationStackScripts.semanticsStackInstructions param
open import verificationStackScripts.stackVerificationP2PKH param
open import verificationStackScripts.stackVerificationP2PKHindexed param
open import verificationStackScripts.hoareTripleStackBasic param
open import verificationStackScripts.stackVerificationLemmasPart2 param




mutual

  p2pkhFunctionDecoded : (pbkh : ℕ)(msg₁ : Msg)(stack₁ : Stack) → Maybe Stack
  p2pkhFunctionDecoded  pbkh  msg₁  []              =  nothing
  p2pkhFunctionDecoded  pbkh  msg₁  (pbk ∷ stack₁)  =  p2pkhFunctionDecodedAux1 pbk msg₁ stack₁
                                                       (compareNaturals pbkh (hashFun pbk))

  p2pkhFunctionDecodedAux1 : (pbk : ℕ)(msg₁ : Msg)(stack₁ : Stack)(cpRes : ℕ) → Maybe Stack
  p2pkhFunctionDecodedAux1  pbk  msg₁  []               cpRes        =  nothing
  p2pkhFunctionDecodedAux1  pbk  msg₁  (sig₁ ∷ stack₁)  zero         =  nothing
  p2pkhFunctionDecodedAux1  pbk  msg₁  (sig₁ ∷ stack₁)  (suc cpRes)  =
                            just (boolToNat (isSigned  msg₁ sig₁ pbk) ∷ stack₁)
