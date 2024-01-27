open import basicBitcoinDataType

module paperTypes2021PostProceed.semanticBasicOperationsForTypeSetting (param : GlobalParameters) where

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



open import libraries.listLib
open import libraries.natLib
open import libraries.boolLib
open import libraries.andLib
open import libraries.maybeLib

open import stack
open import semanticBasicOperations param hiding (executeStackCheckSig3Aux;compareSigsMultiSigAux;compareSigsMultiSig;executeMultiSig3;executeMultiSig2;executeMultiSig)



executeStackCheckSig3Aux : Msg →  Stack → Maybe Stack
executeStackCheckSig3Aux msg [] = nothing
executeStackCheckSig3Aux mst (x ∷ []) = nothing
executeStackCheckSig3Aux msg (m ∷ k ∷ []) =  nothing
executeStackCheckSig3Aux msg (m ∷ k ∷ x ∷ []) =  nothing
executeStackCheckSig3Aux msg (m ∷ k ∷ x ∷ f ∷ []) =  nothing
executeStackCheckSig3Aux msg (m ∷ k ∷ x ∷ f ∷ l ∷ []) =  nothing
executeStackCheckSig3Aux msg (p1 ∷ p2 ∷ p3 ∷ s1 ∷ s2 ∷ s3 ∷ s) =  stackAuxFunction s
       ((isSigned msg s1 p1 ) ∧b (isSigned msg s2 p2) ∧b (isSigned msg s3 p3))



mutual

 cmpMultiSigs : (msg : Msg)(sigs pbks : List ℕ)  → Bool
 cmpMultiSigs msg  []               pubkeys    =  true
 cmpMultiSigs msg  (sig ∷ sigs)  []            =  false
 cmpMultiSigs msg  (sig ∷ sigs)  (pbk ∷ pbks)  = cmpMultiSigsAux msg sigs pbks sig (isSigned msg sig pbk)

 cmpMultiSigsAux : (msg : Msg)(sigs pbks : List ℕ)(sig : ℕ)(testRes : Bool) → Bool
 cmpMultiSigsAux  msg  sigs  pbks  sig  false  =  cmpMultiSigs  msg  (sig ∷ sigs)  pbks
 cmpMultiSigsAux  msg  sigs  pbks  sig  true   =  cmpMultiSigs  msg  sigs             pbks




executeMultiSig3 : (msg : Msg)(pbks : List ℕ)(numSigs : ℕ)(st : Stack)(sigs : List ℕ) → Maybe Stack
executeMultiSig3  msg  pbks  _             [] sigs               =  nothing
executeMultiSig3  msg  pbks  zero          (x ∷ restStack) sigs
                  =  just (boolToNat (cmpMultiSigs msg sigs pbks) ∷ restStack)
executeMultiSig3  msg  pbks  (suc numSigs) (sig ∷ rest) sigs
                  =  executeMultiSig3 msg pbks numSigs rest (sig ∷ sigs)


coreExecuteMultiSigThree : (msg : Msg)(sigs : List ℕ)(pbks : List ℕ)(restStack : Stack) → Maybe Stack
coreExecuteMultiSigThree msg sigs pbks restStack =
  just (boolToNat (cmpMultiSigs msg sigs pbks) ∷ restStack)


executeMultiSig2 : (msg : Msg)(numPbks : ℕ)(st :   Stack)(pbks : List ℕ) → Maybe Stack
executeMultiSig2  msg  _        []                pbks  =  nothing
executeMultiSig2  msg  zero     (numSigs ∷ rest)  pbks  =  executeMultiSig3 msg pbks numSigs rest []
executeMultiSig2  msg  (suc n)  (pbk ∷ rest)      pbks  =  executeMultiSig2 msg n rest (pbk ∷ pbks)



executeMultiSig : Msg →  Stack →  Maybe Stack
executeMultiSig msg [] = nothing
executeMultiSig msg (numberOfPbks ∷ st) = executeMultiSig2 msg numberOfPbks st []
