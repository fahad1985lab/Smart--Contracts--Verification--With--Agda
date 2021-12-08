open import basicBitcoinDataType

module verificationStackScripts.semanticBasicOperationsForTypeSetting (param : GlobalParameters) where

open import Data.Nat  hiding (_≤_)
open import Data.List hiding (_++_)
open import Data.Unit  hiding (_≤_)
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
open import libraries.miscLib
open import libraries.maybeLib

open import stack

open import semanticBasicOperations param hiding (executeStackCheckSig3Aux;compareSigsMultiSigAux;compareSigsMultiSig;executeMultiSig3;executeMultiSig2;executeMultisig)

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
--semantic Basic Operations For Type Setting compare SigsMultiSig
 cmpSigs : (msg : Msg)(sigs pbks : List ℕ)  → Bool
 cmpSigs msg  []               pubkeys    =  true
 cmpSigs msg  (sig ∷ sigs)  []            =  false
 cmpSigs msg  (sig ∷ sigs)  (pbk ∷ pbks)  = cmpSigsAux msg sigs pbks sig (isSigned msg sig pbk)

 cmpSigsAux : (msg : Msg)(sigs pbks : List ℕ)(sig : ℕ)(testRes : Bool) → Bool
 cmpSigsAux  msg  sigs  pbks  sig  false  =  cmpSigs  msg  (sig ∷ sigs)  pbks
 cmpSigsAux  msg  sigs  pbks  sig  true   =  cmpSigs  msg  sigs             pbks


--semantic Basic Operations For Type Setting execute MultiSigThree
--@BEGIN@executeMultiSigThree
executeMultiSig3 : (msg : Msg)(pbks : List ℕ)(numSigs : ℕ)(st : Stack)(sigs : List ℕ) → Maybe Stack
executeMultiSig3  msg  pbks  _             [] sigs               =  nothing
executeMultiSig3  msg  pbks  zero          (x ∷ restStack) sigs
                  =  just ((boolToNat (cmpSigs msg sigs pbks)) ∷ restStack)
executeMultiSig3  msg  pbks  (suc numSigs) (sig ∷ rest) sigs
                  =  executeMultiSig3 msg pbks numSigs rest (sig ∷ sigs)

--semantic Basic Operations For Type Setting core Execute MultiSig Three
coreExecuteMultiSigThree : (msg : Msg)(sigs : List ℕ)(pbks : List ℕ)(restStack : Stack) → Maybe Stack
coreExecuteMultiSigThree msg sigs pbks restStack =  just ((boolToNat (cmpSigs msg sigs pbks)) ∷ restStack)


--semantic Basic Operations For Type Setting execute MultiSig Two

executeMultiSig2 : (msg : Msg)(numPbks : ℕ)(st :   Stack)(pbks : List ℕ) → Maybe Stack
executeMultiSig2  msg  _        []                pbks  =  nothing
executeMultiSig2  msg  zero     (numSigs ∷ rest)  pbks  =  executeMultiSig3 msg pbks numSigs rest []
executeMultiSig2  msg  (suc n)  (pbk ∷ rest)      pbks  =  executeMultiSig2 msg n rest (pbk ∷ pbks)

--open import addition10


-- Add the notes to a file  notes in notes
-- next steps
-- move executeMultisig to semanticsInstructions.agda
-- add opMultiSig to the instructions
-- define ⟦ OpMultiSig ⟧s = liftMsgStackToStateTransformerDepIfStack' executeMultisig
-- in semanticsInstructions
-- define in addition4.agda
--   ⟦ OpMultiSig   ⟧stacks time₁ msg =  executeMultisig msg


-- Try out evaluatings scripts as in scriptInterpreter.agda  whether it works as intended
--   write some multisignature script and a scriptsig  and check whether they work correctly

-- Try out experiments like stackfunP2PKH   in additionAntonExperiments.agda
-- for
-- ⟦ (opPush 2) ∷ (opPush pbk1) ∷  (opPush pbk2) ∷  (opPush pbk3) ∷  (opPush 3) ∷  opMultiSig ∷  []     ⟧stack time msg stack
-- whether this is equal to
-- executeMultiSig3 msg (pbk1 ∷ pbk2 ∷ pbk3 ∷ []) 2 stack []
-- similarly as in lemma1 by postulating   pbk1,..,pbk3,time,msg,stack

-- if yes then the
-- weakest precondtion for the multisig script would be:
-- stack needs to have size at least 2 and the for signatures sig1 sig2 on the stack we have
-- cmpSigs  msg (sig1 ∷ [ sig2 ]) (pbk1 ∷ pbk2 ∷ [ pbk3 ] ) = true

--semantic Basic Operations For Type Setting check pubk

executeMultisig : Msg →  Stack →  Maybe Stack
executeMultisig msg [] = nothing
executeMultisig msg (numberOfPbks ∷ st) = executeMultiSig2 msg numberOfPbks st []

