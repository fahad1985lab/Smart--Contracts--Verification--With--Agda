open import basicBitcoinDataType

module verificationStackScripts.semanticsStackInstructions (param : GlobalParameters) where



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


--our libraries
open import libraries.listLib
open import libraries.natLib
open import libraries.boolLib
open import libraries.andLib
open import libraries.miscLib
open import libraries.maybeLib

open import stack
open import semanticBasicOperations param
open import instructionBasic
open import verificationStackScripts.stackState
open import verificationStackScripts.sPredicate


--semantics Stack Instructions 
⟦_⟧s : InstructionBasic → StackState → Maybe StackState
⟦ opEqual ⟧s = liftStackToStackStateTransformer'  executeStackEquality
⟦ opAdd ⟧s = liftStackToStackStateTransformer' executeStackAdd
⟦ (opPush x) ⟧s = liftStackToStackStateTransformer' ((executeStackPush x))
⟦ opSub ⟧s  = liftStackToStackStateTransformer' executeStackSub
⟦ opVerify ⟧s = liftStackToStackStateTransformer' executeStackVerify
⟦ opCheckSig ⟧s  =   liftMsgStackToStateTransformer' executeStackCheckSig
⟦ opEqualVerify ⟧s = liftStackToStackStateTransformer' executeStackVerify
⟦ opDup ⟧s = liftStackToStackStateTransformer' executeStackDup
⟦ opDrop ⟧s = liftStackToStackStateTransformer' executeStackDrop
⟦ opSwap ⟧s = liftStackToStackStateTransformer'  executeStackSwap
⟦ opCHECKLOCKTIMEVERIFY ⟧s = liftTimeStackToStateTransformer' executeOpCHECKLOCKTIMEVERIFY
⟦ opCheckSig3  ⟧s = liftMsgStackToStateTransformer' executeStackCheckSig3Aux
⟦ opHash  ⟧s = liftStackToStackStateTransformer' executeOpHash
⟦ opMultiSig ⟧s = liftMsgStackToStateTransformer' executeMultisig



⟦_⟧s⁺ : InstructionBasic → Maybe StackState → Maybe StackState
⟦ op ⟧s⁺ t = t >>= ⟦ op ⟧s
-- ⟦ op ⟧s⁺ nothing = nothing
-- ⟦ op ⟧s⁺ (just s ) = ⟦ op ⟧s s


⟦_⟧ : BitcoinScriptBasic → StackState → Maybe StackState
⟦ []  ⟧  = just
⟦ x ∷ []  ⟧  = ⟦ x ⟧s
⟦ x ∷ l   ⟧  s = ⟦ x ⟧s s >>=  ⟦ l ⟧

⟦_⟧⁺ : BitcoinScriptBasic → Maybe StackState → Maybe StackState
⟦ p ⟧⁺ s = s >>= ⟦ p ⟧


validStackAux : (pbkh : ℕ) →  (msg : Msg) →  Stack →  Bool
validStackAux pkh msg[]  []  = false
validStackAux pkh msg (pbk ∷ []) = false
validStackAux pkh msg (pbk ∷ sig ∷ s) = hashFun pbk  ==b pkh ∧b isSigned  msg sig pbk

validStack : (pkh : ℕ) →  BStackStatePred
validStack pkh ⟨ time , msg₁ , stack₁ ⟩ = validStackAux  pkh   msg₁  stack₁
