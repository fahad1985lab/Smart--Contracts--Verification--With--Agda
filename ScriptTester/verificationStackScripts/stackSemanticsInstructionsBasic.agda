open import basicBitcoinDataType
 
module verificationStackScripts.stackSemanticsInstructionsBasic (param : GlobalParameters)  where

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
open import verificationStackScripts.stackInstruction



-- The stack operation of type
--   Time → Msg →  Stack → Maybe Stack
-- on which the semantics is based
-- we have (see next lemma) for nonif instructions
-- ⟦ op ⟧s  ≡ stackTransform2StateTransform ⟦ op ⟧sˢ

-- The stacks operations is only corret for non-if instructions
-- original name was   executeStackPartOfInstr

⟦_⟧sˢ : InstructionBasic →  Time → Msg →  Stack → Maybe Stack
⟦ opEqual  ⟧sˢ time₁ msg = executeStackEquality
⟦ opAdd    ⟧sˢ time₁ msg = executeStackAdd
⟦ opPush x ⟧sˢ time₁ msg = executeStackPush x
⟦ opSub    ⟧sˢ time₁ msg = executeStackSub
⟦ opVerify ⟧sˢ time₁ msg = executeStackVerify
⟦ opCheckSig ⟧sˢ time₁ msg = executeStackCheckSig msg
⟦ opEqualVerify ⟧sˢ time₁ msg = executeStackVerify
⟦ opDup    ⟧sˢ time₁ msg = executeStackDup
⟦ opDrop   ⟧sˢ time₁ msg = executeStackDrop
⟦ opSwap   ⟧sˢ time₁ msg = executeStackSwap
⟦ opHash   ⟧sˢ time₁ msg = executeOpHash
⟦ opCHECKLOCKTIMEVERIFY ⟧sˢ time₁ msg = executeOpCHECKLOCKTIMEVERIFY time₁
⟦ opCheckSig3 ⟧sˢ time₁ msg = executeStackCheckSig3Aux msg
⟦ opMultiSig ⟧sˢ  time₁ msg =  executeMultisig msg

-- execute only the stack operations of a bitcoin script
--  is correct only for non-if instructiosn
⟦_⟧ˢ : (prog : BitcoinScriptBasic)(time₁ : Time)(msg : Msg)(stack₁ : Stack) → Maybe Stack
⟦ []        ⟧ˢ time₁ msg stack₁ = just stack₁
⟦ op ∷ []   ⟧ˢ time₁ msg stack₁ = ⟦ op ⟧sˢ time₁ msg stack₁
⟦ op ∷ prog ⟧ˢ time₁ msg stack₁ =  ⟦ op ⟧sˢ time₁ msg stack₁ >>= ⟦ prog ⟧ˢ time₁ msg
