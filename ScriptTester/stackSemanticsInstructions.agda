open import basicBitcoinDataType

module stackSemanticsInstructions (param : GlobalParameters) where

open import Data.Nat  hiding (_≤_)
open import Data.List hiding (_++_)
open import Data.Unit  hiding (_≤_)
open import Data.Empty
open import Data.Bool  hiding (_≤_ ; if_then_else_ ) renaming (_∧_ to _∧b_ ; _∨_ to _∨b_ ; T to True)
open import Data.Product renaming (_,_ to _,,_ )
open import Data.Nat.Base hiding (_≤_)
-- open import Data.List.NonEmpty hiding (head)
open import Data.Maybe

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; module ≡-Reasoning; sym)
open ≡-Reasoning
open import Agda.Builtin.Equality
--open import Agda.Builtin.Equality.Rewrite


open import libraries.listLib
open import libraries.natLib
open import libraries.boolLib
open import libraries.andLib
open import libraries.miscLib
open import libraries.maybeLib

open import stack
open import instruction
open import semanticBasicOperations param


-- The stack operation of type
--   Time → Msg →  Stack → Maybe Stack
-- on which the semantics is based
-- we have (see next lemma) for nonif instructions
-- ⟦ op ⟧s  ≡ stackTransform2StateTransform ⟦ op ⟧stacks

-- The stacks operations is only corret for non-if instructions
-- original name was   executeStackPartOfInstr

⟦_⟧stacks : InstructionAll →  Time → Msg →  Stack → Maybe Stack
⟦ opEqual  ⟧stacks time₁ msg = executeStackEquality
⟦ opAdd    ⟧stacks time₁ msg = executeStackAdd
⟦ opPush x ⟧stacks time₁ msg = executeStackPush x
⟦ opSub    ⟧stacks time₁ msg = executeStackSub
⟦ opVerify ⟧stacks time₁ msg = executeStackVerify
⟦ opCheckSig ⟧stacks time₁ msg = executeStackCheckSig msg
⟦ opEqualVerify ⟧stacks time₁ msg = executeStackVerify
⟦ opDup    ⟧stacks time₁ msg = executeStackDup
⟦ opDrop   ⟧stacks time₁ msg = executeStackDrop
⟦ opSwap   ⟧stacks time₁ msg = executeStackSwap
⟦ opHash   ⟧stacks time₁ msg = executeOpHash
⟦ opCHECKLOCKTIMEVERIFY ⟧stacks time₁ msg = executeOpCHECKLOCKTIMEVERIFY time₁
⟦ opIf     ⟧stacks time₁ msg = just
⟦ opElse   ⟧stacks time₁ msg = just
⟦ opEndIf  ⟧stacks time₁ msg = just
⟦ opCheckSig3 ⟧stacks time₁ msg = executeStackCheckSig3Aux msg
⟦ opMultiSig ⟧stacks  time₁ msg =  executeMultiSig msg

-- execute only the stack operations of a bitcoin script
--  is correct only for non-if instructiosn
⟦_⟧stack : (prog : BitcoinScript)(time₁ : Time)(msg : Msg)(stack₁ : Stack) → Maybe Stack
⟦ []        ⟧stack time₁ msg stack₁ = just stack₁
⟦ op ∷ []   ⟧stack time₁ msg stack₁ = ⟦ op ⟧stacks time₁ msg stack₁
⟦ op ∷ prog ⟧stack time₁ msg stack₁ = ⟦ op ⟧stacks time₁ msg stack₁ >>=  ⟦ prog ⟧stack time₁ msg
