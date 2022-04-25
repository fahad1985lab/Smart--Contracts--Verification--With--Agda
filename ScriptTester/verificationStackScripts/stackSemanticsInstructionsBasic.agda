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
open import libraries.maybeLib


open import stack
open import semanticBasicOperations param
open import instructionBasic
open import verificationStackScripts.stackState
open import verificationStackScripts.sPredicate




⟦_⟧ₛˢ : InstructionBasic →  Time → Msg →  Stack → Maybe Stack  
⟦ opEqual  ⟧ₛˢ time₁ msg = executeStackEquality
⟦ opAdd    ⟧ₛˢ time₁ msg = executeStackAdd
⟦ opPush x ⟧ₛˢ time₁ msg = executeStackPush x
⟦ opSub    ⟧ₛˢ time₁ msg = executeStackSub
⟦ opVerify ⟧ₛˢ time₁ msg = executeStackVerify
⟦ opCheckSig ⟧ₛˢ time₁ msg = executeStackCheckSig msg
⟦ opEqualVerify ⟧ₛˢ time₁ msg = executeStackVerify
⟦ opDup    ⟧ₛˢ time₁ msg = executeStackDup
⟦ opDrop   ⟧ₛˢ time₁ msg = executeStackDrop
⟦ opSwap   ⟧ₛˢ time₁ msg = executeStackSwap
⟦ opHash   ⟧ₛˢ time₁ msg = executeOpHash
⟦ opCHECKLOCKTIMEVERIFY ⟧ₛˢ time₁ msg = executeOpCHECKLOCKTIMEVERIFY time₁
⟦ opCheckSig3 ⟧ₛˢ time₁ msg = executeStackCheckSig3Aux msg
⟦ opMultiSig ⟧ₛˢ  time₁ msg =  executeMultiSig msg



-- execute only the stack operations of a bitcoin script
--  is correct only for non-if instructiosn
⟦_⟧ˢ : (prog : BitcoinScriptBasic)(time₁ : Time)(msg : Msg)(stack₁ : Stack) → Maybe Stack
⟦ []        ⟧ˢ time₁ msg stack₁ = just stack₁
⟦ op ∷ []   ⟧ˢ time₁ msg stack₁ = ⟦ op ⟧ₛˢ time₁ msg stack₁
⟦ op ∷ prog ⟧ˢ time₁ msg stack₁ =  ⟦ op ⟧ₛˢ time₁ msg stack₁ >>= ⟦ prog ⟧ˢ time₁ msg
