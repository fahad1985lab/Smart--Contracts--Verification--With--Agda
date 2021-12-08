open import basicBitcoinDataType

module hoareTripleStack (param : GlobalParameters) where

open import Data.Nat  renaming (_≤_ to _≤'_ ; _<_ to _<'_)
open import Data.List hiding (_++_)
open import Data.Sum
open import Data.Maybe
open import Data.Unit  hiding (_≤_)
open import Data.Empty
open import Data.Bool  hiding (_≤_ ; if_then_else_ ) renaming (_∧_ to _∧b_ ; _∨_ to _∨b_ ; T to True)
open import Data.Bool.Base hiding (_≤_ ; if_then_else_ ) renaming (_∧_ to _∧b_ ; _∨_ to _∨b_ ; T to True)
open import Data.Product renaming (_,_ to _,,_ )
open import Data.Nat.Base hiding (_≤_)
-- open import Data.List.NonEmpty hiding (head)

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
open import libraries.emptyLib

open import stack
open import stackPredicate

open import instruction
-- open import ledger param
open import stackSemanticsInstructions param

--------------------------------------------------------------------------
--   defines hoare triples for stack functions
--   and that their correspondence to the full hoare triples for nonif instructions
---------------------------------------------------------------------------------------



-- Defines the condition for the stackfunction of an instruction
--   for the hoare truple based on φ ψ only to be correct
--
-- here we have a generic version which doesn't refer to an instruction
--  but just its stack partx
--
-- we later show that this implies the correctness of a
--  Hoare triple for that instruction
--  provided we have a non-if instruction

record <_>stgen_<_> (φ : StackPredicate) (stackfun : StackTransformer)
                       (ψ : StackPredicate) : Set where
  constructor hoareTripleStackGen -- corrStackPartGeneric
  field
    ==>stg : (time : Time)(msg : Msg)(s : Stack)
            → φ time msg s
            → liftPred2Maybe (ψ  time msg) (stackfun time msg s)
    <==stg : (time : Time)(msg : Msg)(s : Stack)
            → liftPred2Maybe (ψ  time msg) (stackfun time msg s)
            → φ time msg s
open <_>stgen_<_> public

{-
HoareTripleStackGen : (φ : StackPredicate) (stackfun : StackTransformer) (ψ : StackPredicate)
                      → Set
HoareTripleStackGen φ stackfun ψ  = < φ >stgen stackfun < ψ >
-}
{-
-- The condition CorrectnessStackPartGeneric
--  instantiated for the stack part of an instruction
--     is only really correct for non-if instructions
CorrectnessStackPartOfInstr : (instr : InstructionAll)
                              (φ ψ : StackPredicate)
                              → Set
CorrectnessStackPartOfInstr instr φ ψ = < φ >stgen ⟦ instr ∷ []  ⟧stack < ψ >
-}

-- Hoare triple  with stack instructions
<_>stack_<_> : StackPredicate → BitcoinScript → StackPredicate → Set
< φ >stack prog < ψ > = < φ >stgen ⟦ prog  ⟧stack  < ψ >
