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
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; module ≡-Reasoning; sym)
open ≡-Reasoning
open import Agda.Builtin.Equality


open import libraries.listLib
open import libraries.natLib
open import libraries.boolLib
open import libraries.andLib
open import libraries.maybeLib
open import libraries.emptyLib

open import stack
open import stackPredicate
open import instruction
open import stackSemanticsInstructions param

---------------------------------------------------------------------------------
--   define hoare triples for stack functions
--   and that their correspondence to the full hoare triples for nonif instructions
---------------------------------------------------------------------------------------



record <_>gˢ_<_> (φ : StackPredicate) (stackfun : StackTransformer)
                       (ψ : StackPredicate) : Set where
  constructor hoareTripleStackGen 
  field
    ==>stg : (time : Time)(msg : Msg)(s : Stack)
            → φ time msg s
            → liftPred2Maybe (ψ  time msg) (stackfun time msg s)
    <==stg : (time : Time)(msg : Msg)(s : Stack)
            → liftPred2Maybe (ψ  time msg) (stackfun time msg s)
            → φ time msg s
open <_>gˢ_<_> public


