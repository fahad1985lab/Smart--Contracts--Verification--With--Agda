module stackPredicate where

open import Data.Nat  hiding (_≤_)
open import Data.List hiding (_++_)
open import Data.Unit  hiding (_≤_)
open import Data.Empty
open import Data.Sum
open import Data.Maybe
open import Data.Bool  hiding (_≤_ ; if_then_else_ ) renaming (_∧_ to _∧b_ ; _∨_ to _∨b_ ; T to True)
open import Data.Bool.Base hiding (_≤_ ; if_then_else_ ) renaming (_∧_ to _∧b_ ; _∨_ to _∨b_ ; T to True)
open import Data.Product renaming (_,_ to _,,_ )
open import Data.Nat.Base hiding (_≤_)
open import Data.List.NonEmpty hiding (head)
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
open import basicBitcoinDataType


StackPredicate : Set₁
StackPredicate = Time → Msg → Stack → Set

_⊎sp_   : (φ ψ : StackPredicate) → StackPredicate
(φ  ⊎sp  ψ)  t m st = φ  t m st  ⊎ ψ  t m st

_∧sp_ : ( φ ψ  : StackPredicate ) → StackPredicate
(φ ∧sp ψ ) t m s   =  φ t m s  ∧  ψ t m s


truePredaux : StackPredicate → StackPredicate
truePredaux φ time msg [] = ⊥
truePredaux φ time msg (zero ∷ st) = ⊥
truePredaux φ time msg (suc x ∷ st) = φ time msg  st


acceptStateˢ : StackPredicate
acceptStateˢ  time  msg₁  []            =  ⊥
acceptStateˢ  time  msg₁  (x ∷ stack₁)  =  NotFalse x


