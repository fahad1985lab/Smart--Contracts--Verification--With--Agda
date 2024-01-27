open import basicBitcoinDataType

module verificationP2PKHbasic (param : GlobalParameters) where

open import libraries.listLib
open import Data.List.Base
open import libraries.natLib
open import Data.Nat  renaming (_≤_ to _≤'_ ; _<_ to _<'_)
open import Data.List hiding (_++_)
open import Data.Unit  
open import Data.Empty
open import Data.Bool  hiding (_≤_ ; _<_ ; if_then_else_ ) renaming (_∧_ to _∧b_ ; _∨_ to _∨b_ ; T to True)
open import Data.Product renaming (_,_ to _,,_ )
open import Data.Nat.Base hiding (_≤_ ; _<_)
open import Data.List.NonEmpty hiding (head )
open import Data.Nat using (ℕ; _+_; _≥_; _>_; zero; suc; s≤s; z≤n)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; module ≡-Reasoning; sym)
open ≡-Reasoning
open import Agda.Builtin.Equality

open import libraries.andLib
open import libraries.maybeLib
open import libraries.boolLib

open import stack
open import stackPredicate
open import instruction
open import instructionBasic
open import semanticBasicOperations param


instruction-1 : InstructionBasic
instruction-1 = opCheckSig

instruction-2 : InstructionBasic
instruction-2 = opVerify

instruction-3 : InstructionBasic
instruction-3 = opEqual

instruction-4 : ℕ →  InstructionBasic
instruction-4 pbkh = opPush  pbkh

instruction-5 : InstructionBasic
instruction-5 = opHash

instruction-6 : InstructionBasic
instruction-6 = opDup

accept-0Basic : StackPredicate
accept-0Basic = acceptStateˢ

accept₁ˢ : StackPredicate
accept₁ˢ time m [] = ⊥
accept₁ˢ time m (sig ∷ []) = ⊥
accept₁ˢ time m ( pbk  ∷ sig ∷ st) = IsSigned m  sig pbk


accept₂ˢCore : Time → Msg → ℕ → ℕ → ℕ → Set
accept₂ˢCore time m zero pbk sig = ⊥
accept₂ˢCore time m (suc x) pbk sig =  IsSigned  m sig pbk


accept₂ˢ : StackPredicate
accept₂ˢ time m [] = ⊥
accept₂ˢ time m (x ∷ []) = ⊥
accept₂ˢ time m (x ∷ x₁ ∷ []) = ⊥
accept₂ˢ time m (x ∷ pbk ∷ sig ∷ rest) = accept₂ˢCore time m x pbk sig



accept₃ˢ : StackPredicate
accept₃ˢ time m [] = ⊥
accept₃ˢ time m (x ∷ []) = ⊥
accept₃ˢ time m (x ∷ x₁ ∷ []) = ⊥
accept₃ˢ time m (x ∷ x₁ ∷ x2 ∷ []) = ⊥
accept₃ˢ time m (pbkh2 ∷ pbkh1 ∷ pbk ∷ sig ∷ rest)
     =  (pbkh2 ≡  pbkh1) ∧ IsSigned  m sig pbk



accept₄ˢ : ( pbkh1 : ℕ ) → StackPredicate
accept₄ˢ pbkh1 time m [] = ⊥
accept₄ˢ pbkh1 time m (x ∷ []) = ⊥
accept₄ˢ pbkh1 time m (x ∷ x1  ∷ []) = ⊥
accept₄ˢ pbkh1 time m ( pbkh2   ∷ pbk ∷ sig ∷ st)
        = (pbkh2 ≡  pbkh1) ∧  IsSigned  m sig pbk


accept₅ˢ : ( pbkh1 : ℕ ) → StackPredicate
accept₅ˢ  pbkh1 time m [] = ⊥
accept₅ˢ  pbkh1 time m (x ∷ []) = ⊥
accept₅ˢ  pbkh1 time m (x ∷ x₁ ∷ []) = ⊥
accept₅ˢ  pbkh1 time m ( pbk1   ∷ pbk2 ∷ sig ∷ st)
       =  (hashFun pbk1 ≡  pbkh1) ∧  IsSigned   m  sig  pbk2


wPreCondP2PKHˢ : (pbkh : ℕ ) → StackPredicate
wPreCondP2PKHˢ  pbkh  time  m  []                    =  ⊥
wPreCondP2PKHˢ  pbkh  time  m  (x ∷ [])              =  ⊥
wPreCondP2PKHˢ  pbkh  time  m  ( pbk ∷ sig ∷ st)  =
                (hashFun pbk ≡  pbkh ) ∧ IsSigned  m sig pbk



correct3Aux1 : (x : ℕ)(rest : List ℕ)(time : Time)(msg : Msg) → accept₂ˢ time msg (x ∷ rest)
               →  isTrueNat x
correct3Aux1 zero (zero ∷ []) time msg accept = accept
correct3Aux1 zero (zero ∷ x ∷ rest) time msg accept = accept
correct3Aux1 zero (suc x ∷ []) time msg accept = accept
correct3Aux1 zero (suc x ∷ x₁ ∷ rest) time msg accept = accept
correct3Aux1 (suc x) (x₁ ∷ rest) time msg accept = tt


correct3Aux2 : ( x pbk sig : ℕ )( rest : List ℕ)(time : Time)(m : Msg)
                → accept₂ˢ time m (x ∷ pbk ∷ sig ∷ rest)
                → IsSigned  m sig pbk
correct3Aux2 (suc x) pubkey sig rest time m accept = accept



lemmaCorrect3From1 : (x z t : ℕ)(time : Time )(m : Msg)
                    →  accept₂ˢCore time m x z t → isTrueNat x
lemmaCorrect3From1 (suc x) z t time m p = tt


lemmaCorrect3From : (x y z t : ℕ)(time : Time)(m : Msg)
                    →  accept₂ˢCore time m (compareNaturals x y) z t → x ≡ y
lemmaCorrect3From x y z t time m p = compareNatToEq x  y (lemmaCorrect3From1 (compareNaturals x y) z t time m p)


script-1-b  : BitcoinScriptBasic
script-1-b = opCheckSig ∷ []

script-2-b : BitcoinScriptBasic
script-2-b = opVerify ∷ script-1-b

script-3-b : BitcoinScriptBasic
script-3-b = opEqual ∷ script-2-b

script-4-b : ℕ → BitcoinScriptBasic
script-4-b pbkh  =  opPush  pbkh ∷ script-3-b

script-5-b : ℕ →  BitcoinScriptBasic
script-5-b pbkh = opHash  ∷ script-4-b  pbkh

script-6-b : ℕ → BitcoinScriptBasic
script-6-b pbkh  = opDup ∷ script-5-b pbkh



script-7-b : ℕ → BitcoinScriptBasic
script-7-b pbkh = opMultiSig ∷ script-6-b pbkh

script-7'-b : (pbkh pbk1 pbk2 : ℕ) → BitcoinScriptBasic
script-7'-b pbkh pbk1 pbk2 = opMultiSig ∷ script-6-b pbkh


script-1  : BitcoinScript
script-1  = basicBScript2BScript script-1-b

script-2  : BitcoinScript
script-2  = basicBScript2BScript script-2-b

script-3  : BitcoinScript
script-3  = basicBScript2BScript script-3-b

script-4  : ℕ → BitcoinScript
script-4  pbk = basicBScript2BScript (script-4-b pbk)

script-5  : ℕ → BitcoinScript
script-5  pbk = basicBScript2BScript (script-5-b pbk)

script-6  : ℕ → BitcoinScript
script-6  pbk = basicBScript2BScript (script-6-b pbk)

script-7  : ℕ → BitcoinScript
script-7  pbk = basicBScript2BScript (script-7-b pbk)


script-7' : (pbkh pbk1 pbk2 : ℕ) → BitcoinScript
script-7'  pbkh pbk1 pbk2 = basicBScript2BScript (script-7'-b pbkh pbk1 pbk2)



instructionsBasic : (pbkh : ℕ) (n : ℕ) → n ≤ 5 → InstructionBasic
instructionsBasic pbkh 0 _ = opCheckSig
instructionsBasic pbkh 1 _ = opVerify
instructionsBasic pbkh 2 _ = opEqual
instructionsBasic pbkh 3 _ = opPush pbkh
instructionsBasic pbkh 4 _ = opHash
instructionsBasic pbkh 5 _ = opDup

scriptP2PKH : (pbkh : ℕ) → BitcoinScript
scriptP2PKH pbkh = opDup ∷ opHash ∷ (opPush pbkh) ∷ opEqual ∷ opVerify ∷ opCheckSig ∷ []

weakestPreConditionP2PKHˢ : (pbkh : ℕ) → StackPredicate
weakestPreConditionP2PKHˢ = wPreCondP2PKHˢ
