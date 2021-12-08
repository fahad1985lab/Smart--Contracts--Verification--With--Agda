--@PREFIX@stackVerificationPtoPKHUsingEqualityOfPrograms
-- \stackVerificationPtoPKHUsingEqualityOfPrograms
open import basicBitcoinDataType

module verificationStackScripts.stackVerificationP2PKHUsingEqualityOfPrograms(param : GlobalParameters)  where



open import Data.Nat  hiding (_≤_)
open import Data.List hiding (_++_)
open import Data.Unit  hiding (_≤_)
open import Data.Empty
open import Data.Sum
open import Data.Bool  hiding (_≤_ ; if_then_else_ ) renaming (_∧_ to _∧b_ ; _∨_ to _∨b_ ; T to True)
open import Data.Product renaming (_,_ to _,,_ )
open import Data.Nat.Base hiding (_≤_)
open import Data.List.NonEmpty hiding (head ; [_] )
open import Data.Maybe
open import Relation.Nullary

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; module ≡-Reasoning; sym)
open ≡-Reasoning
open import Agda.Builtin.Equality


--our libraries
open import libraries.listLib
open import libraries.equalityLib
open import libraries.natLib
open import libraries.boolLib
open import libraries.emptyLib
open import libraries.andLib
open import libraries.miscLib
open import libraries.maybeLib

open import stack
open import stackPredicate
open import semanticBasicOperations param
open import stackSemanticsInstructions param
open import hoareTripleStack param
open import instruction
open import verificationP2PKHbasic param
open import verificationStackScripts.stackState
open import verificationStackScripts.sPredicate
open import verificationStackScripts.stackHoareTriple param
open import verificationStackScripts.stackVerificationLemmas param
open import verificationStackScripts.stackSemanticsInstructionsBasic param
open import verificationStackScripts.semanticsStackInstructions param
open import verificationStackScripts.stackVerificationP2PKH param
open import verificationStackScripts.stackVerificationP2PKHindexed param
open import verificationStackScripts.stackVerificationP2PKHextractedProgram param
open import verificationStackScripts.hoareTripleStackBasic param
open import verificationStackScripts.stackVerificationLemmasPart2 param
-------------------------------------------------------
-- The symbolic execution has been moved to
--
--     stackVerificationP2PKHsymbolicExecution.agda
--
-- The extracted program obtained by the symbolic execution has been moved to
--
--  stackVerificationP2PKHextractedProgram.agda
--
------------------------------------------------------------------------------



{-   Discussion with Arnold:
       maybe better not to create the optimized program because we obtained this program in a systematic way
       and can from it read off the weakest pre condition already
       Discussion of further improvement (permutative conversions in a systematic way) for future work
-}


-- \stackVerificationPtoPKHUsingEqualityOfProgramsptopkhNonEmptyStackAbstr
--@BEGIN@ptopkhNonEmptyStackAbstr
p2PKHNonEmptyStackAbstr : (msg₁ : Msg)(pbk : ℕ)(stack₁ : Stack)(cmp : ℕ) → Maybe Stack
p2PKHNonEmptyStackAbstr msg₁ pbk stack₁ cmp =  executeStackVerify (cmp ∷  pbk ∷ stack₁) >>=
                                               executeStackCheckSig msg₁
--@END

stackfunP2PKHNonEmptyStackAbstractedCorCompr0IsNothing : (msg₁ : Msg)(pbk : ℕ)(stack₁ : Stack)
      →  p2PKHNonEmptyStackAbstr msg₁ pbk stack₁ 0 ≡ nothing
stackfunP2PKHNonEmptyStackAbstractedCorCompr0IsNothing msg₁ pbk stack₁ = refl


stackfunP2PKHNonEmptyStackAbstractedCorEmptysNothing : (msg₁ : Msg)(pbk : ℕ)(x : ℕ)
      →  p2PKHNonEmptyStackAbstr msg₁ pbk [] x ≡ nothing

stackfunP2PKHNonEmptyStackAbstractedCorEmptysNothing msg₁ pbk₁ zero = refl
stackfunP2PKHNonEmptyStackAbstractedCorEmptysNothing msg₁ pbk₁ (suc x) = refl

stackfunP2PKHNonEmptyStackAbstractedCor :  (pubKeyHash : ℕ)(time₁ : Time)(msg₁ : Msg)(pbk : ℕ)(stack₁ : Stack)
                → ⟦ scriptP2PKHbas pubKeyHash ⟧stb time₁ msg₁ (pbk ∷ stack₁)
                   ≡ p2PKHNonEmptyStackAbstr  msg₁ pbk stack₁
                           (compareNaturals pubKeyHash (hashFun pbk))
stackfunP2PKHNonEmptyStackAbstractedCor pubKeyHash time₁ msg₁ pbk stack₁ = refl


p2pkhFunctionDecodedaux1cor : (pbk : ℕ)(msg₁ : Msg)(stack₁ : Stack)(cpRes : ℕ)
 → p2PKHNonEmptyStackAbstr msg₁ pbk stack₁ cpRes ≡ p2pkhFunctionDecodedaux1 pbk msg₁ stack₁ cpRes

p2pkhFunctionDecodedaux1cor pbk₁ msg₁ [] cpRes = stackfunP2PKHNonEmptyStackAbstractedCorEmptysNothing msg₁ pbk₁ cpRes
p2pkhFunctionDecodedaux1cor pbk₁ msg₁ (x ∷ stack₁) zero = refl
p2pkhFunctionDecodedaux1cor pbk₁ msg₁ (x ∷ stack₁) (suc cpRes) = refl

-- \stackVerificationPtoPKHUsingEqualityOfProgramsptopkhFunctionDecodedcor
--@BEGIN@ptopkhFunctionDecodedcor
p2pkhFunctionDecodedcor : (time₁ : ℕ) (pbkh : ℕ)(msg₁ : Msg)(stack₁ : Stack)
 → ⟦ scriptP2PKHbas pbkh ⟧stb time₁ msg₁ stack₁  ≡ p2pkhFunctionDecoded pbkh  msg₁ stack₁
--@END
p2pkhFunctionDecodedcor time₁ pbkh msg₁ [] = refl
p2pkhFunctionDecodedcor time₁ pbkh msg₁ (pbk ∷ stack₁) =
       ⟦ scriptP2PKHbas pbkh ⟧stb time₁ msg₁ (pbk ∷ stack₁)
          ≡⟨ stackfunP2PKHNonEmptyStackAbstractedCor pbkh time₁ msg₁ pbk stack₁ ⟩
       p2PKHNonEmptyStackAbstr  msg₁ pbk stack₁ (compareNaturals pbkh (hashFun pbk))
          ≡⟨ p2pkhFunctionDecodedaux1cor pbk msg₁ stack₁ (compareNaturals pbkh (hashFun pbk)) ⟩
       p2pkhFunctionDecodedaux1 pbk msg₁ stack₁    (compareNaturals pbkh (hashFun pbk))
       ∎

{- Now we just verify the   hoare triple for the function we have found we have decoded

-}

lemmaPHKcoraux3 : (x₁ : ℕ)(time : Time) (msg₁ : Msg) (x₂ : ℕ)(s : Stack) (x : ℕ) →
                 liftPred2Maybe (λ s₁ → acceptStateˢ time msg₁ s₁)
                  (p2pkhFunctionDecodedaux1 x₁ msg₁ (x₂ ∷ s) x)
                  → ¬ (x ≡ 0 )
lemmaPHKcoraux3 x₁ time msg₁ x₂ s zero () x₄
lemmaPHKcoraux3 x₁ time msg₁ x₂ s (suc x) x₃ ()

lemmaCompareNat2 : ( x y : ℕ ) → ¬ (compareNaturals x y ≡ 0 ) → x ≡ y
lemmaCompareNat2 zero zero p = refl
lemmaCompareNat2 zero (suc y) p = efq (p refl)
lemmaCompareNat2 (suc x) zero p = efq (p refl)
lemmaCompareNat2 (suc x) (suc y) p = cong suc (lemmaCompareNat2 x y p)


lemmaPHKcoraux2 : (pbk : ℕ)(time : Time) (msg₁ : Msg) (sig : ℕ)(s : Stack) (cpRes : ℕ) →
                 liftPred2Maybe (λ s₁ → acceptStateˢ time msg₁ s₁)
                  (p2pkhFunctionDecodedaux1 pbk msg₁ (sig ∷ s) cpRes)
                  → NotFalse (boolToNat (isSigned  msg₁ sig pbk))
lemmaPHKcoraux2 pbk time msg₁ sig s (suc cpRes) p = p


{- This lemma  is actually for the paper 1
   and follows because
    ⟦ scriptP2PKHbas pbkh ⟧stack  =  (λ time msg₁ s → p2pkhFunctionDecoded pbkh msg₁ s)
-}

-- \stackVerificationPtoPKHUsingEqualityOfProgramslemmaPTKHcoraux
--@BEGIN@lemmaPTKHcoraux
lemmaPTKHcoraux : (pbkh : ℕ) →  < weakestPreConditionP2PKH-basis pbkh >stgen
                                (λ time msg₁ s → p2pkhFunctionDecoded pbkh msg₁ s)
                                < acceptStateˢ >
--@END
lemmaPTKHcoraux .(hashFun pbk) .==>stg time msg₁ (pbk ∷ sig ∷ s) (conj refl and4)
      rewrite (lemmaCompareNat (hashFun pbk))
      = boolToNatNotFalseLemma (isSigned  msg₁ sig pbk) and4
lemmaPTKHcoraux pbkh .<==stg time msg₁ (pbk ∷ sig ∷ s) x
    = conj (sym (lemmaCompareNat2 pbkh (hashFun pbk)
                 (lemmaPHKcoraux3 pbk time msg₁ sig s (compareNaturals pbkh (hashFun pbk)) x)))
           (boolToNatNotFalseLemma2 (isSigned  msg₁ sig pbk)
             (lemmaPHKcoraux2 pbk time msg₁ sig s ((compareNaturals pbkh (hashFun pbk))) x))


LemmaPTPKHcor : (pubKeyHash : ℕ)
  →   <  weakestPreConditionP2PKH-basis pubKeyHash >stackb
        scriptP2PKHbas pubKeyHash
      < acceptStateˢ   >
LemmaPTPKHcor pbkh
    = lemmaTransferHoareTripleStack (weakestPreConditionP2PKH-basis pbkh) acceptStateˢ
        (λ time msg s → p2pkhFunctionDecoded pbkh msg s )
        ⟦ scriptP2PKH pbkh ⟧stack
        (λ t m s → sym (p2pkhFunctionDecodedcor t pbkh m s))
        (lemmaPTKHcoraux pbkh)


-- \stackVerificationPtoPKHUsingEqualityOfProgramstheoremPTPKHcor
--@BEGIN@theoremPTPKHcor
theoremPTPKHcor :  (pbkh : ℕ)
                   → < wPreCondP2PKH pbkh >iff scriptP2PKHbas pbkh < acceptState >
--@END
theoremPTPKHcor pbkh =
   hoareTripleStack2HoareTriple (scriptP2PKHbas pbkh)
      (wPreCondP2PKHˢ pbkh) acceptStateˢ (LemmaPTPKHcor pbkh)







-- Some test cases used in the development
-- shows how to check for each step  what the functions are and how they compute

------------------------------------------- Tests ------------------------------------------------------------






{-
  stackfunP2PKHemptyNotCorrectPbkIsNothing : (pubKeyHash : ℕ)(time₁ : Time)(msg₁ : Msg)(stack₁ : State1)
        → ( neg (pubKeyHash ≡ hashFun pbk)  )
        → ⟦ scriptP2PKHbas pubKeyHash ⟧stb time₁ msg₁ (pbk ∷ []) ≡ nothing
  stackfunP2PKHemptyNotCorrectPbkIsNothing pubKeyHash time₁ msg₁ stack₁ = {!!}

-}
