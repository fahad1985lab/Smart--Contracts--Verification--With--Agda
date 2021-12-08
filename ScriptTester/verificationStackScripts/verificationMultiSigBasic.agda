--@PREFIX@verificationMultiSigBasic
--\verificationMultiSigBasic
open import basicBitcoinDataType

module verificationStackScripts.verificationMultiSigBasic (param : GlobalParameters) where


open import Data.List.Base hiding (_++_ )
open import Data.Nat  renaming (_≤_ to _≤'_ ; _<_ to _<'_)
open import Data.List hiding (_++_  )
open import Data.Sum
open import Data.Unit  hiding (_≤_)
open import Data.Empty
open import Data.Maybe
open import Data.Bool  hiding (_≤_ ; _<_ ; if_then_else_  )  renaming (_∧_ to _∧b_ ; _∨_ to _∨b_ ; T to True)
open import Data.Product renaming (_,_ to _,,_ )
open import Data.Nat.Base hiding (_≤_ ; _<_)
open import Data.List.NonEmpty hiding (head; [_])
open import Data.Nat using (ℕ; _+_; _≥_; _>_; zero; suc; s≤s; z≤n)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; module ≡-Reasoning; sym)
open ≡-Reasoning
open import Agda.Builtin.Equality


--our libraries
open import libraries.listLib
open import libraries.emptyLib
open import libraries.natLib
open import libraries.boolLib
open import libraries.equalityLib
open import libraries.andLib
open import libraries.miscLib
open import libraries.maybeLib

open import stack
open import stackPredicate
open import semanticBasicOperations param
open import instructionBasic
open import verificationMultiSig param
open import hoareTripleStack param
open import verificationStackScripts.semanticsStackInstructions param
open import verificationStackScripts.stackVerificationLemmas param
open import verificationStackScripts.stackHoareTriple param
open import verificationStackScripts.sPredicate
open import verificationStackScripts.hoareTripleStackBasic param
open import verificationStackScripts.stackState
open import verificationStackScripts.stackSemanticsInstructionsBasic param
open import verificationStackScripts.stackVerificationLemmasPart2 param
open import verificationStackScripts.stackVerificationP2PKH param

mainLemmaCorrectnessMultiSig-2-4 : (msg₁ : Msg)(pbk1 pbk2 pbk3 pbk4  : ℕ) →
                   < weakestPreConditionMultiSig-2-4-bas pbk1 pbk2 pbk3 pbk4 >stackb
                    multiSigScript-2-4-b pbk1 pbk2 pbk3 pbk4
                  < acceptStateˢ >
mainLemmaCorrectnessMultiSig-2-4 msg₁ pbk1 pbk2 pbk3 pbk4 .==>stg time msg₂ (sig2 ∷ sig1 ∷ dummy ∷ stack)
  (inj₁ (conj and3 and4)) =
   boolToNatNotFalseLemma (compareSigsMultiSigAux msg₂ (sig2 ∷ []) (pbk2 ∷ pbk3 ∷ pbk4 ∷ []) sig1
   (isSigned  msg₂ sig1 pbk1))
  (lemmaHoareTripleStackGeAux'7 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 and3 and4)
mainLemmaCorrectnessMultiSig-2-4 msg₁ pbk1 pbk2 pbk3 pbk4 .==>stg time msg₂ (sig2 ∷ sig1 ∷ dummy ∷ stack)
  (inj₂ (inj₁ (conj and3 and4))) =
   boolToNatNotFalseLemma (compareSigsMultiSigAux msg₂ (sig2 ∷ []) (pbk2 ∷ pbk3 ∷ pbk4 ∷ []) sig1
   (isSigned  msg₂ sig1 pbk1))
  (lemmaHoareTripleStackGeAux'8 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 and3 and4)
mainLemmaCorrectnessMultiSig-2-4 msg₁ pbk1 pbk2 pbk3 pbk4 .==>stg time msg₂ (sig2 ∷ sig1 ∷ dummy ∷ stack)
  (inj₂ (inj₂ (inj₁ (conj and3 and4)))) =
   boolToNatNotFalseLemma (compareSigsMultiSigAux msg₂ (sig2 ∷ []) (pbk2 ∷ pbk3 ∷ pbk4 ∷ []) sig1
   (isSigned  msg₂ sig1 pbk1))
   (lemmaHoareTripleStackGeAux'9 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 and3 and4)
mainLemmaCorrectnessMultiSig-2-4 msg₁ pbk1 pbk2 pbk3 pbk4 .==>stg time msg₂ (sig2 ∷ sig1 ∷ dummy ∷ stack)
  (inj₂ (inj₂ (inj₂ (inj₁ (conj and3 and4))))) =
   boolToNatNotFalseLemma (compareSigsMultiSigAux msg₂ (sig2 ∷ []) (pbk2 ∷ pbk3 ∷ pbk4 ∷ []) sig1
   (isSigned  msg₂ sig1 pbk1))
   (lemmaHoareTripleStackGeAux'10 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 and3 and4)
mainLemmaCorrectnessMultiSig-2-4 msg₁ pbk1 pbk2 pbk3 pbk4 .==>stg time msg₂ (sig2 ∷ sig1 ∷ dummy ∷ stack)
  (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (conj and3 and4)))))) =
   boolToNatNotFalseLemma (compareSigsMultiSigAux msg₂ (sig2 ∷ []) (pbk2 ∷ pbk3 ∷ pbk4 ∷ []) sig1
   (isSigned  msg₂ sig1 pbk1))
   (lemmaHoareTripleStackGeAux'11 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 and3 and4)
mainLemmaCorrectnessMultiSig-2-4 msg₁ pbk1 pbk2 pbk3 pbk4 .==>stg time msg₂ (sig2 ∷ sig1 ∷ dummy ∷ stack)
  (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (conj and3 and4)))))) =
   boolToNatNotFalseLemma (compareSigsMultiSigAux msg₂ (sig2 ∷ []) (pbk2 ∷ pbk3 ∷ pbk4 ∷ []) sig1
   (isSigned  msg₂ sig1 pbk1))
   (lemmaHoareTripleStackGeAux'12 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 and3 and4)
mainLemmaCorrectnessMultiSig-2-4 msg₁ pbk1 pbk2 pbk3 pbk4 .<==stg time msg₂  (sig2 ∷ sig1 ∷ dummy ∷ stack) x =
  lemmaHoareTripleStackGeAux'Comb2-4 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2
  (boolToNatNotFalseLemma2 (compareSigsMultiSigAux msg₂ (sig2 ∷ []) (pbk2 ∷ pbk3 ∷ pbk4 ∷ [])
  sig1 (isSigned  msg₂ sig1 pbk1)) x)


weakestPreConditionMultiSig-2-4 : (pbk1 pbk2 pbk3 pbk4 :  ℕ)→ StackStatePred
weakestPreConditionMultiSig-2-4 pbk1 pbk2 pbk3 pbk4 = stackPred2SPred (weakestPreConditionMultiSig-2-4-bas pbk1 pbk2 pbk3 pbk4)





-- Main theorem for multisig-2-4
--\verificationMultiSigBasictheoremCorrectnessMultiSigTwoFour
--@BEGIN@theoremCorrectnessMultiSigTwoFour
theoremCorrectnessMultiSig-2-4 : (pbk1 pbk2 pbk3 pbk4 :  ℕ)
                                 → < weakestPreConditionMultiSig-2-4 pbk1 pbk2 pbk3 pbk4  >iff
                                    multiSigScript-2-4-b pbk1 pbk2 pbk3 pbk4
                                    < stackPred2SPred acceptStateˢ  >
--@END
theoremCorrectnessMultiSig-2-4 pbk1 pbk2 pbk3 pbk4
                          = hoareTripleStack2HoareTriple (multiSigScript-2-4-b pbk1 pbk2 pbk3 pbk4)
                          (weakestPreConditionMultiSig-2-4-bas pbk1 pbk2 pbk3 pbk4 ) acceptStateˢ
                          (mainLemmaCorrectnessMultiSig-2-4 (nat pbk4) pbk1 pbk2 pbk3 pbk4)
--@END


-------------------------------------------------------------
--  Here we prove the correctness of a combined script
--  namely the correctness of a combination of a check time script and themultisig script
--
-- This demonstrates a combination of method1 and method 2:
--  we prove the correctness of the time script and the multisig script separately (the time script is trivial to verify)
--    using  method 2
-- Then we prove the correctenss of the combined script using method1
--    and this shows that we can make bigger jumps in method 1
-------------------------------
--\verificationMultiSigBasictheoremCorrectnessTimeCheck
--@BEGIN@theoremCorrectnessTimeCheck
theoremCorrectnessTimeCheck : (φ : StackPredicate)(time₁ : Time)
   →   <  stackPred2SPred (timeCheckPreCond time₁ ∧sp φ)   >iff
        checkTimeScript-b time₁
        <  stackPred2SPred φ   >
--@END
theoremCorrectnessTimeCheck φ time₁ .==> ⟨ currentTime₁ , msg₁ , stack₁ ⟩ (conj and3 and4) with (currentTime₁ ≤b time₁)
theoremCorrectnessTimeCheck φ time₁ .==> ⟨ currentTime₁ , msg₁ , stack₁ ⟩ (conj and3 and4) | true = and4
theoremCorrectnessTimeCheck φ time₁ .<== ⟨ currentTime₁ , msg₁ , stack₁ ⟩ p with (currentTime₁ ≤b time₁)
theoremCorrectnessTimeCheck φ time₁ .<== ⟨ currentTime₁ , msg₁ , stack₁ ⟩ p | true = conj tt p


--\verificationMultiSigBasictheoremCorrectnessCombinedMultiSigTimeCheck
--@BEGIN@theoremCorrectnessCombinedMultiSigTimeCheck
theoremCorrectnessCombinedMultiSigTimeCheck : (time₁ : Time) (pbk1 pbk2 pbk3 pbk4 :  ℕ)
   →   < stackPred2SPred (  timeCheckPreCond time₁ ∧sp
                             weakestPreConditionMultiSig-2-4-bas  pbk1 pbk2 pbk3 pbk4) >iff
        checkTimeScript-b time₁ ++ multiSigScript-2-4-b pbk1 pbk2 pbk3 pbk4
        < acceptState >
theoremCorrectnessCombinedMultiSigTimeCheck time₁ pbk1 pbk2 pbk3 pbk4 =
  stackPred2SPred (timeCheckPreCond time₁ ∧sp
     weakestPreConditionMultiSig-2-4-bas  pbk1 pbk2 pbk3 pbk4)
           <><>⟨  checkTimeScript-b time₁  ⟩⟨  theoremCorrectnessTimeCheck
                  (weakestPreConditionMultiSig-2-4-bas pbk1 pbk2 pbk3 pbk4) time₁  ⟩
  stackPred2SPred (weakestPreConditionMultiSig-2-4-bas pbk1 pbk2 pbk3 pbk4)
           <><>⟨ multiSigScript-2-4-b pbk1 pbk2 pbk3 pbk4
                 ⟩⟨ theoremCorrectnessMultiSig-2-4 pbk1 pbk2 pbk3 pbk4   ⟩e
  stackPred2SPred acceptStateˢ ∎p
--@END
