open import basicBitcoinDataType

module verificationStackScripts.stackVerificationP2PKHindexed (param : GlobalParameters) where

open import Data.Nat  renaming (_≤_ to _≤'_ ; _<_ to _<'_)
open import Data.List hiding (_++_)
open import Data.Unit  hiding (_≤_)
open import Data.Empty
open import Data.Bool  hiding   (_≤_ ; _<_ ; if_then_else_ )
                       renaming (_∧_ to _∧b_ ; _∨_ to _∨b_ ; T to True)
open import Data.Product renaming (_,_ to _,,_ )
open import Data.List.NonEmpty hiding (head )
open import Data.Nat using (ℕ; _+_; _≥_; _>_; zero; suc; s≤s; z≤n)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; module ≡-Reasoning; sym)
open ≡-Reasoning
open import Agda.Builtin.Equality


--our libraries
open import libraries.andLib
open import libraries.maybeLib
open import libraries.boolLib
open import libraries.listLib
open import libraries.natLib

open import stack
open import stackPredicate
open import semanticBasicOperations param
open import instructionBasic
open import verificationP2PKHbasic param
open import verificationStackScripts.stackState
open import verificationStackScripts.sPredicate
open import verificationStackScripts.semanticsStackInstructions param
open import verificationStackScripts.stackVerificationLemmas param
open import verificationStackScripts.stackHoareTriple param
open import verificationStackScripts.stackVerificationP2PKH param


instructions : (pubKeyHash : ℕ) (n : ℕ) → n ≤ 5 → InstructionBasic
instructions pubKeyHash 0 _ = opCheckSig
instructions pubKeyHash 1 _ = opVerify
instructions pubKeyHash 2 _ = opEqual
instructions pubKeyHash 3 _ = opPush pubKeyHash
instructions pubKeyHash 4 _ = opHash
instructions pubKeyHash 5 _ = opDup



script : (pubKeyHash : ℕ) (n : ℕ) → n ≤ 6 → BitcoinScriptBasic
script pubKeyHash 0 _ = []
script pubKeyHash (suc n) n≤6
   = instructions pubKeyHash n  n≤6 ∷ script pubKeyHash  n (leqSucLemma n 5 n≤6)


script' : (pubKeyHash : ℕ) (n : ℕ) → n ≤ 6 → BitcoinScriptBasic
script' pubKeyHash 0 _ = []
script' pubKeyHash (suc n) n≤6
   = (instructions pubKeyHash n  n≤6 ∷ [] ) ++ script' pubKeyHash  n (leqSucLemma n 5 n≤6)


conditionBasic : (pubKeyHash : ℕ)  (n : ℕ) → n ≤ 6 → StackPredicate
conditionBasic pubKeyHash 0 _ = acceptStateˢ
conditionBasic pubKeyHash 1 _ = accept₁ˢ
conditionBasic pubKeyHash 2 _ = accept₂ˢ
conditionBasic pubKeyHash 3 _ = accept₃ˢ
conditionBasic pubKeyHash 4 _ = accept₄ˢ pubKeyHash
conditionBasic pubKeyHash 5 _ = accept₅ˢ pubKeyHash
conditionBasic pubKeyHash 6 _ = wPreCondP2PKHˢ pubKeyHash

condition : (pubKeyHash : ℕ)  (n : ℕ) → n ≤ 6 → (s : StackState) → Set
condition pubKeyHash n n≤6 = stackPred2SPred (conditionBasic pubKeyHash n n≤6)


correct-opCheckSig-to' : (s : StackState) → accept₁ s
                →  (acceptState ⁺) (⟦ opCheckSig ⟧ₛ s)
correct-opCheckSig-to' ⟨ time , msg₁ , pubKey  ∷ sig ∷ st  ⟩ a
     = boolToNatNotFalseLemma (isSigned  msg₁ sig pubKey) a




correct-opCheckSig-from' : (s : StackState)
                 →  (acceptState ⁺) (⟦ opCheckSig ⟧ₛ s)
                 → accept₁ s
correct-opCheckSig-from' ⟨ time , msg₁ , pubKey ∷ sig ∷ stack₁ ⟩ a
        = boolToNatNotFalseLemma2 (isSigned  msg₁ sig pubKey) a



correctStep-to  : (pubKeyHash : ℕ)  (n : ℕ) (n≤5 : n ≤ 5)
  (s : StackState)
  → condition pubKeyHash (suc n) n≤5 s
  → ( (condition pubKeyHash n (leqSucLemma n 5 n≤5)) ⁺)
                    (⟦ instructions pubKeyHash n n≤5 ⟧ₛ s)
correctStep-to pubKeyHash 0 _ = correct-opCheckSig-to'
correctStep-to pubKeyHash 1 _ = correct-opVerify-to
correctStep-to pubKeyHash 2 _ = correct-opEqual-to
correctStep-to pubKeyHash 3 _ = correct-opPush-to pubKeyHash
correctStep-to pubKeyHash 4 _ = correct-opHash-to pubKeyHash
correctStep-to pubKeyHash 5 _ = correct-opDup-to pubKeyHash


correctStep-from :  (pubKeyHash : ℕ)  (n : ℕ)(n≤5 : n ≤ 5)(s : StackState)
    → ( (condition pubKeyHash n (leqSucLemma n 5 n≤5)) ⁺)
                        (⟦ instructions pubKeyHash n n≤5 ⟧ₛ s)
    → condition pubKeyHash (suc n) n≤5 s
correctStep-from pubKeyHash 0 _ = correct-opCheckSig-from'
correctStep-from pubKeyHash 1 _ =  correct-opVerify-from
correctStep-from pubKeyHash 2 _ = correct-opEqual-from
correctStep-from pubKeyHash 3 _ = correct-opPush-from pubKeyHash
correctStep-from pubKeyHash 4 _ = correct-opHash-from pubKeyHash
correctStep-from pubKeyHash 5 _ = correct-opDup-from pubKeyHash






correct-from : (pubKeyHash : ℕ) (n : ℕ)  (n≤6 : n ≤ 6)(s : StackState)
               → (acceptState ⁺) ( ⟦ script pubKeyHash n n≤6 ⟧ s)
               → condition pubKeyHash n n≤6 s
correct-from pubKeyHash 0 n≤6 s st
       = emptyProgramCorrect-from (condition pubKeyHash 0 tt) s st
correct-from pubKeyHash (suc n) n≤6 s st
       = bindTransformer-fromSingle
         (condition pubKeyHash (suc n) n≤6)
         (condition pubKeyHash n (leqSucLemma n 5 n≤6))
         acceptState
         (instructions pubKeyHash n n≤6)
         (script pubKeyHash n (leqSucLemma n 5 n≤6))
         (correctStep-from pubKeyHash n n≤6)
         (correct-from pubKeyHash n (leqSucLemma n 5 n≤6)) s st

correct-to  : (pubKeyHash : ℕ)  (n : ℕ) (n≤6 : n ≤ 6)(s : StackState)
           → condition pubKeyHash n n≤6 s
           → (acceptState ⁺) (⟦ script pubKeyHash n n≤6 ⟧ s)
correct-to pubKeyHash 0 n≤6 = emptyProgramCorrect-to (condition pubKeyHash 0 tt)
correct-to pubKeyHash (suc n) n≤6 = bindTransformer-toSingle (condition pubKeyHash (suc n) n≤6)
     (condition pubKeyHash n (leqSucLemma n 5 n≤6)) acceptState
     (instructions pubKeyHash n n≤6)
     (script pubKeyHash n (leqSucLemma n 5 n≤6))
     (correctStep-to pubKeyHash n n≤6)
     (correct-to pubKeyHash n (leqSucLemma n 5 n≤6))





completeCorrect-1-to : (s : StackState) → accept₁ s
     →  (acceptState ⁺) (⟦ script-1-b ⟧ s)
completeCorrect-1-to ⟨ time , msg₁ , pubKey  ∷ sig ∷ st ⟩ n≤6
     = boolToNatNotFalseLemma (isSigned  msg₁ sig pubKey) n≤6


completeCorrect-1-from : (s : StackState)
                         → (acceptState ⁺) (⟦ script-1-b ⟧ s )
                         → accept₁ s
completeCorrect-1-from ⟨ time , msg₁ , pubKey ∷ sig ∷ stack₁ ⟩ n≤6
         = boolToNatNotFalseLemma2 (isSigned  msg₁ sig pubKey) n≤6


completeCorrect-2-to : (s : StackState) → accept₂ s
                      →  (acceptState ⁺) (⟦ script-2-b ⟧ s)
completeCorrect-2-to  s a
    = bindTransformer-toSingle accept₂ accept₁ acceptState instruction-2
      script-1-b correct-opVerify-to completeCorrect-1-to  s a


completeCorrect-2-from : (s : StackState) →  (acceptState ⁺) (⟦ script-2-b ⟧ s) → accept₂ s
completeCorrect-2-from  s a =
                 bindTransformer-fromSingle accept₂ accept₁
                 acceptState instruction-2 script-1-b correct-opVerify-from
                  completeCorrect-1-from  s a



completeCorrect-3-to : (s : StackState) → accept₃ s →  (acceptState ⁺) (⟦ script-3-b ⟧ s)
completeCorrect-3-to  s a =
                 bindTransformer-toSingle accept₃ accept₂
                 acceptState instruction-3 script-2-b correct-opEqual-to
                  completeCorrect-2-to s a


completeCorrect-3-from : (s : StackState) →  (acceptState ⁺) (⟦ script-3-b ⟧ s) → accept₃ s
completeCorrect-3-from  s a =
                 bindTransformer-fromSingle accept₃ accept₂
                 acceptState instruction-3 script-2-b correct-opEqual-from
                  completeCorrect-2-from  s a


completeCorrect-4-to : (pubKeyHash : ℕ )(s : StackState) → accept₄ pubKeyHash s
                     →  (acceptState ⁺) (⟦ script-4-b pubKeyHash ⟧ s)
completeCorrect-4-to pubKeyHash s a  =
                 bindTransformer-toSingle (accept₄ pubKeyHash) accept₃
                 acceptState (instruction-4 pubKeyHash) script-3-b (correct-opPush-to pubKeyHash)
                  completeCorrect-3-to s a



completeCorrect-4-from :(pubKeyHash : ℕ )(s : StackState) →  (acceptState ⁺) (⟦ script-4-b pubKeyHash ⟧ s)
                       → accept₄ pubKeyHash s
completeCorrect-4-from pubKeyHash s a =
                 bindTransformer-fromSingle (accept₄ pubKeyHash) accept₃
                 acceptState (instruction-4 pubKeyHash) script-3-b (correct-opPush-from pubKeyHash)
                  completeCorrect-3-from s a


completeCorrect-5-to : (pubKeyHash : ℕ )(s : StackState) → accept₅ pubKeyHash s
                      →  (acceptState ⁺) (⟦ script-5-b pubKeyHash ⟧ s)
completeCorrect-5-to pubKeyHash s a  =
                 bindTransformer-toSingle (accept₅ pubKeyHash) (accept₄ pubKeyHash)
                 acceptState instruction-5 (script-4-b pubKeyHash) (correct-opHash-to pubKeyHash)
                      (completeCorrect-4-to pubKeyHash) s  a



completeCorrect-5-from :(pubKeyHash : ℕ )(s : StackState) →  (acceptState ⁺) (⟦ script-5-b pubKeyHash ⟧ s)
                      → accept₅ pubKeyHash s
completeCorrect-5-from pubKeyHash s a =
                   bindTransformer-fromSingle (accept₅ pubKeyHash) (accept₄ pubKeyHash)
                   acceptState instruction-5 (script-4-b pubKeyHash) (correct-opHash-from pubKeyHash)
                     (completeCorrect-4-from  pubKeyHash) s a



completecorrect-6-to : (pubKeyHash : ℕ ) → (s : StackState) → wPreCondP2PKH pubKeyHash s
                     →  (acceptState ⁺) (⟦ script-6-b pubKeyHash ⟧ s )
completecorrect-6-to pubKeyHash s a =
                  bindTransformer-toSingle (wPreCondP2PKH pubKeyHash) (accept₅ pubKeyHash)
                  acceptState instruction-6 (script-5-b pubKeyHash) (correct-opDup-to pubKeyHash)
                   (completeCorrect-5-to pubKeyHash) s a




completeCorrect-6-from :(pubKeyHash : ℕ )(s : StackState) →  (acceptState ⁺) (⟦ script-6-b pubKeyHash ⟧ s)
                    → wPreCondP2PKH pubKeyHash s
completeCorrect-6-from pubKeyHash s a =
                  bindTransformer-fromSingle (wPreCondP2PKH pubKeyHash) (accept₅ pubKeyHash)
                  acceptState instruction-6 (script-5-b pubKeyHash) (correct-opDup-from pubKeyHash)
                   (completeCorrect-5-from  pubKeyHash) s a




instructionSequence : (pubKeyHash : ℕ) (n : ℕ) → n ≤ 5 → BitcoinScriptBasic
instructionSequence pubKeyHash n n≤6 = instructions pubKeyHash n n≤6 ∷ []



scriptSequence : (pubKeyHash : ℕ) (n : ℕ) → n ≤ 6 → BitcoinScriptBasic
scriptSequence pubKeyHash 0 _ = []
scriptSequence pubKeyHash (suc n) n≤6 = instructionSequence pubKeyHash n  n≤6 ++ scriptSequence pubKeyHash  n (leqSucLemma n 5 n≤6)





correctStep-toSequence'  : (pubKeyHash : ℕ)  (n : ℕ) → (n≤6 : n ≤ 5)
               (s : StackState) → condition pubKeyHash (suc n) n≤6 s
                            → ((condition pubKeyHash n (leqSucLemma n 5 n≤6)) ⁺)
                                              (⟦ instructionSequence pubKeyHash n n≤6 ⟧ s)
correctStep-toSequence' pubKeyHash 0 _  = liftCondOperation2Program-to (condition pubKeyHash 1 tt)
                                              (condition pubKeyHash 0 tt) (instructions pubKeyHash 0 tt)
                                              correct-opCheckSig-to'
correctStep-toSequence' pubKeyHash 1 _ = liftCondOperation2Program-to (condition pubKeyHash 2 tt)
                                              (condition pubKeyHash 1 tt) (instructions pubKeyHash 1 tt)
                                              correct-opVerify-to
correctStep-toSequence' pubKeyHash 2 _ = liftCondOperation2Program-to (condition pubKeyHash 3 tt)
                                              (condition pubKeyHash 2 tt) (instructions pubKeyHash 2 tt)
                                              correct-opEqual-to
correctStep-toSequence' pubKeyHash 3 _ = liftCondOperation2Program-to (condition pubKeyHash 4 tt)
                                              (condition pubKeyHash 3 tt) (instructions pubKeyHash 3 tt)
                                              (correct-opPush-to pubKeyHash)
correctStep-toSequence' pubKeyHash 4 _ = liftCondOperation2Program-to (condition pubKeyHash 5 tt)
                                              (condition pubKeyHash 4 tt) (instructions pubKeyHash 4 tt)
                                              (correct-opHash-to pubKeyHash)
correctStep-toSequence' pubKeyHash 5 _ = liftCondOperation2Program-to (condition pubKeyHash 6 tt)
                                              (condition pubKeyHash 5 tt) (instructions pubKeyHash 5 tt)
                                              (correct-opDup-to pubKeyHash)




correctStep-FromSequence'  : (pubKeyHash : ℕ)  (n : ℕ) → (n≤6 : n ≤ 5)
                        (s : StackState) → ( (condition pubKeyHash n (leqSucLemma n 5 n≤6)) ⁺) (⟦ instructionSequence pubKeyHash n n≤6 ⟧ s)
                                  → condition pubKeyHash (suc n) n≤6 s

correctStep-FromSequence' pubKeyHash 0 _ = liftCondOperation2Program-from (condition pubKeyHash 1 tt)
                                              (condition pubKeyHash 0 tt) (instructions pubKeyHash 0 tt)
                                               correct-opCheckSig-from'
correctStep-FromSequence' pubKeyHash 1 _ = liftCondOperation2Program-from (condition pubKeyHash 2 tt)
                                              (condition pubKeyHash 1 tt) (instructions pubKeyHash 1 tt)
                                               correct-opVerify-from
correctStep-FromSequence' pubKeyHash 2 _ = liftCondOperation2Program-from (condition pubKeyHash 3 tt)
                                              (condition pubKeyHash 2 tt) (instructions pubKeyHash 2 tt)
                                               correct-opEqual-from
correctStep-FromSequence' pubKeyHash 3 _ = liftCondOperation2Program-from (condition pubKeyHash 4 tt)
                                              (condition pubKeyHash 3 tt) (instructions pubKeyHash 3 tt)
                                               (correct-opPush-from pubKeyHash)
correctStep-FromSequence' pubKeyHash 4 _ = liftCondOperation2Program-from (condition pubKeyHash 5 tt)
                                               (condition pubKeyHash 4 tt) (instructions pubKeyHash 4 tt)
                                               (correct-opHash-from  pubKeyHash)
correctStep-FromSequence' pubKeyHash 5 _ = liftCondOperation2Program-from (condition pubKeyHash 6 tt)
                                               (condition pubKeyHash 5 tt) (instructions pubKeyHash 5 tt)
                                               (correct-opDup-from pubKeyHash)




correct-toSequence  : (pubKeyHash : ℕ)  (n : ℕ) (n≤6 : n ≤ 6)(s : StackState)
           → condition pubKeyHash n n≤6 s
           → (acceptState ⁺) (⟦ scriptSequence pubKeyHash n n≤6 ⟧ s)
correct-toSequence pubKeyHash 0 n≤6 = emptyProgramCorrect-to (condition pubKeyHash 0 tt)
correct-toSequence pubKeyHash (suc n) n≤6 = bindTransformer-toSequence ( (condition pubKeyHash (suc n) n≤6))
                                                       ( (condition pubKeyHash n (leqSucLemma n 5 n≤6)))  acceptState
                                                       ((instructionSequence pubKeyHash n n≤6)) (scriptSequence  pubKeyHash n (leqSucLemma n 5 n≤6))
                                                       (correctStep-toSequence' pubKeyHash n n≤6)
                                                       (correct-toSequence pubKeyHash n (leqSucLemma n 5 n≤6))



correct-fromSequence  : (pubKeyHash : ℕ)  (n : ℕ) (n≤6 : n ≤ 6)(s : StackState)
             → (acceptState ⁺) (⟦ scriptSequence pubKeyHash n n≤6 ⟧ s)
            → condition pubKeyHash n n≤6 s
correct-fromSequence pubKeyHash zero n≤6 s st =  emptyProgramCorrect-from (condition pubKeyHash 0 tt) s st
correct-fromSequence pubKeyHash (suc n) n≤6 s st =
                      bindTransformer-fromSequence (condition pubKeyHash (suc n) n≤6)
                      (condition pubKeyHash n (leqSucLemma n 5 n≤6)) acceptState
                      (instructionSequence pubKeyHash n n≤6) (scriptSequence pubKeyHash n (leqSucLemma n 5 n≤6))
                      (correctStep-FromSequence' pubKeyHash n n≤6) (correct-fromSequence pubKeyHash n (leqSucLemma n 5 n≤6)) s st



weakestPreConditionP2PKH : (pubKeyHash : ℕ) (s : StackState) → Set
weakestPreConditionP2PKH pubKeyHash = stackPred2SPred (wPreCondP2PKHˢ pubKeyHash)

correctComplete-from : (pubKeyHash : ℕ)(s : StackState)
         → (acceptState ⁺) (⟦ script-6-b pubKeyHash ⟧ s)
         → weakestPreConditionP2PKH pubKeyHash s
correctComplete-from pubKeyHash = correct-from pubKeyHash 6 tt

correctComplete-to : (pubKeyHash : ℕ)(s : StackState) → weakestPreConditionP2PKH pubKeyHash s
                  → (acceptState ⁺) (⟦ script-6-b pubKeyHash ⟧ s)
correctComplete-to pubKeyHash = correct-to pubKeyHash 6 tt

correctnessP2PKH : (pubKeyHash : ℕ)
                   → <  weakestPreConditionP2PKH pubKeyHash >ⁱᶠᶠ
                      scriptP2PKHᵇ pubKeyHash
                     < acceptState  >
correctnessP2PKH pubKeyHash .==> = correctComplete-to   pubKeyHash
correctnessP2PKH pubKeyHash .<== = correctComplete-from pubKeyHash
