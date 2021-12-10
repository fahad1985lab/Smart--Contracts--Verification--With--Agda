open import basicBitcoinDataType

module verificationStackScripts.loadAllStackScripts (param : GlobalParameters) where

open import verificationStackScripts.demoEqualityReasoning param
open import verificationStackScripts.hoareTripleStackBasic param
open import verificationStackScripts.semanticsStackInstructions param
open import verificationStackScripts.sPredicate
open import verificationStackScripts.stackHoareTriple param
open import verificationStackScripts.stackInstruction
open import verificationStackScripts.stackSemanticsInstructionsBasic param
open import verificationStackScripts.stackState
open import verificationStackScripts.stackVerificationLemmas param
open import verificationStackScripts.stackVerificationP2PKH param
open import verificationStackScripts.stackVerificationP2PKHindexed param
open import verificationStackScripts.stackVerificationP2PKHUsingEqualityOfPrograms param
open import verificationStackScripts.verificationMultiSigBasic param