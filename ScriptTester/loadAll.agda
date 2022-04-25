open import basicBitcoinDataType

module loadAll (param : GlobalParameters) where

-- Loads all files by directory in alphabetic order
-- Alphabetic order is used so that we can easily check that it is complete
-- and therefore by typechecking this file we can guarantee that the complete
-- code is type correct.


open import libraries.andLib
open import libraries.boolLib
open import libraries.emptyLib
open import libraries.equalityLib
open import libraries.listLib
open import libraries.maybeLib
open import libraries.natLib


----------------------
-- Root Directory   --
----------------------


open import exampleBasicData
open import exampleGeneratedWeakPreCond
open import hoareTripleStack param
open import instruction
open import instructionBasic
open import ledger param
open import semanticBasicOperations param
open import stack
open import stackPredicate
open import stackSemanticsInstructions param
open import verificationMultiSig param
open import verificationP2PKHbasic param


----------------------------------------
-- Directory verificationStackScripts --
-----------------------------------------


open import verificationStackScripts.hoareTripleStackBasic param
open import verificationStackScripts.semanticsStackInstructions param
open import verificationStackScripts.sPredicate
open import verificationStackScripts.stackHoareTriple param
open import verificationStackScripts.stackSemanticsInstructionsBasic param
open import verificationStackScripts.stackState
open import verificationStackScripts.stackVerificationLemmas param
open import verificationStackScripts.stackVerificationLemmasPart2 param
open import verificationStackScripts.stackVerificationP2PKH param
open import verificationStackScripts.stackVerificationP2PKHextractedProgram param
open import verificationStackScripts.stackVerificationP2PKHindexed param
open import verificationStackScripts.stackVerificationP2PKHsymbolicExecution param
open import verificationStackScripts.stackVerificationP2PKHUsingEqualityOfPrograms param
open import verificationStackScripts.stackVerificationP2PKHUsingEqualityOfProgramsTest param
open import verificationStackScripts.verificationMultiSigBasic param



----------------------------------------
-- Directory paperTypes2021PostProceed --
-----------------------------------------
open import paperTypes2021PostProceed.demoEqualityReasoning param
open import paperTypes2021PostProceed.maybeDef
open import paperTypes2021PostProceed.semanticBasicOperationsForTypeSetting param
open import paperTypes2021PostProceed.stackVerificationP2PKHsymbolicExecutionPaperVersion param
open import paperTypes2021PostProceed.verificationMultiSigBasicSymbolicExecutionPaper param

