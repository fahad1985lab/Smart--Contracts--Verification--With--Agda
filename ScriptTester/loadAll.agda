
{- OPTIONS --allow-unsolved-metas #-}
open import basicBitcoinDataType

module loadAll (param : GlobalParameters) where

-- Loads all files by directory in alphabetic order
--    other loadAll files are not loaded
-- Alphabetic order is used so that we can easily check that it is complete
-- and therefore by typechecking this file we can guarantee that the complete
-- code is type correct.


-- The file
-- loadStackVersionInNaturalOrder
-- will load the files which are not using the IfStack in a more natural order
-- so for studying this code use this file and a file
--   to be defined for the IfStack
--


open import libraries.andLib
open import libraries.boolLib
open import libraries.emptyLib
open import libraries.equalityLib
open import libraries.finLib
open import libraries.listLib
open import libraries.maybeLib
open import libraries.miscLib
open import libraries.natLib


----------------------
-- Root Directory   --
----------------------

-- open import basicBitcoinDataType  -- (was already imported before the module)
open import exampleBasicData
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

open import verificationStackScripts.demoEqualityReasoning param
open import verificationStackScripts.demoEqualityReasoningVers2 param
open import verificationStackScripts.hoareTripleStackBasic param
open import verificationStackScripts.maybeDef
open import verificationStackScripts.semanticBasicOperationsForTypeSetting param
open import verificationStackScripts.semanticsStackInstructions param
open import verificationStackScripts.sPredicate
open import verificationStackScripts.stackHoareTriple param
open import verificationStackScripts.stackInstruction
open import verificationStackScripts.stackSemanticsInstructionsBasic param
open import verificationStackScripts.stackState
open import verificationStackScripts.stackVerificationLemmas param
open import verificationStackScripts.stackVerificationLemmasPart2 param
open import verificationStackScripts.stackVerificationP2PKH param
open import verificationStackScripts.stackVerificationP2PKHextractedProgram param
open import verificationStackScripts.stackVerificationP2PKHindexed param
open import verificationStackScripts.stackVerificationP2PKHsymbolicExecution param
open import verificationStackScripts.stackVerificationP2PKHsymbolicExecutionPaperVersion param
open import verificationStackScripts.stackVerificationP2PKHsymbolicExecutionPaperVersionPart2 param
open import verificationStackScripts.stackVerificationP2PKHUsingEqualityOfPrograms param
open import verificationStackScripts.stackVerificationP2PKHUsingEqualityOfProgramsTest param
open import verificationStackScripts.verificationMultiSigBasic param
open import verificationStackScripts.verificationMultiSigBasicEqualityOfProgram param
open import verificationStackScripts.verificationMultiSigBasicSymbolicExecution param
open import verificationStackScripts.verificationMultiSigBasicSymbolicExecutionPaper param
open import verificationStackScripts.verificationMultiSigBasicSymbolicExecutionPaperVersion param
