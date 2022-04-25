open import basicBitcoinDataType

module guidelines (param : GlobalParameters) where


-- The file guidelines.agda shows the code in the order as it appears in the paper.
-- The authors:  Fahad F. Alhabardi, Arnold Beckmann, Bogdan Lazar, and Anton Setzer
-- The title of the paper: Verification of Bitcoin Script in Agda using Weakest Preconditions for Access Control


-- Abstract

-- 1. Introduction

-- 2. Related work



-- 3 Operational Semantics for Bitcoin SCRIPT
-- 3.1.  Introduction to Bitcoin SCRIPT
-- 3.2.  Operational Semantics

-- Stack defined in
open import stack

--Time and Msg are defined in
open import basicBitcoinDataType

--StackState defined in
open import verificationStackScripts.stackState

--InstructionBasic and BitcoinScriptBasic are defined in
open import instructionBasic

-- Maybe X defined in
open import paperTypes2021PostProceed.maybeDef

--⟦_⟧ₛˢ defined in
open import verificationStackScripts.stackSemanticsInstructionsBasic param

--executeOpHash, executeStackVerify etc.. defined in
open import semanticBasicOperations param

--⟦ _ ⟧ₛ and ⟦ _ ⟧⁺ are defined in 
open import verificationStackScripts.semanticsStackInstructions param
 

-- 4. Specifying Security of Bitcoin Scripts 
-- 4.1.  Weakest Precondition for Security
-- 4.2.  Formalising Weakest Preconditions in Agda

--StackState defined in
open import verificationStackScripts.stackState

--StackState → Set and acceptState defined in
open import verificationStackScripts.sPredicate

-- _⁺
open import libraries.maybeLib

-- <_>ⁱᶠᶠ_<_>  defined in
open import verificationStackScripts.stackHoareTriple param

--

-- 4.3.  Automatically Generated Weakest Preconditions

open import exampleGeneratedWeakPreCond

-- 4.4.  Equational Reasoning with Hoare Triples

-- <_>ⁱᶠᶠ_<_> and  _<=>ᵖ_ defined in
open import verificationStackScripts.stackHoareTriple param

--proof1, proof2, proof3, proof4, and theorem defined in 
open import paperTypes2021PostProceed.demoEqualityReasoning param


-- 5. Proof of Correctness of the P2PKH script using the Step-by-Step Approach

--scriptP2PKHᵇ, wPreCondP2PKH, accept₁, accept₂, correct-opCheckSig, theoremP2PKH  etc.. defined in
open import verificationStackScripts.stackVerificationP2PKH param

--acceptStateˢ defined in
open import stackPredicate

--wPreCondP2PKHˢ defined in
open import verificationP2PKHbasic param

--acceptState defined in
open import verificationStackScripts.sPredicate


-- 6. Proof of Correctness using Symbolic Execution
-- 6.1. Example: P2PKH Script

--abstrFun etc.. defined in
open import paperTypes2021PostProceed.stackVerificationP2PKHsymbolicExecutionPaperVersion param

--p2pkhFunctionDecoded and p2pkhFunctionDecodedaux1 defined in 
open import verificationStackScripts.stackVerificationP2PKHextractedProgram param

--<_>gˢ_<_> defined in 
open import hoareTripleStack param

--p2pkhFunctionDecodedcor, lemmaPTKHcoraux, and theoremPTPKHcor defined in
open import verificationStackScripts.stackVerificationP2PKHUsingEqualityOfPrograms param


-- 6.2. Example: MultiSig Script (P2MS)

--cmpMultiSigs and cmpMultiSigsAux defined in 
open import paperTypes2021PostProceed.semanticBasicOperationsForTypeSetting param

-- opPushLis and multiSigScriptm-nᵇ defined in 
open import verificationMultiSig param

-- Symbolic execution defined in
open import paperTypes2021PostProceed.verificationMultiSigBasicSymbolicExecutionPaper param


--theoremCorrectnessMultiSig-2-4 and weakestPreConditionMultiSig-2-4 defined in
open import verificationStackScripts.verificationMultiSigBasic param

--stackPred2SPred defined in
open import verificationStackScripts.sPredicate



-- 6.3. Example: Combining the two Methods

--checkTimeScript and timeCheckPreCond defined in 
open import verificationMultiSig param

--theoremCorrectnessTimeChec and theoremCorrectnessCombinedMultiSigTimeChec defined in
open import verificationStackScripts.verificationMultiSigBasic param


-- 7. Practical Usage of Agda

-- 8. Conclusion

--theoremCorrectnessMultiSig-2-4 defined in
open import verificationStackScripts.verificationMultiSigBasic param

-- Bibliography

