open import basicBitcoinDataType

module guidelines (param : GlobalParameters) where


-- The file guidelines.agda shows the code in the order as it appears in the paper.
-- The authors:  Fahad Alhabardi, Arnold Beckmann, Bogdan Lazar, and Anton Setzer
-- The title of the paper: Verification of Bitcoin’s Smart Contracts in Agda using Weakest Preconditions for Access Control



-- Sect 1 introduction
-- Sect 2 related work



-- Sect 3 Operational Semantics for Bitcoin Script
-- Subsect 3.1 Introduction to Bitcoin Script
-- Subsect 3.2 Operational Semantics

open import instructionBasic
open import semanticBasicOperations param
open import verificationStackScripts.maybeDef
open import verificationStackScripts.semanticsStackInstructions param
open import verificationStackScripts.stackState




-- Sect 4 Hoare Logic, Weakest Preconditions for Security, and Equational Reasoning
-- Subsect 4.1  Weakest Precondition for Security
-- Subsect 4.2  Equational Reasoning with Hoare Triples

open import verificationStackScripts.demoEqualityReasoning param
open import verificationStackScripts.demoEqualityReasoningVers2 param


-- Sect 5 Proof of Correctness of the P2PKH script using the Step by Step Approach

open import verificationStackScripts.stackVerificationP2PKH param
open import stackPredicate
open import verificationP2PKHbasic param




-- Sect 6 Proof of Correctness using Symbolic Execution
-- Subsect 6.1 Example: P2PKH Script

open import verificationStackScripts.stackVerificationP2PKHextractedProgram param
open import verificationStackScripts.stackVerificationP2PKHsymbolicExecutionPaperVersion param
open import verificationStackScripts.stackVerificationP2PKHUsingEqualityOfPrograms param


-- Subsect 6.2 Example: MultiSig Script (P2MS)

open import semanticBasicOperations param     
open import verificationStackScripts.semanticBasicOperationsForTypeSetting param
open import verificationMultiSig param        
open import verificationStackScripts.verificationMultiSigBasicSymbolicExecutionPaper param
open import verificationStackScripts.verificationMultiSigBasic param

-- Subsect 6.3 Example: Combining the two Methods
open import verificationMultiSig param
open import verificationStackScripts.verificationMultiSigBasic param



-- Sect 7 Conclusion





