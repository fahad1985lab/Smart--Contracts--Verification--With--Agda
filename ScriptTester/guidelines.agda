open import basicBitcoinDataType

module guidelines (param : GlobalParameters) where


-- This file is used for the guidelines code in the paper.
-- The authors:  Fahad Alhabardi, Arnold Beckmann, Bogdan Lazar, and Anton Setzer
-- The title of the paper: Verification of Smart Contracts in Bitcoin in Agda using Weakest Pre-Conditions


-- Sect 1 introduction
-- Sect 2 related work



-- Sect 3 Operational Semantics for Bitcoin Script
-- Subsect 3.1 Introduction to Bitcoin Script
-- Subsect 3.2 Operational Semantics

open import instructionBasic
open import verificationStackScripts.stackState
open import verificationStackScripts.semanticsStackInstructions param
open import semanticBasicOperations param


-- Sect 4 Weakest Preconditions in Hoare Triples for Security
-- Subsect 4.1 Operational Semantics

open import verificationStackScripts.demoEqualityReasoning param


-- Sect 5 Proof of Correctness using Step by Step Approach
-- Subsect 5.1 Example: P2PKH

open import verificationStackScripts.stackVerificationP2PKH param
open import verificationP2PKHbasic param
open import stackPredicate

-- Sect 6 Proof of Correctness using Symbolic Execution

open import verificationStackScripts.stackVerificationP2PKHUsingEqualityOfPrograms param
open import verificationStackScripts.stackVerificationP2PKHsymbolicExecutionPaperVersion param

-- Subsect 6.1 Example: Multisig Script
-- Subsect 6.2 Combined MultiSig Script

open import verificationMultiSig param
open import verificationStackScripts.semanticBasicOperationsForTypeSetting param
open import verificationStackScripts.verificationMultiSigBasicSymbolicExecutionPaper param
open import verificationStackScripts.verificationMultiSigBasic param

-- Sect 7 Conclusion





