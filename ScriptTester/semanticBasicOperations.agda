open import basicBitcoinDataType

module semanticBasicOperations (param : GlobalParameters) where

open import Data.Nat  hiding (_≤_)
open import Data.List hiding (_++_)
open import Data.Unit  hiding (_≤_)
open import Data.Empty
open import Data.Bool  hiding (_≤_ ; if_then_else_ ) renaming (_∧_ to _∧b_ ; _∨_ to _∨b_ ; T to True)
open import Data.Product renaming (_,_ to _,,_ )
open import Data.Nat.Base hiding (_≤_)
open import Data.Maybe

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; module ≡-Reasoning; sym)
open ≡-Reasoning
open import Agda.Builtin.Equality



open import libraries.listLib
open import libraries.natLib
open import libraries.boolLib
open import libraries.andLib
open import libraries.maybeLib

open import stack

 

hashFun : ℕ → ℕ
hashFun = param .hash



executeOpHash : Stack → Maybe Stack
executeOpHash [] = nothing
executeOpHash (x ∷ s) = just (hashFun x ∷ s)

--operational semantics for opAdd
executeStackAdd : Stack → Maybe Stack
executeStackAdd [] = nothing
executeStackAdd (n ∷ []) = nothing
executeStackAdd (n ∷ m ∷ e) = just ((n + m) ∷ e)


--operational semantics for opVerify
executeStackVerify : Stack → Maybe Stack
executeStackVerify [] = nothing
executeStackVerify (0 ∷ e) = nothing
executeStackVerify (suc n ∷ e) = just (e)


--operational semantics for opEqual
executeStackEquality : Stack → Maybe Stack
executeStackEquality [] = nothing
executeStackEquality (n ∷ []) = nothing
executeStackEquality (n ∷ m ∷ e) = just ((compareNaturals n m)  ∷ e)



--operational semantics for opSwap
executeStackSwap : Stack → Maybe Stack
executeStackSwap [] = nothing
executeStackSwap (x ∷ []) = nothing
executeStackSwap (y ∷ x  ∷ s) = just (x ∷  y  ∷ s)


--operational semantics for opSub
executeStackSub : Stack → Maybe Stack
executeStackSub [] = nothing
executeStackSub (n ∷ []) = nothing
executeStackSub (n ∷ m ∷ e) = just ((n ∸ m) ∷ e)

--operational semantics for opDup
executeStackDup : Stack → Maybe Stack
executeStackDup [] = nothing
executeStackDup (n ∷ ns) = (just (n ∷ n ∷ ns))

--operational semantics for opPush
executeStackPush : ℕ →  Stack → Maybe Stack
executeStackPush n s = just (n ∷ s )

--operational semantics for opDrop
executeStackDrop : Stack → Maybe Stack
executeStackDrop [] = nothing
executeStackDrop (x ∷ s) = just s

--auxiliary function for OpCHECKLOCKTIMEVERIFY
executeOpCHECKLOCKTIMEVERIFYAux : Stack → Bool → Maybe Stack
executeOpCHECKLOCKTIMEVERIFYAux s false = nothing
executeOpCHECKLOCKTIMEVERIFYAux s true = just s


-- operational semantics for OpCHECKLOCKTIMEVERIFY
executeOpCHECKLOCKTIMEVERIFY : (currentTime : Time) → Stack → Maybe Stack
executeOpCHECKLOCKTIMEVERIFY currentTime [] = nothing
executeOpCHECKLOCKTIMEVERIFY currentTime (x ∷ s)
      = executeOpCHECKLOCKTIMEVERIFYAux (x ∷ s) (instructOpTime currentTime x)

-- isSigned refers to pbk and not pbkh since a message can only be checked against pbk
isSigned : (msg : Msg)(s : Signature)(pbk : PublicKey) → Bool
isSigned = param .signed

IsSigned : (msg : Msg)(s : Signature)(pbk : PublicKey) → Set
IsSigned = Signed param


--operational semantics for opCheckSig
executeStackCheckSig : Msg →  Stack → Maybe Stack
executeStackCheckSig msg [] = nothing
executeStackCheckSig msg (x ∷ []) = nothing
-- pbk is on top of sig
executeStackCheckSig msg (pbk ∷ sig ∷ s) = stackAuxFunction s (isSigned msg sig pbk)



--operational semantics for opCheckSig3
executeStackCheckSig3Aux : Msg →  Stack → Maybe Stack
executeStackCheckSig3Aux msg [] = nothing
executeStackCheckSig3Aux mst (x ∷ []) = nothing
executeStackCheckSig3Aux msg (m ∷ k ∷ []) =  nothing
executeStackCheckSig3Aux msg (m ∷ k ∷ x ∷ []) =  nothing
executeStackCheckSig3Aux msg (m ∷ k ∷ x ∷ f ∷ []) =  nothing
executeStackCheckSig3Aux msg (m ∷ k ∷ x ∷ f ∷ l ∷ []) =  nothing
executeStackCheckSig3Aux msg (p1 ∷ p2 ∷ p3 ∷ s1 ∷ s2 ∷ s3 ∷ s) =  stackAuxFunction s
       ((isSigned msg s1 p1 ) ∧b (isSigned msg s2 p2) ∧b (isSigned msg s3 p3))

mutual
  compareSigsMultiSigAux : (msg : Msg)(restSigs restPubKeys : List ℕ)(topSig : ℕ)(testRes : Bool) → Bool

  compareSigsMultiSigAux  msg₁  restSigs  restPubKeys  topSig  false  =  compareSigsMultiSig  msg₁  (topSig ∷ restSigs)  restPubKeys
    -- If the top publicKey doesn't match the topSignature
    -- we throw away the top publicKey, but still need to find a match for the
    -- top publicKey in the remaining signatures
  compareSigsMultiSigAux  msg₁  restSigs  restPubKeys  topSig  true  =  compareSigsMultiSig  msg₁  restSigs               restPubKeys
    -- If the top publicKey matches the topSignature
    -- we need to find matches between the remaining public Keys and signatures

  compareSigsMultiSig : (msg : Msg)(sigs pbks : List ℕ)  → Bool
  compareSigsMultiSig msg []               pubkeys = true    -- all signatures have found a match
                                            -- throw away remaing public keys
  compareSigsMultiSig msg (topSig ∷ sigs) []      = false
                                             -- for topSig we haven't found  a match
  compareSigsMultiSig msg (topSig ∷ sigs) (topPbk ∷ pbks)
        = compareSigsMultiSigAux msg sigs pbks topSig (isSigned msg topSig topPbk)



executeMultiSig3 : (msg : Msg)(pbks : List ℕ)(numSigs : ℕ)(st : Stack)(sigs : List ℕ) → Maybe Stack
executeMultiSig3 msg₁ pbks zero [] sigs = nothing
            -- need to fetch one extra because of a bug in bitcoin definition of MultiSig
executeMultiSig3 msg₁ pbks zero (x ∷ restStack) sigs
     = just (boolToNat (compareSigsMultiSig msg₁ sigs pbks) ∷ restStack)
     -- We have found enough public Keys and signatures to compare
     -- We check using compareSigsMultiSig   whether public Keys match the signatures
     -- and the result is pushed on the stack.
     --
     -- Note that in BitcoinScript the public Keys and signatures need to be in the same order
     --
executeMultiSig3 msg₁ pbks (suc numSigs) [] sigs = nothing
executeMultiSig3 msg₁ pbks (suc numSigs) (sig ∷ rest) sigs = executeMultiSig3 msg₁ pbks numSigs rest (sig ∷ sigs)



executeMultiSig2 : (msg : Msg)(numPbks : ℕ)(st :  Stack)(pbks : List ℕ) → Maybe Stack
executeMultiSig2  msg  _        []                pbks  =  nothing
executeMultiSig2  msg  zero     (numSigs ∷ rest)  pbks  =  executeMultiSig3 msg pbks numSigs rest []
executeMultiSig2  msg  (suc n)  (pbk ∷ rest)      pbks  =  executeMultiSig2 msg n rest (pbk ∷ pbks)


executeMultiSig : Msg →  Stack →  Maybe Stack
executeMultiSig msg [] = nothing
executeMultiSig msg (numberOfPbks ∷ st) = executeMultiSig2 msg numberOfPbks st []

