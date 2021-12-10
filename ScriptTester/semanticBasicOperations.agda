open import basicBitcoinDataType

module semanticBasicOperations (param : GlobalParameters) where

open import Data.Nat  hiding (_≤_)
open import Data.List hiding (_++_)
open import Data.Unit  hiding (_≤_)
open import Data.Empty
open import Data.Bool  hiding (_≤_ ; if_then_else_ ) renaming (_∧_ to _∧b_ ; _∨_ to _∨b_ ; T to True)
open import Data.Product renaming (_,_ to _,,_ )
open import Data.Nat.Base hiding (_≤_)
-- open import Data.List.NonEmpty hiding (head)
open import Data.Maybe

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; module ≡-Reasoning; sym)
open ≡-Reasoning
open import Agda.Builtin.Equality
--open import Agda.Builtin.Equality.Rewrite


open import libraries.listLib
open import libraries.natLib
open import libraries.boolLib
open import libraries.andLib
open import libraries.miscLib
open import libraries.maybeLib

open import stack


--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

hashFun : ℕ → ℕ
hashFun = param .hash


-- executeOpHash : Msg → Stack → Maybe Stack
executeOpHash : Stack → Maybe Stack
executeOpHash [] = nothing
executeOpHash (x ∷ s) = just (hashFun x ∷ s)

--function for opAdd
executeStackAdd : Stack → Maybe Stack
executeStackAdd [] = nothing
executeStackAdd (n ∷ []) = nothing
executeStackAdd (n ∷ m ∷ e) = just ((n + m) ∷ e)


--function for opVerify
executeStackVerify : Stack → Maybe Stack
executeStackVerify [] = nothing
executeStackVerify (0 ∷ e) = nothing
executeStackVerify (suc n ∷ e) = just (e)


--function for opEqual
executeStackEquality : Stack → Maybe Stack
executeStackEquality [] = nothing
executeStackEquality (n ∷ []) = nothing
executeStackEquality (n ∷ m ∷ e) = just ((compareNaturals n m)  ∷ e)



--function for opSwap
executeStackSwap : Stack → Maybe Stack
executeStackSwap [] = nothing
executeStackSwap (x ∷ []) = nothing
executeStackSwap (y ∷ x  ∷ s) = just (x ∷  y  ∷ s)


--function for opSub
executeStackSub : Stack → Maybe Stack
executeStackSub [] = nothing
executeStackSub (n ∷ []) = nothing
executeStackSub (n ∷ m ∷ e) = just ((n ∸ m) ∷ e)

--function for opDup
executeStackDup : Stack → Maybe Stack
executeStackDup [] = nothing
executeStackDup (n ∷ ns) = (just (n ∷ n ∷ ns))

--function for opPush
executeStackPush : ℕ →  Stack → Maybe Stack
executeStackPush n s = just (n ∷ s )

--function for opDrop
executeStackDrop : Stack → Maybe Stack
executeStackDrop [] = nothing
executeStackDrop (x ∷ s) = just s

--auxiliary function for OpCHECKLOCKTIMEVERIFY
executeOpCHECKLOCKTIMEVERIFYAux : Stack → Bool → Maybe Stack
executeOpCHECKLOCKTIMEVERIFYAux s false = nothing
executeOpCHECKLOCKTIMEVERIFYAux s true = just s


-- function for OpCHECKLOCKTIMEVERIFY
executeOpCHECKLOCKTIMEVERIFY : (currentTime : Time) → Stack → Maybe Stack
executeOpCHECKLOCKTIMEVERIFY currentTime [] = nothing
executeOpCHECKLOCKTIMEVERIFY currentTime (x ∷ s)
      = executeOpCHECKLOCKTIMEVERIFYAux (x ∷ s) (instructOpTime currentTime x)


isSigned : (msg : Msg)(s : Signature)(pbk : PublicKey) → Bool
isSigned = param .signed

IsSigned : (msg : Msg)(s : Signature)(pbk : PublicKey) → Set
IsSigned = Signed param


--function for opCheckSig
executeStackCheckSig : Msg →  Stack → Maybe Stack
executeStackCheckSig msg [] = nothing
executeStackCheckSig msg (x ∷ []) = nothing
-- pbk is on top of sig
executeStackCheckSig msg (pbk ∷ sig ∷ s) = stackAuxFunction s (isSigned msg sig pbk)

{-
 -- Alternative definition of executeStackCheckSig
 --   which refers to the shape of the msg
 --   might be used later so keep it
executeStackCheckSig : Time → Msg →  Stack → Maybe Stack
executeStackCheckSig msg [] = nothing
executeStackCheckSig msg (x ∷ []) = nothing
executeStackCheckSig msg (pbk ∷ sig ∷ s) = stackAuxFunction s (isSigned msg sig pbk)
--executeStackCheckSig (msg +msg msg₁) s = nothing
-- executeStackCheckSig (list l) s = nothing
-}


--function for opCheckSig3
executeStackCheckSig3Aux : Msg →  Stack → Maybe Stack
executeStackCheckSig3Aux msg [] = nothing
executeStackCheckSig3Aux mst (x ∷ []) = nothing
executeStackCheckSig3Aux msg (m ∷ k ∷ []) =  nothing
executeStackCheckSig3Aux msg (m ∷ k ∷ x ∷ []) =  nothing
executeStackCheckSig3Aux msg (m ∷ k ∷ x ∷ f ∷ []) =  nothing
executeStackCheckSig3Aux msg (m ∷ k ∷ x ∷ f ∷ l ∷ []) =  nothing
executeStackCheckSig3Aux msg (p1 ∷ p2 ∷ p3 ∷ s1 ∷ s2 ∷ s3 ∷ s) =  stackAuxFunction s
       ((isSigned msg s1 p1 ) ∧b (isSigned msg s2 p2) ∧b (isSigned msg s3 p3))
-- executeStackCheckSig3Aux (msg +msg msg₁) s = nothing
-- executeStackCheckSig3Aux (list l) s = nothing



-- executeMultiSig3 msg n m rest fetchedpublicKeys []


{-

----- Order of Arguments in executeMultiSig and compareSigsMultiSig ------------

Note in the following
in executeMultiSig2/3 the order is publickeys then sigs
  since we are first fetching the public keys then the signatures
in compareSigsMultiSig it is sigs then publicKeys
since we are checking for each signature whether we find a corresponding public key
  it matches
-}

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



--semantic Basic Operations execute MultiSig Two
executeMultiSig2 : (msg : Msg)(numPbks : ℕ)(st :  Stack)(pbks : List ℕ) → Maybe Stack
executeMultiSig2  msg  _        []                pbks  =  nothing
executeMultiSig2  msg  zero     (numSigs ∷ rest)  pbks  =  executeMultiSig3 msg pbks numSigs rest []
executeMultiSig2  msg  (suc n)  (pbk ∷ rest)      pbks  =  executeMultiSig2 msg n rest (pbk ∷ pbks)


-- Add the notes to a file  notes in notes
-- next steps
-- move executeMultisig to semanticsInstructions.agda
-- add opMultiSig to the instructions
-- define ⟦ OpMultiSig ⟧s = liftMsgStackToStateTransformerDepIfStack' executeMultisig
-- in semanticsInstructions
-- define in addition4.agda
--   ⟦ OpMultiSig   ⟧stacks time₁ msg =  executeMultisig msg


-- Try out evaluatings scripts as in scriptInterpreter.agda  whether it works as intended
--   write some multisignature script and a scriptsig  and check whether they work correctly

-- Try out experiments like stackfunP2PKH   in additionAntonExperiments.agda
-- for
-- ⟦ (opPush 2) ∷ (opPush pbk1) ∷  (opPush pbk2) ∷  (opPush pbk3) ∷  (opPush 3) ∷  opMultiSig ∷  []     ⟧stack time msg₁ stack
-- whether this is equal to
-- executeMultiSig3 msg₁ (pbk1 ∷ pbk2 ∷ pbk3 ∷ []) 2 stack []
-- similarly as in lemma1 by postulating   pbk1,..,pbk3,time,msg,stack

-- if yes then the
-- weakest precondtion for the multisig script would be:
-- stack needs to have size at least 2 and the for signatures sig1 sig2 on the stack we have
-- compareSigsMultiSig  msg₁ (sig1 ∷ [ sig2 ]) (pbk1 ∷ pbk2 ∷ [ pbk3 ] ) = true

--semantic Basic Operations check pubk
executeMultisig : Msg →  Stack →  Maybe Stack
executeMultisig msg [] = nothing
executeMultisig msg (numberOfPbks ∷ st) = executeMultiSig2 msg numberOfPbks st []

