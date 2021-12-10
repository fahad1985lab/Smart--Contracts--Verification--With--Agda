open import basicBitcoinDataType

module verificationStackScripts.verificationMultiSigBasicSymbolicExecutionPaper (param : GlobalParameters) where


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
   renaming (compareSigsMultiSigAux to cmpSigsMultiSigAux)
open import instructionBasic
open import verificationMultiSig param  hiding (multiSigScript2-4ᵇ)
open import verificationStackScripts.semanticsStackInstructions param
open import verificationStackScripts.stackVerificationLemmas param
open import verificationStackScripts.stackHoareTriple param
open import verificationStackScripts.sPredicate
open import verificationStackScripts.hoareTripleStackBasic param
open import verificationStackScripts.stackState
open import verificationStackScripts.stackSemanticsInstructionsBasic param
open import verificationStackScripts.verificationMultiSigBasic param

private
  postulate pbk₁ pbk₂ pbk₃ pbk₄ :  ℕ
  postulate time₁ : Time
  postulate msg₁ : Msg
  postulate stack₁ : List ℕ
  postulate sig₂ sig₁ dummy : ℕ

--verification MultiSig Basic Symbolic Execution Paper complex multisig
multiSigScript2-4ᵇ : (pbk1 pbk2 pbk3 pbk4 :  ℕ) → BitcoinScriptBasic
multiSigScript2-4ᵇ  pbk1 pbk2 pbk3 pbk4 = (opPush 2)     ∷  (opPush pbk1)  ∷  (opPush pbk2) ∷
                   (opPush pbk3) ∷      (opPush pbk4)  ∷  (opPush 4)     ∷  [ opMultiSig ]


--verification MultiSig Basic Symbolic Execution 

multisigScript-2-4-symbolic =
        ⟦ multiSigScript2-4ᵇ pbk₁ pbk₂ pbk₃ pbk₄ ⟧ˢ time₁ msg₁ stack₁

{- evaluated we get

executeMultiSig3 msg₁ (pbk₁ ∷ pbk₂ ∷ pbk₃ ∷ [ pbk₄ ]) 2 stack₁ []

-}

--result multisig
test2 : Maybe Stack
test2 =
      executeMultiSig3 msg₁ (pbk₁ ∷ pbk₂ ∷ pbk₃ ∷ [ pbk₄ ]) 2 stack₁ []


-- now we try out stack₁ = []

multisigScript-2-4-symbolic-empty = ⟦ multiSigScript2-4ᵇ pbk₁ pbk₂ pbk₃ pbk₄ ⟧ˢ time₁ msg₁ []

{-
result nothing
-}

multisigScript-2-4-symbolic-1stackelement = ⟦ multiSigScript2-4ᵇ pbk₁ pbk₂ pbk₃ pbk₄ ⟧ˢ time₁ msg₁ [ sig₂ ]

{-
result nothing
-}

multisigScript-2-4-symbolic-2stackelement = ⟦ multiSigScript2-4ᵇ pbk₁ pbk₂ pbk₃ pbk₄ ⟧ˢ time₁ msg₁ (sig₂ ∷ [ sig₁ ])

{-
result nothing
-}

--verification MultiSig Basic Symbolic Execution Paper stack Needed First Step MultiSig
stackNeededFirstStepMultiSig : (sig₂ sig₁ dummy : ℕ)(stack₁ : Stack) → Stack
stackNeededFirstStepMultiSig sig₂ sig₁ dummy stack₁ =
  sig₂ ∷ sig₁ ∷ dummy ∷ stack₁

--stack has three element
multisigScript-2-4-symbolic-3stackelement =
  ⟦ multiSigScript2-4ᵇ pbk₁ pbk₂ pbk₃ pbk₄ ⟧ˢ time₁ msg₁ (sig₂ ∷ sig₁ ∷ dummy ∷ stack₁)

{-
just
(boolToNat
 (cmpSigsMultiSigAux msg₁ [ sig₂ ] (pbk₂ ∷ pbk₃ ∷ [ pbk₄ ]) sig₁  (isSigned msg₁ sig₁ pbk₁))
 ∷  stack₁)
-}
--verification MultiSig Basic Symbolic Execution Paper stack has three element Normalised

multisigScript-2-4-symbolic-3stackelementNormalised : Maybe Stack
multisigScript-2-4-symbolic-3stackelementNormalised =
  just  (boolToNat (cmpSigsMultiSigAux msg₁ [ sig₂ ] (pbk₂ ∷ pbk₃ ∷ [ pbk₄ ]) sig₁
        (isSigned msg₁ sig₁ pbk₁)) ∷  stack₁)



{-
So the program succeeds (we obtain result just) and all we need to check is whether the top element is

(boolToNat
 (cmpSigsMultiSigAux msg₁ [ sig₂ ] (pbk₂ ∷ pbk₃ ∷ [ pbk₄ ]) sig₁  (isSigned msg₁ sig₁ pbk₁))

is > 0


which is the case if
(cmpSigsMultiSigAux msg₁ [ sig₂ ] (pbk₂ ∷ pbk₃ ∷ [ pbk₄ ]) sig₁  (isSigned msg₁ sig₁ pbk₁))

is true


so we symbolically evaluate

cmpSigsMultiSigAux msg₁ [ sig₂ ] (pbk₂ ∷ pbk₃ ∷ [ pbk₄ ]) sig₁  (isSigned msg₁ sig₁ pbk₁)

-}

topElementMultisigScript-2-4-symbolic-3' : Bool
topElementMultisigScript-2-4-symbolic-3' =
   cmpSigsMultiSigAux msg₁ [ sig₂ ] (pbk₂ ∷ pbk₃ ∷ [ pbk₄ ]) sig₁  (param .signed msg₁ sig₁ pbk₁)

--compare Sigmulti
topElementMultisigScript-2-4-symbolic-3 : Bool
topElementMultisigScript-2-4-symbolic-3 =
   cmpSigsMultiSigAux msg₁ [ sig₂ ] (pbk₂ ∷ pbk₃ ∷ [ pbk₄ ]) sig₁  (isSigned msg₁ sig₁ pbk₁)

--verification MultiSig Basic Symbolic Execution Paper subex Top Element One
subExpTopElementMultisigScript-2-4-symbolic-3 : (msg₁ : Msg)(sig₁ pbk₁ : ℕ) → Bool
subExpTopElementMultisigScript-2-4-symbolic-3 msg₁ sig₁ pbk₁ =
 isSigned msg₁ sig₁ pbk₁



testEqual : topElementMultisigScript-2-4-symbolic-3' ≡ topElementMultisigScript-2-4-symbolic-3
testEqual = refl

{- So we can always write

isSigned   instead of     param .signed

-}




{-
We now make a casedistinction on (isSigned msg₁ sig₁ pbk₁)


-}




multisigAuxStep1True = cmpSigsMultiSigAux msg₁ [ sig₂ ] (pbk₂ ∷ pbk₃ ∷ [ pbk₄ ]) sig₁ true
{-
  compareSigsMultiSigAux msg₁ [] (pbk₃ ∷ [ pbk₄ ]) sig₂ (isSigned msg₁ sig₂ pbk₂)
-}

--verification MultiSig Basic Symbolic Execution Paper result Step1 true
resultMultisigAuxStep1True : Bool
resultMultisigAuxStep1True =
  cmpSigsMultiSigAux msg₁ [] (pbk₃ ∷ [ pbk₄ ]) sig₂ (isSigned msg₁ sig₂ pbk₂)

--verification MultiSig Basic Symbolic Execution Paper result Step1 true SubExp

resultMultisigAuxStep1TrueSubExp : Bool
resultMultisigAuxStep1TrueSubExp =
  isSigned msg₁ sig₂ pbk₂



multisigAuxStep1TrueStep2True = cmpSigsMultiSigAux msg₁ [] (pbk₃ ∷ [ pbk₄ ]) sig₂ true

{- returns true -}


multisigAuxStep1TrueStep2False = cmpSigsMultiSigAux msg₁ [] (pbk₃ ∷ [ pbk₄ ]) sig₂ false

{- returns
   compareSigsMultiSigAux msg₁ [] [ pbk₄ ] sig₂ (isSigned msg₁ sig₂ pbk₃)
-}


--verification MultiSig Basic Symbolic Execution Paper result Step1 true Step2 False
resultMultisigAuxStep1Step2False : Bool
resultMultisigAuxStep1Step2False =
  cmpSigsMultiSigAux msg₁ [] [ pbk₄ ] sig₂ (isSigned msg₁ sig₂ pbk₃)

--verification MultiSig Basic Symbolic Execution Paper result Step1 true Step2 False Core

resultMultisigAuxStep1Step2FalseCoreExp : Bool
resultMultisigAuxStep1Step2FalseCoreExp =
  isSigned msg₁ sig₂ pbk₃


multisigAuxStep1TrueStep2FalseStep3True = cmpSigsMultiSigAux msg₁ [] [ pbk₄ ] sig₂ true


{- returns true -}

multisigAuxStep1TrueStep2FalseStep3False = cmpSigsMultiSigAux msg₁ [] [ pbk₄ ] sig₂ false

{- returns
    cmpSigsMultiSigAux msg₁ [] [] sig₂ (isSigned msg₁ sig₂ pbk₄)
-}



multisigAuxStep1TrueStep2FalseStep3FalseStep4True = cmpSigsMultiSigAux msg₁ [] [] sig₂ true

{- returns true -}

multisigAuxStep1TrueStep2FalseStep3FalseStep4False = cmpSigsMultiSigAux msg₁ [] [] sig₂ false

{- returns false -}

multisigAuxStep1False = cmpSigsMultiSigAux msg₁ [ sig₂ ] (pbk₂ ∷ pbk₃ ∷ [ pbk₄ ]) sig₁ false

{- returns

   cmpSigsMultiSigAux msg₁ [ sig₂ ] (pbk₃ ∷ [ pbk₄ ]) sig₁ (isSigned msg₁ sig₁ pbk₂)

-}

multisigAuxStep1FalseStep2True  = cmpSigsMultiSigAux msg₁ [ sig₂ ] (pbk₃ ∷ [ pbk₄ ]) sig₁ true

{- returns
     cmpSigsMultiSigAux msg₁ [] [ pbk₄ ] sig₂ (isSigned msg₁ sig₂ pbk₃)
-}

multisigAuxStep1FalseStep2TrueStep3True  = cmpSigsMultiSigAux msg₁ [] [ pbk₄ ] sig₂ true

{- returns true -}

multisigAuxStep1FalseStep2TrueStep3False  = cmpSigsMultiSigAux msg₁ [] [ pbk₄ ] sig₂ false

{- returns
   cmpSigsMultiSigAux msg₁ [] [] sig₂ (isSigned msg₁ sig₂ pbk₄)
-}

multisigAuxStep1FalseStep2TrueStep3FalseStep4True  = cmpSigsMultiSigAux msg₁ [] [] sig₂ true

{- returns true -}

multisigAuxStep1FalseStep2TrueStep3FalseStepFalse  = cmpSigsMultiSigAux msg₁ [] [] sig₂ false

{- returns false -}


multisigAuxStep1FalseStep2False  = cmpSigsMultiSigAux msg₁ [ sig₂ ] (pbk₃ ∷ [ pbk₄ ]) sig₁ false

{-returns

  cmpSigsMultiSigAux msg₁ [ sig₂ ] [ pbk₄ ] sig₁ (isSigned msg₁ sig₁ pbk₃)
-}

multisigAuxStep1FalseStep2FalseStep3True  = cmpSigsMultiSigAux msg₁ [ sig₂ ] [ pbk₄ ] sig₁ true

{- returns
   cmpSigsMultiSigAux msg₁ [] [] sig₂ (isSigned msg₁ sig₂ pbk₄)
-}

multisigAuxStep1FalseStep2FalseStep3TrueStep4True  = cmpSigsMultiSigAux msg₁ [] [] sig₂ true

{- returns true -}

multisigAuxStep1FalseStep2FalseStep3TrueStep4False  = cmpSigsMultiSigAux msg₁ [] [] sig₂ false

{- returns false -}




multisigAuxStep1FalseStep2FalseStep3False  = cmpSigsMultiSigAux msg₁ [ sig₂ ] [ pbk₄ ] sig₁ false

{- returns
    cmpSigsMultiSigAux msg₁ [ sig₂ ] [] sig₁ (isSigned msg₁ sig₁ pbk₄)
-}

multisigAuxStep1FalseStep2FalseStep3FalseStep4True  = cmpSigsMultiSigAux msg₁ [ sig₂ ] [] sig₁ true

{- returns false -}

multisigAuxStep1FalseStep2FalseStep3FalseStep4False  = cmpSigsMultiSigAux msg₁ [ sig₂ ] [] sig₁ false

{- returns false -}


{- So we see that that

(cmpSigsMultiSigAux msg₁ [ sig₂ ] (pbk₂ ∷ pbk₃ ∷ [ pbk₄ ]) sig₁  (isSigned msg₁ sig₁ pbk₁))


returns true iff

(isSigned msg₁ sig₂ pbk₂)   and (isSigned msg₁ sig₂ pbk₂)
or
(isSigned msg₁ sig₂ pbk₂)   and ¬ (isSigned msg₁ sig₂ pbk₂)  and (isSigned msg₁ sig₂ pbk₃)
or
(isSigned msg₁ sig₂ pbk₂)   and ¬ (isSigned msg₁ sig₂ pbk₂)  and ¬ (isSigned msg₁ sig₂ pbk₃) and (isSigned msg₁ sig₂ pbk₄)
or
¬ (isSigned msg₁ sig₂ pbk₂)  and (isSigned msg₁ sig₁ pbk₂) and (isSigned msg₁ sig₂ pbk₃)
or
¬ (isSigned msg₁ sig₂ pbk₂)  and (isSigned msg₁ sig₁ pbk₂) and ¬ (isSigned msg₁ sig₂ pbk₃) and (isSigned msg₁ sig₂ pbk₄)
or
¬ (isSigned msg₁ sig₂ pbk₂)  and ¬ (isSigned msg₁ sig₁ pbk₂)  and (isSigned msg₁ sig₁ pbk₃)  and (isSigned msg₁ sig₂ pbk₄)



we simplify it to:

(isSigned msg₁ sig₂ pbk₂)   and (isSigned msg₁ sig₂ pbk₂)
or
(isSigned msg₁ sig₂ pbk₂)   and (isSigned msg₁ sig₂ pbk₃)
or
(isSigned msg₁ sig₂ pbk₂)   and  (isSigned msg₁ sig₂ pbk₄)
or
(isSigned msg₁ sig₁ pbk₂) and (isSigned msg₁ sig₂ pbk₃)
or
(isSigned msg₁ sig₁ pbk₂) and (isSigned msg₁ sig₂ pbk₄)
or
(isSigned msg₁ sig₁ pbk₃)  and (isSigned msg₁ sig₂ pbk₄)



so the full script is accepted if and only if the stack has hight at least 3 and
if the top elements are sig₁ sig₂  dummy
then  the above condition holds

so the weakest precondition is ...  name for weakest precondition


-}




{-
test : Set
test = {!!}
-}
