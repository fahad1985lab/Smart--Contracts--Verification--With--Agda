module exampleBasicData where



open import Data.Nat  hiding (_≤_)
open import Data.List hiding (_++_)
open import Data.Unit  hiding (_≤_)
open import Data.Empty
open import Data.Bool  hiding (_≤_ ; if_then_else_ ) renaming (_∧_ to _∧b_ ; _∨_ to _∨b_ ; T to True)
open import Data.Bool.Base hiding (_≤_ ; if_then_else_ ) renaming (_∧_ to _∧b_ ; _∨_ to _∨b_ ; T to True)
open import Data.Product renaming (_,_ to _,,_ )
open import Data.Nat.Base hiding (_≤_)
open import Data.List.NonEmpty hiding (head)

open import libraries.listLib
open import libraries.natLib
open import libraries.boolLib
open import libraries.andLib
open import libraries.maybeLib

open import basicBitcoinDataType

msgTest : Msg
msgTest = nat 5

msgTest6 : Msg
msgTest6 = nat 6

msgTest2 : Msg
msgTest2 = list  (nat 5 ∷ nat 3 ∷  [])


msgTest3 : Msg
msgTest3 = list  (msgTest2 ∷ nat 3 ∷  [])

hashExample : ℕ → ℕ
hashExample zero    = 10
hashExample (suc n) = 5

checkSigTestBas : (msg₁ sig pbk  :  ℕ ) → Bool
checkSigTestBas msg₁ sig  pbk = ((msg₁ ≡ℕb 5) ∧b (sig ≡ℕb 1)  ∧b (pbk ≡ℕb 5))  ∨b -- Alice
                               ((msg₁ ≡ℕb 5) ∧b (sig ≡ℕb 2)  ∧b (pbk ≡ℕb 6))  ∨b -- Bob
                               ((msg₁ ≡ℕb 5) ∧b (sig ≡ℕb 3)  ∧b (pbk ≡ℕb 7))  ∨b -- Charlie
                               ((msg₁ ≡ℕb 5) ∧b (sig ≡ℕb 4)  ∧b (pbk ≡ℕb 8))  ∨b -- Dan
                               ((msg₁ ≡ℕb 5) ∧b (sig ≡ℕb 14) ∧b (pbk ≡ℕb 13)) ∨b
                               ((msg₁ ≡ℕb 5) ∧b (sig ≡ℕb 15) ∧b (pbk ≡ℕb 16)) ∨b
                               ((msg₁ ≡ℕb 5) ∧b (sig ≡ℕb 9)  ∧b (pbk ≡ℕb 17)) ∨b
                               ((msg₁ ≡ℕb 5) ∧b (sig ≡ℕb 6)  ∧b (pbk ≡ℕb 7))  ∨b
                               ((msg₁ ≡ℕb 5) ∧b (sig ≡ℕb 4)  ∧b (pbk ≡ℕb 9))

checkSigTest : (msg : Msg)(sig :  ℕ)(pbk : ℕ) → Bool
checkSigTest (nat n) sig pbk = checkSigTestBas n sig pbk
checkSigTest  (m +msg m₁) sig pbk = false
checkSigTest (list l) sig pbk  = false


paramExample : GlobalParameters
paramExample .publicKey2Address   n = n
paramExample .hash                  = hashExample
paramExample .signed                = checkSigTest


hashExample2 : ℕ → ℕ
hashExample2 n  =  if (n ≤b 10) then  1 else  ( if  ( n ≤b 22)  then 2 else 3)


paramExample2 : GlobalParameters
paramExample2 .publicKey2Address   n = n
paramExample2 .hash                  = hashExample2
paramExample2 .signed                = checkSigTest
