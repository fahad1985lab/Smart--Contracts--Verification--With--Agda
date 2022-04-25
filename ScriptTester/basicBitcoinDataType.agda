module basicBitcoinDataType where



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



Time   : Set
Time   =   ℕ
Amount : Set
Amount =  ℕ

Address : Set
Address  =  ℕ

TXID : Set
TXID =    ℕ

Signature : Set
Signature =  ℕ

PublicKey : Set
PublicKey  =  ℕ

infixr 3 _+msg_

data Msg : Set where
   nat     :  (n : ℕ)       → Msg
   _+msg_  :  (m m' : Msg)     → Msg
   list    :  (l  : List Msg)  → Msg



-- function that compares time
instructOpTime : (currentTime : Time) (entryInContract : Time) → Bool
instructOpTime currentTime entryInContract  = entryInContract ≤b currentTime



record GlobalParameters : Set where
  field
    publicKey2Address : (pubk : PublicKey) → Address
    hash              : ℕ → ℕ
    signed            : (msg : Msg)(s : Signature)(publicKey : PublicKey) → Bool
  Signed : (msg : Msg)(s : Signature)(publicKey : PublicKey) → Set
  Signed msg s publicKey  = True (signed msg s publicKey)

open GlobalParameters public
