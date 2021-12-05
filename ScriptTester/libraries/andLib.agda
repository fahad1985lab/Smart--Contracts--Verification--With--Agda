module libraries.andLib  where

record _∧_ ( A B : Set ) : Set where
   constructor conj
   field
    and1 : A
    and2 : B
open _∧_  public


{-
record _∧3_∧3_ ( A B C : Set ) : Set where
   constructor conj3
   field
    and1 : A
    and2 : B
    and3 : C
open _∧3_∧3_  public
-}
