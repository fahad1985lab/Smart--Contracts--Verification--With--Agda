
module verificationStackScripts.maybeDef where


--Maybe
data Maybe (X : Set) : Set where  nothing :  Maybe X; just    :  X → Maybe X



return : {A : Set} → A → Maybe A
return = just


_>>=_ : {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
nothing >>= q = nothing
just x >>= q = q x
