import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

data ℕ : Set where
    zero : ℕ
    succ : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
zero + n = n 
(succ m) + n = succ (m + n) 

_ : 2 + 3 ≡ 5
_ = 
    begin
            2 + 3
        ≡⟨⟩
            succ (1 + 3)
        ≡⟨⟩
            succ (succ (0 + 3))
        ≡⟨⟩
            succ (succ 3)
        ≡⟨⟩
            succ 4
        ≡⟨⟩ 
            5
    ∎

_*_ : ℕ → ℕ → ℕ
zero * n = zero
(succ m) * n = n + (m * n)

_ : 4 * 4 ≡ 16
_ = refl

_^_ : ℕ → ℕ → ℕ
m ^ zero = succ zero
m ^ (succ n) = m * (m ^ n)

_ : 3 ^ 4 ≡ 81
_ = refl

{- Monus -}

_∸_ : ℕ → ℕ → ℕ
m ∸ zero = m
zero ∸ succ n = zero
succ m ∸ succ n = m ∸ n

_ : 3 ∸ 5 ≡ 0
_ = begin 
        3 ∸ 5
    ≡⟨⟩ 
        2 ∸ 4
    ≡⟨⟩ 
        1 ∸ 3
    ≡⟨⟩ 
        0 ∸ 2
    ≡⟨⟩
        0
    ∎

{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _∸_ #-}

data Bin : Set where
    ⟨⟩ : Bin
    _O : Bin → Bin
    _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (n O) = n I
inc (n I) = (inc n) O

_ : inc (⟨⟩ I O I I) ≡ ⟨⟩ I I O O
_ = begin
        inc (⟨⟩ I O I I)
    ≡⟨⟩
        (inc (⟨⟩ I O I)) O
    ≡⟨⟩
        (inc (⟨⟩ I O)) O O
    ≡⟨⟩
        ((⟨⟩ I I) O) O
    ≡⟨⟩
        ⟨⟩ I I O O
    ∎

to : ℕ → Bin 
to zero = ⟨⟩
to (succ n) = inc (to n)

from : Bin → ℕ 
from ⟨⟩ = zero
from (x O) = 2 * (from x)
from (x I) = 2 * (succ (from x))

