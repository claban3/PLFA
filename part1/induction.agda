import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)

{- Proof of Associativity -}

-- example
_ : (3 + 4) + 5 ≡ 3 + (4 + 5)
_ =
    begin
        (3 + 4) + 5
    ≡⟨⟩
        7 + 5
    ≡⟨⟩
        12
    ≡⟨⟩
        3 + 9
    ≡⟨⟩
        3 + (4 + 5)
    ∎

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p = 
    begin
        (zero + n) + p
    ≡⟨⟩
        n + p
    ≡⟨⟩ 
        zero + (n + p)
    ∎
+-assoc (suc m) n p =
    begin 
        (suc m + n) + p
    ≡⟨⟩
        suc (m + n) + p
    ≡⟨⟩
        suc ((m + n) + p)
    ≡⟨ cong suc (+-assoc m n p) ⟩
        suc (m + (n + p))
    ≡⟨⟩
        suc m + (n + p)
    ∎

{- Proof of Commutativity -}
+-identityʳ : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ zero =
    begin
        zero + zero 
    ≡⟨⟩
        zero
    ∎
+-identityʳ (suc m) = 
    begin
        suc m + zero
    ≡⟨⟩
        suc (m + zero)
    ≡⟨ cong suc (+-identityʳ m) ⟩
        suc m
    ∎

+-suc : ∀(m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n = 
    begin 
        zero + suc n
    ≡⟨⟩
        suc n 
    ≡⟨⟩
        suc (zero + n)
    ∎
+-suc (suc m) n = 
    begin
        (suc m) + suc n
    ≡⟨⟩
        suc (m + suc n)
    ≡⟨ cong suc (+-suc m n) ⟩
        suc (suc (m + n))
    ≡⟨⟩
        suc (suc m + n)
    ∎

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero = 
    begin 
        m + zero
    ≡⟨ +-identityʳ m ⟩
        m
    ≡⟨⟩
        zero + m
    ∎
+-comm m (suc n) =
    begin
        m + (suc n)
    ≡⟨ +-suc m n ⟩
        suc (m + n)
    ≡⟨ cong suc (+-comm m n) ⟩
        suc (n + m)
    ≡⟨⟩
        suc n + m
    ∎

+-assoc' : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc' zero n p = refl
+-assoc' (suc m) n p rewrite +-assoc' m n p = refl

{- Swap -}
+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p = 
    begin
        m + (n + p)
    ≡⟨ +-comm m (n + p) ⟩ 
        (n + p) + m 
    ≡⟨ +-assoc n p m ⟩
        n + (p + m)
    ≡⟨ cong (n +_) (+-comm p m) ⟩
        n + (m + p)
    ∎ 

*-zero : ∀ (m : ℕ) → m * zero ≡ zero
*-zero zero = refl
*-zero (suc m) rewrite *-zero m = refl

{- Distrib -}

*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ zero n p = refl
*-distrib-+ (suc m) n p = 
    begin
        (suc m + n) * p
    ≡⟨⟩
        suc (m + n) * p
    ≡⟨⟩
        p + (m + n) * p
    ≡⟨ cong (p +_) (*-distrib-+ m n p) ⟩
        p + (m * p + n * p)
    ≡⟨ sym (+-assoc p (m * p) (n * p)) ⟩
        (p + m * p) + n * p
    ≡⟨⟩
        suc m * p + n * p
    ∎
