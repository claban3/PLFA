import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm; *-comm; +-identityʳ; *-suc)

data _≤_ : ℕ → ℕ → Set where
    z≤n : ∀ {n : ℕ} → zero ≤ n
    s≤s : ∀ {m n : ℕ} → m ≤ n → suc m ≤ suc n

infix 4 _≤_

_ : 2 ≤ 4
_ = s≤s (s≤s z≤n)

inv-s≤s : ∀ {m n : ℕ}
    → suc m ≤ suc n
    → m ≤ n 
inv-s≤s (s≤s m≤n) = m≤n

≤-refl : ∀ {n : ℕ} → n ≤ n 
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-trans : ∀ {m n p : ℕ}
    → m ≤ n 
    → n ≤ p 
    -------
    → m ≤ p 

≤-trans z≤n _ = z≤n
≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)

≤-antisym : ∀ {m n : ℕ}
    → m ≤ n 
    → n ≤ m 
    -------
    → m ≡ n

≤-antisym z≤n z≤n = refl
≤-antisym (s≤s m≤n) (s≤s n≤m) = cong suc (≤-antisym m≤n n≤m) 

data Total (m n : ℕ) : Set where 

    forward :
        m ≤ n 
        -----
        → Total m n

    flipped : 
        n ≤ m 
        -----
        → Total m n

≤-total : ∀ (m n : ℕ) → Total m n 
≤-total zero    n                     = forward z≤n
≤-total (suc m) zero                  = flipped z≤n
≤-total (suc m) (suc n) with ≤-total m n 
...                     | forward m≤n = forward (s≤s m≤n)
...                     | flipped n≤m = flipped (s≤s n≤m)

+-monoʳ-≤ : ∀ (n p q : ℕ)
    → p ≤ q 
     --------------
    → n + p ≤ n + q
+-monoʳ-≤ zero    p q p≤q  =  p≤q
+-monoʳ-≤ (suc n) p q p≤q  =  s≤s (+-monoʳ-≤ n p q p≤q)

+-monoˡ-≤ : ∀ (m n p : ℕ) 
    → m ≤ n
    -------------
    → (m + p) ≤ (n + p)
+-monoˡ-≤ m n p m≤n rewrite +-comm m p | +-comm n p = +-monoʳ-≤ p m n m≤n

+-mono-≤ : ∀ (m n p q : ℕ)
    → m ≤ n
    → p ≤ q
    -------------
    → (m + p) ≤ (n + q)
+-mono-≤ m n p q m≤n p≤q = ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ n p q p≤q)

*-monoʳ-≤ : ∀ (m p q : ℕ)
    → p ≤ q 
    -----------
    → m * p ≤ m * q
*-monoʳ-≤ zero p q p≤q = z≤n
*-monoʳ-≤ (suc m) p q p≤q rewrite (sym (*-suc p m )) | (sym (*-suc q m)) 
    = +-mono-≤ p q (m * p) (m * q) (p≤q) (*-monoʳ-≤ m p q p≤q)
    
*-monoˡ-≤ : ∀ (m n p : ℕ)
    → m ≤ n
    ----------
    → m * p ≤ n * p

*-monoˡ-≤ m n p m≤n rewrite *-comm m p | *-comm n p = *-monoʳ-≤ p m n m≤n 

*-mono-≤ : ∀ (m n p q : ℕ)
    → m ≤ n
    → p ≤ q
    ---------------
    → (m * p) ≤ (n * q)
*-mono-≤ m n p q m≤n p≤q = ≤-trans (*-monoˡ-≤ m n p m≤n) (*-monoʳ-≤ n p q p≤q) 

infix 4 _<_

data _<_ : ℕ → ℕ → Set where
    z<s : ∀ {n : ℕ}
        -----------
        → zero < suc n 
    s<s : ∀ {m n : ℕ}
        → m < n 
        --------------
        → suc m < suc n 

data even : ℕ → Set 
data odd : ℕ → Set 

data even where 
    zero : 
        ------------
        even zero 
    
    suc : ∀ {n : ℕ}
        → odd n 
        -----
        → even (suc n)

data odd where 
    suc : ∀ {n : ℕ}
        → even n 
        ---------
        → odd (suc n)

