open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _<_; s≤s)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_)
open import isomorphism using (_≅_; extensionality)

¬_ : Set → Set 
¬ A = A → ⊥ 

¬-elim : ∀ {A : Set}
    → ¬ A
    → A 
    -----
    → ⊥
¬-elim ¬x x = ¬x x 

infix 3 ¬_

¬¬-intro : ∀ {A : Set}
    → A
    -------
    → ¬ ¬ A
¬¬-intro x = λ{¬x → ¬x x}

¬¬¬-elim : ∀ {A : Set}
    → ¬ ¬ ¬ A
    ---------
    → ¬ A
¬¬¬-elim ¬¬¬x = λ x → ¬¬¬x (¬¬-intro x)

contraposition : ∀ {A B : Set}
    → (A → B)
    ---------
    → (¬ B → ¬ A)
contraposition f ¬y = λ x → ¬y (f x)

_≡/_ : ∀ {A : Set} → A → A → Set 
x ≡/ y = ¬ (x ≡ y)

_ : 1 ≡/ 2
_ = λ()

id : ⊥ → ⊥ 
id x = x 

assimlation : ∀ {A : Set} (¬x ¬x' : ¬ A) → ¬x ≡ ¬x'
assimlation ¬x ¬x' = extensionality (λ x → ⊥-elim (¬x x))

<-irreflexive : ∀ (n : ℕ) → ¬ (n < n)
<-irreflexive zero = λ()
<-irreflexive (suc n) (s≤s n<n) = <-irreflexive n n<n

