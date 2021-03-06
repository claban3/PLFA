import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Function using (_∘_)
open import isomorphism using (_≅_; _≲_; _⇔_; extensionality)
open isomorphism.≅-Reasoning

data _×_ (A B : Set) : Set where 
    ⟨_,_⟩ : A → B → A × B

proj₁ : ∀ {A B : Set}
    → A × B 
    -------
    → A 
proj₁ ⟨ A , B ⟩ = A 

proj₂ : ∀ {A B : Set}
    → A × B 
    -------
    → B
proj₂ ⟨ A , B ⟩ = B

η-× : ∀ {A B : Set} → (w : A × B) → ⟨ proj₁ w , proj₂ w ⟩ ≡ w 
η-× ⟨ x , y ⟩ = refl

infixr 2 _×_ 

record _×'_ (A B : Set) : Set where 
    constructor ⟨_,_⟩'
    field 
        proj₁' : A 
        proj₂' : B 
open _×'_ 

η-×' : ∀ {A B : Set} → (w : A ×' B) → ⟨ proj₁' w , proj₂' w ⟩' ≡ w 
η-×' w = refl

×-comm : ∀ {A B : Set} → A × B ≅ B × A 
×-comm = 
    record 
        { to        = λ{ ⟨ x , y ⟩ → ⟨ y , x ⟩ }
        ; from      = λ{ ⟨ x , y ⟩ → ⟨ y , x ⟩ }
        ; from∘to   = λ{ ⟨ x , y ⟩ → refl }
        ; to∘from   = λ{ ⟨ x , y ⟩ → refl }
        }

×-assoc : ∀ {A B C : Set} → (A × B) × C ≅ A × (B × C)
×-assoc =
    record
        { to      = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → ⟨ x , ⟨ y , z ⟩ ⟩ }
        ; from    = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → ⟨ ⟨ x , y ⟩ , z ⟩ }
        ; from∘to = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → refl }
        ; to∘from = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → refl }
        }

⇔≅× : ∀ {A B : Set} → (A ⇔ B) ≅ ((A → B) × (B → A))
⇔≅× =
    record 
        { to        = λ{ A⇔B → ⟨ _⇔_.to A⇔B , _⇔_.from A⇔B ⟩}
        ; from      = λ{ ⟨ x , y ⟩ → record {to = x ; from = y}}
        ; from∘to   = λ{ A⇔B → refl } 
        ; to∘from   = λ{ ⟨ x , y ⟩ → refl}
        }

data ⊤ : Set where 
    tt : 
        --
        ⊤

η-⊤ : (w : ⊤) → w ≡ tt
η-⊤ tt = refl

⊤-identityˡ : ∀ {A : Set} → ⊤ × A ≅ A
⊤-identityˡ =
    record
        { to      = λ{ ⟨ tt , x ⟩ → x }
        ; from    = λ{ x → ⟨ tt , x ⟩ }
        ; from∘to = λ{ ⟨ tt , x ⟩ → refl }
        ; to∘from = λ{ x → refl }
        }

⊤-identityʳ : ∀ {A : Set} → (A × ⊤) ≅ A
⊤-identityʳ {A} =
    ≅-begin
        (A × ⊤)
    ≅⟨ ×-comm ⟩
        (⊤ × A)
    ≅⟨ ⊤-identityˡ ⟩
        A
    ≅-∎

data _⊎_ (A B : Set) : Set where  
    inj₁ : A → A ⊎ B 
    inj₂ : B → A ⊎ B 

case-⊎ : ∀ {A B C : Set} 
    → (A → C)
    → (B → C)
    → (A ⊎ B)
    ---------
    → C
case-⊎ AC BC (inj₁ A) = AC A 
case-⊎ AC BC (inj₂ B) = BC B 

