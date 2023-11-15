import Katydid.Std.Tipe

open List

-- Lang : Set (suc ℓ)
-- Lang = A ✶ → Set ℓ
def Lang (α : Type u) : Type (u + 1) :=
  List α -> Type u

-- ∅ : Lang
-- ∅ w = ⊥
def emptySet : Lang α :=
  fun _ => Empty

-- 𝒰 : Lang
-- 𝒰 w = ⊤
def universal : Lang α :=
  fun _ => Unit

-- 𝟏 : Lang
-- 𝟏 w = w ≡ []
def emptyStr : Lang α :=
  fun w => w ≡ []

-- ` : A → Lang
-- ` c w = w ≡ [ c ]
def char (a : α) :=
  fun w => w ≡ [a]

-- infixl 7 _·_
-- _·_ : Set ℓ → Op₁ Lang
-- (s · P) w = s × P w
def scalar (s : Type u) (P : Lang α) : Lang α :=
  fun w => s × P w

-- infixr 6 _∪_
-- _∪_ : Op₂ Lang
-- (P ∪ Q) w = P w ⊎ Q w
def or_ (P : Lang α) (Q : Lang α) : Lang α :=
  fun w => P w ⊕ Q w

-- infixr 6 _∩_
-- _∩_ : Op₂ Lang
-- (P ∩ Q) w = P w × Q w
def and_ (P : Lang α) (Q : Lang α) : Lang α :=
  fun w => P w × Q w

-- infixl 7 _⋆_
-- _⋆_ : Op₂ Lang
-- (P ⋆ Q) w = ∃⇃ λ (u ,  v) → (w ≡ u ⊙ v) × P u × Q v
def concat_ (P : Lang α) (Q : Lang α) : Lang α :=
  fun (w : List α) =>
    Σ (x : List α) (y : List α), (w ≡ (x ++ y)) × P x × Q y

-- infixl 10 _☆
-- _☆ : Op₁ Lang
-- (P ☆) w = ∃ λ ws → (w ≡ concat ws) × All P ws
def star_ (P : Lang α) : Lang α :=
  fun (w : List α) =>
    Σ (ws : List (List α)), (w ≡ (List.join ws)) × All P ws

-- attribute [simp] allows these definitions to be unfolded when using the simp tactic.
attribute [simp] universal emptySet emptyStr char scalar or_ and_ concat_ star_