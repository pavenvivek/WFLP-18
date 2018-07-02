
open import Data.Bool
open import Patch_Theory.agda_lib.Equiv

module Patch_Theory.agda_lib.Interval where

  private
    data #I : Set where
      #zer : #I
      #one : #I

  I : Set
  I = #I

  zer : I
  zer = #zer

  one : I
  one = #one

  postulate  -- HIT
    seg : zer ≡ one

  I-rec : (P : I → Set) → (x₀ : P zer) → (x₁ : P one) → 
          (p : transport P seg x₀ ≡ x₁) →
          ((t : I) → P t)
  I-rec P x₀ x₁ p #zer = x₀
  I-rec P x₀ x₁ p #one = x₁

  postulate  -- HIT
   βrec-I : (P : I → Set) → (x₀ : P zer) → (x₁ : P one) →
            (p : transport P seg x₀ ≡ x₁) →
            apd (I-rec P x₀ x₁ p) seg ≡ p

  _==I_ : #I → #I → Bool
  #zer  ==I #zer  = true
  #zer  ==I #one  = false
  #one  ==I #one  = true
  #one  ==I #zer  = false
