{-
This second-order signature was created from the following second-order syntax description:

syntax STLC2 | Λ2

type
  N    : 0-ary
  N'   : 0-ary
  _↣_  : 2-ary | r30
  _↣'_ : 2-ary | r30

term
  n    : N
  app  : α ↣ β  α  ->  β | _$_ l20
  lam  : α.β  ->  α ↣ β | ƛ_ r10
  app' : α ↣' β  α  ->  β | _$'_ l21
  lam' : α.β  ->  α ↣' β | ƛ'_ r11

theory
  
-}

module STLC2.Signature where

open import SOAS.Context

-- Type declaration
data Λ2T : Set where
  N    : Λ2T
  N'   : Λ2T
  _↣_  : Λ2T → Λ2T → Λ2T
  _↣'_ : Λ2T → Λ2T → Λ2T
infixr 30 _↣_
infixr 30 _↣'_


open import SOAS.Syntax.Signature Λ2T public
open import SOAS.Syntax.Build Λ2T public

-- Operator symbols
data Λ2ₒ : Set where
  nₒ : Λ2ₒ
  appₒ lamₒ app'ₒ lam'ₒ : {α β : Λ2T} → Λ2ₒ

-- Term signature
Λ2:Sig : Signature Λ2ₒ
Λ2:Sig = sig λ
  {  nₒ            → ⟼₀ N
  ; (appₒ  {α}{β}) → (⊢₀ α ↣ β) , (⊢₀ α) ⟼₂ β
  ; (lamₒ  {α}{β}) → (α ⊢₁ β) ⟼₁ α ↣ β
  ; (app'ₒ {α}{β}) → (⊢₀ α ↣' β) , (⊢₀ α) ⟼₂ β
  ; (lam'ₒ {α}{β}) → (α ⊢₁ β) ⟼₁ α ↣' β
  }

open Signature Λ2:Sig public
