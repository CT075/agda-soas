{-
This second-order equational theory was created from the following second-order syntax description:

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

module STLC2.Equality where

open import SOAS.Common
open import SOAS.Context
open import SOAS.Variable
open import SOAS.Families.Core
open import SOAS.Families.Build
open import SOAS.ContextMaps.Inductive

open import STLC2.Signature
open import STLC2.Syntax

open import SOAS.Metatheory.SecondOrder.Metasubstitution Λ2:Syn
open import SOAS.Metatheory.SecondOrder.Equality Λ2:Syn

private
  variable
    α β γ τ : Λ2T
    Γ Δ Π : Ctx

infix 1 _▹_⊢_≋ₐ_

-- Axioms of equality
data _▹_⊢_≋ₐ_ : ∀ 𝔐 Γ {α} → (𝔐 ▷ Λ2) α Γ → (𝔐 ▷ Λ2) α Γ → Set where
  

open EqLogic _▹_⊢_≋ₐ_
open ≋-Reasoning


