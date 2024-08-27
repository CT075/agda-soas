module Partial where

open import Data.Empty
open import Data.Maybe
open import Data.Product

import SOAS.Context
open import SOAS.Families.Core

open import STLC.Signature using (ΛT; N; _↣_)
open import STLC.Syntax
open import STLC2.Signature using (Λ2T; N'; _↣'_) renaming (N to N2; _↣_ to _↣2_)
open import STLC2.Syntax

open SOAS.Context using (∅ ; _∙_)

-- Binding-time analysis for the STLC as described by Nielson/Nielson in
-- https://dl.acm.org/doi/pdf/10.1145/73560.73569

-- Setup

data _⊨_ {T₁ T₂} : SOAS.Context.Ctx {T₁} → SOAS.Context.Ctx {T₂} → Set where
  ∅⊨∅ : ∅ ⊨ ∅
  ∙⊨∙ : ∀{x y Γ Δ} → x ∙ Γ ⊨ y ∙ Δ

Ctx = SOAS.Context.Ctx {ΛT}
Ctx2 = SOAS.Context.Ctx {Λ2T}

AuxCtx : Set → Set
AuxCtx T = SOAS.Context.Ctx {T}

empty-fam : ∀{T} → Familyₛ {T}
empty-fam x Γ = ⊥

Λ2₀ = Λ2 empty-fam

-- Nielson/Nielson's formulation imposes a kind system on its types to ensure
-- that we don't do something nonsensical, but I couldn't figure out how to
-- express that purely syntactically, so we have to break from purely-intrinsic
-- typing for now.

data BindKind : Set where
  Now : BindKind
  Later : BindKind

data ⊢_∈_ : Λ2T → BindKind → Set where
  n-now : ⊢ N2 ∈ Now
  n-later : ⊢ N' ∈ Later
  arr-now : ∀{τ₁ τ₂} → ⊢ τ₁ ∈ Now → ⊢ τ₂ ∈ Now → ⊢ τ₁ ↣2 τ₂ ∈ Now
  arr-later : ∀{τ₁ τ₂ k} → ⊢ τ₁ ∈ Later → ⊢ τ₂ ∈ Later → ⊢ τ₁ ↣' τ₂ ∈ k

-- Transformation on types

delay-T : Λ2T → Λ2T
delay-T N2 = N'
delay-T N' = N'
delay-T (tt₁ ↣2 tt₂) = delay-T tt₁ ↣2 delay-T tt₂
delay-T (tt₁ ↣' tt₂) = delay-T tt₁ ↣' delay-T tt₂

checkkind : (tt : Λ2T) → (k : BindKind) → Maybe (⊢ tt ∈ k)
checkkind N2 Now = just n-now
checkkind N2 Later = nothing
checkkind N' Now = nothing
checkkind N' Later = just n-later
checkkind (tt₁ ↣2 tt₂) Now = do
  tt₁-now ← checkkind tt₁ Now
  tt₂-now ← checkkind tt₂ Now
  just (arr-now tt₁-now tt₂-now)
checkkind (tt₁ ↣2 tt₂) Later = nothing
checkkind (tt₁ ↣' tt₂) k = do
  tt₁-later ← checkkind tt₁ Later
  tt₂-later ← checkkind tt₂ Later
  just (arr-later tt₁-later tt₂-later)

complete-T : Λ2T → Λ2T
complete-T N2 = N2
complete-T N' = N'
complete-T (tt @ (tt₁ ↣2 tt₂)) = aux (checkkind tt₁ Now) (checkkind tt₂ Now)
  where
    aux : Maybe (⊢ tt₁ ∈ Now) → Maybe (⊢ tt₂ ∈ Now) → Λ2T
    aux (just tt₁-now) (just tt₂-now) = tt₁' ↣2 tt₂'
      where
        tt₁' = complete-T tt₁
        tt₂' = complete-T tt₂
    aux nothing (just _) = delay-T tt
    aux (just _) nothing = delay-T tt
    aux nothing nothing = delay-T tt
complete-T (tt @ (_ ↣' _)) = delay-T tt

-- Transformation on terms

postulate
  -- not a true lattice; does not always exist
  _⊓_ : Λ2T → Λ2T → Λ2T

-- The intrinsic typing pretty much only gets in the way here. While it
-- immediately eliminates a few of messy ases from the paper, it is very
-- difficult to express the algorithm in full generality, simply due to the
-- fact that every term _must_ have a prescribed type. This means that we need
-- to do complex bookkeeping (not included in this version of the file) to
-- track the intrinsic vs desired type lifting.
--
-- This construction of contexts also makes it very frustrating to lookup
-- information stored in auxiliary variable mappings.

{-
messier to use this because of termination checker

record Λ2-Constraint : Set where
  constructor C
  field
    Γ : Ctx2
    tt : Λ2T
    te : Λ2₀ tt Γ
-}

complete-C : ∀ Γ tt (te : Λ2₀ tt Γ) → Σ[ Γ' ∈ Ctx2 ] Σ[ tt' ∈ Λ2T ] (Λ2₀ tt' Γ')
complete-C Γ N2 n = Γ , N2 , n
-- need separate lifted constant
--complete-C (C Γ N' n) = C Γ N' n
complete-C Γ tt (var x) = Γ , tt , var x
complete-C Γ (tt₁ ↣2 tt₂) (ƛ te) =
  let Γ' , tt' , te' = complete-C (tt₁ ∙ Γ) tt₂ te
   in
  -- need to lookup top variable in Γ', but cannot, because function signature
  -- does not guarantee that Γ' has the same domain as Γ
  --
  -- if `tt₁ ↣ tt₂` is well-kinded, then tt₁ and tt₂ must both be Now
  --
  -- Doesn't typecheck: te' references Γ', which already includes tt₁, so we
  -- cannot put it under `ƛ`
  Γ' , (tt₁ ↣2 tt') , {! ƛ te' !}
-- Cannot express case for completing a Now-Lambda against a Later Arrow or
-- Later-Lambda against Now Arrow
complete-C Γ (tt₁ ↣' tt₂) (ƛ' te) =
  let tt₁' = delay-T tt₁
      tt₂' = delay-T tt₂
      -- can't use te here because we delayed the types tt₁ and tt₂
      Γ' , tt' , te' = complete-C (tt₁' ∙ Γ) tt₂' {! te !}
   in
  -- same problem as previous case
  Γ , (tt₁' ↣' tt₂') , {! ƛ' te' !}
complete-C Γ tt (te₁ $ te₂) = {!!}
complete-C Γ tt ((_$'_) {α = tt₁} {β = tt₂} te₁ te₂) =
  let Γ₁ , tt' , te₁' = complete-C Γ (delay-T (tt₁ ↣' tt₂)) {! te₁ !}
      Γ₂ , tt₁' , te₂' = complete-C Γ (delay-T tt₁) {! te₂ !}
   in
  -- how to extract domain of tt'?
  {!!}

-- Further proofs

data _≤k_ : BindKind → BindKind → Set where
  ≤k-refl : ∀{k₁ k₂} → k₁ ≤k k₂
  later≤now : Later ≤k Now

forget-T : Λ2T → ΛT
forget-T N2 = N
forget-T N' = N
forget-T (a ↣2 b) = (forget-T a) ↣ (forget-T b)
forget-T (a ↣' b) = (forget-T a) ↣ (forget-T b)

