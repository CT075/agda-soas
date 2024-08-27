{-
This second-order term syntax was created from the following second-order syntax description:

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


module STLC2.Syntax where

open import SOAS.Common
open import SOAS.Context
open import SOAS.Variable
open import SOAS.Families.Core
open import SOAS.Construction.Structure
open import SOAS.ContextMaps.Inductive

open import SOAS.Metatheory.Syntax

open import STLC2.Signature

private
  variable
    Γ Δ Π : Ctx
    α β : Λ2T
    𝔛 : Familyₛ

-- Inductive term declaration
module Λ2:Terms (𝔛 : Familyₛ) where

  data Λ2 : Familyₛ where
    var  : ℐ ⇾̣ Λ2
    mvar : 𝔛 α Π → Sub Λ2 Π Γ → Λ2 α Γ

    n    : Λ2 N Γ
    _$_  : Λ2 (α ↣ β) Γ → Λ2 α Γ → Λ2 β Γ
    ƛ_   : Λ2 β (α ∙ Γ) → Λ2 (α ↣ β) Γ
    _$'_ : Λ2 (α ↣' β) Γ → Λ2 α Γ → Λ2 β Γ
    ƛ'_  : Λ2 β (α ∙ Γ) → Λ2 (α ↣' β) Γ

  infixl 20 _$_
  infixr 10 ƛ_
  infixl 21 _$'_
  infixr 11 ƛ'_

  open import SOAS.Metatheory.MetaAlgebra ⅀F 𝔛

  Λ2ᵃ : MetaAlg Λ2
  Λ2ᵃ = record
    { 𝑎𝑙𝑔 = λ where
      (nₒ    ⋮ _)     → n
      (appₒ  ⋮ a , b) → _$_  a b
      (lamₒ  ⋮ a)     → ƛ_   a
      (app'ₒ ⋮ a , b) → _$'_ a b
      (lam'ₒ ⋮ a)     → ƛ'_  a
    ; 𝑣𝑎𝑟 = var ; 𝑚𝑣𝑎𝑟 = λ 𝔪 mε → mvar 𝔪 (tabulate mε) }

  module Λ2ᵃ = MetaAlg Λ2ᵃ

  module _ {𝒜 : Familyₛ}(𝒜ᵃ : MetaAlg 𝒜) where

    open MetaAlg 𝒜ᵃ

    𝕤𝕖𝕞 : Λ2 ⇾̣ 𝒜
    𝕊 : Sub Λ2 Π Γ → Π ~[ 𝒜 ]↝ Γ
    𝕊 (t ◂ σ) new = 𝕤𝕖𝕞 t
    𝕊 (t ◂ σ) (old v) = 𝕊 σ v
    𝕤𝕖𝕞 (mvar 𝔪 mε) = 𝑚𝑣𝑎𝑟 𝔪 (𝕊 mε)
    𝕤𝕖𝕞 (var v) = 𝑣𝑎𝑟 v

    𝕤𝕖𝕞  n         = 𝑎𝑙𝑔 (nₒ    ⋮ tt)
    𝕤𝕖𝕞 (_$_  a b) = 𝑎𝑙𝑔 (appₒ  ⋮ 𝕤𝕖𝕞 a , 𝕤𝕖𝕞 b)
    𝕤𝕖𝕞 (ƛ_   a)   = 𝑎𝑙𝑔 (lamₒ  ⋮ 𝕤𝕖𝕞 a)
    𝕤𝕖𝕞 (_$'_ a b) = 𝑎𝑙𝑔 (app'ₒ ⋮ 𝕤𝕖𝕞 a , 𝕤𝕖𝕞 b)
    𝕤𝕖𝕞 (ƛ'_  a)   = 𝑎𝑙𝑔 (lam'ₒ ⋮ 𝕤𝕖𝕞 a)

    𝕤𝕖𝕞ᵃ⇒ : MetaAlg⇒ Λ2ᵃ 𝒜ᵃ 𝕤𝕖𝕞
    𝕤𝕖𝕞ᵃ⇒ = record
      { ⟨𝑎𝑙𝑔⟩ = λ{ {t = t} → ⟨𝑎𝑙𝑔⟩ t }
      ; ⟨𝑣𝑎𝑟⟩ = refl
      ; ⟨𝑚𝑣𝑎𝑟⟩ = λ{ {𝔪 = 𝔪}{mε} → cong (𝑚𝑣𝑎𝑟 𝔪) (dext (𝕊-tab mε)) }  }
      where
      open ≡-Reasoning
      ⟨𝑎𝑙𝑔⟩ : (t : ⅀ Λ2 α Γ) → 𝕤𝕖𝕞 (Λ2ᵃ.𝑎𝑙𝑔 t) ≡ 𝑎𝑙𝑔 (⅀₁ 𝕤𝕖𝕞 t)
      ⟨𝑎𝑙𝑔⟩ (nₒ    ⋮ _) = refl
      ⟨𝑎𝑙𝑔⟩ (appₒ  ⋮ _) = refl
      ⟨𝑎𝑙𝑔⟩ (lamₒ  ⋮ _) = refl
      ⟨𝑎𝑙𝑔⟩ (app'ₒ ⋮ _) = refl
      ⟨𝑎𝑙𝑔⟩ (lam'ₒ ⋮ _) = refl

      𝕊-tab : (mε : Π ~[ Λ2 ]↝ Γ)(v : ℐ α Π) → 𝕊 (tabulate mε) v ≡ 𝕤𝕖𝕞 (mε v)
      𝕊-tab mε new = refl
      𝕊-tab mε (old v) = 𝕊-tab (mε ∘ old) v

    module _ (g : Λ2 ⇾̣ 𝒜)(gᵃ⇒ : MetaAlg⇒ Λ2ᵃ 𝒜ᵃ g) where

      open MetaAlg⇒ gᵃ⇒

      𝕤𝕖𝕞! : (t : Λ2 α Γ) → 𝕤𝕖𝕞 t ≡ g t
      𝕊-ix : (mε : Sub Λ2 Π Γ)(v : ℐ α Π) → 𝕊 mε v ≡ g (index mε v)
      𝕊-ix (x ◂ mε) new = 𝕤𝕖𝕞! x
      𝕊-ix (x ◂ mε) (old v) = 𝕊-ix mε v
      𝕤𝕖𝕞! (mvar 𝔪 mε) rewrite cong (𝑚𝑣𝑎𝑟 𝔪) (dext (𝕊-ix mε))
        = trans (sym ⟨𝑚𝑣𝑎𝑟⟩) (cong (g ∘ mvar 𝔪) (tab∘ix≈id mε))
      𝕤𝕖𝕞! (var v) = sym ⟨𝑣𝑎𝑟⟩

      𝕤𝕖𝕞! n = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! (_$_ a b) rewrite 𝕤𝕖𝕞! a | 𝕤𝕖𝕞! b = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! (ƛ_ a) rewrite 𝕤𝕖𝕞! a = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! (_$'_ a b) rewrite 𝕤𝕖𝕞! a | 𝕤𝕖𝕞! b = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! (ƛ'_ a) rewrite 𝕤𝕖𝕞! a = sym ⟨𝑎𝑙𝑔⟩


-- Syntax instance for the signature
Λ2:Syn : Syntax
Λ2:Syn = record
  { ⅀F = ⅀F
  ; ⅀:CS = ⅀:CompatStr
  ; mvarᵢ = Λ2:Terms.mvar
  ; 𝕋:Init = λ 𝔛 → let open Λ2:Terms 𝔛 in record
    { ⊥ = Λ2 ⋉ Λ2ᵃ
    ; ⊥-is-initial = record { ! = λ{ {𝒜 ⋉ 𝒜ᵃ} → 𝕤𝕖𝕞 𝒜ᵃ ⋉ 𝕤𝕖𝕞ᵃ⇒ 𝒜ᵃ }
    ; !-unique = λ{ {𝒜 ⋉ 𝒜ᵃ} (f ⋉ fᵃ⇒) {x = t} → 𝕤𝕖𝕞! 𝒜ᵃ f fᵃ⇒ t } } } }

-- Instantiation of the syntax and metatheory
open Syntax Λ2:Syn public
open Λ2:Terms public
open import SOAS.Families.Build public
open import SOAS.Syntax.Shorthands Λ2ᵃ public
open import SOAS.Metatheory Λ2:Syn public


