/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Coalgebra.Basic

public meta import Toric.Mathlib.RingTheory.Coalgebra.SimpAttr

/-!
# Tactic to reassociate comultiplication in a coalgebra
-/

public section

open TensorProduct

namespace Coalgebra
variable {R A M N P M' N' P' Q Q' : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A]
    [Coalgebra R A]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] [AddCommMonoid P] [Module R P]
    [AddCommMonoid M'] [Module R M'] [AddCommMonoid N'] [Module R N']
    [AddCommMonoid P'] [Module R P'] [AddCommMonoid Q] [Module R Q] [AddCommMonoid Q'] [Module R Q']

local notation3 "α" => _root_.TensorProduct.assoc R
local infix:90 " ◁ " => LinearMap.lTensor
local notation3:90 f:90 " ▷ " X:90 => LinearMap.rTensor X f
local notation3 "δ" => comul (R := R)

@[coassoc_simps, coassoc_cleanup_simps]
lemma comp_assoc_symm (f₁ : M →ₗ[R] N) (f₂ : N →ₗ[R] P) (f₃ : P →ₗ[R] Q) :
    f₃ ∘ₗ (f₂ ∘ₗ f₁) = (f₃ ∘ₗ f₂) ∘ₗ f₁ := rfl

@[coassoc_cleanup_simps]
lemma map_comp_left (f₁ : M →ₗ[R] N) (f₂ : N →ₗ[R] P) (g : M' →ₗ[R] N') :
    map (f₂ ∘ₗ f₁) g = map f₂ .id ∘ₗ map f₁ g := by ext; rfl

@[coassoc_cleanup_simps]
lemma map_comp_right (f₁ : M →ₗ[R] N) (f₂ : N →ₗ[R] P) (g : M' →ₗ[R] N') :
    map g (f₂ ∘ₗ f₁) = map .id f₂ ∘ₗ map g f₁ := by ext; rfl

@[coassoc_simps]
lemma map_comul_right_comp_comul (f : A →ₗ[R] M) :
    map f δ ∘ₗ δ = α M A A ∘ₗ (f ▷ A) ▷ A ∘ₗ δ ▷ A ∘ₗ δ := by
  rw [← LinearMap.lTensor_comp_rTensor, LinearMap.comp_assoc, ← coassoc_symm]
  simp only [← LinearMap.comp_assoc, LinearMap.lTensor_comp_rTensor,
    ← LinearMap.rTensor_comp_lTensor]
  congr; ext; rfl

@[coassoc_simps]
lemma map_comul_right_comp_comul_assoc (f : A →ₗ[R] M) (h : M ⊗[R] (A ⊗[R] A) →ₗ[R] P) :
    (h ∘ₗ map f δ) ∘ₗ δ = h ∘ₗ α M A A ∘ₗ (f ▷ A) ▷ A ∘ₗ δ ▷ A ∘ₗ δ := by
  simp [LinearMap.comp_assoc, map_comul_right_comp_comul]

@[coassoc_simps]
lemma map_comp_comul_right_comp_comul (f : A →ₗ[R] M) (g : A ⊗[R] A →ₗ[R] N) :
    map f (g ∘ₗ δ) ∘ₗ δ = M ◁ g ∘ₗ α M A A ∘ₗ (f ▷ A) ▷ A ∘ₗ δ ▷ A ∘ₗ δ := by
  simp [map_comp_right, LinearMap.comp_assoc, map_comul_right_comp_comul]
  rfl

@[coassoc_simps]
lemma map_comp_comul_right_comp_comul_assoc
    (f : A →ₗ[R] M) (g : A ⊗[R] A →ₗ[R] N) (h : M ⊗[R] N →ₗ[R] P) :
    (h ∘ₗ map f (g ∘ₗ δ)) ∘ₗ δ = h ∘ₗ M ◁ g ∘ₗ α M A A ∘ₗ (f ▷ A) ▷ A ∘ₗ δ ▷ A ∘ₗ δ := by
  simp [LinearMap.comp_assoc, map_comp_comul_right_comp_comul]

@[coassoc_simps]
lemma map_map (f₁ : M →ₗ[R] N) (f₂ : N →ₗ[R] P) (g₁ : M' →ₗ[R] N') (g₂ : N' →ₗ[R] P') :
    map f₂ g₂ ∘ₗ map f₁ g₁ = map (f₂ ∘ₗ f₁) (g₂ ∘ₗ g₁) := by
  ext; rfl

@[coassoc_simps]
lemma map_map_assoc (f₁ : M →ₗ[R] N) (f₂ : N →ₗ[R] P) (g₁ : M' →ₗ[R] N') (g₂ : N' →ₗ[R] P')
    (h : P ⊗[R] P' →ₗ[R] Q) :
    (h ∘ₗ map f₂ g₂) ∘ₗ map f₁ g₁ = h ∘ₗ map (f₂ ∘ₗ f₁) (g₂ ∘ₗ g₁) := by
  ext; rfl

@[coassoc_simps]
lemma map_id_id : map (.id) (.id) = (.id : M ⊗[R] N →ₗ[R] _) := by ext; rfl

@[coassoc_simps]
lemma map_map_comp_assoc_eq_assoc (f : M →ₗ[R] M') (g : N →ₗ[R] N') (h : P →ₗ[R] P')
    (i : M' ⊗[R] (N' ⊗[R] P') →ₗ[R] Q) :
    (i ∘ₗ map f (map g h)) ∘ₗ α M N P = i ∘ₗ α M' N' P' ∘ₗ map (map f g) h := by ext; rfl

@[coassoc_simps]
lemma map_map_comp_assoc_eq_assoc' (f : M →ₗ[R] M') (g : N →ₗ[R] N') (h : P →ₗ[R] P')
    (i₁ : M' ⊗[R] Q' →ₗ[R] Q) (i₂ : N' ⊗[R] P' →ₗ[R] Q') :
    (i₁ ∘ₗ map f (i₂ ∘ₗ map g h)) ∘ₗ α M N P = i₁ ∘ₗ M' ◁ i₂ ∘ₗ α M' N' P' ∘ₗ map (map f g) h := by
  ext; rfl

@[coassoc_simps]
lemma map_map_comp_assoc_eq_assoc'' (f : M →ₗ[R] M') (g : N →ₗ[R] N') (h : P →ₗ[R] P')
    (i₂ : N' ⊗[R] P' →ₗ[R] Q') :
    map f (i₂ ∘ₗ map g h) ∘ₗ α M N P = M' ◁ i₂ ∘ₗ α M' N' P' ∘ₗ map (map f g) h := by
  ext; rfl

@[coassoc_simps]
lemma map_map_comp_assoc_symm_eq_assoc (f : M →ₗ[R] M') (g : N →ₗ[R] N') (h : P →ₗ[R] P')
    (i : (M' ⊗[R] N') ⊗[R] P' →ₗ[R] Q) :
    (i ∘ₗ map (map f g) h) ∘ₗ (α M N P).symm = i ∘ₗ (α M' N' P').symm ∘ₗ map f (map g h) := by
  ext; rfl

@[coassoc_simps]
lemma map_map_comp_assoc_symm_eq_assoc' (f : M →ₗ[R] M') (g : N →ₗ[R] N') (h : P →ₗ[R] P')
    (i₁ : Q' ⊗[R] P' →ₗ[R] Q) (i₂ : M' ⊗[R] N' →ₗ[R] Q') :
    (i₁ ∘ₗ map (i₂ ∘ₗ map f g) h) ∘ₗ (α M N P).symm =
      i₁ ∘ₗ i₂ ▷ P' ∘ₗ (α M' N' P').symm ∘ₗ map f (map g h) := by
  ext; rfl

@[coassoc_simps]
lemma map_map_comp_assoc_symm_eq_assoc'' (f : M →ₗ[R] M') (g : N →ₗ[R] N') (h : P →ₗ[R] P')
    (i₂ : M' ⊗[R] N' →ₗ[R] Q') :
    map (i₂ ∘ₗ map f g) h ∘ₗ (α M N P).symm = i₂ ▷ P' ∘ₗ (α M' N' P').symm ∘ₗ map f (map g h) := by
  ext; rfl

attribute [coassoc_simps] LinearMap.comp_id LinearMap.id_comp
  LinearMap.lTensor_def LinearMap.rTensor_def map_map_comp_assoc_eq map_map_comp_assoc_symm_eq
  map_id_id TensorProduct.AlgebraTensorModule.map_eq

open Lean.Parser.Tactic in
/-- `coassoc_simps` reassociates attempts to replace `x` by
`x₁ ⊗ₜ x₂` via linearity. This is an implementation detail that is used to set up tensor products
of coalgebras, bialgebras, and hopf algebras, and shouldn't be relied on downstream. -/
scoped macro "coassoc_simps" : tactic =>
  `(tactic|
    ( simp only [coassoc_simps]
      simp only [coassoc_cleanup_simps]
      repeat congr 1; guard_goal_nums 1
      ext; rfl))

end Coalgebra
