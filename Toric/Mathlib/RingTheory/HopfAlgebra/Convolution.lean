/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała, Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała, Yunzhou Xie
-/
import Mathlib.RingTheory.HopfAlgebra.Basic
import Toric.Mathlib.RingTheory.Bialgebra.Convolution

/-!
# Convolution product on Hopf algebra maps

This file constructs the ring structure on bialgebra homs `C → A` where `C` and `A` are Hopf
algebras and multiplication is given by
```
         .
        / \
f * g = f g
        \ /
         .
```
-/

suppress_compilation

open Algebra Coalgebra Bialgebra HopfAlgebra TensorProduct WithConv
open scoped RingTheory.LinearMap

variable {R A C : Type*} [CommSemiring R]

namespace HopfAlgebra
variable [CommSemiring A] [HopfAlgebra R A]

lemma antipode_mul_antidistrib (a b : A) : antipode R (a * b) = antipode R b * antipode R a := by
  let α := antipode R ∘ₗ .mul' R A
  let β : A ⊗[R] A →ₗ[R] A := .mul' R A ∘ₗ map (antipode R) (antipode R) ∘ₗ TensorProduct.comm R A A
  suffices h : toConv α = toConv β from congr($h (a ⊗ₜ b))
  apply left_inv_eq_right_inv (a := toConv (LinearMap.mul' R A : A ⊗[R] A →ₗ[R] A)) <;> ext a b
  · simp [α, ((ℛ R a).tmul (ℛ R b)).convMul_apply, ← Bialgebra.counit_mul, mul_comm b a,
      ← sum_antipode_mul_eq_algebraMap_counit ((ℛ R a).mul (ℛ R b))]
  · simp [((ℛ R a).tmul (ℛ R b)).convMul_apply, mul_comm, mul_mul_mul_comm, Finset.sum_mul_sum,
      ← Finset.sum_product', β, ← sum_mul_antipode_eq_algebraMap_counit (ℛ R a),
      ← sum_mul_antipode_eq_algebraMap_counit (ℛ R b)]

lemma antipode_mul_distrib (a b : A) : antipode R (a * b) = antipode R a * antipode R b := by
  rw [antipode_mul_antidistrib, mul_comm]

alias antipode_mul := antipode_mul_distrib

variable (R A) in
/-- The antipode of a commutative Hopf algebra as an algebra hom. -/
@[simps!]
def antipodeAlgHom : A →ₐ[R] A := .ofLinearMap (antipode R) antipode_one antipode_mul

@[simp] lemma toLinearMap_antipodeAlgHom : (antipodeAlgHom R A).toLinearMap = antipode R := rfl

end HopfAlgebra

namespace LinearMap

local notation "η" => Algebra.linearMap R A
local notation "ε" => counit (R := R) (A := C)
local notation "μ" => mul' R A
local notation "δ" => comul
local infix:70 " ⊗ₘ " => TensorProduct.map
-- local notation "α" => TensorProduct.assoc _ _ _

variable [Semiring C] [HopfAlgebra R C]

@[simp] lemma antipode_mul_id : toConv (antipode R (A := C)) * toConv id = 1 := by
  ext c; rw [(ℛ R c).convMul_apply]; simp [sum_antipode_mul_eq_algebraMap_counit (ℛ R c)]

@[simp] lemma id_mul_antipode : toConv id * toConv (antipode R (A := C)) = 1 := by
  ext c; rw [(ℛ R c).convMul_apply]; simp [sum_mul_antipode_eq_algebraMap_counit (ℛ R c)]

end LinearMap

namespace LinearMap
variable [Semiring C] [HopfAlgebra R C]

local notation "ε₁" => counit (R := R) (A := C)
local notation "ε₂" => counit (R := R) (A := C ⊗[R] C)
local notation "μ₁" => LinearMap.mul' R C
local notation "μ₂" => LinearMap.mul' R (C ⊗[R] C)
local notation "δ₁" => comul (R := R) (A := C)
local notation "δ₂" => comul (R := R) (A := C ⊗[R] C)
local notation "η₁" => Algebra.linearMap R C
local notation "η₂" => Algebra.linearMap R (C ⊗[R] C)
local infix:90 " ◁ " => LinearMap.lTensor
local notation:90 f:90 " ▷ " X:90 => LinearMap.rTensor X f
local notation "α" => TensorProduct.assoc R
local notation "β" => TensorProduct.comm R
local notation "𝑺" => antipode R (A := C)
local notation "𝑭" => δ₁ ∘ₗ 𝑺
local notation "𝑮" => (𝑺 ⊗ₘ 𝑺) ∘ₗ (β C C) ∘ₗ δ₁

lemma comul_right_inv : toConv δ₁ * toConv 𝑭 = 1 := by
  apply WithConv.ext
  simp only [LinearMap.convMul_def, LinearMap.convOne_def, ofConv_toConv]
  calc μ₂ ∘ₗ map δ₁ (δ₁ ∘ₗ 𝑺) ∘ₗ δ₁
      = μ₂ ∘ₗ ((δ₁ ∘ₗ id) ⊗ₘ (δ₁ ∘ₗ 𝑺)) ∘ₗ δ₁ := rfl
    _ = μ₂ ∘ₗ (δ₁ ⊗ₘ δ₁) ∘ₗ (id ⊗ₘ 𝑺) ∘ₗ δ₁ := by
        simp only [_root_.TensorProduct.map_comp, comp_assoc]
    _ = δ₁ ∘ₗ μ₁ ∘ₗ (id ⊗ₘ 𝑺) ∘ₗ δ₁ := by
        have : μ₂ ∘ₗ (δ₁ ⊗ₘ δ₁) = δ₁ ∘ₗ μ₁ := by ext; simp
        simp [this, ← comp_assoc]
    _ = δ₁ ∘ₗ (toConv id * toConv 𝑺).ofConv := by simp [LinearMap.convMul_def]
    _ = δ₁ ∘ₗ (1 : WithConv (C →ₗ[R] C)).ofConv := by rw [id_mul_antipode]
    _ = Algebra.linearMap R (C ⊗[R] C) ∘ₗ ε₁ := by
        simp [LinearMap.convOne_def, show δ₁ ∘ₗ η₁ = η₂ from by ext; simp; rfl, ← comp_assoc]

end LinearMap

namespace AlgHom
variable [CommSemiring A] [Semiring C] [Bialgebra R C] [HopfAlgebra R A]

lemma antipode_id_cancel : HopfAlgebra.antipodeAlgHom R A * AlgHom.id R A = 1 := by
  apply AlgHom.toLinearMap_injective
  apply WithConv.toConv_injective
  rw [AlgHom.toLinearMap_convMul, AlgHom.toLinearMap_convOne]
  simp [LinearMap.antipode_mul_id]

lemma counitAlgHom_comp_antipodeAlgHom :
    (counitAlgHom R A).comp (HopfAlgebra.antipodeAlgHom R A) = counitAlgHom R A :=
  AlgHom.toLinearMap_injective <| by simp

private lemma inv_convMul_cancel (f : C →ₐc[R] A) :
    (.comp (HopfAlgebra.antipodeAlgHom R A) f : C →ₐ[R] A) * f = 1 := calc
  _ = (.comp (HopfAlgebra.antipodeAlgHom R A) f : C →ₐ[R] A) * (.comp (.id R A) f) := by simp
  _ = .comp (lmul' R) (.comp (Algebra.TensorProduct.map (HopfAlgebra.antipodeAlgHom R A)
       (.id R A)) <| .comp (Algebra.TensorProduct.map f f) (comulAlgHom R C)) := by
    rw [convMul_def, Algebra.TensorProduct.map_comp]
    simp only [comp_assoc]
  _ = (HopfAlgebra.antipodeAlgHom R A * AlgHom.id R A).comp f := by
    simp only [convMul_def, BialgHomClass.map_comp_comulAlgHom]
    simp only [comp_assoc]
  _ = _ := by simp [antipode_id_cancel, convOne_def, comp_assoc]

end AlgHom

namespace BialgHom
variable [CommSemiring A] [CommSemiring C]

section HopfAlgebra
variable [HopfAlgebra R A] [HopfAlgebra R C] [IsCocomm R C]

/-- The antipode of a commutative cocommutative Hopf algebra as a coalgebra hom. -/
def antipodeBialgHom : C →ₐc[R] C where
  __ := antipodeAlgHom R (A := C)
  map_smul' := _
  counit_comp := counit_comp_antipode
  map_comp_comul := by sorry

instance : Inv (C →ₐc[R] A) where inv := antipodeBialgHom.comp

set_option linter.unusedSectionVars false in
lemma inv_def (f : C →ₐc[R] A) : f⁻¹ = antipodeBialgHom.comp f := rfl

set_option linter.unusedSectionVars false in
@[simp] lemma inv_apply (f : C →ₐc[R] A) (c : C) : f⁻¹ c = antipode R (f c) := rfl

private lemma inv_convMul_cancel (f : C →ₐc[R] A) : f⁻¹ * f = 1 := sorry

instance : CommGroup (C →ₐc[R] A) where inv_mul_cancel := inv_convMul_cancel

end HopfAlgebra
end BialgHom
