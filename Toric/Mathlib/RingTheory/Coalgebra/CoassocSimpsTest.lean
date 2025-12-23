import Toric.Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Coalgebra.Basic

section Test

open TensorProduct in
theorem LinearMap.mul'_comp_map_lid_comp
    {R M N A : Type*} [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]
    [AddCommMonoid M] [Module R M] [Coalgebra R A] [SMulCommClass R A A] [IsScalarTower R A A]
    [AddCommMonoid N] [Module R N]
    (f : M →ₗ[R] R ⊗[R] A) (g : N →ₗ[R] _) :
    mul' R A ∘ₗ map (TensorProduct.lid R A ∘ₗ f) g =
      TensorProduct.lid R A ∘ₗ (mul' R A).lTensor R ∘ₗ TensorProduct.assoc R R A A ∘ₗ map f g := by
  trans mul' R A ∘ₗ ((TensorProduct.lid R _).toLinearMap.rTensor _) ∘ₗ (TensorProduct.map f g)
  · ext; simp
  simp only [← LinearMap.comp_assoc]
  congr 1
  ext
  simp

variable {R A : Type*} [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A] [Coalgebra R A]
  [SMulCommClass R A A] [IsScalarTower R A A]

open Coalgebra TensorProduct LinearMap

local notation3 "δ" => comul (R := R) (A := A)
local notation3 "ε" => counit (R := R) (A := A)
local notation3 "μ" => LinearMap.mul' R A
local notation3 "λ" => (TensorProduct.lid R _).toLinearMap
local notation3 "λ⁻¹" => (TensorProduct.lid R _).symm.toLinearMap
local infixl:85 " ⊗ₘ " => TensorProduct.map
local notation3 "α" => (TensorProduct.assoc R _ _ _).toLinearMap
local notation3 "α⁻¹" => (TensorProduct.assoc R _ _ _).symm.toLinearMap

/-- If `(id ⊗ mul) ∘ assoc ∘ (comul ⊗ id) = (mul ⊗ id) ∘ assoc.symm ∘ (id ⊗ comul)`,
then `(id ⊗ mul) ∘ assoc ∘ (comul ⊗ id) = comul ∘ mul`. -/
theorem LinearMap.lTensor_mul'_comp_assoc_comp_rTensor_comul_of
    (h : (id ⊗ₘ μ) ∘ₗ α ∘ₗ (δ ⊗ₘ id) = (μ ⊗ₘ id) ∘ₗ α⁻¹ ∘ₗ (id ⊗ₘ δ)) :
    id ⊗ₘ μ ∘ₗ α ∘ₗ δ ⊗ₘ id = δ ∘ₗ μ := calc
    _ = μ ⊗ₘ id ∘ₗ α⁻¹ ∘ₗ (λ ∘ₗ ε ⊗ₘ id ∘ₗ δ) ⊗ₘ δ := by
      simp only [h, map_counit_comp_comul_left, coassoc_simps]
    _ = λ ∘ₗ ε ⊗ₘ id ∘ₗ α ∘ₗ (μ ⊗ₘ id ∘ₗ α⁻¹ ∘ₗ id ⊗ₘ δ) ⊗ₘ id ∘ₗ α⁻¹ ∘ₗ id ⊗ₘ δ := by
      rw [← h]
      simp only [lid_tensor, coassoc_simps, assoc_symm_comp_map δ, mul'_comp_map_lid_comp]
    _ = λ ∘ₗ ε ⊗ₘ δ ∘ₗ (id ⊗ₘ μ ∘ₗ α ∘ₗ δ ⊗ₘ id) := by
      simp only [assoc_tensor, h, coassoc_simps]
    _ = λ ∘ₗ id ⊗ₘ (δ ∘ₗ μ) ∘ₗ α ∘ₗ (ε ⊗ₘ id ∘ₗ δ) ⊗ₘ id := by
      simp only [coassoc_simps]
    _ = δ ∘ₗ μ := by
      simp only [coassoc_simps, map_counit_comp_comul_left]

end Test
