import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.RingTheory.Coalgebra.TensorProduct
import Toric.Mathlib.RingTheory.Coalgebra.CoassocSimps

open TensorProduct

namespace Coalgebra

variable {R C : Type*} [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
  [IsCocomm R C]

local notation3 "ε" => counit (R := R) (A := C)
local notation3 "μ" => LinearMap.mul' R R
local notation3 "δ" => comul (R := R)
local infix:90 " ◁ " => LinearMap.lTensor
local notation3:90 f:90 " ▷ " X:90 => LinearMap.rTensor X f
local infix:70 " ⊗ₘ " => _root_.TensorProduct.map
local notation3 "α" => _root_.TensorProduct.assoc R
local notation "ββ" => TensorProduct.tensorTensorTensorComm R C C C C

variable (R C) in
/-- Comultiplication as a coalgebra hom. -/
noncomputable def comulCoalgHom : C →ₗc[R] C ⊗[R] C where
  __ := δ
  counit_comp := by
    simp only [counit_def, AlgebraTensorModule.rid_eq_rid, ← lid_eq_rid]
    calc
        (μ ∘ₗ (ε ⊗ₘ ε)) ∘ₗ δ
    _ = (μ ∘ₗ ε ▷ R) ∘ₗ (C ◁ ε ∘ₗ δ) := by
      rw [LinearMap.comp_assoc, LinearMap.comp_assoc, ← LinearMap.comp_assoc _ _ (.rTensor _ _)]
      simp
    _ = ε := by ext; simp
  map_comp_comul := by
    let e : (C ⊗[R] C) ⊗[R] (C ⊗[R] C) ≃ₗ[R] C ⊗[R] ((C ⊗[R] C) ⊗[R] C) :=
      _root_.TensorProduct.assoc _ _ _ _ ≪≫ₗ
        TensorProduct.congr (.refl _ _) (_root_.TensorProduct.assoc _ _ _ _).symm
    rw [← e.comp_toLinearMap_eq_iff, TensorProduct.comul_def]
    trans (((TensorProduct.comm _ _ _).toLinearMap ∘ₗ δ).rTensor _ ∘ₗ δ).lTensor _ ∘ₗ δ
    · rw [Coalgebra.comm_comp_comul]
      simp [e, coassoc_simps]
    · simp only [e, AlgebraTensorModule.tensorTensorTensorComm, coassoc_simps]

end Coalgebra
