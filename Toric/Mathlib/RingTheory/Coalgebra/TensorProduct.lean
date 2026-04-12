module

public import Mathlib.RingTheory.Coalgebra.TensorProduct

meta import Mathlib.RingTheory.Coalgebra.CoassocSimps

import Mathlib.Algebra.Algebra.Bilinear

public section

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

variable (R C) in
/-- Comultiplication as a coalgebra hom. -/
@[expose] noncomputable def comulCoalgHom : C →ₗc[R] C ⊗[R] C where
  __ := δ
  counit_comp := by
    simp only [counit_def, AlgebraTensorModule.rid_eq_rid, ← lid_eq_rid]
    calc
        (μ ∘ₗ (ε ⊗ₘ ε)) ∘ₗ δ
    _ = (μ ∘ₗ ε ▷ R) ∘ₗ (C ◁ ε ∘ₗ δ) := by simp [coassoc_simps]
    _ = ε := by ext; simp
  map_comp_comul := by simp [comul_def, coassoc_simps]

end Coalgebra
