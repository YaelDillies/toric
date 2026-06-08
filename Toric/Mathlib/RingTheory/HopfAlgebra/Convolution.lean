module

public import Mathlib.RingTheory.HopfAlgebra.Convolution

public section

suppress_compilation

open Algebra Coalgebra Bialgebra HopfAlgebra TensorProduct WithConv
open scoped RingTheory.LinearMap

variable {R A C : Type*} [CommSemiring R]

namespace AlgHom
variable [CommSemiring A] [CommSemiring C] [Bialgebra R C] [HopfAlgebra R A]

private lemma inv_convMul_cancel (f : WithConv <| C →ₐc[R] A) :
    (toConv (.comp (antipodeAlgHom R A) f.ofConv) * toConv f.ofConv.toAlgHom) = 1 := calc
  _ = toConv (.comp (HopfAlgebra.antipodeAlgHom R A) f.ofConv : C →ₐ[R] A) *
        toConv (.comp (.id R A) f.ofConv) := by simp
  _ = toConv (.comp (lmul' R) (.comp (Algebra.TensorProduct.map (HopfAlgebra.antipodeAlgHom R A)
       (.id R A)) <| .comp (Algebra.TensorProduct.map f.ofConv f.ofConv) (comulAlgHom R C))) := by
    rw [convMul_def, Algebra.TensorProduct.map_comp]
    simp only [comp_assoc]
  _ = toConv ((toConv (antipodeAlgHom R A) * toConv (AlgHom.id R A)).ofConv.comp f.ofConv) := by
    simp only [convMul_def, BialgHom.map_comp_comulAlgHom]
    simp only [comp_assoc]
  _ = _ := by simp [antipode_id_cancel, convOne_def, comp_assoc]

end AlgHom

namespace BialgHom
variable [CommSemiring A] [CommSemiring C]

section HopfAlgebra
variable [HopfAlgebra R A] [HopfAlgebra R C] [IsCocomm R C]

/-- The antipode of a commutative cocommutative Hopf algebra as a coalgebra hom. -/
@[expose, simps]
def antipodeBialgHom : C →ₐc[R] C where
  __ := antipodeAlgHom R C
  map_smul' := _
  counit_comp := counit_comp_antipode
  map_comp_comul := by
    have : IsCocomm R C := inferInstance
    sorry

instance : Inv (WithConv <| C →ₐc[R] A) where inv f := toConv <| f.ofConv.comp antipodeBialgHom

set_option linter.unusedSectionVars false in
lemma inv_def (f : WithConv <| C →ₐc[R] A) : f⁻¹ = toConv (f.ofConv.comp antipodeBialgHom) := rfl

set_option linter.unusedSectionVars false in
@[simp] lemma inv_apply (f : WithConv <| C →ₐc[R] A) (c : C) : f⁻¹ c = f (antipode R c) := rfl

lemma inv_convMul_cancel (f : WithConv <| C →ₐc[R] A) : f⁻¹ * f = 1 := sorry

instance : CommGroup (WithConv <| C →ₐc[R] A) where inv_mul_cancel := inv_convMul_cancel

end HopfAlgebra
end BialgHom
