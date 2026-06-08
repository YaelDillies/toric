module

public import Mathlib.RingTheory.Bialgebra.TensorProduct
public import Toric.Mathlib.RingTheory.TensorProduct.Maps

public section

open Algebra Coalgebra TensorProduct

namespace Bialgebra
variable {ι κ R A B : Type*} [CommSemiring R]

@[simp]
lemma counitAlgHom_comp_includeRight [CommSemiring A] [Semiring B] [Algebra R A] [Bialgebra R B] :
    ((counitAlgHom A (A ⊗[R] B)).restrictScalars R).comp Algebra.TensorProduct.includeRight =
      (Algebra.ofId R A).comp (counitAlgHom R B) := by
  ext; simp [Algebra.algebraMap_eq_smul_one]

lemma comul_includeRight [CommSemiring A] [CommSemiring B] [Bialgebra R B] [Algebra R A] :
    (RingHomClass.toRingHom (Bialgebra.comulAlgHom A (A ⊗[R] B))).comp
      (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B))) =
      (Algebra.TensorProduct.mapRingHom (algebraMap R A)
        (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B)))
        (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B)))
        (by simp; rfl)
        (by simp; rfl)).comp
        (RingHomClass.toRingHom (Bialgebra.comulAlgHom R B)) := by
  ext x; simp [← (ℛ R x).eq, tmul_sum]

end Bialgebra
