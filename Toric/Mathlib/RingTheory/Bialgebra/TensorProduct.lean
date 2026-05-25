module

public import Mathlib.RingTheory.Bialgebra.TensorProduct
public import Mathlib.Tactic.SuppressCompilation
public import Toric.Mathlib.RingTheory.TensorProduct.Maps

public section

suppress_compilation

open Algebra Coalgebra TensorProduct

namespace Bialgebra
variable {R A B : Type*} [CommSemiring R]

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

section CommSemiring
variable [Semiring A] [Semiring B] [Bialgebra R A] [Bialgebra R B] {a b : A}

/-- Representations of `a` and `b` yield a representation of `a ⊗ b`. -/
@[expose, simps]
protected def _root_.Coalgebra.Repr.tmul (ℛa : Coalgebra.Repr R a) (ℛb : Coalgebra.Repr R b) :
    Coalgebra.Repr R (a ⊗ₜ[R] b) where
  ι := ℛa.ι × ℛb.ι
  index := ℛa.index ×ˢ ℛb.index
  left i := ℛa.left i.1 ⊗ₜ ℛb.left i.2
  right i := ℛa.right i.1 ⊗ₜ ℛb.right i.2
  eq := by
    simp only [comul_def, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      AlgebraTensorModule.map_tmul]
    rw [← ℛa.eq, ← ℛb.eq]
    simp_rw [sum_tmul, tmul_sum, ← Finset.sum_product', map_sum]
    simp

/-- Representations of `a` and `b` yield a representation of `a * b`. -/
@[expose, simps!, simps! index] protected noncomputable
def _root_.Coalgebra.Repr.mul (ℛ₁ : Coalgebra.Repr R a) (ℛ₂ : Coalgebra.Repr R b) :
    Coalgebra.Repr R (a * b) := (ℛ₁.tmul ℛ₂).induced (R := R) (mulCoalgHom R A)

end CommSemiring
end Bialgebra
