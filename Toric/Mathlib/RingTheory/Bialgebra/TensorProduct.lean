import Mathlib.RingTheory.Bialgebra.TensorProduct
import Toric.Mathlib.RingTheory.Coalgebra.Hom
import Toric.Mathlib.RingTheory.TensorProduct.Maps

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

section Semiring
variable [Semiring A] [Bialgebra R A] {a b : A}

variable (R A) in
/-- Multiplication on a bialgebra as a coalgebra hom. -/
def mulCoalgHom : A ⊗[R] A →ₗc[R] A where
  __ := LinearMap.mul' R A
  map_smul' a b := by induction b <;> simp
  counit_comp := by ext; simp [mul_comm]
  map_comp_comul := by
    ext a b
    simp [← (ℛ R a).eq, ← (ℛ R b).eq, sum_tmul]
    simp [tmul_sum, Finset.sum_mul_sum]

@[simp] lemma mulCoalgHom_apply (a b : A) : mulCoalgHom R A (a ⊗ₜ b) = a * b := rfl

/-- Representations of `a` and `b` yield a representation of `a ⊗ b`. -/
@[simps]
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

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Bialgebra R A]
  [Bialgebra R B] {a a₁ a₂ : A} {b : B}

/-- Representations of `a₁` and `a₂` yield a representation of `a₁ * a₂`. -/
@[simps!, simps! index] protected noncomputable
def _root_.Coalgebra.Repr.mul (ℛ₁ : Coalgebra.Repr R a₁) (ℛ₂ : Coalgebra.Repr R a₂) :
    Coalgebra.Repr R (a₁ * a₂) := (ℛ₁.tmul ℛ₂).induced (R := R) (mulCoalgHom R A)

end Semiring

section CommSemiring
variable [CommSemiring A] [CommSemiring B] [Bialgebra R A] [Bialgebra R B] {a b : A}

variable (R A B) in
/-- The tensor product of `R`-bialgebras is commutative, up to bialgebra isomorphism. -/
def TensorProduct.comm : A ⊗[R] B ≃ₐc[R] B ⊗[R] A :=
  .ofAlgEquiv (Algebra.TensorProduct.comm R A B) (by ext <;> simp) <| by
    ext a <;>
    · dsimp
      rw [← (ℛ R a).eq]
      simp [tmul_sum, sum_tmul]
      rfl

variable (R A) in
/-- Multiplication on a commutative bialgebra as a bialgebra hom. -/
def mulBialgHom : A ⊗[R] A →ₐc[R] A where
  __ := lmul' R
  __ := mulCoalgHom R A

@[simp] lemma mulBialgHom_apply (a b : A) : mulBialgHom R A (a ⊗ₜ b) = a * b := rfl

variable (R A) in
def comulBialgHom [IsCocomm R A] : A →ₐc[R] A ⊗[R] A where
  __ := comulAlgHom R A
  __ := comulCoalgHom R A

variable (R A) in
lemma comm_comp_comulBialgHom [IsCocomm R A] :
    (TensorProduct.comm R A A).toBialgHom.comp (comulBialgHom R A) = comulBialgHom R A := by
  ext; exact comm_comul _ _

end CommSemiring
end Bialgebra
