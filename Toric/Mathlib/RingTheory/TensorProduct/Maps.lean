module

public import Mathlib.RingTheory.TensorProduct.Maps

public section

open TensorProduct

namespace Algebra.TensorProduct
variable {R S A B C D : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S] [Semiring A]
  [Algebra R A] [Algebra S A] [IsScalarTower R S A] [Semiring B] [Algebra R B] [Semiring C]
  [Algebra R C] [Algebra S C] [IsScalarTower R S C] [Semiring D] [Algebra R D]

@[simp] lemma map_comp_includeLeftRingHom (f : A →ₐ[S] C) (g : B →ₐ[R] D) :
    (map f g : A ⊗[R] B →+* C ⊗[R] D).comp includeLeftRingHom =
      includeLeftRingHom.comp (f : A →+* C) := by ext; simp

@[simp] lemma rid_comp_includeLeftRingHom :
    (Algebra.TensorProduct.rid R S A : A ⊗[R] R →+* A).comp includeLeftRingHom = .id A := by
  ext; simp

end Algebra.TensorProduct

variable {R S T R' S' T' : Type*}
  [CommSemiring R] [CommSemiring S] [CommSemiring T] [Algebra R S] [Algebra R T]
  [CommSemiring R'] [CommSemiring S'] [CommSemiring T'] [Algebra R' S'] [Algebra R' T']
  (fR : R →+* R') (fS : S →+* S') (fT : T →+* T')
  (HS : fS.comp (algebraMap _ _) = (algebraMap _ _).comp fR)
  (HT : fT.comp (algebraMap _ _) = (algebraMap _ _).comp fR)

/-- Heterobasic version of `Algebra.TensorProduct.map` as a ring homomorphism. -/
@[expose]
noncomputable def Algebra.TensorProduct.mapRingHom : S ⊗[R] T →+* S' ⊗[R'] T' :=
  letI := fR.toAlgebra
  letI := ((algebraMap R' S').comp fR).toAlgebra
  letI := ((algebraMap R' T').comp fR).toAlgebra
  letI := fS.toAlgebra
  letI := fT.toAlgebra
  letI : IsScalarTower R R' S' := .of_algebraMap_eq' rfl
  letI : IsScalarTower R R' T' := .of_algebraMap_eq' rfl
  letI : IsScalarTower R S S' := .of_algebraMap_eq' HS.symm
  letI : IsScalarTower R T T' := .of_algebraMap_eq' HT.symm
  (lift (R := R) (S := R) (includeLeft.comp (IsScalarTower.toAlgHom R S S'))
    ((includeRight.restrictScalars R).comp (IsScalarTower.toAlgHom R T T'))
    (fun _ _ ↦ .all _ _)).toRingHom

@[simp]
lemma Algebra.TensorProduct.mapRingHom_tmul (s : S) (t : T) :
    mapRingHom fR fS fT HS HT (s ⊗ₜ t) = fS s ⊗ₜ fT t := by
  trans (fS s * 1 : S') ⊗ₜ[R'] (1 * fT t : T')
  · dsimp [mapRingHom, lift_tmul]; rfl
  · simp

@[simp]
lemma Algebra.TensorProduct.mapRingHom_comp_includeLeftRingHom :
    (mapRingHom fR fS fT HS HT).comp (includeLeftRingHom) = includeLeftRingHom.comp fS := by
  ext; simp

@[simp]
lemma Algebra.TensorProduct.mapRingHom_comp_includeRight :
    (mapRingHom fR fS fT HS HT).comp (RingHomClass.toRingHom includeRight) =
      (RingHomClass.toRingHom includeRight).comp fT := by
  ext; simp
