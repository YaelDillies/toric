module

public import Mathlib.RingTheory.AdjoinRoot

@[expose] public section

open Algebra TensorProduct
open scoped Polynomial

noncomputable section

namespace AdjoinRoot
variable {R S T U : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
  [CommRing U] [Algebra R U] {p : Polynomial S}

-- TODO: get rid of rfl
variable (p) in
def tensorAlgEquiv (p : S[X]) (q : (T ⊗[R] S)[X]) (h : p.map includeRight.toRingHom = q) :
    T ⊗[R] AdjoinRoot p ≃ₐ[T] AdjoinRoot q := by
  refine .ofAlgHom
    (Algebra.TensorProduct.lift (algHom T T _)
      (mapAlgHom includeRight p q <| by exact h.symm.dvd) fun _ _ ↦ .all ..)
    (liftAlgHom _ (Algebra.TensorProduct.map (AlgHom.id T T)
      (((Algebra.ofId S (AdjoinRoot p))).restrictScalars R)) (1 ⊗ₜ root _) ?_) ?_ ?_
  · simp only [← h, AlgHom.toRingHom_eq_coe]
    rw [Polynomial.eval₂_map]
    change Polynomial.eval₂ ((Algebra.TensorProduct.map (AlgHom.id R T) _).comp _).toRingHom _ _ = _
    simp only [map_comp_includeRight, AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom,
      AlgHom.coe_restrictScalars, ← Polynomial.eval₂_map]
    change Polynomial.eval₂ _ ((RingHomClass.toRingHom includeRight) (root p)) (p.map (of _)) = _
    rw [Polynomial.eval₂_hom]
    simp [Polynomial.eval_map]
  · ext
    · simp [Algebra.ofId_apply, ← AlgHom.toRingHom_eq_coe]
      rfl
    simp
  · ext : 1
    · ext
    ext : 2 <;> simp [← AlgHom.toRingHom_eq_coe]
    rfl

@[simp] lemma tensorAlgEquiv_root (p : S[X]) (q : Polynomial (T ⊗[R] S)) (h) :
    tensorAlgEquiv p q h (1 ⊗ₜ root p) = root q := by simp [tensorAlgEquiv]

@[simp] lemma tensorAlgEquiv_of (p : S[X]) (q : Polynomial (T ⊗[R] S)) (h) {x : S} :
    tensorAlgEquiv p q h (1 ⊗ₜ of p x) = of q (1 ⊗ₜ x):= by simp [tensorAlgEquiv]

end AdjoinRoot
