module

public import Mathlib.Algebra.Algebra.Equiv

public section

lemma AlgEquiv.image_symm_eq_preimage {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] (e : A ≃ₐ[R] B) (S : Set B) :
    e.symm '' S = e ⁻¹' S := e.toLinearEquiv.image_symm_eq_preimage _
