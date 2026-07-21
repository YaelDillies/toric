module

public import Mathlib.Algebra.Category.Ring.Under.Basic

public section

open CategoryTheory.ConcreteCategory

namespace AlgHom
universe u
variable {R : CommRingCat.{u}} {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

-- TODO: Replace in mathlib
@[simp] lemma toUnder_right' (f : A →ₐ[R] B) : f.toUnder.right = ofHom (f : A →+* B) := rfl

end AlgHom
