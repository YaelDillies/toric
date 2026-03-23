module

public import Mathlib.Algebra.Polynomial.Bivariate

@[expose] public section

local notation3:max R "[X][Y]" => Polynomial (Polynomial R)
local notation3:max "Y" => Polynomial.C (Polynomial.X)

namespace Polynomial
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

-- TODO: bundle this
noncomputable def aevalAEval (x y : A) : R[X][Y] →ₐ[R] A where
  toFun p := eval y (eval₂ (mapRingHom (algebraMap R A)) (C x) p)
  map_one' := by simp
  map_mul' x y := by simp
  map_zero' := by simp
  map_add' x y := by simp
  commutes' r := by simp

@[simp] lemma aevalAEval_X (x y : A) : aevalAEval (R := R) x y X = x := by simp [aevalAEval]
@[simp] lemma aevalAEval_Y (x y : A) : aevalAEval (R := R) x y Y = y := by simp [aevalAEval]

end Polynomial
