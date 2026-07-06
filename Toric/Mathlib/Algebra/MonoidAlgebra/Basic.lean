module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Toric.Mathlib.Algebra.MonoidAlgebra.MapDomain

public section

namespace AddMonoidAlgebra
variable {R A M : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [AddMonoid M]

@[simp]
lemma toMultiplicativeAlgEquiv_single (m : M) (a : A) :
    toMultiplicativeAlgEquiv (R := R) A M (single m a) = .single (.ofAdd m) a := by
  simp [toMultiplicativeAlgEquiv]

end AddMonoidAlgebra
