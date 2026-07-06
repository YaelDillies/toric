module

public import Mathlib.Algebra.MonoidAlgebra.MapDomain

public section

namespace AddMonoidAlgebra
variable {R M : Type*} [Semiring R] [Add M]

@[simp]
lemma toMultiplicative_single (m : M) (r : R) :
    AddMonoidAlgebra.toMultiplicative R M (single m r) = .single (.ofAdd m) r := by
  simp [AddMonoidAlgebra.toMultiplicative]

end AddMonoidAlgebra
