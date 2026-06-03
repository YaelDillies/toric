module

public import Mathlib.RingTheory.Coalgebra.GroupLike

public section

namespace GroupLike
variable {R A : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A] [Coalgebra R A]

@[simp] lemma val_valEquiv (x : GroupLike R A) : (valEquiv x).val = x.val := rfl

@[simp] lemma val_valEquiv_symm_apply (x : {x : A // IsGroupLikeElem R x}) :
    (valEquiv.symm x).val = x.val := rfl

end GroupLike
