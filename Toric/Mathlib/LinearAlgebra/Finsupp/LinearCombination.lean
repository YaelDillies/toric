module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

open Submodule

public section

namespace Finsupp
variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

lemma mem_span_setOf_iff_exists_linearCombination {p : M → Prop} {x : M} :
    x ∈ span R {a | p a} ↔ ∃ l : {a // p a} →₀ R, linearCombination R (↑) l = x :=
  mem_span_iff_linearCombination ..

end Finsupp
