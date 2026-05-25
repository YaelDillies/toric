/-
Copyright (c) 2025 Patrick Luo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Patrick Luo, Paul Lezeau
-/
module

public import Mathlib.GroupTheory.FreeAbelianGroup
public import Toric.Mathlib.RingTheory.Bialgebra.MonoidAlgebra

/-!
# Multivariate Laurent polynomials

This file defines Laurent polynomial rings over a base ring (or even semiring),
with variables from a general type `σ` (which could be infinite).
-/

@[expose] public section

open AddMonoidAlgebra

variable (σ R S : Type*)

abbrev MvLaurentPolynomial [Semiring R] := AddMonoidAlgebra R <| FreeAbelianGroup σ

noncomputable
def MvLaurentPolynomial.liftEquiv [CommRing R] [CommRing S] [Algebra R S] :
    (σ → Sˣ) ≃* (WithConv <| MvLaurentPolynomial σ R →ₐ[R] S) := by
  refine .trans ?_ <| MonoidAlgebra.liftMulEquiv _ _ <| Abelianization <| FreeGroup σ
  exact
  { toFun f := (Units.coeHom S).comp (Abelianization.lift (FreeGroup.lift f))
    invFun f n := f.toHomUnits (.of (.of n))
    left_inv _ := by ext; simp
    right_inv f := by ext; simp
    map_mul' x y := by ext; simp }
