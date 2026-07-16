/-
Copyright (c) 2025 Patrick Luo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Luo
-/
module

public import Mathlib.Algebra.AffineMonoid.Embedding
public import Mathlib.GroupTheory.MonoidLocalization.Finite
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Toric.ToricVariety.Defs

/-!
# Affine monoids give rise to toric varieties
-/

public section

suppress_compilation

open Algebra AlgebraicGeometry Scheme CategoryTheory Limits AddMonoidAlgebra AddLocalization
  AffineAddMonoid

universe u
variable {𝕜 M : Type u} [Field 𝕜] [AddCancelCommMonoid M] [AddMonoid.FG M] [IsAddTorsionFree M]

namespace AffineToricVarietyFromMonoid

noncomputable instance instToricVariety : ToricVariety 𝕜 (Diag (Spec <| .of 𝕜) M) where
  torus := Diag (Spec <| .of 𝕜) (GrothendieckAddGroup M)
  modObjTorus := sorry
  torusEmb := sorry
  isOver_torusEmb := sorry
  isOpenImmersion_torusEmb := by
    stop
    obtain ⟨s, hsgen⟩ := AddMonoid.FG.fg_top (N := M)
    let x : AddMonoidAlgebra R M := ∏ z ∈ s, single z 1
    let alg : Algebra R[M] R[FreeAbelianGroup <| Fin <| dim M] :=
      (AddMonoidAlgebra.mapDomainAlgHom R _ <| embedding M).toAlgebra
    have _ : IsLocalization.Away x (AddMonoidAlgebra R <| FreeAbelianGroup <| Fin <| dim M) := by
      sorry
    exact .of_isLocalization x (M := R[FreeAbelianGroup <| Fin <| dim M])
  isDominant_torusEmb := by -- integral + open nonempty
    stop
    let img := RingHom.range (AddMonoidAlgebra.mapDomainRingHom R <| embedding M)
    have img_domain := Subring.instIsDomainSubtypeMem img
    have := (AlgebraicGeometry.affine_isIntegral_iff (CommRingCat.of (AddMonoidAlgebra R M)))
    sorry
  torusMul_comp_torusEmb := by
    stop
    simp [← Spec.map_comp, ← CommRingCat.ofHom_comp, pullback.condition]
    sorry

end AffineToricVarietyFromMonoid
