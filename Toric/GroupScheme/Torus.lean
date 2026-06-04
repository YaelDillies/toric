/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała, Andrew Yang
-/
module

public import Mathlib.Algebra.FreeAbelianGroup.Finsupp
public import Mathlib.FieldTheory.Separable
public import Toric.GroupScheme.Diagonalizable
public import Toric.MvLaurentPolynomial

/-!
# The standard algebraic torus

This file defines the standard algebraic torus over `Spec R` as `Spec (R ⊗ ℤ[Fₙ])`.
-/

public noncomputable section

open CategoryTheory Opposite Limits
open scoped AddMonoidAlgebra SpecOfNotation

universe u

namespace AlgebraicGeometry.Scheme
section IsSplitTorusOver
variable {G H S : Scheme.{u}} [G.Over S] [H.Over S] [GrpObj (asOver G S)]
  [GrpObj (asOver H S)]

-- TODO: Move me!
instance {M N : Scheme.{u}} [M.Over S] [N.Over S] [MonObj (asOver M S)] [MonObj (asOver N S)]
    (e : M ≅ N) [e.hom.IsOver S] [IsMonHom (e.hom.asOver S)] : IsMonHom (e.asOver S).hom := ‹_›

variable (G S) in
@[mk_iff]
class IsSplitTorusOver : Prop where
  existsIso :
    ∃ (A : Type u) (_ : AddCommGroup A) (_ : Module.Free ℤ A) (e : G ≅ Diag S A)
      (_ : e.hom.IsOver S), IsMonHom (e.hom.asOver S)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance diag_isSplitTorusOver {A : Type u} [AddCommGroup A] [Module.Free ℤ A] :
    (Diag S A).IsSplitTorusOver S :=
  ⟨A, ‹_›, ‹_›, by exact .refl (S.Diag A), by dsimp; infer_instance, by dsimp; infer_instance⟩

set_option backward.defeqAttrib.useBackward true in
lemma IsSplitTorusOver.of_isIso [H.IsSplitTorusOver S] (f : G ⟶ H) [IsIso f] [f.IsOver S]
    [IsMonHom (f.asOver S)] : G.IsSplitTorusOver S :=
  have : IsMonHom ((asIso f).hom.asOver S) := ‹_›
  let ⟨A, _, _, e, _, _⟩ := ‹H.IsSplitTorusOver S›
  ⟨A, _, ‹_›, (asIso f).trans e, by dsimp; infer_instance, by dsimp; infer_instance⟩

lemma IsSplitTorusOver.of_isIso' [G.IsSplitTorusOver S]
    (f : G ⟶ H) [IsIso f] [f.IsOver S] [IsMonHom (f.asOver S)] : H.IsSplitTorusOver S :=
  have : IsMonHom ((inv f).asOver S) := by
    simpa using inferInstanceAs <| IsMonHom (asIso <| f.asOver S).inv
  .of_isIso (inv f)

lemma IsSplitTorusOver.of_iso [H.IsSplitTorusOver S] (e : G ≅ H) [e.hom.IsOver S]
    [IsMonHom (e.hom.asOver S)] : G.IsSplitTorusOver S := of_isIso e.hom

set_option backward.defeqAttrib.useBackward true in
variable (G S) in
/-- Every split torus that's locally of finite type is isomorphic to `𝔾ₘⁿ` for some `n`. -/
lemma exists_iso_diag_finite_of_isSplitTorusOver_locallyOfFiniteType [G.IsSplitTorusOver S]
    [hG : LocallyOfFiniteType (G ↘ S)] [Nonempty S] :
    ∃ (ι : Type u) (_ : Finite ι) (e : G ≅ Diag S ℤ[ι]) (_ : e.hom.IsOver S),
      IsMonHom (e.hom.asOver S) := by
  obtain ⟨A, _, _, e, _, _⟩ := ‹G.IsSplitTorusOver S›
  replace hG : LocallyOfFiniteType (Diag S A ↘ S) := by
    rw [← MorphismProperty.cancel_left_of_respectsIso @LocallyOfFiniteType e.hom]
    erw [comp_over e.hom]
    assumption
  rw [locallyOfFiniteType_diag_iff] at hG
  exact ⟨Module.Free.ChooseBasisIndex ℤ A, inferInstance,
    e.trans <| Diag.mapIso S (Module.Free.chooseBasis ℤ A).repr.toAddEquiv,
    by dsimp; infer_instance, by dsimp; infer_instance⟩

end IsSplitTorusOver

section IsTorusOver
variable {k : Type u} [Field k] {G H : Scheme.{u}} [G.Over Spec(k)] [H.Over Spec(k)]
  [GrpObj (G.asOver Spec(k))] [GrpObj (H.asOver Spec(k))]

variable (k G) in
@[mk_iff]
class IsTorusOver : Prop where
  existsSplit :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L) (_ : Algebra.IsSeparable k L),
      (pullback (G ↘ Spec(k)) <| Spec.map <| CommRingCat.ofHom <|
        algebraMap k L).IsSplitTorusOver Spec(L)

set_option backward.isDefEq.respectTransparency false in
instance [G.IsSplitTorusOver Spec(k)] : G.IsTorusOver k := by
  refine ⟨k, ‹_›, inferInstance, inferInstance, ?_⟩
  simp only [Algebra.algebraMap_self, CommRingCat.ofHom_id]
  suffices (pullback (G ↘ Spec(k)) (𝟙 _)).IsSplitTorusOver Spec(k) by
    convert this <;> simp
  exact .of_isIso (pullback.fst (G ↘ Spec(k)) (𝟙 _))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma IsTorusOver.of_iso (e : G ≅ H) [e.hom.IsOver Spec(k)] [IsMonHom (e.hom.asOver Spec(k))]
    [H.IsTorusOver k] : G.IsTorusOver k := by
  obtain ⟨L, _, _, _, hH⟩ := ‹H.IsTorusOver k›
  refine ⟨L, _, ‹_›, ‹_›, ?_⟩
  let e'' := (Over.pullback <| Spec.map <| CommRingCat.ofHom <| algebraMap k L).mapGrp.mapIso <|
    Grp.mkIso' <| e.asOver Spec(k)
  let e' := (Grp.forget _ ⋙ Over.forget _).mapIso e''
  dsimp at e'
  have : e'.hom.IsOver Spec(L) := by simp [e', e'']
  have : IsMonHom <| e'.hom.asOver Spec(L) := by simpa using! Mon.instIsMonHomHom e''.hom.hom
  exact .of_iso e'

lemma IsTorusOver.of_isIso [H.IsTorusOver k]
    (f : G ⟶ H) [IsIso f] [f.IsOver Spec(k)] [IsMonHom (f.asOver Spec(k))] :
    G.IsTorusOver k :=
  have : IsMonHom (Hom.asOver (asIso f).hom Spec(k)) := ‹_›
  .of_iso (asIso f)

end IsTorusOver

/-- The (split) algebraic torus over `S` indexed by `σ`. -/
abbrev SplitTorus (S : Scheme) (σ : Type u) : Scheme.{u} := Diag S <| FreeAbelianGroup σ

@[inherit_doc SplitTorus]
notation3 "𝔾ₘ[" S ", " σ "]" => SplitTorus S σ

/-- The multiplicative group over `S`. -/
notation3 "𝔾ₘ["S"]" => 𝔾ₘ[S, PUnit]

-- attribute [ext] Comma

-- def SplitTorus.representableBy (S : Scheme) (σ : Type*) :
--     ((Over.forget _).op ⋙ Scheme.Γ ⋙ forget₂ _ CommMonCat ⋙ CommMonCat.units ⋙
--       CommGrp.coyonedaRight.obj (op σ) ⋙ CategoryTheory.forget _).RepresentableBy
--       (𝔾ₘ[S, σ].asOver S) := by
--   letI X :=
--   (((((Over.mapPullbackAdj (specULiftZIsTerminal.from S)).comp
--     (Over.equivalenceOfIsTerminal specULiftZIsTerminal).toAdjunction).comp <|
--     (ΓSpec.adjunction.comp <| (CommRingCat.forget₂Adj CommRingCat.isInitial).op.comp <|
--       CommGrp.forget₂CommMonAdj.op.comp <|
--         commGroupAddCommGroupEquivalence.symm.toAdjunction.op.comp <|
--           AddCommGrp.adj.op)).representableBy (op σ)).ofIso <|
--     isoWhiskerRight (NatIso.op (Over.forgetMapTerminal _ _))
--       (Scheme.Γ ⋙ forget₂ _ CommMonCat ⋙
--         CommMonCat.units ⋙ CategoryTheory.forget _ ⋙ opOp _ ⋙ yoneda.obj (op σ)) ≪≫
--         (isoWhiskerLeft ((Over.forget _).op ⋙ Scheme.Γ ⋙ forget₂ _ CommMonCat ⋙
--           CommMonCat.units ⋙ CategoryTheory.forget CommGrp) (Coyoneda.opIso.app _)))
--   convert X using 1
--   apply Comma.ext
--   · dsimp [SplitTorus, Diag]
--     congr 1

set_option backward.defeqAttrib.useBackward true in
variable (G S : Scheme.{u}) [G.Over S] [GrpObj (G.asOver S)] in
/-- Every split torus that's locally of finite type is isomorphic to `𝔾ₘⁿ` for some `n`. -/
lemma exists_iso_splitTorus_of_isSplitTorusOver [G.IsSplitTorusOver S] :
    ∃ (σ : Type u) (e : G ≅ SplitTorus S σ) (_ : e.hom.IsOver S),
      IsMonHom (e.hom.asOver S) := by
  obtain ⟨A, _, _, e, _, _⟩ := ‹G.IsSplitTorusOver S›
  exact ⟨Module.Free.ChooseBasisIndex ℤ A,
    e.trans <| Diag.mapIso S ((Module.Free.chooseBasis ℤ A).repr.toAddEquiv.trans
      (FreeAbelianGroup.equivFinsupp _).symm),
    by dsimp; infer_instance, by dsimp; infer_instance⟩

variable {R : CommRingCat} {σ : Type*}

variable (R σ) in
/-- The split torus with dimensions `σ` over `Spec R` is isomorphic to `Spec R[ℤ^σ]`. -/
abbrev splitTorusIso (R : CommRingCat) (σ : Type*) :
    𝔾ₘ[Spec R, σ] ≅ Spec(MvLaurentPolynomial σ R) := diagSpecIso _ _

end AlgebraicGeometry.Scheme
