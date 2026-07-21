/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.RingTheory.TensorProduct.MonoidAlgebra
public import Toric.Hopf.GrpAlg
public import Toric.Mathlib.Algebra.Category.Ring.Under.Basic
public import Toric.Mathlib.RingTheory.Bialgebra.MonoidAlgebra

@[expose] public noncomputable section

open CategoryTheory Limits Opposite MonoidalCategory MonoidAlgebra MonObj

attribute [local instance] Functor.Monoidal.ofChosenFiniteProducts
attribute [local instance] MonoidAlgebra.algebraMonoidAlgebra
attribute [local instance] MonoidAlgebra.isScalarTower_monoidAlgebra

namespace AlgebraicGeometry.Scheme
universe v u
variable {R S : CommRingCat.{u}} (M : CommMonCat.{u}) (f : R ⟶ S) (Sf : Spec S ⟶ Spec R)
  (H : Sf = Spec.map f)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
abbrev specCommMonAlgPullbackObjXIso :
    (((commMonAlg R).op ⋙ bialgSpec R ⋙ (Over.pullback Sf).mapMon).obj (.op M)).X ≅
      (((commMonAlg S).op ⋙ bialgSpec S).obj (.op M)).X :=
  letI := f.hom.toAlgebra
  haveI H : IsPullback (Spec.map (CommRingCat.ofHom (algebraMap R[M] S[M])))
    (Spec.map (CommRingCat.ofHom (algebraMap S S[M])))
    (Spec.map (CommRingCat.ofHom (algebraMap R R[M])))
    Sf := H ▸ (CommRingCat.isPushout_of_isPushout R S R[M] S[M]).op.map Scheme.Spec
  Over.isoMk H.isoPullback.symm (by dsimp; simp)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option linter.flexible false in
lemma specCommMonAlgPullbackObjXIso_one :
    η ≫ (specCommMonAlgPullbackObjXIso M f Sf H).hom = η := by
  subst H
  let := f.hom.toAlgebra
  ext
  apply ((CommRingCat.isPushout_of_isPushout R S R[M] S[M]).op.map Scheme.Spec).hom_ext <;>
  · simp [Functor.Monoidal.ε_of_cartesianMonoidalCategory, RingHom.algebraMap_toAlgebra,
      CommRingCat.mkUnder, CommRingCat.of_carrier, -AlgHom.toUnder_right']
    simp [← Spec.map_id, ← Spec.map_comp]
    congr 1
    ext <;> simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option linter.flexible false in
-- The `simp` calls are non-terminal merely because the `erw` calls are necessary: the `@[simp]`
-- lemmas `Over.tensorHom_left_fst/snd` want their target to be syntactically an `Over.mk`, which
-- `(algSpec R).obj _` isn't syntactically.
@[reassoc]
private
lemma specCommMonAlgPullbackObjIso_mul_aux :
    (CartesianMonoidalCategory.prodComparisonIso (Over.pullback Sf) _ _).inv.left ≫
      pullback.fst _ _ ≫ (pullbackSpecIso R R[M] R[M]).hom =
    ((specCommMonAlgPullbackObjXIso M f Sf H).hom ⊗ₘ
      (specCommMonAlgPullbackObjXIso M f Sf H).hom).left ≫
      (pullbackSpecIso S _ _).hom ≫
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.mapRingHom f.hom _ _
          (mapRingHom_comp_algebraMap f.hom (M := M))
          (mapRingHom_comp_algebraMap f.hom (M := M)))) := by
  subst H
  let := f.hom.toAlgebra
  have H := (CommRingCat.isPushout_of_isPushout R S R[M] S[M]).op.map Scheme.Spec
  let e : (((commMonAlg R).op ⋙ bialgSpec R ⋙ (Over.pullback (Spec.map f)).mapMon).obj (.op M)).X ≅
    (((commMonAlg S).op ⋙ bialgSpec S).obj (.op M)).X :=
      Over.isoMk H.isoPullback.symm (by dsimp; simp; rfl)
  have hc := mapRingHom_comp_algebraMap f.hom (M := M)
  have h₂ := Algebra.TensorProduct.mapRingHom_comp_includeLeftRingHom _ _ _ hc hc
  have h₃ := Algebra.TensorProduct.mapRingHom_comp_includeRight _ _ _ hc hc
  apply_fun (Spec.map <| CommRingCat.ofHom ·) at h₂ h₃
  simp only [CommRingCat.ofHom_comp, Spec.map_comp] at h₂ h₃
  rw [← Category.assoc, ← Iso.eq_comp_inv]
  dsimp
  ext
  · simp [h₂]
    erw [Over.tensorHom_left_fst_assoc]
    simp [specCommMonAlgPullbackObjXIso, RingHom.algebraMap_toAlgebra]
    exact Over.prodComparisonIso_pullback_inv_left_fst_fst (Spec.map f) _ _
  · simp [h₃]
    erw [Over.tensorHom_left_snd_assoc]
    simp [specCommMonAlgPullbackObjXIso, RingHom.algebraMap_toAlgebra]
    exact Over.prodComparisonIso_pullback_inv_left_fst_snd' (Spec.map f) _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option linter.flexible false in
lemma specCommMonAlgPullbackObjXIso_mul :
    μ ≫ (specCommMonAlgPullbackObjXIso M f Sf H).hom =
    ((specCommMonAlgPullbackObjXIso M f Sf H).hom ⊗ₘ
      (specCommMonAlgPullbackObjXIso M f Sf H).hom) ≫ μ := by
  dsimp [AlgHom.toUnder]
  -- FIXME: `erw?` says nothing
  subst H
  let := f.hom.toAlgebra
  have h₃ := comulAlgHom_comp_mapRingHom f.hom (M := M)
  have h₄ := (Bialgebra.comulAlgHom S S[M]).comp_algebraMap
  apply_fun (Spec.map <| CommRingCat.ofHom ·) at h₃ h₄
  simp only [AlgHom.toRingHom_eq_coe, CommRingCat.ofHom_comp, Spec.map_comp] at h₃ h₄
  ext
  apply ((CommRingCat.isPushout_of_isPushout R S R[M] S[M]).op.map Scheme.Spec).hom_ext
  · simpa [Functor.Monoidal.μ_of_cartesianMonoidalCategory, RingHom.algebraMap_toAlgebra,
      AlgHom.toUnder, h₃, specCommMonAlgPullbackObjXIso] using
        specCommMonAlgPullbackObjIso_mul_aux_assoc M f _ rfl
          (Spec.map (CommRingCat.ofHom (Bialgebra.comulAlgHom R R[M]).toRingHom))
  · simp [Functor.Monoidal.μ_of_cartesianMonoidalCategory, RingHom.algebraMap_toAlgebra,
      AlgHom.toUnder, h₄, Algebra.TensorProduct.algebraMap_def, pullback.condition]
    erw [Over.tensorHom_left_snd_assoc]
    simp [specCommMonAlgPullbackObjXIso, RingHom.algebraMap_toAlgebra]
    exact Over.prodComparisonIso_pullback_inv_left_snd' (Spec.map f) ..

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
-- should we make something like `BialgHom.toRingHom`?
/-- The spectrum of a commutative algebra functor commutes with base change. -/
def specCommMonAlgPullback :
    (commMonAlg R).op ⋙ bialgSpec R ⋙ (Over.pullback Sf).mapMon ≅
      (commMonAlg S).op ⋙ bialgSpec S :=
  NatIso.ofComponents (fun M ↦ Mon.mkIso (specCommMonAlgPullbackObjXIso M.unop f Sf H)
    (specCommMonAlgPullbackObjXIso_one M.unop f Sf H)
    (specCommMonAlgPullbackObjXIso_mul M.unop f Sf H))
  fun {M N} φ ↦ by
    subst H
    let := f.hom.toAlgebra
    have H := (CommRingCat.isPushout_of_isPushout R S R[N.unop] S[N.unop]).op.map Scheme.Spec
    have h₁ : (mapRingHom M.unop f.hom).comp (mapDomainBialgHom R φ.unop.hom).toAlgHom =
        (mapDomainBialgHom S φ.unop.hom).toAlgHom.toRingHom.comp
          (mapRingHom N.unop f.hom) := mapRingHom_comp_mapDomainRingHom _ _
    have h₂ := (mapDomainBialgHom S φ.unop.hom).toAlgHom.comp_algebraMap
    apply_fun (Spec.map <| CommRingCat.ofHom ·) at h₁ h₂
    simp only [CommRingCat.ofHom_comp, Spec.map_comp] at h₁ h₂
    ext
    apply ((CommRingCat.isPushout_of_isPushout R S R[N.unop] S[N.unop]).op.map Scheme.Spec).hom_ext
    · simp [RingHom.algebraMap_toAlgebra, AlgHom.toUnder, Iso.eq_inv_comp, h₁]
    · simp [RingHom.algebraMap_toAlgebra, AlgHom.toUnder, ← h₂]

-- TODO: Make `CommRingCat.mkUnder` abbrev or add dsimp lemmas etc.
@[reassoc (attr := simp)]
lemma specCommMonAlgPullback_inv_app_hom_left_fst (M) :
    ((specCommMonAlgPullback f Sf H).inv.app M).hom.left ≫
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R R[↥(unop M)]))) _ =
        Spec.map (CommRingCat.ofHom (mapRingHom M.unop f.hom)) :=
  let := f.hom.toAlgebra
  have H' := (CommRingCat.isPushout_of_isPushout R S R[M.unop] S[M.unop]).op.map Scheme.Spec
  H ▸ H'.isoPullback_hom_fst

@[reassoc (attr := simp)]
lemma specCommMonAlgPullback_inv_app_hom_left_snd (M) :
    ((specCommMonAlgPullback f Sf H).inv.app M).hom.left ≫
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R R[↥(unop M)]))) _ =
        Spec.map (CommRingCat.ofHom (algebraMap _ _)) :=
  let := f.hom.toAlgebra
  have H' := (CommRingCat.isPushout_of_isPushout R S R[M.unop] S[M.unop]).op.map Scheme.Spec
  H ▸ H'.isoPullback_hom_snd

/-- The spectrum of a group algebra functor commutes with base change. -/
def specCommGrpAlgPullback :
    (commGrpAlg R).op ⋙ hopfSpec R ⋙ (Over.pullback Sf).mapGrp ≅
      (commGrpAlg S).op ⋙ hopfSpec S :=
  ((Grp.fullyFaithfulForget₂Mon _).whiskeringRight _).preimageIso <|
    (forget₂ CommGrpCat CommMonCat).op.isoWhiskerLeft (specCommMonAlgPullback f _ H)

end AlgebraicGeometry.Scheme
