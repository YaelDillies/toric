/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.TensorProduct.MonoidAlgebra
public import Toric.GroupScheme.HopfAffine
public import Toric.Hopf.GrpAlg
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

abbrev specCommMonAlgPullbackObjXIso :
    (((commMonAlg R).op ⋙ bialgSpec R ⋙ (Over.pullback Sf).mapMon).obj (.op M)).X ≅
      (((commMonAlg S).op ⋙ bialgSpec S).obj (.op M)).X :=
  letI := f.hom.toAlgebra
  letI H : IsPullback (Spec.map (CommRingCat.ofHom (algebraMap R[M] S[M])))
    (Spec.map (CommRingCat.ofHom (algebraMap S S[M])))
    (Spec.map (CommRingCat.ofHom (algebraMap R R[M])))
    Sf := H ▸ (CommRingCat.isPushout_of_isPushout R S R[M] S[M]).op.map Scheme.Spec
  Over.isoMk H.isoPullback.symm (by dsimp; simp)

lemma specCommMonAlgPullbackObjXIso_one :
    η ≫ (specCommMonAlgPullbackObjXIso M f Sf H).hom = η := by
  subst H
  dsimp [AlgHom.toUnder]
  letI := f.hom.toAlgebra
  have h₁ := counitAlgHom_comp_mapRangeRingHom f.hom (M := M)
  have h₂ := (Bialgebra.counitAlgHom S S[M]).comp_algebraMap
  apply_fun (Spec.map <| CommRingCat.ofHom ·) at h₁ h₂
  simp only [CommRingCat.ofHom_comp, Spec.map_comp, AlgHom.toRingHom_eq_coe] at h₁ h₂
  ext
  apply ((CommRingCat.isPushout_of_isPushout R S R[M] S[M]).op.map Scheme.Spec).hom_ext <;>
    simp [Functor.Monoidal.ε_of_cartesianMonoidalCategory, RingHom.algebraMap_toAlgebra, h₁, h₂,
      CommRingCat.mkUnder]

@[reassoc]
private
lemma specCommMonAlgPullbackObjIso_mul_aux :
    (CartesianMonoidalCategory.prodComparisonIso (Over.pullback Sf) _ _).inv.left ≫
      pullback.fst _ _ ≫ (pullbackSpecIso R R[M] R[M]).hom =
    ((specCommMonAlgPullbackObjXIso M f Sf H).hom ⊗ₘ
      (specCommMonAlgPullbackObjXIso M f Sf H).hom).left ≫
      (pullbackSpecIso S _ _).hom ≫
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.mapRingHom f.hom _ _
          (mapRangeRingHom_comp_algebraMap f.hom (M := M))
          (mapRangeRingHom_comp_algebraMap f.hom (M := M)))) := by
  subst H
  letI := f.hom.toAlgebra
  letI H := (CommRingCat.isPushout_of_isPushout R S R[M] S[M]).op.map Scheme.Spec
  letI e : (((commMonAlg R).op ⋙ bialgSpec R ⋙ (Over.pullback (Spec.map f)).mapMon).obj (.op M)).X ≅
    (((commMonAlg S).op ⋙ bialgSpec S).obj (.op M)).X :=
      Over.isoMk H.isoPullback.symm (by dsimp; simp; rfl)
  letI hc := mapRangeRingHom_comp_algebraMap f.hom (M := M)
  have h₂ := Algebra.TensorProduct.mapRingHom_comp_includeLeftRingHom _ _ _ hc hc
  have h₃ := Algebra.TensorProduct.mapRingHom_comp_includeRight _ _ _ hc hc
  apply_fun (Spec.map <| CommRingCat.ofHom ·) at h₂ h₃
  simp only [CommRingCat.ofHom_comp, Spec.map_comp] at h₂ h₃
  rw [← Category.assoc, ← Iso.eq_comp_inv]
  dsimp
  ext <;> simp [h₂, h₃, RingHom.algebraMap_toAlgebra]

lemma specCommMonAlgPullbackObjXIso_mul :
    μ ≫ (specCommMonAlgPullbackObjXIso M f Sf H).hom =
    ((specCommMonAlgPullbackObjXIso M f Sf H).hom ⊗ₘ
      (specCommMonAlgPullbackObjXIso M f Sf H).hom) ≫ μ := by
  dsimp [AlgHom.toUnder]
  -- FIXME: `erw?` says nothing
  erw [Functor.mapMon_obj_mon_mul, Functor.mapMon_obj_mon_mul]
  subst H
  letI := f.hom.toAlgebra
  have h₃ := comulAlgHom_comp_mapRangeRingHom f.hom (M := M)
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
    letI := f.hom.toAlgebra
    letI H := (CommRingCat.isPushout_of_isPushout R S R[N.unop] S[N.unop]).op.map Scheme.Spec
    have h₁ : (mapRangeRingHom M.unop f.hom).comp (mapDomainBialgHom R φ.unop.hom) =
        (RingHomClass.toRingHom (mapDomainBialgHom S φ.unop.hom)).comp
          (mapRangeRingHom N.unop f.hom) := mapRangeRingHom_comp_mapDomainRingHom _ _
    have h₂ := (AlgHomClass.toAlgHom (mapDomainBialgHom S φ.unop.hom)).comp_algebraMap
    apply_fun (Spec.map <| CommRingCat.ofHom ·) at h₁ h₂
    simp only [CommRingCat.ofHom_comp, Spec.map_comp] at h₁ h₂
    ext
    apply ((CommRingCat.isPushout_of_isPushout R S R[N.unop] S[N.unop]).op.map Scheme.Spec).hom_ext
    · simp [RingHom.algebraMap_toAlgebra,AlgHom.toUnder, Iso.eq_inv_comp, h₁]
    · simp [RingHom.algebraMap_toAlgebra, AlgHom.toUnder, ← h₂]

-- TODO: Make `CommRingCat.mkUnder` abbrev or add dsimp lemmas etc.
@[reassoc (attr := simp)]
lemma specCommMonAlgPullback_inv_app_hom_left_fst (M) :
    ((specCommMonAlgPullback f Sf H).inv.app M).hom.left ≫
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R R[↥(unop M)]))) _ =
        Spec.map (CommRingCat.ofHom (mapRangeRingHom M.unop f.hom)) :=
  letI := f.hom.toAlgebra
  let H' := (CommRingCat.isPushout_of_isPushout R S R[M.unop] S[M.unop]).op.map Scheme.Spec
  H ▸ H'.isoPullback_hom_fst

@[reassoc (attr := simp)]
lemma specCommMonAlgPullback_inv_app_hom_left_snd (M) :
    ((specCommMonAlgPullback f Sf H).inv.app M).hom.left ≫
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R R[↥(unop M)]))) _ =
        Spec.map (CommRingCat.ofHom (algebraMap _ _)) :=
  letI := f.hom.toAlgebra
  let H' := (CommRingCat.isPushout_of_isPushout R S R[M.unop] S[M.unop]).op.map Scheme.Spec
  H ▸ H'.isoPullback_hom_snd

/-- The spectrum of a group algebra functor commutes with base change. -/
def specCommGrpAlgPullback :
    (commGrpAlg R).op ⋙ hopfSpec R ⋙ (Over.pullback Sf).mapGrp ≅
      (commGrpAlg S).op ⋙ hopfSpec S :=
  ((Grp.fullyFaithfulForget₂Mon _).whiskeringRight _).preimageIso <|
    (forget₂ CommGrpCat CommMonCat).op.isoWhiskerLeft (specCommMonAlgPullback f _ H)

end AlgebraicGeometry.Scheme
