module

public import Mathlib.RingTheory.Bialgebra.Convolution
public import Mathlib.RingTheory.Bialgebra.GroupLike
public import Mathlib.RingTheory.Bialgebra.MonoidAlgebra

public noncomputable section

open TensorProduct Bialgebra Coalgebra Function WithConv

variable {R S A B G H I M N : Type*}

namespace MonoidAlgebra
section CommSemiring
variable [CommSemiring R] [CommSemiring S]

section Semiring
variable [Semiring A] [Semiring B] [Bialgebra R A] [Bialgebra R B]

@[to_additive (dont_translate := R A) (attr := simp) isGroupLikeElem_single_one]
lemma isGroupLikeElem_single_one (g : G) : IsGroupLikeElem R (single g 1 : A[G]) where
  counit_eq_one := by simp
  comul_eq_tmul_self := by simp [Algebra.TensorProduct.one_def]

/-- A group algebra is spanned by its group-like elements. -/
@[to_additive (dont_translate := R A) (attr := simp) span_isGroupLikeElem]
lemma span_isGroupLikeElem : Submodule.span A {a : A[G] | IsGroupLikeElem R a} = ⊤ :=
  eq_top_mono (Submodule.span_mono <| Set.range_subset_iff.2 isGroupLikeElem_single_one) <| by
    rw [← Finsupp.range_linearCombination]
    exact LinearMap.range_eq_top_of_surjective _ fun x ↦
      ⟨x.coeff, by simp [Finsupp.linearCombination_apply]⟩

variable [Monoid M] [Monoid N]

@[to_additive (attr := simp)]
lemma mapDomainBialgHom_single (f : M →* N) (m : M) (r : R) :
    mapDomainBialgHom R f (single m r) = single (f m) r := mapDomain_single

/-- A `R`-algebra homomorphism from `R[M]` is uniquely defined by its
values on the functions `single a 1`. -/
@[to_additive (dont_translate := A)
/-- A `R`-algebra homomorphism from `R[M]` is uniquely defined by its
values on the functions `single a 0`. -/]
lemma bialgHom_ext ⦃φ₁ φ₂ : A[M] →ₐc[R] B⦄
  (single_one_right : ∀ (m : M), φ₁ (single m 1) = φ₂ (single m 1))
  (single_one_left : (φ₁ : A[M] →ₐ[R] B).comp singleOneAlgHom =
    (φ₂ : A[M] →ₐ[R] B).comp singleOneAlgHom) : φ₁ = φ₂ :=
  BialgHom.coe_toAlgHom_injective <| algHom_ext single_one_right single_one_left

-- The priority must be `high`.
/-- See note [partially-applied ext lemmas]. -/
@[ext high]
lemma bialgHom_ext' ⦃φ₁ φ₂ : A[M] →ₐc[R] B⦄
    (single_one_right : (φ₁ : A[M] →* B).comp (of A M) = (φ₂ : A[M] →* B).comp (of A M))
    (single_one_left : (φ₁ : A[M] →ₐ[R] B).comp singleOneAlgHom =
      (φ₂ : A[M] →ₐ[R] B).comp singleOneAlgHom) : φ₁ = φ₂ :=
  BialgHom.coe_toAlgHom_injective <| algHom_ext' single_one_right single_one_left

@[to_additive (attr := simp)]
lemma counit_domCongr (e : M ≃* N) (x : MonoidAlgebra A M) :
    counit (R := R) (domCongr R A e x) = counit x := by
  induction x using MonoidAlgebra.induction_linear <;> simp [*]

variable (R A) in
/-- Isomorphic monoids have isomorphic monoid algebras. -/
@[expose, to_additive (attr := simps!) (dont_translate := R A)]
def domCongrBialgHom (e : M ≃* N) : A[M] ≃ₐc[R] A[N] :=
  .ofAlgEquiv (domCongr R A e) (by ext <;> simp) <| by
    ext a
    · simp
    · simp [← (Coalgebra.Repr.arbitrary R a).eq]

variable (M) in
/-- The trivial monoid algebra is isomorphic to the base ring. -/
@[expose]
noncomputable def bialgEquivOfSubsingleton [Subsingleton M] : R[M] ≃ₐc[R] R where
  __ := Bialgebra.counitBialgHom ..
  invFun := algebraMap _ _
  left_inv r := by
    change (Algebra.ofId _ _).comp (Bialgebra.counitAlgHom R _) r = AlgHom.id R _ r
    congr 1
    ext g : 2
    simp [Subsingleton.elim g 1]
  right_inv := (Bialgebra.counitAlgHom R (R[M])).commutes

lemma isGroupLikeElem_of (m : M) : IsGroupLikeElem R (of A M m) := isGroupLikeElem_single_one ..

end Semiring

section CommSemiring
variable [CommSemiring A]

section Algebra
variable [Algebra R A] [Monoid M]

variable (R M A) in
/-- `MonoidAlgebra.lift` as a `MulEquiv`. -/
def liftMulEquiv : (M →* A) ≃* WithConv (R[M] →ₐ[R] A) where
  toEquiv := (lift R A M).trans (WithConv.equiv _).symm
  map_mul' f g := by ext; simp [AlgHom.convMul_apply]

@[to_additive (dont_translate := R A) (attr := simp) convMul_algHom_single_one]
lemma convMul_algHom_single_one (f g : WithConv <| R[M] →ₐ[R] A) (x : M) :
    (f * g) (single x 1) = f (single x 1) * g (single x 1) := by simp [AlgHom.convMul_apply]

end Algebra

variable [Bialgebra R A]

@[to_additive (dont_translate := R A) (attr := simp) convMul_bialgHom_single_one]
lemma convMul_bialgHom_single [CommMonoid M] (f g : WithConv <| R[M] →ₐc[R] A) (x : M) :
    (f * g) (single x 1) = f (single x 1) * g (single x 1) := by
  simp only [BialgHom.convMul_def, BialgHom.coe_comp, Function.comp_apply]
  change mulBialgHom R A (Bialgebra.TensorProduct.map f.ofConv g.ofConv (comul (single x 1))) = _
  simp [Bialgebra.TensorProduct.map_tmul]

end CommSemiring

section CommMonoid
variable [CommMonoid M] [CommMonoid N]

@[simp]
lemma mapDomainBialgHom_mul (f g : M →* N) :
    mapDomainBialgHom R (f * g) =
      ofConv ((toConv <| mapDomainBialgHom R f) * (toConv <| mapDomainBialgHom R g)) := by ext; simp

lemma comulAlgHom_comp_mapRingHom (f : R →+* S) :
    (comulAlgHom S (MonoidAlgebra S M)).toRingHom.comp (mapRingHom M f) =
      .comp (Algebra.TensorProduct.mapRingHom f (mapRingHom M f) (mapRingHom M f)
        (by ext; simp) (by ext; simp))
        (comulAlgHom R (R[M])).toRingHom := by ext <;> simp

lemma counitAlgHom_comp_mapRingHom (f : R →+* S) :
    (counitAlgHom S (MonoidAlgebra S M)).toRingHom.comp (mapRingHom M f) =
      f.comp (counitAlgHom R (R[M])).toRingHom := by ext <;> simp

end CommMonoid
end CommSemiring

section CommRing
variable [CommRing R] [IsDomain R]

open Submodule in
@[to_additive (dont_translate := R) (attr := simp) isGroupLikeElem_iff_mem_range_single_one]
lemma isGroupLikeElem_iff_mem_range_single_one {x : R[M]} :
    IsGroupLikeElem R x ↔ x ∈ Set.range (single · 1) where
  mp hx := by
    by_contra h
    have : LinearIndepOn R id (insert x <| .range (single · 1)) :=
      linearIndepOn_isGroupLikeElem.mono <| by simp [Set.subset_def, hx]
    have : x.coeff.sum single ∉ span R (.range (single · 1)) := by
      simpa using this.notMem_span_of_insert h
    refine this <| sum_mem fun g hg ↦ ?_
    rw [← mul_one (x.coeff g), ← smul_eq_mul, ← smul_single]
    exact smul_mem _ _ <| subset_span <| Set.mem_range_self _
  mpr := by rintro ⟨g, rfl⟩; exact isGroupLikeElem_single_one _

open Submodule in
@[to_additive (dont_translate := R) (attr := simp)]
lemma isGroupLikeElem_iff_mem_range_of {x : R[M]} :
    IsGroupLikeElem R x ↔ x ∈ Set.range (single · 1) := isGroupLikeElem_iff_mem_range_single_one

section Group
variable [Group G] [Group H]

@[to_additive (dont_translate := R)]
private noncomputable def mapDomainOfBialgHomFun (f : MonoidAlgebra R G →ₐc[R] MonoidAlgebra R H) :
    G → H :=
  fun g ↦ (isGroupLikeElem_iff_mem_range_of.1 <| (isGroupLikeElem_single_one g).map f).choose

@[to_additive (dont_translate := R) (attr := simp)]
private lemma single_mapDomainOfBialgHomFun_one (f : MonoidAlgebra R G →ₐc[R] MonoidAlgebra R H)
    (g : G) : single (mapDomainOfBialgHomFun f g) 1 = f (single g 1) :=
  (isGroupLikeElem_iff_mem_range_of.1 <| (isGroupLikeElem_single_one g).map f).choose_spec

open Coalgebra in
/-- A bialgebra homomorphism `R[G] → R[H]` between group algebras over a domain `R` comes from a
group hom `G → H`.

See `MonoidAlgebra.mapDomainBialgHom` for the forward map. -/
noncomputable def mapDomainOfBialgHom (f : MonoidAlgebra R G →ₐc[R] MonoidAlgebra R H) :
    G →* H where
  toFun := mapDomainOfBialgHomFun f
  map_one' := of_injective (R := R) <| by simp [← one_def]
  map_mul' g₁ g₂ := by
    refine of_injective (R := R) ?_
    simp only [of_apply, single_mapDomainOfBialgHomFun_one]
    rw [← mul_one (1 : R), ← single_mul_single, ← single_mul_single, map_mul]
    simp

protected lemma single_mapDomainOfBialgHom (f : MonoidAlgebra R G →ₐc[R] MonoidAlgebra R H)
    (g : G) (r : R) : single (mapDomainOfBialgHom f g) r = f (single g r) := by
  rw [← mul_one r, ← smul_eq_mul, ← smul_single, ← smul_single, map_smul]
  exact congr(r • $(single_mapDomainOfBialgHomFun_one f g))

@[simp]
lemma mapDomainBialgHom_mapDomainOfBialgHom (f : MonoidAlgebra R G →ₐc[R] MonoidAlgebra R H) :
    mapDomainBialgHom R (mapDomainOfBialgHom f) = f := by
  refine BialgHom.coe_toAlgHom_injective <| algHom_ext (fun x ↦ ?_) (Subsingleton.elim _ _)
  simp only [BialgHom.coe_toAlgHom, mapDomainBialgHom_single]
  exact single_mapDomainOfBialgHomFun_one f x

@[simp] lemma mapDomainOfBialgHom_mapDomainBialgHom (f : G →* H) :
    mapDomainOfBialgHom (mapDomainBialgHom (R := R) f) = f := by
  ext g; refine of_injective (R := R) ?_; simp [MonoidAlgebra.single_mapDomainOfBialgHom]

/-- The equivalence between group homs `G → H` and bialgebra homs `R[G] → R[H]` of group algebras
over a domain. -/
@[expose, simps]
noncomputable def mapDomainBialgHomEquiv :
    (G →* H) ≃ (MonoidAlgebra R G →ₐc[R] MonoidAlgebra R H) where
  toFun := mapDomainBialgHom R
  invFun := mapDomainOfBialgHom
  left_inv := mapDomainOfBialgHom_mapDomainBialgHom
  right_inv := mapDomainBialgHom_mapDomainOfBialgHom

end Group

section CommGroup
variable [CommGroup G] [CommGroup H]

/-- The group isomorphism between group homs `G → H` and bialgebra homs `R[G] → R[H]` of group
algebras over a domain. -/
noncomputable def mapDomainBialgHomMulEquiv :
    (G →* H) ≃* WithConv (MonoidAlgebra R G →ₐc[R] MonoidAlgebra R H) where
  toEquiv := mapDomainBialgHomEquiv.trans (WithConv.equiv _).symm
  map_mul' f g := by simp

end CommGroup
end CommRing
end MonoidAlgebra


namespace AddMonoidAlgebra
section CommSemiring
variable [CommSemiring R] [CommSemiring S]

section Semiring
variable [Semiring A] [Semiring B] [Bialgebra R A] [Bialgebra R B] [AddMonoid M] [AddMonoid N]

-- The priority must be `high`.
/-- See note [partially-applied ext lemmas]. -/
@[ext high]
lemma bialgHom_ext' ⦃φ₁ φ₂ : A[M] →ₐc[R] B⦄
    (single_one_right : (φ₁ : A[M] →* B).comp (of A M) = (φ₂ : A[M] →* B).comp (of A M))
    (single_one_left : (φ₁ : A[M] →ₐ[R] B).comp singleZeroAlgHom =
      (φ₂ : A[M] →ₐ[R] B).comp singleZeroAlgHom) : φ₁ = φ₂ :=
  BialgHom.coe_toAlgHom_injective <| algHom_ext' single_one_right single_one_left

variable (M) in
/-- The trivial monoid algebra is isomorphic to the base ring. -/
@[expose]
noncomputable def bialgEquivOfSubsingleton [Subsingleton M] : R[M] ≃ₐc[R] R where
  __ := Bialgebra.counitBialgHom ..
  invFun := algebraMap _ _
  left_inv r := by
    change (Algebra.ofId _ _).comp (Bialgebra.counitAlgHom R _) r = AlgHom.id R _ r
    congr 1
    ext g : 3
    simp [Subsingleton.elim g 0]
  right_inv := (Bialgebra.counitAlgHom R R[M]).commutes

lemma isGroupLikeElem_of (m : M) : IsGroupLikeElem R (of A M m) := isGroupLikeElem_single_one ..

end Semiring

section CommSemiring
variable [CommSemiring A]

section Algebra
variable [Algebra R A] [AddMonoid M]

variable (R M A) in
/-- `AddMonoidAlgebra.lift` as a `MulEquiv`. -/
def liftMulEquiv : (Multiplicative M →* A) ≃* WithConv (R[M] →ₐ[R] A) where
  toEquiv := (lift R A M).trans (WithConv.equiv _).symm
  map_mul' f g := by ext; simp [AlgHom.convMul_apply]

end Algebra

@[simp]
lemma convMul_bialgHom_single [Bialgebra R A] [AddCommMonoid M] (f g : WithConv <| R[M] →ₐc[R] A)
    (m : M) : (f * g) (single m 1) = f (single m 1) * g (single m 1) := by
  simp only [BialgHom.convMul_def, BialgHom.coe_comp, Function.comp_apply]
  change mulBialgHom R A (Bialgebra.TensorProduct.map f.ofConv g.ofConv (comul (single m 1))) = _
  simp [Bialgebra.TensorProduct.map_tmul]

end CommSemiring

section AddCommMonoid
variable [AddCommMonoid M] [AddCommMonoid N]

@[simp]
lemma mapDomainBialgHom_add (f g : M →+ N) :
    mapDomainBialgHom R (f + g) =
     (toConv (mapDomainBialgHom R f) * toConv (mapDomainBialgHom R g)).ofConv := by ext; simp

lemma comulAlgHom_comp_mapRingHom (f : R →+* S) :
    (comulAlgHom S S[M]).toRingHom.comp (mapRingHom M f) =
      .comp (Algebra.TensorProduct.mapRingHom f (mapRingHom M f) (mapRingHom M f)
        (by ext; simp) (by ext; simp))
        (comulAlgHom R R[M]).toRingHom := by ext <;> simp

lemma counitAlgHom_comp_mapRingHom (f : R →+* S) :
    (counitAlgHom S S[M]).toRingHom.comp (mapRingHom M f) =
      f.comp (counitAlgHom R R[M]).toRingHom := by ext <;> simp

end AddCommMonoid
end CommSemiring

section CommRing
variable [CommRing R] [IsDomain R]

section AddGroup
variable [AddGroup G] [AddGroup H] [AddGroup I]

open Submodule in
@[simp]
lemma isGroupLikeElem_iff_mem_range_of {x : R[G]} :
    IsGroupLikeElem R x ↔ x ∈ Set.range (of R G) := isGroupLikeElem_iff_mem_range_single_one

@[simp]
private lemma single_mapDomainOfBialgHomFun_one (f : R[G] →ₐc[R] R[H]) (g : G) :
    single (mapDomainOfBialgHomFun f g) 1 = f (single g 1) :=
  (isGroupLikeElem_iff_mem_range_of.1 <| (isGroupLikeElem_of g).map f).choose_spec

open Coalgebra in
/-- A bialgebra homomorphism `R[G] → R[H]` between group algebras over a domain `R` comes from a
group hom `G → H`.

See `AddMonoidAlgebra.mapDomainBialgHom` for the forward map. -/
noncomputable def mapDomainOfBialgHom (f : R[G] →ₐc[R] R[H]) : G →+ H where
  toFun := mapDomainOfBialgHomFun f
  map_zero' := Multiplicative.ofAdd.injective <| of_injective (R := R) <| by simp [← one_def]
  map_add' g₁ g₂ := by
    refine Multiplicative.ofAdd.injective <| of_injective (R := R) ?_
    simp only [of_apply, single_mapDomainOfBialgHomFun_one, toAdd_ofAdd, ofAdd_add, toAdd_mul,
      single_mapDomainOfBialgHomFun_one]
    rw [← mul_one (1 : R), ← single_mul_single, ← single_mul_single, map_mul]
    simp

@[simp]
protected lemma single_mapDomainOfBialgHom (f : R[G] →ₐc[R] R[H]) (g : G) (r : R) :
    single (mapDomainOfBialgHom f g) r = f (single g r) := by
  rw [← mul_one r, ← smul_eq_mul, ← smul_single, ← smul_single, map_smul]
  exact congr(r • $(single_mapDomainOfBialgHomFun_one f g))

@[simp]
lemma mapDomainBialgHom_mapDomainOfBialgHom (f : R[G] →ₐc[R] R[H]) :
    mapDomainBialgHom R (mapDomainOfBialgHom f) = f := by ext; simp

@[simp] lemma mapDomainOfBialgHom_mapDomainBialgHom (f : G →+ H) :
    mapDomainOfBialgHom (mapDomainBialgHom R f) = f := by
  ext g
  refine Multiplicative.ofAdd.injective <| of_injective (R := R) ?_
  simp [AddMonoidAlgebra.single_mapDomainOfBialgHom]

@[simp] lemma mapDomainOfBialgHom_id : mapDomainOfBialgHom (.id R R[G]) = .id _ := by
  simp [← mapDomainBialgHom_id]

@[simp] lemma mapDomainOfBialgHom_comp (f : R[H] →ₐc[R] R[I]) (g : R[G] →ₐc[R] R[H]) :
    mapDomainOfBialgHom (f.comp g) = (mapDomainOfBialgHom f).comp (mapDomainOfBialgHom g) := by
  rw [← mapDomainOfBialgHom_mapDomainBialgHom (R := R)
    ((mapDomainOfBialgHom f).comp (mapDomainOfBialgHom g)),
    mapDomainBialgHom_comp, mapDomainBialgHom_mapDomainOfBialgHom,
    mapDomainBialgHom_mapDomainOfBialgHom]

/-- The equivalence between group homs `G → H` and bialgebra homs `R[G] → R[H]` of group algebras
over a domain. -/
@[expose, simps]
noncomputable def mapDomainBialgHomEquiv : (G →+ H) ≃ (R[G] →ₐc[R] R[H]) where
  toFun := mapDomainBialgHom R
  invFun := mapDomainOfBialgHom
  left_inv := mapDomainOfBialgHom_mapDomainBialgHom
  right_inv := mapDomainBialgHom_mapDomainOfBialgHom

end AddGroup

section AddCommGroup
variable [AddCommGroup G] [AddCommGroup H]

/-- The group isomorphism between group homs `G → H` and bialgebra homs `R[G] → R[H]` of group
algebras over a domain. -/
noncomputable def mapDomainBialgHomAddEquiv :
    (G →+ H) ≃+ Additive (WithConv <| R[G] →ₐc[R] R[H]) where
  toEquiv := mapDomainBialgHomEquiv.trans <| (WithConv.equiv _).symm.trans Additive.ofMul
  map_add' f g := by simp

end AddCommGroup
end CommRing
end AddMonoidAlgebra

namespace MonoidAlgebra
variable (R A) [CommSemiring R] [Semiring A] [Bialgebra R A]

/-- The `R`-algebra map from the group algebra on the group-like elements of `A` to `A`. -/
@[expose, simps!]
noncomputable def liftGroupLikeAlgHom : R[GroupLike R A] →ₐ[R] A :=
  lift R A (GroupLike R A) { toFun g := g.1, map_one' := by simp, map_mul' := by simp }

/-- The `R`-bialgebra map from the group algebra on the group-like elements of `A` to `A`. -/
@[expose, simps!]
noncomputable def liftGroupLikeBialgHom : R[GroupLike R A] →ₐc[R] A :=
  .ofAlgHom (liftGroupLikeAlgHom R A) (by aesop) (by aesop)

end MonoidAlgebra
