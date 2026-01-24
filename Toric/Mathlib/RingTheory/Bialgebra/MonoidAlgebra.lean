import Mathlib.RingTheory.Bialgebra.GroupLike
import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
import Toric.Mathlib.RingTheory.Bialgebra.Convolution

noncomputable section

open TensorProduct Bialgebra Coalgebra Function

variable {R S A G H I M N : Type*}

namespace MonoidAlgebra
section CommSemiring
variable [CommSemiring R] [CommSemiring S]

section Semiring
variable [Semiring A] [Bialgebra R A]

section Monoid
variable [Monoid M] [Monoid N]

/-- A `R`-algebra homomorphism from `R[M]` is uniquely defined by its
values on the functions `single a 1`. -/
lemma bialgHom_ext ⦃φ₁ φ₂ : R[M] →ₐc[R] A⦄ (h : ∀ x, φ₁ (single x 1) = φ₂ (single x 1)) : φ₁ = φ₂ :=
  BialgHom.coe_algHom_injective <| algHom_ext h

-- The priority must be `high`.
/-- See note [partially-applied ext lemmas]. -/
@[ext high]
lemma bialgHom_ext' ⦃φ₁ φ₂ : R[M] →ₐc[R] A⦄
    (h : (φ₁ : R[M] →* A).comp (of R M) = .comp φ₂ (of R M)) : φ₁ = φ₂ :=
  bialgHom_ext fun x ↦ congr($h x)

@[simp] lemma counit_domCongr (e : M ≃* N) (x : MonoidAlgebra A M) :
    counit (R := R) (domCongr R A e x) = counit x := by
  induction x using MonoidAlgebra.induction_linear <;> simp [*]

variable (R A) in
/-- Isomorphic monoids have isomorphic monoid algebras. -/
@[simps!]
def domCongrBialgHom (e : M ≃* N) : MonoidAlgebra A M ≃ₐc[R] MonoidAlgebra A N :=
  .ofAlgEquiv (domCongr R A e) (by ext; simp) <| by
    apply AlgHom.toLinearMap_injective
    ext
    simp [TensorProduct.map_map, TensorProduct.AlgebraTensorModule.map_eq]

variable (M) in
/-- The trivial monoid algebra is isomorphic to the base ring. -/
noncomputable def bialgEquivOfSubsingleton [Subsingleton M] : R[M] ≃ₐc[R] R where
  __ := Bialgebra.counitBialgHom ..
  invFun := algebraMap _ _
  left_inv r := by
    change (Algebra.ofId _ _).comp (Bialgebra.counitAlgHom R _) r = AlgHom.id R _ r
    congr 1
    ext g : 2
    simp [Subsingleton.elim g 1]
  right_inv := (Bialgebra.counitAlgHom R (R[M])).commutes

end Monoid

section Group
variable [Group G]

lemma isGroupLikeElem_of (g : G) : IsGroupLikeElem R (of A G g) where
  counit_eq_one := by simp
  comul_eq_tmul_self := by simp [Algebra.TensorProduct.one_def]

@[simp]
lemma isGroupLikeElem_single_one (g : G) : IsGroupLikeElem R (single g 1 : MonoidAlgebra A G) :=
  isGroupLikeElem_of _

/-- A group algebra is spanned by its group-like elements. -/
@[simp]
lemma span_isGroupLikeElem : Submodule.span A {a : MonoidAlgebra A G | IsGroupLikeElem R a} = ⊤ :=
  eq_top_mono (Submodule.span_mono <| Set.range_subset_iff.2 isGroupLikeElem_of) <| by
    rw [← Finsupp.range_linearCombination]
    -- TODO: Mathlib doesn't have the identity map `R[M] ≃ (M →₀ R)`. Defeq abuse ensues.
    convert LinearMap.range_id
    ext
    simp

end Group
end Semiring

section CommSemiring
variable [CommSemiring A]

section Algebra
variable [Algebra R A] [Monoid M]

variable (R M A) in
/-- `MonoidAlgebra.lift` as a `MulEquiv`. -/
def liftMulEquiv : (M →* A) ≃* (R[M] →ₐ[R] A) where
  __ := lift R A M
  map_mul' f g := by ext; simp [AlgHom.convMul_apply]

@[simp]
lemma convMul_algHom_single (f g : R[M] →ₐ[R] A) (x : M) :
    (f * g) (single x 1) = f (single x 1) * g (single x 1) := by simp [AlgHom.convMul_apply]

end Algebra

variable [Bialgebra R A]

@[simp]
lemma convMul_bialgHom_single [CommMonoid M] (f g : R[M] →ₐc[R] A) (x : M) :
    (f * g) (single x 1) = f (single x 1) * g (single x 1) := by
  simp [← BialgHom.toCoalgHom_apply, ← CoalgHom.coe_toLinearMap, ← CoalgHom.toLinearMap_eq_coe,
    -LinearMap.coe_coe, BialgHom.toLinearMap_convMul]

end CommSemiring

section CommMonoid
variable [CommMonoid M] [CommMonoid N] (f : R →+* S)

@[simp]
lemma mapDomainBialgHom_mul (f g : M →* N) :
    mapDomainBialgHom R (f * g) = mapDomainBialgHom R f * mapDomainBialgHom R g := by
  ext x : 2; simp

lemma comulAlgHom_comp_mapRangeRingHom :
    (comulAlgHom S (MonoidAlgebra S M)).toRingHom.comp (mapRangeRingHom M f) =
      .comp (Algebra.TensorProduct.mapRingHom f (mapRangeRingHom M f) (mapRangeRingHom M f)
        (by ext; simp) (by ext; simp))
        (comulAlgHom R (R[M])).toRingHom := by ext <;> simp

lemma counitAlgHom_comp_mapRangeRingHom :
    (counitAlgHom S (MonoidAlgebra S M)).toRingHom.comp (mapRangeRingHom M f) =
      f.comp (counitAlgHom R (R[M])).toRingHom := by ext <;> simp

end CommMonoid
end CommSemiring

section CommRing
variable [CommRing R] [IsDomain R]

section Group
variable [Group G] [Group H]

open Submodule in
@[simp]
lemma isGroupLikeElem_iff_mem_range_of {x : MonoidAlgebra R G} :
    IsGroupLikeElem R x ↔ x ∈ Set.range (of R G) where
  mp hx := by
    by_contra h
    have : LinearIndepOn R id (insert x <| .range (of R G)) :=
      linearIndepOn_isGroupLikeElem.mono <| by simp [Set.subset_def, hx]
    have : x.sum single ∉ span R (.range (of R G)) := by simpa using this.notMem_span_of_insert h
    refine this <| sum_mem fun g hg ↦ ?_
    rw [← mul_one (x g), ← smul_eq_mul, ← smul_single]
    refine smul_mem _ _ <| subset_span <| Set.mem_range_self _
  mpr := by rintro ⟨g, rfl⟩; exact isGroupLikeElem_of _

private noncomputable def mapDomainOfBialgHomFun (f : MonoidAlgebra R G →ₐc[R] MonoidAlgebra R H) :
    G → H :=
  fun g ↦ (isGroupLikeElem_iff_mem_range_of.1 <| (isGroupLikeElem_of g).map f).choose

@[simp]
private lemma single_mapDomainOfBialgHomFun_one (f : MonoidAlgebra R G →ₐc[R] MonoidAlgebra R H)
    (g : G) : single (mapDomainOfBialgHomFun f g) 1 = f (single g 1) :=
  (isGroupLikeElem_iff_mem_range_of.1 <| (isGroupLikeElem_of g).map f).choose_spec

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
    mapDomainBialgHom R (mapDomainOfBialgHom f) = f :=
  BialgHom.coe_algHom_injective <| algHom_ext fun x ↦ by
    simpa [-single_mapDomainOfBialgHomFun_one] using single_mapDomainOfBialgHomFun_one f x

@[simp] lemma mapDomainOfBialgHom_mapDomainBialgHom (f : G →* H) :
    mapDomainOfBialgHom (mapDomainBialgHom (R := R) f) = f := by
  ext g; refine of_injective (R := R) ?_; simp [MonoidAlgebra.single_mapDomainOfBialgHom]

/-- The equivalence between group homs `G → H` and bialgebra homs `R[G] → R[H]` of group algebras
over a domain. -/
@[simps]
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
    (G →* H) ≃* (MonoidAlgebra R G →ₐc[R] MonoidAlgebra R H) where
  toEquiv := mapDomainBialgHomEquiv
  map_mul' f g := by simp

end CommGroup
end CommRing
end MonoidAlgebra


namespace AddMonoidAlgebra
section CommSemiring
variable [CommSemiring R] [CommSemiring S]

section Semiring
variable [Semiring A] [Bialgebra R A]


section AddMonoid
variable [AddMonoid M] [AddMonoid N]

/-- A `R`-algebra homomorphism from `R[M]` is uniquely defined by its values on the functions
`single a 1`. -/
lemma bialgHom_ext ⦃φ₁ φ₂ : R[M] →ₐc[R] A⦄ (h : ∀ x, φ₁ (single x 1) = φ₂ (single x 1)) : φ₁ = φ₂ :=
  BialgHom.coe_algHom_injective <| algHom_ext h

-- The priority must be `high`.
/-- See note [partially-applied ext lemmas]. -/
@[ext high]
lemma bialgHom_ext' ⦃φ₁ φ₂ : R[M] →ₐc[R] A⦄
    (h : (φ₁ : R[M] →* A).comp (of R M) = .comp φ₂ (of R M)) : φ₁ = φ₂ :=
  bialgHom_ext fun x ↦ congr($h x)

@[simp] lemma counit_domCongr (e : M ≃+ N) (x : A[M]) :
    counit (R := R) (domCongr R A e x) = counit x := by
  induction x using MonoidAlgebra.induction_linear <;> simp [*]

variable (R A) in
/-- Isomorphic monoids have isomorphic monoid algebras. -/
@[simps!]
def domCongrBialgHom (e : M ≃+ N) : A[M] ≃ₐc[R] A[N] :=
  .ofAlgEquiv (domCongr R A e) (by ext; simp) <| by
    apply AlgHom.toLinearMap_injective
    ext
    simp [TensorProduct.map_map, TensorProduct.AlgebraTensorModule.map_eq]

variable (M) in
/-- The trivial monoid algebra is isomorphic to the base ring. -/
noncomputable def bialgEquivOfSubsingleton [Subsingleton M] : R[M] ≃ₐc[R] R where
  __ := Bialgebra.counitBialgHom ..
  invFun := algebraMap _ _
  left_inv r := by
    change (Algebra.ofId _ _).comp (Bialgebra.counitAlgHom R _) r = AlgHom.id R _ r
    congr 1
    ext g : 3
    simp [Subsingleton.elim g 0]
  right_inv := (Bialgebra.counitAlgHom R R[M]).commutes

end AddMonoid

section AddGroup
variable [AddGroup G]

lemma isGroupLikeElem_of (g : G) : IsGroupLikeElem R (of A G g) :=
  MonoidAlgebra.isGroupLikeElem_of (R := R) (A := A) (Multiplicative.ofAdd g)

@[simp]
lemma isGroupLikeElem_single (g : G) : IsGroupLikeElem R (single g 1 : A[G]) := isGroupLikeElem_of _

/-- A group algebra is spanned by its group-like elements. -/
@[simp]
lemma span_isGroupLikeElem : Submodule.span A {a : A[G] | IsGroupLikeElem R a} = ⊤ :=
  eq_top_mono (Submodule.span_mono <| Set.range_subset_iff.2 isGroupLikeElem_of) <| by
    rw [← Finsupp.range_linearCombination]
    -- TODO: Mathlib doesn't have the identity map `R[M] ≃ (M →₀ R)`. Defeq abuse ensues.
    convert LinearMap.range_id
    ext
    simp
    rfl

end AddGroup
end Semiring

section CommSemiring
variable [CommSemiring A]

@[simp]
lemma convMul_algHom_single [Algebra R A] [AddMonoid M] (f g : R[M] →ₐ[R] A) (x : M) :
    (f * g) (single x 1) = f (single x 1) * g (single x 1) := by
  simp [-AlgHom.coe_toLinearMap, ← AlgHom.toLinearMap_apply, AlgHom.toLinearMap_convMul]

@[simp]
lemma convMul_bialgHom_single [Bialgebra R A] [AddCommMonoid M] (f g : R[M] →ₐc[R] A) (x : M) :
    (f * g) (single x 1) = f (single x 1) * g (single x 1) := by
  simp [← BialgHom.toCoalgHom_apply, ← CoalgHom.coe_toLinearMap, ← CoalgHom.toLinearMap_eq_coe,
    -LinearMap.coe_coe, BialgHom.toLinearMap_convMul]

end CommSemiring

section AddCommMonoid
variable [AddCommMonoid M] [AddCommMonoid N] (f : R →+* S)

@[simp]
lemma mapDomainBialgHom_add (f g : M →+ N) :
    mapDomainBialgHom R (f + g) = mapDomainBialgHom R f * mapDomainBialgHom R g :=
  MonoidAlgebra.mapDomainBialgHom_mul f.toMultiplicative g.toMultiplicative

lemma comulAlgHom_comp_mapRangeRingHom :
    (comulAlgHom S S[M]).toRingHom.comp (mapRangeRingHom M f) =
      .comp (Algebra.TensorProduct.mapRingHom f (mapRangeRingHom M f) (mapRangeRingHom M f)
        (by ext; simp) (by ext; simp))
        (comulAlgHom R R[M]).toRingHom := by ext <;> simp

lemma counitAlgHom_comp_mapRangeRingHom :
    (counitAlgHom S S[M]).toRingHom.comp (mapRangeRingHom M f) =
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
    IsGroupLikeElem R x ↔ x ∈ Set.range (of R G) :=
  MonoidAlgebra.isGroupLikeElem_iff_mem_range_of (G := Multiplicative G)

private noncomputable def mapDomainOfBialgHomFun (f : R[G] →ₐc[R] R[H]) : G → H :=
  fun g ↦ (isGroupLikeElem_iff_mem_range_of.1 <| (isGroupLikeElem_of g).map f).choose

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

protected lemma single_mapDomainOfBialgHom (f : R[G] →ₐc[R] R[H]) (g : G) (r : R) :
    single (mapDomainOfBialgHom f g) r = f (single g r) := by
  rw [← mul_one r, ← smul_eq_mul, ← smul_single, ← smul_single, map_smul]
  exact congr(r • $(single_mapDomainOfBialgHomFun_one f g))

@[simp]
lemma mapDomainBialgHom_mapDomainOfBialgHom (f : R[G] →ₐc[R] R[H]) :
    mapDomainBialgHom R (mapDomainOfBialgHom f) = f :=
  BialgHom.coe_algHom_injective <| algHom_ext fun x ↦ by
    simpa [-single_mapDomainOfBialgHomFun_one] using single_mapDomainOfBialgHomFun_one f x

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
@[simps]
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
noncomputable def mapDomainBialgHomAddEquiv : (G →+ H) ≃+ Additive (R[G] →ₐc[R] R[H]) where
  toEquiv := mapDomainBialgHomEquiv.trans Additive.ofMul
  map_add' f g := by simp

end AddCommGroup
end CommRing
end AddMonoidAlgebra

namespace MonoidAlgebra
variable (R A) [CommSemiring R] [Semiring A] [Bialgebra R A]

/-- The `R`-algebra map from the group algebra on the group-like elements of `A` to `A`. -/
@[simps!]
noncomputable def liftGroupLikeAlgHom : MonoidAlgebra R (GroupLike R A) →ₐ[R] A :=
  lift R A (GroupLike R A) { toFun g := g.1, map_one' := by simp, map_mul' := by simp }

/-- The `R`-bialgebra map from the group algebra on the group-like elements of `A` to `A`. -/
@[simps!]
noncomputable def liftGroupLikeBialgHom : MonoidAlgebra R (GroupLike R A) →ₐc[R] A :=
  .ofAlgHom (liftGroupLikeAlgHom R A) (by aesop) (by aesop)

end MonoidAlgebra
