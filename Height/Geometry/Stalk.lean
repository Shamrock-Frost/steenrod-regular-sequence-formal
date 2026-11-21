import Height.Geometry.Interface
import Height.Toolbox.LocalRing
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Properties

/-!
# The points and stalks of the closed subscheme `V(I)`

`Vsch I` is affine and locally Noetherian, and its underlying space is `Spec (K[ι] ⧸ I)`:
both embed onto the zero locus of `I` in `Spec K[ι]`, `Vsch I` through `Vι I` and `specHomeo`,
`Spec (K[ι] ⧸ I)` through the quotient map (`VschHomeo`).  Everything the tangent statements
of `Geometry/Spec.lean` need about a stalk is then read off the corresponding prime:
`ringKrullDim` of the stalk is the height of that prime
(`AlgebraicGeometry.ringKrullDim_stalk_eq_coheight` and `idealHeight_eq_coheight`), and at a
closed point the height is the dimension of `K[ι] ⧸ I`
(`Toolbox/AffineAlgebra.height_eq_ringKrullDim_of_isMaximal`).

The same homeomorphism carries the topology of `Spec (K[ι] ⧸ I)` over: `V(I)` is a Noetherian
space, and for `I` prime an irreducible one.  Over an algebraically closed field its closed
points are exactly its `K`-points (`isClosed_singleton_of_pt`, `exists_pt_of_isClosed`).
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Order Height.Toolbox

namespace Height.Geometry

universe u

variable {K : Type u} [Field K] {ι : Type u} [Finite ι]

instance : IsAffine 𝔸(ι; Spec (.of K)) := IsAffine.of_isIso (specIso K ι).hom

instance (I : Ideal (MvPolynomial ι K)) : IsAffine (Vsch I) := isAffine_of_isAffineHom (Vι I)

instance : IsLocallyNoetherian 𝔸(ι; Spec (.of K)) :=
  isLocallyNoetherian_of_isOpenImmersion (specIso K ι).hom

instance (I : Ideal (MvPolynomial ι K)) : IsLocallyNoetherian (Vsch I) :=
  LocallyOfFiniteType.isLocallyNoetherian (Vι I)

omit [Finite ι] in
private theorem isEmbedding_specHomeo_comp_Vι (I : Ideal (MvPolynomial ι K)) :
    IsEmbedding ((specHomeo K ι) ∘ (Vι I)) :=
  (specHomeo K ι).isEmbedding.comp (Vι I).isEmbedding

omit [Finite ι] in
private theorem range_specHomeo_comp_Vι (I : Ideal (MvPolynomial ι K)) :
    Set.range ((specHomeo K ι) ∘ (Vι I)) =
      PrimeSpectrum.zeroLocus (I : Set (MvPolynomial ι K)) := by
  rw [Set.range_comp, range_Vι, V_eq_specHomeo_preimage,
    Set.image_preimage_eq _ (specHomeo K ι).surjective]

omit [Finite ι] in
private theorem range_comap_mk (I : Ideal (MvPolynomial ι K)) :
    Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) =
      PrimeSpectrum.zeroLocus (I : Set (MvPolynomial ι K)) := by
  rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]

/-- `V(I)` sits in `Spec K[ι]` as the zero locus of `I`. -/
private noncomputable def zeroLocusHomeoVsch (I : Ideal (MvPolynomial ι K)) :
    Vsch I ≃ₜ (PrimeSpectrum.zeroLocus (I : Set (MvPolynomial ι K))) :=
  (isEmbedding_specHomeo_comp_Vι I).toHomeomorph.trans
    (Homeomorph.setCongr (range_specHomeo_comp_Vι I))

/-- `Spec (K[ι] ⧸ I)` sits in `Spec K[ι]` as the zero locus of `I`. -/
private noncomputable def zeroLocusHomeoSpec (I : Ideal (MvPolynomial ι K)) :
    PrimeSpectrum (MvPolynomial ι K ⧸ I) ≃ₜ
      (PrimeSpectrum.zeroLocus (I : Set (MvPolynomial ι K))) :=
  (PrimeSpectrum.isClosedEmbedding_comap_of_surjective _ _
    Ideal.Quotient.mk_surjective).isEmbedding.toHomeomorph.trans
      (Homeomorph.setCongr (range_comap_mk I))

/-- **The underlying space of `V(I)` is `Spec (K[ι] ⧸ I)`**: both are the zero locus of `I`
inside `Spec K[ι]` (`range_Vι` and `PrimeSpectrum.range_comap_of_surjective`). -/
noncomputable def VschHomeo (I : Ideal (MvPolynomial ι K)) :
    Vsch I ≃ₜ PrimeSpectrum (MvPolynomial ι K ⧸ I) :=
  (zeroLocusHomeoVsch I).trans (zeroLocusHomeoSpec I).symm

omit [Finite ι] in
/-- **`VschHomeo` is the inverse of the quotient map on the zero locus**: the prime of `p` in
`K[ι] ⧸ I` contracts to the prime of `Vι I p` in `K[ι]`. -/
theorem comap_mk_VschHomeo (I : Ideal (MvPolynomial ι K)) (p : Vsch I) :
    PrimeSpectrum.comap (Ideal.Quotient.mk I) (VschHomeo I p) = specHomeo K ι (Vι I p) :=
  congrArg Subtype.val ((zeroLocusHomeoSpec I).apply_symm_apply (zeroLocusHomeoVsch I p))

omit [Finite ι] in
/-- The dimension of `V(I)` is the Krull dimension of `K[ι] ⧸ I`. -/
theorem topologicalKrullDim_Vsch (I : Ideal (MvPolynomial ι K)) :
    topologicalKrullDim (Vsch I) = ringKrullDim (MvPolynomial ι K ⧸ I) := by
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact (VschHomeo I).isHomeomorph.topologicalKrullDim_eq

omit [Finite ι] in
/-- The stalk of `V(I)` at `p` has the dimension of the height of the corresponding prime. -/
theorem ringKrullDim_stalk_Vsch (I : Ideal (MvPolynomial ι K)) (p : Vsch I) :
    ringKrullDim ((Vsch I).presheaf.stalk p) =
      (((VschHomeo I p).asIdeal.height : ℕ∞) : WithBot ℕ∞) := by
  rw [ringKrullDim_stalk_eq_coheight,
    ← Topology.IsOpenEmbedding.coheight_eq (VschHomeo I) (VschHomeo I).isOpenEmbedding]
  exact congrArg _
    (idealHeight_eq_coheight (CommRingCat.of (MvPolynomial ι K ⧸ I)) (VschHomeo I p)).symm

omit [Finite ι] in
/-- A closed point of `V(I)` corresponds to a maximal ideal. -/
theorem isMaximal_of_isClosed {I : Ideal (MvPolynomial ι K)} {p : Vsch I}
    (hp : IsClosed ({p} : Set (Vsch I))) : (VschHomeo I p).asIdeal.IsMaximal := by
  rw [← PrimeSpectrum.isClosed_singleton_iff_isMaximal, ← Set.image_singleton]
  exact ((VschHomeo I).isClosed_image).mpr hp

omit [Finite ι] in
/-- A `K`-point of `V(I)` is a closed point. -/
theorem isClosed_singleton_of_pt {I : Ideal (MvPolynomial ι K)} {x : ι → K}
    {p : Vsch I} (hp : Vι I p = (ptEquiv K x : 𝔸(ι; Spec (.of K)))) :
    IsClosed ({p} : Set (Vsch I)) := by
  have hcl : IsClosed ({(ptEquiv K x : 𝔸(ι; Spec (.of K)))} : Set 𝔸(ι; Spec (.of K))) := by
    rw [← (specHomeo K ι).isClosed_image, Set.image_singleton, specHomeo_pt,
      PrimeSpectrum.isClosed_singleton_iff_isMaximal]
    -- `pointToPoint x` is `⟨vanishingIdeal K {x}, _⟩`, so this is mathlib's instance
    exact inferInstanceAs (MvPolynomial.vanishingIdeal K ({x} : Set (ι → K))).IsMaximal
  have hset : ({p} : Set (Vsch I)) = (Vι I) ⁻¹' {(ptEquiv K x : 𝔸(ι; Spec (.of K)))} := by
    ext q
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    exact ⟨fun h => h ▸ hp, fun h => (Vι I).isEmbedding.injective (h.trans hp.symm)⟩
  rw [hset]
  exact hcl.preimage (Vι I).continuous

/-! ### `V(I)` as `Spec (K[ι] ⧸ I)`, and its stalks as localisations -/

/-- The closed immersion `Spec (K[ι] ⧸ I) ⟶ 𝔸(ι; Spec K)` cut out by `I`. -/
noncomputable def quotSpec (I : Ideal (MvPolynomial ι K)) :
    Spec (.of (MvPolynomial ι K ⧸ I)) ⟶ 𝔸(ι; Spec (.of K)) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ (specIso K ι).inv

instance (I : Ideal (MvPolynomial ι K)) : IsClosedImmersion (quotSpec I) :=
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  IsClosedImmersion.comp _ _

omit [Finite ι] in
/-- `quotSpec I` pulls the regular function of `g` back to the class of `g`. -/
theorem quotSpec_appTop_regularEquiv (I : Ideal (MvPolynomial ι K)) (g : MvPolynomial ι K) :
    (quotSpec I).appTop (regularEquiv g) =
      (Scheme.ΓSpecIso (.of (MvPolynomial ι K ⧸ I))).inv (Ideal.Quotient.mk I g) := by
  have hspec : ((specIso K ι).inv).appTop (regularEquiv g) =
      (Scheme.ΓSpecIso (.of (MvPolynomial ι K))).inv g := by
    have h : ((specIso K ι).inv ≫ (specIso K ι).hom).appTop = 𝟙 _ := by simp
    rw [Scheme.Hom.comp_appTop] at h
    show ((specIso K ι).inv).appTop
      (((specIso K ι).hom).appTop ((Scheme.ΓSpecIso (.of (MvPolynomial ι K))).inv g)) = _
    rw [← CommRingCat.comp_apply, h]
    rfl
  show ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ (specIso K ι).inv)).appTop
    (regularEquiv g) = _
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hspec, ← CommRingCat.comp_apply,
    ← Scheme.ΓSpecIso_inv_naturality]
  rfl

omit [Finite ι] in
/-- The kernel ideal sheaf of `quotSpec I` is the ideal sheaf of `I`. -/
theorem ker_quotSpec (I : Ideal (MvPolynomial ι K)) : (quotSpec I).ker = idealSheaf I := by
  rw [Scheme.ker_of_isAffine, idealSheaf]
  congr 1
  ext h
  obtain ⟨g, rfl⟩ := (regularEquiv (K := K) (ι := ι)).surjective h
  rw [RingHom.mem_ker, quotSpec_appTop_regularEquiv]
  constructor
  · intro h0
    have hg : Ideal.Quotient.mk I g = 0 := by
      have h1 := congrArg (Scheme.ΓSpecIso (.of (MvPolynomial ι K ⧸ I))).hom h0
      rwa [Iso.inv_hom_id_apply, map_zero] at h1
    exact Ideal.mem_map_of_mem _ (Ideal.Quotient.eq_zero_iff_mem.mp hg)
  · intro hmem
    obtain ⟨y, hy, hey⟩ :=
      (Ideal.mem_map_iff_of_surjective _ (regularEquiv (K := K) (ι := ι)).surjective).mp hmem
    have hyg : y = g := (regularEquiv (K := K) (ι := ι)).injective hey
    subst hyg
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hy, map_zero]

omit [Finite ι] in
private theorem exists_iso_subscheme {X : Scheme.{u}} (f : X ⟶ 𝔸(ι; Spec (.of K)))
    [IsClosedImmersion f] {J : (𝔸(ι; Spec (.of K))).IdealSheafData} (h : f.ker = J) :
    ∃ e : X ≅ J.subscheme, e.hom ≫ J.subschemeι = f := by
  subst h
  exact ⟨asIso f.toImage, f.toImage_imageι⟩

/-- **`V(I)` is `Spec (K[ι] ⧸ I)`** as a scheme. -/
noncomputable def VschSpecIso (I : Ideal (MvPolynomial ι K)) :
    Spec (.of (MvPolynomial ι K ⧸ I)) ≅ Vsch I :=
  (exists_iso_subscheme (quotSpec I) (ker_quotSpec I)).choose

omit [Finite ι] in
theorem VschSpecIso_hom_Vι (I : Ideal (MvPolynomial ι K)) :
    (VschSpecIso I).hom ≫ Vι I = quotSpec I :=
  (exists_iso_subscheme (quotSpec I) (ker_quotSpec I)).choose_spec

/-- **The stalk of `V(I)` at a point is the localisation of `K[ι] ⧸ I` at the corresponding
prime** (the scheme isomorphism `VschSpecIso` on stalks, then
`StructureSheaf.IsLocalization.to_stalk`). -/
noncomputable def stalkVschRingEquiv (I : Ideal (MvPolynomial ι K))
    (q : ↥(Spec (.of (MvPolynomial ι K ⧸ I)))) [q.asIdeal.IsPrime] :
    (Vsch I).presheaf.stalk ((VschSpecIso I).hom q) ≃+* Localization.AtPrime q.asIdeal :=

  letI : Algebra (MvPolynomial ι K ⧸ I)
      ((Spec (.of (MvPolynomial ι K ⧸ I))).presheaf.stalk q) := StructureSheaf.stalkAlgebra _ q
  haveI : IsLocalization.AtPrime
      ((Spec (.of (MvPolynomial ι K ⧸ I))).presheaf.stalk q) q.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk _ q
  ((asIso ((VschSpecIso I).hom.stalkMap q)).commRingCatIsoToRingEquiv).trans
    (IsLocalization.algEquiv q.asIdeal.primeCompl (Localization.AtPrime q.asIdeal)
      ((Spec (.of (MvPolynomial ι K ⧸ I))).presheaf.stalk q)).toRingEquiv.symm

/-- The cotangent space of a stalk of `V(I)` has the dimension of `q ⧸ q²` for the
corresponding prime (`Toolbox/AffineAlgebra.finrank_cotangentSpace_localization_atPrime`
transported by `Toolbox/LocalRing.finrank_cotangentSpace_of_ringEquiv`). -/
theorem finrank_cotangentSpace_stalk_Vsch (I : Ideal (MvPolynomial ι K))
    (q : ↥(Spec (.of (MvPolynomial ι K ⧸ I)))) (hq : q.asIdeal.IsMaximal) :
    Module.finrank
        (IsLocalRing.ResidueField ((Vsch I).presheaf.stalk ((VschSpecIso I).hom q)))
        (IsLocalRing.CotangentSpace ((Vsch I).presheaf.stalk ((VschSpecIso I).hom q))) =
      Module.finrank ((MvPolynomial ι K ⧸ I) ⧸ q.asIdeal) q.asIdeal.Cotangent := by
  have _ := hq
  have _ : q.asIdeal.IsPrime := q.isPrime
  exact (finrank_cotangentSpace_of_ringEquiv (stalkVschRingEquiv I q)).trans
    (finrank_cotangentSpace_localization_atPrime q.asIdeal)

omit [Finite ι] in
/-- The quotient map on points is the contraction along `K[ι] → K[ι] ⧸ I`. -/
theorem specHomeo_quotSpec (I : Ideal (MvPolynomial ι K))
    (q : ↥(Spec (.of (MvPolynomial ι K ⧸ I)))) :
    specHomeo K ι ((quotSpec I) q) = PrimeSpectrum.comap (Ideal.Quotient.mk I) q := by
  show ((specIso K ι).hom).base
    (((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ (specIso K ι).inv)).base q) = _
  rw [Scheme.Hom.comp_base]
  show ((specIso K ι).inv ≫ (specIso K ι).hom).base
    ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).base q) = _
  rw [Iso.inv_hom_id]
  rfl

omit [Finite ι] in
/-- **The two presentations of the points of `V(I)` agree**: the homeomorphism `VschHomeo`
inverts the isomorphism `VschSpecIso`.  Both classify a point by a prime of `K[ι] ⧸ I`, and
the contractions of those primes to `K[ι]` agree (`comap_mk_VschHomeo`, `specHomeo_quotSpec`),
so the primes do (`PrimeSpectrum.comap` along a surjection is injective). -/
theorem VschHomeo_VschSpecIso_hom (I : Ideal (MvPolynomial ι K))
    (q : ↥(Spec (.of (MvPolynomial ι K ⧸ I)))) :
    VschHomeo I ((VschSpecIso I).hom q) = q := by
  refine PrimeSpectrum.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective ?_
  rw [comap_mk_VschHomeo, ← specHomeo_quotSpec I q, ← VschSpecIso_hom_Vι I, Scheme.Hom.comp_base]
  rfl

omit [Finite ι] in
/-- **The prime of a `K`-point.**  If the point of `V(I)` classified by `q` is the `K`-point
of `x`, then `q` is the ideal of `x` in `K[ι] ⧸ I`. -/
theorem asIdeal_eq_of_pt {I : Ideal (MvPolynomial ι K)} {x : ι → K}
    {q : ↥(Spec (.of (MvPolynomial ι K ⧸ I)))}
    (hq : Vι I ((VschSpecIso I).hom q) = (ptEquiv K x : 𝔸(ι; Spec (.of K)))) :
    q.asIdeal =
      (MvPolynomial.vanishingIdeal K ({x} : Set (ι → K))).map (Ideal.Quotient.mk I) := by
  have h1 : (quotSpec I) q = (ptEquiv K x : 𝔸(ι; Spec (.of K))) := by
    rw [← VschSpecIso_hom_Vι I, Scheme.Hom.comp_base]
    exact hq
  have h2 : specHomeo K ι ((quotSpec I) q) =
      PrimeSpectrum.comap (Ideal.Quotient.mk I) q := specHomeo_quotSpec I q
  have h3 : PrimeSpectrum.comap (Ideal.Quotient.mk I) q =
      MvPolynomial.pointToPoint (k := K) x := by
    rw [← h2, h1, specHomeo_pt]
  have h4 : Ideal.comap (Ideal.Quotient.mk I) q.asIdeal =
      MvPolynomial.vanishingIdeal K ({x} : Set (ι → K)) := congrArg PrimeSpectrum.asIdeal h3
  rw [← h4, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]

omit [Finite ι] in
/-- Every point of `V(I)` is classified by a prime of `K[ι] ⧸ I`. -/
theorem exists_point_VschSpecIso (I : Ideal (MvPolynomial ι K)) (p : Vsch I) :
    ∃ q : ↥(Spec (.of (MvPolynomial ι K ⧸ I))), (VschSpecIso I).hom q = p :=
  ⟨((VschSpecIso I).inv).base p, by
    show ((VschSpecIso I).inv ≫ (VschSpecIso I).hom).base p = p
    rw [Iso.inv_hom_id]
    rfl⟩

/-- **Over an algebraically closed field a closed point of `V(I)` is a `K`-point.**  `Vι I`
is a closed immersion, so the image of a closed point is a closed point of the affine space,
and there it is a `K`-point by the Nullstellensatz (`range_pt`). -/
theorem exists_pt_of_isClosed [IsAlgClosed K] {I : Ideal (MvPolynomial ι K)} {p : Vsch I}
    (hp : IsClosed ({p} : Set (Vsch I))) :
    ∃ x : ι → K, Vι I p = (ptEquiv K x : 𝔸(ι; Spec (.of K))) := by
  have hemb : IsClosedEmbedding (Vι I).base := IsClosedImmersion.isClosedEmbedding (Vι I)
  have hcl : IsClosed ({Vι I p} : Set 𝔸(ι; Spec (.of K))) := by
    rw [← Set.image_singleton]
    exact hemb.isClosedMap _ hp
  obtain ⟨x, hx⟩ : Vι I p ∈ Set.range fun x : ι → K => (ptEquiv K x : 𝔸(ι; Spec (.of K))) := by
    rw [range_pt]
    exact hcl
  exact ⟨x, hx.symm⟩

/-- For `I` prime `V(I)` is irreducible: `K[ι] ⧸ I` is a domain, so `Spec (K[ι] ⧸ I)` is
irreducible (`PrimeSpectrum.irreducibleSpace`). -/
instance irreducibleSpace_Vsch (I : Ideal (MvPolynomial ι K)) [I.IsPrime] :
    IrreducibleSpace (Vsch I) := by
  have _ : IsDomain (MvPolynomial ι K ⧸ I) := (Ideal.Quotient.isDomain_iff_prime I).mpr ‹_›
  refine (irreducibleSpace_def _).mpr ?_
  have h : IsIrreducible (Set.univ : Set (PrimeSpectrum (MvPolynomial ι K ⧸ I))) :=
    (irreducibleSpace_def _).mp inferInstance
  have h2 := h.image (VschHomeo I).symm (VschHomeo I).symm.continuous.continuousOn
  rwa [Set.image_univ, (VschHomeo I).symm.surjective.range_eq] at h2

end Height.Geometry
