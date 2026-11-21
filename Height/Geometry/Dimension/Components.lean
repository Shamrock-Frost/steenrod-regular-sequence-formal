import Height.Geometry.Dimension.Irreducible
import Height.Geometry.Dimension.Trdeg
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian

/-!
# Decomposition into irreducible components

For an arbitrary subset `Y ⊆ (ι → K)` of affine
space over an algebraically closed field, the zero loci of the minimal primes of
`vanishingIdeal K Y` are finitely many irreducible closed sets covering the
Zariski closure of `Y`, maximal among the irreducible closed subsets of that
closure, and `affineDim Y` is the largest of their dimensions.

**Exact statement** (`Height.Geometry.components`), for
`[IsAlgClosed K] [Finite ι]` and `Y : Set (ι → K)`:

```
∃ (m : ℕ) (C : Fin m → Set (ι → K)),
  (∀ i, (MvPolynomial.vanishingIdeal K (C i)).IsPrime) ∧
  (∀ i, zclosure (C i) = C i) ∧
  (∀ i, C i ⊆ zclosure Y) ∧
  zclosure Y = ⋃ i, C i ∧
  (∀ i, ∀ Z : Set (ι → K), (MvPolynomial.vanishingIdeal K Z).IsPrime →
      C i ⊆ Z → Z ⊆ zclosure Y → Z ⊆ C i) ∧
  affineDim Y = ⨆ i, affineDim (C i)
```

The maximality clause (the fifth) is part of the package because the stability
of the components under a group action (`locClosed_components` in
`Dimension/LocClosed.lean`) uses it: the closure of the sweep of a component is
irreducible and contains the component, so it lies in it by maximality.

Also here, because it is the other half of the fibre inequalities: the image of
an affine set under a polynomial map does not gain dimension
(`Height.Geometry.affineDim_image_le`), through `ringKrullDim_eq_trdeg`
and the transcendence-degree tower law.
-/

universe u v

open MvPolynomial

namespace Height.Geometry

variable {K : Type u} [Field K] {ι κ : Type v}

/-! ### Finite intersections of ideals and finite unions of zero loci -/

/-- The zero locus of a finite intersection of ideals is the union of the zero
loci: if `x` avoids every `zeroLocus (P j)` then a product of witnesses lies in
the intersection and is nonzero at `x`. -/
theorem zeroLocus_iInf {J : Type*} [Finite J] (P : J → Ideal (MvPolynomial ι K)) :
    MvPolynomial.zeroLocus K (⨅ j, P j) = ⋃ j, MvPolynomial.zeroLocus K (P j) := by
  classical
  cases nonempty_fintype J
  refine le_antisymm (fun x hx => ?_) ?_
  · by_contra hcon
    rw [Set.mem_iUnion] at hcon
    push Not at hcon
    have hwit : ∀ j, ∃ p ∈ P j, aeval x p ≠ 0 := by
      intro j
      by_contra h
      push Not at h
      exact hcon j fun p hp => h p hp
    choose p hp hpx using hwit
    have hmem : (∏ j, p j) ∈ ⨅ j, P j := by
      refine Submodule.mem_iInf _ |>.2 fun k => ?_
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem p (Finset.mem_univ k)
      rw [hc, mul_comm]
      exact Ideal.mul_mem_left _ _ (hp k)
    have := hx _ hmem
    rw [map_prod] at this
    exact absurd this (Finset.prod_ne_zero_iff.2 fun j _ => hpx j)
  · refine Set.iUnion_subset fun j => MvPolynomial.zeroLocus_anti_mono ?_
    exact iInf_le P j

/-! ### The components -/

/-- **Components.**  Decomposition of the closure of an affine set into finitely many
irreducible components: they are closed, irreducible, contained in the closure,
they cover it, each is maximal among the irreducible subsets of the closure that
contain it, and the dimension of `Y` is the largest of their dimensions. -/
theorem components [IsAlgClosed K] [Finite ι] (Y : Set (ι → K)) :
    ∃ (m : ℕ) (C : Fin m → Set (ι → K)),
      (∀ i, (MvPolynomial.vanishingIdeal K (C i)).IsPrime) ∧
      (∀ i, zclosure (C i) = C i) ∧
      (∀ i, C i ⊆ zclosure Y) ∧
      zclosure Y = ⋃ i, C i ∧
      (∀ i, ∀ Z : Set (ι → K), (MvPolynomial.vanishingIdeal K Z).IsPrime →
        C i ⊆ Z → Z ⊆ zclosure Y → Z ⊆ C i) ∧
      affineDim Y = ⨆ i, affineDim (C i) := by
  classical
  -- Enumerate the minimal primes of the vanishing ideal.
  obtain ⟨m, P, hPmem, hPsurj⟩ :
      ∃ (m : ℕ) (P : Fin m → Ideal (MvPolynomial ι K)),
        (∀ i, P i ∈ (MvPolynomial.vanishingIdeal K Y).minimalPrimes) ∧
        (∀ p ∈ (MvPolynomial.vanishingIdeal K Y).minimalPrimes, ∃ i, P i = p) := by
    have hfin : (MvPolynomial.vanishingIdeal K Y).minimalPrimes.Finite :=
      Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial ι K) _
    have _ : Fintype (MvPolynomial.vanishingIdeal K Y).minimalPrimes := hfin.fintype
    refine ⟨Fintype.card _,
      fun i => (((Fintype.equivFin _).symm i : (MvPolynomial.vanishingIdeal K Y).minimalPrimes) :
        Ideal (MvPolynomial ι K)),
      fun i => ((Fintype.equivFin _).symm i).2, fun p hp => ⟨Fintype.equivFin _ ⟨p, hp⟩, ?_⟩⟩
    simp
  have hprime : ∀ i, (P i).IsPrime := fun i => (hPmem i).isPrime
  have hvan : ∀ i, MvPolynomial.vanishingIdeal K (MvPolynomial.zeroLocus K (P i)) = P i := by
    intro i
    have _ : (P i).IsPrime := hprime i
    exact MvPolynomial.IsPrime.vanishingIdeal_zeroLocus _
  -- The intersection of the minimal primes is the (radical) vanishing ideal.
  have hinf : (⨅ i, P i) = MvPolynomial.vanishingIdeal K Y := by
    have hrad : (MvPolynomial.vanishingIdeal K Y).radical = MvPolynomial.vanishingIdeal K Y := by
      have h := MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := K)
        (MvPolynomial.vanishingIdeal K Y)
      rw [← h]
      exact vanishingIdeal_zclosure Y
    rw [← hrad, ← Ideal.sInf_minimalPrimes]
    refine le_antisymm (le_sInf fun p hp => ?_) (le_iInf fun i => sInf_le (hPmem i))
    obtain ⟨i, rfl⟩ := hPsurj p hp
    exact iInf_le P i
  have hcover : zclosure Y = ⋃ i, MvPolynomial.zeroLocus K (P i) := by
    show MvPolynomial.zeroLocus K (MvPolynomial.vanishingIdeal K Y) = _
    rw [← hinf, zeroLocus_iInf]
  refine ⟨m, fun i => MvPolynomial.zeroLocus K (P i), fun i => ?_, fun i => ?_, fun i => ?_,
    hcover, fun i Z hZp hCZ hZY => ?_, ?_⟩
  · rw [hvan i]; exact hprime i
  · exact zclosure_zeroLocus _
  · rw [hcover]
    exact Set.subset_iUnion (fun i => MvPolynomial.zeroLocus K (P i)) i
  · have h1 : MvPolynomial.vanishingIdeal K Y ≤ MvPolynomial.vanishingIdeal K Z := by
      have := MvPolynomial.vanishingIdeal_anti_mono (k := K) hZY
      rwa [vanishingIdeal_zclosure] at this
    have h2 : MvPolynomial.vanishingIdeal K Z ≤ P i := by
      have := MvPolynomial.vanishingIdeal_anti_mono (k := K) hCZ
      rwa [hvan i] at this
    have h3 : P i ≤ MvPolynomial.vanishingIdeal K Z := (hPmem i).2 ⟨hZp, h1⟩ h2
    have h4 : MvPolynomial.vanishingIdeal K Z = P i := le_antisymm h2 h3
    calc Z ⊆ zclosure Z := subset_zclosure Z
      _ = MvPolynomial.zeroLocus K (P i) := by
          show MvPolynomial.zeroLocus K (MvPolynomial.vanishingIdeal K Z) = _
          rw [h4]
  · rw [← affineDim_zclosure Y, hcover, affineDim_iUnion]

/-! ### Images do not gain dimension -/

/-- An injective map of finitely generated domains over a field does not
decrease the Krull dimension.  This is `ringKrullDim_eq_trdeg` plus the
transcendence-degree tower law. -/
theorem ringKrullDim_le_of_injective (F : Type u) (A B : Type v) [Field F] [CommRing A]
    [CommRing B] [IsDomain A] [IsDomain B] [Algebra F A] [Algebra F B]
    [Algebra.FiniteType F A] [Algebra.FiniteType F B] (φ : A →ₐ[F] B)
    (hφ : Function.Injective φ) : ringKrullDim A ≤ ringKrullDim B := by
  obtain ⟨dA, hdA, htA⟩ := ringKrullDim_eq_trdeg F A
  obtain ⟨dB, hdB, htB⟩ := ringKrullDim_eq_trdeg F B
  let _instAB : Algebra A B := (φ : A →+* B).toAlgebra
  have _ : IsScalarTower F A B :=
    IsScalarTower.of_algebraMap_eq fun x => (φ.commutes x).symm
  have _ : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hφ
  have _ : FaithfulSMul F A :=
    (faithfulSMul_iff_algebraMap_injective F A).mpr (algebraMap F A).injective
  have htower : Cardinal.lift.{v} (Algebra.trdeg F A) + Cardinal.lift.{v} (Algebra.trdeg A B)
      = Cardinal.lift.{v} (Algebra.trdeg F B) := lift_trdeg_add_eq F A B
  rw [htA, htB] at htower
  simp only [Cardinal.lift_natCast] at htower
  have hle : (dA : Cardinal.{v}) ≤ (dB : Cardinal.{v}) :=
    htower ▸ le_self_add
  have hnat : dA ≤ dB := by exact_mod_cast hle
  rw [hdA, hdB]
  exact_mod_cast hnat

/-- The image of an *irreducible* affine set under a polynomial map does not gain
dimension. -/
theorem affineDim_image_le_of_isPrime [IsAlgClosed K] [Finite ι] [Finite κ]
    {f : (ι → K) → (κ → K)} (hf : IsPolyMap f) {C : Set (ι → K)}
    (hC : (MvPolynomial.vanishingIdeal K C).IsPrime) :
    affineDim (f '' C) ≤ affineDim C := by
  obtain ⟨F, hF⟩ := hf
  have _ : (MvPolynomial.vanishingIdeal K C).IsPrime := hC
  have himg : (MvPolynomial.vanishingIdeal K (f '' C)).IsPrime :=
    irreducible_image ⟨F, hF⟩ hC
  have _ : (MvPolynomial.vanishingIdeal K (f '' C)).IsPrime := himg
  -- The induced map on coordinate rings.
  have hker : ∀ g : MvPolynomial κ K, g ∈ MvPolynomial.vanishingIdeal K (f '' C) ↔
      aeval F g ∈ MvPolynomial.vanishingIdeal K C := by
    intro g
    rw [vanishingIdeal_image hF]
    exact Iff.rfl
  set φ : MvPolynomial κ K ⧸ MvPolynomial.vanishingIdeal K (f '' C) →ₐ[K]
      MvPolynomial ι K ⧸ MvPolynomial.vanishingIdeal K C :=
    Ideal.Quotient.liftₐ _
      ((Ideal.Quotient.mkₐ K (MvPolynomial.vanishingIdeal K C)).comp (aeval F))
      (fun g hg => Ideal.Quotient.eq_zero_iff_mem.2 ((hker g).1 hg)) with hφdef
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective a
    have : Ideal.Quotient.mk (MvPolynomial.vanishingIdeal K C) (aeval F g) = 0 := ha
    rw [Ideal.Quotient.eq_zero_iff_mem] at this ⊢
    exact (hker g).2 this
  exact ringKrullDim_le_of_injective K _ _ φ hinj

/-- **Images do not gain dimension.**  For any subset `S` of affine space and any
polynomial map `f`, `affineDim (f '' S) ≤ affineDim S`. -/
theorem affineDim_image_le [IsAlgClosed K] [Finite ι] [Finite κ]
    {f : (ι → K) → (κ → K)} (hf : IsPolyMap f) (S : Set (ι → K)) :
    affineDim (f '' S) ≤ affineDim S := by
  obtain ⟨m, C, hCprime, -, -, hcover, -, hdim⟩ := components (K := K) S
  have h1 : f '' S ⊆ ⋃ i, f '' C i := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := hz
    have : y ∈ ⋃ i, C i := hcover ▸ subset_zclosure S hy
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 this
    exact Set.mem_iUnion.2 ⟨i, ⟨y, hi, rfl⟩⟩
  calc affineDim (f '' S) ≤ affineDim (⋃ i, f '' C i) := affineDim_mono h1
    _ = ⨆ i, affineDim (f '' C i) := affineDim_iUnion _
    _ ≤ ⨆ i, affineDim (C i) :=
        iSup_mono fun i => affineDim_image_le_of_isPrime hf (hCprime i)
    _ = affineDim S := hdim.symm

/-- Two affine sets carried into one another by polynomial maps have the same
dimension. -/
theorem affineDim_image_eq [IsAlgClosed K] [Finite ι] [Finite κ]
    {u : (ι → K) → (κ → K)} {v : (κ → K) → (ι → K)} (hu : IsPolyMap u) (hv : IsPolyMap v)
    {S : Set (ι → K)} (h : ∀ y ∈ S, v (u y) = y) :
    affineDim (u '' S) = affineDim S := by
  refine le_antisymm (affineDim_image_le hu S) ?_
  have hS : S ⊆ v '' (u '' S) := by
    intro y hy
    exact ⟨u y, ⟨y, hy, rfl⟩, h y hy⟩
  calc affineDim S ≤ affineDim (v '' (u '' S)) := affineDim_mono hS
    _ ≤ affineDim (u '' S) := affineDim_image_le hv _

end Height.Geometry
