import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Height.Toolbox.AffineAlgebra
import Height.Toolbox.Topology

/-!
# Krull dimension of subsets of a prime spectrum

The dimension of a *constructible* subset of `Spec R` is the dimension of its closure, for
`R` a finitely generated algebra over a field.  This is the geometric form of the dimension
formula for affine algebras (`Toolbox/AffineAlgebra.ringKrullDim_localization_away`): it is
what makes `affineDim`, which is by construction a dimension of Zariski closures, compute the
honest dimension of a constructible set.

The two structural computations are stated for an arbitrary commutative ring:
`topologicalKrullDim_zeroLocus` (`dim V(I) = dim (R ⧸ I)`) and
`topologicalKrullDim_zeroLocus_inter_basicOpen` (`dim (V(I) ∩ D(f)) = dim (R ⧸ I)_f`, the
localisation realised as an open subspace of a closed subspace).  All of them are mathlib
candidates.
-/

universe u v

namespace Height.Toolbox

open PrimeSpectrum TopologicalSpace Topology

section Structural

variable {R : Type*} [CommRing R]

/-- **The zero locus of `I` has the Krull dimension of `R ⧸ I`**: `comap` of the quotient map
is a closed embedding onto it (`PrimeSpectrum.isClosedEmbedding_comap_of_surjective`). -/
theorem topologicalKrullDim_zeroLocus (I : Ideal R) :
    topologicalKrullDim (zeroLocus (I : Set R)) = ringKrullDim (R ⧸ I) := by
  have hrange : Set.range (comap (Ideal.Quotient.mk I)) = zeroLocus (I : Set R) := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
  have e : PrimeSpectrum (R ⧸ I) ≃ₜ (zeroLocus (I : Set R)) :=
    (PrimeSpectrum.isClosedEmbedding_comap_of_surjective _ _
        Ideal.Quotient.mk_surjective).isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hrange)
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := R ⧸ I)]
  exact (IsHomeomorph.topologicalKrullDim_eq _ e.isHomeomorph).symm

/-- The structure map `R → (R ⧸ I)_f` of the localised quotient: `Spec` of it is the
inclusion of `V(I) ∩ D(f)`. -/
noncomputable def awayQuotient (I : Ideal R) (f : R) :
    R →+* Localization.Away (Ideal.Quotient.mk I f) :=
  (algebraMap (R ⧸ I) (Localization.Away (Ideal.Quotient.mk I f))).comp (Ideal.Quotient.mk I)

private theorem comap_awayQuotient (I : Ideal R) (f : R) :
    comap (awayQuotient I f) = (comap (Ideal.Quotient.mk I)).comp
      (comap (algebraMap (R ⧸ I) (Localization.Away (Ideal.Quotient.mk I f)))) := by
  rw [awayQuotient, comap_comp]

/-- **`V(I) ∩ D(f)` is the spectrum of `(R ⧸ I)_f`**, as a subspace of `Spec R`
(`PrimeSpectrum.localization_away_comap_range` after the closed immersion of `V(I)`). -/
theorem range_comap_awayQuotient (I : Ideal R) (f : R) :
    Set.range (comap (awayQuotient I f)) =
      zeroLocus (I : Set R) ∩ (basicOpen f : Set (PrimeSpectrum R)) := by
  rw [comap_awayQuotient]
  show Set.range (comap (Ideal.Quotient.mk I) ∘
    comap (algebraMap (R ⧸ I) (Localization.Away (Ideal.Quotient.mk I f)))) = _
  rw [Set.range_comp, PrimeSpectrum.localization_away_comap_range _ (Ideal.Quotient.mk I f),
    show ((basicOpen (Ideal.Quotient.mk I f) : Set (PrimeSpectrum (R ⧸ I)))) =
      comap (Ideal.Quotient.mk I) ⁻¹' (basicOpen f : Set (PrimeSpectrum R)) from rfl,
    Set.image_preimage_eq_inter_range,
    range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker, Set.inter_comm]

/-- The pieces produced by `Topology.IsConstructible.induction_of_isTopologicalBasis` on the
basic opens are the locally closed sets `V(s) ∩ D(f)`. -/
theorem basicOpen_sdiff_biUnion (f : R) (s : Set R) :
    ((basicOpen f : Set (PrimeSpectrum R)) \ ⋃ j ∈ s, (basicOpen j : Set (PrimeSpectrum R))) =
      zeroLocus ((Ideal.span s : Ideal R) : Set R) ∩ basicOpen f := by
  rw [zeroLocus_span]
  ext q
  simp only [Set.mem_sdiff, Set.mem_iUnion, mem_basicOpen, not_exists, not_not,
    Set.mem_inter_iff, mem_zeroLocus, Set.subset_def, SetLike.mem_coe]
  tauto

theorem isEmbedding_comap_awayQuotient (I : Ideal R) (f : R) :
    IsEmbedding (comap (awayQuotient I f)) := by
  rw [comap_awayQuotient]
  exact (PrimeSpectrum.isClosedEmbedding_comap_of_surjective _ _
      Ideal.Quotient.mk_surjective).isEmbedding.comp
    (PrimeSpectrum.localization_away_isOpenEmbedding _ (Ideal.Quotient.mk I f)).isEmbedding

/-- **A basic open of a zero locus is the spectrum of the localised quotient**: `V(I) ∩ D(f)`
is the range of `comap` of `R → (R ⧸ I)_f`, a closed embedding followed by an open one
(`PrimeSpectrum.localization_away_comap_range`). -/
theorem topologicalKrullDim_zeroLocus_inter_basicOpen (I : Ideal R) (f : R) :
    topologicalKrullDim
        (zeroLocus (I : Set R) ∩ basicOpen f : Set (PrimeSpectrum R)) =
      ringKrullDim (Localization.Away (Ideal.Quotient.mk I f)) := by
  rw [← range_comap_awayQuotient I f, ← Set.image_univ,
    topologicalKrullDim_image_of_isEmbedding (isEmbedding_comap_awayQuotient I f),
    ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact (Homeomorph.Set.univ _).isHomeomorph.topologicalKrullDim_eq

end Structural

section Affine

variable (K : Type u) [Field K] {R : Type v} [CommRing R] [Algebra K R] [Algebra.FiniteType K R]

-- `K` is not mentioned by the statements, so without this its instances would be dropped
-- (the same trap as in `Toolbox/AffineAlgebra.lean`).
include K

/-- A nonempty basic open of an irreducible closed subset of the spectrum of an affine algebra
has the dimension of that closed subset: this is
`AffineAlgebra.ringKrullDim_localization_away` read on the spectrum. -/
theorem topologicalKrullDim_zeroLocus_inter_basicOpen_of_isPrime (P : Ideal R) [P.IsPrime]
    {f : R} (hf : f ∉ P) :
    topologicalKrullDim
        (zeroLocus (P : Set R) ∩ basicOpen f : Set (PrimeSpectrum R)) =
      ringKrullDim (R ⧸ P) := by
  have _ : Algebra.FiniteType K (R ⧸ P) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K P) Ideal.Quotient.mk_surjective
  have hne : Ideal.Quotient.mk P f ≠ 0 := fun h => hf (Ideal.Quotient.eq_zero_iff_mem.mp h)
  rw [topologicalKrullDim_zeroLocus_inter_basicOpen,
    ringKrullDim_localization_away (K := K) (R ⧸ P) hne]

/-- **The base case of `topologicalKrullDim_closure_of_isConstructible`**: `V(I) ∩ D(f)` is
covered by the finitely many `V(P) ∩ D(f)` for `P` a minimal prime of `I`, and each of those
is either empty (when `f ∈ P`) or dense in the irreducible `V(P)`, of the same dimension. -/
theorem topologicalKrullDim_closure_zeroLocus_inter_basicOpen_le (I : Ideal R) (f : R) :
    topologicalKrullDim
        (closure (zeroLocus (I : Set R) ∩ basicOpen f : Set (PrimeSpectrum R))) ≤
      topologicalKrullDim (zeroLocus (I : Set R) ∩ basicOpen f : Set (PrimeSpectrum R)) := by
  have _ : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing K R
  have _ : Finite I.minimalPrimes := Ideal.finite_minimalPrimes_of_isNoetherianRing R I
  set W : Set (PrimeSpectrum R) :=
    zeroLocus (I : Set R) ∩ basicOpen f with hWdef
  set C : I.minimalPrimes → Set (PrimeSpectrum R) :=
    fun P => zeroLocus ((P : Ideal R) : Set R) ∩ basicOpen f with hCdef
  have hCsub : ∀ P, C P ⊆ W := fun P q hq =>
    ⟨zeroLocus_anti_mono_ideal P.2.1.2 hq.1, hq.2⟩
  have hcov : W = ⋃ P, C P := by
    refine Set.Subset.antisymm (fun q hq => ?_) (Set.iUnion_subset hCsub)
    have _ : q.asIdeal.IsPrime := q.isPrime
    obtain ⟨P, hPmin, hPq⟩ :=
      Ideal.exists_minimalPrimes_le (I := I) (J := q.asIdeal) ((mem_zeroLocus _ _).mp hq.1)
    exact Set.mem_iUnion.2 ⟨⟨P, hPmin⟩, ⟨(mem_zeroLocus _ _).mpr hPq, hq.2⟩⟩
  have hclos : closure W = ⋃ P, closure (C P) := by
    refine Set.Subset.antisymm ?_
      (Set.iUnion_subset fun P => closure_mono (hcov ▸ Set.subset_iUnion C P))
    refine closure_minimal ?_ (isClosed_iUnion_of_finite fun P => isClosed_closure)
    rw [hcov]
    exact Set.iUnion_mono fun P => subset_closure
  rw [hclos, topologicalKrullDim_iUnion_of_isClosed fun P => isClosed_closure]
  refine iSup_le fun P => ?_
  have hP : (P : Ideal R).IsPrime := P.2.1.1
  by_cases hf : f ∈ (P : Ideal R)
  · have hempty : C P = ∅ :=
      Set.eq_empty_iff_forall_notMem.2 fun q hq => (mem_basicOpen _ _).mp hq.2 (hq.1 hf)
    rw [hempty, closure_empty, (topologicalKrullDim_eq_bot_iff _).2 rfl]
    exact bot_le
  · have hirr : IsIrreducible (zeroLocus ((P : Ideal R) : Set R)) :=
      (isIrreducible_zeroLocus_iff _).mpr (by rw [hP.radical]; exact hP)
    have hne : (zeroLocus ((P : Ideal R) : Set R) ∩
        (basicOpen f : Set (PrimeSpectrum R))).Nonempty :=
      ⟨⟨(P : Ideal R), hP⟩, (mem_zeroLocus _ _).mpr le_rfl, hf⟩
    have hdense : closure (C P) = zeroLocus ((P : Ideal R) : Set R) :=
      Set.Subset.antisymm (closure_minimal Set.inter_subset_left (isClosed_zeroLocus _))
        (subset_closure_inter_of_isPreirreducible_of_isOpen hirr.isPreirreducible
          isOpen_basicOpen hne)
    rw [hdense, topologicalKrullDim_zeroLocus,
      ← topologicalKrullDim_zeroLocus_inter_basicOpen_of_isPrime K (P : Ideal R) hf]
    exact topologicalKrullDim_mono (hCsub P)

/-- **A constructible subset of the spectrum of an affine algebra has the dimension of its
closure.**  A constructible set is a finite union of sets `D f \ ⋃_{j ∈ s} D j = V(s) ∩ D f`
(`Topology.IsConstructible.induction_of_isTopologicalBasis` on the basic opens); the union
step is `topologicalKrullDim_union_of_isClosed` and the pieces are
`topologicalKrullDim_closure_zeroLocus_inter_basicOpen_le`. -/
theorem topologicalKrullDim_closure_of_isConstructible {W : Set (PrimeSpectrum R)}
    (hW : IsConstructible W) :
    topologicalKrullDim (closure W) = topologicalKrullDim W := by
  refine le_antisymm ?_ (topologicalKrullDim_mono subset_closure)
  have _ : Nonempty R := ⟨0⟩
  induction W, hW using Topology.IsConstructible.induction_of_isTopologicalBasis
      (b := fun r : R => (basicOpen r : Set (PrimeSpectrum R)))
      (basis := isTopologicalBasis_basic_opens) (isCompact_basis := isCompact_basicOpen) with
  | sdiff r s hs =>
    rw [basicOpen_sdiff_biUnion r s]
    exact topologicalKrullDim_closure_zeroLocus_inter_basicOpen_le K _ r
  | union A hA B hB ihA ihB =>
    rw [closure_union, topologicalKrullDim_union_of_isClosed isClosed_closure isClosed_closure]
    exact max_le (ihA.trans (topologicalKrullDim_mono Set.subset_union_left))
      (ihB.trans (topologicalKrullDim_mono Set.subset_union_right))

end Affine

end Height.Toolbox
