import Height.Geometry.Interface
import Height.Geometry.Dimension.FibreUpper
import Height.Geometry.Dimension.FibreGeneric
import Height.Geometry.Dimension.Components
import Height.Toolbox.SpectrumDim
import Mathlib.RingTheory.Localization.Away.AdjoinRoot

/-!
# The fibre-dimension theorems on the spectrum, and on `𝔸(ι; Spec K)`

`Dimension/FibreUpper.lean` and `Dimension/FibreGeneric.lean` prove the fibre-dimension
theorems in ring form (`ringKrullDim B ≤ ringKrullDim (A ⧸ ker φ) + ⨆ m maximal, …`).  This
file reads them on prime spectra: for a *locally closed* piece `V(I) ∩ D(g)` of `Spec R`,
which is the spectrum of `(R ⧸ I)_g` (`Toolbox/SpectrumDim`), the ring statement becomes a
statement about the dimension of the piece, of the closure of its image and of its fibres.

Working with pieces rather than with the whole of `Spec R` is what makes the statement of
`Geometry/Spec.topologicalKrullDim_le_image_add_iSup_fibre` provable: the fibres of the
closure of a constructible set can be strictly larger than all fibres of the set itself
(`Z = 𝔸² ∖ V(a)` under `(a, b) ↦ (a, ab)` has all fibres finite while `closure Z = 𝔸²` has a
one-dimensional fibre over the origin).
-/

universe u v w

open PrimeSpectrum TopologicalSpace Topology Height.Toolbox

namespace Height.Geometry

section Spectrum

variable (K : Type u) [Field K] {R : Type v} [CommRing R] [Algebra K R] [Algebra.FiniteType K R]
  {A : Type w} [CommRing A] [Algebra K A] [Algebra.FiniteType K A]

/-- **The fibre of `comap φ` over a maximal ideal `m`, seen inside the range of `comap σ`**, is
the zero locus of the extension of `m` along `σ ∘ φ`.  Maximality of `m` is what makes
`m ≤ comap (σ ∘ φ) q` equivalent to `comap (σ ∘ φ) q = m`. -/
theorem comap_image_zeroLocus_map_of_isMaximal {S B : Type*} [CommRing S] [CommRing B]
    {A' : Type*} [CommRing A'] (σ : S →+* B) (φ : A' →+* S) {m : Ideal A'} (hm : m.IsMaximal) :
    comap σ '' (zeroLocus ((m.map (σ.comp φ)) : Set B)) =
      Set.range (comap σ) ∩
        comap φ ⁻¹' {(⟨m, hm.isPrime⟩ : PrimeSpectrum A')} := by
  have hcomp : ∀ q : PrimeSpectrum B,
      comap φ (comap σ q) = comap (σ.comp φ) q := fun q => by rw [comap_comp]; rfl
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    refine ⟨Set.mem_range_self q, ?_⟩
    have hle : m ≤ (comap (σ.comp φ) q).asIdeal := by
      rw [comap_asIdeal, ← Ideal.map_le_iff_le_comap]
      exact (mem_zeroLocus _ _).mp hq
    rw [Set.mem_preimage, Set.mem_singleton_iff, hcomp q]
    exact PrimeSpectrum.ext ((hm.eq_of_le (comap (σ.comp φ) q).isPrime.ne_top hle).symm)
  · rintro ⟨⟨q, rfl⟩, hpm⟩
    refine ⟨q, ?_, rfl⟩
    rw [Set.mem_preimage, Set.mem_singleton_iff, hcomp q] at hpm
    rw [mem_zeroLocus, SetLike.coe_subset_coe, Ideal.map_le_iff_le_comap, ← comap_asIdeal]
    exact le_of_eq (congrArg PrimeSpectrum.asIdeal hpm).symm

/-- **The fibre-dimension bound on a locally closed piece of `Spec R`.**  `V(I) ∩ D(g)` is the
spectrum of `B = (R ⧸ I)_g`; `FibreUpper.ringKrullDim_le_of_finiteType` applied to
`A → B` bounds its dimension by the dimension of `A ⧸ ker` — the closure of the image — plus
the largest dimension of a fibre over a maximal ideal of `A`. -/
theorem topologicalKrullDim_zeroLocus_inter_basicOpen_le_add_iSup_fibre (φ : A →ₐ[K] R)
    (I : Ideal R) (g : R) :
    topologicalKrullDim (zeroLocus (I : Set R) ∩ basicOpen g : Set (PrimeSpectrum R)) ≤
      topologicalKrullDim (closure (comap (φ : A →+* R) ''
          (zeroLocus (I : Set R) ∩ basicOpen g)) : Set (PrimeSpectrum A)) +
        ⨆ m : {m : Ideal A // m.IsMaximal},
          topologicalKrullDim ((zeroLocus (I : Set R) ∩ basicOpen g) ∩
            comap (φ : A →+* R) ⁻¹' {(⟨m.1, m.2.isPrime⟩ : PrimeSpectrum A)} :
              Set (PrimeSpectrum R)) := by
  classical
  set B := Localization.Away (Ideal.Quotient.mk I g) with hB
  set W : Set (PrimeSpectrum R) := zeroLocus (I : Set R) ∩ basicOpen g with hW
  have hrange : Set.range (comap (awayQuotient I g)) = W := range_comap_awayQuotient I g
  have hemb : IsEmbedding (comap (awayQuotient I g)) := isEmbedding_comap_awayQuotient I g
  have _ : Algebra.FiniteType K B :=
    Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType K (R ⧸ I)) inferInstance
  -- the structure map `R → B` as a `K`-algebra map, and the composite `φ' : A → B`
  set ψ : R →ₐ[K] B :=
    (IsScalarTower.toAlgHom K (R ⧸ I) B).comp (Ideal.Quotient.mkₐ K I) with hψ
  have hψring : (ψ : R →+* B) = awayQuotient I g := rfl
  set φ' : A →ₐ[K] B := ψ.comp φ with hφ'
  have hφ'ring : (φ' : A →+* B) = (awayQuotient I g).comp (φ : A →+* R) := rfl
  have hkey := ringKrullDim_le_of_finiteType K A B φ'
  -- the source
  have h1 : topologicalKrullDim W = ringKrullDim B :=
    (hW ▸ topologicalKrullDim_zeroLocus_inter_basicOpen I g)
  -- the image
  have himg : Set.range (comap (φ' : A →+* B)) = comap (φ : A →+* R) '' W := by
    rw [hφ'ring, comap_comp, ← hrange]
    exact Set.range_comp _ _
  have h2 : ringKrullDim (A ⧸ RingHom.ker (φ' : A →+* B)) =
      topologicalKrullDim (closure (comap (φ : A →+* R) '' W) : Set (PrimeSpectrum A)) := by
    rw [← himg, closure_range_comap, topologicalKrullDim_zeroLocus]
  -- the fibres
  have h3 : ∀ m : {m : Ideal A // m.IsMaximal},
      ringKrullDim (B ⧸ (m.1.map (φ' : A →+* B))) =
        topologicalKrullDim (W ∩ comap (φ : A →+* R) ⁻¹'
          {(⟨m.1, m.2.isPrime⟩ : PrimeSpectrum A)} : Set (PrimeSpectrum R)) := by
    intro m
    have hfib : comap (awayQuotient I g) '' (zeroLocus ((m.1.map (φ' : A →+* B)) : Set B)) =
        W ∩ comap (φ : A →+* R) ⁻¹' {(⟨m.1, m.2.isPrime⟩ : PrimeSpectrum A)} := by
      rw [hφ'ring, comap_image_zeroLocus_map_of_isMaximal _ _ m.2, hrange]
    rw [← hfib, topologicalKrullDim_image_of_isEmbedding hemb, topologicalKrullDim_zeroLocus]
  rw [h1, ← h2]
  refine hkey.trans (add_le_add le_rfl (iSup_le fun m => ?_))
  exact le_of_eq_of_le (h3 m) (le_iSup (fun m : {m : Ideal A // m.IsMaximal} =>
    topologicalKrullDim (W ∩ comap (φ : A →+* R) ⁻¹'
      {(⟨m.1, m.2.isPrime⟩ : PrimeSpectrum A)} : Set (PrimeSpectrum R))) m)

/-- **The fibre-dimension theorem on `Spec R`, upper form.**  A constructible set is a finite
union of locally closed pieces (`IsConstructible.induction_of_isTopologicalBasis` on the basic
opens), and both sides are compatible with finite unions
(`topologicalKrullDim_closure_of_isConstructible` turns the union of subspaces into a union of
closed sets). -/
theorem topologicalKrullDim_le_add_iSup_fibre_of_isConstructible (φ : A →ₐ[K] R)
    {W : Set (PrimeSpectrum R)} (hW : IsConstructible W) :
    topologicalKrullDim W ≤
      topologicalKrullDim (closure (comap (φ : A →+* R) '' W) : Set (PrimeSpectrum A)) +
        ⨆ m : {m : Ideal A // m.IsMaximal},
          topologicalKrullDim (W ∩ comap (φ : A →+* R) ⁻¹'
            {(⟨m.1, m.2.isPrime⟩ : PrimeSpectrum A)} : Set (PrimeSpectrum R)) := by
  have _ : Nonempty R := ⟨0⟩
  induction W, hW using Topology.IsConstructible.induction_of_isTopologicalBasis
      (b := fun r : R => (basicOpen r : Set (PrimeSpectrum R)))
      (basis := isTopologicalBasis_basic_opens) (isCompact_basis := isCompact_basicOpen) with
  | sdiff r s hs =>
    rw [basicOpen_sdiff_biUnion r s]
    exact topologicalKrullDim_zeroLocus_inter_basicOpen_le_add_iSup_fibre K φ _ r
  | union W₁ hW₁ W₂ hW₂ ih₁ ih₂ =>
    have hmax : topologicalKrullDim (W₁ ∪ W₂ : Set (PrimeSpectrum R)) =
        max (topologicalKrullDim W₁) (topologicalKrullDim W₂) := by
      rw [← topologicalKrullDim_closure_of_isConstructible K (hW₁.union hW₂),
        ← topologicalKrullDim_closure_of_isConstructible K hW₁,
        ← topologicalKrullDim_closure_of_isConstructible K hW₂, closure_union,
        topologicalKrullDim_union_of_isClosed isClosed_closure isClosed_closure]
    rw [hmax]
    refine max_le (ih₁.trans (add_le_add ?_ ?_)) (ih₂.trans (add_le_add ?_ ?_))
    · exact topologicalKrullDim_mono (closure_mono (Set.image_mono Set.subset_union_left))
    · exact iSup_mono fun m =>
        topologicalKrullDim_mono (Set.inter_subset_inter_left _ Set.subset_union_left)
    · exact topologicalKrullDim_mono (closure_mono (Set.image_mono Set.subset_union_right))
    · exact iSup_mono fun m =>
        topologicalKrullDim_mono (Set.inter_subset_inter_left _ Set.subset_union_right)

end Spectrum

section Image

-- `Dimension/Components.ringKrullDim_le_of_injective` puts the base field and the two algebras
-- in one universe, so this section does too; the consumers are at `u = 0`.
variable (K : Type u) [Field K] {R A : Type u} [CommRing R] [CommRing A] [Algebra K R]
  [Algebra K A] [Algebra.FiniteType K R] [Algebra.FiniteType K A]

include K

end Image

end Height.Geometry
