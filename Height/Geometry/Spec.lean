import Height.Geometry.Interface
import Height.Toolbox.LocalRing
import Height.Toolbox.SpectrumDim
import Height.Geometry.Fibre
import Height.Geometry.Stalk
import Height.Geometry.Tangent.RegularArc
import Height.Geometry.Tangent.JacobianPrime
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.CategoryTheory.Monoidal.Grp
import Mathlib.CategoryTheory.Monoidal.Mod
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod

/-!
# The geometry API on `𝔸(ι; Spec K)`

These are the scheme-theoretic statements the development is made of.  They are
proved and used through the classical interface of `Geometry/Interface.lean`;
nothing here mentions `aeval`, `zeroLocus K I` or `affineDim`.  General
topology (the Krull dimension of unions, of finite unions, of irreducible
components, and the generic quantifier) is in `Toolbox/Topology.lean`.

What mathlib already gives is used, not restated: the Zariski topology,
`IsLocallyClosed`, `Topology.IsConstructible` and its Boolean calculus,
Noetherianity, sober generic points, and (through `specIso`) Chevalley,
`topologicalKrullDim = ringKrullDim`, components = minimal primes, closed
points; group objects (`GrpObj`) and their actions (`ModObj`) in the cartesian
monoidal category `Over (Spec K)`.  What is stated is what mathlib lacks:

1. the dimension of the closure of a constructible set (finite type over a field);
2. Chevalley for morphisms over `Spec K`;
3. the fibre-dimension theorem, with fibres over `K`-points;
4. orbits of a group scheme action as images of orbit morphisms, orbit
   dimension, the homogeneous fibration count;
5. `dim V (I : Set (MvPolynomial ι K)) ≤ dim T_x` and tangent-generic points;
6. arcs through tangent vectors (the constructor behind
   `exists_pencilComponent_arcTangent`).
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Height.Toolbox

namespace Height.Geometry

universe u

/-! ### 1. Dimension -/

section Dimension

variable {K : Type u} [Field K] {ι : Type u} [Finite ι]

/-- A constructible set has the dimension of its closure.  True over every field; route:
a constructible set is a finite union of pieces `V I ∩ D g` (`IsConstructible.induction`),
each `V I` a finite union of irreducible components `V P` (`IsClosed.exists_V_eq`,
`isIrreducible_V_iff`, `topologicalKrullDim_eq_iSup_irreducibleComponents`), and
`V P ∩ D g` is either empty or dense in `V P` with `dim (V P ∩ D g) = dim (K[ι] ⧸ P)_g =
dim (K[ι] ⧸ P)` (`ringKrullDim_localization_away`, `topologicalKrullDim_V`); finite unions
by `topologicalKrullDim_iUnion_of_isClosed` and `closure_iUnion` for finite families.  Over
an algebraically closed field it is also `topologicalKrullDim_eq_affineDim` through
`topologicalKrullDim_closure_eq_affineDim`. -/
theorem topologicalKrullDim_closure {Z : Set 𝔸(ι; Spec (.of K))} (hZ : IsConstructible Z) :
    topologicalKrullDim (closure Z) = topologicalKrullDim Z := by
  have h := topologicalKrullDim_closure_of_isConstructible K
    ((specHomeo K ι).isConstructible_image hZ)
  rwa [← (specHomeo K ι).image_closure, topologicalKrullDim_image_of_isEmbedding (specHomeo K ι).isEmbedding,
    topologicalKrullDim_image_of_isEmbedding (specHomeo K ι).isEmbedding] at h

end Dimension

/-! ### 2. Chevalley -/

section Chevalley

variable {K : Type u} [Field K] {ι κ : Type u} [Finite ι] [Finite κ]

/-- **Chevalley**: the image of a constructible set under a morphism over `Spec K`
is constructible (`PrimeSpectrum.isConstructible_comap_image` through `specIso`). -/
theorem isConstructible_image (f : HomOver K ι κ) {Z : Set 𝔸(ι; Spec (.of K))}
    (hZ : IsConstructible Z) : IsConstructible (f.1 '' Z) := by
  obtain ⟨F, rfl⟩ := (polyMapEquiv (K := K) (ι := ι) (κ := κ)).surjective f
  have himg : specHomeo K κ '' ((polyMapEquiv F).1 '' Z) =
      PrimeSpectrum.comap (MvPolynomial.aeval (R := K) F).toRingHom '' (specHomeo K ι '' Z) := by
    rw [← Set.image_comp, ← Set.image_comp]
    exact Set.image_congr' (specHomeo_polyMapEquiv F)
  have hcon : IsConstructible (specHomeo K κ '' ((polyMapEquiv F).1 '' Z)) := by
    rw [himg]
    exact PrimeSpectrum.isConstructible_comap_image (finitePresentation_aeval F)
      ((specHomeo K ι).isConstructible_image hZ)
  have hback := (specHomeo K κ).symm.isConstructible_image hcon
  rwa [← Set.image_comp, show ((specHomeo K κ).symm ∘ specHomeo K κ) = id from
    funext fun p => (specHomeo K κ).symm_apply_apply p, Set.image_id] at hback

end Chevalley

/-! ### 3. Morphisms: the fibre-dimension theorem -/

section Morphism

-- `[IsAlgClosed K]`: the fibres are counted over `K`-points, and a nonempty constructible
-- set without `K`-points (`V {X² + 1}` over `𝔽₃`) refutes the bound otherwise (geo-spec).
variable {K : Type u} [Field K] [IsAlgClosed K] {ι κ : Type u} [Finite ι] [Finite κ]

/-- **The fibre-dimension theorem**, upper form: the dimension of a constructible
set is at most the dimension of its image plus the largest fibre dimension over a
`K`-point.  (Today's `FibreUpper.ringKrullDim_le_of_finiteType`, `LocClosed`'s
three `affineDim_le_add_fibre_*` and the transitive-fibration counts are all
this statement.) -/
theorem topologicalKrullDim_le_image_add_iSup_fibre (f : HomOver K ι κ)
    {Z : Set 𝔸(ι; Spec (.of K))} (hZ : IsConstructible Z) :
    topologicalKrullDim Z ≤
      topologicalKrullDim (closure (f.1 '' Z) : Set 𝔸(κ; Spec (.of K))) +
        ⨆ x : κ → K, topologicalKrullDim
          (Z ∩ f.1 ⁻¹' {(ptEquiv K x : 𝔸(κ; Spec (.of K)))} : Set 𝔸(ι; Spec (.of K))) := by
  obtain ⟨F, rfl⟩ := (polyMapEquiv (K := K) (ι := ι) (κ := κ)).surjective f
  have hcomap : ∀ p : 𝔸(ι; Spec (.of K)), specHomeo K κ ((polyMapEquiv F).1 p) =
      PrimeSpectrum.comap
        ((MvPolynomial.aeval (R := K) F : MvPolynomial κ K →ₐ[K] MvPolynomial ι K) :
          MvPolynomial κ K →+* MvPolynomial ι K) (specHomeo K ι p) :=
    specHomeo_polyMapEquiv F
  -- every fibre of the transported map over a maximal ideal is a fibre over a `K`-point
  have hfib : ∀ m : {m : Ideal (MvPolynomial κ K) // m.IsMaximal}, ∃ x : κ → K,
      (specHomeo K ι '' Z) ∩ PrimeSpectrum.comap
          ((MvPolynomial.aeval (R := K) F : MvPolynomial κ K →ₐ[K] MvPolynomial ι K) :
            MvPolynomial κ K →+* MvPolynomial ι K) ⁻¹'
          {(⟨m.1, m.2.isPrime⟩ : PrimeSpectrum (MvPolynomial κ K))} =
        specHomeo K ι '' (Z ∩ (polyMapEquiv F).1 ⁻¹' {(ptEquiv K x : 𝔸(κ; Spec (.of K)))}) := by
    rintro ⟨m, hm⟩
    obtain ⟨x, rfl⟩ := MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton.mp hm
    refine ⟨x, ?_⟩
    have hpt : (⟨MvPolynomial.vanishingIdeal K {x}, hm.isPrime⟩ :
        PrimeSpectrum (MvPolynomial κ K)) = specHomeo K κ (ptEquiv K x : 𝔸(κ; Spec (.of K))) :=
      (specHomeo_pt x).symm
    rw [hpt]
    ext q
    constructor
    · rintro ⟨⟨p, hp, rfl⟩, hq2⟩
      exact ⟨p, ⟨hp, (specHomeo K κ).injective ((hcomap p).trans hq2)⟩, rfl⟩
    · rintro ⟨p, ⟨hp, hp2⟩, rfl⟩
      exact ⟨⟨p, hp, rfl⟩, by rw [Set.mem_preimage, ← hcomap p, Set.mem_singleton_iff, hp2]⟩
  refine le_trans (le_of_eq
      (topologicalKrullDim_image_of_isEmbedding (specHomeo K ι).isEmbedding Z).symm) ?_
  refine (topologicalKrullDim_le_add_iSup_fibre_of_isConstructible K
    (MvPolynomial.aeval (R := K) F : MvPolynomial κ K →ₐ[K] MvPolynomial ι K)
    ((specHomeo K ι).isConstructible_image hZ)).trans (add_le_add (le_of_eq ?_) (iSup_le ?_))
  · rw [show PrimeSpectrum.comap
        ((MvPolynomial.aeval (R := K) F : MvPolynomial κ K →ₐ[K] MvPolynomial ι K) :
          MvPolynomial κ K →+* MvPolynomial ι K) '' (specHomeo K ι '' Z) =
        specHomeo K κ '' ((polyMapEquiv F).1 '' Z) by
      rw [← Set.image_comp, ← Set.image_comp]
      exact (Set.image_congr' hcomap).symm,
      ← (specHomeo K κ).image_closure,
      topologicalKrullDim_image_of_isEmbedding (specHomeo K κ).isEmbedding]
  · intro m
    obtain ⟨x, hx⟩ := hfib m
    rw [hx, topologicalKrullDim_image_of_isEmbedding (specHomeo K ι).isEmbedding]
    exact le_iSup (fun x : κ → K => topologicalKrullDim
      (Z ∩ (polyMapEquiv F).1 ⁻¹' {(ptEquiv K x : 𝔸(κ; Spec (.of K)))} :
        Set 𝔸(ι; Spec (.of K)))) x

end Morphism

/-! ### 4. Group actions and orbits -/

section Orbit

open MonoidalCategory

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

variable {S : Scheme.{u}}

/-- The orbit morphism of a section `y` of `X` under an action of the group object
`G`: `g ↦ g · y`. -/
noncomputable def orbitMap (G : Over S) [GrpObj G] (X : Over S) [ModObj G X]
    (y : 𝟙_ (Over S) ⟶ X) : G ⟶ X :=
  (ρ_ G).inv ≫ (G ◁ y) ≫ ModObj.smul (M := G) (X := X)

/-- The orbit of a section: the image of the group under its orbit morphism. -/
noncomputable def orbit (G : Over S) [GrpObj G] (X : Over S) [ModObj G X]
    (y : 𝟙_ (Over S) ⟶ X) : Set X.left :=
  Set.range (orbitMap G X y).left

/-! #### Translation

The three morphisms above are read on generalised points through mathlib's group and
action structures on hom sets (`CategoryTheory.Hom.group`, `CategoryTheory.Hom.mulAction`):
`h ≫ orbitMap G X y = h • y`, `x ≫ actMap G X g = g • x`, `h ≫ leftTranslate G g = g * h`.
Left translation is then an isomorphism intertwining the orbit morphism with the action,
so every nonempty fibre of the orbit morphism over a section is a translate of the
stabiliser. -/

open scoped MonObj

variable {K : Type u} [Field K] [IsAlgClosed K] (G : Over (Spec (.of K))) [GrpObj G]
  [IsAffine G.left] [LocallyOfFiniteType G.hom]
  (X : Over (Spec (.of K))) [ModObj G X] [IsAffine X.left] [LocallyOfFiniteType X.hom]

omit [IsAlgClosed K] [IsAffine G.left] [LocallyOfFiniteType G.hom] [IsAffine X.left]
  [LocallyOfFiniteType X.hom] in
/-! #### The transitive fibration, transferred to coordinates -/

section Helpers

omit [IsAlgClosed K]

end Helpers

/-! #### The chart transfer

Both fibration counts below open with the same passage from schemes to coordinates: charts
for `G`, `X` and `Y`, the polynomial map computing `f` between the last two, the coordinate
sets of `Z` and of `f '' Z`, and the transported stability of `Z`.  It is stated once here,
so that each count contains only the part that differs — the transitive one carries
equivariance of `f`, the orbit one carries invariance. -/

omit [IsAffine G.left] [LocallyOfFiniteType G.hom] [IsAffine X.left]
  [LocallyOfFiniteType X.hom] in
/-! #### The orbit fibration, transferred to coordinates

Two more chart computations: the `K`-points of an orbit are the orbit of the coordinate
tuple under `AffineChart.toPolyAction`, and the `K`-points of a fibre `Z ∩ f⁻¹(y)` are the
fibre of the polynomial map over the coordinates of `y`. -/

omit [IsAffine G.left] [LocallyOfFiniteType G.hom] [IsAffine X.left]
  [LocallyOfFiniteType X.hom] [IsAlgClosed K] in
omit [IsAffine G.left] [LocallyOfFiniteType G.hom] [IsAffine X.left]
  [LocallyOfFiniteType X.hom] [IsAlgClosed K] in
/-! #### The classical corollaries

The counts above are stated for group objects and sections; consumers work with a
constructible subset of `𝔸(ν; Spec K)`, a `HomOver` map and `K`-points.  This is the
finite-fibre count in that form; the two fibration counts need a `GroupPresentation` and so
live in `Geometry/Group.lean` (which imports this file). -/

omit [GrpObj G] [IsAffine G.left] [LocallyOfFiniteType G.hom] [ModObj G X] [IsAffine X.left]
  [LocallyOfFiniteType X.hom] in
/-- **The finite-fibre count on `K`-points.**  A `HomOver` map with finite fibres over every
`K`-point preserves the dimension of a constructible set.  Finiteness is required over
`K`-points only; the all-points form is not needed
(`LocClosed.affineDim_of_finite_fibres_constructible` and
`topologicalKrullDim_eq_affineDim`, through `pts_image_polyMapEquiv`). -/
theorem topologicalKrullDim_eq_of_finite_fibres_pts {ν κ : Type u} [Finite ν] [Finite κ]
    (F : κ → MvPolynomial ν K) {Z : Set 𝔸(ν; Spec (.of K))} (hZ : IsConstructible Z)
    (hfin : ∀ w : κ → K,
      {x : ν → K | (ptEquiv K x : 𝔸(ν; Spec (.of K))) ∈ Z ∧
        (fun j => MvPolynomial.aeval x (F j)) = w}.Finite) :
    topologicalKrullDim Z = topologicalKrullDim ((polyMapEquiv F).1.base '' Z) := by
  have hfp : IsPolyMap (fun (x : ν → K) (j : κ) => MvPolynomial.aeval x (F j)) :=
    ⟨F, fun _ _ => rfl⟩
  have hmain := affineDim_of_finite_fibres_constructible hfp
    {x : ν → K | (ptEquiv K x : 𝔸(ν; Spec (.of K))) ∈ Z}
    {w : κ → K | (ptEquiv K w : 𝔸(κ; Spec (.of K))) ∈ (polyMapEquiv F).1.base '' Z}
    (isAffineConstructible_pts hZ) (pts_image_polyMapEquiv F hZ) (fun w _ => hfin w)
  rw [topologicalKrullDim_eq_affineDim hZ,
    topologicalKrullDim_eq_affineDim (isConstructible_image (polyMapEquiv F) hZ)]
  exact hmain

omit [GrpObj G] [IsAffine G.left] [LocallyOfFiniteType G.hom] [ModObj G X] [IsAffine X.left]
  [LocallyOfFiniteType X.hom] in
/-- **The finite-fibre count on `K`-points, classical form.**  The `K`-points of a
constructible locus and their image under a polynomial family have the same `affineDim`
as soon as every fibre over a `K`-point is finite.  This is
`topologicalKrullDim_eq_of_finite_fibres_pts` transported by
`topologicalKrullDim_eq_affineDim` and `pts_image_polyMapEquiv`; it is the API form of
`Dimension/LocClosed.affineDim_of_finite_fibres_constructible`. -/
theorem affineDim_image_eq_of_finite_fibres_pts {ν κ : Type u} [Finite ν] [Finite κ]
    (F : κ → MvPolynomial ν K) {Z : Set 𝔸(ν; Spec (.of K))} (hZ : IsConstructible Z)
    (hfin : ∀ w : κ → K,
      {x : ν → K | (ptEquiv K x : 𝔸(ν; Spec (.of K))) ∈ Z ∧
        (fun j => MvPolynomial.aeval x (F j)) = w}.Finite) :
    affineDim ((fun (x : ν → K) (j : κ) => MvPolynomial.aeval x (F j)) ''
        {x : ν → K | (ptEquiv K x : 𝔸(ν; Spec (.of K))) ∈ Z}) =
      affineDim {x : ν → K | (ptEquiv K x : 𝔸(ν; Spec (.of K))) ∈ Z} := by
  have h := topologicalKrullDim_eq_of_finite_fibres_pts F hZ hfin
  rw [topologicalKrullDim_eq_affineDim hZ,
    topologicalKrullDim_eq_affineDim (isConstructible_image (polyMapEquiv F) hZ),
    ← pts_image_polyMapEquiv F hZ] at h
  exact h.symm

omit [GrpObj G] [IsAffine G.left] [LocallyOfFiniteType G.hom] [ModObj G X] [IsAffine X.left]
  [LocallyOfFiniteType X.hom] in
/-- **The fibre-dimension bound on `K`-points.**  If every fibre of the polynomial family
`F` over a `K`-point meets the `K`-points of a constructible locus in a set of dimension
at most `c`, then those `K`-points have dimension at most `c` more than their image.  This
is `topologicalKrullDim_le_image_add_iSup_fibre` transported by
`topologicalKrullDim_closure`, `topologicalKrullDim_eq_affineDim` and
`pts_image_polyMapEquiv`; it is the API form of the three upper bounds
`Dimension/Homogeneous.affineDim_le_add_fibre`,
`Dimension/LocClosed.affineDim_le_add_fibre_locClosed_le` and
`affineDim_le_add_fibre_constructible_le`, and unlike them it needs no Zariski closure of
the source (a constructible locus is enough). -/
theorem affineDim_le_image_add_fibre_pts {ν κ : Type u} [Finite ν] [Finite κ]
    (F : κ → MvPolynomial ν K) {Z : Set 𝔸(ν; Spec (.of K))} (hZ : IsConstructible Z)
    (c : WithBot ℕ∞)
    (hc : ∀ w : κ → K,
      affineDim ({x : ν → K | (ptEquiv K x : 𝔸(ν; Spec (.of K))) ∈ Z} ∩
        (fun (x : ν → K) (j : κ) => MvPolynomial.aeval x (F j)) ⁻¹' {w}) ≤ c) :
    affineDim {x : ν → K | (ptEquiv K x : 𝔸(ν; Spec (.of K))) ∈ Z} ≤
      affineDim ((fun (x : ν → K) (j : κ) => MvPolynomial.aeval x (F j)) ''
        {x : ν → K | (ptEquiv K x : 𝔸(ν; Spec (.of K))) ∈ Z}) + c := by
  have himg : IsConstructible ((polyMapEquiv F).1 '' Z) := isConstructible_image _ hZ
  have hclosed : ∀ w : κ → K, IsClosed ({(ptEquiv K w : 𝔸(κ; Spec (.of K)))} :
      Set 𝔸(κ; Spec (.of K))) := by
    intro w
    have h : (ptEquiv K w : 𝔸(κ; Spec (.of K))) ∈
        Set.range (fun z : κ → K => (ptEquiv K z : 𝔸(κ; Spec (.of K)))) := ⟨w, rfl⟩
    rwa [range_pt] at h
  have hfibc : ∀ w : κ → K, IsConstructible
      (Z ∩ (polyMapEquiv F).1 ⁻¹' {(ptEquiv K w : 𝔸(κ; Spec (.of K)))} :
        Set 𝔸(ν; Spec (.of K))) := fun w =>
    hZ.inter (IsClosed.isConstructible ((hclosed w).preimage (polyMapEquiv F).1.continuous))
  have hfibpts : ∀ w : κ → K,
      {x : ν → K | (ptEquiv K x : 𝔸(ν; Spec (.of K))) ∈
          (Z ∩ (polyMapEquiv F).1 ⁻¹' {(ptEquiv K w : 𝔸(κ; Spec (.of K)))})} =
        {x : ν → K | (ptEquiv K x : 𝔸(ν; Spec (.of K))) ∈ Z} ∩
          (fun (x : ν → K) (j : κ) => MvPolynomial.aeval x (F j)) ⁻¹' {w} := by
    intro w
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
      polyMapEquiv_pt]
    exact and_congr_right fun _ => ⟨fun h => pt_injective h,
      fun h => congrArg (fun z : κ → K => (ptEquiv K z : 𝔸(κ; Spec (.of K)))) h⟩
  refine le_trans (le_of_eq (topologicalKrullDim_eq_affineDim hZ).symm) ?_
  refine le_trans (topologicalKrullDim_le_image_add_iSup_fibre (polyMapEquiv F) hZ) ?_
  rw [topologicalKrullDim_closure himg, topologicalKrullDim_eq_affineDim himg,
    ← pts_image_polyMapEquiv F hZ]
  refine add_le_add le_rfl (iSup_le fun w => ?_)
  rw [topologicalKrullDim_eq_affineDim (hfibc w), hfibpts w]
  exact hc w

end Orbit

/-! ### 5. Tangent spaces -/

section Tangent

variable {K : Type u} [Field K] {ι : Type u} [Fintype ι]

/-- **The embedding dimension of a scheme at a point**: the dimension of the Zariski
cotangent space `𝔪ₚ/𝔪ₚ²` of the stalk over its residue field.  Makes sense at every
point, rational or not. -/
noncomputable def tangentDim (X : Scheme.{u}) (p : X) : ℕ :=
  Module.finrank (IsLocalRing.ResidueField (X.presheaf.stalk p))
    (IsLocalRing.CotangentSpace (X.presheaf.stalk p))

/-- **The tangent bound**: for `I` prime, at a `K`-point the dimension of `V(I)` is at
most the embedding dimension (`ringKrullDim_le_finrank_cotangentSpace` at the stalk;
a `K`-point is closed, so the local dimension is the global one). -/
theorem topologicalKrullDim_le_tangentDim {I : Ideal (MvPolynomial ι K)} [I.IsPrime]
    (x : ι → K) (p : Vsch I) (hp : Vι I p = (ptEquiv K x : 𝔸(ι; Spec (.of K)))) :
    topologicalKrullDim (Vsch I) ≤ (tangentDim (Vsch I) p : WithBot ℕ∞) := by
  have hmax : ((VschHomeo I) p).asIdeal.IsMaximal :=
    isMaximal_of_isClosed (isClosed_singleton_of_pt hp)
  have _ : Algebra.FiniteType K (MvPolynomial ι K ⧸ I) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K I) Ideal.Quotient.mk_surjective
  calc topologicalKrullDim (Vsch I)
      = ringKrullDim (MvPolynomial ι K ⧸ I) := topologicalKrullDim_Vsch I
    _ = (((VschHomeo I p).asIdeal.height : ℕ∞) : WithBot ℕ∞) :=
        (height_eq_ringKrullDim_of_isMaximal (K := K) _ _).symm
    _ = ringKrullDim ((Vsch I).presheaf.stalk p) := (ringKrullDim_stalk_Vsch I p).symm
    _ ≤ (tangentDim (Vsch I) p : WithBot ℕ∞) := ringKrullDim_le_finrank_cotangentSpace _

/-- At a `K`-point the embedding dimension is the dimension of the Jacobian kernel. -/
theorem tangentDim_eq_finrank_jacobianKernel {I : Ideal (MvPolynomial ι K)}
    (x : ι → K) (p : Vsch I) (hp : Vι I p = (ptEquiv K x : 𝔸(ι; Spec (.of K)))) :
    tangentDim (Vsch I) p = Module.finrank K (jacobianKernel I x) := by
  -- `I` vanishes at `x`
  have hI : I ≤ Tangent.pointIdeal x := by
    intro f hf
    rw [Tangent.mem_pointIdeal_iff]
    have hmem : (ptEquiv K x : 𝔸(ι; Spec (.of K))) ∈ V (I : Set (MvPolynomial ι K)) := by
      rw [← range_Vι]
      exact ⟨p, hp⟩
    simpa using (pt_mem_V_iff _ x).mp hmem f hf
  -- the prime of the `K`-point
  obtain ⟨q, hq⟩ := exists_point_VschSpecIso I p
  have hqI : q.asIdeal = (Tangent.pointIdeal x).map (Ideal.Quotient.mk I) := by
    rw [pointIdeal_eq_vanishingIdeal]
    exact asIdeal_eq_of_pt (by rw [hq]; exact hp)
  have hmax : q.asIdeal.IsMaximal := by
    rw [hqI]
    exact isMaximal_map_mk hI (Tangent.pointIdeal_isMaximal x)
  have _ : Nontrivial ((MvPolynomial ι K ⧸ I) ⧸ q.asIdeal) :=
    Ideal.Quotient.nontrivial_iff.mpr hmax.ne_top
  -- and the chain of identifications
  rw [show p = (VschSpecIso I).hom q from hq.symm, tangentDim,
    finrank_cotangentSpace_stalk_Vsch I q hmax,
    Height.Toolbox.finrank_cotangent_eq_of_surjective (S := K) q.asIdeal
      (by rw [hqI]; exact algebraMap_quotient_surjective I x), hqI,
    finrank_cotangent_eq_finrank_jacobianKernel I x hI]

/-- **Generic regularity**: for `I` prime over an algebraically closed field the regular locus
of `V(I)` contains a dense open subset — the statement at *every* point of that open set, not
only at its closed points.

`Tangent/Dense.exists_jacobian_witness` gives `c = n − dim` elements `f₁, …, f_c` of `I` whose
`c × c` Jacobian minor `g` is not in `I`; the principal open `D g` of `V(I)` is nonempty,
hence dense because `V(I)` is irreducible.  Each of its points is a prime `q ⊇ I` with
`g ∉ q`, and there the Jacobian criterion at a prime
(`Tangent.isRegularLocalRing_quotient_map_of_notMem_det`) makes `K[ι]_q ⧸ (f₁, …, f_c)` a
regular local ring of dimension `height q − c`.  The stalk of `V(I)` at that point is
`K[ι]_q ⧸ I K[ι]_q`, of the same dimension
(`Tangent.ringKrullDim_quotient_map_atPrime_add_height` and `height I = c`); both rings are
domains, so the surjection between them is injective (`injective_of_ringKrullDim_eq`), the two
ideals agree, and the stalk is regular.

Serre's theorem — a localisation of a regular local ring is regular — is not used anywhere:
the Jacobian criterion is applied at each prime of the open set directly. -/
theorem generic_isRegularLocalRing [IsAlgClosed K] {I : Ideal (MvPolynomial ι K)}
    [I.IsPrime] :
    Generic (Set.univ : Set (Vsch I)) fun p =>
      IsRegularLocalRing ((Vsch I).presheaf.stalk p) := by
  classical
  obtain ⟨c, d, hcd, hht, hdim⟩ := exists_ringKrullDim_quotient_eq K ι I
  obtain ⟨f, S, hfI, hdet⟩ := Tangent.exists_jacobian_witness I
    (by rw [← Nat.card_eq_fintype_card]; exact hcd) hdim
  set g : MvPolynomial ι K := (Matrix.of fun j k => MvPolynomial.pderiv (S k) (f j)).det with hg
  have hdomI : IsDomain (MvPolynomial ι K ⧸ I) := (Ideal.Quotient.isDomain_iff_prime I).mpr ‹_›
  set U : Set (Vsch I) := VschHomeo I ⁻¹' (PrimeSpectrum.basicOpen (Ideal.Quotient.mk I g) :
    Set (PrimeSpectrum (MvPolynomial ι K ⧸ I))) with hU
  have hUopen : IsOpen U := PrimeSpectrum.isOpen_basicOpen.preimage (VschHomeo I).continuous
  have hUne : (U ∩ (Set.univ : Set (Vsch I))).Nonempty := by
    refine ⟨(VschHomeo I).symm ⟨⊥, Ideal.isPrime_bot⟩, ?_, trivial⟩
    rw [hU, Set.mem_preimage, Homeomorph.apply_symm_apply]
    show Ideal.Quotient.mk I g ∉ (⊥ : Ideal (MvPolynomial ι K ⧸ I))
    rw [Ideal.mem_bot]
    exact fun h => hdet (Ideal.Quotient.eq_zero_iff_mem.mp h)
  refine Generic.of_isIrreducible (IrreducibleSpace.isIrreducible_univ (Vsch I)) U hUopen
    hUne ?_
  rintro p ⟨hpU, -⟩
  -- the prime of `p` in `K[ι]`
  obtain ⟨qq, hqq⟩ := exists_point_VschSpecIso I p
  have _ : qq.asIdeal.IsPrime := qq.isPrime
  have hqqV : VschHomeo I p = qq := by rw [← hqq, VschHomeo_VschSpecIso_hom]
  set q : Ideal (MvPolynomial ι K) := Ideal.comap (Ideal.Quotient.mk I) qq.asIdeal with hq
  have hqp : q.IsPrime := Ideal.IsPrime.comap _
  have hIq : I ≤ q := fun y hy => by
    rw [hq, Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hy]
    exact Ideal.zero_mem _
  have hqmap : q.map (Ideal.Quotient.mk I) = qq.asIdeal := by
    rw [hq, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
  have hgq : g ∉ q := by
    rw [hq, Ideal.mem_comap]
    rw [hU, Set.mem_preimage, hqqV] at hpU
    exact (PrimeSpectrum.mem_basicOpen _ _).mp hpU
  -- the Jacobian criterion at `q`
  obtain ⟨hregJ, hdimJ⟩ := Tangent.isRegularLocalRing_quotient_map_of_notMem_det q
    (fun j => hIq (hfI j)) S hgq
  have hdimI2 := Tangent.ringKrullDim_quotient_map_atPrime_add_height (p := I) (q := q) hIq
  rw [hht] at hdimI2
  obtain ⟨hq', hhq'⟩ : ∃ n : ℕ, q.height = (n : ℕ∞) :=
    ⟨_, (ENat.natCast_toNat (Ideal.height_ne_top hqp.ne_top)).symm⟩
  rw [hhq'] at hdimJ hdimI2
  have hcast : ((hq' : ℕ∞) : WithBot ℕ∞) = ((hq' : ℕ) : WithBot ℕ∞) := by norm_cast
  rw [hcast] at hdimJ hdimI2
  -- the two quotients are domains of the same dimension
  have hIA : (I.map (algebraMap (MvPolynomial ι K) (Localization.AtPrime q))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl _ I ‹_›
      (Set.disjoint_left.mpr fun a ha hb => ha (hIq hb))
  have hdomIA : IsDomain (Localization.AtPrime q ⧸
      I.map (algebraMap (MvPolynomial ι K) (Localization.AtPrime q))) :=
    (Ideal.Quotient.isDomain_iff_prime _).mpr hIA
  have hdomJA : IsDomain (Localization.AtPrime q ⧸ (Ideal.span (Set.range f)).map
      (algebraMap (MvPolynomial ι K) (Localization.AtPrime q))) :=
    Height.Toolbox.isDomain_of_isRegularLocalRing (Localization.AtPrime q ⧸
      (Ideal.span (Set.range f)).map
        (algebraMap (MvPolynomial ι K) (Localization.AtPrime q)))
  have hmJ := ringKrullDim_eq_of_add_eq (B := Localization.AtPrime q ⧸
    (Ideal.span (Set.range f)).map
      (algebraMap (MvPolynomial ι K) (Localization.AtPrime q))) hdimJ
  have hmI := ringKrullDim_eq_of_add_eq (B := Localization.AtPrime q ⧸
    I.map (algebraMap (MvPolynomial ι K) (Localization.AtPrime q))) hdimI2
  -- the surjection of the two quotients is injective, so the two ideals agree
  have hJI : (Ideal.span (Set.range f)) ≤ I :=
    Ideal.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hfI j)
  have hmapJI : (Ideal.span (Set.range f)).map
        (algebraMap (MvPolynomial ι K) (Localization.AtPrime q))
      ≤ I.map (algebraMap (MvPolynomial ι K) (Localization.AtPrime q)) := Ideal.map_mono hJI
  have hlift : ∀ a ∈ (Ideal.span (Set.range f)).map
      (algebraMap (MvPolynomial ι K) (Localization.AtPrime q)),
      (Ideal.Quotient.mk (I.map (algebraMap (MvPolynomial ι K) (Localization.AtPrime q)))) a
        = 0 := fun a ha => Ideal.Quotient.eq_zero_iff_mem.mpr (hmapJI ha)
  have hgsurj : Function.Surjective (Ideal.Quotient.lift _ _ hlift) := by
    intro y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Ideal.Quotient.mk _ a, rfl⟩
  have hginj : Function.Injective (Ideal.Quotient.lift _ _ hlift) :=
    injective_of_ringKrullDim_eq hmJ hmI _ hgsurj
  have hmapIJ : I.map (algebraMap (MvPolynomial ι K) (Localization.AtPrime q))
      ≤ (Ideal.span (Set.range f)).map
        (algebraMap (MvPolynomial ι K) (Localization.AtPrime q)) := by
    intro y hy
    refine Ideal.Quotient.eq_zero_iff_mem.mp (hginj ?_)
    show (Ideal.Quotient.mk (I.map (algebraMap (MvPolynomial ι K) (Localization.AtPrime q)))) y
      = _
    rw [map_zero, Ideal.Quotient.eq_zero_iff_mem.mpr hy]
  -- transport regularity to the stalk
  have hIJ : I.map (algebraMap (MvPolynomial ι K) (Localization.AtPrime q))
      = (Ideal.span (Set.range f)).map
        (algebraMap (MvPolynomial ι K) (Localization.AtPrime q)) :=
    le_antisymm hmapIJ hmapJI
  have hreg1 : IsRegularLocalRing (Localization.AtPrime q ⧸
      I.map (algebraMap (MvPolynomial ι K) (Localization.AtPrime q))) := by
    rw [hIJ]; exact hregJ
  have _ : (q.map (Ideal.Quotient.mk I)).IsPrime := Height.Toolbox.isPrime_map_mk hIq
  have hreg2 : IsRegularLocalRing (Localization.AtPrime (q.map (Ideal.Quotient.mk I))) :=
    IsRegularLocalRing.of_ringEquiv (Height.Toolbox.quotientLocalizationEquiv hIq).symm
  have _ : qq.asIdeal.IsPrime := qq.isPrime
  have hreg3 : IsRegularLocalRing (Localization.AtPrime qq.asIdeal) :=
    Height.Toolbox.isRegularLocalRing_atPrime_of_eq hqmap hreg2
  have hstalk : IsRegularLocalRing ((Vsch I).presheaf.stalk ((VschSpecIso I).hom qq)) :=
    IsRegularLocalRing.of_ringEquiv (R := Localization.AtPrime qq.asIdeal)
      (stalkVschRingEquiv I qq).symm
  rwa [hqq] at hstalk

end Tangent

/-! ### 6. Arcs -/

section Arcs

variable {K : Type u} [Field K] {ι : Type u} [Fintype ι]

omit [Fintype ι] in
/-- A `K`-point of `Vsch I` is a zero of `I`. -/
private theorem eval_eq_zero_of_Vι {I : Ideal (MvPolynomial ι K)} {x : ι → K}
    (p : Vsch I) (hp : Vι I p = (ptEquiv K x : 𝔸(ι; Spec (.of K)))) :
    ∀ f ∈ I, MvPolynomial.eval x f = 0 := by
  intro f hf
  have hmem : (ptEquiv K x : 𝔸(ι; Spec (.of K))) ∈ V (I : Set (MvPolynomial ι K)) := by
    rw [← range_Vι]
    exact ⟨p, hp⟩
  simpa using (pt_mem_V_iff _ x).mp hmem f hf

/-- **Tangent vectors at regular `K`-points are velocities.**  Route, no Cohen: at a
regular `K`-point `x` of `V(I)` the differentials of `I` span a space of dimension
`c = n − dim` (`tangentDim_eq_finrank_jacobianKernel`), so `c` elements of `I` have an
invertible `c × c` minor at `x`; Newton iteration (`Geometry/Tangent/Newton.lean`,
`exists_arc_of_jacobian_unit`) lifts `t` to an arc in `V(f₁, …, f_c)`; the local ring of
`V(f)` at `x` has dimension `≥ n − c` and embedding dimension `≤ n − c`, so it is regular,
hence a domain (`Toolbox`: regular local rings are domains), so `(f) = I` locally at `x`
and the arc lies in `V(I)` (`Geometry/Tangent/ArcOfTangent.lean`). -/
theorem exists_arc_of_tangentVec {I : Ideal (MvPolynomial ι K)} {x : ι → K}
    (p : Vsch I) (hp : Vι I p = (ptEquiv K x : 𝔸(ι; Spec (.of K))))
    (hreg : IsRegularLocalRing ((Vsch I).presheaf.stalk p)) (t : TangentVec I x) :
    ∃ a : Arc I, a.velHom = t.hom := by
  -- `I` vanishes at `x`
  have hx := eval_eq_zero_of_Vι p hp
  have hI : I ≤ Tangent.pointIdeal x := fun f hf => Tangent.mem_pointIdeal_iff.mpr (hx f hf)
  -- the stalk is the local ring of the coordinate ring at the point
  obtain ⟨q, hq⟩ := exists_point_VschSpecIso I p
  have hqI : q.asIdeal = (Tangent.pointIdeal x).map (Ideal.Quotient.mk I) := by
    rw [pointIdeal_eq_vanishingIdeal]
    exact asIdeal_eq_of_pt (by rw [hq]; exact hp)
  have _ : q.asIdeal.IsPrime := q.isPrime
  have _ : IsRegularLocalRing ((Vsch I).presheaf.stalk ((VschSpecIso I).hom q)) := by
    rw [hq]; exact hreg
  have _ : IsRegularLocalRing (Localization.AtPrime q.asIdeal) :=
    IsRegularLocalRing.of_ringEquiv (stalkVschRingEquiv I q)
  have _ : ((Tangent.pointIdeal x).map (Ideal.Quotient.mk I)).IsPrime := hqI ▸ q.isPrime
  have _ : IsRegularLocalRing (Localization.AtPrime
      ((Tangent.pointIdeal x).map (Ideal.Quotient.mk I))) :=
    Height.Toolbox.isRegularLocalRing_atPrime_of_eq hqI ‹_›
  have hreg' : IsRegularLocalRing (Localization.AtPrime (Tangent.pointIdeal x) ⧸
      I.map (algebraMap (MvPolynomial ι K) (Localization.AtPrime (Tangent.pointIdeal x)))) :=
    IsRegularLocalRing.of_ringEquiv
      (R := Localization.AtPrime ((Tangent.pointIdeal x).map (Ideal.Quotient.mk I)))
      (Height.Toolbox.quotientLocalizationEquiv hI)
  -- the arc, in coordinates
  obtain ⟨a, ha0, ha1, haI⟩ := exists_arc_of_regular_pt hI hreg'
    ((exists_tangentVec_iff hx t.vec).mp ⟨t, rfl⟩)
  obtain ⟨A, hA⟩ := (exists_arc_iff (I := I) a).mpr haI
  refine ⟨A, ?_⟩
  have hbase : A.base = x := by funext i; rw [Arc.base, hA]; exact ha0 i
  have hover := A.velHom_isOver
  have hvec : (⟨A.velHom, hover, by rw [A.velHom_restrict, hbase]⟩ :
      TangentVec I x).vec = t.vec := by
    funext i
    show ((ptEquiv K).symm ⟨A.velHom ≫ Vι I, hover⟩ i).snd = t.vec i
    rw [A.snd_coords_velHom hover i, hA]
    exact ha1 i
  exact congrArg TangentVec.hom (TangentVec.vec_injective I x hvec)

/-- Hence at a regular `K`-point the velocities fill the Jacobian kernel. -/
theorem exists_arc_of_mem_jacobianKernel {I : Ideal (MvPolynomial ι K)} {x : ι → K}
    (p : Vsch I) (hp : Vι I p = (ptEquiv K x : 𝔸(ι; Spec (.of K))))
    (hreg : IsRegularLocalRing ((Vsch I).presheaf.stalk p)) {v : ι → K}
    (hv : v ∈ jacobianKernel I x) :
    ∃ a : Arc I, a.base = x ∧ ∀ i, PowerSeries.coeff 1 (a.coords i) = v i := by
  have hx := eval_eq_zero_of_Vι p hp
  obtain ⟨t, htv⟩ := (exists_tangentVec_iff hx v).mpr hv
  obtain ⟨a, ha⟩ := exists_arc_of_tangentVec p hp hreg t
  have hbase : a.base = x := by
    refine (ptEquiv K).injective (Subtype.ext ?_)
    rw [← a.velHom_restrict, ha, t.restrict]
  refine ⟨a, hbase, fun i => ?_⟩
  have hsub : (⟨a.velHom ≫ Vι I, a.velHom_isOver⟩ : Pt K ι (DualNumber K))
      = ⟨t.hom ≫ Vι I, t.isOver⟩ := Subtype.ext (congrArg (fun h => h ≫ Vι I) ha)
  rw [← a.snd_coords_velHom a.velHom_isOver i, hsub, ← htv]
  rfl

end Arcs

end Height.Geometry
