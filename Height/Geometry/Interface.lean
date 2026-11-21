import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.RingTheory.Spectrum.Prime.Chevalley
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Funext
import Height.Toolbox.Topology
import Height.Geometry.Dimension.Affine
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Height.Toolbox.DualNumber
import Height.Toolbox.AffineAlgebra
import Height.Toolbox.SpectrumDim
import Height.Geometry.Dimension.LocClosed
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod

/-!
# The classical interface to `𝔸(ι; Spec K)`

The statements of the development are scheme-theoretic and live in
`Geometry/Spec.lean`.  This file is how they are *proved* and *used*: it says
what each scheme notion is in terms of tuples and polynomials, as
representation, induction and extensionality principles.  It is the only place
the passage between the two worlds happens.

* **Representation.**  For a `K`-algebra `A`, the `A`-points of `𝔸(ι; Spec K)`
  — `K`-morphisms `Spec A ⟶ 𝔸(ι; Spec K)` — are the tuples `ι → A`
  (`ptEquiv`, from `AffineSpace.homOverEquiv`).  `A = K` gives the `K`-points,
  `A = K⟦u⟧` the arcs, `A = K[ε]` the tangent vectors.  Global functions are
  polynomials (`regularEquiv`) and morphisms over `Spec K` between affine spaces
  are tuples of polynomials (`polyMapEquiv`); both are equivalences, and the
  facts "`X i` is the `i`-th coordinate function", "a polynomial map evaluates
  the coordinate polynomials at `K`-points" are their characterisations.
* **Constructors.**  `V s` and `D f`, the vanishing locus and basic open of
  regular functions, with their `K`-points computed.
* **Induction.**  Every closed set is a `V (I : Set (MvPolynomial ι K))`; every constructible set is built
  from `V`'s by complement and finite intersection.
* **Extensionality.**  Over an algebraically closed field, closed and
  constructible sets are determined by their `K`-points (Jacobson); over an
  infinite field, morphisms over `Spec K` are determined by their values on
  `K`-points.
* **Transfer.**  Dimension of a constructible set is `affineDim` of its
  `K`-points; `Generic (V P)` is the `∃ h ∉ P` form; `V (I : Set (MvPolynomial ι K))` has the Krull
  dimension of `K[ι] ⧸ I`; the tangent vectors at a `K`-point of `V (I : Set (MvPolynomial ι K))` are the
  Jacobian kernel; `specIso` is the bridge to `Spec K[ι]`.

Universe: `Scheme.{u}` puts `K`, `ι` and the base in one universe, so
everything is stated for `K ι : Type u`; consumers are at `u = 0`.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Height.Toolbox

namespace Height.Geometry

universe u

/-! ### Representation -/

section Representation

variable (K : Type u) [Field K] (ι : Type u)

/-- The spectrum of a `K`-algebra lies over `Spec K`. -/
noncomputable instance (A : Type u) [CommRing A] [Algebra K A] :
    (Spec (.of A)).Over (Spec (.of K)) :=
  ⟨Spec.map (CommRingCat.ofHom (algebraMap K A))⟩

/-- The `A`-points of affine `ι`-space over `K`: `K`-morphisms `Spec A ⟶ 𝔸(ι; Spec K)`. -/
abbrev Pt (A : Type u) [CommRing A] [Algebra K A] : Type u :=
  {f : Spec (.of A) ⟶ 𝔸(ι; Spec (.of K)) // f.IsOver (Spec (.of K))}

variable {K ι}

variable (K) in
/-- **`A`-points are tuples** (`AffineSpace.homOverEquiv` and `Γ(Spec A, ⊤) ≅ A`).  The
base field is explicit because a tuple over `A` does not determine it. -/
noncomputable def ptEquiv {A : Type u} [CommRing A] [Algebra K A] : (ι → A) ≃ Pt K ι A :=
  (Equiv.piCongrRight fun _ =>
      (Scheme.ΓSpecIso (.of A)).symm.commRingCatIsoToRingEquiv.toEquiv).trans
    (AffineSpace.homOverEquiv (S := Spec (.of K)) (X := Spec (.of A)) (n := ι)).symm

/-- A `K`-point has an underlying point of `𝔸(ι; Spec K)`: the image of the point
of `Spec K`. -/
noncomputable instance : CoeOut (Pt K ι K) 𝔸(ι; Spec (.of K)) :=
  ⟨fun f => f.1 ((IsLocalRing.closedPoint K : PrimeSpectrum K) : Spec (.of K))⟩

variable (K ι)

/-- The isomorphism with the spectrum of the coordinate ring
(`AffineSpace.SpecIso`): the bridge to where mathlib states Chevalley,
`topologicalKrullDim = ringKrullDim`, components and generic points. -/
noncomputable def specIso : 𝔸(ι; Spec (.of K)) ≅ Spec (.of (MvPolynomial ι K)) :=
  AffineSpace.SpecIso ι (.of K)

/-- `specIso` as a homeomorphism onto the prime spectrum: the working form of `specIso`
for everything topological. -/
noncomputable def specHomeo : 𝔸(ι; Spec (.of K)) ≃ₜ PrimeSpectrum (MvPolynomial ι K) :=
  (specIso K ι).hom.homeomorph

variable {K ι}

/-- **Global functions are polynomials**: `Γ(𝔸(ι; Spec K), ⊤) ≅ K[ι]`, through
`specIso` and `Γ(Spec R, ⊤) ≅ R`. -/
noncomputable def regularEquiv : MvPolynomial ι K ≃+* Γ(𝔸(ι; Spec (.of K)), ⊤) :=
  ((Scheme.ΓSpecIso (.of (MvPolynomial ι K))).symm ≪≫
    Scheme.Γ.mapIso (specIso K ι).op).commRingCatIsoToRingEquiv

/-- The pointwise form of `Scheme.ΓSpecIso_inv_naturality` (mathlib has the arrow form only;
mathlib candidate `Scheme.ΓSpecIso_inv_naturality_apply`). -/
private theorem ΓSpecIso_inv_naturality_apply {R S : CommRingCat.{u}} (φ : R ⟶ S) (r : R) :
    (Spec.map φ).appTop ((Scheme.ΓSpecIso R).inv r) = (Scheme.ΓSpecIso S).inv (φ r) := by
  rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]

/-- A morphism `g : X ⟶ Spec K[ι]` is the one classified by the sections `v` as soon as it
is a morphism over `Spec K` (`ha`) with coordinates `v` (`hb`).  The transfer lemma behind
`ptEquiv_comp_specIso` and `polyMapEquiv_eq_specIso`. -/
private theorem homOfVector_comp_specIso_hom {X : Scheme.{u}} (p : X ⟶ Spec (.of K))
    (v : ι → Γ(X, ⊤)) (g : X ⟶ Spec (.of (MvPolynomial ι K)))
    (ha : g ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.C (σ := ι) (R := K))) = p)
    (hb : ∀ i, g.appTop ((Scheme.ΓSpecIso (.of (MvPolynomial ι K))).inv (MvPolynomial.X i)) = v i) :
    AffineSpace.homOfVector p v ≫ (specIso K ι).hom = g := by
  refine (Iso.eq_comp_inv (specIso K ι)).mp ?_
  refine AffineSpace.hom_ext ?_ ?_
  · rw [AffineSpace.homOfVector_over, Category.assoc, specIso, AffineSpace.SpecIso_inv_over, ha]
  · intro i
    rw [AffineSpace.homOfVector_appTop_coord, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      specIso, AffineSpace.SpecIso_inv_appTop_coord, hb]

/-- The `A`-point of coordinates `x`, read through `specIso`, is `Spec` of the evaluation
`K[ι] → A` at `x`. -/
theorem ptEquiv_comp_specIso {A : Type u} [CommRing A] [Algebra K A] (x : ι → A) :
    (ptEquiv K x).1 ≫ (specIso K ι).hom =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := K) x).toRingHom) := by
  refine homOfVector_comp_specIso_hom _ _ _ ?_ ?_
  · rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 1
    ext a
    simp
  · intro i
    rw [ΓSpecIso_inv_naturality_apply]
    simp only [ConcreteCategory.hom_ofHom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      MvPolynomial.aeval_X]
    rfl

variable (K ι)

/-- The morphisms `𝔸(ι; Spec K) ⟶ 𝔸(κ; Spec K)` over `Spec K`. -/
abbrev HomOver (κ : Type u) : Type u :=
  {f : 𝔸(ι; Spec (.of K)) ⟶ 𝔸(κ; Spec (.of K)) // f.IsOver (Spec (.of K))}

variable {K ι}

/-- **Morphisms over `Spec K` are tuples of polynomials**: the `j`-th coordinate of
the morphism is the regular function of the `j`-th polynomial. -/
noncomputable def polyMapEquiv {κ : Type u} : (κ → MvPolynomial ι K) ≃ HomOver K ι κ :=
  (Equiv.piCongrRight fun _ => regularEquiv.toEquiv).trans
    (AffineSpace.homOverEquiv (S := Spec (.of K)) (X := 𝔸(ι; Spec (.of K))) (n := κ)).symm

/-- The polynomial map of `F`, read through `specIso` on the target, is `Spec` of the
substitution `F`.  The arrow form behind `polyMapEquiv_pt` and `polyMapEquiv_eq_specIso`. -/
private theorem polyMapEquiv_comp_specIso {κ : Type u} (F : κ → MvPolynomial ι K) :
    (polyMapEquiv F).1 ≫ (specIso K κ).hom = (specIso K ι).hom ≫
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval F).toRingHom) := by
  refine homOfVector_comp_specIso_hom _ _ _ ?_ ?_
  · have h : (CommRingCat.ofHom (MvPolynomial.C (σ := κ) (R := K)) ≫
        CommRingCat.ofHom (MvPolynomial.aeval F).toRingHom) =
        CommRingCat.ofHom (MvPolynomial.C (σ := ι) (R := K)) := by
      rw [← CommRingCat.ofHom_comp]
      congr 1
      ext a
      simp
    rw [Category.assoc, ← Spec.map_comp, h, ← AffineSpace.SpecIso_inv_over (n := ι) (.of K),
      ← specIso, Iso.hom_inv_id_assoc]
  · intro j
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, ΓSpecIso_inv_naturality_apply]
    simp only [ConcreteCategory.hom_ofHom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      MvPolynomial.aeval_X]
    rfl

/-- A polynomial map evaluates its coordinate polynomials at a `K`-point. -/
theorem polyMapEquiv_pt {κ : Type u} (F : κ → MvPolynomial ι K) (x : ι → K) :
    (polyMapEquiv F).1 (ptEquiv K x : 𝔸(ι; Spec (.of K))) =
      (ptEquiv K fun j => MvPolynomial.aeval x (F j) : 𝔸(κ; Spec (.of K))) := by
  have key : (ptEquiv K x).1 ≫ (polyMapEquiv F).1 =
      (ptEquiv K fun j => MvPolynomial.aeval x (F j)).1 := by
    rw [← cancel_mono (specIso K κ).hom, Category.assoc, polyMapEquiv_comp_specIso,
      ← Category.assoc, ptEquiv_comp_specIso, ptEquiv_comp_specIso, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun p => MvPolynomial.comp_aeval_apply (f := F) (MvPolynomial.aeval x) p
  exact congrArg (fun f : Spec (.of K) ⟶ 𝔸(κ; Spec (.of K)) => f.base _) key

/-- Under `specIso`, a polynomial map is `Spec` of the substitution. -/
theorem polyMapEquiv_eq_specIso {κ : Type u} (F : κ → MvPolynomial ι K) :
    (polyMapEquiv F).1 = (specIso K ι).hom ≫
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval F).toRingHom) ≫ (specIso K κ).inv := by
  rw [← Category.assoc, Iso.eq_comp_inv]
  exact polyMapEquiv_comp_specIso F

/-- The topological form of `polyMapEquiv_eq_specIso`: through `specHomeo` a polynomial map
is the comap of the substitution.  This is how a statement about `HomOver K ι κ` becomes a
statement about `PrimeSpectrum.comap`, where mathlib has Chevalley. -/
theorem specHomeo_polyMapEquiv {κ : Type u} (F : κ → MvPolynomial ι K) (p : 𝔸(ι; Spec (.of K))) :
    specHomeo K κ ((polyMapEquiv F).1 p) =
      PrimeSpectrum.comap (MvPolynomial.aeval (R := K) F).toRingHom (specHomeo K ι p) :=
  congrArg (fun g : 𝔸(ι; Spec (.of K)) ⟶ Spec (.of (MvPolynomial κ K)) => g.base p)
    (polyMapEquiv_comp_specIso F)

/-- Substitution of polynomials is a ring map of finite presentation, so Chevalley
(`PrimeSpectrum.isConstructible_comap_image`) applies to it: `K[ι]` is finitely presented over
`K` and `K[κ]` is of finite type over `K`
(`RingHom.FinitePresentation.of_comp_finiteType`).  A mathlib candidate. -/
theorem finitePresentation_aeval [Finite ι] {κ : Type u} [Finite κ] (F : κ → MvPolynomial ι K) :
    ((MvPolynomial.aeval (R := K) F).toRingHom).FinitePresentation := by
  have hcomp : (MvPolynomial.aeval (R := K) F).toRingHom.comp
      (MvPolynomial.C : K →+* MvPolynomial κ K) = (MvPolynomial.C : K →+* MvPolynomial ι K) := by
    ext a
    simp
  refine RingHom.FinitePresentation.of_comp_finiteType MvPolynomial.C ?_ ?_
  · rw [hcomp,
      show (MvPolynomial.C : K →+* MvPolynomial ι K) = algebraMap K (MvPolynomial ι K) from rfl]
    exact RingHom.finitePresentation_algebraMap.mpr inferInstance
  · rw [show (MvPolynomial.C : K →+* MvPolynomial κ K) = algebraMap K (MvPolynomial κ K) from rfl]
    exact RingHom.finiteType_algebraMap.mpr inferInstance

end Representation

/-! ### Constructors and their `K`-points -/

section Constructors

variable {K : Type u} [Field K] {ι : Type u}

/-- The vanishing locus of a set of polynomials, as regular functions
(`Scheme.zeroLocus`). -/
noncomputable def V (s : Set (MvPolynomial ι K)) : Set 𝔸(ι; Spec (.of K)) :=
  (𝔸(ι; Spec (.of K))).zeroLocus (regularEquiv '' s)

/-- The basic open of a polynomial, as a regular function (`Scheme.basicOpen`). -/
noncomputable def D (f : MvPolynomial ι K) : Set 𝔸(ι; Spec (.of K)) :=
  ((𝔸(ι; Spec (.of K))).basicOpen (regularEquiv f) : Set 𝔸(ι; Spec (.of K)))

-- The two structural facts, `V_eq_specHomeo_preimage` and `D_eq_compl_V`, are stated first
-- because everything else in this section is a corollary of them.

/-- `V` is the prime-spectrum zero locus under `specHomeo`. -/
theorem V_eq_specHomeo_preimage (s : Set (MvPolynomial ι K)) :
    V s = specHomeo K ι ⁻¹'
      (PrimeSpectrum.zeroLocus s : Set (PrimeSpectrum (MvPolynomial ι K))) := by
  have h := AlgebraicGeometry.Scheme.preimage_zeroLocus (specIso K ι).hom (U := ⊤)
    ((Scheme.ΓSpecIso (.of (MvPolynomial ι K))).inv '' s)
  rw [Spec_zeroLocus_eq_zeroLocus, Set.image_image] at h
  exact h.symm

theorem D_eq_compl_V (f : MvPolynomial ι K) : D f = (V {f})ᶜ := by
  have h : V ({f} : Set (MvPolynomial ι K)) = (D f)ᶜ := by
    show 𝔸(ι; Spec (.of K)).zeroLocus (regularEquiv '' {f}) = _
    rw [Set.image_singleton, AlgebraicGeometry.Scheme.zeroLocus_singleton]
    rfl
  rw [h, compl_compl]

theorem pt_mem_V_iff (s : Set (MvPolynomial ι K)) (x : ι → K) :
    (ptEquiv K x : 𝔸(ι; Spec (.of K))) ∈ V s ↔ ∀ f ∈ s, MvPolynomial.aeval x f = 0 := by
  have h : (specIso K ι).hom (ptEquiv K x : 𝔸(ι; Spec (.of K))) =
      PrimeSpectrum.comap (MvPolynomial.aeval (R := K) x).toRingHom
        (IsLocalRing.closedPoint K) :=
    congrArg (fun f : Spec (.of K) ⟶ Spec (.of (MvPolynomial ι K)) =>
      f.base ((IsLocalRing.closedPoint K : PrimeSpectrum K) : Spec (.of K)))
      (ptEquiv_comp_specIso x)
  have key : (PrimeSpectrum.comap (MvPolynomial.aeval (R := K) x).toRingHom
      (IsLocalRing.closedPoint K)) ∈ PrimeSpectrum.zeroLocus s ↔
      ∀ f ∈ s, MvPolynomial.aeval x f = 0 := by
    rw [PrimeSpectrum.mem_zeroLocus]
    simp [Set.subset_def, IsLocalRing.closedPoint, IsLocalRing.maximalIdeal_eq_bot]
  rw [V_eq_specHomeo_preimage]
  show (specIso K ι).hom (ptEquiv K x : 𝔸(ι; Spec (.of K))) ∈
    (PrimeSpectrum.zeroLocus s : Set (PrimeSpectrum (MvPolynomial ι K))) ↔ _
  rw [h]
  exact key

theorem pt_mem_D_iff (f : MvPolynomial ι K) (x : ι → K) :
    (ptEquiv K x : 𝔸(ι; Spec (.of K))) ∈ D f ↔ MvPolynomial.aeval x f ≠ 0 := by
  rw [D_eq_compl_V, Set.mem_compl_iff, pt_mem_V_iff]
  simp

theorem isClosed_V (s : Set (MvPolynomial ι K)) : IsClosed (V s) :=
  AlgebraicGeometry.Scheme.zeroLocus_isClosed _ _

theorem isOpen_D (f : MvPolynomial ι K) : IsOpen (D f) :=
  (𝔸(ι; Spec (.of K)).basicOpen (regularEquiv f)).isOpen

/-- `V I` is irreducible exactly when the radical of `I` is prime (`V` only sees the
radical: the version with `I.IsPrime` on the right is false, e.g. `I = (X²)`; for prime
`I` use `Ideal.IsPrime.radical`). -/
theorem isIrreducible_V_iff (I : Ideal (MvPolynomial ι K)) :
    IsIrreducible (V (I : Set (MvPolynomial ι K))) ↔ I.radical.IsPrime := by
  have h1 : IsIrreducible (V (I : Set (MvPolynomial ι K))) ↔
      IsIrreducible (PrimeSpectrum.zeroLocus (I : Set (MvPolynomial ι K))) := by
    rw [V_eq_specHomeo_preimage]
    exact Homeomorph.isIrreducible_preimage_iff (specHomeo K ι) _
  exact h1.trans (PrimeSpectrum.isIrreducible_zeroLocus_iff I)

end Constructors

/-! ### Induction -/

section Induction

variable {K : Type u} [Field K] {ι : Type u}

/-- Every closed set is a vanishing locus. -/
theorem IsClosed.exists_V_eq {Z : Set 𝔸(ι; Spec (.of K))} (hZ : IsClosed Z) :
    ∃ I : Ideal (MvPolynomial ι K), Z = V (I : Set (MvPolynomial ι K)) := by
  have hW : IsClosed ((specHomeo K ι).symm ⁻¹' Z) :=
    hZ.preimage (specHomeo K ι).symm.continuous
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).mp hW
  refine ⟨I, ?_⟩
  rw [V_eq_specHomeo_preimage, ← hI, Set.preimage_preimage]
  simp

/-- Every closed set is constructible: `K[ι]` is Noetherian, so the complement of a vanishing
locus is retrocompact (`PrimeSpectrum.isRetrocompact_zeroLocus_compl_of_fg`).  `[Finite ι]` is
what makes `K[ι]` Noetherian. -/
theorem IsClosed.isConstructible [Finite ι] {Z : Set 𝔸(ι; Spec (.of K))} (hZ : IsClosed Z) :
    IsConstructible Z := by
  obtain ⟨I, rfl⟩ := IsClosed.exists_V_eq hZ
  rw [V_eq_specHomeo_preimage]
  refine Topology.IsConstructible.preimage_of_isOpenEmbedding (specHomeo K ι).isOpenEmbedding ?_
  refine Topology.IsConstructible.of_compl ?_
  exact (PrimeSpectrum.isRetrocompact_zeroLocus_compl_of_fg
    (IsNoetherian.noetherian I)).isConstructible (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl

/-- **Induction on closed sets**: to prove a property of every closed set, prove
it for the vanishing loci. -/
theorem IsClosed.induction {P : Set 𝔸(ι; Spec (.of K)) → Prop}
    (hV : ∀ I : Ideal (MvPolynomial ι K), P (V (I : Set (MvPolynomial ι K))))
    {Z : Set 𝔸(ι; Spec (.of K))} (hZ : IsClosed Z) : P Z := by
  obtain ⟨I, rfl⟩ := IsClosed.exists_V_eq hZ
  exact hV I

/-- **Induction on constructible sets**: they are generated from the vanishing
loci by complements and finite intersections. -/
theorem IsConstructible.induction {P : Set 𝔸(ι; Spec (.of K)) → Prop}
    (hV : ∀ I : Ideal (MvPolynomial ι K), P (V (I : Set (MvPolynomial ι K))))
    (hcompl : ∀ Z, P Z → P Zᶜ)
    (hinter : ∀ Z Z', P Z → P Z' → P (Z ∩ Z'))
    {Z : Set 𝔸(ι; Spec (.of K))} (hZ : IsConstructible Z) : P Z := by
  induction hZ using Topology.IsConstructible.empty_union_induction with
  | open_retrocompact U hU _ =>
    obtain ⟨I, hI⟩ := IsClosed.exists_V_eq hU.isClosed_compl
    have hU' : U = (V (I : Set (MvPolynomial ι K)))ᶜ := by rw [← hI, compl_compl]
    rw [hU']
    exact hcompl _ (hV I)
  | union s _ t _ hs' ht' =>
    have h : s ∪ t = (sᶜ ∩ tᶜ)ᶜ := by rw [← Set.compl_union, compl_compl]
    rw [h]
    exact hcompl _ (hinter _ _ (hcompl _ hs') (hcompl _ ht'))
  | compl s _ hs' => exact hcompl _ hs'

end Induction

/-! ### Extensionality: `K`-points determine everything -/

section Ext

variable {K : Type u} [Field K] {ι κ : Type u}

/-! #### The bridge to `Spec K[ι]`

The private lemmas of this block are the working form of `specHomeo` used by the
extensionality and transfer proofs. -/

private theorem V_radical (I : Ideal (MvPolynomial ι K)) :
    V (I.radical : Set (MvPolynomial ι K)) = V (I : Set (MvPolynomial ι K)) := by
  rw [V_eq_specHomeo_preimage, V_eq_specHomeo_preimage, PrimeSpectrum.zeroLocus_radical]

/-- The `i`-th coordinate function pulled back along the `A`-point of `a` is `a i`. -/
theorem ptEquiv_appTop_coord {A : Type u} [CommRing A] [Algebra K A] (a : ι → A) (i : ι) :
    (ptEquiv K a).1.appTop (AffineSpace.coord (Spec (.of K)) i) =
      (Scheme.ΓSpecIso (.of A)).inv (a i) := by
  simp [ptEquiv, Iso.commRingCatIsoToRingEquiv]

/-- Under `specIso`, the `K`-point of `x` is the maximal ideal of `x`. -/
theorem specHomeo_pt (x : ι → K) :
    specHomeo K ι (ptEquiv K x : 𝔸(ι; Spec (.of K))) = MvPolynomial.pointToPoint (k := K) x := by
  show ((ptEquiv K x).1 ≫ (specIso K ι).hom) _ = _
  rw [ptEquiv_comp_specIso]
  show PrimeSpectrum.comap (CommRingCat.ofHom
      (MvPolynomial.aeval x : MvPolynomial ι K →ₐ[K] K).toRingHom).hom
      (IsLocalRing.closedPoint K) = _
  refine PrimeSpectrum.ext ?_
  ext f
  show f ∈ Ideal.comap _ _ ↔ _
  simp [IsLocalRing.closedPoint, MvPolynomial.pointToPoint]

private theorem pts_V (I : Ideal (MvPolynomial ι K)) :
    {x : ι → K | (ptEquiv K x : 𝔸(ι; Spec (.of K))) ∈ V (I : Set (MvPolynomial ι K))} =
      MvPolynomial.zeroLocus K I := by
  ext x
  rw [Set.mem_ofPred_eq, pt_mem_V_iff, MvPolynomial.mem_zeroLocus_iff]
  exact ⟨fun h p hp => h p hp, fun h p hp => h p hp⟩

theorem pt_injective :
    Function.Injective (fun x : ι → K => (ptEquiv K x : 𝔸(ι; Spec (.of K)))) := by
  intro x y h
  have hi : MvPolynomial.vanishingIdeal K ({x} : Set (ι → K)) =
      MvPolynomial.vanishingIdeal K ({y} : Set (ι → K)) :=
    congrArg PrimeSpectrum.asIdeal
      (((specHomeo_pt x).symm.trans (congrArg (specHomeo K ι) h)).trans (specHomeo_pt y))
  funext i
  have hmem : (MvPolynomial.X i - MvPolynomial.C (y i) : MvPolynomial ι K) ∈
      MvPolynomial.vanishingIdeal K ({y} : Set (ι → K)) := by
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    simp
  have := (MvPolynomial.mem_vanishingIdeal_singleton_iff x _).1 (hi ▸ hmem)
  simpa [sub_eq_zero] using this

private theorem isClosed_singleton_iff (p : 𝔸(ι; Spec (.of K))) :
    IsClosed ({p} : Set 𝔸(ι; Spec (.of K))) ↔ (specHomeo K ι p).asIdeal.IsMaximal := by
  rw [← PrimeSpectrum.isClosed_singleton_iff_isMaximal, ← Set.image_singleton,
    (specHomeo K ι).isClosed_image]

/-- Over an algebraically closed field the `K`-points are exactly the closed points
(`MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton`).  `[Finite ι]` is necessary:
for `K = ℚ̄` and `ι = ℕ` the kernel of a surjection `K[ι] ↠ K(t)` is a closed point with
residue field `K(t)`, not a `K`-point.  `IsConstructible.ext_pt` needs no finiteness. -/
theorem range_pt [IsAlgClosed K] [Finite ι] :
    Set.range (fun x : ι → K => (ptEquiv K x : 𝔸(ι; Spec (.of K)))) =
      {p : 𝔸(ι; Spec (.of K)) | IsClosed ({p} : Set 𝔸(ι; Spec (.of K)))} := by
  ext p
  simp only [Set.mem_range, Set.mem_ofPred_eq, isClosed_singleton_iff,
    MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, congrArg PrimeSpectrum.asIdeal (specHomeo_pt x)⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, (specHomeo K ι).injective ((specHomeo_pt x).trans (PrimeSpectrum.ext hx.symm))⟩

/-- Closed points are dense in every closed set (`K[ι]` is Jacobson): the closure
of a set of `K`-points is the vanishing locus of its vanishing ideal. -/
theorem closure_pt_image (S : Set (ι → K)) :
    closure ((fun x : ι → K => (ptEquiv K x : 𝔸(ι; Spec (.of K)))) '' S) =
      V (MvPolynomial.vanishingIdeal K S : Set (MvPolynomial ι K)) := by
  refine (Set.image_injective.2 (specHomeo K ι).injective) ?_
  rw [(specHomeo K ι).image_closure, ← Set.image_comp]
  have himg : (specHomeo K ι ∘ fun x : ι → K => (ptEquiv K x : 𝔸(ι; Spec (.of K)))) '' S =
      MvPolynomial.pointToPoint (k := K) '' S :=
    Set.image_congr fun x _ => specHomeo_pt x
  rw [himg, V_eq_specHomeo_preimage, Set.image_preimage_eq _ (specHomeo K ι).surjective,
    ← MvPolynomial.vanishingIdeal_pointToPoint (k := K) S,
    PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]

private theorem isClosed_eq_closure_pt [IsAlgClosed K] [Finite ι]
    {Z : Set 𝔸(ι; Spec (.of K))} (hZ : IsClosed Z) :
    Z = closure ((fun x : ι → K => (ptEquiv K x : 𝔸(ι; Spec (.of K)))) ''
      {x : ι → K | (ptEquiv K x : 𝔸(ι; Spec (.of K))) ∈ Z}) := by
  obtain ⟨I, rfl⟩ := IsClosed.exists_V_eq hZ
  rw [pts_V, closure_pt_image, MvPolynomial.vanishingIdeal_zeroLocus_eq_radical, V_radical]

/-- Two closed sets with the same `K`-points are equal.  `[Finite ι]` is necessary (the
closed point of `range_pt`'s example and `∅` have the same `K`-points). -/
theorem IsClosed.ext_pt [IsAlgClosed K] [Finite ι] {Z Z' : Set 𝔸(ι; Spec (.of K))}
    (hZ : IsClosed Z) (hZ' : IsClosed Z')
    (h : ∀ x : ι → K, (ptEquiv K x : 𝔸(ι; Spec (.of K))) ∈ Z ↔ (ptEquiv K x : 𝔸(ι; Spec (.of K))) ∈ Z') :
    Z = Z' := by
  rw [isClosed_eq_closure_pt hZ, isClosed_eq_closure_pt hZ']
  congr 2
  ext x
  simpa using h x

/-- Finitely many polynomials in arbitrarily many variables involve only finitely many
variables, so the Nullstellensatz applies to them: if a prime contains `g` but not `f`,
then some `K`-point does the same. -/
private theorem exists_sol_of_notMem_prime [IsAlgClosed K] {n : ℕ}
    (g : Fin n → MvPolynomial ι K) (f : MvPolynomial ι K)
    (p : PrimeSpectrum (MvPolynomial ι K))
    (hg : ∀ i, g i ∈ p.asIdeal) (hf : f ∉ p.asIdeal) :
    ∃ x : ι → K, (∀ i, MvPolynomial.aeval x (g i) = 0) ∧ MvPolynomial.aeval x f ≠ 0 := by
  classical
  set s : Finset ι := f.vars ∪ Finset.univ.biUnion fun i => (g i).vars with hs
  have hrange : Set.range (Subtype.val : {i // i ∈ s} → ι) = (↑s : Set ι) := by simp
  have hsub : ∀ q : MvPolynomial ι K, q.vars ⊆ s →
      ∃ q' : MvPolynomial {i // i ∈ s} K, MvPolynomial.rename Subtype.val q' = q := by
    intro q hq
    refine MvPolynomial.exists_rename_eq_of_vars_subset_range q _ Subtype.val_injective ?_
    rw [hrange]
    exact_mod_cast hq
  obtain ⟨f', hf'⟩ := hsub f (by rw [hs]; exact Finset.subset_union_left)
  have hgmem : ∀ i, ∃ q' : MvPolynomial {i // i ∈ s} K,
      MvPolynomial.rename Subtype.val q' = g i := fun i =>
    hsub (g i) (by
      rw [hs]
      exact (Finset.subset_biUnion_of_mem (fun i => (g i).vars) (Finset.mem_univ i)).trans
        Finset.subset_union_right)
  choose g' hg' using hgmem
  by_contra hcon
  have hcon' : ∀ x : ι → K, (∀ i, MvPolynomial.aeval x (g i) = 0) →
      MvPolynomial.aeval x f = 0 := by
    intro x hx
    by_contra hne
    exact hcon ⟨x, hx, hne⟩
  have hnull : f' ∈ (Ideal.span (Set.range g')).radical := by
    rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := K)]
    intro y hy
    set x : ι → K := fun i => if h : i ∈ s then y ⟨i, h⟩ else 0 with hx
    have hxy : x ∘ (Subtype.val : {i // i ∈ s} → ι) = y := by
      funext i
      simp [hx, i.2]
    have hgx : ∀ i, MvPolynomial.aeval x (g i) = 0 := by
      intro i
      rw [← hg' i, MvPolynomial.aeval_rename, hxy]
      exact hy _ (Ideal.subset_span ⟨i, rfl⟩)
    have hfx := hcon' x hgx
    rwa [← hf', MvPolynomial.aeval_rename, hxy] at hfx
  obtain ⟨m, hm⟩ := hnull
  have hmap : f ^ m ∈ Ideal.span (Set.range g) := by
    have h1 : MvPolynomial.rename (R := K) (Subtype.val : {i // i ∈ s} → ι) (f' ^ m) ∈
        (Ideal.span (Set.range g')).map
          (MvPolynomial.rename (R := K) (Subtype.val : {i // i ∈ s} → ι)).toRingHom :=
      Ideal.mem_map_of_mem _ hm
    rw [Ideal.map_span] at h1
    have h2 : ⇑(MvPolynomial.rename (R := K) (Subtype.val : {i // i ∈ s} → ι)).toRingHom ''
        Set.range g' = Set.range g := by
      rw [← Set.range_comp]
      exact congrArg Set.range (funext hg')
    rw [h2] at h1
    rwa [map_pow, hf'] at h1
  exact hf (p.2.mem_of_pow_mem m (Ideal.span_le.2 (Set.range_subset_iff.2 hg) hmap))

/-- A nonempty constructible set has a `K`-point. -/
theorem exists_pt_of_isConstructible [IsAlgClosed K] {Z : Set 𝔸(ι; Spec (.of K))}
    (hZ : IsConstructible Z) (hne : Z.Nonempty) :
    ∃ x : ι → K, (ptEquiv K x : 𝔸(ι; Spec (.of K))) ∈ Z := by
  have himg : specHomeo K ι '' Z = (specHomeo K ι).symm ⁻¹' Z :=
    congrFun (Set.image_eq_preimage_of_inverse (specHomeo K ι).symm_apply_apply
      (specHomeo K ι).apply_symm_apply) Z
  have hZc : IsConstructible (specHomeo K ι '' Z) := by
    rw [himg]
    exact hZ.preimage_of_isOpenEmbedding (specHomeo K ι).symm.isOpenEmbedding
  obtain ⟨S, hS⟩ := PrimeSpectrum.exists_constructibleSetData_iff.mpr hZc
  obtain ⟨p, hp⟩ := hne.image (specHomeo K ι)
  rw [← hS, PrimeSpectrum.ConstructibleSetData.toSet, Set.mem_iUnion₂] at hp
  obtain ⟨C, hC, hpC⟩ := hp
  rw [PrimeSpectrum.BasicConstructibleSetData.toSet, Set.mem_sdiff,
    PrimeSpectrum.mem_zeroLocus, PrimeSpectrum.mem_zeroLocus] at hpC
  obtain ⟨x, hx1, hx2⟩ := exists_sol_of_notMem_prime C.g C.f p
    (fun i => hpC.1 ⟨i, rfl⟩) (fun hmem => hpC.2 (Set.singleton_subset_iff.2 hmem))
  have hmem : MvPolynomial.pointToPoint (k := K) x ∈ specHomeo K ι '' Z := by
    rw [← hS]
    refine Set.mem_iUnion₂.2 ⟨C, hC, ?_⟩
    rw [PrimeSpectrum.BasicConstructibleSetData.toSet, Set.mem_sdiff,
      PrimeSpectrum.mem_zeroLocus, PrimeSpectrum.mem_zeroLocus]
    refine ⟨Set.range_subset_iff.2 fun i => ?_, fun hcon => hx2 ?_⟩
    · exact (MvPolynomial.mem_vanishingIdeal_singleton_iff x _).2 (hx1 i)
    · exact (MvPolynomial.mem_vanishingIdeal_singleton_iff x _).1 (hcon (Set.mem_singleton _))
  obtain ⟨q, hq, hqe⟩ := hmem
  rw [← specHomeo_pt x] at hqe
  exact ⟨x, (specHomeo K ι).injective hqe ▸ hq⟩

/-- Two constructible sets with the same `K`-points are equal (Jacobson). -/
theorem IsConstructible.ext_pt [IsAlgClosed K] {Z Z' : Set 𝔸(ι; Spec (.of K))}
    (hZ : IsConstructible Z) (hZ' : IsConstructible Z')
    (h : ∀ x : ι → K, (ptEquiv K x : 𝔸(ι; Spec (.of K))) ∈ Z ↔ (ptEquiv K x : 𝔸(ι; Spec (.of K))) ∈ Z') :
    Z = Z' := by
  have key : ∀ W W' : Set 𝔸(ι; Spec (.of K)), IsConstructible W → IsConstructible W' →
      (∀ x : ι → K, (ptEquiv K x : 𝔸(ι; Spec (.of K))) ∈ W →
        (ptEquiv K x : 𝔸(ι; Spec (.of K))) ∈ W') → W ⊆ W' := by
    intro W W' hW hW' hh p hp
    by_contra hpn
    obtain ⟨x, hx⟩ := exists_pt_of_isConstructible (hW.sdiff hW') ⟨p, hp, hpn⟩
    exact hx.2 (hh x hx.1)
  exact Set.Subset.antisymm (key Z Z' hZ hZ' fun x => (h x).1)
    (key Z' Z hZ' hZ fun x => (h x).2)

private theorem ptEquiv_appTop_regularEquiv (x : ι → K) (h : MvPolynomial ι K) :
    (ptEquiv K x).1.appTop (regularEquiv h) =
      (Scheme.ΓSpecIso (.of K)).inv (MvPolynomial.aeval x h) := by
  have key : ((ptEquiv K x).1 ≫ (specIso K ι).hom).appTop
      ((Scheme.ΓSpecIso (.of (MvPolynomial ι K))).inv h) =
      (Scheme.ΓSpecIso (.of K)).inv (MvPolynomial.aeval x h) := by
    rw [ptEquiv_comp_specIso, ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality,
      CommRingCat.comp_apply]
    rfl
  exact key

private theorem appTop_coord (f : HomOver K ι κ) (j : κ) :
    f.1.appTop (AffineSpace.coord (Spec (.of K)) j) =
      regularEquiv ((polyMapEquiv (κ := κ)).symm f j) := by
  simp [polyMapEquiv]

/-- Private copy of `polyMapEquiv_pt`, in morphism form. -/
private theorem pt_comp_homOver (f : HomOver K ι κ) (x : ι → K) :
    (ptEquiv K x).1 ≫ f.1 =
      (ptEquiv K fun j => MvPolynomial.aeval x ((polyMapEquiv (κ := κ)).symm f j)).1 := by
  have hover : ((ptEquiv K x).1 ≫ f.1).IsOver (Spec (.of K)) := by
    constructor
    rw [Category.assoc, f.2.1, (ptEquiv K x).2.1]
  have key : (⟨(ptEquiv K x).1 ≫ f.1, hover⟩ : Pt K κ K) =
      ptEquiv K (fun j => MvPolynomial.aeval x ((polyMapEquiv (κ := κ)).symm f j)) := by
    apply (AffineSpace.homOverEquiv (S := Spec (.of K)) (X := Spec (.of K)) (n := κ)).injective
    funext j
    show ((ptEquiv K x).1 ≫ f.1).appTop (AffineSpace.coord _ j) =
      (ptEquiv K _).1.appTop (AffineSpace.coord _ j)
    rw [Scheme.Hom.comp_appTop]
    show (ptEquiv K x).1.appTop (f.1.appTop (AffineSpace.coord _ j)) = _
    rw [appTop_coord, ptEquiv_appTop_regularEquiv, ptEquiv_appTop_coord]
  exact congrArg Subtype.val key

/-- Two morphisms over `Spec K` that agree on `K`-points are equal (a polynomial
identity over an infinite field). -/
theorem HomOver.ext_pt [Infinite K] {f g : HomOver K ι κ}
    (h : ∀ x : ι → K, f.1 (ptEquiv K x : 𝔸(ι; Spec (.of K))) = g.1 (ptEquiv K x : 𝔸(ι; Spec (.of K)))) :
    f = g := by
  apply (polyMapEquiv (κ := κ) (ι := ι) (K := K)).symm.injective
  funext j
  refine MvPolynomial.funext fun x => ?_
  have hx : ((ptEquiv K x).1 ≫ f.1) (IsLocalRing.closedPoint K) =
      ((ptEquiv K x).1 ≫ g.1) (IsLocalRing.closedPoint K) := h x
  rw [pt_comp_homOver, pt_comp_homOver] at hx
  exact congrFun (pt_injective (ι := κ) hx) j

end Ext

/-! ### Transfer -/

section Transfer

variable {K : Type u} [Field K] {ι : Type u}

/-- The dimension of `V (I : Set (MvPolynomial ι K))` is the Krull dimension of the coordinate ring
(`PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim` through `specIso`). -/
theorem topologicalKrullDim_V (I : Ideal (MvPolynomial ι K)) :
    topologicalKrullDim (V (I : Set (MvPolynomial ι K))) =
      ringKrullDim (MvPolynomial ι K ⧸ I) := by
  have e1 : (V (I : Set (MvPolynomial ι K))) ≃ₜ
      (PrimeSpectrum.zeroLocus (I : Set (MvPolynomial ι K))) :=
    (Homeomorph.setCongr (V_eq_specHomeo_preimage (I : Set (MvPolynomial ι K)))).trans
      ((specHomeo K ι).isEmbedding.homeomorphOfSubsetRange (by simp))
  have hrange : Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) =
      PrimeSpectrum.zeroLocus (I : Set (MvPolynomial ι K)) := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
  have e2 : PrimeSpectrum (MvPolynomial ι K ⧸ I) ≃ₜ
      (PrimeSpectrum.zeroLocus (I : Set (MvPolynomial ι K))) :=
    (PrimeSpectrum.isClosedEmbedding_comap_of_surjective _ _
        Ideal.Quotient.mk_surjective).isEmbedding.toHomeomorph.trans
      (Homeomorph.setCongr hrange)
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := MvPolynomial ι K ⧸ I)]
  exact IsHomeomorph.topologicalKrullDim_eq _ (e1.trans e2.symm).isHomeomorph

/-- `topologicalKrullDim_eq_affineDim` for closed sets. -/
theorem topologicalKrullDim_eq_affineDim_of_isClosed [IsAlgClosed K] [Finite ι]
    {Z : Set 𝔸(ι; Spec (.of K))} (hZ : IsClosed Z) :
    topologicalKrullDim Z = affineDim {x : ι → K | (ptEquiv K x : 𝔸(ι; Spec (.of K))) ∈ Z} := by
  obtain ⟨I, rfl⟩ := IsClosed.exists_V_eq hZ
  rw [topologicalKrullDim_V, pts_V, affineDim_zeroLocus]

/-- **A constructible set is dense in the vanishing locus of the vanishing ideal of its
`K`-points**: over an algebraically closed field the `K`-points of a constructible set are
dense in it (Jacobson, i.e. `IsConstructible.ext_pt` applied to `Z \ closure (pts Z)`), and
`closure_pt_image` computes the closure of a set of `K`-points. -/
theorem closure_eq_V_vanishingIdeal_pt [IsAlgClosed K] [Finite ι]
    {Z : Set 𝔸(ι; Spec (.of K))} (hZ : IsConstructible Z) :
    closure Z =
      V (MvPolynomial.vanishingIdeal K
        {x : ι → K | (ptEquiv K x : 𝔸(ι; Spec (.of K))) ∈ Z} : Set (MvPolynomial ι K)) := by
  set S : Set (ι → K) := {x : ι → K | (ptEquiv K x : 𝔸(ι; Spec (.of K))) ∈ Z} with hS
  have hW : closure ((fun x : ι → K => (ptEquiv K x : 𝔸(ι; Spec (.of K)))) '' S) =
      V (MvPolynomial.vanishingIdeal K S : Set (MvPolynomial ι K)) := closure_pt_image S
  refine le_antisymm ?_ ?_
  · have hdiff : Z \ closure ((fun x : ι → K => (ptEquiv K x : 𝔸(ι; Spec (.of K)))) '' S) = ∅ := by
      refine IsConstructible.ext_pt (hZ.sdiff (IsClosed.isConstructible isClosed_closure))
        Topology.IsConstructible.empty fun x => ?_
      simp only [Set.mem_sdiff, Set.mem_empty_iff_false, iff_false, not_and, not_not]
      intro hx
      exact subset_closure ⟨x, hx, rfl⟩
    rw [← hW]
    exact closure_minimal (Set.sdiff_eq_empty.mp hdiff) isClosed_closure
  · rw [← hW]
    exact closure_mono (by rintro _ ⟨x, hx, rfl⟩; exact hx)

/-- **The dimension of the closure of a constructible set is computed on `K`-points.**  This is
the half of `topologicalKrullDim_eq_affineDim` that needs no dimension formula: `affineDim` is
by definition the dimension of a Zariski closure, so the two agree on closures, and
`topologicalKrullDim Z ≤ affineDim (pts Z)` follows by monotonicity.  The missing half,
`topologicalKrullDim Z = topologicalKrullDim (closure Z)`, is `Geometry/Spec.lean`'s
`topologicalKrullDim_closure`; it needs the dimension formula for affine algebras
(`Toolbox/AffineAlgebra.ringKrullDim_localization_away`). -/
theorem topologicalKrullDim_closure_eq_affineDim [IsAlgClosed K] [Finite ι]
    {Z : Set 𝔸(ι; Spec (.of K))} (hZ : IsConstructible Z) :
    topologicalKrullDim (closure Z) =
      affineDim {x : ι → K | (ptEquiv K x : 𝔸(ι; Spec (.of K))) ∈ Z} := by
  rw [closure_eq_V_vanishingIdeal_pt hZ, topologicalKrullDim_V]
  rfl

/-- **Dimension is computed on `K`-points**: for a constructible set, its Krull
dimension is the old `affineDim` of its `K`-points.  `[IsAlgClosed K]` is necessary
(`K = ℝ`, `Z = V {X² + 1}` is a point with no `K`-points).  The closed case is
`topologicalKrullDim_eq_affineDim_of_isClosed`; the constructible case reduces to
`dim Z = dim (closure Z)`, i.e. `ringKrullDim_localization_away` (`Toolbox/AffineAlgebra`). -/
theorem topologicalKrullDim_eq_affineDim [IsAlgClosed K] [Finite ι]
    {Z : Set 𝔸(ι; Spec (.of K))}
    (hZ : IsConstructible Z) :
    topologicalKrullDim Z = affineDim {x : ι → K | (ptEquiv K x : 𝔸(ι; Spec (.of K))) ∈ Z} := by
  rw [← topologicalKrullDim_closure_eq_affineDim hZ]
  have h := Height.Toolbox.topologicalKrullDim_closure_of_isConstructible K
    ((specHomeo K ι).isConstructible_image hZ)
  rw [← (specHomeo K ι).image_closure, topologicalKrullDim_image_of_isEmbedding (specHomeo K ι).isEmbedding,
    topologicalKrullDim_image_of_isEmbedding (specHomeo K ι).isEmbedding] at h
  exact h.symm

/-- The generic point of `V I` for a prime `I`. -/
private noncomputable def genericPt (I : Ideal (MvPolynomial ι K)) [I.IsPrime] :
    𝔸(ι; Spec (.of K)) :=
  (specHomeo K ι).symm ⟨I, inferInstance⟩

private theorem specHomeo_genericPt (I : Ideal (MvPolynomial ι K)) [I.IsPrime] :
    specHomeo K ι (genericPt I) = ⟨I, inferInstance⟩ :=
  (specHomeo K ι).apply_symm_apply _

private theorem closure_genericPt (I : Ideal (MvPolynomial ι K)) [I.IsPrime] :
    closure ({genericPt I} : Set 𝔸(ι; Spec (.of K))) = V (I : Set (MvPolynomial ι K)) := by
  refine (Set.image_injective.2 (specHomeo K ι).injective) ?_
  rw [(specHomeo K ι).image_closure, Set.image_singleton, specHomeo_genericPt,
    PrimeSpectrum.closure_singleton, V_eq_specHomeo_preimage,
    Set.image_preimage_eq _ (specHomeo K ι).surjective]

private theorem genericPt_mem_V (I : Ideal (MvPolynomial ι K)) [I.IsPrime] :
    genericPt I ∈ V (I : Set (MvPolynomial ι K)) := by
  rw [V_eq_specHomeo_preimage, Set.mem_preimage, specHomeo_genericPt]
  exact (PrimeSpectrum.mem_zeroLocus _ _).2 le_rfl

/-- **The generic quantifier at the `K`-points of `V(I)`**: a property of tuples
holds at every `K`-point of a dense open subset of `V(I)`, nothing being asserted
at the non-closed points.  This is the shape every "generically on `V`" statement
of the development has; `genericPts_iff` is its classical interface. -/
def GenericPts (I : Ideal (MvPolynomial ι K)) (P : (ι → K) → Prop) : Prop :=
  Generic (V (I : Set (MvPolynomial ι K)))
    fun p => ∀ x : ι → K, (ptEquiv K x : 𝔸(ι; Spec (.of K))) = p → P x

/-- **The generic quantifier on `V P`, for a property of `K`-points, is the
`∃ h ∉ P` form** the pencil files already use. -/
theorem generic_V_iff [IsAlgClosed K] {I : Ideal (MvPolynomial ι K)} [I.IsPrime]
    (P : (ι → K) → Prop) :
    Generic (V (I : Set (MvPolynomial ι K))) (fun p => ∀ x : ι → K, (ptEquiv K x : 𝔸(ι; Spec (.of K))) = p → P x) ↔
      ∃ h ∉ I, ∀ x ∈ MvPolynomial.zeroLocus K I, MvPolynomial.aeval x h ≠ 0 → P x := by
  have hmemU : ∀ (h : MvPolynomial ι K) (x : ι → K),
      (ptEquiv K x : 𝔸(ι; Spec (.of K))) ∈
        specHomeo K ι ⁻¹' (PrimeSpectrum.basicOpen h : Set (PrimeSpectrum (MvPolynomial ι K))) ↔
      MvPolynomial.aeval x h ≠ 0 := by
    intro h x
    rw [Set.mem_preimage, specHomeo_pt]
    show (MvPolynomial.pointToPoint (k := K) x) ∈ PrimeSpectrum.basicOpen h ↔ _
    rw [PrimeSpectrum.mem_basicOpen]
    exact not_congr (MvPolynomial.mem_vanishingIdeal_singleton_iff x h)
  constructor
  · rintro ⟨U, hUopen, hdense, hQ⟩
    have hpI : genericPt I ∈ U := by
      have hne : (U ∩ V (I : Set (MvPolynomial ι K))).Nonempty := by
        rcases Set.eq_empty_or_nonempty (U ∩ V (I : Set (MvPolynomial ι K))) with he | he
        · rw [he, closure_empty] at hdense
          exact absurd (hdense (genericPt_mem_V I)) (Set.notMem_empty _)
        · exact he
      obtain ⟨q, hqU, hqV⟩ := hne
      have hq : q ∈ closure ({genericPt I} : Set 𝔸(ι; Spec (.of K))) := by
        rw [closure_genericPt]; exact hqV
      obtain ⟨r, hrU, hr⟩ := (mem_closure_iff.1 hq) U hUopen hqU
      rw [Set.mem_singleton_iff] at hr
      exact hr ▸ hrU
    obtain ⟨-, ⟨h, rfl⟩, hIh, hsub⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
        (a := (⟨I, inferInstance⟩ : PrimeSpectrum (MvPolynomial ι K)))
        (u := specHomeo K ι '' U)
        ⟨genericPt I, hpI, specHomeo_genericPt I⟩ ((specHomeo K ι).isOpenMap _ hUopen)
    refine ⟨h, (PrimeSpectrum.mem_basicOpen _ _).1 hIh, fun x hx hxh => ?_⟩
    have hxV : (ptEquiv K x : 𝔸(ι; Spec (.of K))) ∈ V (I : Set (MvPolynomial ι K)) :=
      (pt_mem_V_iff _ x).2 fun f hf => hx f hf
    have hxU : (ptEquiv K x : 𝔸(ι; Spec (.of K))) ∈ U := by
      obtain ⟨p, hp, hpe⟩ := hsub ((hmemU h x).2 hxh)
      exact (specHomeo K ι).injective hpe ▸ hp
    exact hQ _ ⟨hxU, hxV⟩ x rfl
  · rintro ⟨h, hhI, hP⟩
    refine ⟨specHomeo K ι ⁻¹' (PrimeSpectrum.basicOpen h :
      Set (PrimeSpectrum (MvPolynomial ι K))), PrimeSpectrum.isOpen_basicOpen.preimage
        (specHomeo K ι).continuous, ?_, ?_⟩
    · have hsub : ({genericPt I} : Set 𝔸(ι; Spec (.of K))) ⊆
          (specHomeo K ι ⁻¹' (PrimeSpectrum.basicOpen h :
            Set (PrimeSpectrum (MvPolynomial ι K)))) ∩ V (I : Set (MvPolynomial ι K)) := by
        refine Set.singleton_subset_iff.2 ⟨?_, genericPt_mem_V I⟩
        rw [Set.mem_preimage, specHomeo_genericPt]
        show (⟨I, inferInstance⟩ : PrimeSpectrum (MvPolynomial ι K)) ∈ PrimeSpectrum.basicOpen h
        rw [PrimeSpectrum.mem_basicOpen]
        exact hhI
      exact (closure_genericPt I).symm.subset.trans (closure_mono hsub)
    · rintro p ⟨hpU, hpV⟩ x rfl
      exact hP x (fun f hf => (pt_mem_V_iff _ x).1 hpV f hf) ((hmemU h x).1 hpU)

/-- **`GenericPts` in the `∃ h ∉ I` form**: `generic_V_iff`, restated for the
`K`-point quantifier. -/
theorem genericPts_iff [IsAlgClosed K] {I : Ideal (MvPolynomial ι K)} [I.IsPrime]
    (P : (ι → K) → Prop) :
    GenericPts I P ↔
      ∃ h ∉ I, ∀ x ∈ MvPolynomial.zeroLocus K I, MvPolynomial.aeval x h ≠ 0 → P x :=
  generic_V_iff P

/-- **Base change of points**: a `K`-algebra map `φ : A → B` sends the `A`-point of
`a` to the `B`-point of `φ ∘ a`; this is how bases and velocities of arcs are
computed. -/
theorem ptEquiv_map {A B : Type u} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
    (φ : A →ₐ[K] B) (a : ι → A) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (ptEquiv K a).1 = (ptEquiv K fun i => φ (a i)).1 := by
  apply AffineSpace.hom_ext
  · rw [Category.assoc, (ptEquiv K a).2.1, (ptEquiv K fun i => φ (a i)).2.1]
    show Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 1
    ext x
    exact φ.commutes x
  · intro i
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, ptEquiv_appTop_coord,
      ptEquiv_appTop_coord, ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality,
      CommRingCat.comp_apply]
    rfl

end Transfer

/-! ### The closed subscheme `V(I)` -/

section Subscheme

variable {K : Type u} [Field K] {ι : Type u}

/-- The ideal sheaf on `𝔸(ι; Spec K)` generated by `I ⊆ K[ι]` (regular functions
through `regularEquiv`; mathlib's `IdealSheafData.ofIdealTop`). -/
noncomputable def idealSheaf (I : Ideal (MvPolynomial ι K)) : 𝔸(ι; Spec (.of K)).IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop (I.map (regularEquiv (K := K) (ι := ι)).toRingHom)

/-- **The closed subscheme `V(I)`**, with its closed immersion `Vι I` into `𝔸`. -/
noncomputable abbrev Vsch (I : Ideal (MvPolynomial ι K)) : Scheme := (idealSheaf I).subscheme

noncomputable abbrev Vι (I : Ideal (MvPolynomial ι K)) : Vsch I ⟶ 𝔸(ι; Spec (.of K)) :=
  (idealSheaf I).subschemeι

noncomputable instance (I : Ideal (MvPolynomial ι K)) : (Vsch I).Over (Spec (.of K)) :=
  ⟨Vι I ≫ 𝔸(ι; Spec (.of K)) ↘ Spec (.of K)⟩

/-- On an affine scheme `ofIdealTop` reflects the order (mathlib's Galois insertion
`IdealSheafData.equivOfIsAffine`; a mathlib candidate in this form). -/
private theorem ofIdealTop_le_ofIdealTop_iff {X : Scheme.{u}} [IsAffine X]
    (J J' : Ideal Γ(X, ⊤)) :
    Scheme.IdealSheafData.ofIdealTop J ≤ Scheme.IdealSheafData.ofIdealTop J' ↔ J ≤ J' := by
  rw [← map_le_map_iff (Scheme.IdealSheafData.equivOfIsAffine (X := X))]
  simp

/-- **A point evaluates the regular functions**: pulling the regular function of `f`
back along the `A`-point of `a` gives `aeval a f` in `Γ(Spec A, ⊤) ≅ A`.  This is
the heart of `exists_lift_Vι_iff`. -/
theorem Pt.appTop_regularEquiv {A : Type u} [CommRing A] [Algebra K A] (a : ι → A)
    (f : MvPolynomial ι K) :
    (ptEquiv K a).1.appTop (regularEquiv f) =
      (Scheme.ΓSpecIso (.of A)).inv (MvPolynomial.aeval a f) := by
  show (ptEquiv K a).1.appTop ((specIso K ι).hom.appTop
    ((Scheme.ΓSpecIso (.of (MvPolynomial ι K))).inv f)) = _
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, ptEquiv_comp_specIso,
    ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
  rfl

/-- A point is a solution of `f` exactly when `f` is in the kernel of its pullback. -/
theorem Pt.appTop_regularEquiv_eq_zero_iff {A : Type u} [CommRing A] [Algebra K A] (a : ι → A)
    (f : MvPolynomial ι K) :
    (ptEquiv K a).1.appTop (regularEquiv f) = 0 ↔ MvPolynomial.aeval a f = 0 := by
  rw [Pt.appTop_regularEquiv]
  refine ⟨fun h => ?_, fun h => by rw [h, map_zero]⟩
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of A)).hom
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv (MvPolynomial.aeval a f)) =
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom 0 := by rw [h]
  rwa [Iso.inv_hom_id_apply, map_zero] at h2

/-- The underlying set of `V(I)` is `V I`. -/
theorem range_Vι (I : Ideal (MvPolynomial ι K)) :
    Set.range (Vι I) = V (I : Set (MvPolynomial ι K)) := by
  rw [Scheme.IdealSheafData.range_subschemeι]
  simp [idealSheaf, V, Ideal.map, Scheme.zeroLocus_span]

/-- **The interface lemma for `V(I)`**: an `A`-point of `𝔸` factors through `V(I)`
exactly when its coordinates are an `A`-solution of `I`.  The factorisation is
unique since `Vι I` is a monomorphism.  With `A = K`, `K[ε]`, `K⟦u⟧` this computes
the points, tangent vectors and arcs of `V(I)`. -/
theorem exists_lift_Vι_iff {A : Type u} [CommRing A] [Algebra K A]
    (I : Ideal (MvPolynomial ι K)) (a : ι → A) :
    (∃ g : Spec (.of A) ⟶ Vsch I, g ≫ Vι I = (ptEquiv K a).1) ↔
      ∀ f ∈ I, MvPolynomial.aeval a f = 0 := by
  have key : idealSheaf I ≤ (ptEquiv K a).1.ker ↔ ∀ f ∈ I, MvPolynomial.aeval a f = 0 := by
    rw [Scheme.ker_of_isAffine, idealSheaf, ofIdealTop_le_ofIdealTop_iff,
      Ideal.map_le_iff_le_comap]
    exact ⟨fun h f hf => (Pt.appTop_regularEquiv_eq_zero_iff a f).mp
        (RingHom.mem_ker.mp (Ideal.mem_comap.mp (h hf))),
      fun h f hf => Ideal.mem_comap.mpr
        (RingHom.mem_ker.mpr ((Pt.appTop_regularEquiv_eq_zero_iff a f).mpr (h f hf)))⟩
  constructor
  · rintro ⟨g, hg⟩
    refine key.mp ?_
    calc idealSheaf I = (Vι I).ker := (Scheme.IdealSheafData.ker_subschemeι _).symm
      _ ≤ (g ≫ Vι I).ker := Scheme.Hom.le_ker_comp g (Vι I)
      _ = (ptEquiv K a).1.ker := by rw [hg]
  · intro h
    refine ⟨(ptEquiv K a).1.toImage ≫ Scheme.IdealSheafData.inclusion (key.mpr h), ?_⟩
    rw [Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι, Scheme.Hom.toImage_imageι]

end Subscheme

/-! ### Tangent vectors: `K[ε]`-points of `V(I)` -/

section Tangent

variable {K : Type u} [Field K] {ι : Type u}

/-- The closed point `Spec K ⟶ Spec K[ε]` (reduction `ε ↦ 0`). -/
noncomputable def epsZero (K : Type u) [Field K] : Spec (.of K) ⟶ Spec (.of (DualNumber K)) :=
  Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom)

/-- **A tangent vector to `V(I)` at the `K`-point `x`**: a `K[ε]`-point of `V(I)` over
`K` whose reduction is `x`. -/
structure TangentVec (I : Ideal (MvPolynomial ι K)) (x : ι → K) where
  /-- The dual-number point. -/
  hom : Spec (.of (DualNumber K)) ⟶ Vsch I
  isOver : (hom ≫ Vι I).IsOver (Spec (.of K))
  restrict : epsZero K ≫ hom ≫ Vι I = (ptEquiv K x).1

/-- The coordinates of a tangent vector: the `ε`-parts of its dual-number tuple. -/
noncomputable def TangentVec.vec {I : Ideal (MvPolynomial ι K)} {x : ι → K} (t : TangentVec I x) :
    ι → K :=
  fun i => ((ptEquiv K).symm ⟨t.hom ≫ Vι I, t.isOver⟩ i).snd

/-- The differential of `f` at `x`. -/
noncomputable def differential [Fintype ι] (f : MvPolynomial ι K) (x : ι → K) :
    (ι → K) →ₗ[K] K :=
  ∑ i, MvPolynomial.eval x (MvPolynomial.pderiv i f) • LinearMap.proj i

/-- The Jacobian kernel of `I` at `x`: the common kernel of the differentials. -/
noncomputable def jacobianKernel [Fintype ι] (I : Ideal (MvPolynomial ι K)) (x : ι → K) :
    Submodule K (ι → K) :=
  ⨅ f ∈ I, LinearMap.ker (differential f x)

/-- The dual-number tuple of a tangent vector at `x`: constant part `x` (this is
`restrict`, through `ptEquiv_map` along `fstHom`), linear part `vec`. -/
theorem TangentVec.ptEquiv_symm_eq {I : Ideal (MvPolynomial ι K)} {x : ι → K}
    (t : TangentVec I x) :
    (ptEquiv K).symm ⟨t.hom ≫ Vι I, t.isOver⟩ =
      fun i => TrivSqZeroExt.inl (x i) + TrivSqZeroExt.inr (t.vec i) := by
  set a : ι → DualNumber K := (ptEquiv K).symm ⟨t.hom ≫ Vι I, t.isOver⟩ with ha
  have h1 : (ptEquiv K a).1 = t.hom ≫ Vι I := by rw [ha, Equiv.apply_symm_apply]
  have h2 := t.restrict
  rw [← h1, epsZero, ptEquiv_map (TrivSqZeroExt.fstHom K K K) a] at h2
  have h3 := (ptEquiv K).injective (Subtype.ext h2)
  funext i
  refine TrivSqZeroExt.ext ?_ ?_
  · simpa using congrFun h3 i
  · simp [TangentVec.vec, ha]

/-- A tangent vector is determined by its coordinates (`Vι I` is mono). -/
theorem TangentVec.vec_injective (I : Ideal (MvPolynomial ι K)) (x : ι → K) :
    Function.Injective (TangentVec.vec (I := I) (x := x)) := by
  rintro t₁ t₂ h
  have hhom : t₁.hom ≫ Vι I = t₂.hom ≫ Vι I := by
    have e1 := (ptEquiv K).apply_symm_apply ⟨t₁.hom ≫ Vι I, t₁.isOver⟩
    have e2 := (ptEquiv K).apply_symm_apply ⟨t₂.hom ≫ Vι I, t₂.isOver⟩
    rw [t₁.ptEquiv_symm_eq] at e1
    rw [t₂.ptEquiv_symm_eq, ← h] at e2
    exact congrArg Subtype.val (e1.symm.trans e2)
  obtain ⟨h₁, o₁, r₁⟩ := t₁
  obtain ⟨h₂, o₂, r₂⟩ := t₂
  have : h₁ = h₂ := (cancel_mono (Vι I)).mp hhom
  subst this
  rfl

/-- Membership in the Jacobian kernel, unfolded. -/
theorem mem_jacobianKernel_iff [Fintype ι] (I : Ideal (MvPolynomial ι K)) (x v : ι → K) :
    v ∈ jacobianKernel I x ↔
      ∀ f ∈ I, ∑ i, MvPolynomial.eval x (MvPolynomial.pderiv i f) * v i = 0 := by
  simp [jacobianKernel, differential, Submodule.mem_iInf, LinearMap.mem_ker]

/-- **The Jacobian characterisation**: at a `K`-point of `V(I)` the tangent vectors are
exactly the Jacobian kernel (`exists_lift_Vι_iff` with `A = K[ε]` and the first-order
Taylor expansion `f(x + εv) = f(x) + ε ⟨df_x, v⟩`). -/
theorem exists_tangentVec_iff [Fintype ι] {I : Ideal (MvPolynomial ι K)} {x : ι → K}
    (hx : ∀ f ∈ I, MvPolynomial.eval x f = 0) (v : ι → K) :
    (∃ t : TangentVec I x, t.vec = v) ↔ v ∈ jacobianKernel I x := by
  rw [mem_jacobianKernel_iff]
  constructor
  · rintro ⟨t, rfl⟩
    set a : ι → DualNumber K := (ptEquiv K).symm ⟨t.hom ≫ Vι I, t.isOver⟩ with ha
    have h1 : (ptEquiv K a).1 = t.hom ≫ Vι I := by rw [ha, Equiv.apply_symm_apply]
    have hsol : ∀ f ∈ I, MvPolynomial.aeval a f = 0 :=
      (exists_lift_Vι_iff I a).mp ⟨t.hom, h1.symm⟩
    have hta := t.ptEquiv_symm_eq
    intro f hf
    have hf0 := hsol f hf
    rw [← ha] at hta
    rw [hta, MvPolynomial.aeval_dualNumber, hx f hf] at hf0
    simpa using congrArg TrivSqZeroExt.snd hf0
  · intro hv
    set a : ι → DualNumber K :=
      fun i => TrivSqZeroExt.inl (x i) + TrivSqZeroExt.inr (v i) with ha
    have hsol : ∀ f ∈ I, MvPolynomial.aeval a f = 0 := by
      intro f hf
      rw [ha, MvPolynomial.aeval_dualNumber, hx f hf, hv f hf]
      simp
    obtain ⟨g, hg⟩ := (exists_lift_Vι_iff I a).mpr hsol
    have hover : (g ≫ Vι I).IsOver (Spec (.of K)) := by rw [hg]; exact (ptEquiv K a).2
    have hsub : (⟨g ≫ Vι I, hover⟩ : Pt K ι (DualNumber K)) = ptEquiv K a := Subtype.ext hg
    refine ⟨⟨g, hover, ?_⟩, ?_⟩
    · rw [hg, epsZero, ptEquiv_map (TrivSqZeroExt.fstHom K K K) a]
      simp [ha]
    · funext i
      simp [TangentVec.vec, hsub, ha]

end Tangent

/-! ### Arcs: `K⟦u⟧`-points of `V(I)` -/

section Arc

variable {K : Type u} [Field K] {ι : Type u}

/-- **An arc in `V(I)`**: a `K⟦u⟧`-point of `V(I)` over `K`. -/
structure Arc (I : Ideal (MvPolynomial ι K)) where
  /-- The power-series point. -/
  hom : Spec (.of (PowerSeries K)) ⟶ Vsch I
  isOver : (hom ≫ Vι I).IsOver (Spec (.of K))

/-- The closed point `Spec K ⟶ Spec K⟦u⟧` (`u ↦ 0`). -/
noncomputable def arcZero (K : Type u) [Field K] : Spec (.of K) ⟶ Spec (.of (PowerSeries K)) :=
  Spec.map (CommRingCat.ofHom PowerSeries.constantCoeff)

/-- The first-order neighbourhood `Spec K[ε] ⟶ Spec K⟦u⟧` (`u ↦ ε`). -/
noncomputable def arcTrunc (K : Type u) [Field K] :
    Spec (.of (DualNumber K)) ⟶ Spec (.of (PowerSeries K)) :=
  Spec.map (CommRingCat.ofHom PowerSeries.toDualNumber)

/-- The coordinates of an arc: its tuple of power series. -/
noncomputable def Arc.coords {I : Ideal (MvPolynomial ι K)} (a : Arc I) : ι → PowerSeries K :=
  (ptEquiv K).symm ⟨a.hom ≫ Vι I, a.isOver⟩

/-- The base point of an arc. -/
noncomputable def Arc.base {I : Ideal (MvPolynomial ι K)} (a : Arc I) : ι → K :=
  fun i => PowerSeries.constantCoeff (a.coords i)

/-- **The velocity of an arc in coordinates**: the linear coefficients of its
power series.  By `Arc.snd_coords_velHom` these are the `ε`-parts of the
first-order truncation `Arc.velHom`, so this is the coordinate reading of the
scheme-level velocity. -/
noncomputable def Arc.vel {I : Ideal (MvPolynomial ι K)} (a : Arc I) : ι → K :=
  fun i => PowerSeries.coeff 1 (a.coords i)

/-- **The velocity of an arc**: its first-order truncation, a `K[ε]`-point of `V(I)`. -/
noncomputable def Arc.velHom {I : Ideal (MvPolynomial ι K)} (a : Arc I) :
    Spec (.of (DualNumber K)) ⟶ Vsch I :=
  arcTrunc K ≫ a.hom

/-- An arc is the `K⟦u⟧`-point of its coordinates. -/
theorem Arc.ptEquiv_coords {I : Ideal (MvPolynomial ι K)} (a : Arc I) :
    (ptEquiv K a.coords).1 = a.hom ≫ Vι I := by
  rw [Arc.coords, Equiv.apply_symm_apply]

/-- Arcs are formal solutions: the coordinates satisfy every equation of `I`
(`exists_lift_Vι_iff` with `A = K⟦u⟧`). -/
theorem Arc.aeval_coords {I : Ideal (MvPolynomial ι K)} (a : Arc I) :
    ∀ f ∈ I, MvPolynomial.aeval a.coords f = 0 :=
  (exists_lift_Vι_iff I a.coords).mp ⟨a.hom, a.ptEquiv_coords.symm⟩

/-- Every formal solution is an arc. -/
theorem exists_arc_iff {I : Ideal (MvPolynomial ι K)} (c : ι → PowerSeries K) :
    (∃ a : Arc I, a.coords = c) ↔ ∀ f ∈ I, MvPolynomial.aeval c f = 0 := by
  constructor
  · rintro ⟨a, rfl⟩
    exact a.aeval_coords
  · intro h
    obtain ⟨g, hg⟩ := (exists_lift_Vι_iff I c).mpr h
    have hover : (g ≫ Vι I).IsOver (Spec (.of K)) := by rw [hg]; exact (ptEquiv K c).2
    have he : (⟨g ≫ Vι I, hover⟩ : Pt K ι (PowerSeries K)) = ptEquiv K c := Subtype.ext hg
    exact ⟨⟨g, hover⟩, by rw [Arc.coords, he, Equiv.symm_apply_apply]⟩

/-- An arc is determined by its coordinates: `Vι I` is a monomorphism, so two
`K⟦u⟧`-points of `V(I)` with the same tuple of power series are equal. -/
theorem Arc.coords_injective (I : Ideal (MvPolynomial ι K)) :
    Function.Injective (Arc.coords (I := I)) := by
  intro a b h
  have hcomp : a.hom ≫ Vι I = b.hom ≫ Vι I := by
    rw [← a.ptEquiv_coords, ← b.ptEquiv_coords, h]
  have : a.hom = b.hom := (cancel_mono (Vι I)).1 hcomp
  cases a; cases b; simp_all

/-- **The arcs of `V(I)` are the formal solutions of `I`** (`exists_arc_iff`
with the uniqueness of the lift): a `K⟦u⟧`-point of `V(I)` is exactly a tuple of
power series satisfying every equation of `I`. -/
noncomputable def arcEquiv (I : Ideal (MvPolynomial ι K)) :
    Arc I ≃ {c : ι → PowerSeries K // ∀ f ∈ I, MvPolynomial.aeval c f = 0} where
  toFun a := ⟨a.coords, a.aeval_coords⟩
  invFun c := ((exists_arc_iff c.1).2 c.2).choose
  left_inv a := Arc.coords_injective I ((exists_arc_iff a.coords).2 a.aeval_coords).choose_spec
  right_inv c := Subtype.ext ((exists_arc_iff c.1).2 c.2).choose_spec

@[simp] theorem arcEquiv_apply {I : Ideal (MvPolynomial ι K)} (a : Arc I) :
    (arcEquiv I a : ι → PowerSeries K) = a.coords := rfl

@[simp] theorem coords_arcEquiv_symm {I : Ideal (MvPolynomial ι K)}
    (c : {c : ι → PowerSeries K // ∀ f ∈ I, MvPolynomial.aeval c f = 0}) :
    ((arcEquiv I).symm c).coords = c :=
  congrArg Subtype.val ((arcEquiv I).apply_symm_apply c)

/-- The velocity is the `K[ε]`-point of the truncated coordinates. -/
theorem Arc.velHom_comp_Vι {I : Ideal (MvPolynomial ι K)} (a : Arc I) :
    a.velHom ≫ Vι I = (ptEquiv K fun i => PowerSeries.toDualNumber (a.coords i)).1 := by
  have h := ptEquiv_map (PowerSeries.toDualNumberAlgHom (R := K)) a.coords
  rw [PowerSeries.toDualNumberAlgHom_toRingHom] at h
  simp only [PowerSeries.toDualNumberAlgHom_apply] at h
  rw [Arc.velHom, Category.assoc, ← a.ptEquiv_coords, arcTrunc, h]

/-- The velocity is over `K` and reduces to the base point, so it is a tangent vector
at `a.base` (`ptEquiv_map` along `toDualNumber`, and `fstHom_comp_toDualNumber`). -/
theorem Arc.velHom_isOver {I : Ideal (MvPolynomial ι K)} (a : Arc I) :
    (a.velHom ≫ Vι I).IsOver (Spec (.of K)) := by
  have h := (ptEquiv K fun i => PowerSeries.toDualNumber (a.coords i)).2
  rwa [← a.velHom_comp_Vι] at h

/-- Truncating an arc to first order and then killing `ε` is evaluation at `u = 0`. -/
theorem epsZero_comp_arcTrunc : epsZero K ≫ arcTrunc K = arcZero K := by
  rw [epsZero, arcTrunc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    PowerSeries.fstHom_comp_toDualNumber, arcZero]

theorem Arc.velHom_restrict {I : Ideal (MvPolynomial ι K)} (a : Arc I) :
    epsZero K ≫ a.velHom ≫ Vι I = (ptEquiv K a.base).1 := by
  have h := ptEquiv_map (PowerSeries.constantCoeffAlgHom (R := K)) a.coords
  rw [PowerSeries.constantCoeffAlgHom_toRingHom] at h
  simp only [PowerSeries.constantCoeffAlgHom_apply] at h
  rw [Arc.velHom, Category.assoc, ← a.ptEquiv_coords, ← Category.assoc,
    epsZero_comp_arcTrunc, arcZero, h]
  rfl

/-- The coordinates of the velocity are the linear coefficients of the arc. -/
theorem Arc.snd_coords_velHom {I : Ideal (MvPolynomial ι K)} (a : Arc I)
    (h : (a.velHom ≫ Vι I).IsOver (Spec (.of K))) (i : ι) :
    ((ptEquiv K).symm ⟨a.velHom ≫ Vι I, h⟩ i).snd = PowerSeries.coeff 1 (a.coords i) := by
  have he : (⟨a.velHom ≫ Vι I, h⟩ : Pt K ι (DualNumber K)) =
      ptEquiv K (fun j => PowerSeries.toDualNumber (a.coords j)) :=
    Subtype.ext a.velHom_comp_Vι
  rw [he, Equiv.symm_apply_apply]
  simp

end Arc

/-- Affine space with finitely many coordinates is a Noetherian space (`specHomeo` and
`PrimeSpectrum`'s instance for the Noetherian ring `K[ν]`).  A mathlib candidate; a
companion of the `IsLocallyNoetherian` instances of `Geometry/Stalk.lean`. -/
instance noetherianSpace (K : Type u) [Field K] (ν : Type u) [Finite ν] :
    NoetherianSpace 𝔸(ν; Spec (.of K)) :=
  (TopologicalSpace.noetherianSpace_iff_of_homeomorph (specHomeo K ν)).mpr inferInstance

/-! ### Constructibility on `K`-points

A constructible subset of affine space has constructible `K`-points in the coordinate
sense of `Dimension/LocClosed.lean`.  Induction on the basis of principal opens
(`Topology.IsConstructible.induction_of_isTopologicalBasis`): a difference
`D f ∖ ⋃_{g ∈ s} D g` has `K`-points `zeroLocus (span s) ∩ {x | aeval x f ≠ 0}`, which is
locally closed. -/

section Constructible

variable {K : Type u} [Field K] {ι : Type u} [Finite ι]

omit [Finite ι] in
/-- The principal opens are a topological basis of affine space (`specHomeo` and
`PrimeSpectrum.isTopologicalBasis_basic_opens`). -/
theorem isTopologicalBasis_D :
    TopologicalSpace.IsTopologicalBasis
      (Set.range fun f : MvPolynomial ι K => D f) := by
  have h := (specHomeo K ι).isInducing.isTopologicalBasis
    (PrimeSpectrum.isTopologicalBasis_basic_opens (R := MvPolynomial ι K))
  have himg : (Set.preimage (specHomeo K ι)) ''
      (Set.range fun r : MvPolynomial ι K =>
        (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum (MvPolynomial ι K)))) =
      Set.range fun f : MvPolynomial ι K => D f := by
    rw [← Set.range_comp]
    refine congrArg Set.range (funext fun f => ?_)
    show specHomeo K ι ⁻¹' (PrimeSpectrum.basicOpen f : Set _) = D f
    rw [PrimeSpectrum.basicOpen_eq_zeroLocus_compl, Set.preimage_compl,
      ← V_eq_specHomeo_preimage, ← D_eq_compl_V]
  rwa [himg] at h

/-- **The `K`-points of a constructible set are affine-constructible.** -/
theorem isAffineConstructible_pts {Z : Set 𝔸(ι; Spec (.of K))} (hZ : IsConstructible Z) :
    IsAffineConstructible {x : ι → K | (ptEquiv K x : 𝔸(ι; Spec (.of K))) ∈ Z} := by
  refine Topology.IsConstructible.induction_of_isTopologicalBasis
    (P := fun W _ => IsAffineConstructible
      {x : ι → K | (ptEquiv K x : 𝔸(ι; Spec (.of K))) ∈ W})
    (fun f : MvPolynomial ι K => D f) isTopologicalBasis_D
    (fun _ => TopologicalSpace.NoetherianSpace.isCompact _) ?_ ?_ Z hZ
  · intro f s _
    refine IsLocClosed.isConstructible ⟨MvPolynomial.zeroLocus K (Ideal.span s), f,
      zclosure_zeroLocus _, ?_⟩
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_iUnion, Set.mem_inter_iff,
      pt_mem_D_iff, not_exists, not_not, MvPolynomial.mem_zeroLocus_iff]
    constructor
    · rintro ⟨hf, hs⟩
      refine ⟨fun p hp => ?_, hf⟩
      have hle : Ideal.span s ≤
          RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom :=
        Ideal.span_le.mpr fun g hg => RingHom.mem_ker.mpr (hs g hg)
      exact RingHom.mem_ker.mp (hle hp)
    · rintro ⟨hs, hf⟩
      exact ⟨hf, fun g hg => hs g (Ideal.subset_span hg)⟩
  · intro W _ W' _ hW hW'
    have hset : {x : ι → K | (ptEquiv K x : 𝔸(ι; Spec (.of K))) ∈ W ∪ W'} =
        {x : ι → K | (ptEquiv K x : 𝔸(ι; Spec (.of K))) ∈ W} ∪
          {x : ι → K | (ptEquiv K x : 𝔸(ι; Spec (.of K))) ∈ W'} := rfl
    rw [hset]
    exact IsAffineConstructible.union hW hW'

/-- **Classical constructible sets are `K`-points of constructible subsets of `𝔸`** (the
converse of `isAffineConstructible_pts`): a locally closed piece `Z ∩ {g ≠ 0}` with `Z`
Zariski closed is the `K`-point set of `V (vanishingIdeal Z) ∩ D g`. -/
theorem exists_isConstructible_pts_eq {S : Set (ι → K)} (hS : IsAffineConstructible S) :
    ∃ Z : Set 𝔸(ι; Spec (.of K)), IsConstructible Z ∧
      {x : ι → K | (ptEquiv K x : 𝔸(ι; Spec (.of K))) ∈ Z} = S := by
  obtain ⟨J, hJ, P, hP, rfl⟩ := hS
  choose Zc g hZc hPc using hP
  refine ⟨⋃ j, (V (MvPolynomial.vanishingIdeal K (Zc j) : Set (MvPolynomial ι K)) ∩ D (g j)),
    Topology.IsConstructible.iUnion fun j =>
      (Toolbox.isConstructible_of_isClosed (isClosed_V _)).inter
        (Toolbox.isConstructible_of_isOpen (isOpen_D _)), ?_⟩
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, pt_mem_V_iff, pt_mem_D_iff,
    hPc]
  refine exists_congr fun j => and_congr_left fun _ => ?_
  simp only [SetLike.mem_coe]
  rw [← MvPolynomial.mem_zeroLocus_iff]
  change x ∈ zclosure (Zc j) ↔ x ∈ Zc j
  rw [hZc]

/-- **The `K`-points of the image of a constructible set under a polynomial map** are the
image of its `K`-points.  The inclusion `⊇` is `polyMapEquiv_pt`; for `⊆`, a `K`-point of
the image has a nonempty constructible fibre in `Z` (the singleton of a `K`-point is closed,
`range_pt`), which contains a `K`-point by `exists_pt_of_isConstructible`.  This is the
transfer that turns the classical fibration counts of `Dimension/` into statements about
`HomOver` maps of affine spaces. -/
theorem pts_image_polyMapEquiv [IsAlgClosed K] {κ : Type u} [Finite κ]
    (F : κ → MvPolynomial ι K) {Z : Set 𝔸(ι; Spec (.of K))} (hZ : IsConstructible Z) :
    (fun (x : ι → K) (j : κ) => MvPolynomial.aeval x (F j)) ''
        {x : ι → K | (ptEquiv K x : 𝔸(ι; Spec (.of K))) ∈ Z}
      = {w : κ → K | (ptEquiv K w : 𝔸(κ; Spec (.of K))) ∈ (polyMapEquiv F).1.base '' Z} := by
  ext w
  constructor
  · rintro ⟨x, hx, rfl⟩
    show (ptEquiv K (fun j => MvPolynomial.aeval x (F j)) : 𝔸(κ; Spec (.of K))) ∈
      (polyMapEquiv F).1.base '' Z
    rw [← polyMapEquiv_pt F x]
    exact Set.mem_image_of_mem _ hx
  · intro hw
    have hqcl : IsClosed ({(ptEquiv K w : 𝔸(κ; Spec (.of K)))} :
        Set 𝔸(κ; Spec (.of K))) := by
      have hmem : (ptEquiv K w : 𝔸(κ; Spec (.of K))) ∈
          Set.range fun z : κ → K => (ptEquiv K z : 𝔸(κ; Spec (.of K))) := ⟨_, rfl⟩
      rwa [range_pt] at hmem
    obtain ⟨p, hp, hpe⟩ := hw
    obtain ⟨x, hx⟩ := exists_pt_of_isConstructible
      (hZ.inter (IsClosed.isConstructible (hqcl.preimage (Scheme.Hom.continuous _))))
      ⟨p, hp, hpe⟩
    refine ⟨x, hx.1, pt_injective ?_⟩
    show (ptEquiv K (fun j => MvPolynomial.aeval x (F j)) : 𝔸(κ; Spec (.of K))) =
      (ptEquiv K w : 𝔸(κ; Spec (.of K)))
    rw [← polyMapEquiv_pt F x]
    exact hx.2
end Constructible


end Height.Geometry
