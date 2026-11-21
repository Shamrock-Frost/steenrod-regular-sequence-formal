import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field

/-!
# Elementary dimension theory for affine subsets

This is the dependency-free foundation of the affine geometry layer.  An
affine subset is represented by `S : Set (ι → K)`, its closure is the zero
locus of its vanishing ideal, and its dimension is the Krull dimension of the
coordinate ring of that closure.

The file contains only general commutative algebra and affine-space facts:

* Krull dimension of quotients by radicals and finite intersections;
* vanishing ideals of unions;
* polynomial maps and Zariski closure;
* the elementary `affineDim` calculus.

In particular, it imports no part of `Height.Chain`.
-/

universe u v

namespace Height.Geometry

/-! ## Krull dimension of quotients -/

open PrimeSpectrum

section Krull

variable {R : Type*} [CommRing R]

/-- A zero locus is up-closed in `Spec R`. -/
theorem zeroLocus_upClosed {I : Ideal R} {x y : PrimeSpectrum R}
    (hx : x ∈ zeroLocus (I : Set R)) (hxy : x ≤ y) : y ∈ zeroLocus (I : Set R) := by
  rw [mem_zeroLocus] at hx ⊢
  exact hx.trans hxy

/-- A chain of primes contained in a union of zero loci is contained in a single
one of them: its head lies in one of the loci, and zero loci are up-closed. -/
theorem exists_ltSeries_mem_zeroLocus {ι : Sort*} (J : ι → Ideal R)
    (l : LTSeries (PrimeSpectrum R))
    (hl : ∀ i, l i ∈ ⋃ k, zeroLocus (J k : Set R)) :
    ∃ k, ∀ i, l i ∈ zeroLocus (J k : Set R) := by
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (hl 0)
  exact ⟨k, fun i => zeroLocus_upClosed hk (l.monotone (Fin.zero_le i))⟩

/-- If the zero locus of `I` is covered by the zero loci of a family `J k`,
then the Krull dimension of `R ⧸ I` is bounded by any common bound for the
dimensions of the `R ⧸ J k`. -/
theorem ringKrullDim_quotient_le_of_zeroLocus_subset_iUnion {ι : Sort*} {I : Ideal R}
    {J : ι → Ideal R}
    (h : zeroLocus (I : Set R) ⊆ ⋃ k, zeroLocus (J k : Set R))
    {c : WithBot ℕ∞} (hc : ∀ k, ringKrullDim (R ⧸ J k) ≤ c) :
    ringKrullDim (R ⧸ I) ≤ c := by
  rw [ringKrullDim_quotient]
  show (⨆ l : LTSeries (zeroLocus (I : Set R)), (l.length : WithBot ℕ∞)) ≤ c
  refine iSup_le fun l => ?_
  obtain ⟨k, hk⟩ :=
    exists_ltSeries_mem_zeroLocus J
      (LTSeries.mk l.length (fun i => (l i : PrimeSpectrum R))
        (fun _ _ hij => l.strictMono hij))
      (fun i => h (l i).2)
  have hkc := hc k
  rw [ringKrullDim_quotient] at hkc
  refine le_trans ?_ hkc
  refine Order.LTSeries.length_le_krullDim
    (LTSeries.mk (α := (zeroLocus (J k : Set R) : Set (PrimeSpectrum R))) l.length
      (fun i => ⟨(l i : PrimeSpectrum R), hk i⟩)
      (fun _ _ hij => ?_))
  exact Subtype.mk_lt_mk.mpr (Subtype.mk_lt_mk.mp (l.strictMono hij))

/-- Finite-intersection form: the Krull dimension of `R ⧸ ⨅ i, J i` over a finite
index type is bounded by any common bound for the `R ⧸ J i`. -/
theorem ringKrullDim_quotient_iInf_le {ι : Type*} [Finite ι] (J : ι → Ideal R)
    {c : WithBot ℕ∞} (hc : ∀ i, ringKrullDim (R ⧸ J i) ≤ c) :
    ringKrullDim (R ⧸ ⨅ i, J i) ≤ c := by
  classical
  cases nonempty_fintype ι
  refine ringKrullDim_quotient_le_of_zeroLocus_subset_iUnion (J := J) ?_ hc
  intro P hP
  rw [mem_zeroLocus, SetLike.coe_subset_coe] at hP
  have hfin : (Finset.univ.inf J : Ideal R) ≤ P.asIdeal := by
    rwa [Finset.inf_univ_eq_iInf]
  obtain ⟨i, -, hip⟩ := P.isPrime.inf_le'.mp hfin
  exact Set.mem_iUnion.mpr ⟨i, hip⟩

/-- Krull dimension of a quotient depends only on the radical. -/
theorem ringKrullDim_quotient_radical (I : Ideal R) :
    ringKrullDim (R ⧸ I.radical) = ringKrullDim (R ⧸ I) := by
  rw [ringKrullDim_quotient,
    ringKrullDim_quotient, zeroLocus_radical]

/-- Krull dimension of `R ⧸ (I ⊓ J)` is the larger of the two. -/
theorem ringKrullDim_quotient_inf (I J : Ideal R) :
    ringKrullDim (R ⧸ (I ⊓ J)) = max (ringKrullDim (R ⧸ I)) (ringKrullDim (R ⧸ J)) := by
  refine le_antisymm ?_ (max_le ?_ ?_)
  · refine ringKrullDim_quotient_le_of_zeroLocus_subset_iUnion
      (J := fun b : Bool => if b then I else J) ?_ ?_
    · rw [zeroLocus_inf]
      rintro x (hx | hx)
      · exact Set.mem_iUnion.mpr ⟨true, by simpa using hx⟩
      · exact Set.mem_iUnion.mpr ⟨false, by simpa using hx⟩
    · rintro (_ | _) <;> simp [le_max_iff]
  · rw [ringKrullDim_quotient,
      ringKrullDim_quotient]
    exact Order.krullDim_le_of_strictMono
      (fun x => ⟨(x : PrimeSpectrum R), zeroLocus_anti_mono_ideal inf_le_left x.2⟩)
      (fun _ _ h => h)
  · rw [ringKrullDim_quotient,
      ringKrullDim_quotient]
    exact Order.krullDim_le_of_strictMono
      (fun x => ⟨(x : PrimeSpectrum R), zeroLocus_anti_mono_ideal inf_le_right x.2⟩)
      (fun _ _ h => h)

end Krull

/-! ## Vanishing ideals and affine dimension -/

open MvPolynomial

section Affine

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
variable {ι : Type v} {κ : Type*}

/-- The ideal of a union is the intersection of the ideals. -/
theorem vanishingIdeal_union (S T : Set (ι → K)) :
    MvPolynomial.vanishingIdeal k (S ∪ T) =
      MvPolynomial.vanishingIdeal k S ⊓ MvPolynomial.vanishingIdeal k T := by
  ext f
  simp only [MvPolynomial.mem_vanishingIdeal_iff, Ideal.mem_inf, Set.mem_union]
  exact ⟨fun h => ⟨fun x hx => h x (Or.inl hx), fun x hx => h x (Or.inr hx)⟩,
    fun h x hx => hx.elim (h.1 x) (h.2 x)⟩

/-- The ideal of an indexed union is the infimum of the ideals. -/
theorem vanishingIdeal_iUnion {α : Sort*} (S : α → Set (ι → K)) :
    MvPolynomial.vanishingIdeal k (⋃ i, S i) =
      ⨅ i, MvPolynomial.vanishingIdeal k (S i) := by
  ext f
  simp only [MvPolynomial.mem_vanishingIdeal_iff, Submodule.mem_iInf, Set.mem_iUnion]
  exact ⟨fun h i x hx => h x ⟨i, hx⟩, fun h x hx => hx.elim fun i hi => h i x hi⟩

/-- Krull dimension of the coordinate ring of the Zariski closure of a subset
of affine space. -/
noncomputable def affineDim (S : Set (ι → K)) : WithBot ℕ∞ :=
  ringKrullDim (MvPolynomial ι K ⧸ MvPolynomial.vanishingIdeal K S)

/-! ### Polynomial maps -/

/-- A map of affine spaces given by a tuple of polynomials. -/
def IsPolyMap (f : (ι → K) → (κ → K)) : Prop :=
  ∃ F : κ → MvPolynomial ι K, ∀ y j, f y j = aeval y (F j)

/-- Evaluation of a composite of polynomial substitutions, into any `K`-algebra.
The affine geometry uses it at `A = K`; the arc layer needs it at `A = K⟦u⟧`. -/
theorem aeval_aeval {A : Type*} [CommRing A] [Algebra K A]
    (F : κ → MvPolynomial ι K) (y : ι → A) (g : MvPolynomial κ K) :
    aeval y (aeval F g) = aeval (fun j => aeval y (F j)) g := by
  have h : (aeval y : MvPolynomial ι K →ₐ[K] A).comp (aeval F) =
      (aeval (fun j => aeval y (F j)) : MvPolynomial κ K →ₐ[K] A) := by
    refine MvPolynomial.algHom_ext fun j => ?_
    simp
  exact AlgHom.congr_fun h g

/-- The defining identity of a polynomial map, in the form used by the affine
geometry layer. -/
theorem aeval_polyMap {f : (ι → K) → (κ → K)} {F : κ → MvPolynomial ι K}
    (hF : ∀ y j, f y j = aeval y (F j)) (y : ι → K) (g : MvPolynomial κ K) :
    aeval (f y) g = aeval y (aeval F g) := by
  have h : f y = fun j => aeval y (F j) := _root_.funext fun j => hF y j
  rw [h, aeval_aeval]

theorem IsPolyMap.id : IsPolyMap (fun y : ι → K => y) :=
  ⟨fun i => X i, fun _ _ => by simp⟩

theorem IsPolyMap.comp {μ : Type*} {f : (ι → K) → (κ → K)} {g : (κ → K) → (μ → K)}
    (hf : IsPolyMap f) (hg : IsPolyMap g) : IsPolyMap (fun y => g (f y)) := by
  obtain ⟨F, hF⟩ := hf
  obtain ⟨G, hG⟩ := hg
  refine ⟨fun l => aeval F (G l), fun y l => ?_⟩
  show g (f y) l = aeval y (aeval F (G l))
  rw [hG (f y) l, aeval_polyMap hF]

/-- Restricting a point of a sum space to the coordinates of the first summand is
polynomial. -/
theorem isPolyMap_restrict_inl :
    IsPolyMap fun z : ι ⊕ κ → K => fun i => z (Sum.inl i) :=
  ⟨fun i => X (Sum.inl i), fun _ _ => by simp⟩

/-- Restricting a point of a sum space to the coordinates of the second summand is
polynomial. -/
theorem isPolyMap_restrict_inr :
    IsPolyMap fun z : ι ⊕ κ → K => fun j => z (Sum.inr j) :=
  ⟨fun j => X (Sum.inr j), fun _ _ => by simp⟩

/-! ### Zariski closure -/

/-- The Zariski closure of a subset of affine space. -/
def zclosure (S : Set (ι → K)) : Set (ι → K) :=
  MvPolynomial.zeroLocus K (MvPolynomial.vanishingIdeal K S)

theorem subset_zclosure (S : Set (ι → K)) : S ⊆ zclosure S :=
  MvPolynomial.zeroLocus_vanishingIdeal_le S

theorem zclosure_mono {S T : Set (ι → K)} (h : S ⊆ T) : zclosure S ⊆ zclosure T :=
  MvPolynomial.zeroLocus_anti_mono (MvPolynomial.vanishingIdeal_anti_mono h)

/-- The vanishing ideal does not change when passing to the Zariski closure. -/
@[simp] theorem vanishingIdeal_zclosure (S : Set (ι → K)) :
    MvPolynomial.vanishingIdeal K (zclosure S) = MvPolynomial.vanishingIdeal K S :=
  le_antisymm (MvPolynomial.vanishingIdeal_anti_mono (subset_zclosure S))
    (MvPolynomial.le_vanishingIdeal_zeroLocus _)

/-- The zero locus of an ideal is Zariski closed. -/
theorem zclosure_zeroLocus (J : Ideal (MvPolynomial ι K)) :
    zclosure (MvPolynomial.zeroLocus K J) = MvPolynomial.zeroLocus K J := by
  refine le_antisymm (fun x hx p hp => ?_) (subset_zclosure _)
  exact hx p (MvPolynomial.le_vanishingIdeal_zeroLocus J hp)

@[simp] theorem zclosure_zclosure (S : Set (ι → K)) : zclosure (zclosure S) = zclosure S :=
  zclosure_zeroLocus _

/-- A point is Zariski closed. -/
theorem zclosure_singleton (x : ι → K) : zclosure ({x} : Set (ι → K)) = {x} := by
  refine le_antisymm (fun y hy => ?_) (MvPolynomial.zeroLocus_vanishingIdeal_le _)
  refine Set.mem_singleton_iff.2 (funext fun i => ?_)
  have hmem : (X i - C (x i) : MvPolynomial ι K) ∈
      MvPolynomial.vanishingIdeal K ({x} : Set (ι → K)) := by
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    simp
  have := hy _ hmem
  simpa using sub_eq_zero.1 (by simpa using this)
/-- Affine space is Zariski closed. -/
theorem zclosure_univ : zclosure (Set.univ : Set (ι → K)) = Set.univ :=
  Set.eq_univ_of_univ_subset (subset_zclosure _)

/-- An intersection of two Zariski closed sets is Zariski closed. -/
theorem zclosure_inter {S T : Set (ι → K)} (hS : zclosure S = S) (hT : zclosure T = T) :
    zclosure (S ∩ T) = S ∩ T :=
  le_antisymm
    (fun _ hx => ⟨hS ▸ zclosure_mono Set.inter_subset_left hx,
      hT ▸ zclosure_mono Set.inter_subset_right hx⟩)
    (subset_zclosure _)

/-- The common zero set of a family of polynomials is Zariski closed. -/
theorem zclosure_zeros (S : Set (MvPolynomial ι K)) :
    zclosure {x : ι → K | ∀ q ∈ S, aeval x q = 0} = {x : ι → K | ∀ q ∈ S, aeval x q = 0} := by
  rw [← MvPolynomial.zeroLocus_span]
  exact zclosure_zeroLocus _

/-- A set cut out by the vanishing of a set of polynomials is Zariski closed. -/
theorem zclosure_eq_self_of_eqZeroLocus {S : Set (ι → K)} {T : Set (MvPolynomial ι K)}
    (h : ∀ z, z ∈ S ↔ ∀ p ∈ T, MvPolynomial.aeval z p = 0) : zclosure S = S := by
  have hS : S = MvPolynomial.zeroLocus K (Ideal.span T) := by
    rw [MvPolynomial.zeroLocus_span]
    ext z
    exact h z
  rw [hS]
  exact zclosure_zeroLocus _

/-- The preimage of a Zariski closed set under a polynomial map is Zariski
closed. -/
theorem zclosure_preimage {f : (ι → K) → (κ → K)} (hf : IsPolyMap f) {Z : Set (κ → K)}
    (hZ : zclosure Z = Z) : zclosure (f ⁻¹' Z) = f ⁻¹' Z := by
  obtain ⟨F, hF⟩ := hf
  refine le_antisymm (fun x hx => ?_) (subset_zclosure _)
  have hfx : f x ∈ zclosure Z := by
    intro q hq
    rw [aeval_polyMap hF]
    refine hx _ fun y hy => ?_
    rw [← aeval_polyMap hF]
    exact hq _ hy
  rwa [hZ] at hfx

/-- A polynomial map carries the Zariski closure into the Zariski closure of
the image. -/
theorem image_zclosure_subset {f : (ι → K) → (κ → K)} (hf : IsPolyMap f) (S : Set (ι → K)) :
    f '' zclosure S ⊆ zclosure (f '' S) := by
  obtain ⟨F, hF⟩ := hf
  rintro _ ⟨y, hy, rfl⟩ q hq
  rw [aeval_polyMap hF]
  refine hy _ ?_
  intro s hs
  rw [← aeval_polyMap hF]
  exact hq _ ⟨s, hs, rfl⟩

/-! ### The dimension calculus -/

/-- The dimension of a union of two affine sets is the larger dimension. -/
theorem affineDim_union (S T : Set (ι → K)) :
    affineDim (S ∪ T) = max (affineDim S) (affineDim T) := by
  unfold affineDim
  rw [vanishingIdeal_union, ringKrullDim_quotient_inf]

/-- `affineDim` is monotone. -/
theorem affineDim_mono {S T : Set (ι → K)} (h : S ⊆ T) :
    affineDim S ≤ affineDim T := by
  have hT : affineDim T = max (affineDim S) (affineDim T) := by
    rw [← affineDim_union, Set.union_eq_self_of_subset_left h]
  exact hT ▸ le_max_left _ _

/-- The dimension of a finite union is the supremum of the dimensions. -/
theorem affineDim_iUnion {J : Type*} [Finite J] (S : J → Set (ι → K)) :
    affineDim (⋃ j, S j) = ⨆ j, affineDim (S j) := by
  refine le_antisymm ?_ (iSup_le fun j => affineDim_mono (Set.subset_iUnion S j))
  unfold affineDim
  rw [vanishingIdeal_iUnion]
  exact ringKrullDim_quotient_iInf_le _ fun j =>
    le_iSup (fun j => ringKrullDim (MvPolynomial ι K ⧸ MvPolynomial.vanishingIdeal K (S j))) j

@[simp] theorem affineDim_zclosure (S : Set (ι → K)) :
    affineDim (zclosure S) = affineDim S := by
  unfold affineDim
  rw [vanishingIdeal_zclosure]

/-- The vanishing ideal is the unit ideal exactly on the empty set. -/
theorem vanishingIdeal_eq_top_iff (S : Set (ι → K)) :
    MvPolynomial.vanishingIdeal K S = ⊤ ↔ S = ∅ := by
  constructor
  · intro h
    refine Set.eq_empty_iff_forall_notMem.2 fun x hx => ?_
    have h1 : (1 : MvPolynomial ι K) ∈ MvPolynomial.vanishingIdeal K S := by
      rw [h]
      trivial
    have := h1 x hx
    simp at this
  · rintro rfl
    exact MvPolynomial.vanishingIdeal_empty

/-- The dimension of an affine set is `⊥` exactly when the set is empty. -/
theorem affineDim_eq_bot_iff (S : Set (ι → K)) : affineDim S = ⊥ ↔ S = ∅ := by
  unfold affineDim
  rw [ringKrullDim_eq_bot_iff_subsingleton, Ideal.Quotient.subsingleton_iff,
    vanishingIdeal_eq_top_iff]

@[simp] theorem affineDim_empty : affineDim (∅ : Set (ι → K)) = ⊥ :=
  (affineDim_eq_bot_iff _).2 rfl

/-- Over an algebraically closed field the dimension of a zero locus is the
Krull dimension of the quotient by its defining ideal. -/
theorem affineDim_zeroLocus [IsAlgClosed K] [Finite ι] (J : Ideal (MvPolynomial ι K)) :
    affineDim (MvPolynomial.zeroLocus K J) = ringKrullDim (MvPolynomial ι K ⧸ J) := by
  unfold affineDim
  rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical, ringKrullDim_quotient_radical]

end Affine

/-! ### Affine space itself (over an infinite field) -/

section AffineSpace

variable {K : Type u} [Field K] {ι : Type v}

/-- Over an infinite field only the zero polynomial vanishes identically. -/
theorem vanishingIdeal_univ [Infinite K] :
    MvPolynomial.vanishingIdeal K (Set.univ : Set (ι → K)) = ⊥ := by
  ext q
  simp only [MvPolynomial.mem_vanishingIdeal_iff, Ideal.mem_bot]
  constructor
  · intro h
    refine MvPolynomial.funext fun x => ?_
    rw [← MvPolynomial.coe_aeval_eq_eval, map_zero]
    exact h x (Set.mem_univ x)
  · rintro rfl x -
    simp

/-- Affine `ι`-space has dimension `#ι`. -/
theorem affineDim_univ [Finite ι] [Infinite K] :
    affineDim (Set.univ : Set (ι → K)) = ((Nat.card ι : ℕ∞) : WithBot ℕ∞) := by
  show ringKrullDim (MvPolynomial ι K ⧸ MvPolynomial.vanishingIdeal K (Set.univ : Set (ι → K)))
    = _
  rw [vanishingIdeal_univ, ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot (MvPolynomial ι K)),
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  simp

/-- Affine space is irreducible. -/
theorem isPrime_vanishingIdeal_univ [Infinite K] :
    (MvPolynomial.vanishingIdeal K (Set.univ : Set (ι → K))).IsPrime := by
  rw [vanishingIdeal_univ]
  exact Ideal.isPrime_bot

end AffineSpace

end Height.Geometry
