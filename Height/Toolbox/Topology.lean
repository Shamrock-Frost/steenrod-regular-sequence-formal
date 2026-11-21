import Mathlib.Topology.KrullDimension
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Irreducible
import Mathlib.Topology.Constructible

/-!
# General topology: Krull dimension of subsets, and the generic quantifier

These are facts about an arbitrary topological space that mathlib does not yet
state; they are stated here in their natural generality and are mathlib
candidates.  Nothing in this file knows about schemes.
-/

namespace Height.Toolbox

variable {X : Type*} [TopologicalSpace X]

/-! ### The generic quantifier -/

/-- **The generic quantifier**: `P` holds on a dense open subset of `Z` (an open `U`
with `U ∩ Z` dense in `Z`).  For irreducible `Z` this is "on a nonempty open
subset of `Z`" (`Generic.of_isIrreducible`); for reducible `Z` it is the right
notion, and unlike the nonempty-open form it is closed under conjunction. -/
def Generic (Z : Set X) (P : X → Prop) : Prop :=
  ∃ U : Set X, IsOpen U ∧ Z ⊆ closure (U ∩ Z) ∧ ∀ p ∈ U ∩ Z, P p

theorem Generic.mono {Z : Set X} {P Q : X → Prop} (h : Generic Z P) (hPQ : ∀ p, P p → Q p) :
    Generic Z Q := by
  obtain ⟨U, hU, hdense, hP⟩ := h
  exact ⟨U, hU, hdense, fun p hp => hPQ p (hP p hp)⟩

/-- Two dense open subsets of `Z` meet in a dense open subset of `Z`. -/
theorem Generic.and {Z : Set X} {P Q : X → Prop} (hP : Generic Z P) (hQ : Generic Z Q) :
    Generic Z fun p => P p ∧ Q p := by
  obtain ⟨U, hU, hUd, hUP⟩ := hP
  obtain ⟨V, hV, hVd, hVQ⟩ := hQ
  refine ⟨U ∩ V, hU.inter hV, fun z hz => ?_,
    fun p hp => ⟨hUP p ⟨hp.1.1, hp.2⟩, hVQ p ⟨hp.1.2, hp.2⟩⟩⟩
  rw [mem_closure_iff]
  intro W hW hzW
  obtain ⟨y, hyW, hyU, hyZ⟩ := mem_closure_iff.mp (hUd hz) W hW hzW
  obtain ⟨x, ⟨hxW, hxU⟩, hxV, hxZ⟩ :=
    mem_closure_iff.mp (hVd hyZ) (W ∩ U) (hW.inter hU) ⟨hyW, hyU⟩
  exact ⟨x, hxW, ⟨hxU, hxV⟩, hxZ⟩

theorem Generic.exists {Z : Set X} {P : X → Prop} (hZ : Z.Nonempty) (h : Generic Z P) :
    ∃ p ∈ Z, P p := by
  obtain ⟨U, hU, hdense, hP⟩ := h
  obtain ⟨z, hz⟩ := hZ
  rcases Set.eq_empty_or_nonempty (U ∩ Z) with hUZ | ⟨p, hp⟩
  · rw [hUZ, closure_empty] at hdense
    exact absurd (hdense hz) (Set.notMem_empty z)
  · exact ⟨p, hp.2, hP p hp⟩

/-- On an irreducible set a nonempty open subset is dense. -/
theorem Generic.of_isIrreducible {Z : Set X} (hZ : IsIrreducible Z) {P : X → Prop}
    (U : Set X) (hU : IsOpen U) (hne : (U ∩ Z).Nonempty) (hP : ∀ p ∈ U ∩ Z, P p) :
    Generic Z P := by
  refine ⟨U, hU, ?_, hP⟩
  have h := subset_closure_inter_of_isPreirreducible_of_isOpen hZ.isPreirreducible hU
    (by rwa [Set.inter_comm])
  rwa [Set.inter_comm] at h

/-! ### Irreducibility along homeomorphisms -/

/-- Irreducibility is invariant under a homeomorphism (mathlib has `IsIrreducible.preimage`
for open embeddings only). -/
theorem Homeomorph.isIrreducible_preimage_iff {Y : Type*} [TopologicalSpace Y] (e : X ≃ₜ Y)
    (Z : Set Y) : IsIrreducible (e ⁻¹' Z) ↔ IsIrreducible Z := by
  constructor
  · intro h
    have := h.preimage (f := e.symm) e.symm.isOpenEmbedding
      (by simpa [e.symm.surjective.range_eq] using h.nonempty)
    simpa [Set.preimage_preimage] using this
  · intro h
    exact h.preimage e.isOpenEmbedding (by simpa [e.surjective.range_eq] using h.nonempty)

/-- Constructibility is invariant under a homeomorphism (mathlib has the open- and
closed-embedding versions `Topology.IsConstructible.image_of_isOpenEmbedding` and
`Topology.IsConstructible.image_of_isClosedEmbedding`, whose retrocompactness side
condition a homeomorphism makes vacuous). -/
theorem Homeomorph.isConstructible_image {Y : Type*} [TopologicalSpace Y] (e : X ≃ₜ Y)
    {s : Set X} (hs : Topology.IsConstructible s) : Topology.IsConstructible (e '' s) := by
  rw [Set.image_eq_preimage_of_inverse e.symm_apply_apply e.apply_symm_apply]
  exact hs.preimage_of_isOpenEmbedding e.symm.isOpenEmbedding

/-! ### Krull dimension of subsets -/

section KrullDim

open TopologicalSpace

/-- An irreducible subset of `X` contained in `Z` is irreducible in the subspace `Z`.
Mathlib has the open-embedding version (`IsPreirreducible.preimage`), which does not apply. -/
theorem isIrreducible_preimage_val {Z s : Set X} (hs : IsIrreducible s) (hsub : s ⊆ Z) :
    IsIrreducible ((Subtype.val : Z → X) ⁻¹' s) := by
  obtain ⟨x, hx⟩ := hs.nonempty
  refine ⟨⟨⟨x, hsub hx⟩, hx⟩, ?_⟩
  rintro _ _ ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩ ⟨a, ha, hau⟩ ⟨b, hb, hbv⟩
  obtain ⟨y, hy, hyu, hyv⟩ := hs.isPreirreducible u v hu hv ⟨a.1, ha, hau⟩ ⟨b.1, hb, hbv⟩
  exact ⟨⟨y, hsub hy⟩, hy, hyu, hyv⟩

/-- An irreducible set covered by finitely many closed sets lies in one of them.  The `Finset`
form is `isIrreducible_iff_sUnion_isClosed`. -/
theorem exists_subset_of_isIrreducible_of_subset_iUnion {J : Type*} [Finite J] {s : Set X}
    {Z : J → Set X} (hs : IsIrreducible s) (hZ : ∀ j, IsClosed (Z j)) (hsub : s ⊆ ⋃ j, Z j) :
    ∃ j, s ⊆ Z j := by
  classical
  have hfin : (Set.range Z).Finite := Set.finite_range Z
  obtain ⟨W, hW, hsW⟩ := isIrreducible_iff_sUnion_isClosed.mp hs hfin.toFinset
    (fun W hW => by obtain ⟨j, rfl⟩ := hfin.mem_toFinset.mp hW; exact hZ j)
    (by rwa [hfin.coe_toFinset, Set.sUnion_range])
  obtain ⟨j, rfl⟩ := hfin.mem_toFinset.mp hW
  exact ⟨j, hsW⟩

/-- For a closed `Z` the irreducible closed subsets of the subspace `Z` and the irreducible
closed subsets of `X` contained in `Z` are the same poset, so they have the same Krull
dimension.  This is what lets the dimension of a closed subset be computed inside `X`. -/
theorem topologicalKrullDim_eq_krullDim_subtype {Z : Set X} (hZ : IsClosed Z) :
    topologicalKrullDim Z =
      Order.krullDim {s : IrreducibleCloseds X // (s : Set X) ⊆ Z} := by
  have himg : ∀ C : IrreducibleCloseds Z,
      ((IrreducibleCloseds.map (Subtype.val : Z → X) continuous_subtype_val C :
        IrreducibleCloseds X) : Set X) ⊆ Z := by
    intro C
    rw [IrreducibleCloseds.coe_map]
    exact hZ.closure_subset_iff.mpr (by rintro _ ⟨y, -, rfl⟩; exact y.2)
  have hup : StrictMono (fun C : IrreducibleCloseds Z =>
      (⟨IrreducibleCloseds.map (Subtype.val : Z → X) continuous_subtype_val C, himg C⟩ :
        {s : IrreducibleCloseds X // (s : Set X) ⊆ Z})) :=
    fun _ _ h =>
      IrreducibleCloseds.map_strictMono_of_isInducing Topology.IsInducing.subtypeVal h
  have hdown : StrictMono (fun s : {s : IrreducibleCloseds X // (s : Set X) ⊆ Z} =>
      (⟨(Subtype.val : Z → X) ⁻¹' ((s : IrreducibleCloseds X) : Set X),
        isIrreducible_preimage_val s.1.isIrreducible s.2,
        s.1.isClosed.preimage continuous_subtype_val⟩ : IrreducibleCloseds Z)) := by
    refine Monotone.strictMono_of_injective (fun _ _ h _ hx => h hx) ?_
    intro s t h
    have h' : (Subtype.val : Z → X) ⁻¹' ((s : IrreducibleCloseds X) : Set X)
        = (Subtype.val : Z → X) ⁻¹' ((t : IrreducibleCloseds X) : Set X) :=
      congrArg (fun C : IrreducibleCloseds Z => (C : Set Z)) h
    have h2 : (Subtype.val : Z → X) ''
          ((Subtype.val : Z → X) ⁻¹' ((s : IrreducibleCloseds X) : Set X))
        = (Subtype.val : Z → X) ''
          ((Subtype.val : Z → X) ⁻¹' ((t : IrreducibleCloseds X) : Set X)) := congrArg _ h'
    rw [Set.image_preimage_eq_of_subset (by rw [Subtype.range_coe]; exact s.2),
      Set.image_preimage_eq_of_subset (by rw [Subtype.range_coe]; exact t.2)] at h2
    exact Subtype.ext (SetLike.coe_injective h2)
  rw [topologicalKrullDim]
  exact le_antisymm (Order.krullDim_le_of_strictMono _ hup)
    (Order.krullDim_le_of_strictMono _ hdown)

/-- If a preorder is covered by lower sets, its Krull dimension is at most the supremum of
theirs.  (Any chain lies in the piece containing its top element.) -/
theorem krullDim_le_iSup_of_isLowerSet_cover {α : Type*} [Preorder α] {J : Type*} {S : J → Set α}
    (hS : ∀ j, IsLowerSet (S j)) (hcov : ∀ a : α, ∃ j, a ∈ S j) :
    Order.krullDim α ≤ ⨆ j, Order.krullDim (S j) := by
  rw [Order.krullDim]
  refine iSup_le fun p => ?_
  obtain ⟨j, hj⟩ := hcov p.last
  have hmem : ∀ i, p i ∈ S j := fun i => hS j (LTSeries.monotone p (Fin.le_last i)) hj
  exact le_trans (Order.LTSeries.length_le_krullDim
      (LTSeries.mk p.length (fun i => (⟨p i, hmem i⟩ : S j))
        (fun _ _ h => LTSeries.strictMono p h)))
    (le_iSup (fun j => Order.krullDim (S j)) j)

open Topology in
/-- Krull dimension of a subset is a topological invariant: an embedding does not change it
(a homeomorphism is the case `Homeomorph.isEmbedding`). -/
theorem topologicalKrullDim_image_of_isEmbedding {Y : Type*} [TopologicalSpace Y]
    {f : X → Y} (hf : IsEmbedding f) (s : Set X) :
    topologicalKrullDim (f '' s) = topologicalKrullDim s := by
  have hcont : Continuous fun x : s => (⟨f x, Set.mem_image_of_mem f x.2⟩ : (f '' s)) :=
    (hf.continuous.comp continuous_subtype_val).subtype_mk _
  have hind : IsInducing fun x : s => (⟨f x, Set.mem_image_of_mem f x.2⟩ : (f '' s)) :=
    IsInducing.of_comp hcont continuous_subtype_val (hf.isInducing.comp IsInducing.subtypeVal)
  exact (IsHomeomorph.topologicalKrullDim_eq _
    ((Equiv.Set.image f s hf.injective).toHomeomorphOfIsInducing hind).isHomeomorph).symm

theorem topologicalKrullDim_mono {Z Z' : Set X} (h : Z ⊆ Z') :
    topologicalKrullDim Z ≤ topologicalKrullDim Z' :=
  (Topology.IsEmbedding.inclusion h).isInducing.topologicalKrullDim_le

theorem topologicalKrullDim_iUnion_of_isClosed {J : Type*} [Finite J] {Z : J → Set X}
    (hZ : ∀ j, IsClosed (Z j)) :
    topologicalKrullDim (⋃ j, Z j : Set X) = ⨆ j, topologicalKrullDim (Z j) := by
  refine le_antisymm ?_ (iSup_le fun j => topologicalKrullDim_mono (Set.subset_iUnion Z j))
  rw [topologicalKrullDim_eq_krullDim_subtype (isClosed_iUnion_of_finite hZ)]
  refine le_trans (krullDim_le_iSup_of_isLowerSet_cover
    (S := fun j => {t : {s : IrreducibleCloseds X // (s : Set X) ⊆ ⋃ j, Z j} |
      ((t : IrreducibleCloseds X) : Set X) ⊆ Z j})
    (fun _ _ _ hba ha _ hx => ha (hba hx))
    (fun t => exists_subset_of_isIrreducible_of_subset_iUnion t.1.isIrreducible hZ t.2))
    (iSup_mono fun j => ?_)
  rw [topologicalKrullDim_eq_krullDim_subtype (hZ j)]
  exact Order.krullDim_le_of_strictMono (fun t => ⟨t.1.1, t.2⟩) fun _ _ h => h

theorem topologicalKrullDim_union_of_isClosed {Z Z' : Set X} (hZ : IsClosed Z)
    (hZ' : IsClosed Z') :
    topologicalKrullDim (Z ∪ Z' : Set X) = max (topologicalKrullDim Z) (topologicalKrullDim Z') := by
  rw [Set.union_eq_iUnion,
    topologicalKrullDim_iUnion_of_isClosed (fun b => by cases b <;> assumption)]
  refine le_antisymm (iSup_le fun b => ?_)
    (max_le (le_iSup (fun b : Bool => topologicalKrullDim (cond b Z Z' : Set X)) true)
      (le_iSup (fun b : Bool => topologicalKrullDim (cond b Z Z' : Set X)) false))
  cases b
  · exact le_max_right _ _
  · exact le_max_left _ _

theorem topologicalKrullDim_eq_bot_iff (Z : Set X) : topologicalKrullDim Z = ⊥ ↔ Z = ∅ := by
  rw [topologicalKrullDim, Order.krullDim_eq_bot_iff, Set.eq_empty_iff_forall_notMem]
  refine ⟨fun h z hz => h.false ⟨closure {(⟨z, hz⟩ : Z)}, isIrreducible_singleton.closure,
    isClosed_closure⟩, fun h => ⟨fun C => ?_⟩⟩
  obtain ⟨c, -⟩ := C.isIrreducible.nonempty
  exact h c c.2

/-- A Noetherian space has finitely many irreducible components and its dimension is the
largest of theirs (for a closed `Z ⊆ X` apply it to the subspace `Z`). -/
theorem topologicalKrullDim_eq_iSup_irreducibleComponents [TopologicalSpace.NoetherianSpace X] :
    topologicalKrullDim X = ⨆ C : irreducibleComponents X, topologicalKrullDim (C : Set X) := by
  have hfin : (irreducibleComponents X).Finite := NoetherianSpace.finite_irreducibleComponents
  have : Finite (irreducibleComponents X) := hfin.to_subtype
  have hcov : (⋃ C : irreducibleComponents X, (C : Set X)) = Set.univ := by
    rw [← Set.sUnion_eq_iUnion, sUnion_irreducibleComponents]
  rw [← topologicalKrullDim_iUnion_of_isClosed
      (fun C : irreducibleComponents X => isClosed_of_mem_irreducibleComponents _ C.2), hcov]
  exact ((Homeomorph.Set.univ X).isHomeomorph.topologicalKrullDim_eq).symm

end KrullDim

/-! ### Retrocompactness on a Noetherian space -/

/-- In a Noetherian space every subset is retrocompact (every subset is compact), so the
constructible sets are exactly the finite unions of locally closed sets and the transfer
lemmas of `Mathlib/Topology/Constructible.lean` apply without further hypotheses.
A mathlib candidate. -/
theorem isRetrocompact_of_noetherianSpace [TopologicalSpace.NoetherianSpace X] (s : Set X) :
    IsRetrocompact s :=
  fun _ _ _ => TopologicalSpace.NoetherianSpace.isCompact _

/-- In a Noetherian space every open set is constructible. -/
theorem isConstructible_of_isOpen [TopologicalSpace.NoetherianSpace X] {s : Set X}
    (h : IsOpen s) : Topology.IsConstructible s :=
  (isRetrocompact_of_noetherianSpace s).isConstructible h

/-- In a Noetherian space every closed set is constructible. -/
theorem isConstructible_of_isClosed [TopologicalSpace.NoetherianSpace X] {s : Set X}
    (h : IsClosed s) : Topology.IsConstructible s := by
  have hc := (isConstructible_of_isOpen h.isOpen_compl).compl
  rwa [compl_compl] at hc

end Height.Toolbox
