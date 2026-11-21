import Height.Graded.Lead

/-!
# `GradedPresentation`: the graded layer, stated once

`B = K[μ, ν]` is `Graded.Poly K`, graded by total degree over `ℤ` with
`B_d = ⊥` for `d < 0` (`Graded.Bpiece`, `Graded.Bproj`; `Graded/Basic.lean`).
A **graded presentation** is a finite free graded `B`-module

  `F = ⨁_{j : idx} B(-shift j)`,

realised on the underlying module `idx → B`.  The two data that describe it
— a rank `r` and a shift vector `a : Fin r → ℤ` — are the
single object `P : GradedPresentation K`, which carries the graded pieces
`P.piece e`, the homogeneous projections `P.proj e`, gradedness of a
`B`-submodule `P.IsGraded S`, the induced filtration `P.sub S e`, and the
reduction modulo `μ` (`P.redMu e`, `P.redFil S e`).  `HomogeneousBasis` is a
homogeneous `B`-basis of a graded submodule: the conclusion of `lem:free` as
one named object, whose `pres` is the presentation `⨁_i B(-deg i)` that the
submodule is graded free on.

## Why not mathlib's graded notions

In the pinned mathlib:

* `MvPolynomial.homogeneousSubmodule` and `MvPolynomial.homogeneousComponent`
  **are** used — they are the bodies of `Bpiece` and `Bproj`, and
  `MvPolynomial.basisRestrictSupport` is the body of `BpieceBasis`.
* `MvPolynomial.gradedAlgebra` / `MvPolynomial.decomposition` grade
  `MvPolynomial σ R` by `ℕ`, and are deliberately *not* global instances
  ("one may want to consider a different graded algebra structure").  This
  development needs the `ℤ`-indexed grading (`B_d = ⊥` for `d < 0`), because a
  shift `B(-a)` with `a : ℤ` has to be a degree offset and not a new type.
  Mathlib has no transport of a `DirectSum.Decomposition` along `ℕ ↪ ℤ`.
* **An `ℤ`-grading of the ring is nevertheless available**:
  `MvPolynomial.weightedGradedAlgebra K (1 : Fin 2 → ℤ)`
  elaborates, so `weightedHomogeneousSubmodule K (1 : Fin 2 → ℤ)` is an
  `ℤ`-graded algebra structure on `B` — and `Bpiece` is that submodule, spelled
  with an `if`.  With `ℤ` on both sides `VAdd ℤ ℤ` is fine.  (`VAdd ℕ ℤ` really
  is absent, but nothing forces the ring to be graded by `ℕ`.)
* `Submodule.IsHomogeneous ℳ` and `HomogeneousSubmodule 𝒜 ℳ`
  (`Mathlib/RingTheory/GradedAlgebra/Homogeneous/Submodule.lean`) are the right
  notions in the abstract, and could be stated over the `ℤ`-weighted grading
  above.  What is still missing is the *module* side:
  `DirectSum.Decomposition (fun e : ℤ => P.piece e)` for a shifted free module
  is data (`decompose'` and both inverses) that mathlib does not provide and
  that would have to be built for every shift vector, together with
  `SetLike.GradedSMul`.  `P.IsGraded` — stability under the projections — is
  that predicate unfolded, is what every consumer actually uses, and costs
  three lines.

So this development keeps its own `ℤ`-indexed notion, on mathlib's `ℕ`-indexed
homogeneous submodules and components underneath.  This is a matter of cost
on the module side, **not** an impossibility on the ring side.

## Instances at `of K a`

`of` is reducible, so `(of K a).Mod` unfolds to `ι → B` — which is what instance
search needs for the module structures, but which also loses the projection
`P.idx` that the presentation's own instances and `@[simp]` lemmas are indexed
on.  The consequence is that `instFinitePiece` and `instFiniteSub` are *not*
found at `P = of K a`, and that `mem_piece` and `redMu_apply` do not fire there:
the discrimination tree no longer offers them.  `instFinitePieceOf`,
`instFiniteSubOf` and `mem_piece_of` restate what is needed at `of`; a proof
that wants `redMu_apply` there names the value with `show` instead (see
`Graded/Torsion.lean`, `redFil_eq_top`).

The projective-line half of the layer — the chart bundle `Chart` and the
global-section comparison `P.sections`/`P.dehVec`/`P.coordEquiv` — is at the end
of `Height/Graded/ProjectiveLine.lean`, which is where `deh`, `atPoint` and
`atInf` live.
-/

noncomputable section

namespace Height.Graded

open MvPolynomial

/-! ### The presentation -/

/-- A **finite graded free module** over `B = K[μ, ν]`:

  `F = ⨁_{j : idx} B(-shift j)`,

realised on the underlying `B`-module `idx → B`.

`K` is a phantom parameter: it fixes the base field of `B` so that `P.Mod`,
`P.piece` and the rest infer it from `P`. -/
structure GradedPresentation (K : Type*) [Field K] where
  /-- The index set of the free generators; `Fin r` at every present call site. -/
  idx : Type
  [fintypeIdx : Fintype idx]
  /-- The degree shifts: the `j`-th summand is `B(-shift j)`, so its degree-`e`
  piece is `B_{e - shift j}`. -/
  shift : idx → ℤ

attribute [instance] GradedPresentation.fintypeIdx

namespace GradedPresentation

variable {K : Type*} [Field K]

variable (K) in
/-- The presentation of a shift vector, `⨁_{j : ι} B(-a j)`.  Reducible, so
that `(of K a).Mod` unfolds to `ι → B` during instance search. -/
@[simps] abbrev of {ι : Type} [Fintype ι] (a : ι → ℤ) : GradedPresentation K where
  idx := ι
  shift := a

variable (K) in
/-- The untwisted presentation `B^ι = ⨁_{j : ι} B`, the shift vector `0`. -/
abbrev free (ι : Type) [Fintype ι] : GradedPresentation K := of K (fun _ : ι => (0 : ℤ))

variable (P : GradedPresentation K)

/-- The underlying `B`-module `idx → B` of the presentation. -/
abbrev Mod : Type _ := P.idx → Poly K

/-! ### The graded pieces -/

/-- `F_e`, the degree-`e` piece: the tuples whose `j`-th entry is homogeneous of
degree `e - shift j`. -/
def piece (e : ℤ) : Submodule K P.Mod :=
  Submodule.pi Set.univ fun j => Bpiece K (e - P.shift j)

@[simp] theorem mem_piece {e : ℤ} {f : P.Mod} :
    f ∈ P.piece e ↔ ∀ j, f j ∈ Bpiece K (e - P.shift j) := by
  simp [piece]

/-- `mem_piece` again at `P = of K a`.  It is *not* redundant: see the module
docstring — `of` is reducible, and `mem_piece` is indexed on the projection
`P.shift`, so `simp` does not offer it at `of K a`. -/
@[simp] theorem mem_piece_of {ι : Type} [Fintype ι] {a : ι → ℤ} {e : ℤ} {f : ι → Poly K} :
    f ∈ (of K a).piece e ↔ ∀ j, f j ∈ Bpiece K (e - a j) :=
  (of K a).mem_piece

/-- Reading off coordinates identifies `F_e` with `∏_j B_{e - shift j}`. -/
def pieceEquiv (e : ℤ) : P.piece e ≃ₗ[K] ∀ j, Bpiece K (e - P.shift j) where
  toFun f j := ⟨f.1 j, P.mem_piece.1 f.2 j⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun g := ⟨fun j => (g j : Poly K), P.mem_piece.2 fun j => (g j).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance instFinitePiece (e : ℤ) : Module.Finite K (P.piece e) :=
  Module.Finite.equiv (P.pieceEquiv e).symm

/-- `instFinitePiece` again at `P = of K a`.  It is *not* redundant: `of` is
reducible, so at `of K a` the ambient module `P.Mod = P.idx → B` reduces to
`ι → B`, while `instFinitePiece` is indexed on the projection `P.idx`; the
discrimination tree then does not offer the general instance, and instance
search fails.  (`Module.Finite K ((of K a).piece e)` is unprovable by
`inferInstance` without this.) -/
instance instFinitePieceOf {ι : Type} [Fintype ι] (a : ι → ℤ) (e : ℤ) :
    Module.Finite K ((of K a).piece e) :=
  (of K a).instFinitePiece e

/-- **`lem:degree`**, the Hilbert function of a graded free module:
`dim_K F_e = ∑_j (e - a_j + 1)₊`. -/
theorem finrank_piece (e : ℤ) :
    Module.finrank K (P.piece e) = ∑ j, (e - P.shift j + 1).toNat := by
  rw [(P.pieceEquiv e).finrank_eq, Module.finrank_pi_fintype]
  exact Finset.sum_congr rfl fun j _ => finrank_Bpiece K _

/-- A piece below every shift is zero. -/
theorem piece_eq_bot {e : ℤ} (h : ∀ j, e < P.shift j) : P.piece e = ⊥ := by
  refine le_antisymm (fun x hx => ?_) bot_le
  rw [Submodule.mem_bot]
  funext j
  have hj := P.mem_piece.1 hx j
  rw [Bpiece_of_neg (by have := h j; omega), Submodule.mem_bot] at hj
  exact hj

/-- The shifts are bounded below. -/
theorem exists_shift_lowerBound : ∃ e₀ : ℤ, ∀ j, e₀ ≤ P.shift j := by
  obtain ⟨e₀, he₀⟩ := Finite.bddBelow_range P.shift
  exact ⟨e₀, fun j => he₀ ⟨j, rfl⟩⟩

/-- The grading is multiplicative: `B_d · F_e ⊆ F_{d+e}`. -/
theorem smul_mem_piece {d e : ℤ} {f : Poly K} {y : P.Mod}
    (hf : f ∈ Bpiece K d) (hy : y ∈ P.piece e) : f • y ∈ P.piece (d + e) := by
  refine P.mem_piece.2 fun j => ?_
  have := Bpiece_smul_Bpiece hf (P.mem_piece.1 hy j)
  rwa [show d + (e - P.shift j) = d + e - P.shift j by ring] at this

/-! ### The homogeneous projections -/

/-- The projection of `F` onto its degree-`e` piece, coordinatewise. -/
def proj (e : ℤ) : P.Mod →ₗ[K] P.Mod :=
  LinearMap.pi fun j => (Bproj (e - P.shift j)).comp (LinearMap.proj j)

@[simp] theorem proj_apply (e : ℤ) (f : P.Mod) (j : P.idx) :
    P.proj e f j = Bproj (e - P.shift j) (f j) := rfl

theorem proj_mem (e : ℤ) (f : P.Mod) : P.proj e f ∈ P.piece e :=
  P.mem_piece.2 fun _ => Bproj_mem _ _

/-- The projections are orthogonal idempotents. -/
theorem proj_of_mem {e e' : ℤ} {f : P.Mod} (hf : f ∈ P.piece e') :
    P.proj e f = if e = e' then f else 0 := by
  ext j
  rw [P.proj_apply, Bproj_of_mem (P.mem_piece.1 hf j)]
  by_cases h : e = e' <;> simp [h]

@[simp] theorem proj_self {e : ℤ} {f : P.Mod} (hf : f ∈ P.piece e) : P.proj e f = f := by
  simp [P.proj_of_mem hf]

/-- The projection of a multiple of a homogeneous element. -/
theorem proj_smul {b e : ℤ} (f : Poly K) {u : P.Mod} (hu : u ∈ P.piece b) :
    P.proj e (f • u) = (Bproj (e - b)) f • u := by
  funext j
  simp only [proj_apply, Pi.smul_apply, smul_eq_mul]
  have h := Bproj_smul_of_mem (d := e - b) f (P.mem_piece.1 hu j)
  rwa [show e - b + (b - P.shift j) = e - P.shift j by ring] at h

/-- Every element is the finite sum of its homogeneous components. -/
theorem exists_sum_proj (f : P.Mod) : ∃ s : Finset ℤ, ∑ e ∈ s, P.proj e f = f := by
  classical
  refine ⟨Finset.univ.biUnion fun j =>
    (Finset.range ((f j).totalDegree + 1)).image fun d : ℕ => P.shift j + (d : ℤ), ?_⟩
  refine funext fun j => ?_
  rw [Finset.sum_apply]
  simp only [proj_apply]
  refine sum_Bproj (P.shift j) (f j) _ fun d hd => ?_
  exact Finset.mem_biUnion.2 ⟨j, Finset.mem_univ j,
    Finset.mem_image.2 ⟨d, Finset.mem_range.2 (by omega), rfl⟩⟩

/-! ### Graded submodules -/

/-- A `B`-submodule of `F` is **graded** when it is stable under the
homogeneous projections.  This is `Submodule.IsHomogeneous` for the shifted
grading, spelled out (see the module docstring for why mathlib's predicate does
not apply here). -/
def IsGraded (S : Submodule (Poly K) P.Mod) : Prop :=
  ∀ f ∈ S, ∀ e : ℤ, P.proj e f ∈ S

/-- `S_e`, the degree-`e` piece of a submodule, as a `K`-subspace of `F`. -/
def sub (S : Submodule (Poly K) P.Mod) (e : ℤ) : Submodule K P.Mod :=
  S.restrictScalars K ⊓ P.piece e

theorem mem_sub {S : Submodule (Poly K) P.Mod} {e : ℤ} {x : P.Mod} :
    x ∈ P.sub S e ↔ x ∈ S ∧ x ∈ P.piece e := Iff.rfl

instance instFiniteSub (S : Submodule (Poly K) P.Mod) (e : ℤ) :
    Module.Finite K (P.sub S e) :=
  Module.Finite.of_injective (Submodule.inclusion (inf_le_right : P.sub S e ≤ _))
    (Submodule.inclusion_injective _)

/-- `instFiniteSub` again at `P = of K a`; see `instFinitePieceOf` for why the
general instance is not found there. -/
instance instFiniteSubOf {ι : Type} [Fintype ι] (a : ι → ℤ)
    (S : Submodule (Poly K) (ι → Poly K)) (e : ℤ) :
    Module.Finite K ((of K a).sub S e) :=
  (of K a).instFiniteSub S e

theorem finrank_sub_le (S : Submodule (Poly K) P.Mod) (e : ℤ) :
    Module.finrank K (P.sub S e) ≤ Module.finrank K (P.piece e) :=
  LinearMap.finrank_le_finrank_of_injective
    (f := Submodule.inclusion (inf_le_right : P.sub S e ≤ P.piece e))
    (Submodule.inclusion_injective _)

/-! ### Reduction modulo `μ` -/

/-- Coordinatewise reduction modulo `μ` in degree `e`: the `ν`-leading
coefficient in each coordinate. -/
def redMu (e : ℤ) : P.Mod →ₗ[K] (P.idx → K) :=
  LinearMap.pi fun j => (nuLead (e - P.shift j)).comp (LinearMap.proj j)

@[simp] theorem redMu_apply (e : ℤ) (x : P.Mod) (j : P.idx) :
    P.redMu e x j = nuLead (e - P.shift j) (x j) := rfl

/-- Reduction turns multiplication by a homogeneous polynomial into
multiplication by its leading coefficient. -/
theorem redMu_smul {d e : ℤ} {f : Poly K} {x : P.Mod}
    (hf : f ∈ Bpiece K d) (hx : x ∈ P.piece e) :
    P.redMu (d + e) (f • x) = nuLead d f • P.redMu e x := by
  funext j
  simp only [redMu_apply, Pi.smul_apply, smul_eq_mul]
  rw [show d + e - P.shift j = d + (e - P.shift j) by ring]
  exact nuLead_mul hf (P.mem_piece.1 hx j)

/-- Multiplying by `ν^k` shifts the degree and leaves the reduction unchanged. -/
theorem redMu_nu_pow_smul {e : ℤ} {y : P.Mod} (k : ℕ) (hy : y ∈ P.piece e) :
    P.redMu ((k : ℤ) + e) ((nu ^ k : Poly K) • y) = P.redMu e y := by
  rw [P.redMu_smul (nu_pow_mem k) hy, nuLead_nu_pow, one_smul]

/-- An element of `F_e` killed by the reduction is `μ` times an element of
`F_{e-1}`. -/
theorem exists_eq_mu_smul {e : ℤ} {x : P.Mod} (hx : x ∈ P.piece e) (h : P.redMu e x = 0) :
    ∃ y ∈ P.piece (e - 1), x = (mu : Poly K) • y := by
  have h' : ∀ j, ∃ g ∈ Bpiece K (e - 1 - P.shift j), x j = (mu : Poly K) * g := by
    intro j
    obtain ⟨g, hg, hxg⟩ := exists_eq_mu_mul (P.mem_piece.1 hx j) (congrFun h j)
    exact ⟨g, by rwa [show e - P.shift j - 1 = e - 1 - P.shift j by ring] at hg, hxg⟩
  choose g hg hxg using h'
  exact ⟨g, P.mem_piece.2 hg, funext hxg⟩

/-- The reduction of `S_e` modulo `μ`, a subspace of `K^idx`; as `e` grows these
form an increasing filtration. -/
def redFil (S : Submodule (Poly K) P.Mod) (e : ℤ) : Submodule K (P.idx → K) :=
  (P.sub S e).map (P.redMu e)

theorem mem_redFil {S : Submodule (Poly K) P.Mod} {e : ℤ} {v : P.idx → K} :
    v ∈ P.redFil S e ↔ ∃ x ∈ P.sub S e, P.redMu e x = v := Submodule.mem_map

theorem redFil_mono (S : Submodule (Poly K) P.Mod) {e e' : ℤ} (h : e ≤ e') :
    P.redFil S e ≤ P.redFil S e' := by
  rintro v hv
  obtain ⟨x, hx, rfl⟩ := P.mem_redFil.1 hv
  refine P.mem_redFil.2 ⟨(nu ^ (e' - e).toNat : Poly K) • x, ?_, ?_⟩
  · refine P.mem_sub.2 ⟨S.smul_mem _ hx.1, ?_⟩
    have h2 := P.smul_mem_piece (nu_pow_mem (K := K) (e' - e).toNat) hx.2
    rwa [show ((((e' - e).toNat : ℤ)) + e) = e' by omega] at h2
  · have h2 := P.redMu_nu_pow_smul (e := e) (e' - e).toNat hx.2
    rwa [show (((e' - e).toNat : ℤ) + e) = e' by omega] at h2

/-- The filtration is increasing inside the finite-dimensional `K^idx`, hence
eventually constant. -/
theorem exists_redFil_stab (S : Submodule (Poly K) P.Mod) :
    ∃ e₁ : ℤ, ∀ e, e₁ ≤ e → P.redFil S e = P.redFil S e₁ := by
  set g : ℤ → ℕ := fun e => Module.finrank K (P.redFil S e) with hg
  have hbdd : BddAbove (Set.range g) := by
    refine ⟨Fintype.card P.idx, ?_⟩
    rintro _ ⟨e, rfl⟩
    exact (Submodule.finrank_le _).trans (by simp)
  have hne : (Set.range g).Nonempty := ⟨g 0, 0, rfl⟩
  obtain ⟨e₁, he₁⟩ := Nat.sSup_mem hne hbdd
  refine ⟨e₁, fun e he => ?_⟩
  have hrk : g e ≤ g e₁ := he₁ ▸ le_csSup hbdd ⟨e, rfl⟩
  exact (Submodule.eq_of_le_of_finrank_le (P.redFil_mono S he) hrk).symm

/-! ### The presentation map of a homogeneous family -/

/-- `g ↦ ∑ i, g i • elt i`, the presentation map `⨁_i B(-deg i) → F` of a
family, as a `K`-linear map. -/
def combLin {ι : Type} [Fintype ι] (elt : ι → P.Mod) : (ι → Poly K) →ₗ[K] P.Mod :=
  ∑ i, ((LinearMap.toSpanSingleton (Poly K) P.Mod (elt i)).restrictScalars K).comp
    (LinearMap.proj i)

@[simp] theorem combLin_apply {ι : Type} [Fintype ι] (elt : ι → P.Mod) (g : ι → Poly K) :
    P.combLin elt g = ∑ i, g i • elt i := by
  simp [combLin]

/-- On the members of a `B`-basis of `S`, the presentation map is the inverse of
the coordinate map. -/
theorem combLin_basis {ι : Type} [Fintype ι] {S : Submodule (Poly K) P.Mod}
    (w : Module.Basis ι (Poly K) S) (g : ι → Poly K) :
    P.combLin (fun i => ((w i : S) : P.Mod)) g = ((w.equivFun.symm g : S) : P.Mod) := by
  rw [P.combLin_apply, w.equivFun_symm_apply]
  exact (map_sum S.subtype (fun i => g i • w i) Finset.univ).symm

/-- The presentation map of a `B`-linearly independent family is injective. -/
theorem combLin_injective {ι : Type} [Fintype ι] {elt : ι → P.Mod}
    (h : LinearIndependent (Poly K) elt) : Function.Injective (P.combLin elt) := by
  intro g₁ g₂ hg
  rw [P.combLin_apply, P.combLin_apply] at hg
  have h0 : ∑ i, (g₁ i - g₂ i) • elt i = 0 := by
    simp only [sub_smul]
    rw [Finset.sum_sub_distrib, hg, sub_self]
  funext i
  exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 h _ h0 i)

end GradedPresentation

/-- A graded submodule is spanned by its homogeneous elements. -/
theorem GradedPresentation.IsGraded.mem_span {K : Type*} [Field K]
    {P : GradedPresentation K} {S : Submodule (Poly K) P.Mod} (h : P.IsGraded S)
    {f : P.Mod} (hf : f ∈ S) :
    f ∈ Submodule.span (Poly K) (⋃ e : ℤ, ((S : Set P.Mod) ∩ P.piece e)) := by
  obtain ⟨s, hs⟩ := P.exists_sum_proj f
  rw [← hs]
  refine Submodule.sum_mem _ fun e _ => Submodule.subset_span ?_
  exact Set.mem_iUnion.2 ⟨e, h f hf e, P.proj_mem e f⟩

/-! ### Homogeneous bases -/

/-- A **homogeneous `B`-basis** of a graded submodule `S ⊆ F`: the generators
`elt i` are homogeneous of degrees `deg i`, are `B`-linearly independent, and
span `S`.  This is the conclusion of `lem:free` as one named object.

It is the general form of `Pencil.CentralizerBasis`, and it packages the
conjunction produced by `Graded.saturated_free`. -/
structure HomogeneousBasis {K : Type*} [Field K] (P : GradedPresentation K)
    (S : Submodule (Poly K) P.Mod) {ι : Type} [Fintype ι]
    (deg : ι → ℤ) (elt : ι → P.Mod) : Prop where
  /-- The generators lie in `S`. -/
  mem : ∀ i, elt i ∈ S
  /-- The generator `elt i` is homogeneous of degree `deg i`. -/
  homog : ∀ i, elt i ∈ P.piece (deg i)
  /-- The generators are `B`-linearly independent. -/
  linInd : LinearIndependent (Poly K) elt
  /-- The generators span `S`. -/
  span : Submodule.span (Poly K) (Set.range elt) = S

namespace HomogeneousBasis

variable {K : Type*} [Field K] {P : GradedPresentation K}
variable {S : Submodule (Poly K) P.Mod} {ι : Type} [Fintype ι]
variable {deg : ι → ℤ} {elt : ι → P.Mod}

/-- A `B`-basis of `S` whose members are homogeneous *is* a homogeneous basis.
This is the shape `Chain/Multidegree.lean` and `Chain/Conditional.lean` carry
their bases in. -/
theorem of_basis (w : Module.Basis ι (Poly K) S)
    (hw : ∀ i, ((w i : S) : P.Mod) ∈ P.piece (deg i)) :
    HomogeneousBasis P S deg (fun i => ((w i : S) : P.Mod)) where
  mem i := (w i).2
  homog := hw
  linInd := by
    have h := w.linearIndependent.map' (S.subtype) (Submodule.ker_subtype S)
    exact h
  span := by
    have h := congrArg (Submodule.map S.subtype) w.span_eq
    rwa [Submodule.map_span, Submodule.map_top, Submodule.range_subtype,
      ← Set.range_comp] at h

/-- The basis in `Module.Basis` form. -/
theorem exists_basis (H : HomogeneousBasis P S deg elt) :
    ∃ v : Module.Basis ι (Poly K) S, ∀ i, ((v i : S) : P.Mod) = elt i := by
  have hspan : Submodule.span (Poly K) (Set.range (Set.codRestrict elt S H.mem)) = ⊤ := by
    refine Submodule.map_injective_of_injective (Submodule.injective_subtype S) ?_
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp]
    exact H.span
  exact ⟨Module.Basis.mk (H.linInd.codRestrict S H.mem) hspan.ge,
    fun i => by rw [Module.Basis.mk_apply]; rfl⟩

/-- The presentation map of the basis is injective. -/
theorem combLin_injective (H : HomogeneousBasis P S deg elt) :
    Function.Injective (P.combLin elt) :=
  P.combLin_injective H.linInd

/-- **`lem:degree` for a graded submodule**: a submodule with a homogeneous
basis of degrees `deg` has the Hilbert function of the presentation
`⨁_i B(-deg i)`. -/
theorem finrank_sub (H : HomogeneousBasis P S deg elt) (e : ℤ) :
    Module.finrank K (P.sub S e) = ∑ i, (e - deg i + 1).toNat := by
  classical
  have hmap : Submodule.map (P.combLin elt) ((GradedPresentation.of K deg).piece e)
      = P.sub S e := by
    refine le_antisymm ?_ ?_
    · rintro x ⟨g, hg, rfl⟩
      have hg' : ∀ i, g i ∈ Bpiece K (e - deg i) :=
        fun i => by simpa using (GradedPresentation.of K deg).mem_piece.1 hg i
      refine ⟨?_, ?_⟩
      · rw [P.combLin_apply]
        exact Submodule.sum_mem _ fun i _ => S.smul_mem _ (H.mem i)
      · rw [P.combLin_apply]
        refine Submodule.sum_mem _ fun i _ => ?_
        have := P.smul_mem_piece (hg' i) (H.homog i)
        rwa [show e - deg i + deg i = e by ring] at this
    · intro x hx
      obtain ⟨hxS, hxe⟩ := hx
      obtain ⟨w, hw⟩ := H.exists_basis
      set g : ι → Poly K := w.equivFun ⟨x, hxS⟩ with hgdef
      have hgx : P.combLin elt g = x := by
        have h2 : ((w.equivFun.symm g : S) : P.Mod) = x := by
          rw [hgdef, w.equivFun.symm_apply_apply]
        rw [P.combLin_apply,
          Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => by rw [← hw i],
          ← h2, w.equivFun_symm_apply]
        exact (map_sum S.subtype (fun i => g i • w i) Finset.univ).symm
      have hproj : ∀ i, Bproj (e - deg i) (g i) = g i := by
        have h2 : P.proj e (P.combLin elt g)
            = P.combLin elt (fun i => Bproj (e - deg i) (g i)) := by
          rw [P.combLin_apply, P.combLin_apply, map_sum]
          exact Finset.sum_congr rfl fun i _ => P.proj_smul (g i) (H.homog i)
        have h3 : P.combLin elt (fun i => Bproj (e - deg i) (g i)) = P.combLin elt g := by
          rw [← h2, hgx, P.proj_self hxe, ← hgx]
        exact fun i => congrFun (H.combLin_injective h3) i
      refine ⟨g, (GradedPresentation.of K deg).mem_piece.2 fun i => ?_, hgx⟩
      show g i ∈ Bpiece K (e - deg i)
      rw [← hproj i]
      exact Bproj_mem _ _
  rw [← hmap, ← (Submodule.equivMapOfInjective (P.combLin elt) H.combLin_injective
    ((GradedPresentation.of K deg).piece e)).finrank_eq,
    (GradedPresentation.of K deg).finrank_piece]

end HomogeneousBasis

end Height.Graded

end
