import Height.Pencil.Marked
import Height.Pencil.Realized
import Height.Chain.Incidence
import Height.Chain.H1Geometry

/-!
# `thm:h2-conditional`: shifted isotropy implies (H2′)

The paper, `thm:h2-conditional`.  The node of the
chain is `Height.Chain.markedIncidenceBound` (`Chain/Edges.lean`), which
composes the two theorems of this file with `Chain.shiftedIsotropy`.

## What is proved here

`realized_count` (`Pencil/Realized.lean`) is the mathematical core of the theorem — its "Image",
"Kernel" and "Count" paragraphs — as a statement of linear algebra over the
local residue model of `DVR/ResidueModel.lean`:

```
α : T → ⊕_ξ (K⟦u⟧/u^{E ξ})^{⊕2}      (the class map at a tangent-generic point)
im α isotropic for ⊕_ξ ω_ξ           ("Image": (SI) at x₁, x₂; thm:isotropy elsewhere)
dim ker α ≤ dim 𝒩 + 2                ("Kernel": thm:realized-bound)
Σ_ξ 2 E ξ + 2D + 2 Σb ≤ 2 dim Fl     (½ len T = dim Fl − Σb, and D ≤ D_{x_i})
dim 𝒩 = 2 dim Fl + Σb                (thm:realized-bound)
⟹ dim T + D ≤ 3 dim Fl + 2 .
```

`markedIncidenceBound_of_bounds` is that count, read as (H2′) at `(τ, d, N₀)`.

The target of `α` is written as a *single* `residueBlockSpace` over one finite
index: `residueSpaceForm` is by construction the orthogonal sum of its blocks,
so the paper's `uT_{x₁} ⊕ uT_{x₂} ⊕ ⊕_{x ≠ x₁,x₂} T_x` is of that shape,
with `E` the concatenation of `mBlk − 1` at the two marked points
(`uTx`, `OmegaX`) and `mBlk` at the others (`Tx`, `omegaX`).  Componentwise
isotropy implies isotropy for the sum, and the two per-point bounds
`2 dim W + D_x ≤ len_x` and `2 dim Λ_x ≤ len_x` are what would make the
accounting hypothesis `Σ_ξ 2 E ξ + 2D + 2 Σb ≤ 2 dim Fl` true; here they are folded into
`E` and that hypothesis, since the two marked points are produced by the
geometry.

`exists_siVanishing` is the arc bridge: shifted isotropy of the component, as
the predicate `Height.Pencil.ShiftedIsotropy` on the geometry API, is the
coordinate statement `SIVanishing` on a dense open.

## The marked tangent datum

`markedTangentDatum` and `exists_markedRealizedDatum` build the whole numerical
datum of `thm:h2-conditional` — the two-point analogue of
`Chain/H1Geometry.lean`'s `tangentDatum`.  The index is the blocks at `x₁`, the
blocks at `x₂`, then the blocks at the other drop points; the exponents are
`mBlk − 1` on the first two groups and `mBlk` on the third; the class map is
`μ_x` (`muXLin`) on the first two and the ordinary class on the third.

| field of `RealizedDatum.Bounds` | proved by |
|---|---|
| `isotropic` | `residueSpaceForm_mBlkClass_eq_zero`: (SI) at `x₁, x₂`, `thm:isotropy` elsewhere, summed block by block |
| `finrank_ker_le` | `finrank_ker_mBlkClass_le`: `thm:realized-bound` on `{ṫ₁ = ṫ₂ = 0}`, where the shifted classes see what the ordinary ones do; the two `ṫ`-coordinates are the slack `s = 2` |
| `length_le` | `sum_two_mul_mBlkExp_le`: `lem:selfdual-degree` (`selfDualGapStmt`), the per-point accounting `Pencil.sum_two_mul_mBlk_pred_add_DX`, and `D ≤ D_{x_i}` (`Pencil.cOf_sub_cType_le_DX`) |
| `two_dimFl` | `lem:kernel-flag`, definition of `Fl_{τ'}` |
| `affineDim_le` | `dim Ŷ ≤ dim T` — the one hypothesis, the variety half |

## The geometry

`Chain/H2Geometry.lean` proves `exists_siComponents_realizedBounds`, the node's
geometric half, from `exists_markedRealizedDatum_of_arcs` above.
-/

namespace Height.Chain

open Matrix Height.Pencil Height.DVR Height.Steenrod Height.Orbital
open Height.Geometry (MarkedIndex PairIndex SIIndex SIPoint siCoords markedCoords pairCoords
  affineDim)
open Height.Toolbox (cOf)

/-! ### (SI) on a dense open -/

section Vanishing

variable {K : Type} [Field K] {n : ℕ}

/-- The conclusion of shifted isotropy on the dense open `V ∖ V(h)`: the shifted
classes of arc velocities at a point of `V` are `Ω_x`-orthogonal. -/
def SIVanishing (I : Ideal (MvPolynomial (SIIndex (Fin n)) K))
    (h : MvPolynomial (SIIndex (Fin n)) K) : Prop :=
  ∀ z ∈ MvPolynomial.zeroLocus K I, MvPolynomial.eval z h ≠ 0 →
    ∀ m₁ m₂ : MarkedArc I z, siPairing (siCoords.symm z) m₁.a.vel m₂.a.vel m₁.Z m₂.Z = 0

/-- **The arc bridge for (SI)**: `Height.Pencil.ShiftedIsotropy` of the
component, a statement about the `K⟦u⟧`-points of the closed subscheme `V(I)`,
is `SIVanishing` on a dense open of `V(I)` — `Geometry.genericPts_iff` for the
quantifier and `Pencil.siArcEquiv` for the arcs. -/
theorem exists_siVanishing [IsAlgClosed K] {I : Ideal (MvPolynomial (SIIndex (Fin n)) K)}
    [I.IsPrime] (hsi : ShiftedIsotropy I) : ∃ h ∉ I, SIVanishing I h := by
  rw [ShiftedIsotropy, Height.Geometry.genericPts_iff] at hsi
  obtain ⟨h, hh, hmain⟩ := hsi
  refine ⟨h, hh, fun z hz hne m₁ m₂ => ?_⟩
  have hne' : MvPolynomial.aeval z h ≠ 0 := by rwa [MvPolynomial.aeval_eq_eval]
  have hbase : ∀ m : MarkedArc I z,
      ((siArcEquiv I).symm ⟨m.a, m.inLocus⟩ : Height.Geometry.Arc I).base = z := by
    intro m
    rw [base_siArcEquiv_symm, m.base, siCoords.apply_symm_apply]
  have hvel : ∀ m : MarkedArc I z,
      siCoords.symm ((siArcEquiv I).symm ⟨m.a, m.inLocus⟩ : Height.Geometry.Arc I).vel
        = m.a.vel := by
    intro m
    rw [vel_siArcEquiv_symm, siCoords.symm_apply_apply]
  have := hmain z hz hne' _ _ (hbase m₁) (hbase m₂) m₁.Z m₂.Z
    (by rw [hvel m₁]; exact m₁.marked) (by rw [hvel m₂]; exact m₂.marked)
  rwa [hvel m₁, hvel m₂] at this

end Vanishing
/-! ### The marked class map

The two-point analogue of `Chain/H1Geometry.lean`'s `blkClass`: at the two
marked points the class recorded is the *shifted* class `μ_x` of
`lem:marked-shift`, read at the exponents `mBlk − 1`; at the other drop points
it is the ordinary class at `mBlk`, exactly as in (H1).

`μ_x` needs a marking witness for each direction and there is no canonical one,
so one is chosen.  That the choice does not matter is
`Pencil.muX_eq_of_markedWith`, and that the result is *linear* in the direction
is `Pencil.muX_add`, `Pencil.muX_smul`; together they are what makes `muXLin` a
`LinearMap`, and they are what `lem:marked-shift`'s last clause is for. -/

section MarkedClass

variable {K : Type} [Field K] {n : ℕ}

/-- The pencil half of a marked direction. -/
def markedDirPair (v : MarkedIndex (Fin n) → K) : PairIndex (Fin n) → K :=
  fun i => v (Sum.inl i)

/-- The pencil half, as a linear map. -/
def markedDirPairLin : (MarkedIndex (Fin n) → K) →ₗ[K] (PairIndex (Fin n) → K) where
  toFun := markedDirPair
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem markedDirPairLin_apply (v : MarkedIndex (Fin n) → K) :
    markedDirPairLin v = markedDirPair v := rfl

/-- The homogeneous pencil of a marked direction. -/
noncomputable def markedPencil (v : MarkedIndex (Fin n) → K) :
    Matrix (Fin n) (Fin n) (Graded.Poly K) :=
  pencil (pairMatN (markedDirPair v)) (pairMatM (markedDirPair v))

theorem markedPencil_add (v w : MarkedIndex (Fin n) → K) :
    markedPencil (v + w) = markedPencil v + markedPencil w := by
  refine Matrix.ext fun i j => ?_
  simp only [markedPencil, pencil, Matrix.of_apply, Matrix.add_apply, pairMatN_apply,
    pairMatM_apply, markedDirPair, Pi.add_apply, map_add]
  ring

theorem markedPencil_smul (c : K) (v : MarkedIndex (Fin n) → K) :
    markedPencil (c • v) = c • markedPencil v := by
  refine Matrix.ext fun i j => ?_
  simp only [markedPencil, pencil, Matrix.of_apply, Matrix.smul_apply, pairMatN_apply,
    pairMatM_apply, markedDirPair, Pi.smul_apply, smul_eq_mul, map_mul,
    MvPolynomial.smul_eq_C_mul]
  ring

/-- The motion of the `i`-th marked point along a direction. -/
def markedTdot (i : Fin 2) (v : MarkedIndex (Fin n) → K) : K := v (Sum.inr i)

@[simp] theorem markedTdot_add (i : Fin 2) (v w : MarkedIndex (Fin n) → K) :
    markedTdot i (v + w) = markedTdot i v + markedTdot i w := rfl

@[simp] theorem markedTdot_smul (i : Fin 2) (c : K) (v : MarkedIndex (Fin n) → K) :
    markedTdot i (c • v) = c * markedTdot i v := rfl

/-- The marking condition on a whole space of directions at one marked point:
every direction of `T` is marked at `t₀`, with some witness. -/
def IsMarkedOn (N M : Matrix (Fin n) (Fin n) K) (t₀ : K) (i : Fin 2)
    (T : Submodule K (MarkedIndex (Fin n) → K)) : Prop :=
  ∀ v : T, ∃ Z, MarkedWith N M t₀ (markedPencil v.val) (markedTdot i v.val) Z

/-- Additivity of the shifted class along a marked direction, for arbitrary
witnesses.  The witnesses must be *variables*: rewriting `↑(v + w)` inside a
hypothesis whose statement is about `(hT (v + w)).choose` has an ill-typed
motive, since the type of that witness mentions `↑(v + w)`. -/
private theorem muX_marked_add {N M : Matrix (Fin n) (Fin n) K} {t₀ : K} {i : Fin 2}
    {T : Submodule K (MarkedIndex (Fin n) → K)} (v w : T)
    {Zv Zw Zvw : Matrix (Fin n) (Fin n) K}
    (hv : MarkedWith N M t₀ (markedPencil v.val) (markedTdot i v.val) Zv)
    (hw : MarkedWith N M t₀ (markedPencil w.val) (markedTdot i w.val) Zw)
    (hvw : MarkedWith N M t₀ (markedPencil ((v + w : T) : MarkedIndex (Fin n) → K))
      (markedTdot i ((v + w : T) : MarkedIndex (Fin n) → K)) Zvw) :
    muX N M t₀ (markedPencil ((v + w : T) : MarkedIndex (Fin n) → K))
        (markedTdot i ((v + w : T) : MarkedIndex (Fin n) → K)) Zvw
      = muX N M t₀ (markedPencil v.val) (markedTdot i v.val) Zv
        + muX N M t₀ (markedPencil w.val) (markedTdot i w.val) Zw := by
  have hcoe : ((v + w : T) : MarkedIndex (Fin n) → K) = v.val + w.val := rfl
  rw [hcoe, markedPencil_add, markedTdot_add] at hvw ⊢
  exact muX_add hv hw hvw

/-- Homogeneity of the shifted class along a marked direction, for arbitrary
witnesses. -/
private theorem muX_marked_smul {N M : Matrix (Fin n) (Fin n) K} {t₀ : K} {i : Fin 2}
    {T : Submodule K (MarkedIndex (Fin n) → K)} (c : K) (v : T)
    {Zv Zcv : Matrix (Fin n) (Fin n) K}
    (hv : MarkedWith N M t₀ (markedPencil v.val) (markedTdot i v.val) Zv)
    (hcv : MarkedWith N M t₀ (markedPencil ((c • v : T) : MarkedIndex (Fin n) → K))
      (markedTdot i ((c • v : T) : MarkedIndex (Fin n) → K)) Zcv) :
    muX N M t₀ (markedPencil ((c • v : T) : MarkedIndex (Fin n) → K))
        (markedTdot i ((c • v : T) : MarkedIndex (Fin n) → K)) Zcv
      = c • muX N M t₀ (markedPencil v.val) (markedTdot i v.val) Zv := by
  have hcoe : ((c • v : T) : MarkedIndex (Fin n) → K) = c • v.val := rfl
  rw [hcoe, markedPencil_smul, markedTdot_smul, ← smul_eq_mul] at hcv ⊢
  exact muX_smul c hv hcv

/-- **The shifted class map at a marked point**, as a linear map on the whole
space of directions: `v ↦ μ_x(Q̇(v), ṫ_i(v))`, with a chosen witness.

Linearity is `Pencil.muX_add` and `Pencil.muX_smul` applied to *some* witness of
the sum and of the multiple, which is legitimate exactly because
`Pencil.muX_eq_of_markedWith` makes the value witness-independent.  This is what
`lem:marked-shift`'s last clause is for: without it the map cannot be built. -/
noncomputable def muXLin (N M : Matrix (Fin n) (Fin n) K) (t₀ : K) (i : Fin 2)
    {T : Submodule K (MarkedIndex (Fin n) → K)} (hT : IsMarkedOn N M t₀ i T) :
    T →ₗ[K] uTx N M t₀ where
  toFun v := muX N M t₀ (markedPencil v.val) (markedTdot i v.val) (hT v).choose
  map_add' v w := muX_marked_add v w (hT v).choose_spec (hT w).choose_spec (hT (v + w)).choose_spec
  map_smul' c v := muX_marked_smul c v (hT v).choose_spec (hT (c • v)).choose_spec

/-- The value of the class map at any witness: the choice does not matter. -/
theorem muXLin_apply (N M : Matrix (Fin n) (Fin n) K) (t₀ : K) (i : Fin 2)
    {T : Submodule K (MarkedIndex (Fin n) → K)} (hT : IsMarkedOn N M t₀ i T) (v : T)
    {Z : Matrix (Fin n) (Fin n) K}
    (hZ : MarkedWith N M t₀ (markedPencil v.val) (markedTdot i v.val) Z) :
    muXLin N M t₀ i hT v = muX N M t₀ (markedPencil v.val) (markedTdot i v.val) Z :=
  muX_eq_of_markedWith (hT v).choose_spec hZ

end MarkedClass

/-! ### The marked tangent datum

The two-point analogue of `Chain/H1Geometry.lean`'s `tangentDatum`.  The index
is split as a sum rather than a single sigma so that the exponents are given by
`Sum.elim` and no dependent `if` appears: the blocks at `x₁`, the blocks at
`x₂`, then the blocks at the remaining drop points. -/

section MarkedDatum

variable {K : Type} [Field K] {n : ℕ}

/-- The block index of the marked class map: the blocks at the two marked
points, then the blocks at the other drop points. -/
abbrev mBlkIdx (N M : Matrix (Fin n) (Fin n) K) (t₁ t₂ : K) (F : Finset K) : Type :=
  (txData N M t₁).Blocks ⊕ (txData N M t₂).Blocks ⊕
    (Σ x : {t : K // t ∈ F}, (txData N M x.val).Blocks)

/-- The exponents: `mBlk − 1` at the two marked points (`u T_x`, `Ω_x`), `mBlk`
at the others (`T_x`, `ω_x`). -/
noncomputable def mBlkExp (N M : Matrix (Fin n) (Fin n) K) (t₁ t₂ : K) (F : Finset K) :
    mBlkIdx N M t₁ t₂ F → ℕ :=
  Sum.elim (fun b => (txData N M t₁).mBlk b - 1)
    (Sum.elim (fun b => (txData N M t₂).mBlk b - 1)
      (fun s => (txData N M s.1.val).mBlk s.2))

/-- The ordinary class map at one point, on marked directions. -/
noncomputable def markedBlockClass (N M : Matrix (Fin n) (Fin n) K) (t₀ : K)
    (T : Submodule K (MarkedIndex (Fin n) → K)) :
    T →ₗ[K] (txData N M t₀).torsion :=
  ((txData N M t₀).blockClass (txData N M t₀).mBlk).comp
    ((patLin t₀).comp (markedDirPairLin.comp T.subtype))

theorem markedBlockClass_apply (N M : Matrix (Fin n) (Fin n) K) (t₀ : K)
    {T : Submodule K (MarkedIndex (Fin n) → K)} (v : T) :
    markedBlockClass N M t₀ T v
      = (txData N M t₀).blockClass (txData N M t₀).mBlk
          (Qat (markedPencil v.val) t₀) := rfl

/-- **The marked class map** `α` of `thm:h2-conditional`, before reindexing:
the shifted class at each of the two marked points, the ordinary class at every
other drop point. -/
noncomputable def mBlkClass (N M : Matrix (Fin n) (Fin n) K) (t₁ t₂ : K) (F : Finset K)
    {T : Submodule K (MarkedIndex (Fin n) → K)}
    (h₁ : IsMarkedOn N M t₁ 0 T) (h₂ : IsMarkedOn N M t₂ 1 T) :
    T →ₗ[K] residueBlockSpace K (mBlkExp N M t₁ t₂ F) :=
  LinearMap.pi fun s =>
    match s with
    | Sum.inl b => (LinearMap.proj b).comp (muXLin N M t₁ 0 h₁)
    | Sum.inr (Sum.inl b) => (LinearMap.proj b).comp (muXLin N M t₂ 1 h₂)
    | Sum.inr (Sum.inr x) => (LinearMap.proj x.2).comp (markedBlockClass N M x.1.val T)

@[simp] theorem mBlkClass_inl (N M : Matrix (Fin n) (Fin n) K) (t₁ t₂ : K) (F : Finset K)
    {T : Submodule K (MarkedIndex (Fin n) → K)}
    (h₁ : IsMarkedOn N M t₁ 0 T) (h₂ : IsMarkedOn N M t₂ 1 T) (v : T)
    (b : (txData N M t₁).Blocks) :
    mBlkClass N M t₁ t₂ F h₁ h₂ v (Sum.inl b) = muXLin N M t₁ 0 h₁ v b := rfl

@[simp] theorem mBlkClass_inr_inl (N M : Matrix (Fin n) (Fin n) K) (t₁ t₂ : K) (F : Finset K)
    {T : Submodule K (MarkedIndex (Fin n) → K)}
    (h₁ : IsMarkedOn N M t₁ 0 T) (h₂ : IsMarkedOn N M t₂ 1 T) (v : T)
    (b : (txData N M t₂).Blocks) :
    mBlkClass N M t₁ t₂ F h₁ h₂ v (Sum.inr (Sum.inl b)) = muXLin N M t₂ 1 h₂ v b := rfl

@[simp] theorem mBlkClass_inr_inr (N M : Matrix (Fin n) (Fin n) K) (t₁ t₂ : K) (F : Finset K)
    {T : Submodule K (MarkedIndex (Fin n) → K)}
    (h₁ : IsMarkedOn N M t₁ 0 T) (h₂ : IsMarkedOn N M t₂ 1 T) (v : T)
    (x : Σ x : {t : K // t ∈ F}, (txData N M x.val).Blocks) :
    mBlkClass N M t₁ t₂ F h₁ h₂ v (Sum.inr (Sum.inr x))
      = markedBlockClass N M x.1.val T v x.2 := rfl

/-- **(SI) in the form the count consumes**: the shifted classes of the
directions of `T` at the marked point `t₀` are `Ω_x`-isotropic.  Quantified over
arbitrary marking witnesses, as `Pencil.siPairing` and `SIVanishing` are — by
`Pencil.muX_eq_of_markedWith` the condition does not depend on them. -/
def MarkedIsotropic (N M : Matrix (Fin n) (Fin n) K) (t₀ : K) (i : Fin 2)
    (T : Submodule K (MarkedIndex (Fin n) → K)) : Prop :=
  ∀ (v w : T) (Zv Zw : Matrix (Fin n) (Fin n) K),
    MarkedWith N M t₀ (markedPencil v.val) (markedTdot i v.val) Zv →
    MarkedWith N M t₀ (markedPencil w.val) (markedTdot i w.val) Zw →
    OmegaX N M t₀ (muX N M t₀ (markedPencil v.val) (markedTdot i v.val) Zv)
      (muX N M t₀ (markedPencil w.val) (markedTdot i w.val) Zw) = 0

/-- A space of marked directions whose pencil half is realised. -/
def IsMarkedRealized (N M : Matrix (Fin n) (Fin n) K)
    (T : Submodule K (MarkedIndex (Fin n) → K)) : Prop :=
  ∀ v : T, IsRealizedDir N M (pairMatN (markedDirPair v.val)) (pairMatM (markedDirPair v.val))

/-- **`thm:isotropy` for the marked class map**: (SI) at the two marked points
and `thm:isotropy` at the other drop points make the image of `α` isotropic for
the residue form on the concatenated exponents.

`residueSpaceForm` is by construction the orthogonal sum of its blocks, so the
three groups of indices contribute separately: the two marked groups by
hypothesis, the rest by `residueSpaceForm_blockClass_eq_zero`. -/
theorem residueSpaceForm_mBlkClass_eq_zero
    {N M : Matrix (Fin n) (Fin n) K} {t₁ t₂ : K} {F : Finset K}
    {T : Submodule K (MarkedIndex (Fin n) → K)}
    (h₁ : IsMarkedOn N M t₁ 0 T) (h₂ : IsMarkedOn N M t₂ 1 T)
    (hnilP : pencil N M ^ n = 0) (hreal : IsMarkedRealized N M T)
    (hSI₁ : MarkedIsotropic N M t₁ 0 T) (hSI₂ : MarkedIsotropic N M t₂ 1 T)
    (v w : T) :
    residueSpaceForm (mBlkExp N M t₁ t₂ F)
      (mBlkClass N M t₁ t₂ F h₁ h₂ v) (mBlkClass N M t₁ t₂ F h₁ h₂ w) = 0 := by
  rw [residueSpaceForm_eq_sum, Fintype.sum_sum_type, Fintype.sum_sum_type]
  have hA : ∑ b : (txData N M t₁).Blocks,
      blockResidueForm K (mBlkExp N M t₁ t₂ F (Sum.inl b))
        (mBlkClass N M t₁ t₂ F h₁ h₂ v (Sum.inl b))
        (mBlkClass N M t₁ t₂ F h₁ h₂ w (Sum.inl b)) = 0 :=
    hSI₁ v w _ _ (h₁ v).choose_spec (h₁ w).choose_spec
  have hB : ∑ b : (txData N M t₂).Blocks,
      blockResidueForm K (mBlkExp N M t₁ t₂ F (Sum.inr (Sum.inl b)))
        (mBlkClass N M t₁ t₂ F h₁ h₂ v (Sum.inr (Sum.inl b)))
        (mBlkClass N M t₁ t₂ F h₁ h₂ w (Sum.inr (Sum.inl b))) = 0 :=
    hSI₂ v w _ _ (h₂ v).choose_spec (h₂ w).choose_spec
  have hC : ∑ x : Σ x : {t : K // t ∈ F}, (txData N M x.val).Blocks,
      blockResidueForm K (mBlkExp N M t₁ t₂ F (Sum.inr (Sum.inr x)))
        (mBlkClass N M t₁ t₂ F h₁ h₂ v (Sum.inr (Sum.inr x)))
        (mBlkClass N M t₁ t₂ F h₁ h₂ w (Sum.inr (Sum.inr x))) = 0 := by
    rw [Fintype.sum_sigma]
    refine Finset.sum_eq_zero fun x _ => ?_
    exact residueSpaceForm_blockClass_eq_zero hnilP x.val (hreal v) (hreal w)
  rw [hA, hB, hC, add_zero, add_zero]

/-- The two marked-point motions of a direction, as a linear map. -/
def markedTdotLin : (MarkedIndex (Fin n) → K) →ₗ[K] (Fin 2 → K) where
  toFun v := fun i => markedTdot i v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The pencil half of a direction of `T`, as a pair of matrices: what
`Pencil.realizedDimStmt` quantifies over. -/
noncomputable def markedMatLin (T : Submodule K (MarkedIndex (Fin n) → K)) :
    T →ₗ[K] Matrix (Fin n) (Fin n) K × Matrix (Fin n) (Fin n) K :=
  pairMatEquiv.toLinearMap.comp (markedDirPairLin.comp T.subtype)

@[simp] theorem markedMatLin_apply (T : Submodule K (MarkedIndex (Fin n) → K)) (v : T) :
    markedMatLin T v = (pairMatN (markedDirPair v.val), pairMatM (markedDirPair v.val)) := rfl

/-- On a direction that does not move the marked point, a vanishing *shifted*
class forces the vanishing of the *ordinary* class — `Pencil.muX_eq_zero_iff_blockClass`,
read through the chosen witness. -/
private theorem blockClass_eq_zero_of_muXLin {N M : Matrix (Fin n) (Fin n) K} {t₀ : K}
    {i : Fin 2} {T : Submodule K (MarkedIndex (Fin n) → K)} (hT : IsMarkedOn N M t₀ i T) (v : T)
    (htd : markedTdot i v.val = 0) (h0 : muXLin N M t₀ i hT v = 0) :
    (txData N M t₀).blockClass (txData N M t₀).mBlk (Qat (markedPencil v.val) t₀) = 0 := by
  obtain ⟨Z, hZ⟩ := hT v
  have hval : muXLin N M t₀ i hT v
      = muX N M t₀ (markedPencil v.val) (markedTdot i v.val) Z := muXLin_apply N M t₀ i hT v hZ
  rw [htd] at hZ hval
  rw [hval] at h0
  exact (muX_eq_zero_iff_blockClass hZ).mp h0

/-- **The kernel half of `thm:h2-conditional`**: the kernel of the marked class
map is, up to the two `ṫ`-coordinates, a space of local commutators, so
`thm:realized-bound` applies to it with a slack of `2`.

This is where the slack `s = 2` of `RealizedDatum.Bounds` comes from, and why it
is `2` and not more: on `{ṫ₁ = ṫ₂ = 0}` the shifted classes see exactly what the
ordinary ones do (`blockClass_eq_zero_of_muXLin`), so that subspace consists of
local commutators; and it is cut out of the kernel by a linear map to `K²`. -/
theorem finrank_ker_mBlkClass_le [IsAlgClosed K] [Infinite K]
    {N M : Matrix (Fin n) (Fin n) K} {τ : Nat.Partition n} {t₁ t₂ : K} {F : Finset K}
    (hnil : NilpotentPencil N M) (hgen : GenericType N M τ) (hMty : HasType M τ)
    (hF : ∀ t₀, t₀ ≠ t₁ → t₀ ≠ t₂ → t₀ ∉ F → ¬ IsDropPoint N M t₀ τ)
    {ι : Type} [Fintype ι] {b : ι → ℤ} {u : ι → (Fin (n * n) → Graded.Poly K)}
    (hbasis : CentralizerBasis N M b u)
    {T : Submodule K (MarkedIndex (Fin n) → K)}
    (h₁ : IsMarkedOn N M t₁ 0 T) (h₂ : IsMarkedOn N M t₂ 1 T)
    (hreal : IsMarkedRealized N M T) :
    (Module.finrank K (LinearMap.ker (mBlkClass N M t₁ t₂ F h₁ h₂)) : ℤ) + cType τ
      ≤ n * n + ∑ i, b i + 2 := by
  classical
  set L : T →ₗ[K] (Fin 2 → K) := markedTdotLin.comp T.subtype with hLdef
  set Kα := LinearMap.ker (mBlkClass N M t₁ t₂ F h₁ h₂) with hKαdef
  set W := Kα ⊓ LinearMap.ker L with hWdef
  -- the two `ṫ`-coordinates cut `W` out of the kernel
  have hsplit : Module.finrank K (Kα.map L) + Module.finrank K W = Module.finrank K Kα := by
    rw [hWdef]; exact Height.Toolbox.finrank_map_add_finrank_inf_ker L Kα
  have hle2 : Module.finrank K (Kα.map L) ≤ 2 := by
    have h := Submodule.finrank_le (Kα.map L)
    simpa using h
  -- the drop points, with the two marked ones adjoined
  have hF' : ∀ t₀ ∉ insert t₁ (insert t₂ F), ¬ IsDropPoint N M t₀ τ := by
    intro t₀ ht₀
    simp only [Finset.mem_insert, not_or] at ht₀
    exact hF t₀ ht₀.1 ht₀.2.1 ht₀.2.2
  -- every direction of `W` is a local commutator
  have hloc : ∀ p ∈ W.map (markedMatLin T), IsLocalCommutator N M (pencil p.1 p.2) := by
    rintro _ ⟨v, hv, rfl⟩
    have hvα : mBlkClass N M t₁ t₂ F h₁ h₂ v = 0 := hv.1
    have hvL : ∀ i, markedTdot i v.val = 0 := by
      intro i
      have h : L v = 0 := hv.2
      exact congrFun h i
    refine isLocalCommutator_of_blockClass hnil hgen hMty hF' (hreal v).commutator ?_
    intro t₀ ht₀
    rcases Finset.mem_insert.mp ht₀ with rfl | ht₀'
    · exact blockClass_eq_zero_of_muXLin h₁ v (hvL 0) (funext fun c => congrFun hvα (Sum.inl c))
    rcases Finset.mem_insert.mp ht₀' with rfl | ht₀''
    · exact blockClass_eq_zero_of_muXLin h₂ v (hvL 1)
        (funext fun c => congrFun hvα (Sum.inr (Sum.inl c)))
    · exact funext fun c => congrFun hvα (Sum.inr (Sum.inr ⟨⟨t₀, ht₀''⟩, c⟩))
  -- on `W` the pencil half is injective, the `ṫ`-coordinates being zero
  have hinj : (W ⊓ LinearMap.ker (markedMatLin T) : Submodule K T) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro v ⟨hvW, hvker⟩
    have hvL : ∀ i, markedTdot i v.val = 0 := by
      intro i
      have h : L v = 0 := hvW.2
      exact congrFun h i
    have hmat : markedMatLin T v = 0 := hvker
    refine Subtype.ext (funext fun x => ?_)
    match x with
    | Sum.inl (Sum.inl ij) =>
        exact congrFun (congrFun (congrArg Prod.fst hmat) ij.1) ij.2
    | Sum.inl (Sum.inr ij) =>
        exact congrFun (congrFun (congrArg Prod.snd hmat) ij.1) ij.2
    | Sum.inr i => exact hvL i
  have hrank : Module.finrank K (W.map (markedMatLin T)) = Module.finrank K W := by
    have h := Height.Toolbox.finrank_map_add_finrank_inf_ker (markedMatLin T) W
    rw [hinj, finrank_bot, add_zero] at h
    exact h
  have hdim := realizedDimStmt N M τ hnil hgen b u hbasis _ hloc
  rw [hrank] at hdim
  omega


/-- **The accounting of `thm:h2-conditional`** (`length_le`): the concatenated
exponents, the defect `D` at the two marked points and the basis degrees fit
inside `2 dim Fl_{τ'}`.

The two marked groups contribute `len_{x_i} − D_{x_i}` each
(`Pencil.sum_two_mul_mBlk_pred_add_DX`), the rest contribute `∑_{x ∈ F} len_x`,
`lem:selfdual-degree` (`Pencil.selfDualGapStmt`) says the total of all `len_x`
plus `2 ∑ b` is `2 dim Fl_{τ'}`, and `D ≤ D_{x_i}`
(`Pencil.cOf_sub_cType_le_DX`) absorbs the two defects. -/
theorem sum_two_mul_mBlkExp_le [IsAlgClosed K] [Infinite K]
    {N M N₀ : Matrix (Fin n) (Fin n) K} {τ : Nat.Partition n} {t₁ t₂ : K} {F : Finset K}
    (hnil : NilpotentPencil N M) (hgen : GenericType N M τ) (hMty : HasType M τ)
    (hne : t₁ ≠ t₂) (ht₁ : t₁ ∉ F) (ht₂ : t₂ ∉ F)
    (hF : ∀ t₀, t₀ ≠ t₁ → t₀ ≠ t₂ → t₀ ∉ F → ¬ IsDropPoint N M t₀ τ)
    {ι : Type} [Fintype ι] {b : ι → ℤ} {u : ι → (Fin (n * n) → Graded.Poly K)}
    (hbasis : CentralizerBasis N M b u)
    (hN₀ : IsNilpotent N₀)
    (hm₁ : N + t₁ • M ∈ orbitClosure N₀) (hm₂ : N + t₂ • M ∈ orbitClosure N₀) :
    (∑ ξ : mBlkIdx N M t₁ t₂ F, 2 * mBlkExp N M t₁ t₂ F ξ)
        + 2 * (cOf N₀ - cType τ) + 2 * (∑ i, b i).toNat ≤ 2 * dimFl τ := by
  classical
  -- the three groups of indices
  have hexp : (∑ ξ : mBlkIdx N M t₁ t₂ F, 2 * mBlkExp N M t₁ t₂ F ξ)
      = (∑ c : (txData N M t₁).Blocks, 2 * ((txData N M t₁).mBlk c - 1))
        + ((∑ c : (txData N M t₂).Blocks, 2 * ((txData N M t₂).mBlk c - 1))
          + ∑ t₀ ∈ F, lenX N M t₀) := by
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
    congr 1
    congr 1
    rw [Fintype.sum_sigma, ← Finset.sum_coe_sort F (fun t₀ => lenX N M t₀)]
    rfl
  have hacc₁ := Pencil.sum_two_mul_mBlk_pred_add_DX N M t₁
  have hacc₂ := Pencil.sum_two_mul_mBlk_pred_add_DX N M t₂
  -- `lem:selfdual-degree` over the drop points, the two marked ones adjoined
  have hmem₂ : t₂ ∉ F := ht₂
  have hmem₁ : t₁ ∉ insert t₂ F := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨hne, ht₁⟩
  have hsplit : ∑ t₀ ∈ insert t₁ (insert t₂ F), lenX N M t₀
      = lenX N M t₁ + (lenX N M t₂ + ∑ t₀ ∈ F, lenX N M t₀) := by
    rw [Finset.sum_insert hmem₁, Finset.sum_insert hmem₂]
  have hgap := selfDualGapStmt N M τ hnil hgen hMty b u hbasis (insert t₁ (insert t₂ F))
    (fun t₀ hd => by
      by_contra hc
      simp only [Finset.mem_insert, not_or] at hc
      exact hF t₀ hc.1 hc.2.1 hc.2.2 hd)
  rw [hsplit] at hgap
  -- `D ≤ D_x` at each marked point
  have hD₁ := Pencil.cOf_sub_cType_le_DX N M N₀ τ t₁ hnil hgen hN₀ hm₁
  have hD₂ := Pencil.cOf_sub_cType_le_DX N M N₀ τ t₂ hnil hgen hN₀ hm₂
  have hbnn : (0 : ℤ) ≤ ∑ i, b i := centralizerBasis_sum_nonneg hbasis
  have hcast : (((∑ i, b i).toNat : ℕ) : ℤ) = ∑ i, b i := Int.toNat_of_nonneg hbnn
  rw [hexp]
  omega


/-- **The pencil half of `thm:h2-conditional`.**  At a nilpotent pencil `(N, M)`
of generic type `τ` whose member at infinity has type `τ`, with two distinct
marked parameters at which the members are degenerations of `N₀`, and a space
`T` of marked realised directions on which (SI) holds, the whole numerical datum
of `thm:h2-conditional` exists: the concatenated exponents `E` — `mBlk − 1` at
the two marked points and `mBlk` elsewhere — the class map `α`, the isotropy of
its image, the bound on its kernel with slack `2`, and the accounting.

The two-point analogue of `Chain/H1Geometry.lean`'s `tangentDatum`; it is
everything `RealizedDatum.Bounds` asks for except `affineDim_le` (the variety
half) and `two_dimFl` (the definition of `Fl_{τ'}`). -/
theorem markedTangentDatum [IsAlgClosed K] [Infinite K]
    {N M N₀ : Matrix (Fin n) (Fin n) K} {τ : Nat.Partition n} {t₁ t₂ : K}
    (hnil : NilpotentPencil N M) (hgen : GenericType N M τ) (hMty : HasType M τ)
    (hne : t₁ ≠ t₂) (hN₀ : IsNilpotent N₀)
    (hm₁ : N + t₁ • M ∈ orbitClosure N₀) (hm₂ : N + t₂ • M ∈ orbitClosure N₀)
    (T : Submodule K (MarkedIndex (Fin n) → K))
    (hreal : IsMarkedRealized N M T)
    (h₁ : IsMarkedOn N M t₁ 0 T) (h₂ : IsMarkedOn N M t₂ 1 T)
    (hSI₁ : MarkedIsotropic N M t₁ 0 T) (hSI₂ : MarkedIsotropic N M t₂ 1 T) :
    ∃ (m : ℕ) (E : Fin m → ℕ) (α : T →ₗ[K] residueBlockSpace K E) (sumb : ℕ),
      (∀ x ∈ LinearMap.range α, ∀ y ∈ LinearMap.range α, residueSpaceForm E x y = 0) ∧
        Module.finrank K (LinearMap.ker α) ≤ 2 * dimFl τ + sumb + 2 ∧
        (∑ ξ, 2 * E ξ) + 2 * (cOf N₀ - cType τ) + 2 * sumb ≤ 2 * dimFl τ := by
  classical
  obtain ⟨F₀, hF₀⟩ := finite_dropPoints hgen
  obtain ⟨ι₀, hι₀, b, u, hbasis⟩ := exists_centralizerBasis N M
  set F := (F₀.erase t₁).erase t₂ with hFdef
  have ht₁ : t₁ ∉ F := by simp [hFdef, Finset.mem_erase]
  have ht₂ : t₂ ∉ F := by simp [hFdef, Finset.mem_erase]
  have hF : ∀ t₀, t₀ ≠ t₁ → t₀ ≠ t₂ → t₀ ∉ F → ¬ IsDropPoint N M t₀ τ := by
    intro t₀ hn₁ hn₂ hnF
    refine hF₀ t₀ fun hmem => hnF ?_
    simp [hFdef, Finset.mem_erase, hn₁, hn₂, hmem]
  have hnilP : pencil N M ^ n = 0 := pencil_pow_eq_zero_of_nilpotentPencil hnil
  obtain ⟨σ⟩ : Nonempty (Fin (Fintype.card (mBlkIdx N M t₁ t₂ F)) ≃ mBlkIdx N M t₁ t₂ F) :=
    ⟨(Fintype.equivFin (mBlkIdx N M t₁ t₂ F)).symm⟩
  have hreixinj : Function.Injective
      (LinearMap.pi (fun ξ : Fin (Fintype.card (mBlkIdx N M t₁ t₂ F)) =>
        LinearMap.proj (R := K) (φ := fun s : mBlkIdx N M t₁ t₂ F =>
          blockQuot K (mBlkExp N M t₁ t₂ F s) × blockQuot K (mBlkExp N M t₁ t₂ F s)) (σ ξ))) := by
    intro x y hxy
    funext s
    obtain ⟨ξ, rfl⟩ := σ.surjective s
    exact congrFun hxy ξ
  have hbnn : (0 : ℤ) ≤ ∑ i, b i := centralizerBasis_sum_nonneg hbasis
  have hcast : (((∑ i, b i).toNat : ℕ) : ℤ) = ∑ i, b i := Int.toNat_of_nonneg hbnn
  refine ⟨Fintype.card (mBlkIdx N M t₁ t₂ F), fun ξ => mBlkExp N M t₁ t₂ F (σ ξ),
    (LinearMap.pi fun ξ => LinearMap.proj (σ ξ)) ∘ₗ mBlkClass N M t₁ t₂ F h₁ h₂,
    (∑ i, b i).toNat, ?_, ?_, ?_⟩
  · -- the image is isotropic: (SI) at the two marked points, `thm:isotropy` elsewhere
    rintro x ⟨v, rfl⟩ y ⟨w, rfl⟩
    set f : mBlkIdx N M t₁ t₂ F → K := fun s =>
      blockResidueForm K (mBlkExp N M t₁ t₂ F s)
        (mBlkClass N M t₁ t₂ F h₁ h₂ v s) (mBlkClass N M t₁ t₂ F h₁ h₂ w s) with hf
    have key : ∑ s : mBlkIdx N M t₁ t₂ F, f s = 0 :=
      residueSpaceForm_mBlkClass_eq_zero h₁ h₂ hnilP hreal hSI₁ hSI₂ v w
    have h2 : ∑ ξ : Fin (Fintype.card (mBlkIdx N M t₁ t₂ F)), f (σ ξ) = 0 := by
      rw [Equiv.sum_comp σ f]; exact key
    exact h2
  · -- the kernel: the reindexing is injective, then `finrank_ker_mBlkClass_le`
    have hker : LinearMap.ker ((LinearMap.pi fun ξ => LinearMap.proj (σ ξ)) ∘ₗ
        mBlkClass N M t₁ t₂ F h₁ h₂) = LinearMap.ker (mBlkClass N M t₁ t₂ F h₁ h₂) := by
      refine le_antisymm (fun v hv => ?_) (fun v hv => ?_)
      · exact hreixinj (by rw [map_zero]; exact hv)
      · show _ = 0
        rw [LinearMap.comp_apply, show mBlkClass N M t₁ t₂ F h₁ h₂ v = 0 from hv, map_zero]
    rw [hker]
    have h := finrank_ker_mBlkClass_le hnil hgen hMty hF hbasis h₁ h₂ hreal
    have hc := cType_le τ
    have hd := two_dimFl τ
    omega
  · -- the accounting
    have hsum : ∑ ξ : Fin (Fintype.card (mBlkIdx N M t₁ t₂ F)),
        2 * mBlkExp N M t₁ t₂ F (σ ξ)
        = ∑ s : mBlkIdx N M t₁ t₂ F, 2 * mBlkExp N M t₁ t₂ F s :=
      Equiv.sum_comp σ (fun s => 2 * mBlkExp N M t₁ t₂ F s)
    rw [hsum]
    exact sum_two_mul_mBlkExp_le hnil hgen hMty hne ht₁ ht₂ hF hbasis hN₀ hm₁ hm₂


/-- **The realised datum of `thm:h2-conditional`.**  `markedTangentDatum`
packaged as a `RealizedDatum` with its `Bounds`: everything the count consumes,
with only the variety half left as a hypothesis.

What remains of `exists_siComponents_realizedBounds` after this is therefore
pure geometry: produce the two single-point incidences as `SIComponent`s, a
tangent-generic point of a component of the cone `Ŷ` with its tangent space `T`,
the marking and realisedness of `T` there, and `dim Ŷ ≤ dim T`. -/
theorem exists_markedRealizedDatum [IsAlgClosed K] [Infinite K]
    {N M N₀ : Matrix (Fin n) (Fin n) K} {τ : Nat.Partition n} {t₁ t₂ : K}
    {S : Set (MarkedIndex (Fin n) → K)}
    (hnil : NilpotentPencil N M) (hgen : GenericType N M τ) (hMty : HasType M τ)
    (hne : t₁ ≠ t₂) (hN₀ : IsNilpotent N₀)
    (hm₁ : N + t₁ • M ∈ orbitClosure N₀) (hm₂ : N + t₂ • M ∈ orbitClosure N₀)
    (T : Submodule K (MarkedIndex (Fin n) → K))
    (hreal : IsMarkedRealized N M T)
    (h₁ : IsMarkedOn N M t₁ 0 T) (h₂ : IsMarkedOn N M t₂ 1 T)
    (hSI₁ : MarkedIsotropic N M t₁ 0 T) (hSI₂ : MarkedIsotropic N M t₂ 1 T)
    (haff : affineDim S ≤ ((Module.finrank K T : ℕ) : WithBot ℕ∞)) :
    ∃ R : RealizedDatum K (MarkedIndex (Fin n)),
      R.Bounds τ (cOf N₀ - cType τ) 2 S := by
  obtain ⟨m, E, α, sumb, hiso, hker, hlen⟩ :=
    markedTangentDatum hnil hgen hMty hne hN₀ hm₁ hm₂ T hreal h₁ h₂ hSI₁ hSI₂
  exact ⟨⟨m, E, T, α, dimFl τ, sumb⟩, hiso, hker, hlen, two_dimFl τ, haff⟩


/-! ### (SI) transported to the two-point incidence -/

/-- **(SI) becomes `MarkedIsotropic`.**  Shifted isotropy of a single-point
component, in its coordinate form `SIVanishing` at a point `z` of the dense
open, gives the isotropy hypothesis of `markedTangentDatum` for a space `T` of
directions of the two-point incidence — provided every direction of `T` is the
velocity of a marked arc of the component at `z`.

The witnesses need not match: the arc carries its own, and
`Pencil.muX_eq_of_markedWith` says the shifted class does not depend on it.
That is the second use of `lem:marked-shift`'s last clause, after the
construction of `muXLin`. -/
theorem markedIsotropic_of_siVanishing
    {I : Ideal (MvPolynomial (SIIndex (Fin n)) K)} {h : MvPolynomial (SIIndex (Fin n)) K}
    (hSI : SIVanishing I h) {z : SIIndex (Fin n) → K}
    (hz : z ∈ MvPolynomial.zeroLocus K I) (hzh : MvPolynomial.eval z h ≠ 0)
    {N M : Matrix (Fin n) (Fin n) K} {t₀ : K} (hq : siCoords.symm z = (N, M, t₀))
    {T : Submodule K (MarkedIndex (Fin n) → K)} {i : Fin 2}
    (harc : ∀ v : T, ∃ m : MarkedArc I z,
      m.a.vel = (pairMatN (markedDirPair v.val), pairMatM (markedDirPair v.val),
        markedTdot i v.val)) :
    MarkedIsotropic N M t₀ i T := by
  intro v w Zv Zw hZv hZw
  obtain ⟨m₁, hm₁⟩ := harc v
  obtain ⟨m₂, hm₂⟩ := harc w
  have hpair : OmegaX N M t₀
      (muX N M t₀ (markedPencil v.val) (markedTdot i v.val) m₁.Z)
      (muX N M t₀ (markedPencil w.val) (markedTdot i w.val) m₂.Z) = 0 := by
    have hs := hSI z hz hzh m₁ m₂
    rw [hq, hm₁, hm₂] at hs
    exact hs
  have hmk₁ : MarkedWith N M t₀ (markedPencil v.val) (markedTdot i v.val) m₁.Z := by
    have hm := m₁.marked
    rw [SIMarked, hq, hm₁] at hm
    exact hm
  have hmk₂ : MarkedWith N M t₀ (markedPencil w.val) (markedTdot i w.val) m₂.Z := by
    have hm := m₂.marked
    rw [SIMarked, hq, hm₂] at hm
    exact hm
  rwa [muX_eq_of_markedWith hmk₁ hZv, muX_eq_of_markedWith hmk₂ hZw] at hpair


/-! ### Arcs supply the hypotheses of the marked datum

Three of the four hypotheses of `markedTangentDatum` come from arcs of the
two-point incidence through the point, and this section says exactly which arc
data each needs.  Only `affineDim_le` is not of this shape. -/

/-- **`IsMarkedOn` from member arcs.**  If every direction of `T` is the
velocity of an arc whose marked member has constant rank profile, then `T` is
marked at `t₀`: `Pencil.MemberArc.exists_markedWith`, i.e. the smoothness of the
nilpotent orbit at the member. -/
theorem isMarkedOn_of_memberArcs {N M : Matrix (Fin n) (Fin n) K} {t₀ : K}
    {T : Submodule K (MarkedIndex (Fin n) → K)} {i : Fin 2}
    (harc : ∀ v : T, Nonempty (MemberArc N M t₀ (pairMatN (markedDirPair v.val))
      (pairMatM (markedDirPair v.val)) (markedTdot i v.val))) :
    IsMarkedOn N M t₀ i T :=
  fun v => (harc v).some.exists_markedWith

/-- What an arc of the incidence supplies at a direction: an arc of the pencil
based at `(N, M)` with `(Nd, Md)` as velocity, nilpotent, of constant rank
profile, and of multidegree `(τ, d)` at the base and generically.  These are
exactly the hypotheses of `isRealizedDir_of_arc`; the H1 node assembles them
inline, and its natural home is beside `IsRealizedDir`. -/
structure PencilArcData (N M Nd Md : Matrix (Fin n) (Fin n) K)
    (τ : Nat.Partition n) (d : ℕ → ℕ) where
  /-- the arc of the first matrix -/
  Ns : Matrix (Fin n) (Fin n) (PowerSeries K)
  /-- the arc of the second matrix -/
  Ms : Matrix (Fin n) (Fin n) (PowerSeries K)
  matC_N : matC Ns = N
  matC_M : matC Ms = M
  matD_N : matD Ns = Nd
  matD_M : matD Ms = Md
  /-- the pencil is nilpotent along the arc -/
  nilpotent : (pencil Ns Ms) ^ n = 0
  /-- the rank profile does not jump -/
  rank : ∀ k ≤ n, ArcRankEq Ns Ms k
  /-- the multidegree at the base point -/
  multidegree : HasMultidegree (matC Ns) (matC Ms) τ d
  /-- the multidegree at the generic point -/
  multidegreeGen : HasMultidegree (Ns.map (algebraMap (PowerSeries K) (LaurentSeries K)))
    (Ms.map (algebraMap (PowerSeries K) (LaurentSeries K))) τ d

/-- An arc realises its direction (`cor:arc-torsion` and `lem:flag-flat`(1)). -/
theorem PencilArcData.isRealizedDir {N M Nd Md : Matrix (Fin n) (Fin n) K}
    {τ : Nat.Partition n} {d : ℕ → ℕ} (A : PencilArcData N M Nd Md τ d) :
    IsRealizedDir N M Nd Md := by
  have h := isRealizedDir_of_arc A.Ns A.Ms τ d A.nilpotent A.rank A.multidegree A.multidegreeGen
  rwa [A.matC_N, A.matC_M, A.matD_N, A.matD_M] at h

/-- **`IsMarkedRealized` from pencil arcs.** -/
theorem isMarkedRealized_of_arcs {N M : Matrix (Fin n) (Fin n) K}
    {τ : Nat.Partition n} {d : ℕ → ℕ} {T : Submodule K (MarkedIndex (Fin n) → K)}
    (harc : ∀ v : T, Nonempty (PencilArcData N M (pairMatN (markedDirPair v.val))
      (pairMatM (markedDirPair v.val)) τ d)) :
    IsMarkedRealized N M T :=
  fun v => (harc v).some.isRealizedDir


/-- **The realised datum from arcs**: everything `thm:h2-conditional` consumes,
from arc data at a single point of the two-point incidence, the two (SI)
statements, and `dim Ŷ ≤ dim T`.

This is the single obligation the geometry has to meet.  `MarkedIsotropic` is
itself supplied by `markedIsotropic_of_siVanishing` from the (SI) of the two
`SIComponent`s, so what `Chain/H2Geometry.lean` has to produce is: the two components,
a point of `Ŷ` with its tangent space, arcs of the incidence realising every
tangent direction (in the three forms above), and the variety bound. -/
theorem exists_markedRealizedDatum_of_arcs [IsAlgClosed K] [Infinite K]
    {N M N₀ : Matrix (Fin n) (Fin n) K} {τ : Nat.Partition n} {d : ℕ → ℕ} {t₁ t₂ : K}
    {S : Set (MarkedIndex (Fin n) → K)}
    (hnil : NilpotentPencil N M) (hgen : GenericType N M τ) (hMty : HasType M τ)
    (hne : t₁ ≠ t₂) (hN₀ : IsNilpotent N₀)
    (hm₁ : N + t₁ • M ∈ orbitClosure N₀) (hm₂ : N + t₂ • M ∈ orbitClosure N₀)
    (T : Submodule K (MarkedIndex (Fin n) → K))
    (hpencilArcs : ∀ v : T, Nonempty (PencilArcData N M (pairMatN (markedDirPair v.val))
      (pairMatM (markedDirPair v.val)) τ d))
    (hmember₁ : ∀ v : T, Nonempty (MemberArc N M t₁ (pairMatN (markedDirPair v.val))
      (pairMatM (markedDirPair v.val)) (markedTdot 0 v.val)))
    (hmember₂ : ∀ v : T, Nonempty (MemberArc N M t₂ (pairMatN (markedDirPair v.val))
      (pairMatM (markedDirPair v.val)) (markedTdot 1 v.val)))
    (hSI₁ : MarkedIsotropic N M t₁ 0 T) (hSI₂ : MarkedIsotropic N M t₂ 1 T)
    (haff : affineDim S ≤ ((Module.finrank K T : ℕ) : WithBot ℕ∞)) :
    ∃ R : RealizedDatum K (MarkedIndex (Fin n)), R.Bounds τ (cOf N₀ - cType τ) 2 S :=
  exists_markedRealizedDatum hnil hgen hMty hne hN₀ hm₁ hm₂ T
    (isMarkedRealized_of_arcs (d := d) hpencilArcs)
    (isMarkedOn_of_memberArcs hmember₁) (isMarkedOn_of_memberArcs hmember₂)
    hSI₁ hSI₂ haff

end MarkedDatum



/-! ### The count -/

section Main

variable {K : Type} [Field K] {n : ℕ}

/-- **`thm:h2-conditional` from the tangent datum**: the realised classes at a
tangent-generic point of a component of the cone `Ŷ` give (H2′) at
`(τ, d, N₀)`. -/
theorem markedIncidenceBound_of_bounds {τ : Nat.Partition n} {d : ℕ → ℕ}
    {N₀ : Matrix (Fin n) (Fin n) K} (R : RealizedDatum K (MarkedIndex (Fin n)))
    (hR : R.Bounds τ (cOf N₀ - cType τ) 2 (markedCoords '' markedLocus τ d N₀)) :
    MarkedIncidenceBound τ d N₀ := by
  have hcount := hR.finrank_add_le
  have h2D := two_dimFl τ
  have hR2 := hR.two_dimFl
  have hfin : Module.finrank K R.T + (cOf N₀ - cType τ) ≤ 3 * dimFl τ + 2 := by omega
  refine le_trans (add_le_add hR.affineDim_le le_rfl) ?_
  exact_mod_cast hfin


end Main

end Height.Chain
