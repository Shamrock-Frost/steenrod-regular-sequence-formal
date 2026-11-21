import Height.Pencil.Local
import Height.Pencil.Isotropy

/-!
# The `gl_n` bridge to the residue form, and the isotropy bound

The paper, `lem:residue-form` (evaluation on representatives) and
`thm:isotropy`.  The mathematics is in
`Height/DVR/AlternatingPresentation.lean`, where it is a statement about a
Smith presentation of a `σ`-alternating matrix over `K⟦u⟧`; what is here
is the bridge from `gl_n` to those vector coordinates.

## The bridge

The standard basis of `gl_n` is self-dual for `(X, Y) ↦ trace (X Y)` up to the
index transposition `swapIdx n` (`trace_mul_eq_sum_vecMat`), so

```
trace (A · Q)  =  ∑ₐ vecMat A a · vecMat Q (swapIdx n a) ,
```

which is exactly the `σ`-twisted pairing of the DVR layer at `σ = swapIdx n`,
and `adMat P *ᵥ vecMat A = vecMat (P A − A P)` (`adMat_mulVec`) turns a
commutator hypothesis into membership of the image of `adMat P`
(`mulVec_of_commutator`).  On that bridge:

* `LocalData.omega_eq_residue` is `residueSpaceForm_blockClassOf`;
* `DX_add_rank` is `two_card_blocks_add_rank`.

## What is proved and what is not

For `P ∈ gl_n(K⟦u⟧)` and two directions `Q₁ = [P, A₁]`, `Q₂ = [P, A₂]` with
`A_i ∈ gl_n(K⸨u⸩)`,

```
residueSpaceForm D.mBlk (D.blockClass D.mBlk Q₁) (D.blockClass D.mBlk Q₂)
  = laurentResidueFormValue A₁ Q₂ = res_x trace (A₁ Q₂) du
```

(`LocalData.omega_eq_residue`), for **every** Smith presentation `D` of `ad_P`.
Self-duality and normalisation of `D` hold by construction
(`Pencil/Local.lean`), so they are not hypotheses.  Combined with
`thm:isotropy` (`Pencil/Isotropy.lean`) this gives `LocalData.omega_eq_zero`,
which is what `(H1)` consumes at a drop point.

The second hypothesis of `omega_eq_residue` is genuinely needed: `Q₂` must also
be a commutator over `K⸨u⸩`.  The right-hand side is linear in `Q₂` over all of
`gl_n(K⟦u⟧)`, whereas `blockClass` only records the torsion coordinates; on a
direction whose class in `coker ad_P` has a nonzero free part the two sides
differ, and `hA₂` is exactly what kills the free coordinates
(`exists_coordsOf_eq_mul`).  The paper assumes it: in
`lem:residue-form` both `Ṗ_i` are tangent directions, hence commutators over
`K_x` by `cor:arc-torsion`.

Two things are **not** stated here:

* *Independence of `lenX` from the choice of local datum.*  `Pencil/Local.lean`
  defines `lenX`, `DX`, `Tx`, `OmegaX` from `txData = localData (Pat N M t₀)`,
  an arbitrary choice, so a statement about them ought to hold for every
  presentation.  For `DX` that is proved: `two_card_blocks_add_rank` identifies
  `2 · #Blocks` with a difference of ranks of `ad_P`, the same number for every
  choice.  For `lenX`, `sum_two_mBlk` reduces it to `∑_i mExp i`, but the
  independence of that sum from the choice — uniqueness of the invariant factors
  over `K⟦u⟧` — is **not** proved anywhere in the tree.  (`sum_two_mBlk` plus a
  uniqueness statement for Smith data over `K⟦u⟧` would make it a corollary.)
* *The half-dimensional bound for the realised classes.*  What the tree has
  is `Height.DVR.residueSpaceForm_isotropic_bound`
  (`DVR/ResidueModel.lean`): every `ω_x`-isotropic subspace of the residue space
  has `2 · dim ≤ ∑ 2 m_i`.  `omega_eq_zero` below supplies the isotropy
  hypothesis pointwise, so the bound is available by composing the two — that
  composition is what `Chain/H1Geometry.lean` performs inline.

## The corank form of `lem:local-pairing` (`DX_add_rank`)

`LocalData.two_card_blocks_add_rank` (`DVR/AlternatingPresentation.lean`) and
its chart form `DX_add_rank` prove the corank form of `lem:local-pairing`:

```
D_x + rank (ad_{N + t₀M})  =  rank (ad_P over K⸨u⸩) .
```

The type form `D_x + c(τ) = c(τ(x))` is `Height.Pencil.DX_add_cType` in
`Pencil/Realized.lean`, proved for `[Infinite K]` from this identity and two
inputs: `Toolbox/CentralizerDim.lean`'s `rank_adMat_eq`
(`rank (ad_X) + cOf X = n²` for nilpotent `X`) and `Pencil/Realized.lean`'s
`rank_map_adMat_pencilPoly`.  `[Infinite K]` is necessary: over a finite field
`GenericType N M τ` can hold vacuously for every `τ`, so the hypothesis-free
form is false.  Its consumers are `Chain/H1Geometry.lean` and
`Pencil/SelfDual.lean`.
-/

namespace Height.Pencil

open Matrix Height.DVR Height.Toolbox Isotropy

universe u

/-! ### Base change of `adMat` and `vecMat` -/

section BaseChange

variable {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}

theorem vecMat_map (φ : R →+* S) (Q : Matrix (Fin n) (Fin n) R) (a : Fin (n * n)) :
    vecMat (Q.map φ) a = φ (vecMat Q a) := rfl

/-- The trace of a product, read in the coordinates of `Local.lean`: the
standard basis of `gl_n` is self-dual for `(X, Y) ↦ trace (X Y)` up to the
index transposition `swapIdx`.  This is the `σ`-twisted pairing of
`DVR/AlternatingPresentation.lean` at `σ = swapIdx n`. -/
theorem trace_mul_eq_sum_vecMat (X Y : Matrix (Fin n) (Fin n) R) :
    trace (X * Y) = ∑ a : Fin (n * n), vecMat X a * vecMat Y (swapIdx n a) := by
  have hswap : ∀ a : Fin (n * n),
      vecMat Y (swapIdx n a) = Y (glIdx n a).2 (glIdx n a).1 := by
    intro a
    rw [vecMat_apply, glIdx_swapIdx]
    rfl
  rw [Finset.sum_congr rfl fun a (_ : a ∈ Finset.univ) => by
    rw [vecMat_apply, hswap a]]
  rw [Equiv.sum_comp (glIdx n) fun p : Fin n × Fin n => X p.1 p.2 * Y p.2 p.1,
    Fintype.sum_prod_type]
  rw [Matrix.trace]
  exact Finset.sum_congr rfl fun i _ => by rw [Matrix.diag_apply, Matrix.mul_apply]

end BaseChange

/-! ### The bridge to the vector coordinates of the DVR layer -/

section Bridge

variable {K : Type u} [Field K] {n : ℕ}

/-- A commutator relation over `K⸨u⸩` says that `vec Q` is in the image of
`adMat P` after base change: the hypothesis shape of the DVR layer. -/
theorem mulVec_of_commutator {P Q : Matrix (Fin n) (Fin n) (PowerSeries K)}
    (A : Matrix (Fin n) (Fin n) (LaurentSeries K))
    (hA : toK (LaurentSeries K) P * A - A * toK (LaurentSeries K) P
      = toK (LaurentSeries K) Q) :
    (adMat P).map (algebraMap (PowerSeries K) (LaurentSeries K)) *ᵥ vecMat A
      = fun i => algebraMap (PowerSeries K) (LaurentSeries K) (vecMat Q i) := by
  set φ := algebraMap (PowerSeries K) (LaurentSeries K) with hφ
  have h : P.map φ * A - A * P.map φ = Q.map φ := hA
  rw [← adMat_map, adMat_mulVec, h]
  funext i
  exact vecMat_map φ Q i

/-- The trace pairing of `gl_n` in the vector coordinates of the DVR layer. -/
theorem trace_mul_toK_eq_sum (A : Matrix (Fin n) (Fin n) (LaurentSeries K))
    (Q : Matrix (Fin n) (Fin n) (PowerSeries K)) :
    trace (A * toK (LaurentSeries K) Q)
      = ∑ a : Fin (n * n), vecMat A a *
          algebraMap (PowerSeries K) (LaurentSeries K) (vecMat Q (swapIdx n a)) := by
  rw [trace_mul_eq_sum_vecMat]
  exact Finset.sum_congr rfl fun a _ => by rw [vecMat_map]

/-- The residue pairing of `lem:residue-form` in the vector coordinates of the
DVR layer. -/
theorem laurentResidueFormValue_eq_sum (A : Matrix (Fin n) (Fin n) (LaurentSeries K))
    (Q : Matrix (Fin n) (Fin n) (PowerSeries K)) :
    laurentResidueFormValue A Q
      = laurentResidue K (∑ a : Fin (n * n), vecMat A a *
          algebraMap (PowerSeries K) (LaurentSeries K) (vecMat Q (swapIdx n a))) := by
  rw [laurentResidueFormValue, residueFormValue, trace_mul_toK_eq_sum]

end Bridge

/-! ### The `LocalData` forms -/

section Coords

variable {K : Type u} [Field K] {n : ℕ} {P : Matrix (Fin n) (Fin n) (PowerSeries K)}

/-- **`lem:residue-form`, evaluation on representatives.**  For a Smith
presentation of `ad_P` over `K⟦u⟧`, the residue form of `DVR/ResidueModel.lean`
applied to the block classes of two directions `Q₁ = [P, A₁]`, `Q₂ = [P, A₂]`
(with `A_i` over `K⸨u⸩`) is the residue of `trace (A₁ Q₂)`.

Both commutator hypotheses are needed; see the module docstring. -/
theorem LocalData.omega_eq_residue (D : LocalData K n P)
    (Q₁ Q₂ : Matrix (Fin n) (Fin n) (PowerSeries K))
    (A₁ A₂ : Matrix (Fin n) (Fin n) (LaurentSeries K))
    (hA₁ : toK (LaurentSeries K) P * A₁ - A₁ * toK (LaurentSeries K) P
      = toK (LaurentSeries K) Q₁)
    (hA₂ : toK (LaurentSeries K) P * A₂ - A₂ * toK (LaurentSeries K) P
      = toK (LaurentSeries K) Q₂) :
    residueSpaceForm D.mBlk (D.blockClass D.mBlk Q₁) (D.blockClass D.mBlk Q₂)
      = laurentResidueFormValue A₁ Q₂ := by
  rw [laurentResidueFormValue_eq_sum, D.blockClass_eq_blockClassOf,
    D.blockClass_eq_blockClassOf]
  simpa using D.residueSpaceForm_blockClassOf 0 (Nat.zero_le 1)
    (vecMat Q₁) (vecMat Q₂) (vecMat Q₁) (vecMat Q₂) (by simp) (by simp)
    (vecMat A₁) (vecMat A₂)
    (mulVec_of_commutator A₁ hA₁) (mulVec_of_commutator A₂ hA₂)

end Coords

/-! ### `lem:local-pairing`, corank form -/

section Corank

variable {K : Type u} [Field K] {n : ℕ}

/-- `lem:local-pairing`, corank form in the chart at a finite point: `D_x`
plus the rank of `ad` at the member `N + t₀ M` is the rank of `ad_P` over
`K⸨u⸩`.  Replacing the two ranks by `n² − c(τ(x))` and `n² − c(τ)` turns this
into `DX_add_cType`; see the module docstring. -/
theorem DX_add_rank (N M : Matrix (Fin n) (Fin n) K) (t₀ : K) :
    DX N M t₀ + Matrix.rank (adMat (N + t₀ • M))
      = ((adMat (Pat N M t₀)).map
          (algebraMap (PowerSeries K) (LaurentSeries K))).rank := by
  have hmap : (adMat (Pat N M t₀)).map (PowerSeries.constantCoeff (R := K))
      = adMat (N + t₀ • M) := by
    rw [← adMat_map]
    congr 1
    exact matC_Pat N M t₀
  rw [DX, ← hmap]
  exact (txData N M t₀).two_card_blocks_add_rank

end Corank

/-! ### `thm:isotropy` in the local model -/

section Isotropy

variable {K : Type u} [Field K] {n : ℕ} {P : Matrix (Fin n) (Fin n) (PowerSeries K)}

/-- **`thm:isotropy`** in the local model: the residue form of
`DVR/ResidueModel.lean` vanishes on the block classes of two kernel-flat
directions that are commutators over `K⸨u⸩`.  `omega_eq_residue` turns the
form into the residue of `trace (A₁ Q₂)`, and `trace_regular` says that
function has no pole. -/
theorem LocalData.omega_eq_zero (D : LocalData K n P) (hP : P ^ n = 0)
    (Q₁ Q₂ : Matrix (Fin n) (Fin n) (PowerSeries K))
    (A₁ A₂ : Matrix (Fin n) (Fin n) (LaurentSeries K))
    (hA₁ : toK (LaurentSeries K) P * A₁ - A₁ * toK (LaurentSeries K) P
      = toK (LaurentSeries K) Q₁)
    (hA₂ : toK (LaurentSeries K) P * A₂ - A₂ * toK (LaurentSeries K) P
      = toK (LaurentSeries K) Q₂)
    (hQ₁ : KernelFlat P Q₁) (hQ₂ : KernelFlat P Q₂) :
    residueSpaceForm D.mBlk (D.blockClass D.mBlk Q₁) (D.blockClass D.mBlk Q₂) = 0 := by
  rw [D.omega_eq_residue Q₁ Q₂ A₁ A₂ hA₁ hA₂]
  exact residue_eq_zero P Q₁ Q₂ hP A₁ A₂ hA₁ hA₂ hQ₁ hQ₂

end Isotropy

end Height.Pencil
