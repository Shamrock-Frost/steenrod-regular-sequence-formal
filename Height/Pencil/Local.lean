import Height.Pencil.Chart
import Height.Toolbox.AdMatrix
import Height.DVR.AlternatingPresentation

/-!
# The local torsion model `T_x`, the class map, and the forms `ω_x`, `Ω_x`

`T_x` is *not* built as the torsion submodule of `coker ad_P`; it is defined
concretely as the DVR model
`residueBlockSpace` of `Height/DVR/ResidueModel.lean`, and the identification
with the cokernel is replaced by the one theorem that actually gets used,

```
cls_eq_zero_iff :  cls Q = 0  ↔  ∃ A over K⟦u⟧, Q = P₀ * A - A * P₀ ,
```

which is the Smith-form statement.

## The Smith datum lives in `DVR/AlternatingPresentation.lean`

`ad_{P₀}` is written as an explicit `n² × n²` matrix `adEntry P₀`
(`adEntry_mulVec`), reindexed to `Fin (n*n)` as `adMat`.  The Gram matrix of the
alternating pairing `(A, C) ↦ trace([P₀, A] C)` is, in the standard basis, the
transpose of `adMat` with its columns permuted by the index transposition
`swapIdx n` (`gramMat`), and it is alternating (`gramMat_isAlt`).  So `adMat P`
is *`swapIdx n`-alternating* in the sense of
`Height/DVR/AlternatingPresentation.lean`, and

```
LocalData K n P  :=  DVR.AlternatingPresentation K (n*n) (swapIdx n) (adMat P)
```

is its Smith datum, **self-dual and normalised by construction**: the right
change of basis is the definition `dualMat (swapIdx n) U` and the invariant
factors are the definition `normFactor K (n*n) e`, so self-duality and
normalisation are the theorems `DVR.AlternatingPresentation.V_apply` and
`g_eq_X_pow_mExp`, not hypotheses of the residue lemmas.  `localData P` is the
datum chosen once by `DVR.exists_alternatingPresentation`.

## This file

is only the `gl_n` bridge: `gramMat` and its alternation, the class map of a
matrix direction (`coords`, `blockClass`, `freeClass`, `cls`, obtained from the
DVR vector-level maps by composing with `vecMat`), `cls_eq_zero_iff`, and the
chart-level names `txData`, `Tx`, `uTx`, `cls`, `OmegaX`, `lenX`, `DX`.  The
exponents `mExp`, the blocks `Blocks`/`mBlk`, the free indices `Frees` and every
counting or residue theorem about them belong to the presentation.

## Remarks on the formulation

* The class map is `U *ᵥ vec Q` (`coords`), not `U⁻¹ · vec Q`: with
  `U * adMat P * V = diagonal g` that is the right combination.
* `Tx` is `residueBlockSpace K m` over the index set `Blocks`, not over all
  indices with `1 ≤ m i`.  `residueBlockSpace` already carries *two* quotients
  per index, so the index set must be one representative per `blockInvol`-pair,
  else the dimension doubles; `Blocks` is that set of representatives.  The
  exponents agree along a pair, so nothing is lost.
* `DVR/ResidueModel.lean` has no separate `dividedResidueSpaceForm`: the
  divided form is `residueSpaceForm` at the exponents `m − 1`, which is how
  `OmegaX` is defined here.
* The residue identity `omega_eq_residue` and the type form `DX_add_cType` of
  `lem:local-pairing` are not in this file; see the comment at its end.
-/

namespace Height.Pencil

open Matrix Height.DVR Height.Toolbox

universe u

/-! ### The Gram matrix of `ad_P` -/

section Gram

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The Gram matrix of `(A, C) ↦ trace([P, A] C)` in the standard basis,
reindexed by `Fin (n*n)`: the transpose of `adMat` with its columns permuted by
the index transposition.  It is the `swapIdx n`-twist of `adMat P` in the sense
of `DVR/AlternatingPresentation.lean`. -/
def gramMat (P : Matrix (Fin n) (Fin n) R) : Matrix (Fin (n * n)) (Fin (n * n)) R :=
  (adMat P)ᵀ.submatrix id (swapIdx n)

theorem gramMat_apply (P : Matrix (Fin n) (Fin n) R) (a b : Fin (n * n)) :
    gramMat P a b = adEntry P (glIdx n b).swap (glIdx n a) := by
  show adEntry P (glIdx n (swapIdx n b)) (glIdx n a) = _
  rw [glIdx_swapIdx]

theorem gramMat_isAlt (P : Matrix (Fin n) (Fin n) R) : IsAltMatrix (gramMat P) := by
  constructor
  · intro a
    rw [gramMat_apply]
    exact adEntry_swap_self P (glIdx n a)
  · intro a b
    rw [gramMat_apply, gramMat_apply]
    exact adEntry_swap_skew P (glIdx n b) (glIdx n a)

/-- The image of `ad_P` read on coordinates: `vec Q` is in the image of `adMat P`
exactly when `Q` is a commutator with `P`. -/
theorem mem_range_adMat_iff (P Q : Matrix (Fin n) (Fin n) R) :
    vecMat Q ∈ LinearMap.range (adMat P).mulVecLin ↔ ∃ A, Q = P * A - A * P := by
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨A, rfl⟩ := vecMat_surjective (R := R) (n := n) z
    exact ⟨A, (vecMat_injective (by rw [← adMat_mulVec]; exact hz)).symm⟩
  · rintro ⟨A, rfl⟩
    exact ⟨vecMat A, adMat_mulVec P A⟩

end Gram

/-! ### The local data at a point of `ℙ¹` -/

section Data

variable {K : Type u} [Field K] {n : ℕ}

/-- The Smith datum of `ad_P` over `K⟦u⟧`: the presentation of `adMat P` as a
`swapIdx n`-alternating matrix (`DVR/AlternatingPresentation.lean`).  It is
self-dual and normalised by construction (`V_apply`, `g_eq_X_pow_mExp`). -/
abbrev LocalData (K : Type u) [Field K] (n : ℕ)
    (P : Matrix (Fin n) (Fin n) (PowerSeries K)) :=
  DVR.AlternatingPresentation K (n * n) (swapIdx n) (adMat P)

namespace LocalData

variable {P : Matrix (Fin n) (Fin n) (PowerSeries K)} (D : LocalData K n P)

/-- The coordinates of a direction after the change of basis: `U · vec Q`. -/
noncomputable def coords (Q : Matrix (Fin n) (Fin n) (PowerSeries K)) :
    Fin (n * n) → PowerSeries K :=
  D.coordsOfL (vecMat Q)

/-- `coords` as a `K⟦u⟧`-linear map. -/
noncomputable def coordsL : Matrix (Fin n) (Fin n) (PowerSeries K) →ₗ[PowerSeries K]
    (Fin (n * n) → PowerSeries K) where
  toFun := D.coords
  map_add' Q Q' := by
    simp only [coords]
    rw [show vecMat (Q + Q') = vecMat Q + vecMat Q' from rfl, map_add]
  map_smul' c Q := by
    simp only [coords, RingHom.id_apply]
    rw [show vecMat (c • Q) = c • vecMat Q from rfl, map_smul]

/-- `coords` as a `K`-linear map. -/
noncomputable def coordsK :
    Matrix (Fin n) (Fin n) (PowerSeries K) →ₗ[K] (Fin (n * n) → PowerSeries K) :=
  D.coordsL.restrictScalars K

/-- The block coordinates of a direction, at arbitrary exponents: the vector
block class of `DVR/AlternatingPresentation.lean` composed with `vecMat`. -/
noncomputable def blockClass (e : D.Blocks → ℕ) :
    Matrix (Fin n) (Fin n) (PowerSeries K) →ₗ[K] residueBlockSpace K e :=
  LinearMap.pi fun b : D.Blocks =>
    LinearMap.prod
      ((uPowSubmodule K (e b)).mkQ ∘ₗ LinearMap.proj b.val ∘ₗ D.coordsK)
      ((uPowSubmodule K (e b)).mkQ ∘ₗ LinearMap.proj (blockInvol b.val) ∘ₗ D.coordsK)

@[simp] theorem blockClass_apply (e : D.Blocks → ℕ)
    (Q : Matrix (Fin n) (Fin n) (PowerSeries K)) (b : D.Blocks) :
    D.blockClass e Q b =
      (Submodule.Quotient.mk (D.coords Q b.val),
        Submodule.Quotient.mk (D.coords Q (blockInvol b.val))) := rfl

theorem blockClass_eq_blockClassOf (e : D.Blocks → ℕ)
    (Q : Matrix (Fin n) (Fin n) (PowerSeries K)) :
    D.blockClass e Q = D.blockClassOf e (vecMat Q) := rfl

/-- The free coordinates of a direction. -/
noncomputable def freeClass :
    Matrix (Fin n) (Fin n) (PowerSeries K) →ₗ[K] (D.Frees → PowerSeries K) :=
  LinearMap.pi fun i : D.Frees => LinearMap.proj i.val ∘ₗ D.coordsK

@[simp] theorem freeClass_apply (Q : Matrix (Fin n) (Fin n) (PowerSeries K))
    (i : D.Frees) : D.freeClass Q i = D.coords Q i.val := rfl

/-- The class map: the torsion classes in `T_x` together with the free
coordinates. -/
noncomputable def cls :
    Matrix (Fin n) (Fin n) (PowerSeries K) →ₗ[K] D.torsion × (D.Frees → PowerSeries K) :=
  LinearMap.prod (D.blockClass D.mBlk) D.freeClass

/-- **The commutator criterion**: a direction has zero
class exactly when it is a commutator over `K⟦u⟧`.  Both halves of `cls` are
needed: the torsion coordinates and the free ones.  This is
`DVR.AlternatingPresentation.clsOf_eq_zero_iff` through `mem_range_adMat_iff`. -/
theorem cls_eq_zero_iff (Q : Matrix (Fin n) (Fin n) (PowerSeries K)) :
    D.cls Q = 0 ↔ ∃ A, Q = P * A - A * P := by
  rw [← mem_range_adMat_iff P Q, ← D.clsOf_eq_zero_iff (vecMat Q)]
  rfl

/-- **The divided vanishing criterion on matrix directions.**  If `u S` is a
commutator with `P`, then `S` is zero on the divided torsion `u T_x`.

`lem:marked-shift` in the model: the shifted class of `Pencil/Marked.lean` is
`blockClass (m − 1)` of `Ṙ / u`, and changing the marking witness changes `Ṙ`
by a commutator.  `DVR.AlternatingPresentation.blockClassOf_pred_eq_zero`. -/
theorem blockClass_pred_eq_zero {S : Matrix (Fin n) (Fin n) (PowerSeries K)}
    (h : ∃ A, (PowerSeries.X : PowerSeries K) • S = P * A - A * P) :
    D.blockClass (fun b => D.mBlk b - 1) S = 0 := by
  rw [blockClass_eq_blockClassOf]
  exact D.blockClassOf_pred_eq_zero _ ((mem_range_adMat_iff P _).mpr h)

/-- A commutator with `P` has no torsion class: half of `cls_eq_zero_iff`. -/
theorem blockClass_eq_zero_of_isCommutator {Q : Matrix (Fin n) (Fin n) (PowerSeries K)}
    (h : ∃ A, Q = P * A - A * P) : D.blockClass D.mBlk Q = 0 :=
  congrArg Prod.fst ((D.cls_eq_zero_iff Q).mpr h)

/-- **The divided criterion on matrix directions**: reading `S` at the lowered
exponents `m − 1` sees exactly what reading `u S` at `m` sees.

`Pencil/Marked.lean` reads the shifted representative `Ṙ = u S` at `m − 1`;
this says the reading loses nothing, which is where the kernel slack of
`thm:h2-conditional` is measured. -/
theorem blockClass_pred_eq_zero_iff (S : Matrix (Fin n) (Fin n) (PowerSeries K)) :
    D.blockClass (fun b => D.mBlk b - 1) S = 0
      ↔ D.blockClass D.mBlk ((PowerSeries.X : PowerSeries K) • S) = 0 := by
  rw [blockClass_eq_blockClassOf, blockClass_eq_blockClassOf]
  exact D.blockClassOf_pred_eq_zero_iff _
end LocalData

end Data

/-! ### The local model at a point of `ℙ¹` -/

section AtPoint

variable {K : Type u} [Field K] {n : ℕ}

/-- The local data at `P`, chosen once by `DVR.exists_alternatingPresentation`. -/
noncomputable def localData (P : Matrix (Fin n) (Fin n) (PowerSeries K)) :
    LocalData K n P :=
  (DVR.exists_alternatingPresentation (swapIdx n) (swapIdx_swapIdx (n := n))
    (adMat P) (gramMat_isAlt P)).some

/-- The local data of the pencil `(N, M)` at the finite point `t₀`. -/
noncomputable def txData (N M : Matrix (Fin n) (Fin n) K) (t₀ : K) :
    LocalData K n (Pat N M t₀) :=
  localData (Pat N M t₀)

/-- `T_x` at the point `t₀`. -/
@[reducible] noncomputable def Tx (N M : Matrix (Fin n) (Fin n) K) (t₀ : K) : Type u :=
  (txData N M t₀).torsion

/-- `u T_x` at the point `t₀`. -/
@[reducible] noncomputable def uTx (N M : Matrix (Fin n) (Fin n) K) (t₀ : K) : Type u :=
  (txData N M t₀).dividedTorsion

/-- The class map at `t₀`. -/
noncomputable def cls (N M : Matrix (Fin n) (Fin n) K) (t₀ : K) :
    Matrix (Fin n) (Fin n) (PowerSeries K) →ₗ[K]
      Tx N M t₀ × ((txData N M t₀).Frees → PowerSeries K) :=
  (txData N M t₀).cls

/-- **The commutator criterion** at a point of the chart: a direction
has zero class at `t₀` exactly when it is a commutator with the localized
pencil over `K⟦u⟧`. -/
theorem cls_eq_zero_iff (N M : Matrix (Fin n) (Fin n) K) (t₀ : K)
    (Q : Matrix (Fin n) (Fin n) (PowerSeries K)) :
    cls N M t₀ Q = 0 ↔ ∃ A, Q = Pat N M t₀ * A - A * Pat N M t₀ :=
  (txData N M t₀).cls_eq_zero_iff Q

/-- `Ω_x`, the divided residue form on `u T_x` (`lem:divided-form`).  There is
no separate `dividedResidueSpaceForm` in `DVR/ResidueModel.lean`: the divided
form is `residueSpaceForm` at the exponents `m − 1`. -/
noncomputable def OmegaX (N M : Matrix (Fin n) (Fin n) K) (t₀ : K) :
    LinearMap.BilinForm K (uTx N M t₀) :=
  residueSpaceForm (fun b => (txData N M t₀).mBlk b - 1)

/-- `len_x T`, the length of the local torsion. -/
noncomputable def lenX (N M : Matrix (Fin n) (Fin n) K) (t₀ : K) : ℕ :=
  ∑ b, 2 * (txData N M t₀).mBlk b

/-- `D_x`, twice the number of hyperbolic blocks. -/
noncomputable def DX (N M : Matrix (Fin n) (Fin n) K) (t₀ : K) : ℕ :=
  2 * Fintype.card (txData N M t₀).Blocks

/-- **`lem:residue-form`, the isotropy bound at a point**: an `ω_x`-isotropic
subspace of `T_x` has dimension at most `½ len_x`.

`ω_x` is nondegenerate on `T_x`, which in the model is
`DVR.residueSpaceForm_isotropic_bound` at the exponents `mBlk`; `len_x` is by
definition the total `∑_b 2 m_b`. -/
theorem two_finrank_le_lenX (N M : Matrix (Fin n) (Fin n) K) (t₀ : K)
    (Λ : Submodule K (Tx N M t₀))
    (hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, residueSpaceForm (txData N M t₀).mBlk x y = 0) :
    2 * Module.finrank K Λ ≤ lenX N M t₀ :=
  Height.DVR.residueSpaceForm_isotropic_bound _ Λ hΛ

/-- **The accounting behind `lem:divided-form`**: the divided exponents at a
point account for `len_x − D_x`.  Every hyperbolic block has `1 ≤ m_b`, and
`D_x` is twice their number; stated additively so no `ℕ`-subtraction appears. -/
theorem sum_two_mul_mBlk_pred_add_DX (N M : Matrix (Fin n) (Fin n) K) (t₀ : K) :
    (∑ b : (txData N M t₀).Blocks, 2 * ((txData N M t₀).mBlk b - 1)) + DX N M t₀
      = lenX N M t₀ := by
  have hcard : DX N M t₀ = ∑ _b : (txData N M t₀).Blocks, 2 := by
    rw [DX, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
  rw [hcard, lenX, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hb : 1 ≤ (txData N M t₀).mBlk b := b.2.2
  omega

/-- **`lem:divided-form`, the isotropy bound at a marked point**: an
`Ω_x`-isotropic subspace of `u T_x` has dimension at most `½ (len_x − D_x)`.

The same bound at the lowered exponents `m_b − 1`, plus the accounting
`sum_two_mul_mBlk_pred_add_DX`. -/
theorem two_finrank_add_DX_le_lenX (N M : Matrix (Fin n) (Fin n) K) (t₀ : K)
    (W : Submodule K (uTx N M t₀))
    (hW : ∀ x ∈ W, ∀ y ∈ W,
      residueSpaceForm (fun b => (txData N M t₀).mBlk b - 1) x y = 0) :
    2 * Module.finrank K W + DX N M t₀ ≤ lenX N M t₀ :=
  calc 2 * Module.finrank K W + DX N M t₀
      ≤ (∑ b : (txData N M t₀).Blocks, 2 * ((txData N M t₀).mBlk b - 1)) + DX N M t₀ :=
        Nat.add_le_add_right (Height.DVR.residueSpaceForm_isotropic_bound _ W hW) _
    _ = lenX N M t₀ := sum_two_mul_mBlk_pred_add_DX N M t₀

/-! #### The residue identity and `lem:local-pairing` are in `Pencil/Torsion.lean`

`Height/Pencil/Torsion.lean` evaluates `ω_x` on representatives and relates
`D_x` to the ranks of `ad`; its module docstring gives the details:

* `LocalData.omega_eq_residue` needs the hypothesis that `Q₂` too is a
  commutator over `K⸨u⸩` — otherwise the right-hand side sees the free part of
  the class of `Q₂` in `coker ad_P`, which `T_x` does not record.

* `DX_add_cType`: `Torsion.lean` proves its corank form `DX_add_rank`
  (`D_x + rank ad_{N+t₀M} = rank ad_P` over `K⸨u⸩`), and the type form is
  `Pencil/Realized.lean`'s `DX_add_cType`, which carries `[Infinite K]` (over a
  finite field `GenericType N M τ` can hold vacuously for every `τ`, so the
  hypothesis-free form is false).
-/

end AtPoint

end Height.Pencil
