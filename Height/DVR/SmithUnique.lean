import Height.DVR.ResidueModel
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.ENat.SuccOrder

/-!
# Truncation and divisibility over `K⟦u⟧`

**Despite the file name, no uniqueness statement for the Smith normal form is
proved here.**  What this file proves is the elementary calculus that
`DVR/CokerTorsion.lean` and `DVR/AlternatingPresentation.lean` run on:

* coordinatewise truncation of a vector of power series — `truncPi`,
  `truncPi_surjective`, `mem_ker_truncPi`;
* the normalised factorisation of a nonzero power series —
  `exists_unit_mul_X_pow` (`f = v · u^{ord f}` with `v` a unit) and
  `dvd_iff_X_pow_order_dvd`;
* membership of the image of a diagonal matrix,
  `mem_range_mulVecLin_diagonal`.

## What is not proved

The *invariant* form is not in this development: level subspaces
`(range A.mulVecLin) ⊔ u^k·(ι → R)`, their `K`-dimensions, the diagonal
computation, and the resulting independence of `∑ᵢ ord (gᵢ)` from the choice
of Smith datum `U · A · V = diagonal g`.

Consequently `Pencil.lenX` is defined from one arbitrary presentation
(`Pencil.txData`), and its independence of that choice is not proved.  Given
such a uniqueness statement,
`AlternatingPresentation.sum_two_mBlk` would make the independence a corollary.
`Pencil.DX` is not affected: `AlternatingPresentation.two_card_blocks_add_rank`
identifies it with a difference of ranks of `A`, which no choice enters.
-/

namespace Height.DVR

open Matrix PowerSeries

universe u v

/-! ### Truncation of vectors of power series -/

section Trunc

variable {K : Type u} [Field K] {ι : Type v}

/-- The coefficients of each coordinate below its own exponent. -/
noncomputable def truncPi (K : Type u) [Field K] {ι : Type v} (e : ι → ℕ) :
    (ι → PowerSeries K) →ₗ[K] ((i : ι) → Fin (e i) → K) :=
  LinearMap.pi fun i => (truncCoeffsₗ K (e i)).comp (LinearMap.proj i)

theorem truncPi_surjective (e : ι → ℕ) : Function.Surjective (truncPi K e) := by
  intro c
  choose f hf using fun i => truncCoeffsₗ_surjective (K := K) (e i) (c i)
  exact ⟨f, funext fun i => hf i⟩

theorem mem_ker_truncPi {e : ι → ℕ} {x : ι → PowerSeries K} :
    x ∈ LinearMap.ker (truncPi K e) ↔ ∀ i, (X : PowerSeries K) ^ e i ∣ x i := by
  constructor
  · intro hx i
    have h1 := congrFun hx i
    rw [PowerSeries.X_pow_dvd_iff]
    intro j hj
    have h2 := congrFun h1 ⟨j, hj⟩
    simpa [truncPi, truncCoeffsₗ] using h2
  · intro hx
    funext i
    have hmem : x i ∈ uPowSubmodule K (e i) := by
      rw [uPowSubmodule, Submodule.restrictScalars_mem, Ideal.mem_span_singleton]
      exact hx i
    rw [← ker_truncCoeffsₗ (K := K) (e i)] at hmem
    exact hmem

end Trunc

/-! ### The level dimensions of a diagonal matrix -/

section Diagonal

variable {K : Type u} [Field K] {ι : Type v}

theorem exists_unit_mul_X_pow {f : PowerSeries K} (h : f ≠ 0) :
    ∃ v : (PowerSeries K)ˣ, f = (v : PowerSeries K) * X ^ f.order.toNat := by
  obtain ⟨e, v, hv⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h PowerSeries.X_irreducible
  have horder : f.order = (e : ℕ∞) := by
    rw [hv, PowerSeries.order_mul, PowerSeries.order_zero_of_isUnit v.isUnit,
      PowerSeries.order_X_pow, zero_add]
  have hm : f.order.toNat = e := by rw [horder]; rfl
  rw [hm]
  exact ⟨v, hv⟩

theorem dvd_iff_X_pow_order_dvd {f : PowerSeries K} (h : f ≠ 0) (c : PowerSeries K) :
    f ∣ c ↔ (X : PowerSeries K) ^ f.order.toNat ∣ c := by
  obtain ⟨v, hv⟩ := exists_unit_mul_X_pow h
  have key : f * ((v⁻¹ : (PowerSeries K)ˣ) : PowerSeries K) = X ^ f.order.toNat := by
    conv_lhs => rw [hv]
    rw [mul_right_comm, v.mul_inv, one_mul]
  exact ⟨fun hd => dvd_trans PowerSeries.X_pow_order_dvd hd,
    fun hd => dvd_trans ⟨_, key.symm⟩ hd⟩

variable [Fintype ι]

variable [DecidableEq ι]

theorem mem_range_mulVecLin_diagonal {g x : ι → PowerSeries K} :
    x ∈ LinearMap.range (Matrix.diagonal g).mulVecLin ↔ ∀ i, g i ∣ x i := by
  constructor
  · rintro ⟨y, rfl⟩ i
    exact ⟨y i, by simp [Matrix.mulVec_diagonal]⟩
  · intro h
    choose y hy using h
    exact ⟨y, funext fun i => by simp [Matrix.mulVec_diagonal, ← hy i]⟩

end Diagonal

end Height.DVR
