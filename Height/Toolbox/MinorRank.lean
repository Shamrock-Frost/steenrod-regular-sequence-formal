import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Rank by minors

The rank of a matrix over a field is the largest size of a square submatrix
with nonzero determinant.  This is the fact that makes the chain strata of
`Strata.lean` locally closed subsets of affine space, cut out by polynomial
equations and inequations in the matrix entries; it is what lets the rank
profile of a matrix be compared between a point and the generic point of an
arc through it.

Mathlib has the easy half (`Matrix.rank_of_det_ne_zero` together with
`Matrix.rank_submatrix_le`); the other half, `exists_submatrix_det_ne_zero`,
is proved here by extracting `k` linearly independent rows and then `k`
linearly independent columns of the resulting matrix.
-/

namespace Height.Toolbox

open Matrix

universe u

variable {K : Type u} [Field K]

/-- A matrix over a field has `rank` many linearly independent rows. -/
theorem exists_indep_rows {p q : ℕ} (A : Matrix (Fin p) (Fin q) K) :
    ∃ f : Fin A.rank → Fin p, LinearIndependent K (A.row ∘ f) := by
  classical
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K A.row
  have hfin : Finite κ := Finite.of_injective a ha
  have : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = A.rank := by
    rw [A.rank_eq_finrank_span_row, ← hspan, finrank_span_eq_card hli]
  refine ⟨a ∘ (Fintype.equivFinOfCardEq hcard).symm, ?_⟩
  exact hli.comp _ (Fintype.equivFinOfCardEq hcard).symm.injective

/-- Any number of rows up to the rank can be chosen linearly independent. -/
theorem exists_indep_rows_le {p q k : ℕ} (A : Matrix (Fin p) (Fin q) K) (hk : k ≤ A.rank) :
    ∃ f : Fin k → Fin p, LinearIndependent K (A.row ∘ f) := by
  obtain ⟨f, hf⟩ := exists_indep_rows A
  exact ⟨f ∘ Fin.castLE hk, hf.comp _ (Fin.castLE_injective hk)⟩

/-- Rank by minors, the substantial half: if `k ≤ rank A` then some `k × k`
submatrix of `A` is nonsingular. -/
theorem exists_submatrix_det_ne_zero {p q k : ℕ} (A : Matrix (Fin p) (Fin q) K)
    (hk : k ≤ A.rank) :
    ∃ (f : Fin k → Fin p) (g : Fin k → Fin q), (A.submatrix f g).det ≠ 0 := by
  classical
  obtain ⟨f, hf⟩ := exists_indep_rows_le A hk
  have hBrow : (A.submatrix f id).row = A.row ∘ f := rfl
  have hBrank : (A.submatrix f id).rank = k := by
    rw [LinearIndependent.rank_matrix (hBrow ▸ hf), Fintype.card_fin]
  have hBT : k ≤ ((A.submatrix f id)ᵀ).rank := by
    rw [Matrix.rank_transpose, hBrank]
  obtain ⟨g, hg⟩ := exists_indep_rows_le ((A.submatrix f id)ᵀ) hBT
  refine ⟨f, g, ?_⟩
  have hCrow : (((A.submatrix f id)ᵀ).submatrix g id).row = ((A.submatrix f id)ᵀ).row ∘ g := rfl
  have hunit : IsUnit (((A.submatrix f id)ᵀ).submatrix g id) :=
    Matrix.linearIndependent_rows_iff_isUnit.mp (hCrow ▸ hg)
  have hdet : (((A.submatrix f id)ᵀ).submatrix g id).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp hunit).ne_zero
  have hEq : ((A.submatrix f id)ᵀ).submatrix g id = (A.submatrix f g)ᵀ := by
    ext i j
    rfl
  rw [hEq, Matrix.det_transpose] at hdet
  exact hdet

/-- The easy half: a nonsingular square submatrix is a lower bound for the
rank. -/
theorem le_rank_of_submatrix_det_ne_zero {p q k : ℕ} (A : Matrix (Fin p) (Fin q) K)
    (f : Fin k → Fin p) (g : Fin k → Fin q) (h : (A.submatrix f g).det ≠ 0) :
    k ≤ A.rank := by
  have h1 : (A.submatrix f g).rank = k := by
    rw [Matrix.rank_of_det_ne_zero h, Fintype.card_fin]
  rw [← h1]
  exact Matrix.rank_submatrix_le A f g

/-- Rank by minors: `k ≤ rank A` iff some `k × k` submatrix of `A` is
nonsingular. -/
theorem le_rank_iff_exists_submatrix_det_ne_zero {p q : ℕ} (A : Matrix (Fin p) (Fin q) K)
    (k : ℕ) :
    k ≤ A.rank ↔
      ∃ (f : Fin k → Fin p) (g : Fin k → Fin q), (A.submatrix f g).det ≠ 0 :=
  ⟨exists_submatrix_det_ne_zero A, fun ⟨f, g, h⟩ => le_rank_of_submatrix_det_ne_zero A f g h⟩

/-- The rank is determined by which minors vanish: if all `(r+1) × (r+1)`
minors vanish and some `r × r` minor does not, the rank is `r`. -/
theorem rank_eq_of_minors {p q r : ℕ} (A : Matrix (Fin p) (Fin q) K)
    (hvanish : ∀ (f : Fin (r + 1) → Fin p) (g : Fin (r + 1) → Fin q),
      (A.submatrix f g).det = 0)
    (f₀ : Fin r → Fin p) (g₀ : Fin r → Fin q) (hne : (A.submatrix f₀ g₀).det ≠ 0) :
    A.rank = r := by
  refine le_antisymm ?_ (le_rank_of_submatrix_det_ne_zero A f₀ g₀ hne)
  by_contra hlt
  obtain ⟨f, g, h⟩ := exists_submatrix_det_ne_zero A (Nat.not_le.mp hlt)
  exact h (hvanish f g)

end Height.Toolbox
