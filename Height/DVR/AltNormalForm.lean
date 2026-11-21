import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# The hyperbolic normal form of an alternating matrix over a valuation ring

`lem:local-pairing` of the paper: an alternating
matrix over a discrete valuation ring is congruent, by an invertible matrix
over the ring, to a direct sum of hyperbolic blocks `[[0, dᵢ], [-dᵢ, 0]]` and
zeros.  The proof is the classical one: pick an entry of minimal valuation —
necessarily off the diagonal, which vanishes — move it to the last two
coordinates, clear its row and column by simultaneous row/column operations
(possible because it divides every entry), and induct on the size.

Only total divisibility is used, so everything is stated over a
`ValuationRing`; `PowerSeries K` is one.

## Main definitions and results

* `Height.DVR.IsAltMatrix` — vanishing diagonal and skew symmetry.
* `Height.DVR.hypNF n d` — the normal form: hyperbolic `2×2` blocks stacked at
  the *end* of the index range, so that `hypNF (m+2) d` restricted to the first
  `m` coordinates is `hypNF m d`.
* `Height.DVR.alt_hyperbolic` — the normal form theorem.
-/

namespace Height.DVR

open Matrix Finset

universe u

section AltMatrix

variable {R : Type u} [CommRing R] {ι : Type*}

/-- An alternating matrix: the diagonal vanishes and the matrix is skew.  Both
conditions are imposed, since in characteristic two the second does not imply
the first. -/
structure IsAltMatrix (M : Matrix ι ι R) : Prop where
  diag : ∀ i, M i i = 0
  skew : ∀ i j, M j i = -M i j

theorem IsAltMatrix.submatrix {κ : Type*} {M : Matrix ι ι R}
    (h : IsAltMatrix M) (f : κ → ι) : IsAltMatrix (M.submatrix f f) :=
  ⟨fun _ => h.diag _, fun _ _ => h.skew _ _⟩

end AltMatrix

section GramPair

variable {R : Type u} [CommRing R] {ι : Type*} [Fintype ι]

/-- The bilinear pairing attached to a square matrix. -/
def gramPair (M : Matrix ι ι R) (x y : ι → R) : R := x ⬝ᵥ (M *ᵥ y)

theorem gramPair_eq_sum (M : Matrix ι ι R) (x y : ι → R) :
    gramPair M x y = ∑ i, ∑ j, x i * M i j * y j := by
  simp [gramPair, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

/-- A congruence `Tᵀ M T` is the matrix of `gramPair M` in the columns of
`T`. -/
theorem transpose_mul_mul_apply (T M : Matrix ι ι R) (k l : ι) :
    (Tᵀ * M * T) k l = gramPair M (fun i => T i k) (fun i => T i l) := by
  rw [gramPair_eq_sum]
  simp only [Matrix.mul_apply, transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

@[simp] theorem gramPair_single_single [DecidableEq ι] (M : Matrix ι ι R)
    (i j : ι) : gramPair M (Pi.single i 1) (Pi.single j 1) = M i j := by
  simp [gramPair]

theorem gramPair_add_left (M : Matrix ι ι R) (x y z : ι → R) :
    gramPair M (x + y) z = gramPair M x z + gramPair M y z := by
  simp [gramPair, add_dotProduct]

theorem gramPair_sub_left (M : Matrix ι ι R) (x y z : ι → R) :
    gramPair M (x - y) z = gramPair M x z - gramPair M y z := by
  simp [gramPair, sub_dotProduct]

theorem gramPair_smul_left (M : Matrix ι ι R) (c : R) (x y : ι → R) :
    gramPair M (c • x) y = c * gramPair M x y := by
  simp [gramPair, smul_dotProduct, smul_eq_mul]

theorem gramPair_add_right (M : Matrix ι ι R) (x y z : ι → R) :
    gramPair M x (y + z) = gramPair M x y + gramPair M x z := by
  simp [gramPair, mulVec_add, dotProduct_add]

theorem gramPair_sub_right (M : Matrix ι ι R) (x y z : ι → R) :
    gramPair M x (y - z) = gramPair M x y - gramPair M x z := by
  simp [gramPair, mulVec_sub, dotProduct_sub]

theorem gramPair_smul_right (M : Matrix ι ι R) (c : R) (x y : ι → R) :
    gramPair M x (c • y) = c * gramPair M x y := by
  simp [gramPair, mulVec_smul, dotProduct_smul, smul_eq_mul]

/-- The pairing of an alternating matrix is skew. -/
theorem gramPair_skew {M : Matrix ι ι R} (h : IsAltMatrix M) (x y : ι → R) :
    gramPair M y x = -gramPair M x y := by
  rw [gramPair_eq_sum, gramPair_eq_sum]
  have hrw : (∑ i, ∑ j, y i * M i j * x j)
      = ∑ i, ∑ j, -(x j * M j i * y i) :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      rw [h.skew j i]; ring
  rw [hrw]
  simp only [Finset.sum_neg_distrib]
  congr 1
  exact Finset.sum_comm

/-- The pairing of an alternating matrix is alternating, in every
characteristic. -/
theorem gramPair_self {M : Matrix ι ι R} (h : IsAltMatrix M) (x : ι → R) :
    gramPair M x x = 0 := by
  classical
  rw [gramPair_eq_sum, ← Finset.sum_product']
  refine Finset.sum_ninvolution (f := fun p : ι × ι => x p.1 * M p.1 p.2 * x p.2)
    Prod.swap ?_ ?_ ?_ ?_
  · rintro ⟨i, j⟩
    show x i * M i j * x j + x j * M j i * x i = 0
    rw [h.skew i j]
    ring
  · rintro ⟨i, j⟩ hne hcon
    apply hne
    simp only [Prod.swap_prod_mk, Prod.mk.injEq] at hcon
    obtain ⟨hji, -⟩ := hcon
    subst hji
    show x j * M j j * x j = 0
    rw [h.diag, mul_zero, zero_mul]
  · rintro ⟨i, j⟩
    simp
  · rintro ⟨i, j⟩
    rfl

/-- A congruence of an alternating matrix is alternating. -/
theorem IsAltMatrix.congr {M : Matrix ι ι R} (h : IsAltMatrix M)
    (T : Matrix ι ι R) : IsAltMatrix (Tᵀ * M * T) where
  diag i := by rw [transpose_mul_mul_apply]; exact gramPair_self h _
  skew i j := by rw [transpose_mul_mul_apply, transpose_mul_mul_apply]
                 exact gramPair_skew h _ _

end GramPair

section HypNF

variable {R : Type u} [CommRing R]

/-- The hyperbolic normal form on `Fin n`: `2×2` blocks
`[[0, d i], [-d i, 0]]` on the coordinate pairs `(i, i+1)` with `i ≡ n [2]`,
so that the blocks are stacked at the end of the index range and a single
zero row and column is left in front when `n` is odd. -/
def hypNF (R : Type u) [CommRing R] (n : ℕ) (d : ℕ → R) :
    Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j =>
    if (j : ℕ) = (i : ℕ) + 1 ∧ Even ((i : ℕ) + n) then d (i : ℕ)
    else if (i : ℕ) = (j : ℕ) + 1 ∧ Even ((j : ℕ) + n) then -d (j : ℕ)
    else 0

theorem hypNF_apply (n : ℕ) (d : ℕ → R) (i j : Fin n) :
    hypNF R n d i j =
      if (j : ℕ) = (i : ℕ) + 1 ∧ Even ((i : ℕ) + n) then d (i : ℕ)
      else if (i : ℕ) = (j : ℕ) + 1 ∧ Even ((j : ℕ) + n) then -d (j : ℕ)
      else 0 := rfl

theorem hypNF_zero (n : ℕ) : hypNF R n (fun _ => 0) = 0 := by
  ext i j
  rw [hypNF_apply]
  split_ifs <;> simp

/-- The normal form on `Fin (m+2)` restricts, on the first `m` coordinates, to
the normal form on `Fin m` with the *same* exponent family: `d` is indexed by
the position of the block. -/
theorem hypNF_submatrix_castAdd (m : ℕ) (d : ℕ → R) :
    (hypNF R (m + 2) d).submatrix (Fin.castAdd 2) (Fin.castAdd 2)
      = hypNF R m d := by
  ext i j
  simp only [Matrix.submatrix_apply, hypNF_apply, Fin.val_castAdd]
  have h₁ : Even ((i : ℕ) + (m + 2)) ↔ Even ((i : ℕ) + m) := by
    simp only [Nat.even_iff]; omega
  have h₂ : Even ((j : ℕ) + (m + 2)) ↔ Even ((j : ℕ) + m) := by
    simp only [Nat.even_iff]; omega
  simp only [h₁, h₂]

/-- The elementary `2 × 2` hyperbolic block `[[0, a], [-a, 0]]`. -/
def hyp2 (a : R) : Matrix (Fin 2) (Fin 2) R :=
  Matrix.of fun i j =>
    if (i : ℕ) = 0 ∧ (j : ℕ) = 1 then a
    else if (i : ℕ) = 1 ∧ (j : ℕ) = 0 then -a else 0

theorem hyp2_apply (a : R) (i j : Fin 2) :
    hyp2 a i j =
      if (i : ℕ) = 0 ∧ (j : ℕ) = 1 then a
      else if (i : ℕ) = 1 ∧ (j : ℕ) = 0 then -a else 0 := rfl

theorem hypNF_congr (n : ℕ) {d d' : ℕ → R} (h : ∀ k, k < n → d k = d' k) :
    hypNF R n d = hypNF R n d' := by
  ext i j
  rw [hypNF_apply, hypNF_apply, h i i.isLt, h j j.isLt]

/-- The normal form on `Fin (m + 2)`, read in the block decomposition
`Fin m ⊕ Fin 2`, is the normal form on `Fin m` plus a single hyperbolic
block. -/
theorem hypNF_submatrix_finSumFinEquiv (m : ℕ) (d : ℕ → R) :
    (hypNF R (m + 2) d).submatrix finSumFinEquiv finSumFinEquiv
      = Matrix.fromBlocks (hypNF R m d) 0 0 (hyp2 (d m)) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simp only [Matrix.submatrix_apply, finSumFinEquiv_apply_left,
      Matrix.fromBlocks_apply₁₁]
    have h := congrFun (congrFun (hypNF_submatrix_castAdd (R := R) m d) i) j
    simpa [Matrix.submatrix_apply] using h
  · simp only [Matrix.submatrix_apply, finSumFinEquiv_apply_left,
      finSumFinEquiv_apply_right, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply,
      hypNF_apply, Fin.val_castAdd, Fin.val_natAdd]
    have hi := i.isLt
    have hj := j.isLt
    have h1 : ¬((m + (j : ℕ)) = (i : ℕ) + 1 ∧ Even ((i : ℕ) + (m + 2))) := by
      rintro ⟨h, he⟩
      rw [Nat.even_iff] at he
      omega
    have h2 : ¬((i : ℕ) = m + (j : ℕ) + 1 ∧ Even (m + (j : ℕ) + (m + 2))) := by
      rintro ⟨h, -⟩; omega
    rw [ite_eq_right h1, ite_eq_right h2]
  · simp only [Matrix.submatrix_apply, finSumFinEquiv_apply_left,
      finSumFinEquiv_apply_right, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply,
      hypNF_apply, Fin.val_castAdd, Fin.val_natAdd]
    have hi := i.isLt
    have hj := j.isLt
    have h1 : ¬((j : ℕ) = m + (i : ℕ) + 1 ∧ Even (m + (i : ℕ) + (m + 2))) := by
      rintro ⟨h, -⟩; omega
    have h2 : ¬((m + (i : ℕ)) = (j : ℕ) + 1 ∧ Even ((j : ℕ) + (m + 2))) := by
      rintro ⟨h, he⟩
      rw [Nat.even_iff] at he
      omega
    rw [ite_eq_right h1, ite_eq_right h2]
  · have hi := i.isLt
    have hj := j.isLt
    have hpar1 : Even ((m + (i : ℕ)) + (m + 2)) ↔ (i : ℕ) = 0 := by
      constructor
      · intro h; rw [Nat.even_iff] at h; omega
      · intro h; rw [Nat.even_iff]; omega
    have hpar2 : Even ((m + (j : ℕ)) + (m + 2)) ↔ (j : ℕ) = 0 := by
      constructor
      · intro h; rw [Nat.even_iff] at h; omega
      · intro h; rw [Nat.even_iff]; omega
    simp only [Matrix.submatrix_apply, finSumFinEquiv_apply_right,
      Matrix.fromBlocks_apply₂₂, hypNF_apply, hyp2_apply, Fin.val_natAdd,
      hpar1, hpar2]
    by_cases hA : (m + (j : ℕ)) = (m + (i : ℕ)) + 1 ∧ (i : ℕ) = 0
    · have hj1 : (j : ℕ) = 1 := by omega
      rw [ite_eq_left hA, ite_eq_left (⟨hA.2, hj1⟩ : (i : ℕ) = 0 ∧ (j : ℕ) = 1),
        hA.2, Nat.add_zero]
    · by_cases hB : (m + (i : ℕ)) = (m + (j : ℕ)) + 1 ∧ (j : ℕ) = 0
      · have hi1 : (i : ℕ) = 1 := by omega
        rw [ite_eq_right hA, ite_eq_left hB,
          ite_eq_right (by rintro ⟨h1, h2⟩; omega),
          ite_eq_left (⟨hi1, hB.2⟩ : (i : ℕ) = 1 ∧ (j : ℕ) = 0),
          hB.2, Nat.add_zero]
      · rw [ite_eq_right hA, ite_eq_right hB,
          ite_eq_right (by rintro ⟨h1, h2⟩; exact hA ⟨by omega, h1⟩),
          ite_eq_right (by rintro ⟨h1, h2⟩; exact hB ⟨by omega, h2⟩)]

end HypNF
