import QSteenrod.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Univ
import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Universal characteristic-polynomial coefficients and their Steenrod powers

Let `Y` be the generic `N × N` matrix over `GaloisField p r`.  We normalize the
coefficients of

`det(T · 1 - Y) = T^N - c₁ T^(N-1) + ⋯ + (-1)^N c_N`

so that `c_N = det(Y)`.  The elements `Pⁱ(cⱼ)` are collected in the order

`j = 1, …, N`, and, for each `j`, `i = 0, …, j - 1`.
-/

namespace QSteenrod

variable (p r N : ℕ) [Fact p.Prime]

/-- The coordinate ring of the affine space of `N × N` matrices over `GaloisField p r`. -/
abbrev GenericMatrixRing := MvPolynomial (Fin N × Fin N) (GaloisField p r)

/-- The signed `j`th characteristic-polynomial coefficient of the generic
matrix.  The sign convention is chosen so that `c p r N N` is the
determinant. -/
noncomputable def c (j : ℕ) : GenericMatrixRing p r N :=
  (-1) ^ j * (Matrix.charpoly.univ (GaloisField p r) (Fin N)).coeff (N - j)

/-- The ordered lattice points in the strict lower triangle

`{(i, j) | 0 ≤ i < j ≤ N}`.

The outer order is increasing `j`; within each row, `i` is increasing.  Thus,
for example, `strictLowerTriangleIndices 3` is

`[(0, 1), (0, 2), (1, 2), (0, 3), (1, 3), (2, 3)]`.

Mathlib has antidiagonal enumerators for pairs with a fixed sum, but no
dedicated ordered list for this triangular region.
-/
def strictLowerTriangleIndices (N : ℕ) : List (ℕ × ℕ) :=
  (List.range' 1 N).flatMap fun j =>
    (List.range j).map fun i => (i, j)

/-- Membership in the immutable enumeration is exactly membership in the
strict lower triangle. -/
theorem mem_strictLowerTriangleIndices_iff (N i j : ℕ) :
    (i, j) ∈ strictLowerTriangleIndices N ↔ 1 ≤ j ∧ j ≤ N ∧ i < j := by
  constructor
  · intro h
    simp only [strictLowerTriangleIndices, List.mem_flatMap, List.mem_map] at h
    obtain ⟨j', hj', i', hi', hij⟩ := h
    obtain ⟨k, hkN, hk⟩ := List.mem_range'.mp hj'
    have hj1 : 1 ≤ j' := by omega
    have hjN : j' ≤ N := by omega
    have hi : i' < j' := List.mem_range.mp hi'
    injection hij with hii hjj
    omega
  · rintro ⟨hj1, hjN, hij⟩
    apply List.mem_flatMap.mpr
    refine ⟨j, ?_, ?_⟩
    · apply List.mem_range'.mpr
      exact ⟨j - 1, by omega, by omega⟩
    · apply List.mem_map.mpr
      exact ⟨i, List.mem_range.mpr hij, rfl⟩

/-- The list

`P⁰(c₁), P⁰(c₂), P¹(c₂), …, P⁰(c_N), …, P^(N-1)(c_N)`.

Equivalently, this lists `Pⁱ(cⱼ)` for every `0 ≤ i < j ≤ N`, ordered first by
increasing `j` and then by increasing `i`.
-/
noncomputable def powerCharacteristicCoefficients : List (GenericMatrixRing p r N) :=
  (strictLowerTriangleIndices N).map fun ij => P p r ij.1 (c p r N ij.2)

end QSteenrod
