import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

/-!
# Numerical invariants from column lengths (`lem:springer-dim`)

The Springer and centralizer dimension counts only use the finite list of
column lengths of a partition.  We state the required identity for an
arbitrary finite family of natural numbers.
-/

namespace Height.Toolbox

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- The size of a diagram, expressed as the sum of its column lengths. -/
def diagramSize (cols : ι → ℕ) : ℕ := ∑ i, cols i

/-- The centralizer count `c(λ) = ∑ᵢ (λ'ᵢ)²`. -/
def centralizerCount (cols : ι → ℕ) : ℕ := ∑ i, (cols i) ^ 2

/-- The Springer count `n(λ) = ∑ᵢ binom(λ'ᵢ, 2)`. -/
def springerCount (cols : ι → ℕ) : ℕ := ∑ i, (cols i).choose 2

omit [Fintype ι] in
private theorem sum_sq_le_sq_sum (s : Finset ι) (f : ι → ℕ) :
    (∑ i ∈ s, (f i) ^ 2) ≤ (∑ i ∈ s, f i) ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      calc
        f a ^ 2 + ∑ i ∈ s, f i ^ 2 ≤
            f a ^ 2 + (∑ i ∈ s, f i) ^ 2 := Nat.add_le_add_left ih _
        _ ≤ (f a + ∑ i ∈ s, f i) ^ 2 := by
          nlinarith [Nat.zero_le (f a), Nat.zero_le (∑ i ∈ s, f i)]

/-- The sum of the squared column lengths is at most the square of the
diagram size. -/
theorem centralizerCount_le_diagramSize_sq (cols : ι → ℕ) :
    centralizerCount cols ≤ (diagramSize cols) ^ 2 := by
  exact sum_sq_le_sq_sum Finset.univ cols

private theorem square_eq_self_add_two_choose (a : ℕ) :
    a ^ 2 = a + 2 * a.choose 2 := by
  induction a with
  | zero => simp
  | succ a ih =>
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
      simp only [Nat.succ_eq_add_one]
      nlinarith

/-- The numerical identity `c(λ) = |λ| + 2 n(λ)` used in the Springer
dimension calculation. -/
theorem centralizerCount_eq_size_add_two_springerCount (cols : ι → ℕ) :
    centralizerCount cols = diagramSize cols + 2 * springerCount cols := by
  simp only [centralizerCount, diagramSize, springerCount,
    square_eq_self_add_two_choose, Finset.sum_add_distrib, Finset.mul_sum]

/-- The source's form `c(λ) = n + 2 n(λ)` when the column lengths sum to
`n`. -/
theorem centralizerCount_eq_of_diagramSize_eq (cols : ι → ℕ) {n : ℕ}
    (hsize : diagramSize cols = n) :
    centralizerCount cols = n + 2 * springerCount cols := by
  rw [centralizerCount_eq_size_add_two_springerCount, hsize]

end Height.Toolbox
