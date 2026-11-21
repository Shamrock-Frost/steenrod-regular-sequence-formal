import Mathlib.Algebra.BigOperators.Module
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

/-!
# Majorization and the sum of squares

One inequality, used by `Toolbox/Jordan.lean` to compare centraliser
dimensions: if the nonincreasing sequence `a` *majorizes* `b` — every partial
sum of `b` is at most the corresponding partial sum of `a`, and the totals agree
— then `∑ b² ≤ ∑ a²`.

This is the Schur convexity of `x ↦ ∑ xᵢ²`, and the proof is summation by parts
(`Finset.sum_range_by_parts`) applied to `∑ (aᵢ + bᵢ)(aᵢ − bᵢ)`: the boundary
term vanishes because the totals agree, and every remaining term is a product of
a nonpositive increment of `a + b` with a nonnegative partial sum of `a − b`.

Nothing here mentions matrices or partitions; the statement is about sequences
in an ordered ring, and `ℤ` is the only instance needed.  Stated on `ℤ` rather
than `ℕ` so that no truncated subtraction appears.
-/

namespace Height.Toolbox

open Finset

/-- **Schur convexity of the sum of squares.**  If `a` and `b` are
nonincreasing, every partial sum of `b` is at most that of `a`, and the two
totals over `range N` agree, then `∑ b² ≤ ∑ a²`. -/
theorem sum_sq_le_sum_sq_of_majorizes {N : ℕ} (a b : ℕ → ℤ)
    (ha : ∀ i j, i ≤ j → a j ≤ a i) (hb : ∀ i j, i ≤ j → b j ≤ b i)
    (hpart : ∀ k, ∑ i ∈ range k, b i ≤ ∑ i ∈ range k, a i)
    (htot : ∑ i ∈ range N, b i = ∑ i ∈ range N, a i) :
    ∑ i ∈ range N, b i ^ 2 ≤ ∑ i ∈ range N, a i ^ 2 := by
  have key := Finset.sum_range_by_parts (fun i => a i + b i) (fun i => a i - b i) N
  simp only [smul_eq_mul] at key
  have hzero : ∑ i ∈ range N, (a i - b i) = 0 := by
    rw [Finset.sum_sub_distrib, htot, sub_self]
  rw [hzero, mul_zero, zero_sub] at key
  have hterm : ∀ i ∈ range (N - 1),
      ((a (i + 1) + b (i + 1)) - (a i + b i)) * (∑ j ∈ range (i + 1), (a j - b j)) ≤ 0 := by
    intro i _
    have h1 : (a (i + 1) + b (i + 1)) - (a i + b i) ≤ 0 := by
      have h1a := ha i (i + 1) (Nat.le_succ i)
      have h1b := hb i (i + 1) (Nat.le_succ i)
      linarith
    have h2 : 0 ≤ ∑ j ∈ range (i + 1), (a j - b j) := by
      rw [Finset.sum_sub_distrib]
      linarith [hpart (i + 1)]
    nlinarith
  have hsum := Finset.sum_nonpos hterm
  have hLHS : ∑ i ∈ range N, (a i + b i) * (a i - b i)
      = (∑ i ∈ range N, a i ^ 2) - ∑ i ∈ range N, b i ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hLHS] at key
  linarith
