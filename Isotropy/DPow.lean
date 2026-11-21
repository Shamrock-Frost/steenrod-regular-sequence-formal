import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# `D_k`, the derivative of `P ^ k` in a direction `Q`

    dpow P Q k = ∑_{j<k} P^j * Q * P^(k-1-j)

Integer coefficients; no
characteristic enters.  The identities below are the only facts about it the
proofs use, and `DCond` is the kernel-flatness condition they take as a
hypothesis.
-/

namespace Isotropy

open Matrix

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The derivative of `P ^ k` in the direction `Q`. -/
def dpow (P Q : Matrix (Fin n) (Fin n) R) (k : ℕ) : Matrix (Fin n) (Fin n) R :=
  ∑ j ∈ Finset.range k, P ^ j * Q * P ^ (k - 1 - j)

@[simp] theorem dpow_zero (P Q : Matrix (Fin n) (Fin n) R) : dpow P Q 0 = 0 := by
  simp [dpow]

@[simp] theorem dpow_one (P Q : Matrix (Fin n) (Fin n) R) : dpow P Q 1 = Q := by
  simp [dpow]

/-- Chain rule along the flag: `D_{k+1}(Q) = P·D_k(Q) + Q·P^k`. -/
theorem dpow_succ (P Q : Matrix (Fin n) (Fin n) R) (k : ℕ) :
    dpow P Q (k + 1) = P * dpow P Q k + Q * P ^ k := by
  rw [dpow, Finset.sum_range_succ', dpow, Finset.mul_sum]
  simp only [Nat.add_sub_cancel, pow_zero, one_mul, Nat.sub_zero]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show k - (i + 1) = k - 1 - i by omega, pow_succ']
  simp only [mul_assoc]

/-- The mirror chain rule: `D_{k+1}(Q) = D_k(Q)·P + P^k·Q`. -/
theorem dpow_succ' (P Q : Matrix (Fin n) (Fin n) R) (k : ℕ) :
    dpow P Q (k + 1) = dpow P Q k * P + P ^ k * Q := by
  rw [dpow, Finset.sum_range_succ, dpow, Finset.sum_mul]
  simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, mul_one]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [show k - i = (k - 1 - i) + 1 by have := Finset.mem_range.mp hi; omega,
    pow_succ, ← mul_assoc]

/-- Telescoping: `D_k([P, A]) = P^k·A − A·P^k`. -/
theorem dpow_commutator (P A : Matrix (Fin n) (Fin n) R) (k : ℕ) :
    dpow P (P * A - A * P) k = P ^ k * A - A * P ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [dpow_succ, ih]
    simp only [pow_succ', mul_sub, sub_mul, mul_assoc]
    abel
theorem dpow_add (P Q₁ Q₂ : Matrix (Fin n) (Fin n) R) (k : ℕ) :
    dpow P (Q₁ + Q₂) k = dpow P Q₁ k + dpow P Q₂ k := by
  simp only [dpow, ← Finset.sum_add_distrib, mul_add, add_mul]

theorem dpow_map {S : Type*} [CommRing S] (f : R →+* S) (P Q : Matrix (Fin n) (Fin n) R)
    (k : ℕ) : (dpow P Q k).map f = dpow (P.map f) (Q.map f) k := by
  show (f.mapMatrix (dpow P Q k)) = _
  rw [dpow, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_mul, map_pow, map_pow]
  rfl


theorem dpow_sub (P Q₁ Q₂ : Matrix (Fin n) (Fin n) R) (k : ℕ) :
    dpow P (Q₁ - Q₂) k = dpow P Q₁ k - dpow P Q₂ k := by
  simp only [dpow, ← Finset.sum_sub_distrib, mul_sub, sub_mul]

/-- The kernel flag `S_k = ker(P^k)` as submodules of `Rⁿ`. -/
def kerFlag (P : Matrix (Fin n) (Fin n) R) (k : ℕ) : Submodule R (Fin n → R) :=
  LinearMap.ker (P ^ k).mulVecLin

theorem mem_kerFlag {P : Matrix (Fin n) (Fin n) R} {k : ℕ} {v : Fin n → R} :
    v ∈ kerFlag P k ↔ (P ^ k).mulVec v = 0 := by
  simp [kerFlag]

@[simp] theorem kerFlag_zero (P : Matrix (Fin n) (Fin n) R) : kerFlag P 0 = ⊥ := by
  simp [kerFlag]

theorem kerFlag_eq_top {P : Matrix (Fin n) (Fin n) R} {k : ℕ} (h : P ^ k = 0) :
    kerFlag P k = ⊤ := by
  simp [kerFlag, h]

theorem kerFlag_le_succ (P : Matrix (Fin n) (Fin n) R) (k : ℕ) :
    kerFlag P k ≤ kerFlag P (k + 1) := by
  intro v hv
  rw [mem_kerFlag] at hv ⊢
  rw [pow_succ', ← mulVec_mulVec, hv, mulVec_zero]

theorem kerFlag_mono (P : Matrix (Fin n) (Fin n) R) : Monotone (kerFlag P) :=
  monotone_nat_of_le_succ (kerFlag_le_succ P)

/-- `P` lowers its own kernel flag. -/
theorem mulVec_mem_kerFlag {P : Matrix (Fin n) (Fin n) R} {k : ℕ} {v : Fin n → R}
    (hv : v ∈ kerFlag P (k + 1)) : P.mulVec v ∈ kerFlag P k := by
  rw [mem_kerFlag] at hv ⊢
  rw [mulVec_mulVec, ← pow_succ]
  exact hv

/-- The kernel-flatness conditions: for every `k`, `D_k(Q)` carries
`ker P^k` into `im P^k`. -/
def DCond (P Q : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ k, ∀ v ∈ kerFlag P k, ∃ w, (P ^ k).mulVec w = (dpow P Q k).mulVec v

end Isotropy
