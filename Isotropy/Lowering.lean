/-
Strictly flag-lowering matrices.

A matrix is *lowering* when it carries `S_{k+1}` into `S_k` and
*preserving* when it carries each `S_k` into itself.  Lowering matrices are
nilpotent, hence traceless over a field: that vanishing is step (v) of the
DVR core (`Isotropy/DVRCore.lean`) and, through the trace pairing, the whole
content of the field lemma (`Isotropy/FieldLemma.lean`).

The closure properties here are the ones both consumers need: a lowering
matrix stays lowering after composing with a preserving one, and `ad_P` of
a preserving matrix is lowering.
-/
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Isotropy.DPow

namespace Isotropy

open Matrix

variable {R : Type*} [CommRing R] {n : ℕ}

/-- Vanishing flag motions is the same as lowering the flag: this is the
`⟹` direction, the one that turns a direction with no flag motion into a
commutator.  Immediate from the mirror chain rule. -/
theorem lowering_of_dpow_vanishing {P Q : Matrix (Fin n) (Fin n) R}
    (h : ∀ k, ∀ v ∈ kerFlag P k, (dpow P Q k).mulVec v = 0) :
    ∀ k, ∀ v ∈ kerFlag P (k + 1), Q.mulVec v ∈ kerFlag P k := by
  intro k v hv
  have h1 : (dpow P Q (k + 1)).mulVec v = 0 := h (k + 1) v hv
  rw [dpow_succ', add_mulVec, ← mulVec_mulVec, ← mulVec_mulVec,
    h k _ (mulVec_mem_kerFlag hv), zero_add] at h1
  exact mem_kerFlag.mpr h1

/-- The converse: a matrix that lowers the kernel flag has *no* flag motion —
`D_k(Q)` kills `S_k`.

This is the first-order form of "a lowering perturbation does not move the
kernel flag": deforming `P` to `P + ε Q` with `ε² = 0` changes `P^k` by
`ε D_k(Q)`, so `S_k` stays inside the kernel of the deformed `k`-th power.
It is what turns the velocity decomposition `Ṗ = [P, X] + U` into a statement
about the motion of the flag: only the commutator part moves it. -/
theorem dpow_vanishing_of_lowering {P Q : Matrix (Fin n) (Fin n) R}
    (h : ∀ k, ∀ v ∈ kerFlag P (k + 1), Q.mulVec v ∈ kerFlag P k) :
    ∀ k, ∀ v ∈ kerFlag P k, (dpow P Q k).mulVec v = 0 := by
  intro k
  induction k with
  | zero =>
      intro v _
      simp
  | succ k ih =>
      intro v hv
      rw [dpow_succ', add_mulVec, ← mulVec_mulVec, ← mulVec_mulVec,
        ih _ (mulVec_mem_kerFlag hv), zero_add]
      exact mem_kerFlag.mp (h k v hv)

/-- Lowering the kernel flag and having no flag motion are the same thing. -/
theorem lowering_iff_dpow_vanishing {P Q : Matrix (Fin n) (Fin n) R} :
    (∀ k, ∀ v ∈ kerFlag P (k + 1), Q.mulVec v ∈ kerFlag P k) ↔
      ∀ k, ∀ v ∈ kerFlag P k, (dpow P Q k).mulVec v = 0 :=
  ⟨dpow_vanishing_of_lowering, lowering_of_dpow_vanishing⟩

/-- `ad_P` of a flag-preserving matrix lowers the flag. -/
theorem lowering_ad_of_preserving {P B : Matrix (Fin n) (Fin n) R}
    (hB : ∀ k, ∀ v ∈ kerFlag P k, B.mulVec v ∈ kerFlag P k) :
    ∀ k, ∀ v ∈ kerFlag P (k + 1), (B * P - P * B).mulVec v ∈ kerFlag P k := by
  intro k v hv
  rw [sub_mulVec, ← mulVec_mulVec, ← mulVec_mulVec]
  exact Submodule.sub_mem _
    (hB k _ (mulVec_mem_kerFlag hv))
    (mulVec_mem_kerFlag (hB (k + 1) v hv))

/-- Lowering absorbs a flag-preserving matrix on the right. -/
theorem lowering_mul_preserving {P L C : Matrix (Fin n) (Fin n) R}
    (hL : ∀ k, ∀ v ∈ kerFlag P (k + 1), L.mulVec v ∈ kerFlag P k)
    (hC : ∀ k, ∀ v ∈ kerFlag P k, C.mulVec v ∈ kerFlag P k) :
    ∀ k, ∀ v ∈ kerFlag P (k + 1), (L * C).mulVec v ∈ kerFlag P k := by
  intro k v hv
  rw [← mulVec_mulVec]
  exact hL k _ (hC (k + 1) v hv)

/-- Step (v), the vanishing: a matrix strictly lowering an exhaustive kernel
flag is nilpotent, hence traceless (a field is reduced). -/
theorem trace_eq_zero_of_lowering
    {F : Type*} [Field F]
    (P : Matrix (Fin n) (Fin n) F) (hP : P ^ n = 0)
    (B : Matrix (Fin n) (Fin n) F)
    (hB : ∀ k, ∀ v ∈ kerFlag P (k + 1), B.mulVec v ∈ kerFlag P k) :
    trace B = 0 := by
  have htop : kerFlag P n = ⊤ := kerFlag_eq_top hP
  have key : ∀ j, j ≤ n → ∀ v : Fin n → F, (B ^ j).mulVec v ∈ kerFlag P (n - j) := by
    intro j
    induction j with
    | zero =>
      intro _ v
      rw [pow_zero, one_mulVec, Nat.sub_zero, htop]
      exact Submodule.mem_top
    | succ j ih =>
      intro hj v
      rw [pow_succ', ← mulVec_mulVec]
      have h1 := ih (by omega) v
      rw [show n - j = (n - (j + 1)) + 1 by omega] at h1
      exact hB _ _ h1
  have hBn : B ^ n = 0 := by
    ext i j
    have h := key n le_rfl (Pi.single j 1)
    rw [Nat.sub_self, kerFlag_zero, Submodule.mem_bot, mulVec_single_one] at h
    simpa using congrFun h i
  exact IsNilpotent.eq_zero (Matrix.isNilpotent_trace_of_isNilpotent ⟨n, hBn⟩)

/-- The trace identity behind both the field lemma and step (v):
`ad_P` is skew for the trace pairing. -/
theorem trace_ad_mul (P A Y : Matrix (Fin n) (Fin n) R) :
    trace ((P * A - A * P) * Y) = trace (A * (Y * P - P * Y)) := by
  rw [sub_mul, trace_sub, mul_sub, trace_sub]
  congr 1
  · rw [mul_assoc, trace_mul_comm, mul_assoc]
  · rw [mul_assoc]

/-- The same identity with the commutator on the right. -/
theorem trace_mul_ad (B P C : Matrix (Fin n) (Fin n) R) :
    trace (B * (P * C - C * P)) = trace ((B * P - P * B) * C) := by
  rw [mul_sub, trace_sub, sub_mul, trace_sub]
  congr 1
  · rw [mul_assoc]
  · rw [← mul_assoc, trace_mul_comm, mul_assoc]

end Isotropy
