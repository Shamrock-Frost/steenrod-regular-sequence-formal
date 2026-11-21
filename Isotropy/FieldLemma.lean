/-
Over a field the kernel-flatness conditions cut out exactly `im ad_P`.
This replaces an orbit-tangency argument with linear
algebra: applied to the kernel-flatness conditions at the generic point of ℙ¹ it
*constructs* the matrices `A` that the DVR core consumes — no algebraic
groups, no separability.

The statement is `commutator_iff_dcond`, for all
`n` and every field.

The argument, avoiding Jordan form entirely:

  * the D-conditions minus their regular part `g` (Isotropy.RegularPart,
    over a field a PID like any other) leave a direction with all flag
    motions zero, i.e. one that strictly lowers the kernel flag;
  * a lowering `Q` is a commutator, by trace duality: were `Q ∉ im ad_P`,
    a functional would separate them, and every functional on matrices is
    `X ↦ tr(X·Y)`; killing `im ad_P` forces `Y ∈ Z(P)`, so `Y` preserves
    the flag, so `Q·Y` lowers it and `tr(Q·Y) = 0` — contradicting
    separation.
-/
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Isotropy.Lowering
import Isotropy.RegularPart

namespace Isotropy

open Matrix

variable {K : Type*} [Field K] {n : ℕ}

/-- The easy inclusion: commutators satisfy the D-conditions
(telescoping, `dpow_commutator`). -/
theorem dcond_of_commutator (P A : Matrix (Fin n) (Fin n) K) :
    DCond P (P * A - A * P) := by
  intro k v hv
  rw [mem_kerFlag] at hv
  refine ⟨A.mulVec v, ?_⟩
  rw [dpow_commutator, sub_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hv,
    mulVec_zero, sub_zero]

section Duality

/-- `ad_P` as a linear map, so that its image is a subspace. -/
private def adMap (P : Matrix (Fin n) (Fin n) K) :
    Matrix (Fin n) (Fin n) K →ₗ[K] Matrix (Fin n) (Fin n) K where
  toFun A := P * A - A * P
  map_add' A B := by rw [mul_add, add_mul]; abel
  map_smul' c A := by
    simp only [RingHom.id_apply, mul_smul_comm, smul_mul_assoc, smul_sub]

/-- The trace pairing in the form `X ↦ tr(X·Y)`. -/
private def traceRight (Y : Matrix (Fin n) (Fin n) K) :
    Module.Dual K (Matrix (Fin n) (Fin n) K) where
  toFun X := trace (X * Y)
  map_add' X X' := by rw [add_mul, trace_add]
  map_smul' c X := by rw [RingHom.id_apply, smul_mul_assoc, trace_smul]

private def traceRightMap :
    Matrix (Fin n) (Fin n) K →ₗ[K] Module.Dual K (Matrix (Fin n) (Fin n) K) where
  toFun := traceRight
  map_add' Y Y' := by ext X; simp [traceRight, mul_add, trace_add]
  map_smul' c Y := by ext X; simp [traceRight, trace_smul]

@[simp] private theorem traceRightMap_apply (Y X : Matrix (Fin n) (Fin n) K) :
    traceRightMap Y X = trace (X * Y) := rfl

/-- Nondegeneracy of the trace pairing (`Matrix.ext_iff_trace_mul_left`). -/
private theorem traceRightMap_injective :
    Function.Injective (traceRightMap (K := K) (n := n)) := by
  intro Y Y' h
  refine Matrix.ext_iff_trace_mul_left.mpr fun X => ?_
  simpa using LinearMap.congr_fun h X

/-- …hence, by dimension count, every functional on matrices is a trace
pairing. -/
private theorem traceRightMap_surjective :
    Function.Surjective (traceRightMap (K := K) (n := n)) :=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    Subspace.dual_finrank_eq.symm).mp traceRightMap_injective

end Duality

/-- The crux: a matrix strictly lowering the kernel flag of a nilpotent `P`
is a commutator with `P`. -/
theorem exists_commutator_of_lowering
    (P : Matrix (Fin n) (Fin n) K) (hP : P ^ n = 0)
    (Q : Matrix (Fin n) (Fin n) K)
    (hQ : ∀ k, ∀ v ∈ kerFlag P (k + 1), Q.mulVec v ∈ kerFlag P k) :
    ∃ A, P * A - A * P = Q := by
  by_contra hcon
  have hQW : Q ∉ LinearMap.range (adMap P) := by
    rintro ⟨A, hA⟩
    exact hcon ⟨A, hA⟩
  obtain ⟨f, hfQ, hfW⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hQW inferInstance
  obtain ⟨Y, rfl⟩ := traceRightMap_surjective f
  -- separating `Q` from `im ad_P` forces `Y` into the centralizer of `P`
  have hzero : ∀ A, trace ((P * A - A * P) * Y) = 0 := by
    intro A
    have hmem : traceRightMap Y (P * A - A * P) ∈
        (LinearMap.range (adMap P)).map (traceRightMap Y) :=
      Submodule.mem_map_of_mem ⟨A, rfl⟩
    rw [hfW, Submodule.mem_bot] at hmem
    simpa using hmem
  have hcomm : P * Y = Y * P := by
    have h0 : Y * P - P * Y = 0 := by
      refine Matrix.ext_iff_trace_mul_left.mpr fun X => ?_
      rw [← trace_ad_mul, hzero X, mul_zero, trace_zero]
    exact (sub_eq_zero.mp h0).symm
  -- a centralizing `Y` preserves the kernel flag …
  have hYflag : ∀ k, ∀ v ∈ kerFlag P k, Y.mulVec v ∈ kerFlag P k := by
    intro k v hv
    rw [mem_kerFlag] at hv ⊢
    rw [mulVec_mulVec, (Commute.pow_left hcomm k), ← mulVec_mulVec, hv, mulVec_zero]
  -- … so `Q · Y` lowers it, and its trace vanishes: contradiction.
  exact hfQ (by
    simpa using trace_eq_zero_of_lowering P hP (Q * Y)
      (lowering_mul_preserving hQ hYflag))

/-- Over a field the D-conditions characterize the image of `ad_P`. -/
theorem commutator_iff_dcond
    (P : Matrix (Fin n) (Fin n) K) (hP : P ^ n = 0)
    (Q : Matrix (Fin n) (Fin n) K) :
    (∃ A, P * A - A * P = Q) ↔ DCond P Q := by
  constructor
  · rintro ⟨A, rfl⟩
    exact dcond_of_commutator P A
  · intro hD
    obtain ⟨g, hg⟩ := exists_regular_g P Q hP hD
    -- subtracting the regular part kills every flag motion …
    have hvanish : ∀ k, ∀ v ∈ kerFlag P k,
        (dpow P (Q - (P * g - g * P)) k).mulVec v = 0 := by
      intro k v hv
      rw [dpow_sub, dpow_commutator, sub_mulVec, sub_mulVec, ← mulVec_mulVec,
        ← mulVec_mulVec, hg k v hv, mem_kerFlag.mp hv, mulVec_zero, sub_zero, sub_self]
    -- … leaving a lowering direction, which is a commutator
    obtain ⟨A₀, hA₀⟩ := exists_commutator_of_lowering P hP _
      (lowering_of_dpow_vanishing hvanish)
    refine ⟨A₀ + g, ?_⟩
    have hexp : P * (A₀ + g) - (A₀ + g) * P
        = (P * A₀ - A₀ * P) + (P * g - g * P) := by
      rw [mul_add, add_mul]; abel
    rw [hexp, hA₀]
    abel

end Isotropy
