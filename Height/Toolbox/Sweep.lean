import Height.Toolbox.Jordan
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# The centralizer sweep lemma (`lem:sweep`)

The main result identifies the values of the centralizer on an extension
vector, modulo `range(y)`, by a direct telescoping rank-one construction.

`lem:sweep`: for `v ∈ K_c(y) \ K_{c-1}(y)`, `𝔷(y) v + im y = K_c(y)`.
The paper gives this telescoping proof too.
-/

namespace Height.Toolbox

universe u v

variable {K : Type u} [Field K]
variable {W : Type v} [AddCommGroup W] [Module K W]

/-- The span of the values `A v` as `A` ranges over the centralizer of `y`. -/
def centralizerOrbitSpan (y : Module.End K W) (v : W) : Submodule K W :=
  Submodule.span K {w | ∃ A : Module.End K W, Commute A y ∧ A v = w}

/-- The left-hand side `z(y)v + im(y)` of `lem:sweep`, interpreted as a
subspace. -/
def sweepSpace (y : Module.End K W) (v : W) : Submodule K W :=
  centralizerOrbitSpan y v ⊔ LinearMap.range y

/-- The values of the centralizer on one vector already form a subspace, so
taking their span introduces no new elements. -/
theorem mem_centralizerOrbitSpan_iff (y : Module.End K W) (v w : W) :
    w ∈ centralizerOrbitSpan y v ↔
      ∃ A : Module.End K W, Commute A y ∧ A v = w := by
  constructor
  · rw [centralizerOrbitSpan]
    intro hw
    induction hw using Submodule.span_induction with
    | mem w hw => exact hw
    | zero => exact ⟨0, Commute.zero_left y, by simp⟩
    | add a b _ _ ha hb =>
        obtain ⟨A, hA, rfl⟩ := ha
        obtain ⟨B, hB, rfl⟩ := hb
        exact ⟨A + B, hA.add_left hB, by simp⟩
    | smul a w _ hw =>
        obtain ⟨A, hA, rfl⟩ := hw
        exact ⟨a • A, hA.smul_left a, by simp⟩
  · intro hw
    rw [centralizerOrbitSpan]
    exact Submodule.subset_span hw

/-- Membership in the sweep space is exactly an affine centralizer equation. -/
theorem mem_sweepSpace_iff (y : Module.End K W) (v w : W) :
    w ∈ sweepSpace y v ↔
      ∃ (A : Module.End K W) (z : W),
        Commute A y ∧ w = A v + y z := by
  constructor
  · intro hw
    rw [sweepSpace, Submodule.mem_sup] at hw
    obtain ⟨a, ha, b, hb, hab⟩ := hw
    obtain ⟨A, hA, hAv⟩ := (mem_centralizerOrbitSpan_iff y v a).mp ha
    obtain ⟨z, rfl⟩ := hb
    exact ⟨A, z, hA, by simpa [hAv] using hab.symm⟩
  · rintro ⟨A, z, hA, rfl⟩
    rw [sweepSpace, Submodule.mem_sup]
    exact ⟨A v, (mem_centralizerOrbitSpan_iff y v (A v)).mpr ⟨A, hA, rfl⟩,
      y z, LinearMap.mem_range_self y z, rfl⟩

/-- A sign convention for `mem_sweepSpace_iff` matching the correction term
used in the chain-stratum argument. -/
theorem mem_sweepSpace_iff_sub (y : Module.End K W) (v w : W) :
    w ∈ sweepSpace y v ↔
      ∃ (A : Module.End K W) (z : W),
        Commute A y ∧ w = A v - y z := by
  rw [mem_sweepSpace_iff]
  constructor
  · rintro ⟨A, z, hA, hw⟩
    exact ⟨A, -z, hA, by simpa [sub_eq_add_neg] using hw⟩
  · rintro ⟨A, z, hA, hw⟩
    exact ⟨A, -z, hA, by simpa [sub_eq_add_neg] using hw⟩

/-- Every member of the centralizer preserves every kernel-range
subspace. -/
theorem map_mem_kernelRange_of_commute (y A : Module.End K W) (v : W)
    (m : ℕ) (hA : Commute A y) (hv : v ∈ kernelRange y m) :
    A v ∈ kernelRange y m := by
  rw [kernelRange, Submodule.mem_sup] at hv ⊢
  obtain ⟨a, ⟨w, rfl⟩, b, hb, rfl⟩ := hv
  refine ⟨y (A w), LinearMap.mem_range_self y (A w), A b, ?_, ?_⟩
  · rw [LinearMap.mem_ker] at hb ⊢
    rw [← Module.End.mul_apply, ← (hA.pow_right (m - 1)).eq,
      Module.End.mul_apply, hb, map_zero]
  · rw [map_add]
    congr 1
    exact (LinearMap.congr_fun hA.eq w).symm

/-- The centralizer orbit of a vector in `K_m(y)` stays in `K_m(y)`. -/
theorem centralizerOrbitSpan_le_kernelRange (y : Module.End K W) (v : W)
    (m : ℕ) (hv : v ∈ kernelRange y m) :
    centralizerOrbitSpan y v ≤ kernelRange y m := by
  rw [centralizerOrbitSpan, Submodule.span_le]
  rintro w ⟨A, hA, rfl⟩
  exact map_mem_kernelRange_of_commute y A v m hA hv

/-- The easy inclusion in `lem:sweep`. -/
theorem sweepSpace_le_kernelRange (y : Module.End K W) (v : W)
    (m : ℕ) (hv : v ∈ kernelRange y m) :
    sweepSpace y v ≤ kernelRange y m := by
  rw [sweepSpace, sup_le_iff]
  constructor
  · exact centralizerOrbitSpan_le_kernelRange y v m hv
  · rw [kernelRange]
    exact le_sup_left

/-- `lem:sweep` in the first-column case, where `K₁(y) = im(y)`. -/
theorem sweep_first_column (y : Module.End K W) (v : W)
    [FiniteDimensional K W]
    (hv : v ∈ kernelRange y 1) :
    sweepSpace y v = kernelRange y 1 := by
  apply le_antisymm (sweepSpace_le_kernelRange y v 1 hv)
  rw [kernelRange_one, sweepSpace]
  exact le_sup_right

/-- The telescoping rank-one endomorphism used in the general sweep
construction.  Its `m`th stage sends `x` to
`∑ j < m, f (y^(m-1-j) x) • y^j w`. -/
private def rankOneSweepEndomorphism (y : Module.End K W)
    (f : W →ₗ[K] K) (w : W) : ℕ → Module.End K W
  | 0 => 0
  | m + 1 =>
      (f.comp (y ^ m)).smulRight w +
        y.comp (rankOneSweepEndomorphism y f w m)

@[simp] private theorem rankOneSweepEndomorphism_zero_apply
    (y : Module.End K W) (f : W →ₗ[K] K) (w x : W) :
    rankOneSweepEndomorphism y f w 0 x = 0 :=
  rfl

@[simp] private theorem rankOneSweepEndomorphism_succ_apply
    (y : Module.End K W) (f : W →ₗ[K] K) (w x : W) (m : ℕ) :
    rankOneSweepEndomorphism y f w (m + 1) x =
      f ((y ^ m) x) • w + y (rankOneSweepEndomorphism y f w m x) :=
  rfl

/-- Telescoping identity for the rank-one sweep endomorphism. -/
private theorem rankOneSweepEndomorphism_commutator_apply
    (y : Module.End K W) (f : W →ₗ[K] K) (w x : W) (m : ℕ) :
    rankOneSweepEndomorphism y f w m (y x) -
        y (rankOneSweepEndomorphism y f w m x) =
      f ((y ^ m) x) • w - f x • (y ^ m) w := by
  induction m with
  | zero => simp [rankOneSweepEndomorphism_zero_apply]
  | succ m ih =>
      rw [rankOneSweepEndomorphism_succ_apply,
        rankOneSweepEndomorphism_succ_apply, map_add, map_smul]
      have hpow (a : W) : (y ^ m) (y a) = (y ^ (m + 1)) a := by
        rw [← Module.End.mul_apply, pow_succ]
      rw [hpow]
      have hih := congrArg y ih
      simp only [map_sub, map_smul] at hih
      have hpoww : y ((y ^ m) w) = (y ^ (m + 1)) w := by
        rw [← Module.End.mul_apply, ← pow_succ']
      calc
        f ((y ^ (m + 1)) x) • w +
              y (rankOneSweepEndomorphism y f w m (y x)) -
            (f ((y ^ m) x) • y w +
              y (y (rankOneSweepEndomorphism y f w m x))) =
            f ((y ^ (m + 1)) x) • w +
              (y (rankOneSweepEndomorphism y f w m (y x)) -
                y (y (rankOneSweepEndomorphism y f w m x))) -
              f ((y ^ m) x) • y w := by abel
        _ = f ((y ^ (m + 1)) x) • w +
              (f ((y ^ m) x) • y w -
                f x • y ((y ^ m) w)) -
              f ((y ^ m) x) • y w := by rw [hih]
        _ = f ((y ^ (m + 1)) x) • w -
              f x • (y ^ (m + 1)) w := by rw [hpoww]; abel

/-- If `f` kills `range(y^m)` and `y^m w = 0`, the telescoping
endomorphism centralizes `y`. -/
private theorem rankOneSweepEndomorphism_commute
    (y : Module.End K W) (f : W →ₗ[K] K) (w : W) (m : ℕ)
    (hf : ∀ x, f ((y ^ m) x) = 0) (hw : (y ^ m) w = 0) :
    Commute (rankOneSweepEndomorphism y f w m) y := by
  apply LinearMap.ext
  intro x
  apply sub_eq_zero.mp
  change rankOneSweepEndomorphism y f w m (y x) -
    y (rankOneSweepEndomorphism y f w m x) = 0
  rw [rankOneSweepEndomorphism_commutator_apply, hf, hw]
  simp

/-- At a cyclic vector detected by `f`, the telescoping endomorphism
takes the prescribed value modulo `range(y)`. -/
private theorem rankOneSweepEndomorphism_apply_eq_add_range
    (y : Module.End K W) (f : W →ₗ[K] K) (v w : W) (m : ℕ)
    (hm : 1 ≤ m) (hfv : f ((y ^ (m - 1)) v) = 1) :
    ∃ z, rankOneSweepEndomorphism y f w m v = w + y z := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  refine ⟨rankOneSweepEndomorphism y f w r v, ?_⟩
  have hfv' : f ((y ^ r) v) = 1 := by simpa using hfv
  simp only [rankOneSweepEndomorphism_succ_apply, hfv', one_smul]

/-- The general centralizer sweep lemma, proved directly by a telescoping
rank-one construction.  The source's convention `K₀(y) = ∅` is encoded by
`kernelRangeSet`, so the statement also includes the first-column case. -/
theorem sweep (y : Module.End K W) (v : W) (c : ℕ)
    [FiniteDimensional K W]
    (hc : 1 ≤ c) (hvc : v ∈ kernelRange y c)
    (hvprev : v ∉ kernelRangeSet y (c - 1)) :
    sweepSpace y v = kernelRange y c := by
  by_cases hc1 : c = 1
  · subst c
    exact sweep_first_column y v hvc
  · have hc2 : 2 ≤ c := by omega
    apply le_antisymm (sweepSpace_le_kernelRange y v c hvc)
    have hprev : v ∉ kernelRange y (c - 1) := by
      have hcpred : ∃ r, c - 1 = r + 1 := by
        exact ⟨c - 2, by omega⟩
      obtain ⟨r, hr⟩ := hcpred
      simpa [kernelRangeSet, hr] using hvprev
    rw [kernelRange, Submodule.mem_sup] at hvc
    obtain ⟨_, ⟨u, rfl⟩, k, hk, rfl⟩ := hvc
    have hkprev : k ∉ kernelRange y (c - 1) := by
      intro hkprev
      apply hprev
      exact (kernelRange y (c - 1)).add_mem
        (by
          rw [kernelRange]
          exact (show LinearMap.range y ≤
            LinearMap.range y ⊔ LinearMap.ker (y ^ (c - 1 - 1)) from
              le_sup_left) (LinearMap.mem_range_self y u))
        hkprev
    have hsep : (y ^ (c - 2)) k ∉ LinearMap.range (y ^ (c - 1)) := by
      intro hmem
      apply hkprev
      apply (pow_pred_mem_range_pow_iff_mem_kernelRange
        y k (c - 1) (by omega)).mp
      simpa only [show c - 1 - 1 = c - 2 by omega] using hmem
    obtain ⟨f, hf, hfk⟩ := LinearMap.exists_extend_of_notMem
      (0 : LinearMap.range (y ^ (c - 1)) →ₗ[K] K) hsep 1
    have hf_range (a : W) : f ((y ^ (c - 1)) a) = 0 := by
      have h := LinearMap.congr_fun hf
        ⟨(y ^ (c - 1)) a, LinearMap.mem_range_self (y ^ (c - 1)) a⟩
      simpa using h
    intro w hw
    rw [kernelRange, Submodule.mem_sup] at hw
    obtain ⟨_, ⟨z, rfl⟩, k', hk', rfl⟩ := hw
    let A := rankOneSweepEndomorphism y f k' (c - 1)
    have hA : Commute A y :=
      rankOneSweepEndomorphism_commute y f k' (c - 1) hf_range
        (LinearMap.mem_ker.mp hk')
    obtain ⟨z', hz'⟩ := rankOneSweepEndomorphism_apply_eq_add_range
      y f k k' (c - 1) (by omega)
      (by simpa only [show c - 1 - 1 = c - 2 by omega] using hfk)
    apply (mem_sweepSpace_iff y (y u + k) (y z + k')).mpr
    refine ⟨A, z - z' - A u, hA, ?_⟩
    have hAyu : A (y u) = y (A u) := LinearMap.congr_fun hA.eq u
    change A k = k' + y z' at hz'
    rw [map_add, hAyu, hz', map_sub]
    rw [map_sub]
    abel

/-- The sweep equality at the intrinsically defined column in which adjoining
`v` adds its box. -/
theorem sweep_at_boxColumn (y : Module.End K W) (v : W)
    [FiniteDimensional K W] (hy : IsNilpotent y) :
    sweepSpace y v = kernelRange y (boxColumn y v hy) := by
  let c := boxColumn y v hy
  have hc := boxColumn_spec y v hy
  apply sweep y v c hc.1 hc.2
  intro hvprev
  by_cases hc1 : c = 1
  · have hzero : c - 1 = 0 := by omega
    rw [hzero] at hvprev
    simp [kernelRangeSet] at hvprev
  · have hc2 : 2 ≤ c := by omega
    have hmem : v ∈ kernelRange y (c - 1) := by
      obtain ⟨r, hr⟩ : ∃ r, c - 1 = r + 1 := ⟨c - 2, by omega⟩
      simpa [kernelRangeSet, hr] using hvprev
    have hmin := boxColumn_min y v hy (m := c - 1) (by omega) hmem
    change c ≤ c - 1 at hmin
    omega

end Height.Toolbox
