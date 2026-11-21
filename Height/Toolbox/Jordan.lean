import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Rank
import Height.Toolbox.FinrankSplit
import Height.Toolbox.Majorization

/-!
# Kernel dimensions and adjoining one vector (`lem:box-column`)

This file fixes the kernel-dimension model of nilpotent Jordan type used in
`lem:box-column` of the paper.
-/

namespace Height.Toolbox

universe u v

variable {K : Type u} [Field K]
variable {W : Type v} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- The `m`th part of the conjugate Jordan partition, defined by successive
kernel dimensions.  For the intended applications the endomorphism is
nilpotent and `m ≥ 1`. -/
noncomputable def conj (y : Module.End K W) (m : ℕ) : ℕ :=
  Module.finrank K (LinearMap.ker (y ^ m)) -
    Module.finrank K (LinearMap.ker (y ^ (m - 1)))

/-- For `m ≥ 1`, the subspace `K_m(y) = range y + ker y^(m-1)`. -/
def kernelRange (y : Module.End K W) (m : ℕ) : Submodule K W :=
  LinearMap.range y ⊔ LinearMap.ker (y ^ (m - 1))

omit [FiniteDimensional K W] in
/-- The kernel-range spaces form an increasing sequence. -/
theorem kernelRange_mono (y : Module.End K W) {m r : ℕ} (hmr : m ≤ r) :
    kernelRange y m ≤ kernelRange y r := by
  rw [kernelRange, kernelRange]
  apply sup_le_sup le_rfl
  exact (LinearMap.iterateKer y).monotone (Nat.sub_le_sub_right hmr 1)

omit [FiniteDimensional K W] in
@[simp] theorem kernelRange_one (y : Module.End K W) :
    kernelRange y 1 = LinearMap.range y := by
  rw [kernelRange]
  simp only [Nat.reduceSubDiff]
  rw [pow_zero, Module.End.one_eq_id, LinearMap.ker_id, sup_bot_eq]

omit [FiniteDimensional K W] in
/-- The membership calculation at the heart of `lem:box-column`. -/
theorem pow_pred_mem_range_pow_iff_mem_kernelRange
    (y : Module.End K W) (v : W) (m : ℕ) (hm : 1 ≤ m) :
    (y ^ (m - 1)) v ∈ LinearMap.range (y ^ m) ↔ v ∈ kernelRange y m := by
  have hpow : y ^ (m - 1) * y = y ^ m := by
    rw [← pow_succ]
    congr
    omega
  constructor
  · rintro ⟨w, hw⟩
    change v ∈ LinearMap.range y ⊔ LinearMap.ker (y ^ (m - 1))
    rw [Submodule.mem_sup]
    refine ⟨y w, LinearMap.mem_range_self y w, v - y w, ?_, by abel⟩
    rw [LinearMap.mem_ker, map_sub, ← Module.End.mul_apply, hpow, hw, sub_self]
  · change v ∈ LinearMap.range y ⊔ LinearMap.ker (y ^ (m - 1)) → _
    rw [Submodule.mem_sup]
    rintro ⟨a, ⟨w, rfl⟩, b, hb, rfl⟩
    refine ⟨w, ?_⟩
    rw [map_add, ← Module.End.mul_apply, hpow, LinearMap.mem_ker.mp hb, add_zero]

omit [FiniteDimensional K W] in
private theorem range_inf_ker_pow_eq_map_ker_pow
    (y : Module.End K W) (m : ℕ) (hm : 1 ≤ m) :
    LinearMap.range y ⊓ LinearMap.ker (y ^ (m - 1)) =
      (LinearMap.ker (y ^ m)).map y := by
  have hpow : y ^ (m - 1) * y = y ^ m := by
    rw [← pow_succ]
    congr
    omega
  ext z
  constructor
  · rintro ⟨⟨w, rfl⟩, hw⟩
    refine ⟨w, ?_, rfl⟩
    show (y ^ m) w = 0
    rw [← hpow, Module.End.mul_apply]
    exact LinearMap.mem_ker.mp hw
  · rintro ⟨w, hw, rfl⟩
    refine ⟨LinearMap.mem_range_self y w, ?_⟩
    show (y ^ (m - 1)) (y w) = 0
    rw [← Module.End.mul_apply, hpow]
    exact LinearMap.mem_ker.mp hw

private theorem finrank_range_inf_ker_pow
    (y : Module.End K W) (m : ℕ) (hm : 1 ≤ m) :
    Module.finrank K ↥(LinearMap.range y ⊓ LinearMap.ker (y ^ (m - 1))) +
        Module.finrank K (LinearMap.ker y) =
      Module.finrank K (LinearMap.ker (y ^ m)) := by
  let p := LinearMap.ker (y ^ m)
  let f := y.domRestrict p
  have hpow : y ^ (m - 1) * y = y ^ m := by
    rw [← pow_succ]
    congr
    omega
  have hle : LinearMap.ker y ≤ p := by
    intro w hw
    change w ∈ LinearMap.ker (y ^ m)
    rw [LinearMap.mem_ker, ← hpow, Module.End.mul_apply,
      LinearMap.mem_ker.mp hw, map_zero]
  have hker : LinearMap.ker f = (LinearMap.ker y).comap p.subtype := by
    exact LinearMap.ker_domRestrict p y
  have hkerFin : Module.finrank K (LinearMap.ker f) =
      Module.finrank K (LinearMap.ker y) := by
    rw [hker]
    exact (Submodule.comapSubtypeEquivOfLe hle).finrank_eq
  have hrank := LinearMap.finrank_range_add_finrank_ker f
  rw [LinearMap.range_domRestrict, hkerFin] at hrank
  rw [range_inf_ker_pow_eq_map_ker_pow y m hm]
  exact hrank

/-- The dimension formula in `lem:box-column`:
`dim K_m(y) = dim W - conj_m(y)`. -/
theorem finrank_kernelRange (y : Module.End K W) (m : ℕ) (hm : 1 ≤ m) :
    Module.finrank K (kernelRange y m) = Module.finrank K W - conj y m := by
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.range y) (LinearMap.ker (y ^ (m - 1)))
  have hinter := finrank_range_inf_ker_pow y m hm
  have hry := LinearMap.finrank_range_add_finrank_ker y
  have hpred_le : LinearMap.ker (y ^ (m - 1)) ≤ LinearMap.ker (y ^ m) := by
    intro w hw
    have hpow : y * y ^ (m - 1) = y ^ m := by
      rw [← pow_succ']
      congr
      omega
    rw [LinearMap.mem_ker, ← hpow, Module.End.mul_apply, LinearMap.mem_ker.mp hw,
      map_zero]
  have hfin_le : Module.finrank K (LinearMap.ker (y ^ (m - 1))) ≤
      Module.finrank K (LinearMap.ker (y ^ m)) := Submodule.finrank_mono hpred_le
  change Module.finrank K
      ↥(LinearMap.range y ⊔ LinearMap.ker (y ^ (m - 1))) = _
  unfold conj
  omega

/-- The endomorphism of `W × K` obtained by adjoining a vector `v` as the
last column: `(w,t) ↦ (y w + t • v, 0)`. -/
def extendByVector (y : Module.End K W) (v : W) : Module.End K (W × K) where
  toFun z := (y z.1 + z.2 • v, 0)
  map_add' z z' := by
    ext <;> simp [add_smul, add_assoc, add_left_comm, add_comm]
  map_smul' a z := by
    ext <;> simp [mul_smul]

omit [FiniteDimensional K W] in
@[simp] theorem extendByVector_apply (y : Module.End K W) (v w : W) (t : K) :
    extendByVector y v (w, t) = (y w + t • v, 0) := rfl

omit [FiniteDimensional K W] in
/-- Block-power computation used in `lem:box-column`. -/
theorem extendByVector_pow_succ_apply (y : Module.End K W) (v w : W)
    (t : K) (m : ℕ) :
    ((extendByVector y v) ^ (m + 1)) (w, t) =
      ((y ^ (m + 1)) w + t • (y ^ m) v, 0) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ', Module.End.mul_apply, ih]
      simp only [extendByVector_apply, map_add, map_smul, zero_smul, add_zero]
      have hy (k : ℕ) (z : W) : y ((y ^ k) z) = (y ^ (k + 1)) z := by
        rw [← Module.End.mul_apply, ← pow_succ']
      rw [hy (m + 1) w, hy m v]

/-- Whether adjoining `v` increases the kernel dimension at level `m+1`. -/
noncomputable def kernelJump (y : Module.End K W) (v : W) (m : ℕ) : ℕ :=
  by
    classical
    exact if (y ^ m) v ∈ LinearMap.range (y ^ (m + 1)) then 1 else 0

/-- Adjoining one vector changes each kernel dimension by zero or one. -/
theorem finrank_ker_extendByVector_pow_succ (y : Module.End K W) (v : W) (m : ℕ) :
    Module.finrank K (LinearMap.ker ((extendByVector y v) ^ (m + 1))) =
      Module.finrank K (LinearMap.ker (y ^ (m + 1))) +
        kernelJump y v m := by
  classical
  let x := extendByVector y v
  let p := LinearMap.ker (x ^ (m + 1))
  let proj := (LinearMap.snd K W K).domRestrict p
  let e : LinearMap.ker (y ^ (m + 1)) →ₗ[K] LinearMap.ker proj := {
    toFun w :=
      ⟨⟨(w.1, 0), by
          show (x ^ (m + 1)) (w.1, 0) = 0
          rw [show x = extendByVector y v by rfl, extendByVector_pow_succ_apply]
          simp [LinearMap.mem_ker.mp w.2]⟩,
        by rfl⟩
    map_add' w w' := by
      apply Subtype.ext
      apply Subtype.ext
      ext <;> simp
    map_smul' a w := by
      apply Subtype.ext
      apply Subtype.ext
      ext <;> simp }
  have he_inj : Function.Injective e := by
    intro w w' h
    apply Subtype.ext
    exact congrArg (fun z => z.1.1.1) h
  have he_surj : Function.Surjective e := by
    intro z
    have ht : z.1.1.2 = 0 := by
      have hz := LinearMap.mem_ker.mp z.2
      exact hz
    have hx := LinearMap.mem_ker.mp z.1.2
    have hw : (y ^ (m + 1)) z.1.1.1 = 0 := by
      rw [show x = extendByVector y v by rfl, extendByVector_pow_succ_apply] at hx
      simpa [ht] using congrArg Prod.fst hx
    refine ⟨⟨z.1.1.1, hw⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext rfl ht.symm
  have hkerFin : Module.finrank K (LinearMap.ker proj) =
      Module.finrank K (LinearMap.ker (y ^ (m + 1))) :=
    (LinearEquiv.ofBijective e ⟨he_inj, he_surj⟩).finrank_eq.symm
  have hrangeFin : Module.finrank K (LinearMap.range proj) =
      kernelJump y v m := by
    by_cases hv : (y ^ m) v ∈ LinearMap.range (y ^ (m + 1))
    · have hv_mem := hv
      obtain ⟨w, hw⟩ := hv
      have hsurj : Function.Surjective proj := by
        intro t
        let z : W × K := (-t • w, t)
        have hz : z ∈ p := by
          change (x ^ (m + 1)) z = 0
          rw [show x = extendByVector y v by rfl, show z = (-t • w, t) by rfl,
            extendByVector_pow_succ_apply]
          simp only [map_smul]
          rw [hw]
          simp
        exact ⟨⟨z, hz⟩, rfl⟩
      rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self]
      simp [kernelJump, hv_mem]
    · have hzero : proj = 0 := by
        ext z
        by_contra ht
        have ht' : z.1.2 ≠ 0 := by simpa [proj] using ht
        have hx := LinearMap.mem_ker.mp z.2
        have hzpow :
            (y ^ (m + 1)) z.1.1 + z.1.2 • (y ^ m) v = 0 := by
          rw [show x = extendByVector y v by rfl, extendByVector_pow_succ_apply] at hx
          exact congrArg Prod.fst hx
        apply hv
        refine ⟨(-z.1.2⁻¹) • z.1.1, ?_⟩
        have ha : (y ^ (m + 1)) z.1.1 = -(z.1.2 • (y ^ m) v) := by
          exact eq_neg_of_add_eq_zero_left hzpow
        rw [map_smul, ha]
        simp [ht']
      rw [hzero, LinearMap.range_zero, finrank_bot]
      simp [kernelJump, hv]
  have hrank := LinearMap.finrank_range_add_finrank_ker proj
  rw [hkerFin, hrangeFin] at hrank
  change Module.finrank K p = _
  omega

/-- The extra kernel dimension at the actual power `m`, with the convention
`δ₀ = 0` from `lem:box-column`. -/
noncomputable def boxDelta (y : Module.End K W) (v : W) : ℕ → ℕ
  | 0 => 0
  | m + 1 => kernelJump y v m

/-- The source's set-valued convention `K₀(y) = ∅`, followed by
`K_m(y) = range y ⊔ ker y^(m-1)` for `m ≥ 1`. -/
def kernelRangeSet (y : Module.End K W) : ℕ → Set W
  | 0 => ∅
  | m + 1 => kernelRange y (m + 1)

/-- The indicator of membership in the source's set-valued `K_m(y)`. -/
noncomputable def boxIndicator (y : Module.End K W) (v : W) (m : ℕ) : ℕ := by
  classical
  exact if v ∈ kernelRangeSet y m then 1 else 0

omit [FiniteDimensional K W] in
/-- The block calculation identifies `δ_m` with membership in `K_m(y)`. -/
theorem boxDelta_eq_indicator (y : Module.End K W) (v : W) (m : ℕ) :
    boxDelta y v m = boxIndicator y v m := by
  classical
  cases m with
  | zero => simp [boxDelta, boxIndicator, kernelRangeSet]
  | succ m =>
      rw [show boxDelta y v (m + 1) = kernelJump y v m by rfl]
      simp only [kernelJump, boxIndicator]
      rw [show kernelRangeSet y (m + 1) = kernelRange y (m + 1) by rfl]
      have hiff := pow_pred_mem_range_pow_iff_mem_kernelRange
        y v (m + 1) (by omega)
      have hpred : m + 1 - 1 = m := by omega
      rw [hpred] at hiff
      rw [hiff]
      rfl

/-- Kernel dimensions for the extension, including power zero. -/
theorem finrank_ker_extendByVector_pow (y : Module.End K W) (v : W) (m : ℕ) :
    Module.finrank K (LinearMap.ker ((extendByVector y v) ^ m)) =
      Module.finrank K (LinearMap.ker (y ^ m)) + boxDelta y v m := by
  cases m with
  | zero =>
      have hx : LinearMap.ker ((extendByVector y v) ^ 0) = ⊥ := by
        rw [pow_zero]
        ext z
        simp only [LinearMap.mem_ker, Submodule.mem_bot]
        change z = 0 ↔ z = 0
        rfl
      have hy : LinearMap.ker (y ^ 0) = ⊥ := by
        rw [pow_zero]
        ext z
        simp only [LinearMap.mem_ker, Submodule.mem_bot]
        change z = 0 ↔ z = 0
        rfl
      rw [hx, hy, finrank_bot, finrank_bot]
      rfl
  | succ m => exact finrank_ker_extendByVector_pow_succ y v m

omit [FiniteDimensional K W] in
/-- The indicators `δ_m` are nondecreasing. -/
theorem boxDelta_le_succ (y : Module.End K W) (v : W) (m : ℕ) :
    boxDelta y v m ≤ boxDelta y v (m + 1) := by
  classical
  cases m with
  | zero => simp [boxDelta, kernelJump]
  | succ m =>
      simp only [boxDelta, kernelJump]
      by_cases h : (y ^ m) v ∈ LinearMap.range (y ^ (m + 1))
      · have hmem := h
        obtain ⟨w, hw⟩ := hmem
        have hnext : (y ^ (m + 1)) v ∈ LinearMap.range (y ^ (m + 2)) := by
          refine ⟨w, ?_⟩
          have hleft : y * y ^ (m + 1) = y ^ (m + 2) := by rw [← pow_succ']
          have hright : y * y ^ m = y ^ (m + 1) := by rw [← pow_succ']
          calc
            (y ^ (m + 2)) w = y ((y ^ (m + 1)) w) := by
              rw [← hleft, Module.End.mul_apply]
            _ = y ((y ^ m) v) := by rw [hw]
            _ = (y ^ (m + 1)) v := by rw [← hright, Module.End.mul_apply]
        rw [ite_eq_left h, ite_eq_left hnext]
      · simp [h]

omit [FiniteDimensional K W] in
/-- Monotonicity of the kernel indicators over an arbitrary interval. -/
theorem boxDelta_mono (y : Module.End K W) (v : W) {m r : ℕ} (h : m ≤ r) :
    boxDelta y v m ≤ boxDelta y v r := by
  induction r, h using Nat.le_induction with
  | base => exact le_rfl
  | succ r _ ih => exact ih.trans (boxDelta_le_succ y v r)

omit [FiniteDimensional K W] in
theorem boxDelta_le_one (y : Module.End K W) (v : W) (m : ℕ) :
    boxDelta y v m ≤ 1 := by
  cases m with
  | zero => simp [boxDelta]
  | succ m =>
      simp only [boxDelta, kernelJump]
      split <;> omega

omit [FiniteDimensional K W] in
private theorem boxColumn_exists (y : Module.End K W) (v : W)
    (hy : IsNilpotent y) : ∃ m : ℕ, 1 ≤ m ∧ v ∈ kernelRange y m := by
  obtain ⟨r, hr⟩ := hy
  refine ⟨r + 1, by omega, ?_⟩
  rw [kernelRange]
  have hpred : r + 1 - 1 = r := by omega
  rw [hpred, hr]
  simp

/-- The first column in which `v` belongs to `K_m(y)`.  Nilpotence makes
the defining set nonempty. -/
noncomputable def boxColumn (y : Module.End K W) (v : W) (hy : IsNilpotent y) : ℕ :=
  by
    classical
    exact Nat.find (boxColumn_exists y v hy)

omit [FiniteDimensional K W] in
theorem boxColumn_spec (y : Module.End K W) (v : W) (hy : IsNilpotent y) :
    1 ≤ boxColumn y v hy ∧ v ∈ kernelRange y (boxColumn y v hy) :=
  by
    classical
    exact Nat.find_spec (boxColumn_exists y v hy)

omit [FiniteDimensional K W] in
theorem boxColumn_min (y : Module.End K W) (v : W) (hy : IsNilpotent y)
    {m : ℕ} (hm : 1 ≤ m) (hmem : v ∈ kernelRange y m) :
    boxColumn y v hy ≤ m := by
  classical
  exact Nat.find_min' (boxColumn_exists y v hy) ⟨hm, hmem⟩

omit [FiniteDimensional K W] in
/-- A displayed nilpotency exponent bounds the column in which the new box
appears. -/
theorem boxColumn_le_nilpotency_succ (y : Module.End K W) (v : W)
    (r : ℕ) (hy : y ^ r = 0) :
    boxColumn y v ⟨r, hy⟩ ≤ r + 1 := by
  apply boxColumn_min y v ⟨r, hy⟩ (by omega)
  rw [kernelRange]
  have hpred : r + 1 - 1 = r := by omega
  rw [hpred, hy]
  simp

omit [FiniteDimensional K W] in
/-- The kernel indicator is the step function beginning at `boxColumn`. -/
theorem boxDelta_eq_one_iff_boxColumn_le (y : Module.End K W) (v : W)
    (hy : IsNilpotent y) (m : ℕ) :
    boxDelta y v m = 1 ↔ boxColumn y v hy ≤ m := by
  constructor
  · intro hδ
    cases m with
    | zero => simp [boxDelta] at hδ
    | succ m =>
        apply boxColumn_min y v hy (by omega)
        have hi := boxDelta_eq_indicator y v (m + 1)
        rw [hδ] at hi
        unfold boxIndicator at hi
        rw [show kernelRangeSet y (m + 1) = kernelRange y (m + 1) by rfl] at hi
        split at hi
        · assumption
        · contradiction
  · intro hcm
    have hcδ : boxDelta y v (boxColumn y v hy) = 1 := by
      have hc := boxColumn_spec y v hy
      obtain ⟨c, hcpos⟩ : ∃ c, boxColumn y v hy = c + 1 := by
        exact ⟨boxColumn y v hy - 1, by omega⟩
      rw [hcpos] at hc ⊢
      rw [boxDelta_eq_indicator]
      unfold boxIndicator
      rw [show kernelRangeSet y (c + 1) = kernelRange y (c + 1) by rfl]
      simp [hc.2]
    have hle := boxDelta_mono y v hcm
    have hone := boxDelta_le_one y v m
    omega

/-! ### Concavity of the kernel dimensions

`c(X) = Σ_m conj(X)_m²` is a sum over a *partition*: the jumps `conj(X)_m` are
nonincreasing in `m`.  That is the statement that `y` induces an injection
`ker y^{m+2} / ker y^{m+1} ↪ ker y^{m+1} / ker y^m`, proved here without
quotients — as the submodule identities `map y A ⊔ C ≤ B` and
`map y A ⊓ C = map y B` for `A ⊇ B ⊇ C` the three kernels. -/

section Concavity

variable (y : Module.End K W)

/-- The kernels of the powers increase. -/
theorem ker_pow_le_ker_pow_succ (m : ℕ) :
    LinearMap.ker (y ^ m) ≤ LinearMap.ker (y ^ (m + 1)) := by
  intro v hv
  simp only [LinearMap.mem_ker] at hv ⊢
  rw [pow_succ', Module.End.mul_apply, hv, map_zero]

theorem ker_pow_mono {m r : ℕ} (h : m ≤ r) :
    LinearMap.ker (y ^ m) ≤ LinearMap.ker (y ^ r) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction d with
  | zero => simp
  | succ d ih =>
    refine le_trans ih ?_
    rw [← Nat.add_assoc]
    exact ker_pow_le_ker_pow_succ y (m + d)

/-- Rank–nullity for `y` restricted to a submodule containing `ker y`:
`Toolbox/FinrankSplit.lean`'s general form with `p ⊓ ker y = ker y`. -/
theorem finrank_map_add_finrank_ker (p : Submodule K W) (hp : LinearMap.ker y ≤ p) :
    Module.finrank K (p.map y) + Module.finrank K (LinearMap.ker y)
      = Module.finrank K p := by
  rw [← inf_eq_right.mpr hp]
  exact finrank_map_add_finrank_inf_ker y p

/-- **Concavity of the kernel dimensions**: the jump from `m+1` to `m+2` is at
most the jump from `m` to `m+1`. -/
theorem finrank_ker_pow_add_le (m : ℕ) :
    Module.finrank K (LinearMap.ker (y ^ (m + 2)))
        + Module.finrank K (LinearMap.ker (y ^ m))
      ≤ 2 * Module.finrank K (LinearMap.ker (y ^ (m + 1))) := by
  have hCB : LinearMap.ker (y ^ m) ≤ LinearMap.ker (y ^ (m + 1)) :=
    ker_pow_mono y (Nat.le_succ m)
  have hBA : LinearMap.ker (y ^ (m + 1)) ≤ LinearMap.ker (y ^ (m + 2)) :=
    ker_pow_mono y (Nat.le_succ (m + 1))
  have hkerB : LinearMap.ker y ≤ LinearMap.ker (y ^ (m + 1)) := by
    have := ker_pow_mono y (m := 1) (r := m + 1) (by omega)
    rwa [pow_one] at this
  have hkerA : LinearMap.ker y ≤ LinearMap.ker (y ^ (m + 2)) := le_trans hkerB hBA
  have hmapA : (LinearMap.ker (y ^ (m + 2))).map y ≤ LinearMap.ker (y ^ (m + 1)) := by
    rintro _ ⟨v, hv, rfl⟩
    simp only [LinearMap.mem_ker] at hv ⊢
    rw [← Module.End.mul_apply, ← pow_succ]
    exact hv
  have hmapB : (LinearMap.ker (y ^ (m + 1))).map y ≤ LinearMap.ker (y ^ m) := by
    rintro _ ⟨v, hv, rfl⟩
    simp only [LinearMap.mem_ker] at hv ⊢
    rw [← Module.End.mul_apply, ← pow_succ]
    exact hv
  have hsup : (LinearMap.ker (y ^ (m + 2))).map y ⊔ LinearMap.ker (y ^ m)
      ≤ LinearMap.ker (y ^ (m + 1)) := sup_le hmapA hCB
  have hinf : (LinearMap.ker (y ^ (m + 2))).map y ⊓ LinearMap.ker (y ^ m)
      = (LinearMap.ker (y ^ (m + 1))).map y := by
    refine le_antisymm ?_ (le_inf (Submodule.map_mono hBA) hmapB)
    rintro w ⟨⟨v, _, rfl⟩, hwC⟩
    refine ⟨v, LinearMap.mem_ker.mpr ?_, rfl⟩
    rw [pow_succ, Module.End.mul_apply]
    exact LinearMap.mem_ker.mp hwC
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq
    ((LinearMap.ker (y ^ (m + 2))).map y) (LinearMap.ker (y ^ m))
  rw [hinf] at h1
  have h2 : Module.finrank K
      (((LinearMap.ker (y ^ (m + 2))).map y ⊔ LinearMap.ker (y ^ m) : Submodule K W))
      ≤ Module.finrank K (LinearMap.ker (y ^ (m + 1))) := Submodule.finrank_mono hsup
  have hrA := finrank_map_add_finrank_ker y (LinearMap.ker (y ^ (m + 2))) hkerA
  have hrB := finrank_map_add_finrank_ker y (LinearMap.ker (y ^ (m + 1))) hkerB
  omega

/-- The parts of the conjugate partition are nonincreasing. -/
theorem conj_succ_le {m : ℕ} (hm : 1 ≤ m) : conj y (m + 1) ≤ conj y m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have h := finrank_ker_pow_add_le y k
  have hmono := Submodule.finrank_mono (ker_pow_le_ker_pow_succ y k)
  have hmono' := Submodule.finrank_mono (ker_pow_le_ker_pow_succ y (k + 1))
  show Module.finrank K (LinearMap.ker (y ^ (k + 2)))
      - Module.finrank K (LinearMap.ker (y ^ (k + 1)))
    ≤ Module.finrank K (LinearMap.ker (y ^ (k + 1)))
      - Module.finrank K (LinearMap.ker (y ^ k))
  omega

end Concavity

/-! ### Monotonicity of the centraliser dimension

`c(X) = Σ_m conj(X)_m²` and the partial sums of `conj(X)` are the kernel
dimensions, so a matrix whose kernels are everywhere at least as big has a
conjugate partition that *majorizes*; the parts being nonincreasing
(`conj_succ_le`), Schur convexity (`Toolbox/Majorization.lean`) turns that into
`c(X) ≤ c(Y)`.  This is the degeneration monotonicity of the centraliser
dimension, in the rank form in which `Pencil.orbitClosure` is stated. -/

section Monotone

variable (y : Module.End K W)

/-- The parts of the conjugate partition are nonincreasing, over any range. -/
theorem conj_antitone {m r : ℕ} (hm : 1 ≤ m) (h : m ≤ r) : conj y r ≤ conj y m := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction d with
  | zero => simp
  | succ d ih =>
    refine le_trans ?_ ih
    rw [← Nat.add_assoc]
    exact conj_succ_le y (by omega)

/-- The partial sums of the conjugate partition are the kernel dimensions. -/
theorem sum_conj_eq_finrank_ker (k : ℕ) :
    ∑ m ∈ Finset.Icc 1 k, conj y m = Module.finrank K (LinearMap.ker (y ^ k)) := by
  induction k with
  | zero =>
    rw [pow_zero, Module.End.one_eq_id, LinearMap.ker_id]
    simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    have hmono := Submodule.finrank_mono (ker_pow_le_ker_pow_succ y k)
    have hc : conj y (k + 1)
        = Module.finrank K (LinearMap.ker (y ^ (k + 1)))
          - Module.finrank K (LinearMap.ker (y ^ k)) := rfl
    rw [hc]
    omega

end Monotone

/-- Reindexing `Icc 1 k` as `range k`. -/
theorem sum_Icc_one_eq_sum_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (k : ℕ) :
    ∑ m ∈ Finset.Icc 1 k, f m = ∑ i ∈ Finset.range k, f (i + 1) := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

/-- **The centraliser dimension is monotone under degeneration**, at the level
of endomorphisms: if every kernel of a power of `x` is contained in — here,
no larger than — the corresponding kernel of `y`, and both are nilpotent of
exponent `N`, then `Σ conj(x)² ≤ Σ conj(y)²`. -/
theorem sum_conj_sq_le_of_finrank_ker_le {N : ℕ} (x y : Module.End K W)
    (hx : LinearMap.ker (x ^ N) = ⊤) (hy : LinearMap.ker (y ^ N) = ⊤)
    (hle : ∀ k, Module.finrank K (LinearMap.ker (x ^ k))
      ≤ Module.finrank K (LinearMap.ker (y ^ k))) :
    ∑ m ∈ Finset.Icc 1 N, conj x m ^ 2 ≤ ∑ m ∈ Finset.Icc 1 N, conj y m ^ 2 := by
  have hmaj := sum_sq_le_sum_sq_of_majorizes (N := N)
    (fun i => (conj y (i + 1) : ℤ)) (fun i => (conj x (i + 1) : ℤ))
    (fun i j hij => by exact_mod_cast conj_antitone y (by omega) (by omega))
    (fun i j hij => by exact_mod_cast conj_antitone x (by omega) (by omega))
    (fun k => by
      have hx' := sum_Icc_one_eq_sum_range (fun m => (conj x m : ℤ)) k
      have hy' := sum_Icc_one_eq_sum_range (fun m => (conj y m : ℤ)) k
      rw [← hx', ← hy', ← Nat.cast_sum, ← Nat.cast_sum, Nat.cast_le,
        sum_conj_eq_finrank_ker, sum_conj_eq_finrank_ker]
      exact hle k)
    (by
      have hx' := sum_Icc_one_eq_sum_range (fun m => (conj x m : ℤ)) N
      have hy' := sum_Icc_one_eq_sum_range (fun m => (conj y m : ℤ)) N
      rw [← hx', ← hy', ← Nat.cast_sum, ← Nat.cast_sum, Nat.cast_inj,
        sum_conj_eq_finrank_ker, sum_conj_eq_finrank_ker, hx, hy])
  rw [← sum_Icc_one_eq_sum_range (fun m => (conj x m : ℤ) ^ 2),
    ← sum_Icc_one_eq_sum_range (fun m => (conj y m : ℤ) ^ 2)] at hmaj
  exact_mod_cast hmaj

/-- The centraliser dimension of a nilpotent matrix, through its kernel
dimensions: `c(X) = Σ_m conj(X)_m²`. -/
noncomputable def cOf {n : ℕ} (X : Matrix (Fin n) (Fin n) K) : ℕ :=
  ∑ m ∈ Finset.Icc 1 n, (conj (Matrix.toLinAlgEquiv' X) m) ^ 2


/-! ### The matrix form: `c` is monotone under degeneration

`Pencil.orbitClosure N₀` is the *rank* criterion `∀ k, rank (X^k) ≤ rank (N₀^k)`,
so no topology is involved: the criterion says exactly that the kernels of `X`
grow, hence that the conjugate partition of `X` is majorized, hence — by
`sum_conj_sq_le_of_finrank_ker_le` — that `c(N₀) ≤ c(X)`. -/

section MatrixForm

variable {n : ℕ}

/-- The endomorphism of a matrix is its `mulVecLin`. -/
theorem toLinAlgEquiv'_eq_mulVecLin (X : Matrix (Fin n) (Fin n) K) :
    (Matrix.toLinAlgEquiv' X : (Fin n → K) →ₗ[K] (Fin n → K)) = X.mulVecLin := rfl

/-- Rank–nullity in matrix form. -/
theorem rank_add_finrank_ker (X : Matrix (Fin n) (Fin n) K) :
    Matrix.rank X + Module.finrank K (LinearMap.ker (Matrix.toLinAlgEquiv' X)) = n := by
  have h := LinearMap.finrank_range_add_finrank_ker
    (Matrix.toLinAlgEquiv' X : (Fin n → K) →ₗ[K] (Fin n → K))
  have hr : Matrix.rank X = Module.finrank K
      (LinearMap.range (Matrix.toLinAlgEquiv' X : (Fin n → K) →ₗ[K] (Fin n → K))) := rfl
  rw [hr, h]
  simp

/-- A nilpotent matrix is killed by its size: the kernel of the `n`-th power of
its endomorphism is everything. -/
theorem ker_pow_eq_top_of_isNilpotent {X : Matrix (Fin n) (Fin n) K} (hX : IsNilpotent X) :
    LinearMap.ker ((Matrix.toLinAlgEquiv' X) ^ n) = ⊤ := by
  obtain ⟨m, hm⟩ := hX
  have hy : (Matrix.toLinAlgEquiv' X) ^ m = 0 := by
    rw [← map_pow, hm, map_zero]
  have htop : LinearMap.ker ((Matrix.toLinAlgEquiv' X) ^ m) = ⊤ := by
    rw [hy]; exact LinearMap.ker_zero
  have hle := Module.End.ker_pow_le_ker_pow_finrank (Matrix.toLinAlgEquiv' X) m
  rw [htop, top_le_iff] at hle
  simpa using hle

/-- **The centraliser dimension is monotone under degeneration.**  If every
power of `X` has rank at most that of `Y` — the criterion defining
`Pencil.orbitClosure` — and both are nilpotent, then `c(Y) ≤ c(X)`. -/
theorem cOf_le_of_rank_le {X Y : Matrix (Fin n) (Fin n) K}
    (hX : IsNilpotent X) (hY : IsNilpotent Y)
    (h : ∀ k, Matrix.rank (X ^ k) ≤ Matrix.rank (Y ^ k)) :
    cOf Y ≤ cOf X := by
  have hker : ∀ (Z : Matrix (Fin n) (Fin n) K) (k : ℕ),
      Matrix.rank (Z ^ k)
        + Module.finrank K (LinearMap.ker ((Matrix.toLinAlgEquiv' Z) ^ k)) = n := by
    intro Z k
    rw [← map_pow]
    exact rank_add_finrank_ker (Z ^ k)
  show ∑ m ∈ Finset.Icc 1 n, conj (Matrix.toLinAlgEquiv' Y) m ^ 2
      ≤ ∑ m ∈ Finset.Icc 1 n, conj (Matrix.toLinAlgEquiv' X) m ^ 2
  refine sum_conj_sq_le_of_finrank_ker_le (N := n) _ _
    (ker_pow_eq_top_of_isNilpotent hY) (ker_pow_eq_top_of_isNilpotent hX) (fun k => ?_)
  have h1 := hker X k
  have h2 := hker Y k
  have h3 := h k
  omega

end MatrixForm
end Height.Toolbox
