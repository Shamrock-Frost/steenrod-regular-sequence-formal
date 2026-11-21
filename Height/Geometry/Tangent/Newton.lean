import Height.Geometry.Tangent.Taylor
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Arcs in a complete intersection with an invertible Jacobian minor

`Height.Geometry.Tangent.exists_arc_of_jacobian_unit`: let
`f : Fin c → MvPolynomial ι K` vanish at `z : ι → K`, let `S : Fin c ↪ ι`
select `c` of the coordinates, and suppose the `c × c` Jacobian minor
`(∂f_j/∂x_{S k})(z)` is invertible.  Then every tangent vector `v` of the zero
locus of the `f_j` at `z` — a solution of the linear system
`∑ i, (∂f_j/∂x_i)(z) · v i = 0` — is the velocity of a `K⟦t⟧`-arc through `z`
on which every `f_j` vanishes identically.

The proof is Newton iteration in `K⟦X⟧`, done by hand: `newtonSeq` starts from
`z i + v i · X` and repeatedly adds `C(u i) · X^(n+2)` with `u` supported on the
range of `S` and determined by the inverse of the minor.  `dvd_aeval_step`
(first-order Taylor from `Taylor.lean`, plus the observation that the
coefficients of the derivative may be replaced by their constant terms modulo
`X`) shows that each stage kills one more coefficient of every `f_j`; the
iterates then stabilise coefficientwise and the limit
`PowerSeries.mk fun m => coeff m (newtonSeq m i)` is the arc.

No adic-completeness API is used: stabilisation is
`PowerSeries.X_pow_dvd_iff` together with `PowerSeries.ext`.  `K` is only
required to be a commutative ring.
-/

universe u v

open MvPolynomial PowerSeries

namespace Height.Geometry.Tangent

variable {K : Type u} [CommRing K] {ι : Type v} [Fintype ι]

/-! ### Evaluating a polynomial at power series -/

omit [Fintype ι] in
/-- Evaluating at constant power series gives the constant power series of the
evaluation. -/
lemma aeval_C_comp (z : ι → K) (g : MvPolynomial ι K) :
    aeval (fun i => (PowerSeries.C (z i) : PowerSeries K)) g = PowerSeries.C (eval z g) := by
  induction g using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p n hp => simp [hp]

omit [Fintype ι] in
/-- The constant term of an evaluation is the evaluation at the constant
terms. -/
lemma constantCoeff_aeval (a : ι → PowerSeries K) (g : MvPolynomial ι K) :
    PowerSeries.constantCoeff (aeval a g) =
      eval (fun i => PowerSeries.constantCoeff (a i)) g := by
  induction g using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p n hp => simp [hp]

/-! ### One Newton step -/

/-- **The Newton step.**  Displacing the arguments by `C(u i) · X^m` (`m ≥ 1`)
changes the value of `g` by `C(∑ i, (∂g/∂x_i)(z) · u i) · X^m` modulo `X^(m+1)`,
provided the arguments have constant terms `z`. -/
lemma dvd_aeval_step {a : ι → PowerSeries K} {z : ι → K}
    (ha : ∀ i, PowerSeries.constantCoeff (a i) = z i) (u : ι → K) {m : ℕ} (hm : 1 ≤ m)
    (g : MvPolynomial ι K) :
    (PowerSeries.X : PowerSeries K) ^ (m + 1) ∣
      aeval (fun i => a i + PowerSeries.C (u i) * PowerSeries.X ^ m) g - aeval a g
        - PowerSeries.C (∑ i, eval z (pderiv i g) * u i) * PowerSeries.X ^ m := by
  classical
  set y : ι → PowerSeries K := fun i => PowerSeries.C (u i) * PowerSeries.X ^ m with hydef
  have hyJ : ∀ i, y i ∈ Ideal.span {(PowerSeries.X : PowerSeries K) ^ m} := fun i =>
    Ideal.mem_span_singleton.2 ⟨PowerSeries.C (u i), by rw [hydef]; ring⟩
  obtain ⟨e, he, hg⟩ :=
    aeval_add_eq (x := a) (y := y) (Ideal.span {(PowerSeries.X : PowerSeries K) ^ m}) hyJ g
  have he2 : (PowerSeries.X : PowerSeries K) ^ (m + 1) ∣ e := by
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, ← pow_mul] at he
    exact dvd_trans (pow_dvd_pow (PowerSeries.X : PowerSeries K) (by lia)) he
  have hza : (fun i => PowerSeries.constantCoeff (a i)) = z := funext ha
  have hdiff : ∀ i : ι,
      (PowerSeries.X : PowerSeries K) ∣ aeval a (pderiv i g) - PowerSeries.C (eval z (pderiv i g)) := by
    intro i
    rw [PowerSeries.X_dvd_iff, map_sub, PowerSeries.constantCoeff_C, constantCoeff_aeval, hza,
      sub_self]
  have hS : (PowerSeries.X : PowerSeries K) ∣
      ∑ i, (aeval a (pderiv i g) - PowerSeries.C (eval z (pderiv i g))) * PowerSeries.C (u i) :=
    Finset.dvd_sum fun i _ => (hdiff i).mul_right _
  have hid : (∑ i, aeval a (pderiv i g) * y i)
      - PowerSeries.C (∑ i, eval z (pderiv i g) * u i) * PowerSeries.X ^ m
      = (∑ i, (aeval a (pderiv i g) - PowerSeries.C (eval z (pderiv i g)))
          * PowerSeries.C (u i)) * PowerSeries.X ^ m := by
    simp only [hydef, map_sum, map_mul, Finset.sum_mul, sub_mul]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hlin : (PowerSeries.X : PowerSeries K) ^ (m + 1) ∣
      (∑ i, aeval a (pderiv i g) * y i)
        - PowerSeries.C (∑ i, eval z (pderiv i g) * u i) * PowerSeries.X ^ m := by
    obtain ⟨t, ht⟩ := hS
    exact ⟨t, by rw [hid, ht]; ring⟩
  have hay : (fun i => a i + PowerSeries.C (u i) * PowerSeries.X ^ m) = a + y := rfl
  rw [hay, hg]
  have hrw : aeval a g + (∑ i, aeval a (pderiv i g) * y i) + e - aeval a g
      - PowerSeries.C (∑ i, eval z (pderiv i g) * u i) * PowerSeries.X ^ m
      = ((∑ i, aeval a (pderiv i g) * y i)
          - PowerSeries.C (∑ i, eval z (pderiv i g) * u i) * PowerSeries.X ^ m) + e := by ring
  rw [hrw]
  exact dvd_add hlin he2

/-- The first Newton step, from the constant tuple `z` to `z + v · X`. -/
lemma dvd_aeval_base (z v : ι → K) (g : MvPolynomial ι K) :
    (PowerSeries.X : PowerSeries K) ^ 2 ∣
      aeval (fun i => PowerSeries.C (z i) + PowerSeries.C (v i) * PowerSeries.X) g
        - PowerSeries.C (eval z g)
        - PowerSeries.C (∑ i, eval z (pderiv i g) * v i) * PowerSeries.X := by
  have h := dvd_aeval_step (a := fun i => (PowerSeries.C (z i) : PowerSeries K)) (z := z)
    (fun i => by simp) v (m := 1) le_rfl g
  simpa only [pow_one, aeval_C_comp] using h

/-! ### The iteration -/

variable {c : ℕ}

/-- Spread a vector indexed by `Fin c` out over `ι` along an embedding. -/
noncomputable def spread [DecidableEq ι] (S : Fin c ↪ ι) (w : Fin c → K) : ι → K :=
  fun i => ∑ k, if S k = i then w k else 0

lemma sum_mul_spread [DecidableEq ι] (S : Fin c ↪ ι) (e : ι → K) (w : Fin c → K) :
    (∑ i, e i * spread S w i) = ∑ k, e (S k) * w k := by
  have h : ∀ i : ι, e i * spread S w i = ∑ k, (if S k = i then e (S k) * w k else 0) := by
    intro i
    rw [spread, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by by_cases h : S k = i <;> simp [h]
  rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => by simp

/-- The right-hand side of the linear system solved at stage `n`. -/
noncomputable def newtonRHS (f : Fin c → MvPolynomial ι K) (a : ι → PowerSeries K) (n : ℕ) :
    Fin c → K :=
  fun j => -(PowerSeries.coeff (n + 2) (aeval a (f j)))

/-- The Newton iterates.  `N` is meant to be the inverse of the Jacobian
minor selected by `S`. -/
noncomputable def newtonSeq [DecidableEq ι] (f : Fin c → MvPolynomial ι K) (z v : ι → K)
    (N : Matrix (Fin c) (Fin c) K) (S : Fin c ↪ ι) : ℕ → (ι → PowerSeries K)
  | 0 => fun i => PowerSeries.C (z i) + PowerSeries.C (v i) * PowerSeries.X
  | n + 1 => fun i =>
      newtonSeq f z v N S n i +
        PowerSeries.C (spread S (N.mulVec (newtonRHS f (newtonSeq f z v N S n) n)) i)
          * PowerSeries.X ^ (n + 2)

omit [Fintype ι] in
lemma newtonSeq_zero [DecidableEq ι] (f : Fin c → MvPolynomial ι K) (z v : ι → K)
    (N : Matrix (Fin c) (Fin c) K) (S : Fin c ↪ ι) :
    newtonSeq f z v N S 0 = fun i => PowerSeries.C (z i) + PowerSeries.C (v i) * PowerSeries.X := rfl

omit [Fintype ι] in
lemma newtonSeq_succ_apply [DecidableEq ι] (f : Fin c → MvPolynomial ι K) (z v : ι → K)
    (N : Matrix (Fin c) (Fin c) K) (S : Fin c ↪ ι) (n : ℕ) (i : ι) :
    newtonSeq f z v N S (n + 1) i =
      newtonSeq f z v N S n i +
        PowerSeries.C (spread S (N.mulVec (newtonRHS f (newtonSeq f z v N S n) n)) i)
          * PowerSeries.X ^ (n + 2) := rfl

omit [Fintype ι] in
/-- Adding `C x · X ^ k` does not change the coefficients below `k`. -/
lemma coeff_C_mul_X_pow_of_lt (x : K) {k p : ℕ} (hp : p < k) :
    PowerSeries.coeff p (PowerSeries.C x * PowerSeries.X ^ k : PowerSeries K) = 0 := by
  simp [Nat.ne_of_lt hp]

omit [Fintype ι] in
/-- Consecutive iterates agree to high order. -/
lemma newtonSeq_sub_dvd [DecidableEq ι] (f : Fin c → MvPolynomial ι K) (z v : ι → K)
    (N : Matrix (Fin c) (Fin c) K) (S : Fin c ↪ ι) (n : ℕ) (i : ι) :
    (PowerSeries.X : PowerSeries K) ^ (n + 2) ∣ newtonSeq f z v N S (n + 1) i - newtonSeq f z v N S n i := by
  rw [newtonSeq_succ_apply, add_sub_cancel_left]
  exact ⟨_, mul_comm _ _⟩

omit [Fintype ι] in
/-- The coefficients of the iterates stabilise. -/
lemma newtonSeq_coeff_stable [DecidableEq ι] (f : Fin c → MvPolynomial ι K) (z v : ι → K)
    (N : Matrix (Fin c) (Fin c) K) (S : Fin c ↪ ι) (i : ι) :
    ∀ (r q p : ℕ), p ≤ q + 1 →
      PowerSeries.coeff p (newtonSeq f z v N S q i)
        = PowerSeries.coeff p (newtonSeq f z v N S (q + r) i) := by
  intro r
  induction r with
  | zero => intro q p _; rfl
  | succ r ih =>
    intro q p hp
    rw [ih q p hp]
    have hd := newtonSeq_sub_dvd f z v N S (q + r) i
    rw [PowerSeries.X_pow_dvd_iff] at hd
    have h2 := hd p (by lia)
    rw [map_sub, sub_eq_zero] at h2
    exact h2.symm

/-- The three invariants of the Newton iteration: the constant term is `z`, the
linear term is `v`, and the `n`-th iterate solves the equations modulo
`X^(n+2)`. -/
lemma newtonSeq_spec [DecidableEq ι] (f : Fin c → MvPolynomial ι K) (z v : ι → K)
    (S : Fin c ↪ ι) (M : Matrix (Fin c) (Fin c) K)
    (hM : M = Matrix.of fun j k => eval z (pderiv (S k) (f j))) (hJ : IsUnit M.det)
    (hz : ∀ j, eval z (f j) = 0) (hv : ∀ j, ∑ i, eval z (pderiv i (f j)) * v i = 0) (n : ℕ) :
    (∀ i, PowerSeries.constantCoeff (newtonSeq f z v M⁻¹ S n i) = z i) ∧
      (∀ i, PowerSeries.coeff 1 (newtonSeq f z v M⁻¹ S n i) = v i) ∧
      (∀ j, (PowerSeries.X : PowerSeries K) ^ (n + 2) ∣ aeval (newtonSeq f z v M⁻¹ S n) (f j)) := by
  induction n with
  | zero =>
    refine ⟨fun i => by rw [newtonSeq_zero]; simp, fun i => by rw [newtonSeq_zero]; simp,
      fun j => ?_⟩
    have h := dvd_aeval_base z v (f j)
    rw [hz j, hv j] at h
    simp only [map_zero, zero_mul, sub_zero] at h
    rw [newtonSeq_zero]
    exact h
  | succ n ih =>
    obtain ⟨hc0, hc1, hd⟩ := ih
    set A : ι → PowerSeries K := newtonSeq f z v M⁻¹ S n with hAdef
    set u : ι → K := spread S (M⁻¹.mulVec (newtonRHS f A n)) with hudef
    have hcorr : ∀ i, newtonSeq f z v M⁻¹ S (n + 1) i = A i + PowerSeries.C (u i) * PowerSeries.X ^ (n + 2) :=
      fun i => rfl
    refine ⟨fun i => ?_, fun i => ?_, fun j => ?_⟩
    · rw [hcorr i, map_add, hc0 i, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
        coeff_C_mul_X_pow_of_lt _ (by lia), add_zero]
    · rw [hcorr i, map_add, hc1 i, coeff_C_mul_X_pow_of_lt _ (by lia), add_zero]
    · -- the linear system is solved by the inverse of the minor
      have hsolve : (∑ i, eval z (pderiv i (f j)) * u i)
          = -(PowerSeries.coeff (n + 2) (aeval A (f j))) := by
        rw [hudef, sum_mul_spread]
        have hrow : (M.mulVec (M⁻¹.mulVec (newtonRHS f A n))) j
            = ∑ k, eval z (pderiv (S k) (f j)) * (M⁻¹.mulVec (newtonRHS f A n)) k := by
          rw [Matrix.mulVec_apply_eq_sum, hM]; rfl
        rw [← hrow, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hJ, Matrix.one_mulVec]
        rfl
      have hstep := dvd_aeval_step (a := A) (z := z) hc0 u (m := n + 2) (by lia) (f j)
      rw [hsolve] at hstep
      -- the previous residue is a multiple of `PowerSeries.X^(n+2)` whose leading term is cancelled
      obtain ⟨h, hh⟩ := hd j
      have hcoeff : PowerSeries.coeff (n + 2) (aeval A (f j)) = PowerSeries.constantCoeff h := by
        have hx := PowerSeries.coeff_X_pow_mul h (n + 2) 0
        rw [zero_add] at hx
        rw [hh, hx, PowerSeries.coeff_zero_eq_constantCoeff_apply]
      have hres : (PowerSeries.X : PowerSeries K) ^ (n + 2 + 1) ∣ aeval A (f j)
          - PowerSeries.C (PowerSeries.coeff (n + 2) (aeval A (f j))) * PowerSeries.X ^ (n + 2) := by
        obtain ⟨t, ht⟩ :=
          (PowerSeries.X_dvd_iff (φ := h - PowerSeries.C (PowerSeries.constantCoeff h))).2 (by simp)
        refine ⟨t, ?_⟩
        rw [hcoeff, hh]
        have hfact : PowerSeries.X ^ (n + 2) * h
            - PowerSeries.C (PowerSeries.constantCoeff h) * PowerSeries.X ^ (n + 2)
            = PowerSeries.X ^ (n + 2) * (h - PowerSeries.C (PowerSeries.constantCoeff h)) := by
          ring
        rw [hfact, ht]
        ring
      have hgoal : aeval (newtonSeq f z v M⁻¹ S (n + 1)) (f j)
          = (aeval (fun i => A i + PowerSeries.C (u i) * PowerSeries.X ^ (n + 2)) (f j) - aeval A (f j)
              - PowerSeries.C (-(PowerSeries.coeff (n + 2) (aeval A (f j)))) * PowerSeries.X ^ (n + 2))
            + (aeval A (f j)
              - PowerSeries.C (PowerSeries.coeff (n + 2) (aeval A (f j))) * PowerSeries.X ^ (n + 2)) := by
        rw [funext hcorr, map_neg]
        ring
      rw [hgoal]
      exact dvd_add hstep hres

/-! ### The arc -/

/-- **Newton lifting.**  In a complete intersection with an invertible Jacobian minor at a
zero `z`, every tangent vector is the velocity of an arc.

`v` is a tangent vector of the zero locus of `f` at `z` (`hv`) and `S` selects
`c` coordinates whose Jacobian minor at `z` is invertible (`hJ`); the conclusion
produces a tuple of power series `a` with constant term `z`, first coefficient
`v`, and `f_j(a) = 0` identically. -/
theorem exists_arc_of_jacobian_unit {c : ℕ} (f : Fin c → MvPolynomial ι K) (z : ι → K)
    (hz : ∀ j, MvPolynomial.eval z (f j) = 0) (S : Fin c ↪ ι)
    (hJ : IsUnit (Matrix.of fun j k =>
      MvPolynomial.eval z (MvPolynomial.pderiv (S k) (f j))).det)
    (v : ι → K)
    (hv : ∀ j, ∑ i, MvPolynomial.eval z (MvPolynomial.pderiv i (f j)) * v i = 0) :
    ∃ a : ι → PowerSeries K, (∀ i, PowerSeries.constantCoeff (a i) = z i) ∧
      (∀ i, PowerSeries.coeff 1 (a i) = v i) ∧ ∀ j, MvPolynomial.aeval a (f j) = 0 := by
  classical
  have main := newtonSeq_spec f z v S _ rfl hJ hz hv
  refine ⟨fun i => PowerSeries.mk fun p =>
    PowerSeries.coeff p (newtonSeq f z v (Matrix.of fun j k =>
      MvPolynomial.eval z (MvPolynomial.pderiv (S k) (f j)))⁻¹ S p i), fun i => ?_, fun i => ?_,
    fun j => ?_⟩
  · rw [PowerSeries.constantCoeff_mk, PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact (main 0).1 i
  · rw [PowerSeries.coeff_mk]
    exact (main 1).2.1 i
  · -- every coefficient of the limit agrees with a late enough iterate
    set N := (Matrix.of fun j k =>
      MvPolynomial.eval z (MvPolynomial.pderiv (S k) (f j)) : Matrix (Fin c) (Fin c) K)⁻¹ with hN
    set b : ι → PowerSeries K :=
      fun i => PowerSeries.mk fun p => PowerSeries.coeff p (newtonSeq f z v N S p i) with hb
    have hlim : ∀ n i, (PowerSeries.X : PowerSeries K) ^ (n + 2) ∣ b i - newtonSeq f z v N S n i := by
      intro n i
      rw [PowerSeries.X_pow_dvd_iff]
      intro p hp
      rw [map_sub, hb, PowerSeries.coeff_mk, sub_eq_zero]
      rcases le_or_gt p n with hpn | hpn
      · have hst := newtonSeq_coeff_stable f z v N S i (n - p) p p (Nat.le_succ p)
        rw [show p + (n - p) = n from by lia] at hst
        exact hst
      · have hpe : p = n + 1 := by lia
        subst hpe
        exact (newtonSeq_coeff_stable f z v N S i 1 n (n + 1) le_rfl).symm
    have hall : ∀ n, (PowerSeries.X : PowerSeries K) ^ (n + 2) ∣ aeval b (f j) := by
      intro n
      have hmem : ∀ i, b i - newtonSeq f z v N S n i
          ∈ Ideal.span {(PowerSeries.X : PowerSeries K) ^ (n + 2)} :=
        fun i => Ideal.mem_span_singleton.2 (hlim n i)
      have h1 := aeval_sub_aeval_mem (Ideal.span {(PowerSeries.X : PowerSeries K) ^ (n + 2)}) hmem (f j)
      rw [Ideal.mem_span_singleton] at h1
      simpa using dvd_add h1 ((main n).2.2 j)
    refine PowerSeries.ext fun p => ?_
    simpa using (PowerSeries.X_pow_dvd_iff).1 (hall p) p (by lia)

end Height.Geometry.Tangent
