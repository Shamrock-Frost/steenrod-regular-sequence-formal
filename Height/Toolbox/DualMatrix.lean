import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Data.Matrix.Mul
import Isotropy.DPow

/-!
# Matrices over the dual numbers: first-order calculus

A matrix over `R[ε]` is a value `mfst A` and a first-order part `msnd A`, and
multiplication is the Leibniz rule.  The point of the file is `msnd_pow`:

```
msnd (A ^ k) = Isotropy.dpow (mfst A) (msnd A) k ,
```

the derivative of a `k`-th power in the direction `msnd A` — which is what turns
a first-order deformation of a matrix into a statement about the motion of its
kernel flag.
-/

namespace Height.Toolbox

open Matrix TrivSqZeroExt

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The value of a matrix over the dual numbers. -/
def mfst (A : Matrix (Fin n) (Fin n) (DualNumber R)) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => (A i j).fst

/-- The first-order part of a matrix over the dual numbers. -/
def msnd (A : Matrix (Fin n) (Fin n) (DualNumber R)) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => (A i j).snd

/-- The value of a vector over the dual numbers. -/
def vfst (y : Fin n → DualNumber R) : Fin n → R := fun i => (y i).fst

/-- The first-order part of a vector over the dual numbers. -/
def vsnd (y : Fin n → DualNumber R) : Fin n → R := fun i => (y i).snd

@[simp] theorem mfst_apply (A : Matrix (Fin n) (Fin n) (DualNumber R)) (i j : Fin n) :
    mfst A i j = (A i j).fst := rfl

@[simp] theorem msnd_apply (A : Matrix (Fin n) (Fin n) (DualNumber R)) (i j : Fin n) :
    msnd A i j = (A i j).snd := rfl

@[simp] theorem vfst_apply (y : Fin n → DualNumber R) (i : Fin n) :
    vfst y i = (y i).fst := rfl

@[simp] theorem vsnd_apply (y : Fin n → DualNumber R) (i : Fin n) :
    vsnd y i = (y i).snd := rfl

@[simp] theorem mfst_one : mfst (1 : Matrix (Fin n) (Fin n) (DualNumber R)) = 1 := by
  refine Matrix.ext fun i j => ?_
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem mfst_mul (A B : Matrix (Fin n) (Fin n) (DualNumber R)) :
    mfst (A * B) = mfst A * mfst B := by
  refine Matrix.ext fun i j => ?_
  show ((∑ l, A i l * B l j)).fst = ∑ l, (A i l).fst * (B l j).fst
  rw [fst_sum]
  exact Finset.sum_congr rfl fun l _ => fst_mul _ _

theorem msnd_mul (A B : Matrix (Fin n) (Fin n) (DualNumber R)) :
    msnd (A * B) = mfst A * msnd B + msnd A * mfst B := by
  refine Matrix.ext fun i j => ?_
  show ((∑ l, A i l * B l j)).snd
    = (∑ l, (A i l).fst * (B l j).snd) + ∑ l, (A i l).snd * (B l j).fst
  rw [snd_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [snd_mul]
  show (A i l).fst • (B l j).snd + (MulOpposite.op (B l j).fst) • (A i l).snd = _
  simp [MulOpposite.smul_eq_mul_unop, mul_comm]

theorem mfst_pow (A : Matrix (Fin n) (Fin n) (DualNumber R)) (k : ℕ) :
    mfst (A ^ k) = (mfst A) ^ k := by
  induction k with
  | zero => simpa using mfst_one
  | succ k ih => rw [pow_succ, mfst_mul, ih, pow_succ]

/-- **The first-order part of a power is the derivative of the power.** -/
theorem msnd_pow (A : Matrix (Fin n) (Fin n) (DualNumber R)) (k : ℕ) :
    msnd (A ^ k) = Isotropy.dpow (mfst A) (msnd A) k := by
  induction k with
  | zero =>
      rw [pow_zero, Isotropy.dpow_zero]
      refine Matrix.ext fun i j => ?_
      by_cases h : i = j <;> simp [Matrix.one_apply, h]
  | succ k ih =>
      rw [pow_succ, msnd_mul, ih, mfst_pow, Isotropy.dpow_succ']
      exact add_comm _ _

theorem vfst_mulVec (A : Matrix (Fin n) (Fin n) (DualNumber R)) (y : Fin n → DualNumber R) :
    vfst (A *ᵥ y) = mfst A *ᵥ vfst y := by
  funext i
  show ((∑ l, A i l * y l)).fst = ∑ l, (A i l).fst * (y l).fst
  rw [fst_sum]
  exact Finset.sum_congr rfl fun l _ => fst_mul _ _

theorem vsnd_mulVec (A : Matrix (Fin n) (Fin n) (DualNumber R)) (y : Fin n → DualNumber R) :
    vsnd (A *ᵥ y) = mfst A *ᵥ vsnd y + msnd A *ᵥ vfst y := by
  funext i
  show ((∑ l, A i l * y l)).snd
    = (∑ l, (A i l).fst * (y l).snd) + ∑ l, (A i l).snd * (y l).fst
  rw [snd_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [snd_mul]
  show (A i l).fst • (y l).snd + (MulOpposite.op (y l).fst) • (A i l).snd = _
  simp [MulOpposite.smul_eq_mul_unop, mul_comm]

theorem vfst_eq_zero_of_eq_zero {y : Fin n → DualNumber R} (h : y = 0) : vfst y = 0 := by
  rw [h]; funext i; simp [vfst]

theorem vsnd_eq_zero_of_eq_zero {y : Fin n → DualNumber R} (h : y = 0) : vsnd y = 0 := by
  rw [h]; funext i; simp [vsnd]



/-! ## Polynomials with dual-number coefficients -/

section Poly

variable {K : Type*} [CommRing K] {S : Type*} [CommRing S]

/-- A ring map applied to both components of a dual number. -/
def dnMap (f : K →+* S) : DualNumber K →+* DualNumber S where
  toFun x := TrivSqZeroExt.inl (f x.fst) + TrivSqZeroExt.inr (f x.snd)
  map_one' := by
    refine TrivSqZeroExt.ext ?_ ?_ <;> simp
  map_mul' x y := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp [TrivSqZeroExt.fst_mul]
    · simp [TrivSqZeroExt.snd_mul, MulOpposite.smul_eq_mul_unop, mul_comm]
  map_zero' := by
    refine TrivSqZeroExt.ext ?_ ?_ <;> simp
  map_add' x y := by
    refine TrivSqZeroExt.ext ?_ ?_ <;> simp

@[simp] theorem fst_dnMap (f : K →+* S) (x : DualNumber K) : (dnMap f x).fst = f x.fst := by
  simp [dnMap]

@[simp] theorem snd_dnMap (f : K →+* S) (x : DualNumber K) : (dnMap f x).snd = f x.snd := by
  simp [dnMap]

/-- The coefficient inclusion `K[ε] → K[X][ε]`. -/
noncomputable abbrev dnC : DualNumber K →+* DualNumber (Polynomial K) :=
  dnMap Polynomial.C

/-- Evaluation of both components at `X = 0`. -/
noncomputable abbrev dnEval0 : DualNumber (Polynomial K) →+* DualNumber K :=
  dnMap (Polynomial.evalRingHom 0)

/-- `K[ε][u] → K[u][ε]`: a polynomial with dual-number coefficients is a dual
number with polynomial components. -/
noncomputable def polyDual : Polynomial (DualNumber K) →+* DualNumber (Polynomial K) :=
  Polynomial.eval₂RingHom dnC (TrivSqZeroExt.inl Polynomial.X)

@[simp] theorem polyDual_C (x : DualNumber K) :
    polyDual (Polynomial.C x) = dnC x := by
  simp [polyDual]

@[simp] theorem polyDual_X :
    polyDual (Polynomial.X : Polynomial (DualNumber K))
      = TrivSqZeroExt.inl Polynomial.X := by
  simp [polyDual]

/-- Both components of `polyDual p` at `u = 0` are the components of the
constant coefficient of `p`. -/
theorem dnEval0_polyDual (p : Polynomial (DualNumber K)) :
    dnEval0 (polyDual p) = p.coeff 0 := by
  have h1 : dnEval0 (polyDual p)
      = Polynomial.eval₂ ((dnEval0 (K := K)).comp dnC)
          (dnEval0 (TrivSqZeroExt.inl Polynomial.X)) p := by
    show dnEval0 (Polynomial.eval₂ dnC (TrivSqZeroExt.inl Polynomial.X) p) = _
    rw [Polynomial.hom_eval₂]
  have h2 : ((dnEval0 (K := K)).comp dnC) = RingHom.id (DualNumber K) := by
    refine RingHom.ext fun x => ?_
    refine TrivSqZeroExt.ext ?_ ?_ <;> simp
  have h3 : dnEval0 (TrivSqZeroExt.inl (Polynomial.X : Polynomial K)) = 0 := by
    refine TrivSqZeroExt.ext ?_ ?_ <;> simp
  rw [h1, h2, h3, Polynomial.eval₂_at_zero]
  rfl

end Poly

end Height.Toolbox
