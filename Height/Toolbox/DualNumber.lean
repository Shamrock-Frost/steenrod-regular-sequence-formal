import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Dual numbers: first-order truncation of power series, and first-order Taylor

`PowerSeries.toDualNumber : R⟦X⟧ →+* R[ε]` sends `X ↦ ε`, i.e. keeps the constant
and linear coefficients.  Geometrically it is the closed immersion
`Spec R[ε] ⟶ Spec R⟦X⟧` along which an arc is truncated to its velocity.

`MvPolynomial.aeval_dualNumber` is the first-order Taylor expansion
`f (x + ε v) = f x + ε ⟨df_x, v⟩` of a polynomial at a dual-number point.

General algebra; both are mathlib candidates.
-/

namespace PowerSeries

variable {R : Type*} [CommRing R]

/-! ### First-order truncation -/

/-- **First-order truncation** `R⟦X⟧ → R[ε]`, `X ↦ ε`. -/
noncomputable def toDualNumber : R⟦X⟧ →+* DualNumber R where
  toFun f := TrivSqZeroExt.inl (constantCoeff f) + TrivSqZeroExt.inr (coeff 1 f)
  map_one' := by ext <;> simp
  map_mul' f g := by
    ext
    · simp
    · simp [coeff_mul, Finset.Nat.antidiagonal_succ, coeff_zero_eq_constantCoeff_apply,
        TrivSqZeroExt.snd_mul, mul_comm]
  map_zero' := by ext <;> simp
  map_add' f g := by ext <;> simp

@[simp] theorem fst_toDualNumber (f : R⟦X⟧) :
    (toDualNumber f).fst = constantCoeff f := by
  simp [toDualNumber]

@[simp] theorem snd_toDualNumber (f : R⟦X⟧) :
    (toDualNumber f).snd = coeff 1 f := by
  simp [toDualNumber]

@[simp] theorem toDualNumber_X : toDualNumber (X : R⟦X⟧) = DualNumber.eps := by
  ext <;> simp

/-- Truncating and then reducing to the residue field is the constant coefficient. -/
theorem fstHom_comp_toDualNumber :
    (TrivSqZeroExt.fstHom R R R).toRingHom.comp toDualNumber = constantCoeff := by
  ext f
  simp

/-! ### The two truncations as `R`-algebra maps -/

/-- First-order truncation as an `R`-algebra map. -/
noncomputable def toDualNumberAlgHom : R⟦X⟧ →ₐ[R] DualNumber R :=
  { toDualNumber with
    commutes' := fun r => by
      refine TrivSqZeroExt.ext ?_ ?_ <;>
        simp [TrivSqZeroExt.algebraMap_eq_inl, algebraMap_eq] }

@[simp] theorem toDualNumberAlgHom_apply (f : R⟦X⟧) :
    toDualNumberAlgHom f = toDualNumber f := rfl

theorem toDualNumberAlgHom_toRingHom :
    (toDualNumberAlgHom (R := R)).toRingHom = toDualNumber := rfl

/-- The constant coefficient as an `R`-algebra map. -/
noncomputable def constantCoeffAlgHom : R⟦X⟧ →ₐ[R] R :=
  { constantCoeff with commutes' := fun r => by simp [algebraMap_eq] }

@[simp] theorem constantCoeffAlgHom_apply (f : R⟦X⟧) :
    constantCoeffAlgHom f = constantCoeff f := rfl

theorem constantCoeffAlgHom_toRingHom :
    (constantCoeffAlgHom (R := R)).toRingHom = constantCoeff := rfl

end PowerSeries

namespace MvPolynomial

open TrivSqZeroExt

variable {R : Type*} [CommRing R] {σ : Type*} [Fintype σ]

/-- **First-order Taylor expansion**: evaluating a polynomial at the dual-number point
`x + ε v` gives `f x + ε ⟨df_x, v⟩`. -/
theorem aeval_dualNumber (x v : σ → R) (f : MvPolynomial σ R) :
    aeval (fun i => (inl (x i) + inr (v i) : DualNumber R)) f =
      inl (eval x f) + inr (∑ i, eval x (pderiv i f) * v i) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a => simp [TrivSqZeroExt.algebraMap_eq_inl]
  | add p q hp hq =>
      simp only [map_add, hp, hq, add_mul, Finset.sum_add_distrib, inl_add, inr_add]
      abel
  | mul_X p n hp =>
      simp only [map_mul, hp, aeval_X, pderiv_mul, map_add, pderiv_X, eval_X, add_mul,
        Finset.sum_add_distrib]
      refine TrivSqZeroExt.ext (by simp) ?_
      simp [Pi.single_apply, apply_ite, Finset.mul_sum, mul_comm, mul_left_comm, add_comm]

end MvPolynomial
