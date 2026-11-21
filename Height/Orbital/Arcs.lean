import Mathlib.RingTheory.LaurentSeries
import Height.Orbital.Strata
import Isotropy.DVRCore

/-!
# Arcs in a chain stratum

An arc is a `K⟦s⟧`-point of
`gl_n`, i.e. a matrix of power series; its *base point* is the matrix of
constant terms, its *velocity* the matrix of linear coefficients, and its
*generic point* its image in `gl_n(K⸨s⸩)`.  Here "an arc
in the stratum `A_T`" means: base point in `A_T` (over `K`) and generic point
in `A_T` (over `K⸨s⸩`).  No scheme and no "all but finitely many
specializations" enter.

`ArcIn.restrict` restricts an arc to the first `n` coordinates.
`tangent_equation_arc` is the coefficient extraction: the constant and
linear coefficients of an incidence equation `y_s^c u_s = y_s^{c-1} v_s`
are exactly the two hypotheses `hbase` and `htangent` of the algebraic
transporter step.
-/

namespace Height.Orbital

open Matrix
open Height.Toolbox

universe u

section Coeff

variable {K : Type u} [Field K] {n : ℕ}

/-- The constant term of a matrix of power series. -/
noncomputable def matC (M : Matrix (Fin n) (Fin n) (PowerSeries K)) : Matrix (Fin n) (Fin n) K :=
  M.map PowerSeries.constantCoeff

/-- The linear coefficient of a matrix of power series. -/
noncomputable def matD (M : Matrix (Fin n) (Fin n) (PowerSeries K)) : Matrix (Fin n) (Fin n) K :=
  M.map (PowerSeries.coeff 1)

/-- The constant term of a vector of power series. -/
noncomputable def vecC (w : Fin n → PowerSeries K) : Fin n → K :=
  fun i => PowerSeries.constantCoeff (w i)

/-- The linear coefficient of a vector of power series. -/
noncomputable def vecD (w : Fin n → PowerSeries K) : Fin n → K :=
  fun i => PowerSeries.coeff 1 (w i)

@[simp] theorem matC_apply (M : Matrix (Fin n) (Fin n) (PowerSeries K)) (i j : Fin n) :
    matC M i j = PowerSeries.constantCoeff (M i j) := rfl

@[simp] theorem matD_apply (M : Matrix (Fin n) (Fin n) (PowerSeries K)) (i j : Fin n) :
    matD M i j = PowerSeries.coeff 1 (M i j) := rfl

/-- A constant matrix of power series has itself as constant term. -/
theorem matC_map_C (A : Matrix (Fin n) (Fin n) K) :
    matC (A.map (PowerSeries.C : K →+* PowerSeries K)) = A := by
  ext i j; simp [matC]

/-- A constant matrix of power series has no linear term. -/
theorem matD_map_C (A : Matrix (Fin n) (Fin n) K) :
    matD (A.map (PowerSeries.C : K →+* PowerSeries K)) = 0 := by
  ext i j
  show PowerSeries.coeff 1 (PowerSeries.C (A i j)) = 0
  simp

theorem matC_mul (M N : Matrix (Fin n) (Fin n) (PowerSeries K)) :
    matC (M * N) = matC M * matC N :=
  Matrix.map_mul

theorem matC_pow (M : Matrix (Fin n) (Fin n) (PowerSeries K)) (k : ℕ) :
    matC (M ^ k) = matC M ^ k := by
  induction k with
  | zero =>
      rw [pow_zero, pow_zero]
      ext i j
      by_cases h : i = j <;> simp [matC, Matrix.one_apply, h]
  | succ k ih => rw [pow_succ, pow_succ, matC_mul, ih]

/-- The Leibniz rule for the linear coefficient of a product of power
series. -/
theorem coeff_one_mul (φ ψ : PowerSeries K) :
    PowerSeries.coeff 1 (φ * ψ) =
      PowerSeries.coeff 1 φ * PowerSeries.constantCoeff ψ +
        PowerSeries.constantCoeff φ * PowerSeries.coeff 1 ψ := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  simp [PowerSeries.coeff_zero_eq_constantCoeff_apply, add_comm]

/-- The constant term of a scalar multiple by a power series. -/
theorem matC_smul_series (φ : PowerSeries K) (M : Matrix (Fin n) (Fin n) (PowerSeries K)) :
    matC (φ • M) = PowerSeries.constantCoeff φ • matC M := by
  ext i j
  show PowerSeries.constantCoeff (φ * M i j) = _
  rw [map_mul]
  rfl

/-- The Leibniz rule for the linear term of a scalar multiple by a power
series. -/
theorem matD_smul_series (φ : PowerSeries K) (M : Matrix (Fin n) (Fin n) (PowerSeries K)) :
    matD (φ • M) = PowerSeries.coeff 1 φ • matC M + PowerSeries.constantCoeff φ • matD M := by
  ext i j
  show PowerSeries.coeff 1 (φ * M i j) = _
  rw [coeff_one_mul]
  rfl

/-- The constant term is additive. -/
theorem matC_add (M N : Matrix (Fin n) (Fin n) (PowerSeries K)) :
    matC (M + N) = matC M + matC N := by
  ext i j; simp [matC]

/-- The linear term is additive. -/
theorem matD_add (M N : Matrix (Fin n) (Fin n) (PowerSeries K)) :
    matD (M + N) = matD M + matD N := by
  ext i j; simp [matD]

theorem matD_mul (M N : Matrix (Fin n) (Fin n) (PowerSeries K)) :
    matD (M * N) = matD M * matC N + matC M * matD N := by
  ext i j
  show PowerSeries.coeff 1 ((M * N) i j) = _
  rw [Matrix.mul_apply, map_sum]
  simp only [Matrix.add_apply, Matrix.mul_apply, matD_apply, matC_apply,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => coeff_one_mul _ _

theorem matD_pow (M : Matrix (Fin n) (Fin n) (PowerSeries K)) (k : ℕ) :
    matD (M ^ k) = Isotropy.dpow (matC M) (matD M) k := by
  induction k with
  | zero =>
      rw [pow_zero, Isotropy.dpow_zero]
      ext i j
      by_cases h : i = j <;> simp [matD, h]
  | succ k ih =>
      rw [pow_succ, matD_mul, ih, matC_pow, Isotropy.dpow_succ']

theorem vecC_mulVec (M : Matrix (Fin n) (Fin n) (PowerSeries K))
    (w : Fin n → PowerSeries K) : vecC (M *ᵥ w) = matC M *ᵥ vecC w := by
  funext i
  exact RingHom.map_mulVec PowerSeries.constantCoeff M w i

theorem vecD_mulVec (M : Matrix (Fin n) (Fin n) (PowerSeries K))
    (w : Fin n → PowerSeries K) :
    vecD (M *ᵥ w) = matD M *ᵥ vecC w + matC M *ᵥ vecD w := by
  funext i
  show PowerSeries.coeff 1 ((M *ᵥ w) i) = _
  rw [Matrix.mulVec, dotProduct, map_sum]
  simp only [Pi.add_apply, Matrix.mulVec, dotProduct, matD_apply, matC_apply, vecC, vecD,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => coeff_one_mul _ _

/-- The constant and linear coefficients of an incidence equation
`y_s^c u_s = y_s^{c-1} v_s` over `K⟦s⟧`.  These are exactly the hypotheses
`hbase` and `htangent` of the algebraic transporter step. -/
theorem tangent_equation_arc (Y : Matrix (Fin n) (Fin n) (PowerSeries K))
    (u v : Fin n → PowerSeries K) (c : ℕ)
    (h : (Y ^ c) *ᵥ u = (Y ^ (c - 1)) *ᵥ v) :
    (matC Y ^ c) *ᵥ vecC u = (matC Y ^ (c - 1)) *ᵥ vecC v ∧
      Isotropy.dpow (matC Y) (matD Y) (c - 1) *ᵥ vecC v +
            (matC Y ^ (c - 1)) *ᵥ vecD v =
          Isotropy.dpow (matC Y) (matD Y) c *ᵥ vecC u + (matC Y ^ c) *ᵥ vecD u := by
  constructor
  · have hc := congrArg vecC h
    rwa [vecC_mulVec, vecC_mulVec, matC_pow, matC_pow] at hc
  · have hd := congrArg vecD h
    rw [vecD_mulVec, vecD_mulVec, matC_pow, matC_pow, matD_pow, matD_pow] at hd
    exact hd.symm

end Coeff

section Arcs

variable {K : Type u} [Field K] {n : ℕ}

/-- An arc in `gl_n`: a `K⟦s⟧`-point, i.e. a matrix of power series. -/
structure Arc (n : ℕ) (K : Type u) [Field K] where
  /-- The underlying matrix of power series. -/
  mat : Matrix (Fin n) (Fin n) (PowerSeries K)

/-- The base point `x_0` of an arc. -/
noncomputable def Arc.base (a : Arc n K) : Matrix (Fin n) (Fin n) K := matC a.mat

/-- The velocity `ẋ` of an arc. -/
noncomputable def Arc.vel (a : Arc n K) : Matrix (Fin n) (Fin n) K := matD a.mat

/-- The generic point of an arc: its image in `gl_n` over the Laurent series
field `K⸨s⸩`. -/
noncomputable def Arc.gen (a : Arc n K) : Matrix (Fin n) (Fin n) (LaurentSeries K) :=
  Isotropy.toK (LaurentSeries K) a.mat

/-- Restriction of an arc to the first `n` coordinates. -/
def Arc.restrict (a : Arc (n + 1) K) : Arc n K :=
  ⟨_root_.Height.Orbital.restrict a.mat⟩

@[simp] theorem Arc.base_restrict (a : Arc (n + 1) K) :
    a.restrict.base = _root_.Height.Orbital.restrict a.base := rfl

@[simp] theorem Arc.gen_restrict (a : Arc (n + 1) K) :
    a.restrict.gen = _root_.Height.Orbital.restrict a.gen := rfl

/-- An arc in the chain stratum `A_T` through `x`: base point and generic
point both in `A_T`. -/
structure ArcIn (T : Fin n → ℕ) (x : Matrix (Fin n) (Fin n) K) extends Arc n K where
  /-- The base point of the arc is `x`. -/
  base_eq : toArc.base = x
  /-- The base point lies in the stratum. -/
  base_mem : inStratum T x
  /-- The generic point lies in the stratum, over `K⸨s⸩`. -/
  gen_mem : inStratum T toArc.gen

/-- The matrix of power series underlying an arc in a stratum is strictly
upper triangular: this is inherited from the generic point, the map to
Laurent series being injective. -/
theorem ArcIn.isStrictlyUpper_mat {T : Fin n → ℕ} {x : Matrix (Fin n) (Fin n) K}
    (a : ArcIn T x) : IsStrictlyUpper a.mat :=
  isStrictlyUpper_of_map (algebraMap (PowerSeries K) (LaurentSeries K))
    (IsFractionRing.injective (PowerSeries K) (LaurentSeries K)) a.gen_mem.upper

/-- The velocity of an arc in a stratum is strictly upper triangular. -/
theorem ArcIn.isStrictlyUpper_vel {T : Fin n → ℕ} {x : Matrix (Fin n) (Fin n) K}
    (a : ArcIn T x) : IsStrictlyUpper a.vel := fun i j hij => by
  show PowerSeries.coeff 1 (a.mat i j) = 0
  rw [a.isStrictlyUpper_mat i j hij, map_zero]

/-- An arc in `A_T` restricts to an arc in `A_{T ∘ castSucc}`. -/
def ArcIn.restrict {T : Fin (n + 1) → ℕ} {x : Matrix (Fin (n + 1)) (Fin (n + 1)) K}
    (a : ArcIn T x) :
    ArcIn (T ∘ Fin.castSucc) (_root_.Height.Orbital.restrict x) where
  toArc := a.toArc.restrict
  base_eq := by rw [Arc.base_restrict, a.base_eq]
  base_mem := inStratum_restrict a.base_mem
  gen_mem := by
    rw [Arc.gen_restrict]
    exact inStratum_restrict a.gen_mem

end Arcs

end Height.Orbital
