import QSteenrod.Characteristic
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Characteristic coefficients and nilpotence (`lem:pencil`)

This file supplies the characteristic-polynomial half of `lem:pencil`.
-/

namespace Height.Steenrod


open Matrix Polynomial

universe u

variable {K : Type u} [Field K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A square matrix over a field is nilpotent exactly when its characteristic
polynomial is a pure power of `X`. -/
theorem matrix_isNilpotent_iff_charpoly (M : Matrix ι ι K) :
    IsNilpotent M ↔ M.charpoly = X ^ Fintype.card ι := by
  rw [← IsNilpotent.map_iff Matrix.toLinAlgEquiv'.injective]
  change IsNilpotent (Matrix.toLin' M) ↔ _
  simpa only [Matrix.charpoly_toLin', Module.finrank_pi]
    using LinearMap.isNilpotent_iff_charpoly (Matrix.toLin' M)

variable (p r N : ℕ) [Fact p.Prime]
variable [Algebra (GaloisField p r) K]

/-- Evaluating the universal signed characteristic coefficient at a matrix
recovers the corresponding coefficient of that matrix's characteristic
polynomial. -/
theorem eval_characteristicCoefficient (M : Matrix (Fin N) (Fin N) K) (j : ℕ) :
    MvPolynomial.aeval (fun ij => M ij.1 ij.2) (QSteenrod.c p r N j) =
      (-1 : K) ^ j * M.charpoly.coeff (N - j) := by
  simp only [QSteenrod.c, map_mul, map_pow, map_neg, map_one]
  rw [MvPolynomial.aeval_eq_eval₂Hom,
    Matrix.charpoly.univ_coeff_eval₂Hom]
  rfl

/-- The signed `j`th universal characteristic coefficient is homogeneous of
degree `j`. -/
theorem characteristicCoefficient_isHomogeneous (j : ℕ) (hj : j ≤ N) :
    (QSteenrod.c p r N j).IsHomogeneous j := by
  have h := Matrix.charpoly.univ_coeff_isHomogeneous
    (R := GaloisField p r) (n := Fin N) (N - j) j (by simp; omega)
  simpa [QSteenrod.c] using h.C_mul ((-1 : GaloisField p r) ^ j)

/-- Vanishing of the non-leading signed characteristic coefficients. -/
def characteristicCoefficientsVanish (M : Matrix (Fin N) (Fin N) K) : Prop :=
  ∀ j, 1 ≤ j → j ≤ N →
    MvPolynomial.aeval (fun ij => M ij.1 ij.2) (QSteenrod.c p r N j) = 0

/-- A matrix is nilpotent exactly when all its non-leading universal
characteristic coefficients vanish at that matrix. -/
theorem characteristicCoefficientsVanish_iff (M : Matrix (Fin N) (Fin N) K) :
    characteristicCoefficientsVanish p r N M ↔ IsNilpotent M := by
  rw [matrix_isNilpotent_iff_charpoly]
  simp only [Fintype.card_fin]
  constructor
  · intro h
    ext k
    by_cases hklt : k < N
    · let j := N - k
      have hj1 : 1 ≤ j := by omega
      have hjN : j ≤ N := Nat.sub_le _ _
      have hc := h j hj1 hjN
      rw [eval_characteristicCoefficient] at hc
      have hcoeff : M.charpoly.coeff (N - j) = 0 := by
        exact (mul_eq_zero.mp hc).resolve_left (pow_ne_zero _ (by simp))
      have hindex : N - j = k := by simp [j, Nat.sub_sub_self hklt.le]
      rw [Polynomial.coeff_X_pow, ite_eq_right hklt.ne]
      simpa [hindex] using hcoeff
    · by_cases hk : k = N
      · subst k
        have hdegree : M.charpoly.natDegree = N := by
          simp
        calc
          M.charpoly.coeff N = M.charpoly.leadingCoeff := by rw [leadingCoeff, hdegree]
          _ = 1 := M.charpoly_monic
          _ = (X ^ N : K[X]).coeff N := by simp
      · have hNk : N < k := lt_of_le_of_ne (Nat.le_of_not_gt hklt) (Ne.symm hk)
        have hdegree : M.charpoly.natDegree = N := by
          simp
        rw [M.charpoly.coeff_eq_zero_of_natDegree_lt (hdegree.symm ▸ hNk)]
        simp [Polynomial.coeff_X_pow, hk]
  · intro h j hj1 hjN
    rw [eval_characteristicCoefficient, h]
    have hne : N - j ≠ N := by omega
    simp [Polynomial.coeff_X_pow, hne]

end Height.Steenrod
