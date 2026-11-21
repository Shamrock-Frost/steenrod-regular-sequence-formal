import Height.Orbital.KK
import Height.Toolbox.Flags

/-!
# Conjugation invariance of the Kostant--Kirillov representative form

The representative trace formula for the Kostant--Kirillov pairing is
unchanged by simultaneous change of basis.
-/

namespace Height.Orbital

open Matrix

universe u

variable {K : Type u} [Field K] {n : ℕ}

/-- The representative Kostant--Kirillov formula is invariant under
simultaneous conjugation. -/
theorem kkForm_matrixConjugation
    (g : (Matrix (Fin n) (Fin n) K)ˣ)
    (x A B : Matrix (Fin n) (Fin n) K) :
    kkForm
        (Height.Toolbox.matrixConjugationLinearEquiv K n g x)
        (Height.Toolbox.matrixConjugationLinearEquiv K n g A)
        (Height.Toolbox.matrixConjugationLinearEquiv K n g B) =
      kkForm x A B := by
  unfold kkForm
  have hmatrix :
      Height.Toolbox.matrixConjugationLinearEquiv K n g x *
          (Height.Toolbox.matrixConjugationLinearEquiv K n g A *
              Height.Toolbox.matrixConjugationLinearEquiv K n g B -
            Height.Toolbox.matrixConjugationLinearEquiv K n g B *
              Height.Toolbox.matrixConjugationLinearEquiv K n g A) =
        (g : Matrix (Fin n) (Fin n) K) * (x * (A * B - B * A)) *
          (↑(g⁻¹) : Matrix (Fin n) (Fin n) K) := by
    simp [Height.Toolbox.matrixConjugationLinearEquiv_apply,
      mul_sub, sub_mul, Matrix.mul_assoc]
  rw [hmatrix, Matrix.trace_units_conj]

end Height.Orbital
