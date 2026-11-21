import Height.Geometry.Coordinates
import Height.Steenrod.PartnerUniversalIdeal
import Height.Steenrod.Krull
import Mathlib.RingTheory.Nullstellensatz

/-!
# The affine zero locus of the Steenrod ideal (`defn:J`, `rem:krull`)

This packages the target zero locus as a set of matrices and identifies its
entry coordinates with mathlib's affine zero locus.  The pencil criterion
then gives the intrinsic description by the Frobenius pencil.  We also prove
directly that this locus is a cone and record its Nullstellensatz ideal.

This is `V(J)` of `defn:J`, in the form in which `rem:krull` compares its
dimension with `C(n,2)`.
-/

namespace Height.Steenrod

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable (p r n : ℕ) [Fact p.Prime]
variable {K : Type u} [Field K] [Algebra (GaloisField p r) K]

/-- The matrix-valued affine zero locus of the Steenrod ideal. -/
def steenrodMatrixZeroLocus : Set (Matrix (Fin n) (Fin n) K) :=
  {M | steenrodIdealVanishAt p r n M}

/-- Entry coordinates identify the matrix-valued Steenrod locus with the
affine zero locus of the Steenrod ideal. -/
theorem image_steenrodMatrixZeroLocus :
    Geometry.matCoords (K := K) '' steenrodMatrixZeroLocus p r n =
      MvPolynomial.zeroLocus K (steenrodIdeal p r n) := by
  ext x
  constructor
  · rintro ⟨M, hM, rfl⟩
    exact hM
  · intro hx
    refine ⟨(Geometry.matCoords (K := K)).symm x, ?_, ?_⟩
    · exact hx
    · exact (Geometry.matCoords (K := K)).apply_symm_apply x

/-- Nullstellensatz form of the target equations: over an algebraically
closed extension field, all polynomial functions over `F_q` vanishing on
the matrix-valued Steenrod locus form the radical Steenrod ideal. -/
theorem vanishingIdeal_steenrodMatrixZeroLocus_eq_radical
    [IsAlgClosed K] :
    MvPolynomial.vanishingIdeal (GaloisField p r)
        (Geometry.matCoords (K := K) ''
          steenrodMatrixZeroLocus p r n) =
      (steenrodIdeal p r n).radical := by
  rw [image_steenrodMatrixZeroLocus]
  exact MvPolynomial.vanishingIdeal_zeroLocus_eq_radical
    (steenrodIdeal p r n)

end Height.Steenrod
