import Height.Steenrod.Criterion
import Mathlib.FieldTheory.Perfect

/-!
# Entrywise Frobenius as a matrix automorphism (`lem:pencil`, `prop:untwist`)

`lem:pencil` reads the Steenrod vanishing at `M` off the pencil
`Span{M, Fr(M)}`, where `Fr` is the entrywise `q`-power map; `prop:untwist`
uses that `Fr` is a ring map and that it fixes the `F_q`-rational matrices.

This file holds the one fact about `Fr` that is not already in
`Steenrod/Criterion.lean`: it fixes the image of `Mat_n(F_q)` in `Mat_n(K)`.
Nilpotence is preserved by `frobeniusMatrix_isNilpotent`, there.
-/

namespace Height.Steenrod

section Rational

/-! ### Rational matrices are Frobenius-fixed (`prop:untwist`) -/

universe u v

variable (p r : ℕ) [Fact p.Prime] [NeZero r]
variable {K : Type u} [Field K] [ExpChar K p]
variable [Algebra (GaloisField p r) K]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- Scalar extension of a matrix whose entries lie in `F_q` is fixed by
entrywise `q`-Frobenius. -/
theorem frobeniusMatrix_map_algebraMap
    (M : Matrix ι ι (GaloisField p r)) :
    frobeniusMatrix p r (M.map (algebraMap (GaloisField p r) K)) =
      M.map (algebraMap (GaloisField p r) K) := by
  ext i j
  rw [frobeniusMatrix_apply]
  change (algebraMap (GaloisField p r) K (M i j)) ^ (p ^ r) =
    algebraMap (GaloisField p r) K (M i j)
  rw [← map_pow]
  apply congrArg (algebraMap (GaloisField p r) K)
  let := Fintype.ofFinite (GaloisField p r)
  have hcard : Fintype.card (GaloisField p r) = p ^ r := by
    simpa only [Nat.card_eq_fintype_card] using QSteenrod.card_galoisField p r
  simpa only [hcard] using FiniteField.pow_card (M i j)

end Rational

end Height.Steenrod
