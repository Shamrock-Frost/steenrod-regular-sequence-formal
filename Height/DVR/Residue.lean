import Mathlib.RingTheory.LaurentSeries

/-!
# The residue of a formal Laurent series

The local model of the paper's proof is fixed as follows: `R := PowerSeries K`
is the local ring at a point of the pencil, `L := LaurentSeries K` its fraction
field, and the residue `res_x f\,du` of the paper is the coefficient of
`u^{-1}`.  This file provides that map as an additive homomorphism, records
that it kills the valuation ring (the only two properties `lem:residue-form`
uses), and computes the residue of `u^{-m} f` for a power series `f`, which is
the coefficient pairing used by the block calculations of `ResidueBlocks.lean`.
-/

namespace Height.DVR

open HahnSeries LaurentSeries

universe u

variable {K : Type u} [Field K]

/-- The residue of a formal Laurent series: the coefficient of `u^{-1}`. -/
noncomputable def laurentResidue (K : Type u) [Field K] : LaurentSeries K →+ K :=
  HahnSeries.coeff.addMonoidHom (-1)

@[simp] theorem laurentResidue_apply (f : LaurentSeries K) :
    laurentResidue K f = f.coeff (-1) := rfl

/-- The residue vanishes on the valuation ring `K⟦u⟧`. -/
@[simp] theorem laurentResidue_algebraMap (a : PowerSeries K) :
    laurentResidue K (algebraMap (PowerSeries K) (LaurentSeries K) a) = 0 := by
  show HahnSeries.coeff (algebraMap (PowerSeries K) (LaurentSeries K) a) (-1) = 0
  rw [LaurentSeries.coe_algebraMap]
  show HahnSeries.coeff ((a : PowerSeries K) : LaurentSeries K) (-1) = 0
  rw [PowerSeries.coeff_coe]
  norm_num

/-- `u^{-m}` as a Laurent series. -/
noncomputable def uInvPow (K : Type u) [Field K] (m : ℕ) : LaurentSeries K :=
  HahnSeries.single (-(m : ℤ)) 1

theorem uInvPow_mul_uPow (m : ℕ) :
    uInvPow K m * algebraMap (PowerSeries K) (LaurentSeries K) (PowerSeries.X ^ m) = 1 := by
  rw [uInvPow, LaurentSeries.coe_algebraMap, HahnSeries.ofPowerSeries_X_pow,
    HahnSeries.single_mul_single, neg_add_cancel, mul_one]
  rfl

@[simp] theorem uInvPow_zero : uInvPow K 0 = 1 := by
  simpa using uInvPow_mul_uPow (K := K) 0

/-- `res (u^{-m} f) = [u^{m-1}] f` for a power series `f` and `m ≥ 1`: this is
the coefficient extraction `(a, b) ↦ [u^{m-1}](ab)` of `lem:residue-form`. -/
theorem laurentResidue_uInvPow_mul (m : ℕ) (hm : 1 ≤ m) (f : PowerSeries K) :
    laurentResidue K
        (uInvPow K m * algebraMap (PowerSeries K) (LaurentSeries K) f) =
      PowerSeries.coeff (m - 1) f := by
  rw [laurentResidue_apply, uInvPow, HahnSeries.coeff_single_mul, one_mul,
    LaurentSeries.coe_algebraMap]
  show HahnSeries.coeff ((f : PowerSeries K) : LaurentSeries K) (-1 - -(m : ℤ)) = _
  rw [PowerSeries.coeff_coe]
  have hm' : (1 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm
  split_ifs with h
  · exact absurd h (by omega)
  · have hidx : ((-1 : ℤ) - -(m : ℤ)).natAbs = m - 1 := by omega
    rw [hidx]

end Height.DVR
