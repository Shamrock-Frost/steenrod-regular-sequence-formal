import Height.Steenrod.LangUntwist

/-!
# The Frobenius-semilinear row map of `lem:semilinear`

For an invertible target matrix `b`, the rows needed to solve Lang's equation
are the fixed vectors of the Frobenius-semilinear map `x ↦ Fr(x) b⁻¹`.  This
file defines that map (`langFixedRowMap`), records its semilinearity
(`langFixedRowMap_smul`) and says what being fixed means in coordinates
(`langFixedRowMap_fixed_iff`).

`thm:lang` is `Lang/Counting.lean`'s `matrixLang_surjective`, proved by
Lang–Steinberg descent.  The counting half of `lem:semilinear` is not needed
for that proof and is not proved here.
-/

namespace Height.Steenrod

open Height.Toolbox

open scoped Matrix

universe u

variable (p r n : ℕ) [Fact p.Prime]
variable {K : Type u} [Field K] [ExpChar K p] [NeZero r] [IsAlgClosed K]

/-- Frobenius on row vectors, followed by right multiplication by `b⁻¹`. -/
def langFixedRowMap (b : (Matrix (Fin n) (Fin n) K)ˣ) :
    (Fin n → K) →+ (Fin n → K) where
  toFun x := (fun i => x i ^ (p ^ r)) ᵥ*
    (↑(b⁻¹) : Matrix (Fin n) (Fin n) K)
  map_zero' := by
    have hq : p ^ r ≠ 0 := pow_ne_zero r (Fact.out : Nat.Prime p).ne_zero
    ext j
    simp [Matrix.vecMul_apply_eq_sum, zero_pow hq]
  map_add' x y := by
    ext j
    simp only [Pi.add_apply, Matrix.vecMul_apply_eq_sum,
      add_pow_expChar_pow, add_mul, Finset.sum_add_distrib]

omit [NeZero r] [IsAlgClosed K] in
/-- The row map is semilinear for the `p^r`-power Frobenius. -/
theorem langFixedRowMap_smul (b : (Matrix (Fin n) (Fin n) K)ˣ)
    (a : K) (x : Fin n → K) :
    langFixedRowMap p r n b (a • x) =
      (a ^ (p ^ r)) • langFixedRowMap p r n b x := by
  ext j
  change (∑ i, (a * x i) ^ (p ^ r) *
      (↑(b⁻¹) : Matrix (Fin n) (Fin n) K) i j) =
    a ^ (p ^ r) * (∑ i, x i ^ (p ^ r) *
      (↑(b⁻¹) : Matrix (Fin n) (Fin n) K) i j)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_pow]
  ring

omit [NeZero r] [IsAlgClosed K] in
/-- Fixed rows for `x ↦ Fr(x)b⁻¹` are exactly the solutions of
`Fr(x) = xb`. -/
theorem langFixedRowMap_fixed_iff
    (b : (Matrix (Fin n) (Fin n) K)ˣ) (x : Fin n → K) :
    langFixedRowMap p r n b x = x ↔
      (fun j => x j ^ (p ^ r)) =
        x ᵥ* (b : Matrix (Fin n) (Fin n) K) := by
  constructor
  · intro hx
    change (fun j => x j ^ (p ^ r)) ᵥ*
      (↑(b⁻¹) : Matrix (Fin n) (Fin n) K) = x at hx
    calc
      (fun j => x j ^ (p ^ r)) =
          (fun j => x j ^ (p ^ r)) ᵥ* (1 : Matrix (Fin n) (Fin n) K) :=
        (Matrix.vecMul_one _).symm
      _ = (fun j => x j ^ (p ^ r)) ᵥ*
          ((↑(b⁻¹) : Matrix (Fin n) (Fin n) K) *
            (b : Matrix (Fin n) (Fin n) K)) := by
        rw [Units.inv_mul]
      _ = ((fun j => x j ^ (p ^ r)) ᵥ*
          (↑(b⁻¹) : Matrix (Fin n) (Fin n) K)) ᵥ*
            (b : Matrix (Fin n) (Fin n) K) :=
        (Matrix.vecMul_vecMul _ _ _).symm
      _ = x ᵥ* (b : Matrix (Fin n) (Fin n) K) := by rw [hx]
  · intro hx
    change (fun j => x j ^ (p ^ r)) ᵥ*
      (↑(b⁻¹) : Matrix (Fin n) (Fin n) K) = x
    calc
      (fun j => x j ^ (p ^ r)) ᵥ*
          (↑(b⁻¹) : Matrix (Fin n) (Fin n) K) =
        (x ᵥ* (b : Matrix (Fin n) (Fin n) K)) ᵥ*
          (↑(b⁻¹) : Matrix (Fin n) (Fin n) K) := by rw [hx]
      _ = x ᵥ* ((b : Matrix (Fin n) (Fin n) K) *
          (↑(b⁻¹) : Matrix (Fin n) (Fin n) K)) :=
        Matrix.vecMul_vecMul _ _ _
      _ = x ᵥ* (1 : Matrix (Fin n) (Fin n) K) := by
        rw [Units.mul_inv]
      _ = x := Matrix.vecMul_one _

end Height.Steenrod
