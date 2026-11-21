import Height.Steenrod.Lang.Descent

/-!
# `thm:lang`: Lang surjectivity of the matrix Lang map

`thm:lang` is proved here by Lang–Steinberg descent
(`Height/Steenrod/Lang/Descent.lean`), not by counting: the row map is
injective because `b` is invertible and Frobenius is injective on a field, so
`exists_fixed_basis` produces `n` independent fixed rows, which
`exists_matrixLang_eq_of_fixed_row_basis` assembles into a Lang preimage of `b`.

The counting statement -- the fixed rows number exactly `q^n` -- is a
corollary of surjectivity rather than an input to it.  Nothing uses it, and it
is not proved here.
-/

namespace Height.Steenrod

open scoped Matrix

universe u

variable (p r n : ℕ) [Fact p.Prime]
variable {K : Type u} [Field K] [ExpChar K p] [NeZero r] [IsAlgClosed K]

omit [NeZero r] [IsAlgClosed K] in
/-- The row map `x ↦ Fr(x) b⁻¹` is injective: `Fr` is injective on a field of
exponential characteristic `p` and `b⁻¹` is invertible. -/
theorem langFixedRowMap_injective (b : (Matrix (Fin n) (Fin n) K)ˣ) :
    Function.Injective (langFixedRowMap p r n b) := by
  intro x y hxy
  have hb : ∀ z : Fin n → K,
      ((fun j => z j ^ (p ^ r)) ᵥ* (↑(b⁻¹) : Matrix (Fin n) (Fin n) K)) ᵥ*
          (b : Matrix (Fin n) (Fin n) K) = fun j => z j ^ (p ^ r) := by
    intro z
    rw [Matrix.vecMul_vecMul, Units.inv_mul, Matrix.vecMul_one]
  have hfr : (fun j => x j ^ (p ^ r)) = fun j => y j ^ (p ^ r) := by
    rw [← hb x, ← hb y]
    exact congrArg (fun z => z ᵥ* (b : Matrix (Fin n) (Fin n) K)) hxy
  funext j
  have hj : iterateFrobenius K p r (x j) = iterateFrobenius K p r (y j) := by
    simpa only [iterateFrobenius_def] using congrFun hfr j
  exact (iterateFrobenius K p r).injective hj

/-- Lang solvability for a single target, by Lang–Steinberg descent: the fixed
rows of `x ↦ Fr(x) b⁻¹` contain a `K`-basis of `K^n`. -/
theorem exists_matrixLang_eq (b : (Matrix (Fin n) (Fin n) K)ˣ) :
    ∃ g : (Matrix (Fin n) (Fin n) K)ˣ, matrixLang p r g = b := by
  obtain ⟨v, hv, hfixed⟩ :=
    exists_fixed_basis (K := K) (V := Fin n → K) p r
      (langFixedRowMap p r n b) (langFixedRowMap_smul p r n b)
      (langFixedRowMap_injective p r n b)
  let e : Fin n ≃ Fin (Module.finrank K (Fin n → K)) :=
    finCongr (Module.finrank_fin_fun K).symm
  refine exists_matrixLang_eq_of_fixed_row_basis p r b (v ∘ e)
    (hv.comp e e.injective) ?_
  intro i j
  have hrow := (langFixedRowMap_fixed_iff p r n b (v (e i))).mp (hfixed (e i))
  simpa only [Function.comp_apply, Matrix.vecMul_apply_eq_sum] using congrFun hrow j

/-- `thm:lang`: surjectivity of the matrix Lang map on `GL_n(K)`. -/
theorem matrixLang_surjective :
    Function.Surjective (matrixLang (K := K) (ι := Fin n) p r) :=
  fun b => exists_matrixLang_eq p r n b

end Height.Steenrod
