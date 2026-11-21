import Height.Steenrod.Criterion
import Mathlib.Algebra.Group.Semiconj.Units

/-!
# Algebraic transport behind untwisting (`eq:transport`)

This file proves equation `eq:transport` and its nilpotent-pencil consequence.
Lang surjectivity and the comparison of geometric dimensions remain separate.
-/

namespace Height.Steenrod


open Matrix

universe u v

variable (p r : ℕ) [Fact p.Prime]
variable {K : Type u} [Field K] [ExpChar K p]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]

/-- Nilpotence is invariant under conjugation by a matrix with a specified
two-sided inverse. -/
theorem isNilpotent_conjugate_iff (g h A : Matrix ι ι K)
    (hgh : g * h = 1) (hhg : h * g = 1) :
    IsNilpotent (g * A * h) ↔ IsNilpotent A := by
  let gu : (Matrix ι ι K)ˣ := ⟨g, h, hgh, hhg⟩
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have hconj : g * A ^ k * h = 0 := by
      rw [← show (gu : Matrix ι ι K) = g by rfl,
        ← show (↑gu⁻¹ : Matrix ι ι K) = h by rfl,
        ← gu.conj_pow A k]
      exact hk
    calc
      A ^ k = (h * g) * A ^ k * (h * g) := by rw [hhg]; simp
      _ = h * (g * A ^ k * h) * g := by noncomm_ring
      _ = 0 := by rw [hconj]; simp
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [show g = (gu : Matrix ι ι K) by rfl,
      show h = (↑gu⁻¹ : Matrix ι ι K) by rfl,
      gu.conj_pow, hk]
    simp

omit [Fact (Nat.Prime p)] in
/-- Frobenius of a conjugate is conjugate to the Lang-transformed second
endpoint.  Here `h` is the specified inverse of `g`. -/
theorem frobenius_conjugate_transport (g h N : Matrix ι ι K)
    (hgh : g * h = 1)
    (hN : frobeniusMatrix p r N = N) :
    frobeniusMatrix p r (g * N * h) =
      g * ((h * frobeniusMatrix p r g) * N *
        (frobeniusMatrix p r h * g)) * h := by
  have hmap : frobeniusMatrix p r (g * N * h) =
      frobeniusMatrix p r g * N * frobeniusMatrix p r h := by
    rw [frobeniusMatrix, Matrix.map_mul, Matrix.map_mul, ← frobeniusMatrix,
      ← frobeniusMatrix, ← frobeniusMatrix, hN]
  rw [hmap]
  symm
  calc
    g * ((h * frobeniusMatrix p r g) * N *
        (frobeniusMatrix p r h * g)) * h =
      (g * h) * frobeniusMatrix p r g * N *
        frobeniusMatrix p r h * (g * h) := by noncomm_ring
    _ = frobeniusMatrix p r g * N * frobeniusMatrix p r h := by
      rw [hgh]
      simp

omit [Fact (Nat.Prime p)] in
/-- Equation `eq:transport` for every linear combination in the two
pencils. -/
theorem frobenius_pencil_combination_transport (g h N : Matrix ι ι K)
    (hgh : g * h = 1)
    (hN : frobeniusMatrix p r N = N) (s t : K) :
    s • (g * N * h) + t • frobeniusMatrix p r (g * N * h) =
      g * (s • N + t • ((h * frobeniusMatrix p r g) * N *
        (frobeniusMatrix p r h * g))) * h := by
  rw [frobenius_conjugate_transport p r g h N hgh hN]
  simp [mul_add, add_mul]

omit [Fact (Nat.Prime p)] in
/-- The Frobenius pencil through `gNg⁻¹` consists of nilpotent matrices
exactly when the untwisted pencil through `N` and its Lang-conjugate does. -/
theorem frobenius_pencil_untwist (g h N : Matrix ι ι K)
    (hgh : g * h = 1) (hhg : h * g = 1)
    (hN : frobeniusMatrix p r N = N) :
    (∀ s t : K,
      IsNilpotent (s • (g * N * h) +
        t • frobeniusMatrix p r (g * N * h))) ↔
      ∀ s t : K,
        IsNilpotent (s • N + t • ((h * frobeniusMatrix p r g) * N *
          (frobeniusMatrix p r h * g))) := by
  constructor
  · intro hnil s t
    apply (isNilpotent_conjugate_iff g h _ hgh hhg).mp
    rw [← frobenius_pencil_combination_transport p r g h N hgh hN]
    exact hnil s t
  · intro hnil s t
    rw [frobenius_pencil_combination_transport p r g h N hgh hN]
    exact (isNilpotent_conjugate_iff g h _ hgh hhg).mpr (hnil s t)

end Height.Steenrod
