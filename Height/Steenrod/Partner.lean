import Height.Steenrod.Frobenius
import Height.Steenrod.Untwist

/-!
# Nilpotent pencils and partner matrices (`defn:partner`)

This packages the set-theoretic content of the partner variety from
`defn:partner`.  No algebraic-geometric structure is imposed: the predicate
records exactly that every member of the two-dimensional span is nilpotent.
-/

namespace Height.Steenrod

universe u v

variable {K : Type u} [Field K]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]

/-- Two matrices span a nilpotent pencil when every one of their linear
combinations is nilpotent. -/
def NilpotentPencil (A B : Matrix ι ι K) : Prop :=
  ∀ s t : K, IsNilpotent (s • A + t • B)

theorem nilpotentPencil_comm (A B : Matrix ι ι K) :
    NilpotentPencil A B ↔ NilpotentPencil B A := by
  constructor <;> intro h s t
  · simpa [add_comm] using h t s
  · simpa [add_comm] using h t s

/-- Replacing both endpoints by arbitrary linear combinations preserves the
nilpotent-pencil condition. -/
theorem NilpotentPencil.linearCombination {A B : Matrix ι ι K}
    (h : NilpotentPencil A B) (a b c d : K) :
    NilpotentPencil (a • A + b • B) (c • A + d • B) := by
  intro s t
  convert h (s * a + t * c) (s * b + t * d) using 1
  ext i j
  simp
  ring

/-- Simultaneous conjugation by an invertible matrix preserves and reflects
the nilpotent-pencil condition. -/
theorem nilpotentPencil_conjugate_iff (g h A B : Matrix ι ι K)
    (hgh : g * h = 1) (hhg : h * g = 1) :
    NilpotentPencil (g * A * h) (g * B * h) ↔
      NilpotentPencil A B := by
  constructor
  · intro hP s t
    apply (isNilpotent_conjugate_iff g h _ hgh hhg).mp
    simpa [mul_add, add_mul] using hP s t
  · intro hP s t
    rw [show s • (g * A * h) + t • (g * B * h) =
      g * (s • A + t • B) * h by simp [mul_add, add_mul]]
    exact (isNilpotent_conjugate_iff g h _ hgh hhg).mpr (hP s t)

section Frobenius

variable (p r : ℕ) [Fact p.Prime]
variable [ExpChar K p]

section Steenrod

variable [Algebra (GaloisField p r) K] [Infinite K]

/-- The exact list of Steenrod generators vanishes at `M` iff its Frobenius
image is a nilpotent partner. -/
theorem powerCharacteristicCoefficientsVanishAt_iff_partner [NeZero r]
    {N : ℕ} (M : Matrix (Fin N) (Fin N) K) :
    powerCharacteristicCoefficientsVanishAt p r M ↔
      NilpotentPencil M (frobeniusMatrix p r M) := by
  exact powerCharacteristicCoefficients_pencil_criterion p r M

end Steenrod

end Frobenius

end Height.Steenrod
