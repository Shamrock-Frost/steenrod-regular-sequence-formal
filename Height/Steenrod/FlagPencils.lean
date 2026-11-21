import Height.Steenrod.Partner
import Height.Toolbox.Flags
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# Nilpotent pencils carried by a complete flag (`defn:flagless`)

This implements `defn:flagless` without introducing a flag variety.  Over a
field a complete flag is a change of basis of the standard flag, so a pencil
is *triangularizable* exactly when one change of basis puts both endpoints in
the standard nilradical `𝔫`, and *flagless* otherwise.

The linear-algebra model of `𝔫_F` and `𝔟_F` is `Height/Toolbox/Flags.lean`;
this file adds the facts about that model that mention nilpotence and
`NilpotentPencil`, so that `Height/Toolbox` depends on nothing in
`Height/Steenrod`.
-/

namespace Height.Steenrod

open Height.Toolbox

universe u

variable (K : Type u) [Field K] (n : ℕ)

/-- Every matrix in the standard nilradical is nilpotent. -/
theorem isNilpotent_of_mem_standardNilradical
    {M : Matrix (Fin n) (Fin n) K}
    (hM : M ∈ standardNilradical K n) : IsNilpotent M := by
  rw [matrix_isNilpotent_iff_charpoly,
    Matrix.charpoly_of_isUpperTriangular M
      (isUpperTriangular_of_mem_standardNilradical K n hM)]
  have hdiag (i : Fin n) : M i i = 0 := hM i i le_rfl
  simp_rw [hdiag]
  simp

/-- Two matrices lowering the same standard flag span a nilpotent pencil. -/
theorem nilpotentPencil_of_mem_standardNilradical
    {A B : Matrix (Fin n) (Fin n) K}
    (hA : A ∈ standardNilradical K n)
    (hB : B ∈ standardNilradical K n) : NilpotentPencil A B := by
  intro s t
  exact isNilpotent_of_mem_standardNilradical K n
    (Submodule.add_mem _ (Submodule.smul_mem _ s hA)
      (Submodule.smul_mem _ t hB))

/-- A simultaneous conjugate of two standard-nilradical matrices still
spans a nilpotent pencil. -/
theorem nilpotentPencil_conjugate_of_mem_standardNilradical
    (g : (Matrix (Fin n) (Fin n) K)ˣ)
    {A B : Matrix (Fin n) (Fin n) K}
    (hA : A ∈ standardNilradical K n)
    (hB : B ∈ standardNilradical K n) :
    NilpotentPencil
      ((g : Matrix (Fin n) (Fin n) K) * A *
        (↑(g⁻¹) : Matrix (Fin n) (Fin n) K))
      ((g : Matrix (Fin n) (Fin n) K) * B *
        (↑(g⁻¹) : Matrix (Fin n) (Fin n) K)) := by
  exact (nilpotentPencil_conjugate_iff
    (g : Matrix (Fin n) (Fin n) K)
    (↑(g⁻¹) : Matrix (Fin n) (Fin n) K) A B (by simp) (by simp)).2
      (nilpotentPencil_of_mem_standardNilradical K n hA hB)

/-- A pair of matrices is simultaneously strictly upper triangular after one
change of basis. -/
def TriangularizablePencil
    (A B : Matrix (Fin n) (Fin n) K) : Prop :=
  ∃ g : (Matrix (Fin n) (Fin n) K)ˣ,
    (↑(g⁻¹) : Matrix (Fin n) (Fin n) K) * A *
        (g : Matrix (Fin n) (Fin n) K) ∈ standardNilradical K n ∧
    (↑(g⁻¹) : Matrix (Fin n) (Fin n) K) * B *
        (g : Matrix (Fin n) (Fin n) K) ∈ standardNilradical K n

/-- A flagless pencil is a nilpotent pencil that is not simultaneously
triangularizable. -/
def FlaglessPencil (A B : Matrix (Fin n) (Fin n) K) : Prop :=
  NilpotentPencil A B ∧ ¬TriangularizablePencil K n A B

/-- Every triangularizable pencil is a nilpotent pencil. -/
theorem TriangularizablePencil.nilpotentPencil
    {A B : Matrix (Fin n) (Fin n) K}
    (h : TriangularizablePencil K n A B) : NilpotentPencil A B := by
  obtain ⟨g, hA, hB⟩ := h
  have hP := nilpotentPencil_conjugate_of_mem_standardNilradical K n g hA hB
  simpa [mul_assoc] using hP

/-- Simultaneous triangularizability means precisely that both endpoints lie
in one conjugate of the standard nilradical. -/
theorem triangularizablePencil_iff_mem_conjugateNilradical
    (A B : Matrix (Fin n) (Fin n) K) :
    TriangularizablePencil K n A B ↔
      ∃ g : (Matrix (Fin n) (Fin n) K)ˣ,
        A ∈ conjugateNilradical K n g ∧
          B ∈ conjugateNilradical K n g := by
  simp only [TriangularizablePencil, mem_conjugateNilradical_iff]

end Height.Steenrod
