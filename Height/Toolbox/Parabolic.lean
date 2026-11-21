import Isotropy.FieldLemma

/-!
# The parabolic attached to a nilpotent kernel flag (`lem:parabolic-field`)

This is `lem:parabolic-field`.  The hard surjectivity statement is supplied by
the trace-duality theorem `Isotropy.exists_commutator_of_lowering`.
-/

namespace Height.Toolbox

open Matrix

variable {K : Type*} [Field K] {n : ℕ}

/-- Endomorphisms carrying each `S k` into `T k`.  The parabolic and its nilradical are
this one set for two choices of source flag, and `Pencil.flagHomSubmodule` is the module
structure they share. -/
def flagHom (S T : ℕ → Submodule K (Fin n → K)) : Set (Matrix (Fin n) (Fin n) K) :=
  {A | ∀ k, ∀ v ∈ S k, A.mulVec v ∈ T k}

/-- Endomorphisms preserving every member of the kernel flag of `P`. -/
def kernelFlagParabolic (P : Matrix (Fin n) (Fin n) K) :
    Set (Matrix (Fin n) (Fin n) K) :=
  flagHom (Isotropy.kerFlag P) (Isotropy.kerFlag P)

/-- Endomorphisms strictly lowering the kernel flag of `P`. -/
def kernelFlagNilradical (P : Matrix (Fin n) (Fin n) K) :
    Set (Matrix (Fin n) (Fin n) K) :=
  flagHom (fun k => Isotropy.kerFlag P (k + 1)) (Isotropy.kerFlag P)

/-- The matrix centralizer of `P`, viewed as a set. -/
def matrixCentralizer (P : Matrix (Fin n) (Fin n) K) :
    Set (Matrix (Fin n) (Fin n) K) :=
  {A | P * A = A * P}

/-- The commutator map in the sign convention of the source. -/
def adMatrix (P A : Matrix (Fin n) (Fin n) K) :
    Matrix (Fin n) (Fin n) K := P * A - A * P

/-- A commutator with `P` lowers its kernel flag whenever its second argument
preserves that flag. -/
theorem adMatrix_mem_nilradical_of_mem_parabolic
    (P A : Matrix (Fin n) (Fin n) K) (hA : A ∈ kernelFlagParabolic P) :
    adMatrix P A ∈ kernelFlagNilradical P := by
  intro k v hv
  rw [adMatrix, sub_mulVec, ← mulVec_mulVec, ← mulVec_mulVec]
  exact Submodule.sub_mem _
    (Isotropy.mulVec_mem_kerFlag (hA (k + 1) v hv))
    (hA k _ (Isotropy.mulVec_mem_kerFlag hv))

/-- Conversely, if `[P,A]` lowers the kernel flag then `A` preserves it. -/
theorem mem_parabolic_of_adMatrix_mem_nilradical
    (P A : Matrix (Fin n) (Fin n) K)
    (hA : adMatrix P A ∈ kernelFlagNilradical P) :
    A ∈ kernelFlagParabolic P := by
  intro k
  induction k with
  | zero =>
      intro v hv
      rw [Isotropy.kerFlag_zero, Submodule.mem_bot] at hv ⊢
      simp [hv]
  | succ k ih =>
      intro v hv
      have hPv : P.mulVec v ∈ Isotropy.kerFlag P k :=
        Isotropy.mulVec_mem_kerFlag hv
      have hAPv := ih _ hPv
      have hcommv :
          P.mulVec (A.mulVec v) =
            A.mulVec (P.mulVec v) + (adMatrix P A).mulVec v := by
        calc
          P.mulVec (A.mulVec v) = (P * A).mulVec v := by rw [mulVec_mulVec]
          _ = (A * P).mulVec v + (adMatrix P A).mulVec v := by
            simp only [adMatrix, sub_mulVec]
            abel
          _ = A.mulVec (P.mulVec v) + (adMatrix P A).mulVec v := by
            rw [mulVec_mulVec]
      rw [Isotropy.mem_kerFlag] at hAPv ⊢
      have hQv := hA k v hv
      rw [Isotropy.mem_kerFlag] at hQv
      rw [pow_succ]
      repeat rw [← mulVec_mulVec]
      rw [hcommv, mulVec_add, hAPv, hQv, add_zero]

/-- Every matrix commuting with `P` preserves its kernel flag. -/
theorem matrixCentralizer_subset_parabolic (P : Matrix (Fin n) (Fin n) K) :
    matrixCentralizer P ⊆ kernelFlagParabolic P := by
  intro A hA k v hv
  rw [Isotropy.mem_kerFlag] at hv ⊢
  rw [mulVec_mulVec, (Commute.pow_left hA k), ← mulVec_mulVec, hv, mulVec_zero]

/-- `lem:parabolic-field`: commutators lower the kernel flag exactly for
parabolic arguments; the centralizer is parabolic; every lowering map is such
a commutator; and the parabolic and lowering spaces are trace-orthogonal. -/
theorem parabolic_field (P : Matrix (Fin n) (Fin n) K) (hP : P ^ n = 0) :
    (∀ A, adMatrix P A ∈ kernelFlagNilradical P ↔
      A ∈ kernelFlagParabolic P) ∧
    matrixCentralizer P ⊆ kernelFlagParabolic P ∧
    adMatrix P '' kernelFlagParabolic P = kernelFlagNilradical P ∧
    ∀ A ∈ kernelFlagParabolic P, ∀ Q ∈ kernelFlagNilradical P,
      trace (A * Q) = 0 := by
  refine ⟨fun A => ⟨mem_parabolic_of_adMatrix_mem_nilradical P A,
      adMatrix_mem_nilradical_of_mem_parabolic P A⟩,
    matrixCentralizer_subset_parabolic P, ?_, ?_⟩
  · ext Q
    constructor
    · rintro ⟨A, hA, rfl⟩
      exact adMatrix_mem_nilradical_of_mem_parabolic P A hA
    · intro hQ
      obtain ⟨A, hA⟩ := Isotropy.exists_commutator_of_lowering P hP Q hQ
      refine ⟨A, ?_, hA⟩
      apply mem_parabolic_of_adMatrix_mem_nilradical P A
      rwa [adMatrix, hA]
  · intro A hA Q hQ
    rw [trace_mul_comm]
    exact Isotropy.trace_eq_zero_of_lowering P hP (Q * A)
      (Isotropy.lowering_mul_preserving hQ hA)

end Height.Toolbox
