import Height.Steenrod.Evaluation
import Height.Steenrod.Charpoly
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Entrywise Frobenius and nilpotent pencils (`lem:pencil`)

This proves the second equivalence in `lem:pencil`: a Frobenius line consists
of nilpotent matrices exactly when its two-dimensional linear span does.
-/

namespace Height.Steenrod


open Matrix

universe u

variable (p r : ℕ) [Fact p.Prime]
variable {K : Type u} [Field K] [ExpChar K p]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Entrywise `q = p^r` Frobenius on matrices. -/
def frobeniusMatrix (M : Matrix ι ι K) : Matrix ι ι K :=
  M.map (iterateFrobenius K p r)

omit [Fact (Nat.Prime p)] [Fintype ι] [DecidableEq ι] in
@[simp] theorem frobeniusMatrix_apply (M : Matrix ι ι K) (i j : ι) :
    frobeniusMatrix p r M i j = M i j ^ p ^ r := rfl

section Steenrod

variable [Algebra (GaloisField p r) K]

/-- Simultaneous vanishing at `M` of every Steenrod power of every non-leading
signed characteristic coefficient. -/
def steenrodCharacteristicCoefficientsVanish {N : ℕ}
    (M : Matrix (Fin N) (Fin N) K) : Prop :=
  ∀ j, 1 ≤ j → j ≤ N → ∀ i,
    MvPolynomial.aeval (fun ij : Fin N × Fin N => M ij.1 ij.2)
      (QSteenrod.P p r i (QSteenrod.c p r N j)) = 0

/-- Vanishing of precisely the strict lower-triangle family `P^i(c_j)`, with
`0 ≤ i < j ≤ N`. -/
def steenrodTriangleVanish {N : ℕ}
    (M : Matrix (Fin N) (Fin N) K) : Prop :=
  ∀ j, 1 ≤ j → j ≤ N → ∀ i, i < j →
    MvPolynomial.aeval (fun ij : Fin N × Fin N => M ij.1 ij.2)
      (QSteenrod.P p r i (QSteenrod.c p r N j)) = 0

/-- Vanishing at `M` of the fixed ordered list used in the regular-sequence
statement. -/
def powerCharacteristicCoefficientsVanishAt {N : ℕ}
    (M : Matrix (Fin N) (Fin N) K) : Prop :=
  ∀ f ∈ QSteenrod.powerCharacteristicCoefficients p r N,
    MvPolynomial.aeval (fun ij : Fin N × Fin N => M ij.1 ij.2) f = 0

omit [ExpChar K p] in
/-- Membership in the ordered coefficient list is exactly strict-triangle
indexing, so list vanishing agrees with `steenrodTriangleVanish`. -/
theorem powerCharacteristicCoefficientsVanishAt_iff {N : ℕ}
    (M : Matrix (Fin N) (Fin N) K) :
    powerCharacteristicCoefficientsVanishAt p r M ↔
      steenrodTriangleVanish p r M := by
  constructor
  · intro h j hj1 hjN i hij
    exact h _ (List.mem_map.mpr ⟨(i, j),
      (QSteenrod.mem_strictLowerTriangleIndices_iff N i j).mpr ⟨hj1, hjN, hij⟩, rfl⟩)
  · intro h f hf
    simp only [QSteenrod.powerCharacteristicCoefficients, List.mem_map] at hf
    obtain ⟨ij, hij, rfl⟩ := hf
    obtain ⟨hj1, hjN, hi⟩ :=
      (QSteenrod.mem_strictLowerTriangleIndices_iff N ij.1 ij.2).mp hij
    exact h ij.2 hj1 hjN ij.1 hi

private theorem eval_substitution {N : ℕ}
    (M : Matrix (Fin N) (Fin N) K) (f : QSteenrod.GenericMatrixRing p r N)
    (t : K) :
    (MvPolynomial.aeval
      (fun ij : Fin N × Fin N => Polynomial.C (M ij.1 ij.2) +
        Polynomial.monomial 1 (M ij.1 ij.2 ^ QSteenrod.q p r)) f).eval t =
      MvPolynomial.aeval
        (fun ij => (M + t • frobeniusMatrix p r M) ij.1 ij.2) f := by
  let ev : Polynomial K →ₐ[GaloisField p r] K :=
    { Polynomial.evalRingHom t with
      commutes' := fun x => by simp }
  let lhs : QSteenrod.GenericMatrixRing p r N →ₐ[GaloisField p r] K :=
    ev.comp (MvPolynomial.aeval fun ij : Fin N × Fin N =>
      Polynomial.C (M ij.1 ij.2) +
        Polynomial.monomial 1 (M ij.1 ij.2 ^ QSteenrod.q p r))
  let rhs : QSteenrod.GenericMatrixRing p r N →ₐ[GaloisField p r] K :=
    MvPolynomial.aeval fun ij : Fin N × Fin N =>
      (M + t • frobeniusMatrix p r M) ij.1 ij.2
  have h : lhs = rhs := MvPolynomial.algHom_ext fun ij => by
    simp [lhs, rhs, ev, frobeniusMatrix_apply, QSteenrod.q, mul_comm]
  exact DFunLike.congr_fun h f

/-- Evaluating the characteristic coefficient of the polynomial pencil at
`t` gives the corresponding signed coefficient of `M + t Fr(M)`. -/
theorem eval_pencilCharacteristicCoefficient {N : ℕ}
    (M : Matrix (Fin N) (Fin N) K) (j : ℕ) (t : K) :
    (MvPolynomial.aeval
      (fun ij : Fin N × Fin N => Polynomial.C (M ij.1 ij.2) +
        Polynomial.monomial 1 (M ij.1 ij.2 ^ QSteenrod.q p r))
      (QSteenrod.c p r N j)).eval t =
      (-1 : K) ^ j *
        (M + t • frobeniusMatrix p r M).charpoly.coeff (N - j) := by
  rw [eval_substitution]
  exact eval_characteristicCoefficient p r N _ j

end Steenrod

omit [Fact (Nat.Prime p)] in
/-- Entrywise Frobenius preserves nilpotence because it is a ring
endomorphism of the matrix ring. -/
theorem frobeniusMatrix_isNilpotent {M : Matrix ι ι K} (hM : IsNilpotent M) :
    IsNilpotent (frobeniusMatrix p r M) := by
  exact hM.map (iterateFrobenius K p r).mapMatrix

private theorem nilpotent_line_iff_span (M N : Matrix ι ι K)
    (hN : IsNilpotent N) :
    (∀ t : K, IsNilpotent (M + t • N)) ↔
      ∀ s t : K, IsNilpotent (s • M + t • N) := by
  constructor
  · intro hline s t
    by_cases hs : s = 0
    · simpa [hs] using hN.smul t
    · have h := (hline (t / s)).smul s
      have hst : s * (t / s) = t := by field_simp
      simpa [smul_add, smul_smul, hst] using h
  · intro hspan t
    simpa using hspan 1 t

omit [Fact (Nat.Prime p)] in
/-- `lem:pencil`, line-versus-span form.  The nilpotence of `M` follows by
taking `t=0`, and entrywise Frobenius then supplies the other endpoint. -/
theorem pencil_criterion (M : Matrix ι ι K) :
    (∀ t : K, IsNilpotent (M + t • frobeniusMatrix p r M)) ↔
      ∀ s t : K, IsNilpotent (s • M + t • frobeniusMatrix p r M) := by
  constructor
  · intro hline
    have hM : IsNilpotent M := by simpa using hline 0
    exact (nilpotent_line_iff_span M (frobeniusMatrix p r M)
      (frobeniusMatrix_isNilpotent p r hM)).mp hline
  · intro hspan t
    simpa using hspan 1 t

section Steenrod

variable [Algebra (GaloisField p r) K] [Infinite K]

omit [ExpChar K p] [Infinite K] in
/-- The triangular generators vanish exactly when all Steenrod powers of the
non-leading characteristic coefficients vanish. -/
theorem steenrodTriangleVanish_iff_all [NeZero r] {N : ℕ}
    (M : Matrix (Fin N) (Fin N) K) :
    steenrodTriangleVanish p r M ↔
      steenrodCharacteristicCoefficientsVanish p r M := by
  constructor
  · intro h j hj1 hjN i
    rcases lt_trichotomy i j with hij | hij | hji
    · exact h j hj1 hjN i hij
    · subst i
      rw [P_top_eq_pow_of_isHomogeneous p r
        (characteristicCoefficient_isHomogeneous p r N j hjN)]
      have h0 := h j hj1 hjN 0 hj1
      rw [P_zero] at h0
      have hq : QSteenrod.q p r ≠ 0 :=
        pow_ne_zero _ (Fact.out : Nat.Prime p).ne_zero
      rw [map_pow, h0]
      exact zero_pow hq
    · rw [P_eq_zero_of_isHomogeneous p r
        (characteristicCoefficient_isHomogeneous p r N j hjN) hji]
      simp
  · intro h j hj1 hjN i hij
    exact h j hj1 hjN i

/-- The first equivalence in `lem:pencil`, in the exact all-Steenrod-powers
form: all characteristic Steenrod coefficients vanish at `M` exactly when the
Frobenius line through `M` consists of nilpotent matrices. -/
theorem steenrodCharacteristicCoefficientsVanish_iff_nilpotentLine {N : ℕ}
    (M : Matrix (Fin N) (Fin N) K) :
    steenrodCharacteristicCoefficientsVanish p r M ↔
      ∀ t : K, IsNilpotent (M + t • frobeniusMatrix p r M) := by
  constructor
  · intro h t
    rw [← characteristicCoefficientsVanish_iff p r N]
    intro j hj1 hjN
    let g : Polynomial K :=
      MvPolynomial.aeval
        (fun ij : Fin N × Fin N => Polynomial.C (M ij.1 ij.2) +
          Polynomial.monomial 1 (M ij.1 ij.2 ^ QSteenrod.q p r))
        (QSteenrod.c p r N j)
    have hg : g = 0 := by
      ext i
      rw [← evaluation_coeff p r (fun ij : Fin N × Fin N => M ij.1 ij.2)
        (QSteenrod.c p r N j) i]
      exact h j hj1 hjN i
    have ht := congrArg (fun f : Polynomial K => f.eval t) hg
    rw [show g.eval t =
      (-1 : K) ^ j *
        (M + t • frobeniusMatrix p r M).charpoly.coeff (N - j) by
          exact eval_pencilCharacteristicCoefficient p r M j t] at ht
    rw [eval_characteristicCoefficient]
    simpa using ht
  · intro h j hj1 hjN i
    let g : Polynomial K :=
      MvPolynomial.aeval
        (fun ij : Fin N × Fin N => Polynomial.C (M ij.1 ij.2) +
          Polynomial.monomial 1 (M ij.1 ij.2 ^ QSteenrod.q p r))
        (QSteenrod.c p r N j)
    have hg : g = 0 := Polynomial.zero_of_eval_zero g fun t => by
      rw [show g.eval t =
        (-1 : K) ^ j *
          (M + t • frobeniusMatrix p r M).charpoly.coeff (N - j) by
            exact eval_pencilCharacteristicCoefficient p r M j t]
      have hc :=
        (characteristicCoefficientsVanish_iff p r N
          (M + t • frobeniusMatrix p r M)).mpr (h t) j hj1 hjN
      rwa [eval_characteristicCoefficient] at hc
    rw [evaluation_coeff p r (fun ij : Fin N × Fin N => M ij.1 ij.2)
      (QSteenrod.c p r N j) i]
    change g.coeff i = 0
    rw [hg]
    simp

/-- `lem:pencil` after adjoining the line-versus-span equivalence. -/
theorem steenrod_pencil_criterion {N : ℕ}
    (M : Matrix (Fin N) (Fin N) K) :
    steenrodCharacteristicCoefficientsVanish p r M ↔
      ∀ s t : K, IsNilpotent (s • M + t • frobeniusMatrix p r M) := by
  rw [steenrodCharacteristicCoefficientsVanish_iff_nilpotentLine]
  exact pencil_criterion p r M

/-- `lem:pencil` for exactly the triangular generator family defining `J`. -/
theorem triangle_pencil_criterion [NeZero r] {N : ℕ}
    (M : Matrix (Fin N) (Fin N) K) :
    steenrodTriangleVanish p r M ↔
      ∀ s t : K, IsNilpotent (s • M + t • frobeniusMatrix p r M) := by
  rw [steenrodTriangleVanish_iff_all, steenrod_pencil_criterion]

/-- `lem:pencil` stated directly for the fixed ordered list occurring in
the regular-sequence theorem. -/
theorem powerCharacteristicCoefficients_pencil_criterion [NeZero r] {N : ℕ}
    (M : Matrix (Fin N) (Fin N) K) :
    powerCharacteristicCoefficientsVanishAt p r M ↔
      ∀ s t : K, IsNilpotent (s • M + t • frobeniusMatrix p r M) := by
  rw [powerCharacteristicCoefficientsVanishAt_iff,
    triangle_pencil_criterion]

end Steenrod

end Height.Steenrod
