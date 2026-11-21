import Mathlib.Data.Fin.Rev
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Dimension.Constructions
import Height.Toolbox.Isotropic

/-!
# Residue pairings on the elementary torsion blocks

After the alternating matrix is put into hyperbolic normal form, the local
pairings in `lem:residue-form` and `lem:divided-form` reduce to the explicit
finite coefficient calculations proved here.
-/

namespace Height.DVR

universe u

variable {K : Type u} [Field K]

/-- Coefficient vectors for `K[u]/(u^m)`. -/
abbrev TruncatedCoeffs (K : Type u) (m : ℕ) := Fin m → K

/-- The coefficient of `u^(m-1)` in the product of two truncated
polynomials. -/
def residueCoeffPair (m : ℕ) (a b : TruncatedCoeffs K m) : K :=
  ∑ i, a i * b (Fin.rev i)

theorem residueCoeffPair_add_left (m : ℕ)
    (a b c : TruncatedCoeffs K m) :
    residueCoeffPair m (a + b) c =
      residueCoeffPair m a c + residueCoeffPair m b c := by
  simp [residueCoeffPair, add_mul, Finset.sum_add_distrib]

theorem residueCoeffPair_smul_left (m : ℕ) (r : K)
    (a b : TruncatedCoeffs K m) :
    residueCoeffPair m (r • a) b = r • residueCoeffPair m a b := by
  simp [residueCoeffPair, Finset.mul_sum, mul_assoc]

theorem residueCoeffPair_add_right (m : ℕ)
    (a b c : TruncatedCoeffs K m) :
    residueCoeffPair m a (b + c) =
      residueCoeffPair m a b + residueCoeffPair m a c := by
  simp [residueCoeffPair, mul_add, Finset.sum_add_distrib]

theorem residueCoeffPair_smul_right (m : ℕ) (r : K)
    (a b : TruncatedCoeffs K m) :
    residueCoeffPair m a (r • b) = r • residueCoeffPair m a b := by
  simp [residueCoeffPair, Finset.mul_sum, mul_left_comm]

@[simp] theorem residueCoeffPair_single_right (m : ℕ)
    (a : TruncatedCoeffs K m) (i : Fin m) :
    residueCoeffPair m a (Pi.single (Fin.rev i) 1) = a i := by
  simp [residueCoeffPair, Pi.single_apply, Fin.rev_injective.eq_iff]

@[simp] theorem residueCoeffPair_single_left (m : ℕ)
    (a : TruncatedCoeffs K m) (i : Fin m) :
    residueCoeffPair m (Pi.single (Fin.rev i) 1) a = a i := by
  simp [residueCoeffPair, Pi.single_apply]

/-- The coefficient pairing is perfect in its left argument. -/
theorem residueCoeffPair_nondegenerate_left (m : ℕ)
    (a : TruncatedCoeffs K m)
    (h : ∀ b, residueCoeffPair m a b = 0) : a = 0 := by
  funext i
  simpa using h (Pi.single (Fin.rev i) 1)

/-- The coefficient pairing is perfect in its right argument. -/
theorem residueCoeffPair_nondegenerate_right (m : ℕ)
    (b : TruncatedCoeffs K m)
    (h : ∀ a, residueCoeffPair m a b = 0) : b = 0 := by
  funext i
  simpa using h (Pi.single (Fin.rev i) 1)

/-- The hyperbolic residue block on `(K[u]/u^m)^2`. -/
def residueBlockForm (m : ℕ)
    (x y : TruncatedCoeffs K m × TruncatedCoeffs K m) : K :=
  residueCoeffPair m x.1 y.2 - residueCoeffPair m y.1 x.2

/-- The hyperbolic residue block as a bundled bilinear form. -/
def residueBlockBilinForm (m : ℕ) : LinearMap.BilinForm K
    (TruncatedCoeffs K m × TruncatedCoeffs K m) :=
  LinearMap.mk₂ K (residueBlockForm m)
    (by
      intro x z y
      simp [residueBlockForm, residueCoeffPair_add_left,
        residueCoeffPair_add_right]
      ring)
    (by
      intro r x y
      simp [residueBlockForm, residueCoeffPair_smul_left,
        residueCoeffPair_smul_right]
      ring)
    (by
      intro x y z
      simp [residueBlockForm, residueCoeffPair_add_left,
        residueCoeffPair_add_right]
      ring)
    (by
      intro r x y
      simp [residueBlockForm, residueCoeffPair_smul_left,
        residueCoeffPair_smul_right]
      ring)

@[simp] theorem residueBlockBilinForm_apply (m : ℕ)
    (x y : TruncatedCoeffs K m × TruncatedCoeffs K m) :
    residueBlockBilinForm m x y = residueBlockForm m x y := rfl

@[simp] theorem residueBlockForm_self (m : ℕ)
    (x : TruncatedCoeffs K m × TruncatedCoeffs K m) :
    residueBlockForm m x x = 0 := by
  simp [residueBlockForm]

/-- `lem:residue-form` on one elementary hyperbolic block: the residue form
is alternating and nondegenerate. -/
theorem residueBlock_nondegenerate (m : ℕ) :
    (∀ x : TruncatedCoeffs K m × TruncatedCoeffs K m,
        residueBlockForm m x x = 0) ∧
      ∀ x : TruncatedCoeffs K m × TruncatedCoeffs K m,
        (∀ y, residueBlockForm m x y = 0) → x = 0 := by
  refine ⟨residueBlockForm_self m, ?_⟩
  rintro ⟨a, b⟩ h
  have ha : a = 0 := residueCoeffPair_nondegenerate_left m a fun z => by
    simpa [residueBlockForm, residueCoeffPair] using h (0, z)
  have hb : b = 0 := residueCoeffPair_nondegenerate_right m b fun z => by
    have hz := h (z, 0)
    have hz' : -residueCoeffPair m z b = 0 := by
      simpa [residueBlockForm, residueCoeffPair] using hz
    exact neg_eq_zero.mp hz'
  simp [ha, hb]

end Height.DVR
