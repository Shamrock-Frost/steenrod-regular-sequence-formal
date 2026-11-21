import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The matrix of `ad_P`

For a square matrix `P` over a commutative ring, `ad_P : A ↦ P A − A P` is a
linear endomorphism of `gl_n`.  `adEntry P` is its matrix in the standard basis
indexed by `Fin n × Fin n`, and `adMat P` the same matrix reindexed by
`Fin (n * n)` through `glIdx`; `vecOf`/`vecMat` are the corresponding
coordinate vectors of a matrix, so that `adMat P *ᵥ vecMat Q = vecMat (P Q − Q P)`
(`adMat_mulVec`).  `adMat` commutes with base change (`adMat_map`).  The
centraliser of `P` is the kernel of `adMat P` (`Toolbox/CentralizerDim.lean`),
and the pencil program applies `adMat` to pencils over `B`, `K⟦u⟧`, and their
fraction fields.
-/

namespace Height.Toolbox

open Matrix

/-! ### The matrix of `ad_P` -/

section AdMat

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The matrix of `ad_P : A ↦ P A − A P` on `gl_n`, in the standard basis
indexed by `Fin n × Fin n`. -/
def adEntry (P : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin n × Fin n) (Fin n × Fin n) R :=
  Matrix.of fun x y =>
    (if x.2 = y.2 then P x.1 y.1 else 0) - (if x.1 = y.1 then P y.2 x.2 else 0)

theorem adEntry_apply (P : Matrix (Fin n) (Fin n) R) (a b c d : Fin n) :
    adEntry P (a, b) (c, d) = (if b = d then P a c else 0) - (if a = c then P d b else 0) :=
  rfl

/-- Coordinates of a matrix, as a vector indexed by `Fin n × Fin n`. -/
def vecOf (Q : Matrix (Fin n) (Fin n) R) : Fin n × Fin n → R := fun x => Q x.1 x.2

theorem adEntry_mulVec (P Q : Matrix (Fin n) (Fin n) R) :
    adEntry P *ᵥ vecOf Q = vecOf (P * Q - Q * P) := by
  funext x
  obtain ⟨i, j⟩ := x
  have hlhs : (adEntry P *ᵥ vecOf Q) (i, j)
      = ∑ y : Fin n × Fin n, adEntry P (i, j) y * vecOf Q y := rfl
  rw [hlhs, Fintype.sum_prod_type]
  have hstep : ∀ k l : Fin n, adEntry P (i, j) (k, l) * vecOf Q (k, l)
      = (if j = l then P i k * Q k l else 0) - (if i = k then Q k l * P l j else 0) := by
    intro k l
    rw [adEntry_apply, sub_mul]
    congr 1
    · split_ifs <;> simp [vecOf]
    · split_ifs <;> simp [vecOf, mul_comm]
  rw [Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) =>
    Finset.sum_congr rfl fun l (_ : l ∈ Finset.univ) => hstep k l]
  simp only [Finset.sum_sub_distrib]
  have h1 : ∑ k : Fin n, ∑ l : Fin n, (if j = l then P i k * Q k l else 0)
      = ∑ k : Fin n, P i k * Q k j := by
    refine Finset.sum_congr rfl fun k _ => ?_
    simp
  have h2 : ∑ k : Fin n, ∑ l : Fin n, (if i = k then Q k l * P l j else 0)
      = ∑ l : Fin n, Q i l * P l j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp
  rw [h1, h2]
  show _ = (P * Q) i j - (Q * P) i j
  rw [Matrix.mul_apply, Matrix.mul_apply]

theorem adEntry_swap_self (P : Matrix (Fin n) (Fin n) R) (x : Fin n × Fin n) :
    adEntry P x.swap x = 0 := by
  obtain ⟨i, j⟩ := x
  rw [Prod.swap_prod_mk, adEntry_apply]
  by_cases h : i = j
  · simp [h]
  · simp [h, Ne.symm h]

theorem adEntry_swap_skew (P : Matrix (Fin n) (Fin n) R) (x y : Fin n × Fin n) :
    adEntry P y.swap x = -adEntry P x.swap y := by
  obtain ⟨i, j⟩ := x
  obtain ⟨k, l⟩ := y
  rw [Prod.swap_prod_mk, Prod.swap_prod_mk, adEntry_apply, adEntry_apply, neg_sub]
  congr 1
  · by_cases h : j = k
    · simp [h]
    · simp [h, Ne.symm h]
  · by_cases h : l = i
    · simp [h]
    · simp [h, Ne.symm h]

/-! ### `gl_n` reindexed by `Fin (n*n)` -/

variable (n) in
/-- The index type of `gl_n`, transported to `Fin (n*n)`. -/
def glIdx : Fin (n * n) ≃ Fin n × Fin n := finProdFinEquiv.symm

variable (n) in
/-- The transposition of matrix indices, as a permutation of `Fin (n*n)`. -/
def swapIdx : Equiv.Perm (Fin (n * n)) :=
  (glIdx n).trans ((Equiv.prodComm (Fin n) (Fin n)).trans (glIdx n).symm)

@[simp] theorem glIdx_swapIdx (a : Fin (n * n)) :
    glIdx n (swapIdx n a) = (glIdx n a).swap := by
  simp [swapIdx]

@[simp] theorem swapIdx_swapIdx (a : Fin (n * n)) : swapIdx n (swapIdx n a) = a := by
  apply (glIdx n).injective
  simp

/-- The matrix of `ad_P`, reindexed by `Fin (n*n)`. -/
def adMat (P : Matrix (Fin n) (Fin n) R) : Matrix (Fin (n * n)) (Fin (n * n)) R :=
  (adEntry P).submatrix (glIdx n) (glIdx n)

omit [CommRing R] in
/-- The coordinates of a matrix, indexed by `Fin (n*n)`. -/
def vecMat (Q : Matrix (Fin n) (Fin n) R) : Fin (n * n) → R := vecOf Q ∘ (glIdx n)

omit [CommRing R] in
@[simp] theorem vecMat_apply (Q : Matrix (Fin n) (Fin n) R) (a : Fin (n * n)) :
    vecMat Q a = Q (glIdx n a).1 (glIdx n a).2 := rfl

omit [CommRing R] in
theorem vecMat_injective : Function.Injective (vecMat (R := R) (n := n)) := by
  intro Q Q' h
  ext i j
  have := congrFun h ((glIdx n).symm (i, j))
  simpa using this

omit [CommRing R] in
theorem vecMat_surjective : Function.Surjective (vecMat (R := R) (n := n)) := by
  intro w
  refine ⟨Matrix.of fun i j => w ((glIdx n).symm (i, j)), ?_⟩
  funext a
  simp

theorem adMat_mulVec (P Q : Matrix (Fin n) (Fin n) R) :
    adMat P *ᵥ vecMat Q = vecMat (P * Q - Q * P) := by
  rw [adMat, Matrix.submatrix_mulVec_equiv (e₂ := glIdx n)]
  have hcomp : (vecMat Q) ∘ (glIdx n).symm = vecOf Q := by
    funext x
    simp [vecMat, vecOf]
  rw [hcomp, adEntry_mulVec]
  rfl

/-- Base change of `adEntry` along a ring map. -/
theorem adEntry_map {S : Type*} [CommRing S] (φ : R →+* S) (P : Matrix (Fin n) (Fin n) R) :
    adEntry (P.map φ) = (adEntry P).map φ := by
  ext x y
  rw [Matrix.map_apply, adEntry_apply, adEntry_apply, map_sub]
  congr 1 <;> split_ifs <;> simp

/-- Base change of `adMat` along a ring map. -/
theorem adMat_map {S : Type*} [CommRing S] (φ : R →+* S) (P : Matrix (Fin n) (Fin n) R) :
    adMat (P.map φ) = (adMat P).map φ := by
  rw [adMat, adMat, adEntry_map]
  rfl

end AdMat

end Height.Toolbox
