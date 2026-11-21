import Height.Geometry.Dimension.Affine

/-!
# Coordinates on the ambient spaces of matrices

The affine geometry layer works with points `ι → K`.  The pencil program lives
in four ambient spaces built from `n × n` matrices, and each is identified with
an affine space by a linear equivalence:

* `matCoords : Matrix μ μ K ≃ₗ[K] (μ × μ → K)`, a matrix by its entries;
* `pairCoords : Matrix μ μ K × Matrix μ μ K ≃ₗ[K] (PairIndex μ → K)`, a pair of
  matrices (the ambient space of pencils); `fstMat` and `sndMat` are the two
  components of its inverse;
* `markedCoords : Matrix μ μ K × Matrix μ μ K × K × K ≃ₗ[K] (MarkedIndex μ → K)`,
  a pencil with two marked parameters (the ambient space of `Ŷ`);
* `siCoords : SIPoint μ K ≃ₗ[K] (SIIndex μ → K)`, a pencil with one marked
  parameter (the ambient space of the single-point marked incidence).

These are the only coordinate maps of the development.  The inverse of each is
its `.symm`, and images are preimages of the inverse
(`LinearEquiv.image_eq_preimage_symm`).  The definitions are over any semiring,
so the same maps serve matrices over `K`, over `K⟦s⟧` (arcs), and over
polynomial rings (universal points).  The second section records that the
coordinate projections are polynomial maps.
-/

namespace Height.Geometry

section Coordinates

variable {K : Type*} [Semiring K] {μ : Type*}

/-- A matrix as a point of affine entry space. -/
def matCoords : Matrix μ μ K ≃ₗ[K] (μ × μ → K) where
  toFun M ij := M ij.1 ij.2
  invFun x := Matrix.of fun i j => x (i, j)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem matCoords_apply (M : Matrix μ μ K) (ij : μ × μ) :
    matCoords M ij = M ij.1 ij.2 := rfl

@[simp] theorem matCoords_symm_apply (x : μ × μ → K) (i j : μ) :
    matCoords.symm x i j = x (i, j) := rfl

/-- The index type of the affine space of pairs of matrices. -/
abbrev PairIndex (μ : Type*) : Type _ := (μ × μ) ⊕ (μ × μ)

/-- The first matrix of a point of pair space. -/
def fstMat (x : PairIndex μ → K) : Matrix μ μ K := Matrix.of fun i j => x (Sum.inl (i, j))

/-- The second matrix of a point of pair space. -/
def sndMat (x : PairIndex μ → K) : Matrix μ μ K := Matrix.of fun i j => x (Sum.inr (i, j))

omit [Semiring K] in
@[simp] theorem fstMat_apply (x : PairIndex μ → K) (i j : μ) :
    fstMat x i j = x (Sum.inl (i, j)) := rfl

omit [Semiring K] in
@[simp] theorem sndMat_apply (x : PairIndex μ → K) (i j : μ) :
    sndMat x i j = x (Sum.inr (i, j)) := rfl

/-- A pair of matrices as a point of affine space. -/
def pairCoords : (Matrix μ μ K × Matrix μ μ K) ≃ₗ[K] (PairIndex μ → K) where
  toFun p := Sum.elim (matCoords p.1) (matCoords p.2)
  invFun x := (fstMat x, sndMat x)
  left_inv _ := rfl
  right_inv x := by
    funext i
    cases i <;> rfl
  map_add' _ _ := by
    funext i
    cases i <;> rfl
  map_smul' _ _ := by
    funext i
    cases i <;> rfl

@[simp] theorem pairCoords_apply_inl (p : Matrix μ μ K × Matrix μ μ K) (ij : μ × μ) :
    pairCoords p (Sum.inl ij) = p.1 ij.1 ij.2 := rfl

@[simp] theorem pairCoords_apply_inr (p : Matrix μ μ K × Matrix μ μ K) (ij : μ × μ) :
    pairCoords p (Sum.inr ij) = p.2 ij.1 ij.2 := rfl

@[simp] theorem pairCoords_symm_apply (x : PairIndex μ → K) :
    pairCoords.symm x = (fstMat x, sndMat x) := rfl

@[simp] theorem fstMat_pairCoords (p : Matrix μ μ K × Matrix μ μ K) :
    fstMat (pairCoords p) = p.1 := rfl

@[simp] theorem sndMat_pairCoords (p : Matrix μ μ K × Matrix μ μ K) :
    sndMat (pairCoords p) = p.2 := rfl

@[simp] theorem pairCoords_fstMat_sndMat (x : PairIndex μ → K) :
    pairCoords (fstMat x, sndMat x) = x :=
  pairCoords.apply_symm_apply x

/-- The index type of the affine space of marked pencils: a pair of matrices and
two parameters. -/
abbrev MarkedIndex (μ : Type*) : Type _ := PairIndex μ ⊕ Fin 2

/-- A pencil with two marked parameters as a point of affine space. -/
def markedCoords : (Matrix μ μ K × Matrix μ μ K × K × K) ≃ₗ[K] (MarkedIndex μ → K) where
  toFun q := Sum.elim (pairCoords (q.1, q.2.1)) ![q.2.2.1, q.2.2.2]
  invFun x :=
    (fstMat fun i => x (Sum.inl i), sndMat fun i => x (Sum.inl i), x (Sum.inr 0), x (Sum.inr 1))
  left_inv _ := rfl
  right_inv x := by
    funext i
    rcases i with (ij | ij) | j
    · rfl
    · rfl
    · fin_cases j <;> rfl
  map_add' _ _ := by
    funext i
    rcases i with (ij | ij) | j
    · rfl
    · rfl
    · fin_cases j <;> rfl
  map_smul' _ _ := by
    funext i
    rcases i with (ij | ij) | j
    · rfl
    · rfl
    · fin_cases j <;> rfl

@[simp] theorem markedCoords_apply_inl (q : Matrix μ μ K × Matrix μ μ K × K × K)
    (i : PairIndex μ) : markedCoords q (Sum.inl i) = pairCoords (q.1, q.2.1) i := rfl

@[simp] theorem markedCoords_apply_inr_zero (q : Matrix μ μ K × Matrix μ μ K × K × K) :
    markedCoords q (Sum.inr 0) = q.2.2.1 := rfl

@[simp] theorem markedCoords_apply_inr_one (q : Matrix μ μ K × Matrix μ μ K × K × K) :
    markedCoords q (Sum.inr 1) = q.2.2.2 := rfl

@[simp] theorem markedCoords_symm_apply (x : MarkedIndex μ → K) :
    markedCoords.symm x =
      (fstMat fun i => x (Sum.inl i), sndMat fun i => x (Sum.inl i),
        x (Sum.inr 0), x (Sum.inr 1)) := rfl

/-- The index type of the ambient affine space of the single-point marked
incidence: a pair of matrices and one parameter. -/
abbrev SIIndex (μ : Type*) : Type _ := PairIndex μ ⊕ Unit

/-- A point of the ambient space of the single-point marked incidence: two
matrices and a parameter. -/
abbrev SIPoint (μ K : Type*) : Type _ := Matrix μ μ K × Matrix μ μ K × K

/-- A pencil with one marked parameter as a point of affine space. -/
def siCoords : SIPoint μ K ≃ₗ[K] (SIIndex μ → K) where
  toFun q := Sum.elim (pairCoords (q.1, q.2.1)) fun _ => q.2.2
  invFun z := (fstMat fun i => z (Sum.inl i), sndMat fun i => z (Sum.inl i), z (Sum.inr ()))
  left_inv _ := rfl
  right_inv z := by
    funext i
    rcases i with (ij | ij) | u <;> rfl
  map_add' _ _ := by
    funext i
    rcases i with (ij | ij) | u <;> rfl
  map_smul' _ _ := by
    funext i
    rcases i with (ij | ij) | u <;> rfl

@[simp] theorem siCoords_apply_inl (q : SIPoint μ K) (i : PairIndex μ) :
    siCoords q (Sum.inl i) = pairCoords (q.1, q.2.1) i := rfl

@[simp] theorem siCoords_apply_inr (q : SIPoint μ K) (u : Unit) :
    siCoords q (Sum.inr u) = q.2.2 := rfl

@[simp] theorem siCoords_symm_apply (z : SIIndex μ → K) :
    siCoords.symm z =
      (fstMat fun i => z (Sum.inl i), sndMat fun i => z (Sum.inl i), z (Sum.inr ())) := rfl

end Coordinates

/-! ### The coordinate projections are polynomial maps -/

section PolyMap

variable {K : Type*} [Field K] {ι μ : Type*}

/-- A constant matrix-valued map is polynomial. -/
theorem isPolyMap_matConst (A : Matrix μ μ K) :
    IsPolyMap (fun _ : ι → K => matCoords A) :=
  ⟨fun ij => MvPolynomial.C (A ij.1 ij.2), fun _ _ => by simp⟩

/-- A product of two polynomial matrix-valued maps is polynomial. -/
theorem isPolyMap_matMul [Fintype μ] {u v : (ι → K) → Matrix μ μ K}
    (hu : IsPolyMap fun x => matCoords (u x)) (hv : IsPolyMap fun x => matCoords (v x)) :
    IsPolyMap fun x => matCoords (u x * v x) := by
  obtain ⟨Fu, hFu⟩ := hu
  obtain ⟨Fv, hFv⟩ := hv
  refine ⟨fun ij => ∑ k, Fu (ij.1, k) * Fv (k, ij.2), fun x ij => ?_⟩
  show (u x * v x) ij.1 ij.2 = _
  rw [Matrix.mul_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, ← hFu x (ij.1, k), ← hFv x (k, ij.2)]
  rfl

/-- A difference of two polynomial matrix-valued maps is polynomial. -/
theorem isPolyMap_matSub {u v : (ι → K) → Matrix μ μ K}
    (hu : IsPolyMap fun x => matCoords (u x)) (hv : IsPolyMap fun x => matCoords (v x)) :
    IsPolyMap fun x => matCoords (u x - v x) := by
  obtain ⟨Fu, hFu⟩ := hu
  obtain ⟨Fv, hFv⟩ := hv
  refine ⟨fun ij => Fu ij - Fv ij, fun x ij => ?_⟩
  show (u x - v x) ij.1 ij.2 = _
  rw [map_sub, ← hFu x ij, ← hFv x ij]
  rfl

/-- Assembling two polynomial matrix-valued maps into a pair is polynomial. -/
theorem isPolyMap_pairCoords {u v : (ι → K) → Matrix μ μ K}
    (hu : IsPolyMap fun x => matCoords (u x)) (hv : IsPolyMap fun x => matCoords (v x)) :
    IsPolyMap fun x => pairCoords (u x, v x) := by
  obtain ⟨Fu, hFu⟩ := hu
  obtain ⟨Fv, hFv⟩ := hv
  refine ⟨Sum.elim Fu Fv, fun x i => ?_⟩
  cases i with
  | inl ij => exact hFu x ij
  | inr ij => exact hFv x ij

/-- The first matrix of a point of pair space is polynomial in the point. -/
theorem isPolyMap_fstMat : IsPolyMap fun x : PairIndex μ → K => matCoords (fstMat x) :=
  ⟨fun ij => MvPolynomial.X (Sum.inl ij), fun _ _ => by simp⟩

/-- The second matrix of a point of pair space is polynomial in the point. -/
theorem isPolyMap_sndMat : IsPolyMap fun x : PairIndex μ → K => matCoords (sndMat x) :=
  ⟨fun ij => MvPolynomial.X (Sum.inr ij), fun _ _ => by simp⟩

end PolyMap

end Height.Geometry
