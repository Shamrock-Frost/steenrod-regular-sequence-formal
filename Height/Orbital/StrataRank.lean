import Height.Toolbox.MinorRank
import Height.Orbital.Strata

/-!
# The chain strata as rank conditions

An input to `thm:star`.  Membership of a chain stratum
(`Height.Orbital.inStratum`) is a finite conjunction of conditions
`rank M = rank M'` on matrices built polynomially from the entries: by
`Height.Toolbox.pow_pred_mem_range_pow_iff_mem_kernelRange`,

  `chainCol x i ≤ m  ↔  y^(m-1) v ∈ range y^m`   (`y = x|_{F_i}`, `v = x e_i`)

and `b ∈ range A` is `rank [A | b] ≤ rank A`.  Consequently two strictly
upper triangular matrices *over different fields* whose rank profiles agree
have the same column sequence (`chainCol_eq_of_rank_eq`), which is what makes
an arc stay in the stratum of its base point once the ranks are constant.
-/

namespace Height.Orbital

open Matrix
open Height.Toolbox

universe u

section Aug

variable {R : Type*} [CommRing R] {a : ℕ}

/-- The square matrix `A` with the column `b` appended on the right. -/
def augCol (A : Matrix (Fin a) (Fin a) R) (b : Fin a → R) : Matrix (Fin a) (Fin (a + 1)) R :=
  Matrix.of fun i => Fin.snoc (A i) (b i)

omit [CommRing R] in
@[simp] theorem augCol_castSucc (A : Matrix (Fin a) (Fin a) R) (b : Fin a → R)
    (i : Fin a) (j : Fin a) : augCol A b i j.castSucc = A i j := by
  simp [augCol]

omit [CommRing R] in
@[simp] theorem augCol_last (A : Matrix (Fin a) (Fin a) R) (b : Fin a → R) (i : Fin a) :
    augCol A b i (Fin.last a) = b i := by
  simp [augCol]

theorem augCol_map {S : Type*} [CommRing S] (f : R →+* S)
    (A : Matrix (Fin a) (Fin a) R) (b : Fin a → R) :
    (augCol A b).map f = augCol (A.map f) (fun i => f (b i)) := by
  ext i j
  induction j using Fin.lastCases with
  | cast j => simp
  | last => simp

omit [CommRing R] in
theorem range_col_augCol (A : Matrix (Fin a) (Fin a) R) (b : Fin a → R) :
    Set.range (augCol A b).col = insert b (Set.range A.col) := by
  ext w
  constructor
  · rintro ⟨j, rfl⟩
    induction j using Fin.lastCases with
    | cast j =>
        refine Set.mem_insert_of_mem _ ⟨j, ?_⟩
        funext i
        simp
    | last =>
        refine Set.mem_insert_iff.2 (Or.inl ?_)
        funext i
        simp
  · intro hw
    rcases Set.mem_insert_iff.1 hw with rfl | ⟨j, rfl⟩
    · exact ⟨Fin.last a, by funext i; simp⟩
    · exact ⟨j.castSucc, by funext i; simp⟩

end Aug

section ChainData

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] {n : ℕ}

/-- The column vector whose membership in the column space of `(x|_{F_i})^m`
decides `chainCol x i ≤ m`. -/
def chainVec (x : Matrix (Fin n) (Fin n) R) (i : Fin n) (m : ℕ) : Fin i → R :=
  ((flagBlock x i) ^ (m - 1)) *ᵥ flagVec x i

/-- The square matrix whose rank, compared with that of its augmentation by
`chainVec`, decides `chainCol x i ≤ m`. -/
def chainMat (x : Matrix (Fin n) (Fin n) R) (i : Fin n) (m : ℕ) :
    Matrix (Fin i) (Fin i) R :=
  (flagBlock x i) ^ m

theorem flagBlock_map (φ : R →+* S) (x : Matrix (Fin n) (Fin n) R) (i : Fin n) :
    flagBlock (x.map φ) i = (flagBlock x i).map φ := rfl

theorem flagVec_map (φ : R →+* S) (x : Matrix (Fin n) (Fin n) R) (i : Fin n) :
    flagVec (x.map φ) i = fun t => φ (flagVec x i t) := rfl

theorem pow_map {a : ℕ} (φ : R →+* S) (A : Matrix (Fin a) (Fin a) R) (m : ℕ) :
    (A.map φ) ^ m = (A ^ m).map φ :=
  (map_pow φ.mapMatrix A m).symm

theorem chainMat_map (φ : R →+* S) (x : Matrix (Fin n) (Fin n) R) (i : Fin n) (m : ℕ) :
    chainMat (x.map φ) i m = (chainMat x i m).map φ := by
  rw [chainMat, chainMat, flagBlock_map, pow_map]

theorem chainVec_map (φ : R →+* S) (x : Matrix (Fin n) (Fin n) R) (i : Fin n) (m : ℕ) :
    chainVec (x.map φ) i m = fun t => φ (chainVec x i m t) := by
  funext t
  rw [chainVec, chainVec, flagBlock_map, flagVec_map, pow_map]
  exact (RingHom.map_mulVec φ ((flagBlock x i) ^ (m - 1)) (flagVec x i) t).symm

theorem chainAug_map (φ : R →+* S) (x : Matrix (Fin n) (Fin n) R) (i : Fin n) (m : ℕ) :
    augCol (chainMat (x.map φ) i m) (chainVec (x.map φ) i m) =
      (augCol (chainMat x i m) (chainVec x i m)).map φ := by
  rw [chainMat_map, chainVec_map, augCol_map]

end ChainData

section Field

variable {K : Type u} [Field K] {a : ℕ}

/-- Appending a column does not raise the rank exactly when the column
already lies in the column space. -/
theorem rank_augCol_le_iff (A : Matrix (Fin a) (Fin a) K) (b : Fin a → K) :
    (augCol A b).rank ≤ A.rank ↔ b ∈ LinearMap.range A.mulVecLin := by
  rw [Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_cols, range_col_augCol,
    Submodule.span_insert, Matrix.range_mulVecLin]
  constructor
  · intro h
    have hle : Submodule.span K (Set.range A.col) ≤
        (Submodule.span K {b}) ⊔ Submodule.span K (Set.range A.col) := le_sup_right
    have heq := Submodule.eq_of_le_of_finrank_le hle h
    exact heq ▸ (le_sup_left : Submodule.span K {b} ≤ _) (Submodule.mem_span_singleton_self b)
  · intro hb
    have hle : Submodule.span K {b} ≤ Submodule.span K (Set.range A.col) := by
      rw [Submodule.span_le, Set.singleton_subset_iff]
      exact hb
    rw [sup_eq_right.2 hle]

end Field

section ChainColRank

variable {K : Type u} [Field K] {n : ℕ}

theorem toLinAlgEquiv'_eq_mulVecLin {b : ℕ} (M : Matrix (Fin b) (Fin b) K) :
    (Matrix.toLinAlgEquiv' M : (Fin b → K) →ₗ[K] Fin b → K) = M.mulVecLin := by
  ext v i
  simp [Matrix.toLinAlgEquiv'_apply]

/-- `lem:box-column` as a rank condition. -/
theorem chainCol_le_iff_rank_le {x : Matrix (Fin n) (Fin n) K} (hx : IsStrictlyUpper x)
    (i : Fin n) {m : ℕ} (hm : 1 ≤ m) :
    chainCol x hx i ≤ m ↔
      (augCol (chainMat x i m) (chainVec x i m)).rank ≤ (chainMat x i m).rank := by
  have hnil : IsNilpotent (Matrix.toLinAlgEquiv' (flagBlock x i)) :=
    strictlyUpper_isNilpotent (isStrictlyUpper_flagBlock hx i)
  rw [rank_augCol_le_iff]
  constructor
  · intro h
    have hmem : flagVec x i ∈ kernelRange (Matrix.toLinAlgEquiv' (flagBlock x i)) m :=
      kernelRange_mono _ h (boxColumn_spec _ _ hnil).2
    have := (pow_pred_mem_range_pow_iff_mem_kernelRange
      (Matrix.toLinAlgEquiv' (flagBlock x i)) (flagVec x i) m hm).2 hmem
    rw [← map_pow, ← map_pow, toLinAlgEquiv'_eq_mulVecLin] at this
    simpa [chainMat, chainVec, Matrix.mulVecLin_apply, toLinAlgEquiv'_eq_mulVecLin] using this
  · intro h
    refine boxColumn_min _ _ hnil hm ?_
    refine (pow_pred_mem_range_pow_iff_mem_kernelRange
      (Matrix.toLinAlgEquiv' (flagBlock x i)) (flagVec x i) m hm).1 ?_
    rw [← map_pow, ← map_pow, toLinAlgEquiv'_eq_mulVecLin]
    simpa [chainMat, chainVec, Matrix.mulVecLin_apply, toLinAlgEquiv'_eq_mulVecLin] using h

/-- Every column of the chain tableau lies in the first `n` columns. -/
theorem chainCol_le_card {x : Matrix (Fin n) (Fin n) K} (hx : IsStrictlyUpper x) (i : Fin n) :
    chainCol x hx i ≤ n := by
  have hz : (Matrix.toLinAlgEquiv' (flagBlock x i)) ^ (i : ℕ) = 0 := by
    rw [← map_pow, strictlyUpper_pow_eq_zero (isStrictlyUpper_flagBlock hx i), map_zero]
  have := boxColumn_le_nilpotency_succ (Matrix.toLinAlgEquiv' (flagBlock x i))
    (flagVec x i) (i : ℕ) hz
  have hi : (i : ℕ) + 1 ≤ n := i.isLt
  exact le_trans (le_of_eq rfl) (le_trans this hi)

/-- Two strictly upper triangular matrices, over any two fields, with the
same rank profile have the same column sequence. -/
theorem chainCol_eq_of_rank_eq {L : Type u} [Field L]
    {x : Matrix (Fin n) (Fin n) K} {y : Matrix (Fin n) (Fin n) L}
    (hx : IsStrictlyUpper x) (hy : IsStrictlyUpper y)
    (hmat : ∀ (i : Fin n) (m : ℕ), m ≤ n → (chainMat x i m).rank = (chainMat y i m).rank)
    (haug : ∀ (i : Fin n) (m : ℕ), m ≤ n →
      (augCol (chainMat x i m) (chainVec x i m)).rank =
        (augCol (chainMat y i m) (chainVec y i m)).rank)
    (i : Fin n) : chainCol x hx i = chainCol y hy i := by
  have key : ∀ m : ℕ, 1 ≤ m → m ≤ n → (chainCol x hx i ≤ m ↔ chainCol y hy i ≤ m) := by
    intro m hm hmn
    rw [chainCol_le_iff_rank_le hx i hm, chainCol_le_iff_rank_le hy i hm,
      hmat i m hmn, haug i m hmn]
  refine le_antisymm ?_ ?_
  · exact (key _ (one_le_chainCol y hy i) (chainCol_le_card hy i)).2 le_rfl
  · exact (key _ (one_le_chainCol x hx i) (chainCol_le_card hx i)).1 le_rfl

end ChainColRank

end Height.Orbital
