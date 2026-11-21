import Height.Chain.Springer
import Height.Chain.Untwist
import Height.Orbital.StrataRank
import Height.Geometry.Dimension.LocClosed
import Height.Geometry.Spec
import Height.Chain.Constructible

/-!
# The chain-strata dimension bound

`lem:springer-dim`, first half: for a nilpotent `M` over an algebraically closed
field, `dim (𝔫 ∩ O_M) ≤ C(n,2) − n(λ)`.  It is the one input of the chain node
`prop:springer-bound` (`Height.Chain.springer` below, through
`affineDim_triangularizablePartner_le` of `Chain/Springer.lean`).  The node lives here rather than in `Chain/Counts.lean`
because `Chain/Springer.lean` is downstream of that file.

The proof is the induction of `subsec:chain-strata` on `n` through the
restriction `x ↦ x|_{F_n}` (`Orbital/Strata.lean`).  Two things have to be
arranged.

* **The fibre.**  Over `y ∈ A_{T'}` the fibre of `A_T → A_{T'}` consists of the
  matrices obtained by adjoining a last column `v` with
  `boxColumn y v = c := T(last)`; such a `v` lies in `K_c(y) = kernelRange y c`
  (`Toolbox/Jordan.lean`), a linear subspace of dimension `n − μ'_c`, and the
  matrix is reconstructed from `(y, v)` by a polynomial map.

* **Constructibility.**  `A_T` is a rank *equality* locus, so it is only
  locally closed, and its closure has larger fibres (a point of
  `zclosure A_{T'}` of smaller type has a *larger* `K_c`).  The file therefore
  carries, through the induction, an explicit presentation of `A_T` as a
  constructible set (`Height.Geometry.IsAffineConstructible`: a finite union of
  sets `Z ∩ {q ≠ 0}` with `Z` Zariski closed), built recursively — the closed
  part pulls back the closed part of `A_{T'}` and adds the vanishing of the
  `(ρ_c+1)`-minors of `[y^c | y^{c-1} v]`, and the open part multiplies the open
  part of `A_{T'}` by one `(ρ_{c-1}+1)`-minor of `[y^{c-1} | y^{c-2} v]`.  The
  dimension step is then the fibre-dimension inequality on `K`-points,
  `Height.Geometry.affineDim_le_image_add_fibre_pts` (`Geometry/Spec.lean`),
  applied to `A_T` as a whole: the locus of `𝔸` is produced by
  `exists_isConstructible_pts_eq` and the restriction map by
  `polyMapEquiv (restrictCoordPoly K n)`.
-/

namespace Height.Chain

open Matrix Height.Toolbox Height.Orbital Height.Geometry

universe u

/-! ## The Springer number of a column sequence -/

section Count

/-- `C(k+1,2) = C(k,2) + k`. -/
theorem choose_two_succ (k : ℕ) : (k + 1).choose 2 = k.choose 2 + k := by
  have h : (k + 1).choose 2 = k.choose 1 + k.choose 2 := Nat.choose_succ_succ' k 1
  rw [Nat.choose_one_right] at h
  omega

/-- `n(λ)` read off a column sequence: `Σ_m C(#{i : T i = m}, 2)`, the shape of
`Height.Chain.nOf` for a point of the stratum `A_T`. -/
def nSeq {n : ℕ} (T : Fin n → ℕ) : ℕ :=
  ∑ m ∈ Finset.Icc 1 n, ((Finset.univ.filter fun i => T i = m).card).choose 2

/-- Splitting the count of a column sequence at its last entry. -/
theorem card_filter_castSucc {n : ℕ} (T : Fin (n + 1) → ℕ) (m : ℕ) :
    (Finset.univ.filter fun i : Fin (n + 1) => T i = m).card =
      (Finset.univ.filter fun i : Fin n => T i.castSucc = m).card +
        (if T (Fin.last n) = m then 1 else 0) := by
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]

/-- The recursion for `nSeq`: the last box contributes one pair for every
earlier box in the same column. -/
theorem nSeq_succ {n : ℕ} (T : Fin (n + 1) → ℕ) (hc1 : 1 ≤ T (Fin.last n))
    (hcn : T (Fin.last n) ≤ n + 1) (hlt : ∀ i : Fin n, T i.castSucc ≤ n) :
    nSeq T = nSeq (T ∘ Fin.castSucc) +
      (Finset.univ.filter fun i : Fin n => T i.castSucc = T (Fin.last n)).card := by
  classical
  set c := T (Fin.last n) with hc
  set b : ℕ → ℕ := fun m => (Finset.univ.filter fun i : Fin n => T i.castSucc = m).card with hb
  have key : ∀ m : ℕ, ((Finset.univ.filter fun i : Fin (n + 1) => T i = m).card).choose 2
      = (b m).choose 2 + (if c = m then b m else 0) := by
    intro m
    rw [card_filter_castSucc T m]
    by_cases h : c = m
    · rw [ite_eq_left h, ite_eq_left h]
      exact choose_two_succ (b m)
    · rw [ite_eq_right h, ite_eq_right h, add_zero, add_zero]
  rw [nSeq, Finset.sum_congr rfl (fun m _ => key m), Finset.sum_add_distrib]
  have hsplit : ∑ m ∈ Finset.Icc 1 (n + 1), (b m).choose 2 =
      (∑ m ∈ Finset.Icc 1 n, (b m).choose 2) + (b (n + 1)).choose 2 :=
    Finset.sum_Icc_succ_top (by omega) _
  have hzero : b (n + 1) = 0 := by
    rw [hb, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i _
    have := hlt i
    omega
  have hite : ∑ m ∈ Finset.Icc 1 (n + 1), (if c = m then b m else 0) = b c := by
    rw [Finset.sum_ite_eq (Finset.Icc 1 (n + 1)) c b, ite_eq_left]
    exact Finset.mem_Icc.mpr ⟨hc1, hcn⟩
  rw [hsplit, hzero, hite]
  show (∑ m ∈ Finset.Icc 1 n, (b m).choose 2) + Nat.choose 0 2 + b c = nSeq (T ∘ Fin.castSucc) + b c
  rw [Nat.choose_zero_succ, add_zero]
  rfl

/-- Under the constraints that a genuine column sequence satisfies, `n(λ)` is at
most `C(n,2)`. -/
theorem nSeq_le_choose_two : ∀ (n : ℕ) (T : Fin n → ℕ), (∀ i, 1 ≤ T i) →
    (∀ i : Fin n, T i ≤ (i : ℕ) + 1) → nSeq T ≤ n.choose 2 := by
  intro n
  induction n with
  | zero => intro T _ _; simp [nSeq]
  | succ n ih =>
      intro T h1 h2
      have hlt : ∀ i : Fin n, T i.castSucc ≤ n := by
        intro i
        have := h2 i.castSucc
        have hi := i.isLt
        simp only [Fin.val_castSucc] at this
        omega
      have hstep := nSeq_succ T (h1 _) (by simpa using h2 (Fin.last n)) hlt
      have hprev : nSeq (T ∘ Fin.castSucc) ≤ n.choose 2 := by
        refine ih _ (fun i => h1 _) (fun i => ?_)
        have := h2 i.castSucc
        simpa using this
      have hcard : (Finset.univ.filter fun i : Fin n => T i.castSucc = T (Fin.last n)).card ≤ n := by
        have := Finset.card_filter_le (Finset.univ : Finset (Fin n))
          (fun i : Fin n => T i.castSucc = T (Fin.last n))
        simpa using this
      have hch : (n + 1).choose 2 = n.choose 2 + n := choose_two_succ n
      omega

end Count

/-! ## Rank, kernel dimensions and conjugation -/

section RankBridge

variable {K : Type u} [Field K] {n : ℕ}

/-- The conjugate Jordan partition in terms of ranks. -/
theorem conj_eq_rank_sub (A : Matrix (Fin n) (Fin n) K) (m : ℕ) :
    conj (Matrix.toLinAlgEquiv' A) m = (A ^ (m - 1)).rank - (A ^ m).rank := by
  have h1 := finrank_ker_add_rank_pow A m
  have h2 := finrank_ker_add_rank_pow A (m - 1)
  rw [conj]
  omega

/-- On a stratum the ranks of all powers are determined by the column
sequence. -/
theorem rank_pow_add_card_of_inStratum {T : Fin n → ℕ} {x : Matrix (Fin n) (Fin n) K}
    (h : inStratum T x) (m : ℕ) :
    (x ^ m).rank + (Finset.univ.filter fun i => T i ≤ m).card = n := by
  have h1 := finrank_ker_add_rank_pow x m
  rw [finrank_ker_pow_of_inStratum h m] at h1
  omega

/-- Conjugate matrices have the same rank in every power. -/
theorem rank_pow_of_mem_conjOrbit {N X : Matrix (Fin n) (Fin n) K} (hX : X ∈ conjOrbit N)
    (m : ℕ) : (X ^ m).rank = (N ^ m).rank := by
  classical
  obtain ⟨g, rfl⟩ := hX
  set G : Matrix (Fin n) (Fin n) K := (g : Matrix (Fin n) (Fin n) K) with hG
  set Gi : Matrix (Fin n) (Fin n) K := (↑g⁻¹ : Matrix (Fin n) (Fin n) K) with hGi
  have hGGi : G * Gi = 1 := by rw [hG, hGi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hGiG : Gi * G = 1 := by rw [hG, hGi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hsemi : SemiconjBy G N (G * N * Gi) := by
    show G * N = (G * N * Gi) * G
    rw [Matrix.mul_assoc (G * N) Gi G, hGiG, Matrix.mul_one]
  have hpow := hsemi.pow_right m
  have hXm : (G * N * Gi) ^ m = G * N ^ m * Gi := by
    have h1 : G * N ^ m = (G * N * Gi) ^ m * G := hpow
    have h2 : (G * N ^ m) * Gi = ((G * N * Gi) ^ m * G) * Gi := by rw [h1]
    rw [Matrix.mul_assoc ((G * N * Gi) ^ m) G Gi, hGGi, Matrix.mul_one] at h2
    exact h2.symm
  have hGu : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit
  have hGiu : IsUnit Gi.det := (Matrix.isUnit_iff_isUnit_det _).mp g⁻¹.isUnit
  rw [hXm, Matrix.rank_mul_eq_left_of_isUnit_det Gi (G * N ^ m) hGiu,
    Matrix.rank_mul_eq_right_of_isUnit_det G (N ^ m) hGu]

/-- Conjugate matrices have the same conjugate Jordan partition. -/
theorem conj_of_mem_conjOrbit {N X : Matrix (Fin n) (Fin n) K} (hX : X ∈ conjOrbit N) (m : ℕ) :
    conj (Matrix.toLinAlgEquiv' X) m = conj (Matrix.toLinAlgEquiv' N) m := by
  rw [conj_eq_rank_sub, conj_eq_rank_sub, rank_pow_of_mem_conjOrbit hX,
    rank_pow_of_mem_conjOrbit hX]

/-- Conjugate matrices have the same Springer number. -/
theorem nOf_of_mem_conjOrbit {N X : Matrix (Fin n) (Fin n) K} (hX : X ∈ conjOrbit N) :
    nOf X = nOf N :=
  Finset.sum_congr rfl fun m _ => by rw [conj_of_mem_conjOrbit hX]

/-- The Springer number of a point of `A_T` is `nSeq T`. -/
theorem nOf_of_inStratum {T : Fin n → ℕ} {x : Matrix (Fin n) (Fin n) K} (h : inStratum T x) :
    nOf x = nSeq T :=
  Finset.sum_congr rfl fun m _ => by rw [conj_of_inStratum h m]

/-- Every column of a chain tableau lies in the columns before the box. -/
theorem chainCol_le_succ {x : Matrix (Fin n) (Fin n) K} (hx : IsStrictlyUpper x) (i : Fin n) :
    chainCol x hx i ≤ (i : ℕ) + 1 := by
  have hz : (Matrix.toLinAlgEquiv' (flagBlock x i)) ^ (i : ℕ) = 0 := by
    rw [← map_pow, strictlyUpper_pow_eq_zero (isStrictlyUpper_flagBlock hx i), map_zero]
  exact boxColumn_le_nilpotency_succ (Matrix.toLinAlgEquiv' (flagBlock x i)) (flagVec x i) _ hz

theorem le_succ_of_inStratum {T : Fin n → ℕ} {x : Matrix (Fin n) (Fin n) K}
    (h : inStratum T x) (i : Fin n) : T i ≤ (i : ℕ) + 1 := by
  rw [← h.chainCol_eq h.upper i]
  exact chainCol_le_succ h.upper i

end RankBridge

/-! ## The strata in affine coordinates -/

section Affine

variable {K : Type u} [Field K] {n : ℕ}

/-- The chain stratum `A_T` as a subset of affine entry space. -/
def stratumSet (T : Fin n → ℕ) : Set (Fin n × Fin n → K) :=
  {z | inStratum T (matCoords.symm z)}

/-- The index change of the restriction map. -/
def renIdx (n : ℕ) : Fin n × Fin n → Fin (n + 1) × Fin (n + 1) :=
  fun ij => (ij.1.castSucc, ij.2.castSucc)

/-- Restriction to the first `n` coordinates, in entry coordinates. -/
def restrictCoord (z : Fin (n + 1) × Fin (n + 1) → K) : Fin n × Fin n → K :=
  fun ij => z (renIdx n ij)

theorem isPolyMap_restrictCoord : IsPolyMap (restrictCoord (K := K) (n := n)) :=
  ⟨fun ij => MvPolynomial.X (renIdx n ij), fun z ij => by simp [restrictCoord]⟩

/-- The restriction map as a family of polynomials: the shape the geometry API's
`polyMapEquiv` takes. -/
noncomputable def restrictCoordPoly (K : Type u) [Field K] (n : ℕ) :
    Fin n × Fin n → MvPolynomial (Fin (n + 1) × Fin (n + 1)) K :=
  fun ij => MvPolynomial.X (renIdx n ij)

theorem aeval_restrictCoordPoly :
    (fun (z : Fin (n + 1) × Fin (n + 1) → K) (ij : Fin n × Fin n) =>
      MvPolynomial.aeval z (restrictCoordPoly K n ij)) = restrictCoord := by
  funext z ij
  simp [restrictCoordPoly, restrictCoord]

theorem ofMatCoords_restrictCoord (z : Fin (n + 1) × Fin (n + 1) → K) :
    matCoords.symm (restrictCoord z) = restrict (matCoords.symm z) := rfl

theorem aeval_rename_renIdx (z : Fin (n + 1) × Fin (n + 1) → K)
    (p : MvPolynomial (Fin n × Fin n) K) :
    MvPolynomial.aeval z (MvPolynomial.rename (renIdx n) p) =
      MvPolynomial.aeval (restrictCoord z) p := by
  rw [MvPolynomial.aeval_rename]
  rfl

/-- The last column, in entry coordinates. -/
def lastColCoord (z : Fin (n + 1) × Fin (n + 1) → K) : Fin n → K :=
  fun i => z (i.castSucc, Fin.last n)

theorem isPolyMap_lastColCoord : IsPolyMap (lastColCoord (K := K) (n := n)) :=
  ⟨fun i => MvPolynomial.X (i.castSucc, Fin.last n), fun z i => by simp [lastColCoord]⟩

/-! ### Rebuilding a strictly upper triangular matrix from `(y, v)` -/

/-- The polynomial rebuilding the entries of a strictly upper triangular matrix
from its last column, with the entries of its restriction as constants. -/
noncomputable def snocPoly (y : Fin n × Fin n → K) (ij : Fin (n + 1) × Fin (n + 1)) :
    MvPolynomial (Fin n) K :=
  if h1 : (ij.1 : ℕ) < n then
    (if h2 : (ij.2 : ℕ) < n then MvPolynomial.C (y (⟨ij.1, h1⟩, ⟨ij.2, h2⟩))
      else MvPolynomial.X ⟨ij.1, h1⟩)
  else 0

/-- The reconstruction map `v ↦ x`, a polynomial map for each fixed `y`. -/
noncomputable def snocPt (y : Fin n × Fin n → K) (v : Fin n → K) :
    Fin (n + 1) × Fin (n + 1) → K :=
  fun ij => MvPolynomial.aeval v (snocPoly y ij)

theorem isPolyMap_snocPt (y : Fin n × Fin n → K) : IsPolyMap (snocPt y) :=
  ⟨snocPoly y, fun _ _ => rfl⟩

/-- A strictly upper triangular matrix is rebuilt from its restriction and its
last column. -/
theorem snocPt_lastColCoord {z : Fin (n + 1) × Fin (n + 1) → K}
    (hz : IsStrictlyUpper (matCoords.symm z)) :
    snocPt (restrictCoord z) (lastColCoord z) = z := by
  funext ij
  obtain ⟨i, j⟩ := ij
  show MvPolynomial.aeval (lastColCoord z) (snocPoly (restrictCoord z) (i, j)) = z (i, j)
  rw [snocPoly]
  by_cases h1 : (i : ℕ) < n
  · have hi : ((⟨(i : ℕ), h1⟩ : Fin n).castSucc) = i := Fin.ext rfl
    rw [dite_eq_left h1]
    by_cases h2 : (j : ℕ) < n
    · have hj : ((⟨(j : ℕ), h2⟩ : Fin n).castSucc) = j := Fin.ext rfl
      rw [dite_eq_left h2, MvPolynomial.aeval_C]
      show z ((⟨(i : ℕ), h1⟩ : Fin n).castSucc, (⟨(j : ℕ), h2⟩ : Fin n).castSucc) = z (i, j)
      rw [hi, hj]
    · have hj : j = Fin.last n := by
        refine Fin.ext ?_
        have := j.isLt
        simp only [Fin.val_last]
        omega
      rw [dite_eq_right h2, MvPolynomial.aeval_X]
      show z ((⟨(i : ℕ), h1⟩ : Fin n).castSucc, Fin.last n) = z (i, j)
      rw [hi, hj]
  · have hi : i = Fin.last n := by
      refine Fin.ext ?_
      have := i.isLt
      simp only [Fin.val_last]
      omega
    rw [dite_eq_right h1, map_zero, hi]
    exact (hz (Fin.last n) j (Fin.le_last j)).symm

/-! ### The augmented matrix `[y^m | y^{m-1} v]` and its minors -/

/-- `[y^m | y^{m-1} v]` for `y = x|_{F_n}` and `v` the last column of `x`. -/
def augLast (x : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (m : ℕ) :
    Matrix (Fin n) (Fin (n + 1)) K :=
  augCol ((restrict x) ^ m) (((restrict x) ^ (m - 1)) *ᵥ (lastCol x))

/-- The rank criterion of `Orbital/StrataRank.lean` at the last box. -/
theorem chainCol_last_le_iff {x : Matrix (Fin (n + 1)) (Fin (n + 1)) K}
    (hx : IsStrictlyUpper x) {m : ℕ} (hm : 1 ≤ m) :
    chainCol x hx (Fin.last n) ≤ m ↔ (augLast x m).rank ≤ ((restrict x) ^ m).rank :=
  chainCol_le_iff_rank_le hx (Fin.last n) hm

/-- The generic augmented matrix, over the coordinate ring. -/
noncomputable def restrPoly (K : Type u) [Field K] (n : ℕ) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin (n + 1) × Fin (n + 1)) K) :=
  Matrix.of fun i j => MvPolynomial.X (i.castSucc, j.castSucc)

noncomputable def lastPoly (K : Type u) [Field K] (n : ℕ) :
    Fin n → MvPolynomial (Fin (n + 1) × Fin (n + 1)) K :=
  fun i => MvPolynomial.X (i.castSucc, Fin.last n)

noncomputable def augLastPoly (K : Type u) [Field K] (n m : ℕ) :
    Matrix (Fin n) (Fin (n + 1)) (MvPolynomial (Fin (n + 1) × Fin (n + 1)) K) :=
  augCol ((restrPoly K n) ^ m) (((restrPoly K n) ^ (m - 1)) *ᵥ (lastPoly K n))

theorem map_restrPoly (z : Fin (n + 1) × Fin (n + 1) → K) :
    (restrPoly K n).map (MvPolynomial.eval z) = restrict (matCoords.symm z) := by
  ext i j
  show MvPolynomial.eval z (MvPolynomial.X (i.castSucc, j.castSucc)) = _
  rw [MvPolynomial.eval_X]
  rfl

theorem map_lastPoly (z : Fin (n + 1) × Fin (n + 1) → K) (i : Fin n) :
    MvPolynomial.eval z (lastPoly K n i) = lastCol (matCoords.symm z) i := by
  rw [lastPoly, MvPolynomial.eval_X]
  rfl

/-- The augmented matrix commutes with any ring homomorphism. -/
theorem augPow_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (A : Matrix (Fin n) (Fin n) R) (b : Fin n → R) (m : ℕ) :
    (augCol (A ^ m) ((A ^ (m - 1)) *ᵥ b)).map φ =
      augCol ((A.map φ) ^ m) (((A.map φ) ^ (m - 1)) *ᵥ (fun i => φ (b i))) := by
  rw [augCol_map φ, pow_map, pow_map]
  congr 1
  funext i
  exact RingHom.map_mulVec φ (A ^ (m - 1)) b i

theorem map_augLastPoly (z : Fin (n + 1) × Fin (n + 1) → K) (m : ℕ) :
    (augLastPoly K n m).map (MvPolynomial.eval z) = augLast (matCoords.symm z) m := by
  have hb : (fun i => MvPolynomial.eval z (lastPoly K n i)) = lastCol (matCoords.symm z) :=
    funext (map_lastPoly z)
  rw [augLastPoly, augPow_map, map_restrPoly, hb, augLast]

/-- The `s × s` minors of the augmented matrix, as polynomials in the entries. -/
noncomputable def minorPoly (K : Type u) [Field K] (n m s : ℕ)
    (f : Fin s → Fin n) (g : Fin s → Fin (n + 1)) :
    MvPolynomial (Fin (n + 1) × Fin (n + 1)) K :=
  ((augLastPoly K n m).submatrix f g).det

theorem eval_minorPoly (z : Fin (n + 1) × Fin (n + 1) → K) (m s : ℕ)
    (f : Fin s → Fin n) (g : Fin s → Fin (n + 1)) :
    MvPolynomial.eval z (minorPoly K n m s f g) =
      (((augLast (matCoords.symm z) m)).submatrix f g).det := by
  rw [minorPoly, RingHom.map_det, RingHom.mapMatrix_apply, ← Matrix.submatrix_map,
    map_augLastPoly]


/-! ### Zariski closed pieces -/

/-- The nilradical `𝔫`, in entry coordinates. -/
def upperSet (K : Type u) [Field K] (n : ℕ) : Set (Fin n × Fin n → K) :=
  {z | IsStrictlyUpper (matCoords.symm z)}

theorem zclosure_upperSet : zclosure (upperSet K n) = upperSet K n := by
  refine zclosure_eq_self_of_eqZeroLocus
    (T := (fun ij : Fin n × Fin n => MvPolynomial.X ij) '' {ij : Fin n × Fin n | ij.2 ≤ ij.1}) ?_
  intro z
  constructor
  · rintro hz p ⟨ij, hij, rfl⟩
    rw [MvPolynomial.aeval_X]
    exact hz ij.1 ij.2 hij
  · intro h i j hij
    have hx := h (MvPolynomial.X (i, j)) ⟨(i, j), hij, rfl⟩
    rw [MvPolynomial.aeval_X] at hx
    exact hx

/-- The closed condition `rank [y^m | y^{m-1} v] ≤ ρ`. -/
def minorZeroSet (K : Type u) [Field K] (n m ρ : ℕ) : Set (Fin (n + 1) × Fin (n + 1) → K) :=
  {z | ∀ (f : Fin (ρ + 1) → Fin n) (g : Fin (ρ + 1) → Fin (n + 1)),
    ((augLast (matCoords.symm z) m).submatrix f g).det = 0}

theorem mem_minorZeroSet_iff {m ρ : ℕ} (z : Fin (n + 1) × Fin (n + 1) → K) :
    z ∈ minorZeroSet K n m ρ ↔ (augLast (matCoords.symm z) m).rank ≤ ρ := by
  constructor
  · intro h
    by_contra hlt
    obtain ⟨f, g, hfg⟩ :=
      exists_submatrix_det_ne_zero (augLast (matCoords.symm z) m) (Nat.not_le.mp hlt)
    exact hfg (h f g)
  · intro h f g
    by_contra hne
    have := le_rank_of_submatrix_det_ne_zero (augLast (matCoords.symm z) m) f g hne
    omega

theorem zclosure_minorZeroSet {m ρ : ℕ} :
    zclosure (minorZeroSet K n m ρ) = minorZeroSet K n m ρ := by
  refine zclosure_eq_self_of_eqZeroLocus
    (T := Set.range (fun p : (Fin (ρ + 1) → Fin n) × (Fin (ρ + 1) → Fin (n + 1)) =>
      minorPoly K n m (ρ + 1) p.1 p.2)) ?_
  intro z
  constructor
  · rintro hz p ⟨⟨f, g⟩, rfl⟩
    rw [MvPolynomial.aeval_eq_eval, eval_minorPoly]
    exact hz f g
  · intro h f g
    have hx := h _ ⟨(f, g), rfl⟩
    rw [MvPolynomial.aeval_eq_eval, eval_minorPoly] at hx
    exact hx

end Affine

/-! ## The induction on `n` through the restriction -/

section Induction

-- The geometry API ties the index universe of `𝔸(ι)` to that of `K`, so the sections that
-- call it live at `K : Type` (the chain runs at `Kbar p r : Type`).
variable {K : Type} [Field K] {n : ℕ}

/-- Membership of `A_T` is decided by the restriction together with the column
of the last box. -/
theorem inStratum_of_restrict {T : Fin (n + 1) → ℕ}
    {x : Matrix (Fin (n + 1)) (Fin (n + 1)) K} (hx : IsStrictlyUpper x)
    (hres : inStratum (T ∘ Fin.castSucc) (restrict x))
    (hlast : chainCol x hx (Fin.last n) = T (Fin.last n)) : inStratum T x := by
  refine ⟨hx, fun i => ?_⟩
  induction i using Fin.lastCases with
  | last => exact hlast
  | cast i =>
      show chainCol x hx i.castSucc = T i.castSucc
      have hcc : chainCol x hx i.castSucc
          = chainCol (restrict x) (isStrictlyUpper_restrict hx) i := rfl
      rw [hcc]
      exact hres.chainCol_eq _ i

/-- **The fibre bound.**  Over `A_{T'}` the fibres of the restriction on any
subset of `A_T` lie in the linear subspace `K_c(y)`, of dimension `n − μ'_c`. -/
theorem affineDim_fibre_le [IsAlgClosed K] (T : Fin (n + 1) → ℕ)
    {P : Set (Fin (n + 1) × Fin (n + 1) → K)} (hP : P ⊆ stratumSet T)
    (y : Fin n × Fin n → K) :
    affineDim (P ∩ restrictCoord ⁻¹' {y}) ≤
      ((((n - (Finset.univ.filter fun i : Fin n => T i.castSucc = T (Fin.last n)).card : ℕ) :
        ℕ∞)) : WithBot ℕ∞) := by
  classical
  rcases Set.eq_empty_or_nonempty (P ∩ restrictCoord ⁻¹' {y}) with hempty | ⟨z₀, hz₀⟩
  · rw [hempty, affineDim_empty]
    exact bot_le
  · have hx₀ : inStratum T (matCoords.symm z₀) := hP hz₀.1
    have hy₀ : inStratum (T ∘ Fin.castSucc) (matCoords.symm y) := by
      have h := inStratum_restrict hx₀
      rwa [← ofMatCoords_restrictCoord, hz₀.2] at h
    have hc1 : 1 ≤ T (Fin.last n) := one_le_of_inStratum hx₀ (Fin.last n)
    set V : Submodule K (Fin n → K) :=
      kernelRange (Matrix.toLinAlgEquiv' (matCoords.symm y)) (T (Fin.last n)) with hV
    have hVdim : Module.finrank K V =
        n - (Finset.univ.filter fun i : Fin n => T i.castSucc = T (Fin.last n)).card := by
      rw [hV, finrank_kernelRange _ _ hc1, Module.finrank_fin_fun,
        conj_of_inStratum hy₀ (T (Fin.last n))]
      rfl
    -- the fibre is carried isomorphically onto its last columns, which lie in `V`
    have hrec : ∀ z ∈ P ∩ restrictCoord ⁻¹' {y}, snocPt y (lastColCoord z) = z := by
      rintro z ⟨hz1, hz2⟩
      have hz2' : restrictCoord z = y := hz2
      have hx : inStratum T (matCoords.symm z) := hP hz1
      rw [← hz2']
      exact snocPt_lastColCoord hx.upper
    have hdim : affineDim (lastColCoord '' (P ∩ restrictCoord ⁻¹' {y}))
        = affineDim (P ∩ restrictCoord ⁻¹' {y}) :=
      affineDim_image_eq isPolyMap_lastColCoord (isPolyMap_snocPt y) hrec
    have hsub : lastColCoord '' (P ∩ restrictCoord ⁻¹' {y}) ⊆ (V : Set (Fin n → K)) := by
      rintro _ ⟨z, ⟨hz1, hz2⟩, rfl⟩
      have hz2' : restrictCoord z = y := hz2
      have hx : inStratum T (matCoords.symm z) := hP hz1
      have hcc : chainCol (matCoords.symm z) hx.upper (Fin.last n) = T (Fin.last n) :=
        hx.chainCol_eq hx.upper (Fin.last n)
      have hmem := (boxColumn_spec (Matrix.toLinAlgEquiv' (flagBlock (matCoords.symm z) (Fin.last n)))
        (flagVec (matCoords.symm z) (Fin.last n))
        (strictlyUpper_isNilpotent (isStrictlyUpper_flagBlock hx.upper (Fin.last n)))).2
      have hbc : boxColumn (Matrix.toLinAlgEquiv' (flagBlock (matCoords.symm z) (Fin.last n)))
          (flagVec (matCoords.symm z) (Fin.last n))
          (strictlyUpper_isNilpotent (isStrictlyUpper_flagBlock hx.upper (Fin.last n)))
          = T (Fin.last n) := hcc
      rw [hbc] at hmem
      have hfb : flagBlock (matCoords.symm z) (Fin.last n) = matCoords.symm y := by
        rw [flagBlock_last, ← ofMatCoords_restrictCoord, hz2']
      rw [hfb] at hmem
      exact hmem
    rw [← hdim, ← hVdim]
    exact le_trans (affineDim_mono hsub) (le_of_eq (affineDim_submodule V))

/-- **The recursive decomposition.**  If `A_{T'}` is a finite union of locally
closed pieces, so is `A_T`: the closed part pulls back the closed part of
`A_{T'}` and adds `rank [y^c | y^{c-1} v] ≤ ρ_c`; the open part multiplies by one
`(ρ_{c-1}+1)`-minor of `[y^{c-1} | y^{c-2} v]`, which for `c = 1` is dropped. -/
theorem isAffineConstructible_stratumSet_succ (T : Fin (n + 1) → ℕ)
    (hne : (stratumSet T (K := K)).Nonempty)
    (hdec' : IsAffineConstructible (stratumSet (T ∘ Fin.castSucc) (K := K))) :
    IsAffineConstructible (stratumSet T (K := K)) := by
  classical
  obtain ⟨z₀, hz₀⟩ := hne
  obtain ⟨J, hJ, P, hPlc, hdec⟩ := hdec'
  choose Z q hZcl hPeq using hPlc
  have : Finite J := hJ
  simp only [hPeq] at hdec
  have hx₀ : inStratum T (matCoords.symm z₀) := hz₀
  have hy₀ : inStratum (T ∘ Fin.castSucc) (restrict (matCoords.symm z₀)) := inStratum_restrict hx₀
  set c : ℕ := T (Fin.last n) with hcdef
  have hc1 : 1 ≤ c := one_le_of_inStratum hx₀ (Fin.last n)
  set ρ : ℕ → ℕ := fun m => ((restrict (matCoords.symm z₀)) ^ m).rank with hρdef
  have hrank : ∀ {y : Matrix (Fin n) (Fin n) K}, inStratum (T ∘ Fin.castSucc) y →
      ∀ m : ℕ, (y ^ m).rank = ρ m := by
    intro y hy m
    show (y ^ m).rank = ((restrict (matCoords.symm z₀)) ^ m).rank
    have h1 := rank_pow_add_card_of_inStratum hy m
    have h2 := rank_pow_add_card_of_inStratum hy₀ m
    omega
  set W : J → Set (Fin (n + 1) × Fin (n + 1) → K) := fun j =>
    (upperSet K (n + 1) ∩ restrictCoord ⁻¹' (Z j)) ∩ minorZeroSet K n c (ρ c) with hWdef
  have hWcl : ∀ j, zclosure (W j) = W j := fun j =>
    zclosure_inter (zclosure_inter zclosure_upperSet
      (zclosure_preimage isPolyMap_restrictCoord (hZcl j))) zclosure_minorZeroSet
  have hWmem : ∀ (j : J) (z : Fin (n + 1) × Fin (n + 1) → K), z ∈ W j ↔
      (IsStrictlyUpper (matCoords.symm z) ∧ restrictCoord z ∈ Z j ∧
        (augLast (matCoords.symm z) c).rank ≤ ρ c) := by
    intro j z
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, h2, (mem_minorZeroSet_iff z).mp h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, h2⟩, (mem_minorZeroSet_iff z).mpr h3⟩
  -- the restriction of a point of the closed part, if the open part does not vanish
  have hrestr : ∀ (j : J) (z : Fin (n + 1) × Fin (n + 1) → K), restrictCoord z ∈ Z j →
      MvPolynomial.aeval (restrictCoord z) (q j) ≠ 0 →
      inStratum (T ∘ Fin.castSucc) (restrict (matCoords.symm z)) := by
    intro j z h1 h2
    have : restrictCoord z ∈ stratumSet (T ∘ Fin.castSucc) := by
      rw [hdec]
      exact Set.mem_iUnion.mpr ⟨j, h1, h2⟩
    exact this
  by_cases hc : c = 1
  · refine ⟨J, hJ,
      fun j => W j ∩ {y | MvPolynomial.aeval y (MvPolynomial.rename (renIdx n) (q j)) ≠ 0},
      fun j => ⟨W j, MvPolynomial.rename (renIdx n) (q j), hWcl j, rfl⟩, ?_⟩
    ext z
    constructor
    · intro hz
      have hx : inStratum T (matCoords.symm z) := hz
      have hres := inStratum_restrict hx
      have hrz : restrictCoord z ∈ stratumSet (T ∘ Fin.castSucc) := hres
      rw [hdec] at hrz
      obtain ⟨j, hj1, hj2⟩ := Set.mem_iUnion.mp hrz
      refine Set.mem_iUnion.mpr ⟨j, ?_, ?_⟩
      · rw [hWmem]
        refine ⟨hx.upper, hj1, ?_⟩
        have hle : chainCol (matCoords.symm z) hx.upper (Fin.last n) ≤ c :=
          le_of_eq (hx.chainCol_eq hx.upper (Fin.last n))
        have hrk := (chainCol_last_le_iff hx.upper hc1).mp hle
        rwa [hrank hres c] at hrk
      · rw [Set.mem_ofPred_eq, aeval_rename_renIdx]
        exact hj2
    · intro hz
      obtain ⟨j, hj1, hj2⟩ := Set.mem_iUnion.mp hz
      rw [hWmem] at hj1
      obtain ⟨hup, hZj, hrk⟩ := hj1
      rw [Set.mem_ofPred_eq, aeval_rename_renIdx] at hj2
      have hres := hrestr j z hZj hj2
      refine inStratum_of_restrict hup hres ?_
      have hle : chainCol (matCoords.symm z) hup (Fin.last n) ≤ c := by
        rw [chainCol_last_le_iff hup hc1, hrank hres c]
        exact hrk
      have hge : 1 ≤ chainCol (matCoords.symm z) hup (Fin.last n) := one_le_chainCol _ _ _
      omega
  · have hc2 : 2 ≤ c := by omega
    have hc1' : 1 ≤ c - 1 := by omega
    set s : ℕ := ρ (c - 1) + 1 with hsdef
    refine ⟨J × ((Fin s → Fin n) × (Fin s → Fin (n + 1))), inferInstance,
      (fun p => W p.1 ∩ {y | MvPolynomial.aeval y (MvPolynomial.rename (renIdx n) (q p.1) *
        minorPoly K n (c - 1) s p.2.1 p.2.2) ≠ 0}),
      (fun p => ⟨W p.1, MvPolynomial.rename (renIdx n) (q p.1) *
        minorPoly K n (c - 1) s p.2.1 p.2.2, hWcl p.1, rfl⟩), ?_⟩
    ext z
    constructor
    · intro hz
      have hx : inStratum T (matCoords.symm z) := hz
      have hres := inStratum_restrict hx
      have hrz : restrictCoord z ∈ stratumSet (T ∘ Fin.castSucc) := hres
      rw [hdec] at hrz
      obtain ⟨j, hj1, hj2⟩ := Set.mem_iUnion.mp hrz
      have hcc : chainCol (matCoords.symm z) hx.upper (Fin.last n) = c :=
        hx.chainCol_eq hx.upper (Fin.last n)
      have hnotle : ¬ ((augLast (matCoords.symm z) (c - 1)).rank ≤ ρ (c - 1)) := by
        rw [← hrank hres (c - 1)]
        intro h
        have := (chainCol_last_le_iff hx.upper hc1').mpr h
        omega
      obtain ⟨f, g, hfg⟩ := exists_submatrix_det_ne_zero (augLast (matCoords.symm z) (c - 1))
        (by omega : s ≤ (augLast (matCoords.symm z) (c - 1)).rank)
      refine Set.mem_iUnion.mpr ⟨(j, (f, g)), ?_, ?_⟩
      · rw [hWmem]
        refine ⟨hx.upper, hj1, ?_⟩
        have hle : chainCol (matCoords.symm z) hx.upper (Fin.last n) ≤ c := le_of_eq hcc
        have hrk := (chainCol_last_le_iff hx.upper hc1).mp hle
        rwa [hrank hres c] at hrk
      · rw [Set.mem_ofPred_eq, map_mul, aeval_rename_renIdx,
          show ∀ m s (f : Fin s → Fin n) (g : Fin s → Fin (n + 1)),
          MvPolynomial.aeval z (minorPoly K n m s f g) =
            ((augLast (matCoords.symm z) m).submatrix f g).det from
          fun m s f g => eval_minorPoly z m s f g]
        exact mul_ne_zero hj2 hfg
    · intro hz
      obtain ⟨⟨j, f, g⟩, hj1, hj2⟩ := Set.mem_iUnion.mp hz
      rw [hWmem] at hj1
      obtain ⟨hup, hZj, hrk⟩ := hj1
      rw [Set.mem_ofPred_eq, map_mul, aeval_rename_renIdx,
        show ∀ m s (f : Fin s → Fin n) (g : Fin s → Fin (n + 1)),
        MvPolynomial.aeval z (minorPoly K n m s f g) =
          ((augLast (matCoords.symm z) m).submatrix f g).det from
        fun m s f g => eval_minorPoly z m s f g] at hj2
      have hq := left_ne_zero_of_mul hj2
      have hm := right_ne_zero_of_mul hj2
      have hres := hrestr j z hZj hq
      refine inStratum_of_restrict hup hres ?_
      have hle : chainCol (matCoords.symm z) hup (Fin.last n) ≤ c := by
        rw [chainCol_last_le_iff hup hc1, hrank hres c]
        exact hrk
      have hbig : s ≤ (augLast (matCoords.symm z) (c - 1)).rank :=
        le_rank_of_submatrix_det_ne_zero _ f g hm
      have hnot : ¬ (chainCol (matCoords.symm z) hup (Fin.last n) ≤ c - 1) := by
        rw [chainCol_last_le_iff hup hc1', hrank hres (c - 1)]
        omega
      omega

/-- **The dimension step.**  Given that `A_T` is constructible, its dimension is at
most that of `A_{T'}` plus the fibre dimension.  This is the fibre-dimension inequality
on `K`-points (`Height.Geometry.affineDim_le_image_add_fibre_pts`) for the restriction map, with the
locus of `𝔸` produced by `exists_isConstructible_pts_eq`. -/
theorem affineDim_stratumSet_le_step [IsAlgClosed K] (T : Fin (n + 1) → ℕ)
    (hcon : IsAffineConstructible (stratumSet T (K := K))) (d : WithBot ℕ∞)
    (hd : affineDim (stratumSet (T ∘ Fin.castSucc) (K := K)) ≤ d) :
    affineDim (stratumSet T (K := K)) ≤ d +
      ((((n - (Finset.univ.filter fun i : Fin n => T i.castSucc = T (Fin.last n)).card : ℕ) :
        ℕ∞)) : WithBot ℕ∞) := by
  classical
  obtain ⟨Z, hZ, hZpts⟩ := exists_isConstructible_pts_eq hcon
  have hmain := affineDim_le_image_add_fibre_pts (restrictCoordPoly K n) hZ
    ((((n - (Finset.univ.filter fun i : Fin n => T i.castSucc = T (Fin.last n)).card : ℕ) :
      ℕ∞)) : WithBot ℕ∞) ?_
  · rw [aeval_restrictCoordPoly, hZpts] at hmain
    refine le_trans hmain (add_le_add ?_ le_rfl)
    refine le_trans (affineDim_mono ?_) hd
    rintro _ ⟨z, hz, rfl⟩
    exact inStratum_restrict hz
  · intro w
    rw [aeval_restrictCoordPoly, hZpts]
    exact affineDim_fibre_le T (fun _ hz => hz) w

/-- **The chain-strata dimension bound.**  For every column sequence `T`,
`dim A_T ≤ C(n,2) − n(T)`, together with the locally closed decomposition that
the induction needs. -/
theorem isAffineConstructible_and_affineDim_le [IsAlgClosed K] : ∀ (n : ℕ) (T : Fin n → ℕ),
    IsAffineConstructible (stratumSet T (K := K)) ∧
      affineDim (stratumSet T (K := K)) ≤
        (((n.choose 2 - nSeq T : ℕ) : ℕ∞) : WithBot ℕ∞) := by
  intro n
  induction n with
  | zero =>
      intro T
      have hall : stratumSet T (K := K) = Set.univ := by
        ext z
        simp only [Set.mem_univ, iff_true]
        exact ⟨fun i => i.elim0, fun i => i.elim0⟩
      constructor
      · rw [hall]
        exact (IsLocClosed.of_zclosure zclosure_univ).isConstructible
      · rw [hall, affineDim_univ]
        simp
  | succ n ih =>
      intro T
      rcases Set.eq_empty_or_nonempty (stratumSet T (K := K)) with hempty | hne
      · constructor
        · refine ⟨Empty, inferInstance, Empty.elim, fun j => j.elim, ?_⟩
          rw [hempty]
          ext z
          simp
        · rw [hempty, affineDim_empty]
          exact bot_le
      · obtain ⟨z₀, hz₀⟩ := hne
        have hx₀ : inStratum T (matCoords.symm z₀) := hz₀
        have hy₀ : inStratum (T ∘ Fin.castSucc) (restrict (matCoords.symm z₀)) :=
          inStratum_restrict hx₀
        obtain ⟨hdec', hdim'⟩ := ih (T ∘ Fin.castSucc)
        have hdec : IsAffineConstructible (stratumSet T (K := K)) :=
          isAffineConstructible_stratumSet_succ T ⟨z₀, hz₀⟩ hdec'
        refine ⟨hdec, ?_⟩
        set b : ℕ := (Finset.univ.filter fun i : Fin n => T i.castSucc = T (Fin.last n)).card
          with hbdef
        have hstep := affineDim_stratumSet_le_step T hdec _ hdim'
        refine le_trans hstep ?_
        -- the arithmetic
        have hbn : b ≤ n := by
          have := Finset.card_filter_le (Finset.univ : Finset (Fin n))
            (fun i : Fin n => T i.castSucc = T (Fin.last n))
          simpa [hbdef] using this
        have hnSeq : nSeq T = nSeq (T ∘ Fin.castSucc) + b := by
          refine nSeq_succ T (one_le_of_inStratum hx₀ (Fin.last n)) ?_ ?_
          · have := le_succ_of_inStratum hx₀ (Fin.last n)
            simpa using this
          · intro i
            have h1 := le_succ_of_inStratum hy₀ i
            have h2 := i.isLt
            have h3 : (T ∘ Fin.castSucc) i = T i.castSucc := rfl
            omega
        have hprev : nSeq (T ∘ Fin.castSucc) ≤ n.choose 2 :=
          nSeq_le_choose_two n _ (fun i => one_le_of_inStratum hy₀ i)
            (fun i => le_succ_of_inStratum hy₀ i)
        have hch : (n + 1).choose 2 = n.choose 2 + n := choose_two_succ n
        have harith : (n.choose 2 - nSeq (T ∘ Fin.castSucc)) + (n - b)
            = (n + 1).choose 2 - nSeq T := by omega
        rw [← harith]
        push_cast
        exact le_rfl

end Induction

/-! ## The strata bound over `Kbar`, and the Springer bound -/

section Statement

variable {K : Type} [Field K] {n : ℕ}

/-- `𝔫 ∩ O_M` is covered by the finitely many chain strata. -/
theorem nilOrbit_subset_iUnion (M : Matrix (Fin n) (Fin n) K) :
    nilOrbit M ⊆ ⋃ S : Fin n → Fin (n + 1),
      (stratumSet (fun i => (S i : ℕ)) ∩ {z | matCoords.symm z ∈ conjOrbit M}) := by
  rintro _ ⟨x, ⟨hxn, hxo⟩, rfl⟩
  have hup : IsStrictlyUpper x := (mem_standardNilradical_iff K n x).mp hxn
  refine Set.mem_iUnion.mpr ⟨fun i => ⟨chainCol x hup i, Nat.lt_succ_of_le (chainCol_le_card hup i)⟩,
    ⟨hup, fun i => rfl⟩, ?_⟩
  show matCoords.symm (matCoords x) ∈ conjOrbit M
  rwa [matCoords.symm_apply_apply]

/-- **`lem:springer-dim`, first half**: `dim (𝔫 ∩ O_M) ≤ C(n,2) − n(λ)`. -/
theorem affineDim_nilOrbit_le [IsAlgClosed K] (M : Matrix (Fin n) (Fin n) K) :
    affineDim (nilOrbit M) ≤ (((n.choose 2 - nOf M : ℕ) : ℕ∞) : WithBot ℕ∞) := by
  classical
  refine le_trans (affineDim_mono (nilOrbit_subset_iUnion M)) ?_
  rw [affineDim_iUnion]
  refine iSup_le fun S => ?_
  set T : Fin n → ℕ := fun i => (S i : ℕ) with hT
  rcases Set.eq_empty_or_nonempty
    (stratumSet T (K := K) ∩ {z | matCoords.symm z ∈ conjOrbit M}) with hempty | ⟨z, hz⟩
  · rw [hempty, affineDim_empty]
    exact bot_le
  · have hx : inStratum T (matCoords.symm z) := hz.1
    have horb : matCoords.symm z ∈ conjOrbit M := hz.2
    have hnOf : nOf M = nSeq T := by
      rw [← nOf_of_mem_conjOrbit horb, nOf_of_inStratum hx]
    rw [hnOf]
    exact le_trans (affineDim_mono Set.inter_subset_left)
      (isAffineConstructible_and_affineDim_le n T).2

end Statement

section Kbar

open QSteenrod Height.Steenrod

variable (p r n : ℕ) [Fact p.Prime]

/-- **`prop:springer-bound`** (the case `O = O_N`): for a rational nilpotent `N`,
the triangularizable partners of `N` inside its orbit form a set of dimension at
most `n(n-1)/2` — the sweep over the Springer fibre, whose dimension
`lem:springer-dim` bounds through the chain strata (`affineDim_nilOrbit_le`). -/
theorem springer (N : Matrix (Fin n) (Fin n) (GaloisField p r)) (hN : IsNilpotent N) :
    affineDim (matCoords ''
        (triangularizablePartnerLocus n (ext p r n N) ∩ conjOrbit (ext p r n N))) ≤
      (((n.choose 2 : ℕ) : ℕ∞) : WithBot ℕ∞) :=
  affineDim_triangularizablePartner_le (isNilpotent_ext p r n hN) (affineDim_nilOrbit_le _)

end Kbar

end Height.Chain
