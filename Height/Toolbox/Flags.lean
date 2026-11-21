import Mathlib.Data.Fintype.Prod
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Flags, Borels and nilradicals in matrix form (`defn:flagless`)

The paper's proof works with the complete flags `F ∈ Fl`, their Borel
subalgebras `𝔟_F` and nilradicals `𝔫_F`; `defn:flagless` calls a nilpotent
pencil triangularizable when it lies in some `𝔫_F`.  Rather than construct a
flag variety we use the standard coordinate flag and its `GL_n`-conjugates,
which is the same thing over a field.

This file is the whole linear-algebra model:

* the standard flag `F_k = span{e_0, …, e_{k-1}}`, its nilradical
  `𝔫 = {x | x_{ij} = 0 for j ≤ i}` and Borel `𝔟` (upper triangular), each
  described both entrywise and by its action on the flag;
* the dimension counts `dim F_k = k`, `dim 𝔫 = C(n,2)` and
  `dim 𝔟 = C(n,2) + n` used in `prop:springer-bound`;
* the sandwich `𝔟 · 𝔫 · 𝔟 ⊆ 𝔫`, the commutator `[𝔟, 𝔟] ⊆ 𝔫` and the trace
  orthogonality `trace(𝔟 · 𝔫) = 0` (the flag form of
  `lem:parabolic-field` (iii));
* the conjugates `𝔫_F`, `𝔟_F` for `F = g · (standard flag)`, with the same
  statements transported.

Everything that mentions nilpotence or `NilpotentPencil` lives in
`Height/Steenrod/FlagPencils.lean`, so that `Height/Toolbox` depends on
nothing in `Height/Steenrod`.
-/

namespace Height.Toolbox

universe u

variable (K : Type u) [Field K] (n : ℕ)

/-! ## The standard flag and its nilradical -/

/-- The strictly upper-triangular matrices, i.e. the nilradical attached to
the standard coordinate flag. -/
def standardNilradical : Submodule K (Matrix (Fin n) (Fin n) K) where
  carrier := {M | ∀ i j, j ≤ i → M i j = 0}
  zero_mem' := by simp
  add_mem' := by
    intro A B hA hB i j hji
    simp [hA i j hji, hB i j hji]
  smul_mem' := by
    intro a A hA i j hji
    simp [hA i j hji]

/-- The `k`th member of the standard coordinate flag: vectors supported in
coordinates strictly below `k`. -/
def standardFlag (k : ℕ) : Submodule K (Fin n → K) where
  carrier := {v | ∀ i, k ≤ i.1 → v i = 0}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw i hi
    simp [hv i hi, hw i hi]
  smul_mem' := by
    intro a v hv i hi
    simp [hv i hi]

@[simp] theorem mem_standardFlag_iff (k : ℕ) (v : Fin n → K) :
    v ∈ standardFlag K n k ↔ ∀ i, k ≤ i.1 → v i = 0 :=
  Iff.rfl

theorem standardFlag_mono : Monotone (standardFlag K n) := by
  intro k l hkl v hv i hli
  exact hv i (hkl.trans hli)

/-- A matrix lowers the standard coordinate flag by one step. -/
def LowersStandardFlag (M : Matrix (Fin n) (Fin n) K) : Prop :=
  ∀ k, ∀ v ∈ standardFlag K n (k + 1),
    M.mulVec v ∈ standardFlag K n k

/-- The `j`th standard basis vector lies in the flag member just above `j`.  Both
descriptions below read an entry of `M` off `M.mulVec` at this vector. -/
theorem single_mem_standardFlag (j : Fin n) :
    (Pi.single j 1 : Fin n → K) ∈ standardFlag K n (j.1 + 1) := by
  intro l hjl
  have hlj : l ≠ j := by
    intro h
    subst l
    omega
  simp [hlj]

/-- Entries vanishing `s` places below the diagonal carry `V (k + s)` into `V k`.  `s = 1`
is the nilradical direction of `mem_standardNilradical_iff_lowersStandardFlag`, `s = 0` the
Borel direction of `mem_standardBorel_iff_preservesStandardFlag`: one calculation, not two. -/
theorem mulVec_mem_standardFlag {M : Matrix (Fin n) (Fin n) K} {s : ℕ}
    (hM : ∀ i j : Fin n, j.1 < i.1 + s → M i j = 0) (k : ℕ)
    {v : Fin n → K} (hv : v ∈ standardFlag K n (k + s)) :
    M.mulVec v ∈ standardFlag K n k := by
  intro i hki
  rw [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hkj : k + s ≤ j.1
  · rw [hv j hkj, mul_zero]
  · rw [hM i j (by omega), zero_mul]

/-- The entrywise and flag-lowering descriptions of the standard nilradical
agree. -/
theorem mem_standardNilradical_iff_lowersStandardFlag
    (M : Matrix (Fin n) (Fin n) K) :
    M ∈ standardNilradical K n ↔ LowersStandardFlag K n M := by
  constructor
  · exact fun hM k _ hv =>
      mulVec_mem_standardFlag K n (fun _ _ hij => hM _ _ (Nat.lt_succ_iff.mp hij)) k hv
  · intro hM i j hji
    simpa using hM j.1 _ (single_mem_standardFlag K n j) i hji

@[simp] theorem mem_standardNilradical_iff
    (M : Matrix (Fin n) (Fin n) K) :
    M ∈ standardNilradical K n ↔ ∀ i j, j ≤ i → M i j = 0 :=
  Iff.rfl

/-- A matrix in the standard nilradical is upper triangular. -/
theorem isUpperTriangular_of_mem_standardNilradical
    {M : Matrix (Fin n) (Fin n) K}
    (hM : M ∈ standardNilradical K n) : M.IsUpperTriangular := by
  intro i j hji
  exact hM i j hji.le

/-! ## Dimensions of the standard coordinate flag -/

/-- Once the index reaches `n`, the standard coordinate subspace is the
whole ambient space. -/
theorem standardFlag_eq_top_of_card_le (k : ℕ) (hk : n ≤ k) :
    standardFlag K n k = ⊤ := by
  ext v
  simp only [mem_standardFlag_iff, Submodule.mem_top, iff_true]
  intro i hki
  exact (Nat.not_le_of_lt i.2 (hk.trans hki)).elim

/-! ## Dimension of the standard nilradical -/

/-- Indices of entries strictly above the diagonal. -/
abbrev StrictUpperIndex := {ij : Fin n × Fin n // ij.1 < ij.2}

/-! ## The standard Borel subalgebra -/

/-- Upper-triangular matrices, as the subalgebra preserving the standard
coordinate flag. -/
def standardBorel : Subalgebra K (Matrix (Fin n) (Fin n) K) where
  carrier := {M | ∀ i j, j < i → M i j = 0}
  zero_mem' := by simp
  one_mem' := by
    intro i j hji
    simp [ne_of_gt hji]
  add_mem' := by
    intro A B hA hB i j hji
    simp [hA i j hji, hB i j hji]
  mul_mem' := by
    intro A B hA hB i j hji
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k hk
    by_cases hki : k < i
    · rw [hA i k hki, zero_mul]
    · have hik : i ≤ k := not_lt.mp hki
      rw [hB k j (hji.trans_le hik), mul_zero]
  algebraMap_mem' := by
    intro a i j hji
    rw [Matrix.algebraMap_matrix_apply]
    split <;> simp_all

/-- A matrix preserves every member of the standard coordinate flag. -/
def PreservesStandardFlag (M : Matrix (Fin n) (Fin n) K) : Prop :=
  ∀ k, ∀ v ∈ standardFlag K n k, M.mulVec v ∈ standardFlag K n k

/-- The entrywise and flag-preserving descriptions of the standard Borel
agree. -/
theorem mem_standardBorel_iff_preservesStandardFlag
    (M : Matrix (Fin n) (Fin n) K) :
    M ∈ standardBorel K n ↔ PreservesStandardFlag K n M := by
  constructor
  · exact fun hM k _ hv => mulVec_mem_standardFlag K n (s := 0) (fun _ _ hij => hM _ _ hij) k hv
  · intro hM i j hji
    simpa using hM (j.1 + 1) _ (single_mem_standardFlag K n j) i (by omega)

/-- Left multiplication by a flag-preserving matrix preserves the standard
nilradical. -/
theorem standardBorel_mul_standardNilradical
    {A Q : Matrix (Fin n) (Fin n) K}
    (hA : A ∈ standardBorel K n)
    (hQ : Q ∈ standardNilradical K n) :
    A * Q ∈ standardNilradical K n := by
  rw [mem_standardNilradical_iff_lowersStandardFlag]
  intro k v hv
  rw [← Matrix.mulVec_mulVec]
  exact (mem_standardBorel_iff_preservesStandardFlag K n A).mp hA k _
    ((mem_standardNilradical_iff_lowersStandardFlag K n Q).mp hQ k v hv)

/-- Right multiplication by a flag-preserving matrix preserves the standard
nilradical. -/
theorem standardNilradical_mul_standardBorel
    {Q A : Matrix (Fin n) (Fin n) K}
    (hQ : Q ∈ standardNilradical K n)
    (hA : A ∈ standardBorel K n) :
    Q * A ∈ standardNilradical K n := by
  rw [mem_standardNilradical_iff_lowersStandardFlag]
  intro k v hv
  rw [← Matrix.mulVec_mulVec]
  exact (mem_standardNilradical_iff_lowersStandardFlag K n Q).mp hQ k _
    ((mem_standardBorel_iff_preservesStandardFlag K n A).mp hA (k + 1) v hv)

/-- The standard Borel normalizes its nilradical.  Invertibility is not
needed for this stronger sandwich statement. -/
theorem standardBorel_mul_nilradical_mul_standardBorel
    {A Q B : Matrix (Fin n) (Fin n) K}
    (hA : A ∈ standardBorel K n)
    (hQ : Q ∈ standardNilradical K n)
    (hB : B ∈ standardBorel K n) :
    A * Q * B ∈ standardNilradical K n :=
  standardNilradical_mul_standardBorel K n
    (standardBorel_mul_standardNilradical K n hA hQ) hB

/-! ## Dimension of the standard Borel -/

/-- Indices on or above the diagonal. -/
abbrev UpperIndex := {ij : Fin n × Fin n // ij.1 ≤ ij.2}

/-- Upper-triangular indices split into strict-upper indices and diagonal
indices. -/
def upperIndexEquiv : UpperIndex n ≃ StrictUpperIndex n ⊕ Fin n where
  toFun ij := if h : ij.1.1 < ij.1.2 then Sum.inl ⟨ij.1, h⟩ else Sum.inr ij.1.1
  invFun s := match s with
    | Sum.inl ij => ⟨ij.1, ij.2.le⟩
    | Sum.inr i => ⟨(i, i), le_rfl⟩
  left_inv := by
    rintro ⟨⟨i, j⟩, hij⟩
    by_cases hlt : i < j
    · simp [hlt]
    · have hji : j ≤ i := not_lt.mp hlt
      have h : i = j := le_antisymm hij hji
      subst j
      simp
  right_inv := by
    intro s
    rcases s with ij | i
    · simp [ij.2]
    · simp

/-- An upper-triangular matrix is freely determined by its entries on or
above the diagonal. -/
noncomputable def standardBorelEquiv :
    standardBorel K n ≃ₗ[K] (UpperIndex n → K) where
  toFun A ij := A.1 ij.1.1 ij.1.2
  invFun f :=
    ⟨fun i j => if h : i ≤ j then f ⟨(i, j), h⟩ else 0, by
      intro i j hji
      simp [not_le_of_gt hji]⟩
  left_inv A := by
    apply Subtype.ext
    funext i j
    by_cases hij : i ≤ j
    · simp [hij]
    · simp [hij, A.2 i j (not_le.mp hij)]
  right_inv f := by
    funext ⟨⟨i, j⟩, hij⟩
    simp [hij]
  map_add' A B := by
    funext ij
    rfl
  map_smul' a A := by
    funext ij
    rfl

/-- The standard Borel has dimension `choose n 2 + n`. -/
theorem finrank_standardBorel :
    Module.finrank K (standardBorel K n) = n.choose 2 + n := by
  rw [(standardBorelEquiv K n).finrank_eq, Module.finrank_pi,
    Fintype.card_congr (upperIndexEquiv n), Fintype.card_sum]
  have hs : Fintype.card (StrictUpperIndex n) = n.choose 2 := by
    rw [Fintype.card_subtype]
    simpa using (Fintype.card_product_filter_lt (α := Fin n))
  rw [hs, Fintype.card_fin]

/-! ## Units of the standard Borel -/

/-! ## Conjugates of the standard nilradical -/

/-- Conjugation by an invertible matrix as a linear equivalence of the full
matrix space. -/
def matrixConjugationLinearEquiv
    (g : (Matrix (Fin n) (Fin n) K)ˣ) :
    Matrix (Fin n) (Fin n) K ≃ₗ[K] Matrix (Fin n) (Fin n) K where
  toFun A := (g : Matrix (Fin n) (Fin n) K) * A *
    (↑(g⁻¹) : Matrix (Fin n) (Fin n) K)
  invFun A := (↑(g⁻¹) : Matrix (Fin n) (Fin n) K) * A *
    (g : Matrix (Fin n) (Fin n) K)
  left_inv A := by simp [Matrix.mul_assoc]
  right_inv A := by simp [Matrix.mul_assoc]
  map_add' A B := by simp [mul_add, add_mul]
  map_smul' a A := by
    rw [mul_smul_comm, smul_mul_assoc]
    simp

@[simp] theorem matrixConjugationLinearEquiv_apply
    (g : (Matrix (Fin n) (Fin n) K)ˣ)
    (A : Matrix (Fin n) (Fin n) K) :
    matrixConjugationLinearEquiv K n g A =
      (g : Matrix (Fin n) (Fin n) K) * A *
        (↑(g⁻¹) : Matrix (Fin n) (Fin n) K) :=
  rfl

/-- The nilradical obtained by conjugating the standard nilradical by `g`. -/
def conjugateNilradical
    (g : (Matrix (Fin n) (Fin n) K)ˣ) :
    Submodule K (Matrix (Fin n) (Fin n) K) :=
  (standardNilradical K n).map
    (matrixConjugationLinearEquiv K n g).toLinearMap

/-- Membership in a conjugate nilradical can be tested after conjugating back
to the standard flag. -/
theorem mem_conjugateNilradical_iff
    (g : (Matrix (Fin n) (Fin n) K)ˣ)
    (A : Matrix (Fin n) (Fin n) K) :
    A ∈ conjugateNilradical K n g ↔
      (↑(g⁻¹) : Matrix (Fin n) (Fin n) K) * A *
          (g : Matrix (Fin n) (Fin n) K) ∈ standardNilradical K n := by
  rw [conjugateNilradical, Submodule.mem_map]
  constructor
  · rintro ⟨B, hB, rfl⟩
    simpa [conjugateNilradical, Matrix.mul_assoc] using hB
  · intro hA
    refine ⟨(matrixConjugationLinearEquiv K n g).symm A, hA, ?_⟩
    exact (matrixConjugationLinearEquiv K n g).apply_symm_apply A

/-! ## Borels and nilradicals in an arbitrary basis -/

end Height.Toolbox
