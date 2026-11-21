import Height.Chain.Conditional
import Height.Geometry.Dimension.LocClosed

/-!
# Finite characterisations of the pencil conditions

`GenericType` and `HasMultidegree` are stated with quantifiers that range over infinitely
many parameters (`∀ t ∉ F` for an unspecified finite `F`; `∀ e ≥ e₀` for an
unspecified `e₀`).  Neither shape can be read off finitely many polynomial
equations and inequations in the entries of `(N, M)`, which is what the loci of
`Chain/Incidence.lean` need in order to be constructible.

This file replaces the first of the two by a finite condition.

## The rank dictionary

`HasType X τ` is a statement about the numbers `conj X m`; telescoping turns it
into one about the ranks of the powers, and beyond `k = n` nothing new happens:

* `finrank_ker_add_rank_pow`: rank–nullity for `X ^ k`;
* `hasType_iff_rank`: `HasType X τ ↔ ∀ k ≥ 1, rank (X ^ k) + m_k τ = n`;
* `hasType_iff_rank_le`: the same with `k ≤ n`, a *finite* conjunction.

## The generic type by minors

`PencilRankGe N M k r` says that some `r × r` minor of the `k`-th power of the
pencil `N + t M`, read as a matrix over `K[t]` (`pencilPoly`), is a
nonzero polynomial; this is exactly "the generic rank of `(N + tM)^k` is at
least `r`" (`pencilRankGe_of_le_rank` and `exists_finset_le_rank_of_pencilRankGe`,
the two directions).  A nonzero polynomial has
finitely many roots, so the condition holds *off a finite set of parameters*,
and that is what turns a statement about generic `t` into a finite one:

```
genericType_iff :
  GenericType N M τ ↔ ∀ k, 1 ≤ k → k ≤ n →
    PencilRankGe N M k (n - mk τ k) ∧ ¬ PencilRankGe N M k (n - mk τ k + 1)
```

over an infinite field.  Each clause is a finite disjunction (resp. conjunction)
of conditions "a specific coefficient of a specific minor is (non)zero", i.e. a
finite union of `Height.Geometry.IsLocClosed` sets in the entries of `(N, M)`:
that is the sense in which the pencil loci are constructible.

**The multidegree half** is not in this file.  The characterisation
`HasMultidegree N M τ d ↔` one linear condition at `e = n²`
(`hasMultidegree_iff_at`, `Chain/Multidegree.lean`) needs the
generator degrees `c_i` of the kernel flag to be bounded by `n²`, which is
`lem:kernel-flag`(1)+(3), i.e. exactly the existence half of
`Chain.exists_multidegree`.  What *is* recorded here is the rigidity that reduces
the multidegree condition to a finite one once existence is known:
`hasMultidegree_unique` (two multidegrees for the same generic type agree) and
`hasMultidegree_of_agree` (agreement in every degree `k ≥ 1` suffices).  With
`exists_multidegree` in hand these turn "`(N, M)` has multidegree `d`" into the
equality of `d` with the multidegree computed from one Hilbert value.
-/

namespace Height.Chain

open Height.Pencil

open Matrix Height.Toolbox Height.Steenrod

universe u

variable {K : Type u} [Field K] {n : ℕ}

/-! ### Rank–nullity for the powers of a matrix -/

/-- Rank–nullity for `X ^ k`, in the form `HasType` uses. -/
theorem finrank_ker_add_rank_pow (X : Matrix (Fin n) (Fin n) K) (k : ℕ) :
    Module.finrank K (LinearMap.ker
        ((Matrix.toLinAlgEquiv' X : (Fin n → K) →ₗ[K] (Fin n → K)) ^ k))
      + Matrix.rank (X ^ k) = n := by
  have hpow : (Matrix.toLinAlgEquiv' X : (Fin n → K) →ₗ[K] (Fin n → K)) ^ k
      = Matrix.toLinAlgEquiv' (X ^ k) := (map_pow _ _ _).symm
  have htol : (Matrix.toLinAlgEquiv' (X ^ k) : (Fin n → K) →ₗ[K] (Fin n → K))
      = (X ^ k).mulVecLin := rfl
  have hrn := LinearMap.finrank_range_add_finrank_ker ((X ^ k).mulVecLin)
  have hdim : Module.finrank K (Fin n → K) = n := by simp
  rw [hdim] at hrn
  rw [hpow, htol]
  show Module.finrank K (LinearMap.ker ((X ^ k).mulVecLin))
    + Module.finrank K (LinearMap.range ((X ^ k).mulVecLin)) = n
  omega

/-- `m_k(τ) ≤ n`. -/
theorem mk_le (τ : Nat.Partition n) (k : ℕ) : mk τ k ≤ n := by
  by_cases hk : k ≤ n
  · calc mk τ k ≤ ∑ m ∈ Finset.Icc 1 n, conjPart τ m :=
          Finset.sum_le_sum_of_subset (Finset.Icc_subset_Icc_right hk)
      _ = n := Height.Pencil.sum_conjPart τ
  · exact le_of_eq (mk_eq_of_le (by omega))

@[simp] theorem mk_zero (τ : Nat.Partition n) : mk τ 0 = 0 := by
  simp [mk]

/-- `m_k = m_{k-1} + τ'_k` for `k ≥ 1`. -/
theorem mk_succ (τ : Nat.Partition n) (k : ℕ) :
    mk τ (k + 1) = mk τ k + conjPart τ (k + 1) := by
  rw [mk, mk, Finset.sum_Icc_succ_top (by omega)]

/-! ### `HasType` through the ranks of the powers -/

/-- If the rank equations hold then the kernel dimensions are the `m_k`. -/
theorem finrank_ker_pow_eq_mk {X : Matrix (Fin n) (Fin n) K} {τ : Nat.Partition n}
    (h : ∀ k, 1 ≤ k → Matrix.rank (X ^ k) + mk τ k = n) (k : ℕ) :
    Module.finrank K (LinearMap.ker
        ((Matrix.toLinAlgEquiv' X : (Fin n → K) →ₗ[K] (Fin n → K)) ^ k)) = mk τ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [mk_zero, pow_zero, Module.End.one_eq_id, LinearMap.ker_id, finrank_bot]
  · have h1 := finrank_ker_add_rank_pow X k
    have h2 := h k hk
    omega

/-- **The rank dictionary.**  A matrix has Jordan type `τ` exactly when the ranks
of its powers are the ones `τ` prescribes. -/
theorem hasType_iff_rank {X : Matrix (Fin n) (Fin n) K} {τ : Nat.Partition n} :
    HasType X τ ↔ ∀ k, 1 ≤ k → Matrix.rank (X ^ k) + mk τ k = n := by
  constructor
  · intro h k _
    exact rank_pow_add_mk_of_hasType h k
  · intro h m hm
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    show Module.finrank K (LinearMap.ker
        ((Matrix.toLinAlgEquiv' X : (Fin n → K) →ₗ[K] (Fin n → K)) ^ (j + 1)))
      - Module.finrank K (LinearMap.ker
        ((Matrix.toLinAlgEquiv' X : (Fin n → K) →ₗ[K] (Fin n → K)) ^ (j + 1 - 1)))
      = conjPart τ (j + 1)
    rw [show j + 1 - 1 = j from rfl, finrank_ker_pow_eq_mk h, finrank_ker_pow_eq_mk h,
      mk_succ]
    omega

/-- The same, as a *finite* conjunction: nothing new happens past `k = n`. -/
theorem hasType_iff_rank_le {X : Matrix (Fin n) (Fin n) K} {τ : Nat.Partition n} :
    HasType X τ ↔ ∀ k, 1 ≤ k → k ≤ n → Matrix.rank (X ^ k) + mk τ k = n := by
  rw [hasType_iff_rank]
  refine ⟨fun h k hk _ => h k hk, fun h k hk => ?_⟩
  by_cases hkn : k ≤ n
  · exact h k hk hkn
  · -- past `n` the rank of the power has already dropped to zero
    have hkn' : n ≤ k := by omega
    rw [mk_eq_of_le hkn']
    have hle : Matrix.rank (X ^ k) ≤ Matrix.rank (X ^ n) := by
      rw [show k = n + (k - n) by omega, pow_add]
      exact Matrix.rank_mul_le_left _ _
    rcases Nat.eq_zero_or_pos n with hn0 | hn
    · have hw := Matrix.rank_le_width (X ^ k)
      omega
    · have h1 := h n hn le_rfl
      have hmk : mk τ n = n := by
        rw [mk]; exact Height.Pencil.sum_conjPart τ
      omega

/-! ### The generic rank of the pencil, by minors -/

/-- The generic rank of `(N + tM)^k` is at least `r`: some `r × r` minor of the
`k`-th power of `pencilPoly N M` is a nonzero polynomial. -/
def PencilRankGe (N M : Matrix (Fin n) (Fin n) K) (k r : ℕ) : Prop :=
  ∃ f g : Fin r → Fin n, ((pencilPoly N M ^ k).submatrix f g).det ≠ 0

/-- A single parameter at which the rank is at least `r` witnesses
`PencilRankGe`. -/
theorem pencilRankGe_of_le_rank {N M : Matrix (Fin n) (Fin n) K} {k r : ℕ} (t : K)
    (h : r ≤ Matrix.rank ((N + t • M) ^ k)) : PencilRankGe N M k r := by
  obtain ⟨f, g, hfg⟩ := Height.Toolbox.exists_submatrix_det_ne_zero ((N + t • M) ^ k) h
  refine ⟨f, g, fun hzero => hfg ?_⟩
  rw [← det_submatrix_pencilPoly_eval N M f g k t, hzero, Polynomial.eval_zero]

/-- `PencilRankGe` gives the rank bound off a finite set of parameters. -/
theorem exists_finset_le_rank_of_pencilRankGe {N M : Matrix (Fin n) (Fin n) K} {k r : ℕ}
    (h : PencilRankGe N M k r) :
    ∃ F : Finset K, ∀ t : K, t ∉ F → r ≤ Matrix.rank ((N + t • M) ^ k) := by
  classical
  obtain ⟨f, g, hQ⟩ := h
  refine ⟨(((pencilPoly N M ^ k).submatrix f g).det).roots.toFinset, fun t ht => ?_⟩
  refine Height.Toolbox.le_rank_of_submatrix_det_ne_zero _ f g ?_
  rw [← det_submatrix_pencilPoly_eval N M f g k t]
  intro hzero
  exact ht (Multiset.mem_toFinset.2 (Polynomial.mem_roots'.2 ⟨hQ, hzero⟩))

/-- Failure of `PencilRankGe` bounds the rank at *every* parameter. -/
theorem rank_lt_of_not_pencilRankGe {N M : Matrix (Fin n) (Fin n) K} {k r : ℕ}
    (h : ¬ PencilRankGe N M k r) (t : K) : Matrix.rank ((N + t • M) ^ k) < r := by
  by_contra hcon
  exact h (pencilRankGe_of_le_rank t (by omega))

/-! ### The finite characterisation of the generic type -/

/-- **The generic type by minors.**  Over an infinite field the generic type of a
pencil is pinned down by finitely many minor conditions on the entries of
`(N, M)`. -/
theorem genericType_iff [Infinite K] {N M : Matrix (Fin n) (Fin n) K}
    {τ : Nat.Partition n} :
    GenericType N M τ ↔ ∀ k, 1 ≤ k → k ≤ n →
      PencilRankGe N M k (n - mk τ k) ∧ ¬ PencilRankGe N M k (n - mk τ k + 1) := by
  classical
  constructor
  · rintro ⟨F, hF⟩ k hk1 hkn
    have hrank : ∀ t : K, t ∉ F → Matrix.rank ((N + t • M) ^ k) = n - mk τ k := by
      intro t ht
      have h1 := rank_pow_add_mk_of_hasType (hF t ht) k
      have h2 := mk_le τ k
      omega
    obtain ⟨t₀, ht₀⟩ := Set.Infinite.nonempty ((F : Set K).toFinite.infinite_compl)
    have ht₀' : t₀ ∉ F := by simpa using ht₀
    refine ⟨pencilRankGe_of_le_rank t₀ (le_of_eq (hrank t₀ ht₀').symm), ?_⟩
    rintro ⟨f, g, hQ⟩
    set Q : Polynomial K := ((pencilPoly N M ^ k).submatrix f g).det with hQdef
    obtain ⟨t₁, ht₁⟩ := Set.Infinite.nonempty
      ((((F ∪ Q.roots.toFinset) : Finset K) : Set K).toFinite.infinite_compl)
    have ht₁' : t₁ ∉ F ∪ Q.roots.toFinset := by simpa using ht₁
    have ht₁F : t₁ ∉ F := fun h => ht₁' (Finset.mem_union_left _ h)
    have ht₁Q : Polynomial.eval t₁ Q ≠ 0 := fun h =>
      ht₁' (Finset.mem_union_right _ (Multiset.mem_toFinset.2
        (Polynomial.mem_roots'.2 ⟨hQ, h⟩)))
    have hge : n - mk τ k + 1 ≤ Matrix.rank ((N + t₁ • M) ^ k) := by
      refine Height.Toolbox.le_rank_of_submatrix_det_ne_zero _ f g ?_
      rw [← det_submatrix_pencilPoly_eval N M f g k t₁]
      exact ht₁Q
    rw [hrank t₁ ht₁F] at hge
    omega
  · intro h
    -- a finite set of parameters off which every rank is the generic one
    have hex : ∀ k : ℕ, ∃ F : Finset K, ∀ t : K, t ∉ F →
        n - mk τ k ≤ Matrix.rank ((N + t • M) ^ k) := by
      intro k
      by_cases hk : 1 ≤ k ∧ k ≤ n
      · exact exists_finset_le_rank_of_pencilRankGe (h k hk.1 hk.2).1
      · refine ⟨∅, fun t _ => ?_⟩
        rcases Nat.eq_zero_or_pos k with rfl | hk1
        · rw [mk_zero, pow_zero, Nat.sub_zero]
          have : Matrix.rank (1 : Matrix (Fin n) (Fin n) K) = n := by simp
          omega
        · have hkn : n < k := by omega
          rw [mk_eq_of_le (le_of_lt hkn)]
          simp
    choose Fk hFk using hex
    refine ⟨(Finset.range (n + 1)).biUnion Fk, fun t ht => ?_⟩
    rw [hasType_iff_rank_le]
    intro k hk1 hkn
    have htk : t ∉ Fk k := by
      intro hmem
      exact ht (Finset.mem_biUnion.2 ⟨k, Finset.mem_range.2 (by omega), hmem⟩)
    have hge := hFk k t htk
    have hlt := rank_lt_of_not_pencilRankGe (h k hk1 hkn).2 t
    have hmk := mk_le τ k
    omega

/-! ### The type of the member at infinity

`HasType M τ` — the member of the pencil at infinity has the generic type — is
the hypothesis of `Chain.tangentDatum` that no coordinate description of the
locus makes visible.  On the locus it is an *open* condition: one half of
`hasType_iff_rank_le` is automatic, because `M` is the member of the swapped
pencil at the parameter `0` and every rank of a member is at most the generic
rank; so only the nonvanishing of one minor of `M ^ k` per `k` is at issue. -/

/-- **The member at infinity is a degeneration of the generic member.**  For a pencil
of generic type `τ`, `rank (M ^ k) ≤ n − m_k(τ)`: `M = M + 0 · N` is a member of the
swapped pencil (`genericType_swap`), and `genericType_iff` bounds the rank of every
member. -/
theorem rank_pow_add_mk_le_of_genericType [Infinite K] {N M : Matrix (Fin n) (Fin n) K}
    {τ : Nat.Partition n} (h : GenericType N M τ) {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    Matrix.rank (M ^ k) + mk τ k ≤ n := by
  have hlt := rank_lt_of_not_pencilRankGe
    (genericType_iff.mp (genericType_swap h) k hk1 hkn).2 (0 : K)
  rw [zero_smul, add_zero] at hlt
  have hmk := mk_le τ k
  omega

/-- **`HasType M τ` is the maximality of the ranks of the powers of `M`.**  With
`rank_pow_add_mk_le_of_genericType` the two inequalities of `hasType_iff_rank_le`
collapse to one, and that one is the nonvanishing of an `(n − m_k(τ))`-minor of
`M ^ k`. -/
theorem hasType_of_le_rank_pow [Infinite K] {N M : Matrix (Fin n) (Fin n) K}
    {τ : Nat.Partition n} (h : GenericType N M τ)
    (hge : ∀ k, 1 ≤ k → k ≤ n → n - mk τ k ≤ Matrix.rank (M ^ k)) : HasType M τ := by
  rw [hasType_iff_rank_le]
  intro k hk1 hkn
  have hle := rank_pow_add_mk_le_of_genericType h hk1 hkn
  have hgek := hge k hk1 hkn
  have hmk := mk_le τ k
  omega

/-! ### The multidegree at a single degree

The multidegree is determined by the value of one Hilbert function at one
degree, *given* that some multidegree exists.  This is the reduction the
constructibility of `pencilLocus` needs; the existence input is
`Chain.exists_multidegree` (`Chain/Multidegree.lean`). -/

/-- Changing the multidegree in degrees `k ≥ 1` only. -/
theorem hasMultidegree_of_agree {N M : Matrix (Fin n) (Fin n) K} {τ : Nat.Partition n}
    {d d' : ℕ → ℕ} (h' : HasMultidegree N M τ d') (hagree : ∀ k, 1 ≤ k → d k = d' k) :
    HasMultidegree N M τ d := by
  intro k hk
  obtain ⟨e₀, he₀⟩ := h' k hk
  exact ⟨e₀, fun e he => by rw [hagree k hk]; exact he₀ e he⟩

/-- Two multidegrees for the same generic type agree. -/
theorem hasMultidegree_unique {N M : Matrix (Fin n) (Fin n) K} {τ : Nat.Partition n}
    {d d' : ℕ → ℕ} (h : HasMultidegree N M τ d) (h' : HasMultidegree N M τ d') :
    ∀ k, 1 ≤ k → d k = d' k := by
  intro k hk
  obtain ⟨e₀, he₀⟩ := h k hk
  obtain ⟨e₁, he₁⟩ := h' k hk
  have h1 := he₀ (max e₀ e₁) (le_max_left _ _)
  have h2 := he₁ (max e₀ e₁) (le_max_right _ _)
  omega

end Height.Chain
