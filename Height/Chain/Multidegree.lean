import Height.Chain.Constructible
import Height.Pencil.LocalModel
import Height.Pencil.Basic
import Height.Graded.ProjectiveLine
import Mathlib.Algebra.Polynomial.Homogenize
import Mathlib.RingTheory.Localization.Module
import Height.Orbital.GenericRank
import Height.Toolbox.CentralizerDim

/-!
# The generic type and the multidegree of a nilpotent pencil (`lem:kernel-flag`(1),(3))

This file proves `Chain.exists_multidegree`: every
nilpotent pencil `μN + νM` has a generic type `τ` and a multidegree `d` with
`d k ≤ k (n − m_k(τ))`.

The whole computation is run at the generic point of `ℙ¹`, i.e. over the
fraction field `F = Frac(K[μ,ν])` of the graded ring `B = Graded.Poly K`:

* `pencilGenRank N M k` is the rank of `P^k` over `F`.  Both the *generic type*
  and the *rank of the kernel flag* are read off it.
* **Generic type** (`exists_genericType`).  Some `ρ × ρ` minor `δ` of `P^k` is
  nonzero and all `(ρ+1)`-minors vanish (`Height.Orbital.rank_map_eq_of_minor_witness`
  for the zero ideal).  The minors of `P^k` are *homogeneous*
  (`det_submatrix_pencil_pow_isHomogeneous`), and a nonzero homogeneous
  polynomial in two variables stays nonzero after dehomogenisation
  (`Graded.deh_ne_zero_of_isHomogeneous`),
  so `δ` survives the specialisation `μ ↦ 1, ν ↦ t` for all but finitely many
  `t`; at those `t` the rank of `(N + tM)^k` is `ρ`.
* **The rank of the kernel flag** (`card_basis_kerFlag`).  A `B`-basis of
  `S_k = ker P^k` maps to an `F`-basis of `ker P^k ⊆ F^n` — independence by
  `LinearIndependent.localization`, spanning by clearing denominators
  (`IsLocalization.exist_integer_multiples_of_finite`) and using that `S_k` is
  the *whole* kernel over `B`.  So the rank is `n − ρ = m_k(τ)`.
* **The degree bound** (`exists_multidegree_at`, `exists_multidegree`).  Row selection: over `F` the rows of
  `P^k` indexed by a nonsingular minor already cut out `ker P^k`, so
  `y ↦ (P^k y) ∘ f` has kernel exactly `kerPiece` in every degree; rank–nullity
  in degree `e` gives `n(e+1) ≤ dim kerPiece + ρ(e+k+1)`, which is `d_k ≤ ρ k`.
-/

namespace Height.Chain

open Height.Pencil

open Matrix MvPolynomial Height.Graded Height.Steenrod Height.Toolbox

universe u

/-! ### Dehomogenisation `μ ↦ 1, ν ↦ t` -/

section Dehom

variable {K : Type u} [Field K]

/-- Evaluation of `B = K[μ, ν]` at `(1, t)`: it carries `pencil N M` to the
member `N + t M`. -/
noncomputable def evalPencil (t : K) : Graded.Poly K →ₐ[K] K :=
  MvPolynomial.aeval ![1, t]

theorem evalPencil_eq_eval_deh (t : K) (f : Graded.Poly K) :
    evalPencil t f = Polynomial.eval t (Graded.deh K f) := by
  have h : (Polynomial.aeval t).comp (Graded.deh K) = evalPencil t := by
    refine MvPolynomial.algHom_ext fun i => ?_
    fin_cases i <;> simp [Graded.deh, evalPencil]
  have := congrArg (fun φ => φ f) h
  simpa [Polynomial.coe_aeval_eq_eval] using this.symm

/-- A nonzero homogeneous polynomial survives the specialisation `μ ↦ 1,
ν ↦ t` for all but finitely many `t`. -/
theorem exists_finset_evalPencil_ne_zero {D : ℕ} {f : Graded.Poly K}
    (hf : f.IsHomogeneous D) (hne : f ≠ 0) :
    ∃ F : Finset K, ∀ t : K, t ∉ F → evalPencil t f ≠ 0 := by
  classical
  refine ⟨(Graded.deh K f).roots.toFinset, fun t ht => ?_⟩
  rw [evalPencil_eq_eval_deh]
  intro hzero
  exact ht (Multiset.mem_toFinset.2
    (Polynomial.mem_roots'.2 ⟨Graded.deh_ne_zero_of_isHomogeneous hf hne, hzero⟩))

end Dehom

/-! ### The minors of the pencil are homogeneous -/

section Homogeneous

variable {K : Type u} [Field K] {n : ℕ}

/-- Every minor of `P^k` is homogeneous. -/
theorem det_submatrix_pencil_pow_isHomogeneous {s k : ℕ} (N M : Matrix (Fin n) (Fin n) K)
    (f g : Fin s → Fin n) :
    (((pencil N M ^ k).submatrix f g).det).IsHomogeneous (s * k) := by
  have h := det_mem_Bpiece (K := K) ((pencil N M ^ k).submatrix f g) (k : ℤ)
    fun i j => Height.Pencil.pencil_pow_mem_Bpiece N M k (f i) (g j)
  rw [show ((s : ℤ) * (k : ℤ)) = ((s * k : ℕ) : ℤ) by push_cast; ring, Bpiece_natCast] at h
  exact h

end Homogeneous

/-! ### The rank of the pencil at the generic point of `ℙ¹` -/

section GenRank

variable {K : Type u} [Field K] {n : ℕ}

/-- The function field of `ℙ¹`: the fraction field of `B = K[μ, ν]`. -/
abbrev PolyF (K : Type u) [Field K] : Type u := FractionRing (Graded.Poly K)

/-- The inclusion of `B` in its fraction field. -/
noncomputable abbrev toPolyF (K : Type u) [Field K] : Graded.Poly K →+* PolyF K :=
  algebraMap (Graded.Poly K) (PolyF K)

theorem toPolyF_injective : Function.Injective (toPolyF K) :=
  IsFractionRing.injective (Graded.Poly K) (PolyF K)

/-- The rank of `P^k` at the generic point of `ℙ¹`. -/
noncomputable def pencilGenRank (N M : Matrix (Fin n) (Fin n) K) (k : ℕ) : ℕ :=
  Matrix.rank (((pencil N M) ^ k).map (toPolyF K))

/-- Minors commute with the entrywise application of a ring homomorphism. -/
theorem det_submatrix_map {R S : Type*} [CommRing R] [CommRing S] {s : ℕ}
    (φ : R →+* S) (A : Matrix (Fin n) (Fin n) R) (f g : Fin s → Fin n) :
    ((A.map φ).submatrix f g).det = φ ((A.submatrix f g).det) := by
  rw [Matrix.submatrix_map]
  exact (RingHom.map_det φ (A.submatrix f g)).symm

/-- A witnessing nonzero minor of `P^k` of the generic size. -/
theorem exists_minor_witness (N M : Matrix (Fin n) (Fin n) K) (k : ℕ) :
    ∃ f g : Fin (pencilGenRank N M k) → Fin n,
      ((pencil N M ^ k).submatrix f g).det ≠ 0 := by
  obtain ⟨f, g, hfg⟩ := Height.Toolbox.exists_submatrix_det_ne_zero
    (k := pencilGenRank N M k) ((pencil N M ^ k).map (toPolyF K)) (le_of_eq rfl)
  refine ⟨f, g, fun hzero => hfg ?_⟩
  rw [det_submatrix_map, hzero, map_zero]

/-- All minors of `P^k` of size one more than the generic rank vanish. -/
theorem det_submatrix_succ_eq_zero (N M : Matrix (Fin n) (Fin n) K) (k : ℕ)
    (f g : Fin (pencilGenRank N M k + 1) → Fin n) :
    ((pencil N M ^ k).submatrix f g).det = 0 := by
  by_contra hne
  have h : (((pencil N M ^ k).map (toPolyF K)).submatrix f g).det ≠ 0 := by
    rw [det_submatrix_map]
    exact fun hz => hne (toPolyF_injective (by rw [hz, map_zero]))
  have := Height.Toolbox.le_rank_of_submatrix_det_ne_zero _ f g h
  exact absurd this (by simp [pencilGenRank])

/-- The pencil specialises to its member at the parameter `t`. -/
theorem map_pencil_evalPencil (N M : Matrix (Fin n) (Fin n) K) (t : K) :
    (pencil N M).map (evalPencil t).toRingHom = N + t • M := by
  ext i j
  show evalPencil t (MvPolynomial.C (N i j) * Graded.mu + MvPolynomial.C (M i j) * Graded.nu)
    = (N + t • M) i j
  simp [evalPencil, Graded.mu, Graded.nu, Matrix.add_apply, Matrix.smul_apply, mul_comm]

theorem map_pencil_pow_evalPencil (N M : Matrix (Fin n) (Fin n) K) (t : K) (k : ℕ) :
    (pencil N M ^ k).map (evalPencil t).toRingHom = (N + t • M) ^ k := by
  have hmp := map_pow ((evalPencil t).toRingHom.mapMatrix (m := Fin n)) (pencil N M) k
  rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply] at hmp
  rw [hmp, map_pencil_evalPencil]

/-- **The generic rank is attained off a finite set of parameters.** -/
theorem exists_finset_rank_pow_eq (N M : Matrix (Fin n) (Fin n) K) (k : ℕ) :
    ∃ S : Finset K, ∀ t : K, t ∉ S →
      Matrix.rank ((N + t • M) ^ k) = pencilGenRank N M k := by
  classical
  obtain ⟨f₀, g₀, hf₀⟩ := exists_minor_witness N M k
  obtain ⟨S, hS⟩ := exists_finset_evalPencil_ne_zero
    (det_submatrix_pencil_pow_isHomogeneous N M f₀ g₀) hf₀
  refine ⟨S, fun t ht => ?_⟩
  have h := Height.Orbital.rank_map_eq_of_minor_witness (pencil N M ^ k) (⊥ : Ideal (Graded.Poly K))
    (evalPencil t).toRingHom (fun x hx => by rw [Ideal.mem_bot.1 hx, map_zero]) f₀ g₀
    (hS t ht) (fun f g => Ideal.mem_bot.2 (det_submatrix_succ_eq_zero N M k f g))
  rwa [map_pencil_pow_evalPencil] at h

/-- **The rank of the pencil in the chart at a point is the generic rank of the
pencil.**  A minor witnessing `pencilGenRank` is homogeneous, so `Graded.atPoint`
does not kill it, and every larger minor of `P^k` vanishes identically.  No
genericity in the point is needed: the chart at *every* `t₀` sees the generic
rank, which is exactly why the fibre flag is the *generic* jump. -/
theorem rank_map_Pat_pow {L : Type u} [Field L] [Algebra (PowerSeries K) L]
    [IsFractionRing (PowerSeries K) L]
    (N M : Matrix (Fin n) (Fin n) K) (t₀ : K) (k : ℕ) :
    Matrix.rank ((Pat N M t₀ ^ k).map (algebraMap (PowerSeries K) L))
      = pencilGenRank N M k := by
  classical
  obtain ⟨f₀, g₀, hne⟩ := exists_minor_witness N M k
  have hmap : (Pat N M t₀ ^ k).map (algebraMap (PowerSeries K) L)
      = (pencil N M ^ k).map ((algebraMap (PowerSeries K) L).comp (atPoint t₀)) := by
    rw [Pat_pow]
    refine Matrix.ext fun i j => ?_
    rfl
  rw [hmap]
  refine Height.Orbital.rank_map_eq_of_minor_witness (pencil N M ^ k) ⊥ _
    (fun f hf => by rw [Ideal.mem_bot.1 hf, map_zero]) f₀ g₀ ?_
    (fun f g => Ideal.mem_bot.2 (det_submatrix_succ_eq_zero N M k f g))
  have hhom : ((pencil N M ^ k).submatrix f₀ g₀).det
      ∈ Bpiece K ((pencilGenRank N M k : ℤ) * (k : ℤ)) :=
    det_mem_Bpiece _ (k : ℤ) fun i j => pencil_pow_mem_Bpiece N M k (f₀ i) (g₀ j)
  have hat : atPoint t₀ (((pencil N M ^ k).submatrix f₀ g₀).det) ≠ 0 :=
    atPoint_ne_zero_of_homogeneous t₀ hhom hne
  intro h0
  exact hat ((map_eq_zero_iff _ (IsFractionRing.injective (PowerSeries K) L)).mp h0)

/-- **The fibre flag is the generic jump.**  `dim V_k = n − rk P^k` over the
function field of `ℙ¹`, at every point of `ℙ¹`. -/
theorem finrank_fibFlag_add_pencilGenRank (N M : Matrix (Fin n) (Fin n) K) (t₀ : K) (k : ℕ) :
    Module.finrank K (fibFlag (Pat N M t₀) k) + pencilGenRank N M k = n := by
  classical
  set L := FractionRing (PowerSeries K) with hL
  have h1 : Module.finrank K (fibFlag (Pat N M t₀) k)
      = Module.finrank L (Isotropy.kerFlag (Isotropy.toK L (Pat N M t₀)) k) :=
    finrank_fibFlag_eq_generic _ _
  have h2 : Isotropy.kerFlag (Isotropy.toK L (Pat N M t₀)) k
      = LinearMap.ker (((Pat N M t₀ ^ k).map (algebraMap (PowerSeries K) L)).mulVecLin) := by
    rw [Isotropy.kerFlag, ← Isotropy.toK_pow]
  have h3 := LinearMap.finrank_range_add_finrank_ker
    (((Pat N M t₀ ^ k).map (algebraMap (PowerSeries K) L)).mulVecLin)
  have h4 : Module.finrank L (Fin n → L) = n := by simp
  rw [h4] at h3
  rw [h1, h2]
  have h5 : Module.finrank L
      (LinearMap.range (((Pat N M t₀ ^ k).map (algebraMap (PowerSeries K) L)).mulVecLin))
      = pencilGenRank N M k := rank_map_Pat_pow N M t₀ k
  omega

end GenRank

/-! ### The generic type -/

section GenericTypeExists

variable {K : Type u} [Field K] {n : ℕ}

/-- Every nilpotent matrix has a Jordan type: the partition whose parts are the
sizes of its Jordan chains. -/
theorem exists_hasType {X : Matrix (Fin n) (Fin n) K} (hX : IsNilpotent X) :
    ∃ τ : Nat.Partition n, HasType X τ := by
  obtain ⟨d, a, hsum, hconj, -⟩ := Height.Toolbox.finrank_centralizer_pow X hX
  have hsum' : (Multiset.map a Finset.univ.val).sum = n := by
    rw [← hsum]; rfl
  refine ⟨Nat.Partition.ofSums n (Multiset.map a Finset.univ.val) hsum', fun m hm => ?_⟩
  rw [hconj m hm]
  symm
  show Multiset.card (Multiset.filter (fun x => m ≤ x)
      (Multiset.filter (fun x => x ≠ 0) (Multiset.map a Finset.univ.val)))
    = (Finset.univ.filter fun i => m ≤ a i).card
  rw [Multiset.filter_filter]
  have hcong : Multiset.filter (fun x => m ≤ x ∧ x ≠ 0) (Multiset.map a Finset.univ.val)
      = Multiset.filter (fun x => m ≤ x) (Multiset.map a Finset.univ.val) :=
    Multiset.filter_congr fun x _ => by constructor <;> intro hx <;> omega
  rw [hcong, ← Multiset.countP_eq_card_filter, Multiset.countP_map,
    ← Multiset.countP_eq_card_filter, Multiset.countP_eq_card_filter]
  rfl

/-- Beyond `n` the pencil has generic rank `0`. -/
theorem pencilGenRank_eq_zero_of_le {N M : Matrix (Fin n) (Fin n) K} {k : ℕ}
    (hk : n ≤ k) (hn : pencilGenRank N M n = 0) : pencilGenRank N M k = 0 := by
  have hle : pencilGenRank N M k ≤ pencilGenRank N M n := by
    show Matrix.rank ((pencil N M ^ k).map (toPolyF K))
      ≤ Matrix.rank ((pencil N M ^ n).map (toPolyF K))
    have hsplit : (pencil N M ^ k).map (toPolyF K)
        = ((pencil N M ^ n).map (toPolyF K)) * ((pencil N M ^ (k - n)).map (toPolyF K)) := by
      have h1 : ((pencil N M ^ n) * (pencil N M ^ (k - n))).map (toPolyF K)
          = ((pencil N M ^ n).map (toPolyF K)) * ((pencil N M ^ (k - n)).map (toPolyF K)) := by
        have := map_mul ((toPolyF K).mapMatrix (m := Fin n)) (pencil N M ^ n)
          (pencil N M ^ (k - n))
        simp
      rw [← h1, ← pow_add, show n + (k - n) = k by omega]
    rw [hsplit]
    exact Matrix.rank_mul_le_left _ _
  omega

/-- **`lem:kernel-flag`(1), first half**: a nilpotent pencil has a generic type,
and it is the type prescribed by the generic ranks. -/
theorem exists_genericType [Infinite K] {N M : Matrix (Fin n) (Fin n) K}
    (h : NilpotentPencil N M) :
    ∃ τ : Nat.Partition n, GenericType N M τ ∧
      ∀ k, 1 ≤ k → mk τ k + pencilGenRank N M k = n := by
  classical
  choose S hS using fun k => exists_finset_rank_pow_eq N M k
  set T : Finset K := (Finset.range (n + 1)).biUnion S with hT
  obtain ⟨t₀, ht₀⟩ := Set.Infinite.nonempty ((T : Set K).toFinite.infinite_compl)
  have ht₀' : t₀ ∉ T := by simpa using ht₀
  have hnotT : ∀ (t : K), t ∉ T → ∀ k, k ≤ n → t ∉ S k := by
    intro t ht k hk hmem
    exact ht (Finset.mem_biUnion.2 ⟨k, Finset.mem_range.2 (by omega), hmem⟩)
  have hnil : IsNilpotent (N + t₀ • M) := by simpa using h 1 t₀
  obtain ⟨τ, hτ⟩ := exists_hasType hnil
  have hrank : ∀ k, 1 ≤ k → k ≤ n → mk τ k + pencilGenRank N M k = n := by
    intro k hk1 hkn
    have h1 := rank_pow_add_mk_of_hasType hτ k
    have h2 := hS k t₀ (hnotT t₀ ht₀' k hkn)
    omega
  have hall : ∀ k, 1 ≤ k → mk τ k + pencilGenRank N M k = n := by
    intro k hk
    by_cases hkn : k ≤ n
    · exact hrank k hk hkn
    · have hn : pencilGenRank N M n = 0 := by
        rcases Nat.eq_zero_or_pos n with hn0 | hn0
        · have hle : Matrix.rank ((pencil N M ^ n).map (toPolyF K)) ≤ n := by
            subst hn0
            simp
          simp [pencilGenRank, hn0]
        · have h1 := hrank n hn0 le_rfl
          have h2 : mk τ n = n := by rw [mk]; exact Height.Pencil.sum_conjPart τ
          omega
      rw [mk_eq_of_le (by omega), pencilGenRank_eq_zero_of_le (by omega) hn]
      omega
  refine ⟨τ, ⟨T, fun t ht => ?_⟩, hall⟩
  rw [hasType_iff_rank_le]
  intro k hk1 hkn
  have h1 := hS k t (hnotT t ht k hkn)
  have h2 := hall k hk1
  omega

end GenericTypeExists

/-! ### The rank of the kernel flag is `n − ρ` -/

section KerFlagRank

variable {K : Type u} [Field K] {n : ℕ}

/-- The coordinatewise inclusion `B^n ↪ F^n`. -/
noncomputable def embF (K : Type u) [Field K] (n : ℕ) :
    (Fin n → Graded.Poly K) →ₗ[Graded.Poly K] (Fin n → PolyF K) :=
  LinearMap.pi fun i => (Algebra.linearMap (Graded.Poly K) (PolyF K)).comp (LinearMap.proj i)

@[simp] theorem embF_apply (x : Fin n → Graded.Poly K) (i : Fin n) :
    embF K n x i = toPolyF K (x i) := rfl

theorem embF_injective : Function.Injective (embF K n) := fun _ _ hxy =>
  funext fun i => toPolyF_injective (congrFun hxy i)

theorem embF_mulVec (A : Matrix (Fin n) (Fin n) (Graded.Poly K)) (x : Fin n → Graded.Poly K) :
    (A.map (toPolyF K)) *ᵥ (embF K n x) = embF K n (A *ᵥ x) :=
  funext fun i => (RingHom.map_mulVec (toPolyF K) A x i).symm

/-- The kernel of `P^k` at the generic point of `ℙ¹`. -/
noncomputable def kerFlagF (N M : Matrix (Fin n) (Fin n) K) (k : ℕ) :
    Submodule (PolyF K) (Fin n → PolyF K) :=
  LinearMap.ker ((((pencil N M) ^ k).map (toPolyF K)).mulVecLin)

theorem finrank_kerFlagF_add (N M : Matrix (Fin n) (Fin n) K) (k : ℕ) :
    Module.finrank (PolyF K) (kerFlagF N M k) + pencilGenRank N M k = n := by
  have h := LinearMap.finrank_range_add_finrank_ker
    ((((pencil N M) ^ k).map (toPolyF K)).mulVecLin)
  have hdim : Module.finrank (PolyF K) (Fin n → PolyF K) = n := by simp
  rw [hdim] at h
  show Module.finrank (PolyF K)
      (LinearMap.ker ((((pencil N M) ^ k).map (toPolyF K)).mulVecLin)) +
    Module.finrank (PolyF K) (LinearMap.range ((((pencil N M) ^ k).map (toPolyF K)).mulVecLin)) = n
  omega

/-- The image of a `B`-basis of the kernel flag spans the kernel over the
function field: independence is `LinearIndependent.localization`, spanning is
clearing denominators. -/
theorem span_kerFlagF {N M : Matrix (Fin n) (Fin n) K} {k : ℕ} {ι : Type} [Fintype ι]
    (w : Module.Basis ι (Graded.Poly K) (Height.Pencil.kerFlag N M k)) :
    Submodule.span (PolyF K)
        (Set.range fun i =>
          embF K n ((w i : Height.Pencil.kerFlag N M k) : Fin n → Graded.Poly K))
      = kerFlagF N M k := by
  classical
  set w' : ι → (Fin n → Graded.Poly K) :=
    fun i => ((w i : Height.Pencil.kerFlag N M k) : Fin n → Graded.Poly K) with hw'
  -- the `B`-span of `w'` is the kernel flag
  have hspanB : Submodule.span (Graded.Poly K) (Set.range w')
      = Height.Pencil.kerFlag N M k := by
    have h2 := congrArg (Submodule.map (Submodule.subtype (Height.Pencil.kerFlag N M k)))
      w.span_eq
    rwa [Submodule.map_span, Submodule.map_top, Submodule.range_subtype,
      ← Set.range_comp] at h2
  refine le_antisymm ?_ ?_
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    show (((pencil N M) ^ k).map (toPolyF K)) *ᵥ (embF K n (w' i)) = 0
    rw [embF_mulVec]
    have : (pencil N M ^ k) *ᵥ w' i = 0 := (w i).2
    rw [this, map_zero]
  · intro x hx
    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite
      (nonZeroDivisors (Graded.Poly K)) x
    choose y hy using hb
    have hyx : embF K n y = (b : Graded.Poly K) • x := funext fun i => hy i
    have hker : (pencil N M ^ k) *ᵥ y = 0 := by
      refine embF_injective ?_
      rw [← embF_mulVec, hyx, map_zero]
      show (((pencil N M) ^ k).map (toPolyF K)) *ᵥ ((b : Graded.Poly K) • x) = 0
      rw [Matrix.mulVec_smul]
      have hx0 : (((pencil N M) ^ k).map (toPolyF K)) *ᵥ x = 0 := hx
      rw [hx0, smul_zero]
    have hyspan : y ∈ Submodule.span (Graded.Poly K) (Set.range w') := by
      rw [hspanB]; exact hker
    have hembspan : embF K n y ∈ Submodule.span (PolyF K) (Set.range fun i => embF K n (w' i)) := by
      have hmap : Submodule.map (embF K n) (Submodule.span (Graded.Poly K) (Set.range w'))
          = Submodule.span (Graded.Poly K) (Set.range fun i => embF K n (w' i)) := by
        rw [Submodule.map_span, ← Set.range_comp]; rfl
      have h1 : embF K n y ∈ Submodule.span (Graded.Poly K) (Set.range fun i => embF K n (w' i)) := by
        rw [← hmap]; exact ⟨y, hyspan, rfl⟩
      exact Submodule.span_subset_span (Graded.Poly K) (PolyF K) _ h1
    have hbne : (toPolyF K) (b : Graded.Poly K) ≠ 0 := by
      intro h0
      have := toPolyF_injective (by rw [h0, map_zero] :
        (toPolyF K) (b : Graded.Poly K) = (toPolyF K) 0)
      exact absurd this (nonZeroDivisors.coe_ne_zero b)
    have hxeq : x = ((toPolyF K) (b : Graded.Poly K))⁻¹ • embF K n y := by
      rw [hyx]
      funext i
      show x i = ((toPolyF K) (b : Graded.Poly K))⁻¹ * ((b : Graded.Poly K) • x i)
      rw [Algebra.smul_def, ← mul_assoc, inv_mul_cancel₀ hbne, one_mul]
    rw [hxeq]
    exact Submodule.smul_mem _ _ hembspan

/-- **The kernel flag has rank `n − ρ`.** -/
theorem card_basis_kerFlag {N M : Matrix (Fin n) (Fin n) K} {k : ℕ} {ι : Type} [Fintype ι]
    (w : Module.Basis ι (Graded.Poly K) (Height.Pencil.kerFlag N M k)) :
    Fintype.card ι + pencilGenRank N M k = n := by
  classical
  have hliB : LinearIndependent (Graded.Poly K)
      (fun i => embF K n ((w i : Height.Pencil.kerFlag N M k) : Fin n → Graded.Poly K)) := by
    refine LinearIndependent.map' (w.linearIndependent.map' (Submodule.subtype _)
      (Submodule.ker_subtype _)) (embF K n) ?_
    rw [LinearMap.ker_eq_bot]
    exact embF_injective
  have hliF : LinearIndependent (PolyF K)
      (fun i => embF K n ((w i : Height.Pencil.kerFlag N M k) : Fin n → Graded.Poly K)) :=
    hliB.localization (Rₛ := PolyF K) (S := nonZeroDivisors (Graded.Poly K))
  have hcard := finrank_span_eq_card hliF
  rw [span_kerFlagF w] at hcard
  have h := finrank_kerFlagF_add N M k
  omega

end KerFlagRank

/-! ### The Hilbert function of the kernel flag -/

section Hilbert

variable {K : Type u} [Field K] {n : ℕ}

/-- **`lem:kernel-flag`(1), second half**: the kernel flag has a homogeneous
`B`-basis, its degrees are `≥ 0`, and their number is `n - ρ_k`. -/
theorem exists_homog_basis (N M : Matrix (Fin n) (Fin n) K) (k : ℕ) :
    ∃ (s : ℕ) (c : Fin s → ℤ)
      (w : Module.Basis (Fin s) (Graded.Poly K) (Height.Pencil.kerFlag N M k)),
      (∀ i, ((w i : Height.Pencil.kerFlag N M k) : Fin n → Graded.Poly K)
          ∈ (Graded.GradedPresentation.free K (Fin n)).piece (c i)) ∧
        (∀ i, 0 ≤ c i) ∧ s + pencilGenRank N M k = n := by
  classical
  obtain ⟨ι, hι, b, u, H⟩ := Height.Graded.exists_homogeneousBasis
    (Height.Graded.GradedPresentation.free K (Fin n))
    (Height.Pencil.kerFlag N M k)
    (Height.Pencil.isGraded_kerFlag N M k) (Height.Pencil.saturated_kerFlag N M k)
  let _ : Fintype ι := hι
  obtain ⟨v, hv⟩ := H.exists_basis
  have hv' : ∀ i, ((v i : Height.Pencil.kerFlag N M k) : Fin n → Graded.Poly K)
      ∈ (Graded.GradedPresentation.free K (Fin n)).piece (b i) := fun i => by
    rw [hv i]; exact H.homog i
  have hcard := card_basis_kerFlag v
  refine ⟨Fintype.card ι, fun i => b ((Fintype.equivFin ι).symm i),
    v.reindex (Fintype.equivFin ι), fun i => ?_, fun i => ?_, hcard⟩
  · rw [Module.Basis.reindex_apply]
    exact hv' _
  · by_contra hlt
    have hneg : b ((Fintype.equivFin ι).symm i) < 0 := not_le.1 hlt
    have hbot : (Graded.GradedPresentation.free K (Fin n)).piece
        (b ((Fintype.equivFin ι).symm i)) = ⊥ :=
      (Graded.GradedPresentation.free K (Fin n)).piece_eq_bot (fun _ => hneg)
    have hmem := hv' ((Fintype.equivFin ι).symm i)
    rw [hbot, Submodule.mem_bot] at hmem
    exact (v.ne_zero ((Fintype.equivFin ι).symm i)) (Subtype.ext hmem)

/-- The Hilbert function of `kerPiece` read off a homogeneous basis. -/
theorem finrank_kerPiece_of_basis {N M : Matrix (Fin n) (Fin n) K} {k s : ℕ}
    {c : Fin s → ℤ}
    (w : Module.Basis (Fin s) (Graded.Poly K) (Height.Pencil.kerFlag N M k))
    (hw : ∀ i, ((w i : Height.Pencil.kerFlag N M k) : Fin n → Graded.Poly K)
      ∈ (Graded.GradedPresentation.free K (Fin n)).piece (c i)) (e : ℕ) :
    Module.finrank K (kerPiece N M k e) = ∑ i, ((e : ℤ) - c i + 1).toNat := by
  rw [← Height.Pencil.sub_kerFlag]
  exact (Height.Graded.HomogeneousBasis.of_basis
    (P := Height.Graded.GradedPresentation.free K (Fin n))
    (deg := c) w hw).finrank_sub (e : ℤ)

end Hilbert

/-! ### Row selection -/

section RowSelect

variable {K : Type u} [Field K] {n : ℕ}

/-- Selecting the rows of a nonsingular minor of `P^k` loses nothing: over `B`
those rows already cut out the whole kernel, because over the function field the
two kernels have the same dimension. -/
theorem mulVec_eq_zero_of_rows {N M : Matrix (Fin n) (Fin n) K} {k : ℕ}
    {f₀ g₀ : Fin (pencilGenRank N M k) → Fin n}
    (hfg : ((pencil N M ^ k).submatrix f₀ g₀).det ≠ 0)
    {y : Fin n → Graded.Poly K}
    (hy : ∀ i, ((pencil N M ^ k) *ᵥ y) (f₀ i) = 0) :
    (pencil N M ^ k) *ᵥ y = 0 := by
  set A : Matrix (Fin n) (Fin n) (PolyF K) := (pencil N M ^ k).map (toPolyF K) with hA
  set T : Matrix (Fin (pencilGenRank N M k)) (Fin n) (PolyF K) := A.submatrix f₀ id with hT
  have hrow : ∀ (z : Fin n → PolyF K) (i : Fin (pencilGenRank N M k)),
      (T *ᵥ z) i = (A *ᵥ z) (f₀ i) := fun _ _ => rfl
  have hTrank : pencilGenRank N M k ≤ T.rank := by
    refine Height.Toolbox.le_rank_of_submatrix_det_ne_zero T id g₀ ?_
    have hsub : T.submatrix id g₀ = A.submatrix f₀ g₀ := rfl
    rw [hsub, hA, det_submatrix_map]
    exact fun h0 => hfg (toPolyF_injective (by rw [h0, map_zero]))
  have hTker : T.rank + Module.finrank (PolyF K) (LinearMap.ker T.mulVecLin) = n := by
    have h := LinearMap.finrank_range_add_finrank_ker T.mulVecLin
    rw [show Module.finrank (PolyF K) (Fin n → PolyF K) = n from by simp] at h
    exact h
  have hAker := finrank_kerFlagF_add N M k
  have hle : kerFlagF N M k ≤ LinearMap.ker T.mulVecLin := by
    intro z hz
    have hz' : A *ᵥ z = 0 := hz
    show T *ᵥ z = 0
    funext i
    rw [hrow z i, hz']
    rfl
  have heq : kerFlagF N M k = LinearMap.ker T.mulVecLin :=
    Submodule.eq_of_le_of_finrank_le hle (by omega)
  have hyF : embF K n y ∈ LinearMap.ker T.mulVecLin := by
    show T *ᵥ (embF K n y) = 0
    funext i
    rw [hrow (embF K n y) i, hA, embF_mulVec, embF_apply, hy i, map_zero]
    rfl
  rw [← heq] at hyF
  have h0 : embF K n ((pencil N M ^ k) *ᵥ y) = 0 := by
    rw [← embF_mulVec]
    exact hyF
  exact embF_injective (h0.trans (map_zero (embF K n)).symm)

/-- Rank–nullity in degree `e` for the selected rows: `n(e+1) ≤ dim (S_k)_e +
ρ_k (e+k+1)`. -/
theorem row_rank_nullity {N M : Matrix (Fin n) (Fin n) K} {k : ℕ}
    {f₀ g₀ : Fin (pencilGenRank N M k) → Fin n}
    (hfg : ((pencil N M ^ k).submatrix f₀ g₀).det ≠ 0) (e : ℕ) :
    n * (e + 1) ≤ Module.finrank K (kerPiece N M k e)
      + pencilGenRank N M k * (e + k + 1) := by
  classical
  have hVfin : FiniteDimensional K
      ((Graded.GradedPresentation.free K (Fin n)).piece ((e : ℕ) : ℤ)) :=
    inferInstance
  have hWfin : FiniteDimensional K
      ((Graded.GradedPresentation.of K (fun _ : Fin (pencilGenRank N M k) => (0 : ℤ))).piece
        (((e : ℕ) : ℤ) + (k : ℤ))) :=
    inferInstance
  set Ψ : (Fin n → Graded.Poly K) →ₗ[K] (Fin (pencilGenRank N M k) → Graded.Poly K) :=
    (LinearMap.funLeft K (Graded.Poly K) f₀).comp
      ((pencil N M ^ k).mulVecLin.restrictScalars K) with hΨdef
  have hΨapp : ∀ (y : Fin n → Graded.Poly K) (i : Fin (pencilGenRank N M k)),
      Ψ y i = ((pencil N M ^ k) *ᵥ y) (f₀ i) := fun _ _ => rfl
  have hkerΨ : LinearMap.ker Ψ
      = LinearMap.ker (((pencil N M ^ k).mulVecLin).restrictScalars K) := by
    refine le_antisymm (fun y hy => ?_) (fun y hy => ?_)
    · have hy' : ∀ i, ((pencil N M ^ k) *ᵥ y) (f₀ i) = 0 := by
        intro i
        rw [← hΨapp y i]
        exact congrFun (LinearMap.mem_ker.1 hy) i
      exact mulVec_eq_zero_of_rows hfg hy'
    · have hy' : (pencil N M ^ k) *ᵥ y = 0 := LinearMap.mem_ker.1 hy
      refine LinearMap.mem_ker.2 (funext fun i => ?_)
      rw [hΨapp y i, hy']
      rfl
  set Φ := Ψ.domRestrict ((Graded.GradedPresentation.free K (Fin n)).piece ((e : ℕ) : ℤ))
    with hΦdef
  have hrn := LinearMap.finrank_range_add_finrank_ker Φ
  have hVdim : Module.finrank K
      ((Graded.GradedPresentation.free K (Fin n)).piece ((e : ℕ) : ℤ)) = n * (e + 1) := by
    rw [Graded.GradedPresentation.finrank_piece]
    have hterm : ∀ _j : Fin n, (((e : ℕ) : ℤ) - (0 : ℤ) + 1).toNat = e + 1 :=
      fun _ => by omega
    rw [Finset.sum_congr rfl fun j _ => hterm j]
    simp
  have hWdim : Module.finrank K
      ((Graded.GradedPresentation.of K (fun _ : Fin (pencilGenRank N M k) => (0 : ℤ))).piece
        (((e : ℕ) : ℤ) + (k : ℤ))) = pencilGenRank N M k * (e + k + 1) := by
    rw [Graded.GradedPresentation.finrank_piece]
    have hterm : ∀ _j : Fin (pencilGenRank N M k),
        ((((e : ℕ) : ℤ) + (k : ℤ)) - (0 : ℤ) + 1).toNat = e + k + 1 := fun _ => by omega
    rw [Finset.sum_congr rfl fun j _ => hterm j]
    simp
  have hrange : LinearMap.range Φ
      ≤ (Graded.GradedPresentation.of K (fun _ : Fin (pencilGenRank N M k) => (0 : ℤ))).piece
          (((e : ℕ) : ℤ) + (k : ℤ)) := by
    rintro _ ⟨y, rfl⟩
    refine (Graded.GradedPresentation.of K _).mem_piece.2 fun i => ?_
    have hy := (Graded.GradedPresentation.of K _).mem_piece.1 y.2
    have happ : Φ y i
        = ∑ j, (pencil N M ^ k) (f₀ i) j * (y : Fin n → Graded.Poly K) j := rfl
    rw [happ]
    refine Submodule.sum_mem _ fun j _ => ?_
    have h1 := Height.Pencil.pencil_pow_mem_Bpiece N M k (f₀ i) j
    have h2 : (y : Fin n → Graded.Poly K) j ∈ Bpiece K (((e : ℕ) : ℤ) - 0) := hy j
    have h3 := Bpiece_smul_Bpiece h1 h2
    rwa [show (k : ℤ) + (((e : ℕ) : ℤ) - 0) = ((e : ℕ) : ℤ) + (k : ℤ) - 0 by ring] at h3
  have hrangele : Module.finrank K (LinearMap.range Φ)
      ≤ pencilGenRank N M k * (e + k + 1) := by
    rw [← hWdim]
    exact Submodule.finrank_mono hrange
  have hkerΦ : Module.finrank K (LinearMap.ker Φ)
      = Module.finrank K (kerPiece N M k e) := by
    have hmap : Submodule.map
        ((Graded.GradedPresentation.free K (Fin n)).piece ((e : ℕ) : ℤ)).subtype
        (LinearMap.ker Φ) = kerPiece N M k e := by
      rw [hΦdef, LinearMap.ker_domRestrict, Submodule.map_comap_subtype, hkerΨ, inf_comm]
      rfl
    rw [← hmap]
    exact (Submodule.equivMapOfInjective _
      (Submodule.injective_subtype _) (LinearMap.ker Φ)).finrank_eq
  rw [hVdim] at hrn
  calc n * (e + 1)
      = Module.finrank K (LinearMap.range Φ) + Module.finrank K (LinearMap.ker Φ) := hrn.symm
    _ ≤ pencilGenRank N M k * (e + k + 1) + Module.finrank K (kerPiece N M k e) := by
        rw [hkerΦ]
        exact Nat.add_le_add_right hrangele _
    _ = Module.finrank K (kerPiece N M k e) + pencilGenRank N M k * (e + k + 1) :=
        Nat.add_comm _ _

end RowSelect

/-! ### The multidegree -/

section Multidegree

variable {K : Type u} [Field K] {n : ℕ}

/-- **`lem:kernel-flag`(3), one step**: the `k`-th multidegree exists and is
bounded by `k ρ_k`. -/
theorem exists_multidegree_at (N M : Matrix (Fin n) (Fin n) K) (k : ℕ) :
    ∃ dk : ℕ, (∀ e : ℕ, dk ≤ e →
        Module.finrank K (kerPiece N M k e) + dk
          = (n - pencilGenRank N M k) * (e + 1))
      ∧ dk ≤ k * pencilGenRank N M k := by
  classical
  obtain ⟨s, c, w, hw, hc0, hs⟩ := exists_homog_basis N M k
  obtain ⟨f₀, g₀, hfg⟩ := exists_minor_witness N M k
  set d0 : ℕ := (∑ i, c i).toNat with hd0
  have hsum0 : (0 : ℤ) ≤ ∑ i, c i := Finset.sum_nonneg fun i _ => hc0 i
  have hd0eq : ((d0 : ℕ) : ℤ) = ∑ i, c i := Int.toNat_of_nonneg hsum0
  have hcle : ∀ i, c i ≤ (d0 : ℤ) := by
    intro i
    rw [hd0eq]
    exact Finset.single_le_sum (f := c) (fun j _ => hc0 j) (Finset.mem_univ i)
  have hHilb : ∀ e : ℕ, d0 ≤ e →
      Module.finrank K (kerPiece N M k e) + d0 = s * (e + 1) := by
    intro e he
    have h1 : Module.finrank K (kerPiece N M k e) = ∑ i, ((e : ℤ) - c i + 1).toNat :=
      finrank_kerPiece_of_basis w hw e
    have h2 : ((∑ i, ((e : ℤ) - c i + 1).toNat : ℕ) : ℤ)
        = ∑ i, ((e : ℤ) - c i + 1) := by
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      have := hcle i
      omega
    have h3 : ∑ i : Fin s, ((e : ℤ) - c i + 1)
        = (s : ℤ) * ((e : ℤ) + 1) - ∑ i, c i := by
      have hterm : ∀ i : Fin s, ((e : ℤ) - c i + 1) = ((e : ℤ) + 1) - c i :=
        fun i => by ring
      rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_sub_distrib, Finset.sum_const]
      simp
    have hZ : (Module.finrank K (kerPiece N M k e) : ℤ) + (d0 : ℤ)
        = (s : ℤ) * ((e : ℤ) + 1) := by
      rw [h1, h2, h3, hd0eq]
      ring
    exact_mod_cast hZ
  have hsn : s = n - pencilGenRank N M k := by omega
  refine ⟨d0, fun e he => ?_, ?_⟩
  · rw [← hsn]
    exact hHilb e he
  · have hrn := row_rank_nullity hfg d0
    have hH := hHilb d0 le_rfl
    have hn : n * (d0 + 1)
        = s * (d0 + 1) + pencilGenRank N M k * (d0 + 1) := by
      rw [← add_mul, hs]
    have key : n * (d0 + 1) + d0
        ≤ n * (d0 + 1) + k * pencilGenRank N M k := by
      calc n * (d0 + 1) + d0
          ≤ (Module.finrank K (kerPiece N M k d0)
              + pencilGenRank N M k * (d0 + k + 1)) + d0 := Nat.add_le_add_right hrn _
        _ = (Module.finrank K (kerPiece N M k d0) + d0)
              + pencilGenRank N M k * (d0 + k + 1) := by ring
        _ = s * (d0 + 1) + pencilGenRank N M k * (d0 + k + 1) := by rw [hH]
        _ = (s * (d0 + 1) + pencilGenRank N M k * (d0 + 1))
              + k * pencilGenRank N M k := by ring
        _ = n * (d0 + 1) + k * pencilGenRank N M k := by rw [← hn]
    exact Nat.le_of_add_le_add_left key

/-- **`lem:kernel-flag`(1) and (3)**: every nilpotent pencil has a generic type
and a multidegree, and the multidegree obeys `d_k ≤ k (n - m_k)`. -/
theorem exists_multidegree [Infinite K] {N M : Matrix (Fin n) (Fin n) K}
    (h : NilpotentPencil N M) :
    ∃ (τ : Nat.Partition n) (d : ℕ → ℕ), GenericType N M τ ∧ HasMultidegree N M τ d ∧
      ∀ k, d k ≤ k * (n - mk τ k) := by
  classical
  obtain ⟨τ, hgen, hmk⟩ := exists_genericType h
  choose dk hdk hbound using fun k => exists_multidegree_at N M k
  refine ⟨τ, dk, hgen, ?_, ?_⟩
  · intro k hk
    refine ⟨dk k, fun e he => ?_⟩
    rw [hdk k e he, show n - pencilGenRank N M k = mk τ k from by have := hmk k hk; omega]
  · intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have := hbound 0
      omega
    · have h1 := hmk k hk
      have hb := hbound k
      rw [show n - mk τ k = pencilGenRank N M k from by omega]
      exact hb

/-- The generic type pins down the generic rank: `m_k(τ) + ρ_k = n`. -/
theorem mk_add_pencilGenRank_of_genericType [Infinite K] {N M : Matrix (Fin n) (Fin n) K}
    {τ : Nat.Partition n} (hgen : GenericType N M τ) (k : ℕ) :
    mk τ k + pencilGenRank N M k = n := by
  classical
  obtain ⟨F, hF⟩ := hgen
  obtain ⟨S, hS⟩ := exists_finset_rank_pow_eq N M k
  obtain ⟨t, ht⟩ :=
    Set.Infinite.nonempty (((F ∪ S : Finset K) : Set K).toFinite.infinite_compl)
  have ht' : t ∉ F ∪ S := by simpa using ht
  have h1 := rank_pow_add_mk_of_hasType (hF t fun h => ht' (Finset.mem_union_left _ h)) k
  have h2 := hS t fun h => ht' (Finset.mem_union_right _ h)
  omega

/-- **The one-degree characterisation of the multidegree**: for a
pencil of generic type `τ` and an admissible `d`, the multidegree condition is
decided by the Hilbert function in the *single* degree `e = n²`. -/
theorem hasMultidegree_iff_at [Infinite K] {N M : Matrix (Fin n) (Fin n) K}
    {τ : Nat.Partition n} {d : ℕ → ℕ} (hgen : GenericType N M τ)
    (hd : ∀ k, d k ≤ k * (n - mk τ k)) :
    HasMultidegree N M τ d ↔
      ∀ k, 1 ≤ k → k ≤ n →
        Module.finrank K (kerPiece N M k (n * n)) + d k = mk τ k * (n * n + 1) := by
  classical
  have hmk : ∀ k, mk τ k + pencilGenRank N M k = n :=
    mk_add_pencilGenRank_of_genericType hgen
  choose dk hdk hbound using fun k => exists_multidegree_at N M k
  have hsub : ∀ k, n - pencilGenRank N M k = mk τ k := fun k => by have := hmk k; omega
  have hdkle : ∀ k, k ≤ n → dk k ≤ n * n := by
    intro k hkn
    have h1 := hbound k
    have h2 := hmk k
    have hrho : pencilGenRank N M k ≤ n := by omega
    exact h1.trans (Nat.mul_le_mul hkn hrho)
  constructor
  · intro hmd k hk1 hkn
    obtain ⟨e₀, he₀⟩ := hmd k hk1
    have h1 := he₀ (max e₀ (n * n)) (le_max_left _ _)
    have h2 := hdk k (max e₀ (n * n)) ((hdkle k hkn).trans (le_max_right _ _))
    rw [hsub k] at h2
    have hdd : d k = dk k := by omega
    have h3 := hdk k (n * n) (hdkle k hkn)
    rw [hsub k, ← hdd] at h3
    exact h3
  · intro heq k hk1
    by_cases hkn : k ≤ n
    · have h3 := hdk k (n * n) (hdkle k hkn)
      rw [hsub k] at h3
      have h4 := heq k hk1 hkn
      have hdd : d k = dk k := by omega
      refine ⟨dk k, fun e he => ?_⟩
      have h5 := hdk k e he
      rw [hsub k, ← hdd] at h5
      exact h5
    · have hmkn : mk τ k = n := mk_eq_of_le (by omega)
      have hrho : pencilGenRank N M k = 0 := by have := hmk k; omega
      have hdz : d k = 0 := by
        have hb := hd k
        rw [hmkn, Nat.sub_self, Nat.mul_zero] at hb
        omega
      have hdkz : dk k = 0 := by
        have hb := hbound k
        rw [hrho, Nat.mul_zero] at hb
        omega
      refine ⟨0, fun e _ => ?_⟩
      have h5 := hdk k e (by omega)
      rw [hsub k, hdkz] at h5
      rw [hdz]
      exact h5

end Multidegree

end Height.Chain
