import Height.Chain.Substitution
import Height.Chain.Incidence
import Height.Geometry.Dimension.Affine
import Height.Steenrod.PartnerStrata
import Height.Geometry.Dimension.Homogeneous
import Height.Toolbox.MinorRank

/-!
# The conditional height count (`thm:conditional-height`)

The invariance of the pencil loci under reparametrisation and conjugation is
`Chain/Substitution.lean`.

* **Flagless pencils**, `lem:kernel-flag`(3): a pencil whose kernel flag has multidegree
  `0` is triangularizable, so a *flagless* pencil has `d ≠ 0`
  (`multidegree_ne_zero_of_flagless`).  The proof is the paper's: the kernel
  flag `S_k` is graded and saturated (`Height.Pencil`), hence graded free
  (`Graded.saturated_free_basis`); the Hilbert function of a graded free
  submodule (`Graded.HomogeneousBasis.finrank_sub`) turns `d_k = 0` into "all generators
  have degree `0`", i.e. `S_k` has a `B`-basis of constant vectors
  (`exists_const_basis`); evaluating a member of `S_k` at a parameter of the
  pencil's `ℙ¹` therefore lands in the space `kerConst N M k` of constant
  vectors of `S_k` (`evVec_mem_kerConst`), which gives
  `N V_k, M V_k ⊆ V_{k-1}` for `V_k := kerConst N M k`
  (`mulVec_mem_kerConst_of_multidegree_zero`); the rank count makes `V_n = ⊤`
  (`kerConst_eq_top_of_multidegree_zero`); and a greedy complete refinement of
  `V_•` produces the common flag (`greedyFlag`, `triangularizable_of_stab`,
  `triangularizable_of_multidegree_zero`).
* **Semicontinuity**: `isDegeneration_of_genericType` proves `λ ⊴ τ` for every
  member of a pencil of generic type `τ`, by clearing the `(r+1)`-minors of
  `(A + tB)^k` as a polynomial in `t` (`pencilPoly`) and specialising at
  `t = 0`.
* **The objects of the count**: the shear `(A, B) ↦ (A, B - A)`,
  the marking map `ψ = markedPair`, and the finite index type `Strata n` of
  types with a nonzero admissible multidegree (`lem:kernel-flag`(3): `d ≠ 0`,
  `d_k ≤ k(n - m_k)`).  The count itself is in `Chain/Hyps.lean`
  (`affineDim_fibreSet_le`, `flaglessPartner_subset_iUnion`,
  `affineDim_flaglessPartners_le_of_bounds`), beside the fibration theorems it
  consumes.
-/

namespace Height.Chain

open Height.Pencil

open Matrix Height.Graded Height.Steenrod Height.Toolbox QSteenrod
open Height.Geometry (affineDim pairCoords markedCoords PairIndex MarkedIndex fstMat sndMat
  matCoords)

universe u

/-! ### Constant vectors, and evaluation at a point of `ℙ¹` -/

section Constants

variable {K : Type u} [Field K] {n : ℕ}

variable (K n) in
/-- A vector of scalars, read in `B^n`. -/
noncomputable def constEmb : (Fin n → K) →ₗ[K] (Fin n → Graded.Poly K) :=
  LinearMap.pi fun i => (Algebra.linearMap K (Graded.Poly K)).comp (LinearMap.proj i)

@[simp] theorem constEmb_apply (v : Fin n → K) (i : Fin n) :
    constEmb K n v i = MvPolynomial.C (v i) := rfl

/-- Evaluation `μ ↦ 1`, `ν ↦ t`: the member of the pencil at the parameter
`t`. -/
noncomputable def evAlg (t : K) : Graded.Poly K →ₐ[K] K :=
  MvPolynomial.aeval ![(1 : K), t]

@[simp] theorem evAlg_mu (t : K) : evAlg t (mu : Graded.Poly K) = 1 := by simp [evAlg, mu]

@[simp] theorem evAlg_nu (t : K) : evAlg t (nu : Graded.Poly K) = t := by simp [evAlg, nu]

@[simp] theorem evAlg_C (t c : K) : evAlg t (MvPolynomial.C c : Graded.Poly K) = c := by
  simp [evAlg]

variable (n) in
/-- Evaluation applied coordinatewise. -/
noncomputable def evVec (t : K) : (Fin n → Graded.Poly K) →ₗ[K] (Fin n → K) :=
  LinearMap.pi fun i => (evAlg t).toLinearMap.comp (LinearMap.proj i)

@[simp] theorem evVec_apply (t : K) (f : Fin n → Graded.Poly K) (i : Fin n) :
    evVec n t f i = evAlg t (f i) := rfl

theorem evVec_smul (t : K) (g : Graded.Poly K) (f : Fin n → Graded.Poly K) :
    evVec n t (g • f) = (evAlg t g) • evVec n t f := by
  funext i
  simp [Algebra.smul_def]

/-- A homogeneous vector of degree `0` is the image of its evaluation. -/
theorem constEmb_evVec (t : K) {f : Fin n → Graded.Poly K}
    (hf : f ∈ (Graded.GradedPresentation.free K (Fin n)).piece 0) :
    constEmb K n (evVec n t f) = f := by
  funext i
  have hi : f i ∈ Bpiece K 0 := by simpa using (Graded.GradedPresentation.of K _).mem_piece.1 hf i
  rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) by norm_num, Bpiece_natCast,
    MvPolynomial.homogeneousSubmodule_zero] at hi
  obtain ⟨c, hc⟩ := Submodule.mem_one.1 hi
  rw [MvPolynomial.algebraMap_eq] at hc
  simp [← hc]

/-- Evaluation of the pencil applied to a constant vector. -/
theorem evVec_pencil_mulVec (t : K) (N M : Matrix (Fin n) (Fin n) K) (v : Fin n → K) :
    evVec n t (pencil N M *ᵥ constEmb K n v) = N *ᵥ v + t • (M *ᵥ v) := by
  funext i
  rw [evVec_apply, Matrix.mulVec_apply_eq_sum, map_sum]
  simp only [pencil, Matrix.of_apply, constEmb_apply, map_add, map_mul, evAlg_mu, evAlg_nu, evAlg_C, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec_apply_eq_sum, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

end Constants

/-! ### Multidegree zero forces a constant basis -/

section MultidegreeZero

variable {K : Type u} [Field K] {n : ℕ}

/-- The constant vectors of the `k`-th step of the kernel flag. -/
noncomputable def kerConst (N M : Matrix (Fin n) (Fin n) K) (k : ℕ) :
    Submodule K (Fin n → K) :=
  ((Height.Pencil.kerFlag N M k).restrictScalars K).comap (constEmb K n)

theorem mem_kerConst {N M : Matrix (Fin n) (Fin n) K} {k : ℕ} {v : Fin n → K} :
    v ∈ kerConst N M k ↔ constEmb K n v ∈ Height.Pencil.kerFlag N M k := Iff.rfl

/-- `lem:kernel-flag`(3), first half: if the degree-`k` piece of the kernel flag
has multidegree `0`, its `B`-basis consists of constant vectors, and its rank is
`m_k(τ)`. -/
theorem exists_const_basis (N M : Matrix (Fin n) (Fin n) K) {τ : Nat.Partition n}
    (hmd : HasMultidegree N M τ 0) (k : ℕ) (hk : 1 ≤ k) :
    ∃ w : Module.Basis (Fin (mk τ k)) (Graded.Poly K) (Height.Pencil.kerFlag N M k),
      ∀ i, ((w i : _) : Fin n → Graded.Poly K) ∈
        (Graded.GradedPresentation.free K (Fin n)).piece 0 := by
  classical
  set P : Graded.GradedPresentation K := Graded.GradedPresentation.free K (Fin n) with hP
  set S := Height.Pencil.kerFlag N M k with hS
  obtain ⟨ι, hι, b, u, H⟩ := Graded.exists_homogeneousBasis P S
    (Height.Pencil.isGraded_kerFlag N M k) (Height.Pencil.saturated_kerFlag N M k)
  obtain ⟨v, hv⟩ := H.exists_basis
  -- reindex by `Fin s`
  set s := Fintype.card ι with hs
  set eqv := Fintype.equivFin ι with heqv
  set w : Module.Basis (Fin s) (Graded.Poly K) S := v.reindex eqv with hw
  set c : Fin s → ℤ := fun i => b (eqv.symm i) with hc
  have hwc : ∀ i, ((w i : S) : Fin n → Graded.Poly K) ∈ P.piece (c i) := by
    intro i
    rw [hw, Module.Basis.reindex_apply, hv]
    exact H.homog _
  -- the generators have nonnegative degrees
  have hc0 : ∀ i, 0 ≤ c i := by
    intro i
    by_contra hneg
    push Not at hneg
    have hbot : P.piece (c i) = ⊥ := by
      refine P.piece_eq_bot ?_
      intro j
      simpa [hP] using hneg
    have hmem := hwc i
    rw [hbot] at hmem
    have hzero : ((w i : S) : Fin n → Graded.Poly K) = 0 := by simpa using hmem
    exact (w.ne_zero i) (Subtype.ext hzero)
  -- the Hilbert function
  have hHilb : ∀ e : ℤ, Module.finrank K (P.sub S e) = ∑ i, (e - c i + 1).toNat := by
    intro e
    refine (H.finrank_sub e).trans (Fintype.sum_equiv eqv _ _ fun i => ?_)
    rw [hc]
    simp
  obtain ⟨e₀, he₀⟩ := hmd k hk
  set E : ℕ := e₀ + (Finset.univ.sup fun i => (c i).toNat) with hE
  have hEc : ∀ i, c i ≤ (E : ℤ) := by
    intro i
    have h1 : (c i).toNat ≤ Finset.univ.sup fun i => (c i).toNat :=
      Finset.le_sup (f := fun i => (c i).toNat) (Finset.mem_univ i)
    have h2 : c i = ((c i).toNat : ℤ) := (Int.toNat_of_nonneg (hc0 i)).symm
    rw [h2, hE]
    push_cast
    omega
  have key : ∀ e : ℕ, E ≤ e →
      ((mk τ k : ℤ) * (e + 1)) = (s : ℤ) * (e + 1) - ∑ i, c i := by
    intro e he
    have h1 : Module.finrank K (kerPiece N M k e) = mk τ k * (e + 1) := by
      have := he₀ e (le_trans (by omega) he)
      simpa using this
    have h2 : Module.finrank K (P.sub S (e : ℤ)) = Module.finrank K (kerPiece N M k e) := by
      have hkp : P.sub S (e : ℤ) = kerPiece N M k e := Height.Pencil.sub_kerFlag N M k e
      rw [hkp]
    have h3 := hHilb (e : ℤ)
    rw [h2, h1] at h3
    have h4 : ∀ i, (((e : ℤ) - c i + 1).toNat : ℤ) = (e : ℤ) - c i + 1 := by
      intro i
      refine Int.toNat_of_nonneg ?_
      have := hEc i
      have : c i ≤ (e : ℤ) := le_trans this (by exact_mod_cast he)
      omega
    have h5 : ((∑ i, ((e : ℤ) - c i + 1).toNat : ℕ) : ℤ) = ∑ i, ((e : ℤ) - c i + 1) := by
      push_cast
      exact Finset.sum_congr rfl fun i _ => h4 i
    have h6 : ((mk τ k * (e + 1) : ℕ) : ℤ) = ∑ i, ((e : ℤ) - c i + 1) := by
      rw [← h5, h3]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_const] at h6
    simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h6
    push_cast at h6 ⊢
    linarith [h6]
  have hEq1 := key E le_rfl
  have hEq2 := key (E + 1) (by omega)
  push_cast at hEq1 hEq2
  have hsm : (mk τ k : ℤ) = (s : ℤ) := by linear_combination hEq2 - hEq1
  have hsum : ∑ i, c i = 0 := by
    rw [hsm] at hEq1
    linarith
  have hczero : ∀ i, c i = 0 := by
    intro i
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hc0 i)).1 hsum i (Finset.mem_univ i)
    exact this
  have hsm' : s = mk τ k := by exact_mod_cast hsm.symm
  refine ⟨w.reindex (finCongr hsm'), fun i => ?_⟩
  rw [Module.Basis.reindex_apply]
  have hmem := hwc ((finCongr hsm').symm i)
  rwa [hczero] at hmem

/-- Evaluation at a parameter maps the kernel flag into its constant part, once
the flag is generated by constant vectors. -/
theorem evVec_mem_kerConst {N M : Matrix (Fin n) (Fin n) K} {k s : ℕ}
    (w : Module.Basis (Fin s) (Graded.Poly K) (Height.Pencil.kerFlag N M k))
    (hw : ∀ i, ((w i : _) : Fin n → Graded.Poly K)
      ∈ (Graded.GradedPresentation.free K (Fin n)).piece 0)
    (t : K) {x : Fin n → Graded.Poly K} (hx : x ∈ Height.Pencil.kerFlag N M k) :
    evVec n t x ∈ kerConst N M k := by
  classical
  set P : Graded.GradedPresentation K := Graded.GradedPresentation.free K (Fin n)
    with hP
  have hgx : P.combLin (fun i => ((w i : Height.Pencil.kerFlag N M k) : Fin n → Graded.Poly K))
      (w.equivFun ⟨x, hx⟩) = x := by
    rw [P.combLin_basis w]
    simp
  rw [mem_kerConst, ← hgx, P.combLin_apply, map_sum, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [evVec_smul, map_smul, constEmb_evVec t (hw i),
    show (evAlg t (w.equivFun ⟨x, hx⟩ i)) • ((w i : Height.Pencil.kerFlag N M k) :
        Fin n → Graded.Poly K)
      = (MvPolynomial.C (evAlg t (w.equivFun ⟨x, hx⟩ i)) : Graded.Poly K) •
        ((w i : Height.Pencil.kerFlag N M k) : Fin n → Graded.Poly K) by
      rw [← MvPolynomial.algebraMap_eq, algebraMap_smul]]
  exact Submodule.smul_mem _ _ (w i).2

end MultidegreeZero

/-! ### A chain of subspaces refines to a common complete flag -/

section Flag

variable {K : Type u} [Field K] {n : ℕ}

/-- The greedy flag: add one vector at a time, chosen by `f`. -/
noncomputable def greedyFlag (f : Submodule K (Fin n → K) → (Fin n → K)) :
    ℕ → Submodule K (Fin n → K)
  | 0 => ⊥
  | i + 1 => greedyFlag f i ⊔ Submodule.span K {f (greedyFlag f i)}

@[simp] theorem greedyFlag_zero (f : Submodule K (Fin n → K) → (Fin n → K)) :
    greedyFlag f 0 = ⊥ := rfl

theorem greedyFlag_succ (f : Submodule K (Fin n → K) → (Fin n → K)) (i : ℕ) :
    greedyFlag f (i + 1) = greedyFlag f i ⊔ Submodule.span K {f (greedyFlag f i)} := rfl

theorem greedyFlag_mono (f : Submodule K (Fin n → K) → (Fin n → K)) :
    Monotone (greedyFlag f) :=
  monotone_nat_of_le_succ fun i => by rw [greedyFlag_succ]; exact le_sup_left

theorem mem_greedyFlag_succ (f : Submodule K (Fin n → K) → (Fin n → K)) (i : ℕ) :
    f (greedyFlag f i) ∈ greedyFlag f (i + 1) := by
  rw [greedyFlag_succ]
  exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)

/-- If every proper subspace `U` admits a vector outside it which both `N` and
`M` send into `U`, then `N` and `M` are simultaneously strictly upper
triangular. -/
theorem triangularizable_of_stab (N M : Matrix (Fin n) (Fin n) K)
    (hstab : ∀ U : Submodule K (Fin n → K), ∃ v : Fin n → K,
      U ≠ ⊤ → (v ∉ U ∧ N *ᵥ v ∈ U ∧ M *ᵥ v ∈ U)) :
    TriangularizablePencil K n N M := by
  classical
  choose f hf using hstab
  set W : ℕ → Submodule K (Fin n → K) := greedyFlag f with hW
  have hW0 : W 0 = ⊥ := greedyFlag_zero f
  have hWsucc : ∀ i, W (i + 1) = W i ⊔ Submodule.span K {f (W i)} := greedyFlag_succ f
  have hWmono : Monotone W := greedyFlag_mono f
  -- the flag lowers both matrices
  have hstep : ∀ (A : Matrix (Fin n) (Fin n) K),
      (∀ U : Submodule K (Fin n → K), U ≠ ⊤ → A *ᵥ f U ∈ U) →
      ∀ i, ∀ w ∈ W (i + 1), A *ᵥ w ∈ W i := by
    intro A hA i
    induction i with
    | zero =>
        intro w hw
        by_cases htop : W 0 = ⊤
        · rw [htop]; exact Submodule.mem_top
        · rw [hWsucc 0, hW0, bot_sup_eq, Submodule.mem_span_singleton] at hw
          obtain ⟨cst, rfl⟩ := hw
          rw [Matrix.mulVec_smul, hW0]
          exact Submodule.smul_mem _ _ (by simpa [hW0] using hA _ htop)
    | succ i ih =>
        intro w hw
        by_cases htop : W (i + 1) = ⊤
        · rw [htop]; exact Submodule.mem_top
        · rw [hWsucc (i + 1), Submodule.mem_sup] at hw
          obtain ⟨y, hy, z, hz, rfl⟩ := hw
          rw [Matrix.mulVec_add]
          refine Submodule.add_mem _ ?_ ?_
          · exact hWmono (Nat.le_succ i) (ih y hy)
          · rw [Submodule.mem_span_singleton] at hz
            obtain ⟨cst, rfl⟩ := hz
            rw [Matrix.mulVec_smul]
            exact Submodule.smul_mem _ _ (hA _ htop)
  have hN : ∀ i, ∀ w ∈ W (i + 1), N *ᵥ w ∈ W i :=
    hstep N fun U hU => (hf U hU).2.1
  have hM : ∀ i, ∀ w ∈ W (i + 1), M *ᵥ w ∈ W i :=
    hstep M fun U hU => (hf U hU).2.2
  -- dimensions
  have hrank : ∀ i, i ≤ n → Module.finrank K (W i) = i := by
    intro i
    induction i with
    | zero => intro _; rw [hW0]; simp
    | succ i ih =>
        intro hi
        have hi' : i ≤ n := by omega
        have hri := ih hi'
        have hne : W i ≠ ⊤ := by
          intro htop
          rw [htop] at hri
          have htn : Module.finrank K (⊤ : Submodule K (Fin n → K)) = n := by simp
          omega
        have hv : f (W i) ∉ W i := (hf (W i) hne).1
        have hmem : f (W i) ∈ W (i + 1) := mem_greedyFlag_succ f i
        have hlt : W i < W (i + 1) := by
          refine lt_of_le_of_ne (hWmono (Nat.le_succ i)) ?_
          intro heq
          rw [← heq] at hmem
          exact hv hmem
        have hup : Module.finrank K (W (i + 1)) ≤ Module.finrank K (W i) + 1 := by
          rw [hWsucc i]
          have hsum := Submodule.finrank_sup_add_finrank_inf_eq (W i)
            (Submodule.span K {f (W i)})
          have hspan : Module.finrank K (Submodule.span K {f (W i)}) ≤ 1 := by
            simpa using finrank_span_le_card (R := K) ({f (W i)} : Set (Fin n → K))
          omega
        have hdown := Submodule.finrank_lt_finrank_of_lt hlt
        omega
  have hWtop : W n = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    rw [hrank n le_rfl]
    simp
  -- the change of basis
  set e : Fin n → (Fin n → K) := fun i => f (W i.1) with he
  set g : Matrix (Fin n) (Fin n) K := Matrix.of fun row col => e col row with hg
  have hgv : ∀ v : Fin n → K, g *ᵥ v = ∑ col, v col • e col := by
    intro v
    funext row
    rw [Matrix.mulVec_apply_eq_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun col _ => by simp [hg, mul_comm]
  have hesingle : ∀ i : Fin n, g *ᵥ (Pi.single i 1) = e i := by
    intro i
    rw [hgv]
    simp
  have hemem : ∀ i : Fin n, e i ∈ W (i.1 + 1) := fun i => mem_greedyFlag_succ f i.1
  have hmaple : ∀ k, Submodule.map (Matrix.mulVecLin g) (standardFlag K n k) ≤ W k := by
    intro k
    rintro _ ⟨v, hv, rfl⟩
    show g *ᵥ v ∈ W k
    rw [hgv]
    refine Submodule.sum_mem _ fun col _ => ?_
    by_cases hcol : (col : ℕ) < k
    · exact Submodule.smul_mem _ _ (hWmono hcol (hemem col))
    · rw [(mem_standardFlag_iff K n k v).1 hv col (by omega), zero_smul]
      exact Submodule.zero_mem _
  have hmapge : ∀ k, k ≤ n → W k ≤ Submodule.map (Matrix.mulVecLin g) (standardFlag K n k) := by
    intro k
    induction k with
    | zero => intro _; rw [hW0]; exact bot_le
    | succ k ih =>
        intro hk
        rw [hWsucc k]
        refine sup_le ?_ ?_
        · exact le_trans (ih (by omega)) (Submodule.map_mono (standardFlag_mono K n
            (Nat.le_succ k)))
        · rw [Submodule.span_le, Set.singleton_subset_iff]
          have hkn : k < n := by omega
          refine ⟨Pi.single ⟨k, hkn⟩ 1, ?_, ?_⟩
          · intro i hi
            have hne : i ≠ (⟨k, hkn⟩ : Fin n) := by
              intro hcontra
              rw [hcontra] at hi
              simp at hi
            simp [hne]
          · show g *ᵥ (Pi.single (⟨k, hkn⟩ : Fin n) 1) = f (W k)
            rw [hesingle ⟨k, hkn⟩]
  have hmap : ∀ k, k ≤ n → Submodule.map (Matrix.mulVecLin g) (standardFlag K n k) = W k :=
    fun k hk => le_antisymm (hmaple k) (hmapge k hk)
  -- `g` is invertible
  have hsurj : Function.Surjective (Matrix.mulVecLin g) := by
    intro y
    have hy : y ∈ W n := by rw [hWtop]; trivial
    rw [← hmap n le_rfl] at hy
    obtain ⟨v, _, hv⟩ := hy
    exact ⟨v, hv⟩
  have hinj : Function.Injective (Matrix.mulVecLin g) :=
    (LinearMap.injective_iff_surjective).2 hsurj
  have hdet : IsUnit g.det := by
    rw [isUnit_iff_ne_zero]
    intro hzero
    obtain ⟨v, hv, hgv0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hzero
    exact hv (hinj (by simpa using hgv0))
  have hgu : IsUnit g := (Matrix.isUnit_iff_isUnit_det g).mpr hdet
  have hginv : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul g hdet
  -- conjugating back lands in the standard nilradical
  have hlower : ∀ A : Matrix (Fin n) (Fin n) K, (∀ i, ∀ w ∈ W (i + 1), A *ᵥ w ∈ W i) →
      g⁻¹ * A * g ∈ standardNilradical K n := by
    intro A hAW
    rw [mem_standardNilradical_iff_lowersStandardFlag]
    intro k v hv
    by_cases hk : n ≤ k
    · rw [standardFlag_eq_top_of_card_le K n k hk]
      exact Submodule.mem_top
    · push Not at hk
      have hgv1 : g *ᵥ v ∈ W (k + 1) := by
        rw [← hmap (k + 1) (by omega)]
        exact ⟨v, hv, rfl⟩
      have hAgv : A *ᵥ (g *ᵥ v) ∈ W k := hAW k _ hgv1
      rw [← hmap k (by omega)] at hAgv
      obtain ⟨y, hy, hyeq⟩ := hAgv
      have hval : (g⁻¹ * A * g) *ᵥ v = y := by
        rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hyeq]
        show g⁻¹ *ᵥ (g *ᵥ y) = y
        rw [Matrix.mulVec_mulVec, hginv, Matrix.one_mulVec]
      rw [hval]
      exact hy
  have hunit : ((hgu.unit : (Matrix (Fin n) (Fin n) K)ˣ) : Matrix (Fin n) (Fin n) K) = g :=
    hgu.unit_spec
  have hunitinv : ((hgu.unit⁻¹ : (Matrix (Fin n) (Fin n) K)ˣ) : Matrix (Fin n) (Fin n) K)
      = g⁻¹ := by
    rw [Matrix.coe_units_inv, hunit]
  exact ⟨hgu.unit, by rw [hunit, hunitinv]; exact hlower N hN,
    by rw [hunit, hunitinv]; exact hlower M hM⟩

end Flag

/-! ### `lem:kernel-flag`(3): multidegree zero means triangularizable -/

section Step2

variable {K : Type u} [Field K] {n : ℕ}

/-- Evaluation maps the kernel flag into its constant part, at every level. -/
theorem evVec_mem_kerConst_of_multidegree_zero {N M : Matrix (Fin n) (Fin n) K}
    {τ : Nat.Partition n} (hmd : HasMultidegree N M τ 0) (k : ℕ) (t : K)
    {x : Fin n → Graded.Poly K} (hx : x ∈ Height.Pencil.kerFlag N M k) :
    evVec n t x ∈ kerConst N M k := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    rw [Height.Pencil.mem_kerFlag, pow_zero, Matrix.one_mulVec] at hx
    rw [hx, map_zero]
    exact Submodule.zero_mem _
  · obtain ⟨w, hw⟩ := exists_const_basis N M hmd k hk
    exact evVec_mem_kerConst w hw t hx

/-- `N` and `M` lower the chain of constant subspaces. -/
theorem mulVec_mem_kerConst_of_multidegree_zero {N M : Matrix (Fin n) (Fin n) K}
    {τ : Nat.Partition n} (hmd : HasMultidegree N M τ 0) (k : ℕ) {v : Fin n → K}
    (hv : v ∈ kerConst N M (k + 1)) :
    N *ᵥ v ∈ kerConst N M k ∧ M *ᵥ v ∈ kerConst N M k := by
  have hx : pencil N M *ᵥ constEmb K n v ∈ Height.Pencil.kerFlag N M k :=
    Height.Pencil.pencil_mulVec_mem_kerFlag N M k _ hv
  have h0 := evVec_mem_kerConst_of_multidegree_zero hmd k 0 hx
  have h1 := evVec_mem_kerConst_of_multidegree_zero hmd k 1 hx
  rw [evVec_pencil_mulVec] at h0 h1
  simp only [zero_smul, add_zero, one_smul] at h0 h1
  refine ⟨h0, ?_⟩
  have hsub := Submodule.sub_mem _ h1 h0
  simpa using hsub

/-- The `n`-th step of the chain of constant subspaces is everything. -/
theorem kerConst_eq_top_of_multidegree_zero {N M : Matrix (Fin n) (Fin n) K}
    {τ : Nat.Partition n} (hmd : HasMultidegree N M τ 0) (hn : 1 ≤ n) :
    kerConst N M n = ⊤ := by
  classical
  obtain ⟨w, hw⟩ := exists_const_basis N M hmd n hn
  have hmkn : mk τ n = n := Height.Pencil.sum_conjPart τ
  set v : Fin (mk τ n) → (Fin n → K) :=
    fun i => evVec n 0 ((w i : Height.Pencil.kerFlag N M n) : Fin n → Graded.Poly K) with hv
  have hconst : ∀ i, constEmb K n (v i)
      = ((w i : Height.Pencil.kerFlag N M n) : Fin n → Graded.Poly K) := fun i =>
    constEmb_evVec 0 (hw i)
  have hmem : ∀ i, v i ∈ kerConst N M n := by
    intro i
    rw [mem_kerConst, hconst i]
    exact (w i).2
  have hli : LinearIndependent K v := by
    rw [Fintype.linearIndependent_iff]
    intro lam hlam i
    set P : Graded.GradedPresentation K :=
      Graded.GradedPresentation.free K (Fin n) with hP
    have hzero : P.combLin
        (fun i => ((w i : Height.Pencil.kerFlag N M n) : Fin n → Graded.Poly K))
        (fun i => (MvPolynomial.C (lam i) : Graded.Poly K)) = 0 := by
      rw [P.combLin_apply]
      have hstep : ∀ i, (MvPolynomial.C (lam i) : Graded.Poly K) •
          ((w i : Height.Pencil.kerFlag N M n) : Fin n → Graded.Poly K)
          = lam i • constEmb K n (v i) := by
        intro i
        rw [hconst i, ← MvPolynomial.algebraMap_eq, algebraMap_smul]
      rw [Finset.sum_congr rfl fun i _ => hstep i]
      have hpull : ∑ i, lam i • constEmb K n (v i) = constEmb K n (∑ i, lam i • v i) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun i _ => (map_smul _ _ _).symm
      rw [hpull, hlam, map_zero]
    have hzero' : P.combLin
        (fun i => ((w i : Height.Pencil.kerFlag N M n) : Fin n → Graded.Poly K))
        (fun i => (MvPolynomial.C (lam i) : Graded.Poly K))
        = P.combLin
          (fun i => ((w i : Height.Pencil.kerFlag N M n) : Fin n → Graded.Poly K)) 0 := by
      rw [hzero, map_zero]
    have hci := congrFun (P.combLin_injective
      (w.linearIndependent.map' _ (Submodule.ker_subtype _)) hzero') i
    simp only [Pi.zero_apply] at hci
    exact MvPolynomial.C_injective (Fin 2) K (by simpa using hci)
  have hcard : Fintype.card (Fin (mk τ n)) = Module.finrank K (Fin n → K) := by
    simp [hmkn]
  have hspan : Submodule.span K (Set.range v) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' hcard
  refine top_le_iff.mp ?_
  rw [← hspan, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact hmem i

/-- `lem:kernel-flag`(3): a pencil whose kernel flag has multidegree `0` is
simultaneously triangularizable. -/
theorem triangularizable_of_multidegree_zero {N M : Matrix (Fin n) (Fin n) K}
    {τ : Nat.Partition n} (hmd : HasMultidegree N M τ 0) :
    TriangularizablePencil K n N M := by
  classical
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact ⟨1, fun i => i.elim0, fun i => i.elim0⟩
  · have htop : kerConst N M n = ⊤ := kerConst_eq_top_of_multidegree_zero hmd hn
    refine triangularizable_of_stab N M fun U => ?_
    by_cases hU : U = ⊤
    · exact ⟨0, fun h => absurd hU h⟩
    · have hex : ∃ k, ¬ (kerConst N M k ≤ U) := by
        refine ⟨n, ?_⟩
        rw [htop]
        intro hle
        exact hU (top_le_iff.mp hle)
      have hspec : ¬ (kerConst N M (Nat.find hex) ≤ U) := Nat.find_spec hex
      have hpos : Nat.find hex ≠ 0 := by
        intro hzero
        refine hspec ?_
        rw [hzero]
        intro y hy
        rw [mem_kerConst, Height.Pencil.mem_kerFlag, pow_zero, Matrix.one_mulVec] at hy
        have hy0 : y = 0 := by
          funext i
          have := congrFun hy i
          simpa using congrArg (evAlg (0 : K)) this
        rw [hy0]
        exact Submodule.zero_mem _
      have hprev : kerConst N M (Nat.find hex - 1) ≤ U :=
        not_not.mp (Nat.find_min hex (by omega))
      have hsucc : Nat.find hex - 1 + 1 = Nat.find hex := by omega
      obtain ⟨y, hy, hyU⟩ := SetLike.not_le_iff_exists.mp hspec
      refine ⟨y, fun _ => ⟨hyU, ?_, ?_⟩⟩
      · refine hprev ?_
        exact (mulVec_mem_kerConst_of_multidegree_zero hmd (Nat.find hex - 1)
          (by rw [hsucc]; exact hy)).1
      · refine hprev ?_
        exact (mulVec_mem_kerConst_of_multidegree_zero hmd (Nat.find hex - 1)
          (by rw [hsucc]; exact hy)).2

/-- A flagless pencil has a nonzero multidegree. -/
theorem multidegree_ne_zero_of_flagless {N M : Matrix (Fin n) (Fin n) K}
    {τ : Nat.Partition n} {d : ℕ → ℕ} (hf : FlaglessPencil K n N M)
    (hmd : HasMultidegree N M τ d) : d ≠ 0 := by
  intro hd
  subst hd
  exact hf.2 (triangularizable_of_multidegree_zero hmd)

end Step2

/-! ### Semicontinuity of the rank along a pencil (`λ ⊴ τ`) -/

section Degeneration

variable {K : Type u} [Field K] {n : ℕ}

/-- The kernel dimensions of the powers are increasing. -/
theorem finrank_ker_pow_mono (y : Module.End K (Fin n → K)) {a b : ℕ} (hab : a ≤ b) :
    Module.finrank K (LinearMap.ker (y ^ a)) ≤ Module.finrank K (LinearMap.ker (y ^ b)) :=
  Submodule.finrank_mono ((LinearMap.iterateKer y).monotone hab)

/-- Telescoping: `∑_{m=1}^{k} conj y m = dim ker (y^k)`. -/
theorem sum_conj_eq_finrank_ker (y : Module.End K (Fin n → K)) (k : ℕ) :
    ∑ m ∈ Finset.Icc 1 k, conj y m = Module.finrank K (LinearMap.ker (y ^ k)) := by
  induction k with
  | zero =>
      rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty, pow_zero,
        Module.End.one_eq_id, LinearMap.ker_id, finrank_bot]
  | succ k ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih]
      have hmono := finrank_ker_pow_mono y (show k ≤ k + 1 by omega)
      show _ + (Module.finrank K (LinearMap.ker (y ^ (k + 1))) -
        Module.finrank K (LinearMap.ker (y ^ k))) = _
      omega

/-- For a matrix of Jordan type `τ`, `rank (X^k) + m_k(τ) = n`. -/
theorem rank_pow_add_mk_of_hasType {X : Matrix (Fin n) (Fin n) K} {τ : Nat.Partition n}
    (h : HasType X τ) (k : ℕ) :
    Matrix.rank (X ^ k) + mk τ k = n := by
  have hpow : (Matrix.toLinAlgEquiv' X : (Fin n → K) →ₗ[K] (Fin n → K)) ^ k
      = Matrix.toLinAlgEquiv' (X ^ k) := (map_pow _ _ _).symm
  have hker : Module.finrank K
      (LinearMap.ker (Matrix.toLinAlgEquiv' (X ^ k) : (Fin n → K) →ₗ[K] (Fin n → K)))
      = mk τ k := by
    rw [← hpow, ← sum_conj_eq_finrank_ker]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mem_Icc] at hm
    exact h m hm.1
  have htol : (Matrix.toLinAlgEquiv' (X ^ k) : (Fin n → K) →ₗ[K] (Fin n → K))
      = (X ^ k).mulVecLin := rfl
  have hrn := LinearMap.finrank_range_add_finrank_ker
    (Matrix.toLinAlgEquiv' (X ^ k) : (Fin n → K) →ₗ[K] (Fin n → K))
  rw [hker, htol] at hrn
  have hdim : Module.finrank K (Fin n → K) = n := by simp
  rw [hdim] at hrn
  exact hrn

/-- `λ ⊴ τ`: every member of a pencil of generic type `τ` has a type that
degenerates from `τ` (semicontinuity of the rank of `X^k`). -/
theorem isDegeneration_of_genericType [Infinite K] {A B : Matrix (Fin n) (Fin n) K}
    {τ : Nat.Partition n} (h : GenericType A B τ) : IsDegeneration τ A := by
  classical
  obtain ⟨F, hF⟩ := h
  intro k hk
  by_contra hcon
  push Not at hcon
  -- pick a parameter off the drop locus
  obtain ⟨t₁, ht₁⟩ := Set.Infinite.nonempty ((F : Set K).toFinite.infinite_compl)
  have hgen : ∀ t : K, t ∉ F → Matrix.rank ((A + t • B) ^ k) + mk τ k = n :=
    fun t ht => rank_pow_add_mk_of_hasType (hF t ht) k
  have hmk : mk τ k ≤ n := by
    have := hgen t₁ (by simpa using ht₁)
    omega
  have hlt : (n - mk τ k) + 1 ≤ Matrix.rank (A ^ k) := by omega
  obtain ⟨f, g, hfg⟩ := Height.Toolbox.exists_submatrix_det_ne_zero (A ^ k) hlt
  set Q : Polynomial K := ((pencilPoly A B ^ k).submatrix f g).det with hQ
  have hroot : ∀ t : K, t ∉ F → Q.IsRoot t := by
    intro t ht
    have hrank := hgen t ht
    by_contra hne
    have : (n - mk τ k) + 1 ≤ Matrix.rank ((A + t • B) ^ k) := by
      refine Height.Toolbox.le_rank_of_submatrix_det_ne_zero _ f g ?_
      rw [← det_submatrix_pencilPoly_eval A B f g k t]
      exact hne
    omega
  have hQzero : Q = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot Q (Set.Infinite.mono ?_
      ((F : Set K).toFinite.infinite_compl))
    intro t ht
    exact hroot t (by simpa using ht)
  have hzero := det_submatrix_pencilPoly_eval A B f g k (0 : K)
  rw [← hQ, hQzero] at hzero
  simp only [Polynomial.eval_zero, zero_smul, add_zero] at hzero
  exact hfg hzero.symm

end Degeneration

/-! ### Arithmetic in `WithBot ℕ∞` -/

section Arith

theorem le_natCast_of_add_le {x : WithBot ℕ∞} {A B C : ℕ}
    (h : (((A : ℕ) : ℕ∞) : WithBot ℕ∞) + x ≤ (((B : ℕ) : ℕ∞) : WithBot ℕ∞))
    (hABC : ∀ c : ℕ, A + c ≤ B → c ≤ C) :
    x ≤ (((C : ℕ) : ℕ∞) : WithBot ℕ∞) := by
  induction x using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe y =>
      induction y using ENat.recTopCoe with
      | top =>
          exfalso
          rw [← WithBot.coe_add, WithBot.coe_le_coe] at h
          simp at h
      | coe c =>
          have hAc : A + c ≤ B := by
            have hcast : (((A : ℕ) : ℕ∞) : WithBot ℕ∞) + (((c : ℕ) : ℕ∞) : WithBot ℕ∞)
                = ((((A + c : ℕ)) : ℕ∞) : WithBot ℕ∞) := by
              push_cast
              ring
            rw [hcast] at h
            exact_mod_cast h
          exact_mod_cast hABC c hAc

end Arith

/-! ### The shear `(A, B) ↦ (A, B - A)` -/

section Shear

variable {K : Type u} [Field K] {n : ℕ}

/-- The shear `(A, B) ↦ (A, B - A)` in pair coordinates. -/
def shearPair (x : ((Fin n × Fin n) ⊕ (Fin n × Fin n)) → K) :
    ((Fin n × Fin n) ⊕ (Fin n × Fin n)) → K :=
  Sum.elim (fun ij => x (Sum.inl ij)) (fun ij => x (Sum.inr ij) - x (Sum.inl ij))

/-- Its inverse `(A, M) ↦ (A, A + M)`. -/
def unshearPair (x : ((Fin n × Fin n) ⊕ (Fin n × Fin n)) → K) :
    ((Fin n × Fin n) ⊕ (Fin n × Fin n)) → K :=
  Sum.elim (fun ij => x (Sum.inl ij)) (fun ij => x (Sum.inr ij) + x (Sum.inl ij))

theorem isPolyMap_shearPair : Height.Geometry.IsPolyMap (shearPair (K := K) (n := n)) := by
  refine ⟨Sum.elim (fun ij => MvPolynomial.X (Sum.inl ij))
    (fun ij => MvPolynomial.X (Sum.inr ij) - MvPolynomial.X (Sum.inl ij)), fun y j => ?_⟩
  cases j <;> simp [shearPair]

theorem isPolyMap_unshearPair : Height.Geometry.IsPolyMap (unshearPair (K := K) (n := n)) := by
  refine ⟨Sum.elim (fun ij => MvPolynomial.X (Sum.inl ij))
    (fun ij => MvPolynomial.X (Sum.inr ij) + MvPolynomial.X (Sum.inl ij)), fun y j => ?_⟩
  cases j <;> simp [unshearPair]

theorem unshear_shear (x : ((Fin n × Fin n) ⊕ (Fin n × Fin n)) → K) :
    unshearPair (shearPair x) = x := by
  funext j
  cases j <;> simp [unshearPair, shearPair]

theorem shearPair_pairCoords (A B : Matrix (Fin n) (Fin n) K) :
    shearPair (pairCoords (A, B)) = pairCoords (A, B - A) := by
  funext j
  cases j <;> simp [shearPair]

end Shear

/-! ### The objects of the count -/

section Count

variable {K : Type u} [Field K] {n : ℕ}

/-- The marking map `ψ`: the two marked members of the pencil. -/
def markedPair (q : Matrix (Fin n) (Fin n) K × Matrix (Fin n) (Fin n) K × K × K) :
    Matrix (Fin n) (Fin n) K × Matrix (Fin n) (Fin n) K :=
  (q.1 + q.2.2.1 • q.2.1, q.1 + q.2.2.2 • q.2.1)

/-- `n ≤ c(τ)`: each part of the conjugate partition is at most its square. -/
theorem le_cType (τ : Nat.Partition n) : n ≤ cType τ := by
  refine le_trans (le_of_eq (Height.Pencil.sum_conjPart τ).symm) ?_
  exact Finset.sum_le_sum fun m _ => Nat.le_self_pow (by norm_num) _

/-- The conjugate partition vanishes beyond `n`. -/
theorem conjPart_eq_zero_of_lt {τ : Nat.Partition n} {m : ℕ} (hm : n < m) :
    conjPart τ m = 0 := by
  rw [conjPart, Multiset.card_eq_zero, Multiset.filter_eq_nil]
  intro a ha
  have hle : a ≤ n := by
    rw [← τ.parts_sum]
    exact Multiset.single_le_sum (fun _ _ => Nat.zero_le _) a ha
  omega

/-- `m_k(τ) = n` once `k ≥ n`. -/
theorem mk_eq_of_le {τ : Nat.Partition n} {k : ℕ} (hk : n ≤ k) : mk τ k = n := by
  refine Eq.trans ?_ (Height.Pencil.sum_conjPart τ)
  refine (Finset.sum_subset (Finset.Icc_subset_Icc_right hk) fun m hm hm' => ?_).symm
  rw [Finset.mem_Icc] at hm hm'
  exact conjPart_eq_zero_of_lt (by omega)

end Count

section CountKbar

variable (p r n : ℕ) [Fact p.Prime]

/-- The finite index set of the count: types together with a nonzero admissible
multidegree (`lem:kernel-flag`(3): `0 ≠ d`, `d_k ≤ k (n - m_k)`). -/
def Strata : Type :=
  {q : Nat.Partition n × (ℕ → ℕ) // q.2 ≠ 0 ∧ ∀ k, q.2 k ≤ k * (n - mk q.1 k)}

instance : Finite (Strata n) := by
  classical
  have hbnd : ∀ (q : Strata n) (i : Fin n), q.1.2 (i : ℕ) < n * n + 1 := by
    intro q i
    have hb := q.2.2 (i : ℕ)
    have h2 : (i : ℕ) * (n - mk q.1.1 (i : ℕ)) ≤ n * n :=
      Nat.mul_le_mul (le_of_lt i.2) (Nat.sub_le _ _)
    omega
  refine Finite.of_injective
    (fun q : Strata n => (q.1.1, fun i : Fin n => (⟨q.1.2 (i : ℕ), hbnd q i⟩ : Fin (n * n + 1))))
    ?_
  intro q q' heq
  have heq' : (q.1.1, fun i : Fin n => (⟨q.1.2 (i : ℕ), hbnd q i⟩ : Fin (n * n + 1)))
      = (q'.1.1, fun i : Fin n => (⟨q'.1.2 (i : ℕ), hbnd q' i⟩ : Fin (n * n + 1))) := heq
  rw [Prod.mk.injEq] at heq'
  obtain ⟨hτ, hdd⟩ := heq'
  refine Subtype.ext (Prod.ext hτ ?_)
  funext k
  by_cases hk : k < n
  · have h := congrFun hdd ⟨k, hk⟩
    exact congrArg Fin.val h
  · have h1 : q.1.2 k = 0 := by
      have hb := q.2.2 k
      rw [mk_eq_of_le (show n ≤ k by omega), Nat.sub_self, Nat.mul_zero] at hb
      omega
    have h2 : q'.1.2 k = 0 := by
      have hb := q'.2.2 k
      rw [mk_eq_of_le (show n ≤ k by omega), Nat.sub_self, Nat.mul_zero] at hb
      omega
    rw [h1, h2]


end CountKbar

end Height.Chain
