import Height.Steenrod.LangSemilinear

/-!
# Lang–Steinberg descent for Frobenius-semilinear maps

The input for `thm:lang`, a basis of fixed vectors, is proved here by descent.

Let `K` be algebraically closed of characteristic `p`, `q = p ^ r`, and let
`ψ : V →+ V` be additive, `q`-semilinear (`ψ (a • x) = a ^ q • ψ x`) and
injective on a finite-dimensional `K`-space `V`.  Then the `ψ`-fixed vectors
span `V` over `K` (`span_fixed_eq_top`), so `V` has a `K`-basis of fixed
vectors (`exists_fixed_basis`).  The two ingredients are:

* `exists_fixed_ne_zero`: a nonzero fixed vector exists when `V ≠ 0`.  Take
  `v ≠ 0` and let `N + 1` be the length of the longest independent Krylov
  block `v, ψ v, …, ψ^N v`, so that `ψ^{N+1} v = ∑_{i ≤ N} A i • ψ^i v`.  The
  candidate `w = ∑_{i ≤ N} λ_i(t) • ψ^i v` with
  `λ_i(t) = ∑_{j ≤ i} A (i - j) ^ (q ^ j) * t ^ (q ^ (j + 1))` satisfies
  `ψ w - w = (λ_N(t) ^ q - t ^ q) • ψ^{N+1} v`, so `w` is fixed as soon as
  `λ_N(t) = t`.  That is one polynomial equation `t * h t = 0` in one unknown
  whose cofactor `h` has constant term `-1` and degree `q ^ (N+1) - 1 ≥ 1`
  (the top coefficient is `A 0 ^ (q ^ N)`, and `A 0 ≠ 0` because `ψ` is
  injective); `IsAlgClosed.exists_root` supplies a root `t ≠ 0`, and then
  `λ_N(t) = t ≠ 0` forces `w ≠ 0`.
* the lift along a quotient by a fixed line: if `ψ w = w`, `w ≠ 0` and `ψ`
  descends to `V ⧸ (K ∙ w)`, a fixed vector of the quotient lifts to a fixed
  vector of `V` after correcting by `μ • w`, where `μ` solves the
  Artin–Schreier equation `μ ^ q - μ + a = 0` (`exists_frobenius_pow_sub_mul_eq`).

Induction on `finrank` then gives the spanning statement.
-/

namespace Height.Steenrod

open Polynomial

universe u v

section Descent

variable (p r : ℕ) [Fact p.Prime] [NeZero r]
variable {K : Type u} [Field K] [ExpChar K p] [IsAlgClosed K]

/-- `q = p ^ r` is at least `2`. -/
theorem two_le_frobPow : 2 ≤ p ^ r := by
  have h := one_lt_pow' (Fact.out : Nat.Prime p).one_lt (NeZero.ne r)
  omega

omit [ExpChar K p] in
/-- Every scalar of an algebraically closed field is a `q`-th power. -/
theorem exists_pow_frobPow_eq (a : K) : ∃ b : K, b ^ (p ^ r) = a :=
  IsAlgClosed.exists_pow_nat_eq a (by have := two_le_frobPow p r; omega)

variable {V : Type v} [AddCommGroup V] [Module K V]

/-- **Step 1 of Lang–Steinberg descent.**  An injective `q`-semilinear additive
endomorphism of a nonzero finite-dimensional space over an algebraically closed
field of characteristic `p`, `q = p ^ r`, has a nonzero fixed vector. -/
theorem exists_fixed_ne_zero [FiniteDimensional K V]
    (ψ : V →+ V)
    (hsmul : ∀ (a : K) (x : V), ψ (a • x) = a ^ (p ^ r) • ψ x)
    (hinj : Function.Injective ψ)
    {v : V} (hv : v ≠ 0) :
    ∃ w : V, w ≠ 0 ∧ ψ w = w := by
  classical
  have hq2 : 2 ≤ p ^ r := two_le_frobPow p r
  have hexp2 : ∀ j : ℕ, 2 ≤ (p ^ r) ^ (j + 1) := by
    intro j
    calc 2 ≤ p ^ r := hq2
      _ = (p ^ r) ^ 1 := (pow_one _).symm
      _ ≤ (p ^ r) ^ (j + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  -- The Krylov sequence `e i = ψ^i v`.
  set e : ℕ → V := fun i => (ψ : V → V)^[i] v with hedef
  have hesucc : ∀ i, ψ (e i) = e (i + 1) := fun i =>
    (Function.iterate_succ_apply' (ψ : V → V) i v).symm
  have hsnoc : ∀ k : ℕ, (fun i : Fin (k + 1) => e (i : ℕ)) =
      Fin.snoc (fun i : Fin k => e (i : ℕ)) (e k) := by
    intro k
    funext i
    induction i using Fin.lastCases with
    | last => simp
    | cast j => simp
  -- The first dependent length.
  have hdep : ∃ m : ℕ, ¬ LinearIndependent K (fun i : Fin m => e (i : ℕ)) := by
    refine ⟨Module.finrank K V + 1, fun hcon => ?_⟩
    have h := hcon.fintype_card_le_finrank
    simp only [Fintype.card_fin] at h
    omega
  have hmspec : ¬ LinearIndependent K (fun i : Fin (Nat.find hdep) => e (i : ℕ)) :=
    Nat.find_spec hdep
  have hmmin : ∀ k, k < Nat.find hdep →
      LinearIndependent K (fun i : Fin k => e (i : ℕ)) := fun k hk =>
    not_not.mp (Nat.find_min hdep hk)
  have hm0 : Nat.find hdep ≠ 0 := by
    intro h
    rw [h] at hmspec
    exact hmspec linearIndependent_empty_type
  have hm1 : Nat.find hdep ≠ 1 := by
    intro h
    rw [h] at hmspec
    refine hmspec ?_
    rw [linearIndependent_unique_iff]
    simpa [hedef] using hv
  obtain ⟨N, hN⟩ : ∃ N, Nat.find hdep = N + 2 := ⟨Nat.find hdep - 2, by omega⟩
  rw [hN] at hmspec
  have hindep : LinearIndependent K (fun i : Fin (N + 1) => e (i : ℕ)) :=
    hmmin (N + 1) (by omega)
  have hspan : e (N + 1) ∈
      Submodule.span K (Set.range (fun i : Fin (N + 1) => e (i : ℕ))) := by
    by_contra hcon
    exact hmspec (by rw [hsnoc (N + 1)]; exact linearIndependent_finSnoc.mpr ⟨hindep, hcon⟩)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hspan
  set A : ℕ → K := fun i => if h : i < N + 1 then c ⟨i, h⟩ else 0 with hAdef
  have hA : ∑ i ∈ Finset.range (N + 1), A i • e i = e (N + 1) := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => A i • e i) (N + 1), ← hc]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hAi : A (i : ℕ) = c i := by
      simp only [hAdef]
      rw [dite_eq_left i.isLt]
    rw [hAi]
  -- Injectivity of `ψ` forces the constant term of the dependence to be nonzero.
  have hA0 : A 0 ≠ 0 := by
    intro h0
    choose B hB using fun i : ℕ => exists_pow_frobPow_eq (K := K) p r (A (i + 1))
    have hsum : ∑ i ∈ Finset.range N, A (i + 1) • e (i + 1) = e (N + 1) := by
      rw [← hA, Finset.sum_range_succ' (fun i => A i • e i) N, h0, zero_smul, add_zero]
    have hpsi : ψ (∑ i ∈ Finset.range N, B i • e i) = e (N + 1) := by
      rw [map_sum, ← hsum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hsmul, hB i, hesucc]
    have heq : ∑ i ∈ Finset.range N, B i • e i = e N := by
      apply hinj
      rw [hpsi, hesucc]
    have hmem : e N ∈ Submodule.span K (Set.range (fun i : Fin N => e (i : ℕ))) := by
      refine (Submodule.mem_span_range_iff_exists_fun K).mpr ⟨fun i : Fin N => B (i : ℕ), ?_⟩
      rw [Fin.sum_univ_eq_sum_range (fun i => B i • e i) N]
      exact heq
    exact (linearIndependent_finSnoc.mp (by rw [← hsnoc N]; exact hindep)).2 hmem
  -- The one-variable equation.
  set Pol : Polynomial K :=
    (∑ j ∈ Finset.range (N + 1),
        Polynomial.C (A (N - j) ^ ((p ^ r) ^ j)) *
          Polynomial.X ^ ((p ^ r) ^ (j + 1) - 1)) - 1 with hPoldef
  have hPol0 : Pol.eval 0 = -1 := by
    rw [hPoldef]
    simp only [Polynomial.eval_sub, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
    rw [Finset.sum_eq_zero, zero_sub]
    intro j _
    rw [zero_pow (by have := hexp2 j; omega), mul_zero]
  have hPolcoeff : Pol.coeff ((p ^ r) ^ (N + 1) - 1) = A 0 ^ ((p ^ r) ^ N) := by
    rw [hPoldef, Polynomial.coeff_sub, Polynomial.finsetSum_coeff]
    have hone : (1 : Polynomial K).coeff ((p ^ r) ^ (N + 1) - 1) = 0 := by
      rw [Polynomial.coeff_one, ite_eq_right]
      have := hexp2 N
      omega
    rw [hone, sub_zero]
    rw [Finset.sum_eq_single_of_mem N (Finset.self_mem_range_succ N)]
    · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, ite_eq_left rfl, mul_one, Nat.sub_self]
    · intro j _ hj
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, ite_eq_right, mul_zero]
      intro hcon
      have h1 := hexp2 N
      have h2 := hexp2 j
      have h3 : (p ^ r) ^ (N + 1) = (p ^ r) ^ (j + 1) := by omega
      exact hj (by simpa using (Nat.pow_right_injective hq2 h3).symm)
  have hPoldeg : Pol.degree ≠ 0 := by
    intro hdeg
    have hle : (p ^ r) ^ (N + 1) - 1 ≤ Pol.natDegree :=
      Polynomial.le_natDegree_of_ne_zero (by rw [hPolcoeff]; exact pow_ne_zero _ hA0)
    have hzero : Pol.natDegree = 0 :=
      Polynomial.natDegree_eq_zero_iff_degree_le_zero.mpr (le_of_eq hdeg)
    have := hexp2 N
    omega
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_root Pol hPoldeg
  have ht0 : t ≠ 0 := by
    intro h
    rw [Polynomial.IsRoot.def, h, hPol0] at ht
    exact one_ne_zero (neg_eq_zero.mp ht)
  -- The coefficients of the fixed vector.
  set lam : ℕ → K := fun i =>
    ∑ j ∈ Finset.range (i + 1),
      A (i - j) ^ ((p ^ r) ^ j) * t ^ ((p ^ r) ^ (j + 1)) with hlamdef
  have hlam0 : lam 0 = A 0 * t ^ (p ^ r) := by simp [hlamdef]
  have hlamsucc : ∀ i, lam (i + 1) = (lam i) ^ (p ^ r) + A (i + 1) * t ^ (p ^ r) := by
    intro i
    have hpow : (lam i) ^ (p ^ r) =
        ∑ j ∈ Finset.range (i + 1),
          A (i - j) ^ ((p ^ r) ^ (j + 1)) * t ^ ((p ^ r) ^ (j + 1 + 1)) := by
      simp only [hlamdef]
      rw [sum_pow_char_pow (p := p) (n := r)]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hA' : (A (i - j) ^ ((p ^ r) ^ j)) ^ (p ^ r) =
          A (i - j) ^ ((p ^ r) ^ (j + 1)) := by
        rw [← pow_mul (A (i - j)) ((p ^ r) ^ j) (p ^ r), ← pow_succ (p ^ r) j]
      have ht' : (t ^ ((p ^ r) ^ (j + 1))) ^ (p ^ r) =
          t ^ ((p ^ r) ^ (j + 1 + 1)) := by
        rw [← pow_mul t ((p ^ r) ^ (j + 1)) (p ^ r), ← pow_succ (p ^ r) (j + 1)]
      rw [mul_pow, hA', ht']
    rw [hpow]
    simp only [hlamdef]
    rw [Finset.sum_range_succ'
      (fun j => A (i + 1 - j) ^ ((p ^ r) ^ j) * t ^ ((p ^ r) ^ (j + 1))) (i + 1)]
    congr 1
    · refine Finset.sum_congr rfl fun j _ => ?_
      have hidx : i + 1 - (j + 1) = i - j := by omega
      rw [hidx]
    · simp
  have hlamN : lam N = t := by
    have hev : Pol.eval t =
        (∑ j ∈ Finset.range (N + 1),
          A (N - j) ^ ((p ^ r) ^ j) * t ^ ((p ^ r) ^ (j + 1) - 1)) - 1 := by
      rw [hPoldef]
      simp only [Polynomial.eval_sub, Polynomial.eval_finsetSum, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
    have hkey : t * Pol.eval t = lam N - t := by
      rw [hev, mul_sub, mul_one, Finset.mul_sum, hlamdef]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      have hk : (p ^ r) ^ (j + 1) - 1 + 1 = (p ^ r) ^ (j + 1) := by
        have := hexp2 j
        omega
      rw [mul_left_comm, ← pow_succ', hk]
    rw [Polynomial.IsRoot.def] at ht
    rw [ht, mul_zero] at hkey
    exact sub_eq_zero.mp hkey.symm
  -- The fixed vector.
  refine ⟨∑ i ∈ Finset.range (N + 1), lam i • e i, ?_, ?_⟩
  · intro hw0
    have hzero := (Fintype.linearIndependent_iff.mp hindep)
      (fun i : Fin (N + 1) => lam (i : ℕ))
      (by rw [Fin.sum_univ_eq_sum_range (fun i => lam i • e i) (N + 1)]; exact hw0)
      ⟨N, by omega⟩
    simp only at hzero
    rw [hlamN] at hzero
    exact ht0 hzero
  · have hψw : ψ (∑ i ∈ Finset.range (N + 1), lam i • e i) =
        ∑ i ∈ Finset.range (N + 1), (lam i) ^ (p ^ r) • e (i + 1) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hsmul, hesucc]
    have hwalt : ∑ i ∈ Finset.range (N + 1), lam i • e i =
        (∑ i ∈ Finset.range N, (lam i) ^ (p ^ r) • e (i + 1)) +
          t ^ (p ^ r) • e (N + 1) := by
      rw [Finset.sum_range_succ' (fun i => lam i • e i) N, ← hA,
        Finset.sum_range_succ' (fun i => A i • e i) N, smul_add, Finset.smul_sum, ← add_assoc]
      congr 1
      · rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hlamsucc i]
        module
      · rw [hlam0]
        module
    rw [hψw, Finset.sum_range_succ (fun i => (lam i) ^ (p ^ r) • e (i + 1)) N, hlamN]
    exact hwalt.symm

/-- **Step 2 of Lang–Steinberg descent.**  The `ψ`-fixed vectors span `V`.
Induction on `finrank K V`: a nonzero fixed vector `w` spans a `ψ`-stable line,
`ψ` descends injectively to `V ⧸ (K ∙ w)`, every fixed vector of the quotient
lifts to a fixed vector of `V` by solving an Artin–Schreier equation, and the
inductive hypothesis applies to the quotient. -/
private theorem span_fixed_aux (n : ℕ) :
    ∀ {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      (ψ : V →+ V), (∀ (a : K) (x : V), ψ (a • x) = a ^ (p ^ r) • ψ x) →
      Function.Injective ψ → Module.finrank K V ≤ n →
      Submodule.span K {x : V | ψ x = x} = ⊤ := by
  induction n with
  | zero =>
      intro V _ _ _ ψ _ _ hdim
      have hsub : ∀ x : V, x = 0 :=
        finrank_zero_iff_forall_zero.mp (Nat.le_zero.mp hdim)
      rw [eq_top_iff]
      intro y _
      rw [hsub y]
      exact Submodule.zero_mem _
  | succ n ih =>
      intro V _ _ _ ψ hsmul hinj hdim
      rcases Nat.eq_zero_or_pos (Module.finrank K V) with hz | hpos
      · have hsub : ∀ x : V, x = 0 := finrank_zero_iff_forall_zero.mp hz
        rw [eq_top_iff]
        intro y _
        rw [hsub y]
        exact Submodule.zero_mem _
      · have : Nontrivial V := Module.nontrivial_of_finrank_pos hpos
        obtain ⟨v, hv⟩ := exists_ne (0 : V)
        obtain ⟨w, hw0, hwfix⟩ := exists_fixed_ne_zero p r ψ hsmul hinj hv
        set W : Submodule K V := K ∙ w with hWdef
        have hwW : w ∈ W := Submodule.mem_span_singleton_self w
        -- `ψ` reflects the line `W`.
        have hpre : ∀ z : V, ψ z ∈ W → z ∈ W := by
          intro z hz
          obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hz
          obtain ⟨d, hd⟩ := exists_pow_frobPow_eq (K := K) p r c
          have hdz : ψ (d • w) = ψ z := by rw [hsmul, hd, hwfix, hc]
          rw [← hinj hdz]
          exact Submodule.mem_span_singleton.mpr ⟨d, rfl⟩
        -- The semilinear packaging, so that `Submodule.mapQ` applies.
        set f : V →ₛₗ[iterateFrobenius K p r] V :=
          { toFun := ψ
            map_add' := ψ.map_add
            map_smul' := fun a x => by
              simpa only [iterateFrobenius_def] using hsmul a x } with hfdef
        have hWle : W ≤ Submodule.comap f W := by
          intro x hx
          obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp (hWdef ▸ hx)
          rw [Submodule.mem_comap]
          show ψ (c • w) ∈ W
          rw [hsmul, hwfix]
          exact Submodule.smul_mem _ _ hwW
        set ψbar : (V ⧸ W) →ₛₗ[iterateFrobenius K p r] (V ⧸ W) :=
          Submodule.mapQ W W f hWle with hψbardef
        set ψ' : (V ⧸ W) →+ (V ⧸ W) := ψbar.toAddMonoidHom with hψ'def
        have hbarapply : ∀ x : V, ψ' (Submodule.Quotient.mk x) =
            Submodule.Quotient.mk (ψ x) := fun x => rfl
        have hbarinj : Function.Injective ψ' := by
          intro x y hxy
          obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective W x
          obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective W y
          rw [hbarapply, hbarapply] at hxy
          have h1 : ψ x - ψ y ∈ W := (Submodule.Quotient.eq W).mp hxy
          have h2 : ψ (x - y) ∈ W := by rwa [map_sub]
          exact (Submodule.Quotient.eq W).mpr (hpre _ h2)
        have hquotdim : Module.finrank K (V ⧸ W) ≤ n := by
          have h1 := Submodule.finrank_quotient_add_finrank W
          have h2 : Module.finrank K W = 1 := finrank_span_singleton hw0
          omega
        have hbar := ih (V := V ⧸ W) ψ'
          (fun a x => by
            simpa only [hψ'def, LinearMap.toAddMonoidHom_coe, iterateFrobenius_def] using
              map_smulₛₗ ψbar a x)
          hbarinj hquotdim
        -- Lifting fixed vectors along the quotient.
        have hlift : ∀ z : V ⧸ W, ψ' z = z →
            ∃ u : V, ψ u = u ∧ W.mkQ u = z := by
          intro z hz
          obtain ⟨u₀, rfl⟩ := Submodule.Quotient.mk_surjective W z
          rw [hbarapply] at hz
          obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp ((Submodule.Quotient.eq W).mp hz)
          obtain ⟨μ, hμ⟩ := exists_frobenius_pow_sub_mul_eq (K := K) p r 1 (-a)
          refine ⟨u₀ + μ • w, ?_, ?_⟩
          · have hμ' : a + μ ^ (p ^ r) = μ := by
              rw [one_mul] at hμ
              linear_combination hμ
            have hu : ψ u₀ = u₀ + a • w := by rw [ha]; abel
            rw [map_add, hsmul, hwfix, hu, add_assoc, ← add_smul, hμ']
          · show W.mkQ (u₀ + μ • w) = W.mkQ u₀
            rw [map_add, map_smul, (Submodule.mkQ_apply W w).trans
              ((Submodule.Quotient.mk_eq_zero W).mpr hwW), smul_zero, add_zero]
        -- Assemble.
        have hmapT : Submodule.map W.mkQ (Submodule.span K {x : V | ψ x = x}) = ⊤ := by
          rw [Submodule.map_span]
          refine top_le_iff.mp ?_
          calc (⊤ : Submodule K (V ⧸ W))
              = Submodule.span K {z : V ⧸ W | ψ' z = z} := hbar.symm
            _ ≤ Submodule.span K (W.mkQ '' {x : V | ψ x = x}) := by
                refine Submodule.span_mono ?_
                intro z hz
                obtain ⟨u, hu, huz⟩ := hlift z hz
                exact ⟨u, hu, huz⟩
        have hWT : W ≤ Submodule.span K {x : V | ψ x = x} := by
          rw [hWdef, Submodule.span_le, Set.singleton_subset_iff]
          exact Submodule.subset_span hwfix
        rw [eq_top_iff]
        intro y _
        have hy : W.mkQ y ∈ Submodule.map W.mkQ (Submodule.span K {x : V | ψ x = x}) := by
          rw [hmapT]; trivial
        obtain ⟨z, hz, hzy⟩ := hy
        have hyz : y - z ∈ W := (Submodule.Quotient.eq W).mp hzy.symm
        have : y = z + (y - z) := by abel
        rw [this]
        exact Submodule.add_mem _ hz (hWT hyz)

/-- The `ψ`-fixed vectors span `V` over `K` (Lang–Steinberg descent). -/
theorem span_fixed_eq_top [FiniteDimensional K V]
    (ψ : V →+ V)
    (hsmul : ∀ (a : K) (x : V), ψ (a • x) = a ^ (p ^ r) • ψ x)
    (hinj : Function.Injective ψ) :
    Submodule.span K {x : V | ψ x = x} = ⊤ :=
  span_fixed_aux p r (Module.finrank K V) ψ hsmul hinj le_rfl

/-- `V` has a `K`-basis of `ψ`-fixed vectors: the fixed vectors span, and a
spanning set contains a basis. -/
theorem exists_fixed_basis [FiniteDimensional K V]
    (ψ : V →+ V)
    (hsmul : ∀ (a : K) (x : V), ψ (a • x) = a ^ (p ^ r) • ψ x)
    (hinj : Function.Injective ψ) :
    ∃ v : Fin (Module.finrank K V) → V,
      LinearIndependent K v ∧ ∀ i, ψ (v i) = v i := by
  classical
  have htop := span_fixed_eq_top p r ψ hsmul hinj
  obtain ⟨b, hbsub, hbspan, hbind⟩ := exists_linearIndependent K {x : V | ψ x = x}
  rw [htop] at hbspan
  have hbtop : ⊤ ≤ Submodule.span K (Set.range ((↑) : b → V)) := by
    rw [Subtype.range_coe, hbspan]
  let B : Module.Basis b K V := Module.Basis.mk hbind hbtop
  let _ : Fintype b := FiniteDimensional.fintypeBasisIndex B
  have hcard : Fintype.card b = Module.finrank K V :=
    (Module.finrank_eq_card_basis B).symm
  let ε : b ≃ Fin (Module.finrank K V) := Fintype.equivFinOfCardEq hcard
  refine ⟨fun i => ((ε.symm i : V)), ?_, ?_⟩
  · exact hbind.comp ε.symm ε.symm.injective
  · intro i
    exact hbsub (ε.symm i).2

end Descent

end Height.Steenrod
