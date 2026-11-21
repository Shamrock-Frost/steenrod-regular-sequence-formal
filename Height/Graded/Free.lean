import Height.Graded.Presentation

/-!
# `lem:free`: saturated graded submodules of graded free modules are graded free

Let `F = ⨁ j, B(-a j)` be a `GradedPresentation` over `B = K[μ, ν]` and `S ⊆ F`
a graded submodule with `F/S` torsion-free (`S` *saturated*).  Then `S` has a
homogeneous `B`-basis: `exists_homogeneousBasis` produces a
`Graded.HomogeneousBasis`.

The proof is the one in the paper: reduce modulo `μ`,
lift a homogeneous basis, and induct on the degree.  The reduction modulo `μ`
is the coordinatewise leading coefficient along `ν`, `P.redMu e`
(`Height/Graded/Presentation.lean`), whose kernel on `F_e` is `μ · F_{e-1}`.
The images `P.redFil S e ⊆ K^idx` form an increasing filtration of a
finite-dimensional space; a basis adapted to that filtration lifts to the
required homogeneous basis of `S`.
-/

noncomputable section

namespace Height.Graded

open MvPolynomial

variable {K : Type*} [Field K]

/-! ### An adapted homogeneous family -/

variable (P : GradedPresentation K) (S : Submodule (Poly K) P.Mod)

/-- Degree by degree, lift a basis adapted to the filtration `P.redFil S`.  The
family produced is `K`-linearly independent after reduction modulo `μ`, and in
each degree `e` its members of degree `≤ e` span `P.redFil S e`. -/
theorem exists_adapted {e₀ : ℤ} (he₀ : ∀ j, e₀ ≤ P.shift j) (n : ℕ) :
    ∃ (ι : Type) (_ : Fintype ι) (b : ι → ℤ) (u : ι → P.Mod),
      (∀ i, u i ∈ P.sub S (b i)) ∧
      (∀ i, e₀ ≤ b i) ∧ (∀ i, b i < e₀ + n) ∧
      LinearIndependent K (fun i => P.redMu (b i) (u i)) ∧
      (∀ e, e < e₀ + n →
        Submodule.span K ((fun i => P.redMu (b i) (u i)) '' {i | b i ≤ e})
          = P.redFil S e) := by
  induction n with
  | zero =>
      refine ⟨Fin 0, inferInstance, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0,
        fun i => i.elim0, linearIndependent_empty_type, ?_⟩
      intro e he
      have hlt : ∀ j, e < P.shift j := fun j => lt_of_lt_of_le (by simpa using he) (he₀ j)
      have h2 : P.sub S e = ⊥ := by
        refine le_antisymm (fun y hy => ?_) bot_le
        have h3 : y ∈ P.piece e := (Submodule.mem_inf.1 hy).2
        rw [P.piece_eq_bot hlt, Submodule.mem_bot] at h3
        simpa using h3
      have hV : P.redFil S e = ⊥ := by simp only [GradedPresentation.redFil, h2,
        Submodule.map_bot]
      rw [hV, Submodule.span_eq_bot]
      rintro y ⟨i, -, -⟩
      exact i.elim0
  | succ n ih =>
      obtain ⟨ι, hι, b, u, hu, hb0, hb1, hli, hsp⟩ := ih
      have hbE : ∀ i, b i ≤ e₀ + n - 1 := fun i => by have := hb1 i; omega
      have hspan : Submodule.span K (Set.range fun i => P.redMu (b i) (u i))
          = P.redFil S (e₀ + n - 1) := by
        have h := hsp (e₀ + n - 1) (by omega)
        rwa [show {i | b i ≤ e₀ + (n : ℤ) - 1} = Set.univ from Set.eq_univ_of_forall hbE,
          Set.image_univ] at h
      obtain ⟨C, hdisj, hsupC⟩ := IsModularLattice.exists_disjoint_and_sup_eq
        (P.redFil_mono S (show e₀ + (n : ℤ) - 1 ≤ e₀ + n by omega))
      have hCQ : C ≤ P.redFil S (e₀ + n) := hsupC ▸ le_sup_right
      obtain ⟨k, cb⟩ : Σ k : ℕ, Module.Basis (Fin k) K C :=
        ⟨Module.finrank K C, Module.finBasis K C⟩
      have hspanC : Submodule.span K (Set.range fun i => ((cb i : C) : P.idx → K)) = C := by
        have h1 : (Set.range fun i => ((cb i : C) : P.idx → K))
            = C.subtype '' Set.range cb := by
          rw [← Set.range_comp]; rfl
        rw [h1, ← Submodule.map_span, cb.span_eq, Submodule.map_top, Submodule.range_subtype]
      have hlift : ∀ i : Fin k, ∃ y, y ∈ P.sub S (e₀ + n) ∧
          P.redMu (e₀ + n) y = ((cb i : C) : P.idx → K) :=
        fun i => P.mem_redFil.1 (hCQ (cb i).2)
      choose x hx hxe using hlift
      have hfam : (fun i : ι ⊕ Fin k =>
          P.redMu (Sum.elim b (fun _ => e₀ + (n : ℤ)) i) (Sum.elim u x i))
          = Sum.elim (fun i => P.redMu (b i) (u i)) (fun i => ((cb i : C) : P.idx → K)) := by
        funext i
        cases i with
        | inl i => rfl
        | inr i => exact hxe i
      refine ⟨ι ⊕ Fin k, inferInstance, Sum.elim b fun _ => e₀ + (n : ℤ), Sum.elim u x, ?_, ?_,
        ?_, ?_, ?_⟩
      · rintro (i | i)
        · exact hu i
        · exact hx i
      · rintro (i | i)
        · exact hb0 i
        · show e₀ ≤ e₀ + (n : ℤ)
          omega
      · rintro (i | i)
        · have := hb1 i
          show b i < e₀ + ((n + 1 : ℕ) : ℤ)
          push_cast
          omega
        · show e₀ + (n : ℤ) < e₀ + ((n + 1 : ℕ) : ℤ)
          push_cast
          omega
      · rw [hfam]
        refine LinearIndependent.sum_type hli
          (cb.linearIndependent.map' C.subtype (Submodule.ker_subtype C)) ?_
        rw [hspan, hspanC]
        exact hdisj
      · intro e he
        rcases lt_or_ge e (e₀ + n) with hlt | hge
        · have hset : {i : ι ⊕ Fin k | Sum.elim b (fun _ => e₀ + (n : ℤ)) i ≤ e}
              = Sum.inl '' {i | b i ≤ e} := by
            ext i
            cases i with
            | inl i => simp
            | inr i =>
                simp only [Sum.elim_inr, Set.mem_ofPred_eq, Set.mem_image]
                constructor
                · intro hcon; omega
                · rintro ⟨j, -, hj⟩; exact absurd hj (by simp)
          rw [hset, Set.image_image]
          exact hsp e hlt
        · have heq : e = e₀ + (n : ℤ) := by
            have : e < e₀ + ((n + 1 : ℕ) : ℤ) := he
            push_cast at this
            omega
          subst heq
          have hset : {i : ι ⊕ Fin k | Sum.elim b (fun _ => e₀ + (n : ℤ)) i ≤ e₀ + (n : ℤ)}
              = Set.univ := by
            ext i
            cases i with
            | inl i => have := hbE i; simp; omega
            | inr i => simp
          rw [hset, Set.image_univ, hfam, Set.Sum.elim_range, Submodule.span_union, hspan,
            hspanC, hsupC]

/-! ### `lem:free` -/

/-- **`lem:free`**.  A graded submodule `S` of a graded free module
`F = ⨁ j, B(-a j)` with `F/S` torsion-free is graded free: it has a
homogeneous `B`-basis. -/
theorem exists_homogeneousBasis (hgr : P.IsGraded S)
    (hsat : ∀ (f : Poly K) (x : P.Mod), f ≠ 0 → f • x ∈ S → x ∈ S) :
    ∃ (ι : Type) (_ : Fintype ι) (deg : ι → ℤ) (elt : ι → P.Mod),
      HomogeneousBasis P S deg elt := by
  classical
  have hmu0 : (mu : Poly K) ≠ 0 := by simp [mu, MvPolynomial.X_ne_zero]
  have hmu_smul : ∀ v : P.Mod, (mu : Poly K) • v = 0 → v = 0 := by
    intro v hv
    funext j
    have h := congrFun hv j
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
    rcases mul_eq_zero.1 h with h' | h'
    · exact absurd h' hmu0
    · exact h'
  obtain ⟨e₀, he₀⟩ := P.exists_shift_lowerBound
  obtain ⟨e₁, he₁⟩ := P.exists_redFil_stab S
  obtain ⟨n, hnE⟩ : ∃ n : ℕ, e₁ ≤ e₀ + (n : ℤ) - 1 :=
    ⟨(e₁ - e₀).toNat + 1, by push_cast; omega⟩
  obtain ⟨ι, hι, b, u, hu, hb0, hb1, hli, hsp⟩ := exists_adapted P S he₀ n
  -- the spanning statement holds in *every* degree, by stabilization
  have hspAll : ∀ e : ℤ,
      Submodule.span K ((fun i => P.redMu (b i) (u i)) '' {i | b i ≤ e}) = P.redFil S e := by
    intro e
    rcases lt_or_ge e (e₀ + n) with hlt | hge
    · exact hsp e hlt
    · have huniv : {i | b i ≤ e} = Set.univ :=
        Set.eq_univ_of_forall fun i => show b i ≤ e by have := hb1 i; omega
      have huniv' : {i | b i ≤ e₀ + (n : ℤ) - 1} = Set.univ :=
        Set.eq_univ_of_forall fun i => show b i ≤ e₀ + (n : ℤ) - 1 by have := hb1 i; omega
      rw [huniv, ← huniv', hsp (e₀ + n - 1) (by omega),
        he₁ (e₀ + n - 1) hnE, he₁ e (le_trans hnE (by omega))]
  refine ⟨ι, hι, b, u, ⟨fun i => (Submodule.mem_inf.1 (hu i)).1,
    fun i => (Submodule.mem_inf.1 (hu i)).2, ?_, ?_⟩⟩
  · -- linear independence over `B`
    rw [Fintype.linearIndependent_iff]
    -- first: homogeneous relations vanish
    have hom : ∀ (m : ℕ) (e : ℤ), e < e₀ + m → ∀ h : ι → Poly K,
        (∀ i, h i ∈ Bpiece K (e - b i)) → (∑ i, h i • u i = 0) → ∀ i, h i = 0 := by
      intro m
      induction m with
      | zero =>
          intro e he h hh _ i
          have : e - b i < 0 := by have := hb0 i; simp only [Nat.cast_zero] at he; omega
          have h2 := hh i
          rw [Bpiece_of_neg this, Submodule.mem_bot] at h2
          exact h2
      | succ m ihm =>
          intro e he h hh hsum i
          rcases lt_or_ge e (e₀ + m) with hlt | hge
          · exact ihm e hlt h hh hsum i
          have hem : e = e₀ + (m : ℤ) := by push_cast at he; omega
          -- reduce modulo `μ`
          have hlead : ∀ i, nuLead (e - b i) (h i) = 0 := by
            have hzero : ∑ i, nuLead (e - b i) (h i) • P.redMu (b i) (u i) = 0 := by
              have : ∀ i, P.redMu e (h i • u i)
                  = nuLead (e - b i) (h i) • P.redMu (b i) (u i) := by
                intro i
                have h2 := P.redMu_smul (hh i) (Submodule.mem_inf.1 (hu i)).2
                rwa [show e - b i + b i = e by ring] at h2
              calc ∑ i, nuLead (e - b i) (h i) • P.redMu (b i) (u i)
                  = ∑ i, P.redMu e (h i • u i) := by
                      exact (Finset.sum_congr rfl fun i _ => this i).symm
                _ = P.redMu e (∑ i, h i • u i) := by rw [map_sum]
                _ = 0 := by rw [hsum, map_zero]
            exact Fintype.linearIndependent_iff.1 hli _ hzero
          -- divide by `μ`
          have hdiv : ∀ i, ∃ g ∈ Bpiece K (e - 1 - b i), h i = (mu : Poly K) * g := by
            intro i
            obtain ⟨g, hg, hgi⟩ := exists_eq_mu_mul (hh i) (hlead i)
            exact ⟨g, by rwa [show e - b i - 1 = e - 1 - b i by ring] at hg, hgi⟩
          choose g hg hgi using hdiv
          have hsum' : ∑ i, g i • u i = 0 := by
            refine hmu_smul _ ?_
            rw [Finset.smul_sum]
            calc ∑ i, (mu : Poly K) • (g i • u i) = ∑ i, h i • u i := by
                  refine Finset.sum_congr rfl fun i _ => ?_
                  rw [hgi i, mul_smul]
              _ = 0 := hsum
          have := ihm (e - 1) (by omega) g hg hsum' i
          rw [hgi i, this, mul_zero]
    intro gg hgg i
    -- every homogeneous component of every `gg i` vanishes
    have hcomp : ∀ (d : ℤ) (i : ι), Bproj d (gg i) = 0 := by
      intro d i
      have hpr : ∑ i', (Bproj (d + b i - b i')) (gg i') • u i' = 0 := by
        have h1 : P.proj (d + b i) (∑ i', gg i' • u i') = 0 := by rw [hgg, map_zero]
        rw [map_sum] at h1
        rw [← h1]
        exact Finset.sum_congr rfl fun i' _ =>
          (P.proj_smul (gg i') (Submodule.mem_inf.1 (hu i')).2).symm
      have := hom ((d + b i - e₀).toNat + 1) (d + b i) (by push_cast; omega)
        (fun i' => Bproj (d + b i - b i') (gg i')) (fun i' => Bproj_mem _ _) hpr i
      simpa using this
    -- hence `gg i = 0`
    have hz := sum_Bproj (0 : ℤ) (gg i)
      (Finset.image (fun k : ℕ => (k : ℤ)) (Finset.range ((gg i).totalDegree + 1)))
      (fun k hk => Finset.mem_image.2 ⟨k, Finset.mem_range.2 (by omega), by simp⟩)
    rw [← hz]
    exact Finset.sum_eq_zero fun d _ => by simpa using hcomp (d - 0) i
  · -- spanning
    refine le_antisymm (Submodule.span_le.2 ?_) ?_
    · rintro _ ⟨i, rfl⟩
      exact (Submodule.mem_inf.1 (hu i)).1
    · have hPS : Submodule.span (Poly K) (Set.range u) ≤ S :=
        Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact (Submodule.mem_inf.1 (hu i)).1)
      have key : ∀ (m : ℕ) (e : ℤ), e < e₀ + m →
          ∀ y ∈ P.sub S e, y ∈ Submodule.span (Poly K) (Set.range u) := by
        intro m
        induction m with
        | zero =>
            intro e he y hy
            have hlt : ∀ j, e < P.shift j := fun j =>
              lt_of_lt_of_le (by simpa using he) (he₀ j)
            have h3 : y ∈ P.piece e := (Submodule.mem_inf.1 hy).2
            rw [P.piece_eq_bot hlt, Submodule.mem_bot] at h3
            rw [h3]
            exact Submodule.zero_mem _
        | succ m ihm =>
            intro e he y hy
            rcases lt_or_ge e (e₀ + m) with hlt | hge
            · exact ihm e hlt y hy
            have hem : e = e₀ + (m : ℤ) := by push_cast at he; omega
            have hW : P.redFil S e ≤
                (((Submodule.span (Poly K) (Set.range u)).restrictScalars K)
                  ⊓ P.piece e).map (P.redMu e) := by
              rw [← hspAll e]
              refine Submodule.span_le.2 ?_
              rintro _ ⟨i, hi, rfl⟩
              have hi' : b i ≤ e := hi
              have p1' : (nu ^ (e - b i).toNat : Poly K) • u i ∈
                  Submodule.span (Poly K) (Set.range u) :=
                Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
              have p1 : (nu ^ (e - b i).toNat : Poly K) • u i ∈
                  (Submodule.span (Poly K) (Set.range u)).restrictScalars K := p1'
              have p2 : (nu ^ (e - b i).toNat : Poly K) • u i ∈ P.piece e := by
                have h2 := P.smul_mem_piece (nu_pow_mem (K := K) (e - b i).toNat)
                  (Submodule.mem_inf.1 (hu i)).2
                rwa [show (((e - b i).toNat : ℤ) + b i) = e by omega] at h2
              have hmem : (nu ^ (e - b i).toNat : Poly K) • u i ∈
                  ((Submodule.span (Poly K) (Set.range u)).restrictScalars K)
                    ⊓ P.piece e := Submodule.mem_inf.2 ⟨p1, p2⟩
              have heq : P.redMu e ((nu ^ (e - b i).toNat : Poly K) • u i)
                  = P.redMu (b i) (u i) := by
                have h2 := P.redMu_nu_pow_smul (e := b i) (e - b i).toNat
                  (Submodule.mem_inf.1 (hu i)).2
                rwa [show (((e - b i).toNat : ℤ) + b i) = e by omega] at h2
              have hfin := Submodule.mem_map_of_mem (f := P.redMu e) hmem
              rw [heq] at hfin
              exact hfin
            obtain ⟨z, hz, hz2⟩ := hW (P.mem_redFil.2 ⟨y, hy, rfl⟩)
            have hyz : y - z ∈ P.piece e :=
              Submodule.sub_mem _ (Submodule.mem_inf.1 hy).2 (Submodule.mem_inf.1 hz).2
            have hyzS : y - z ∈ S :=
              Submodule.sub_mem _ (Submodule.mem_inf.1 hy).1 (hPS (Submodule.mem_inf.1 hz).1)
            have hlam : P.redMu e (y - z) = 0 := by rw [map_sub, hz2, sub_self]
            obtain ⟨w, hw, hw2⟩ := P.exists_eq_mu_smul hyz hlam
            have hwS : w ∈ S := hsat _ _ hmu0 (by rw [← hw2]; exact hyzS)
            have hwspan : w ∈ Submodule.span (Poly K) (Set.range u) :=
              ihm (e - 1) (by omega) w (Submodule.mem_inf.2 ⟨hwS, hw⟩)
            have : y = z + (mu : Poly K) • w := by rw [← hw2]; abel
            rw [this]
            exact Submodule.add_mem _ (Submodule.mem_inf.1 hz).1
              (Submodule.smul_mem _ _ hwspan)
      intro y hy
      refine Submodule.span_le.2 ?_ (hgr.mem_span hy)
      rintro z hz
      rw [Set.mem_iUnion] at hz
      obtain ⟨e, hz1, hz2⟩ := hz
      exact key ((e - e₀).toNat + 1) e (by push_cast; omega) z (Submodule.mem_inf.2 ⟨hz1, hz2⟩)

/-! ### The unbundled form

`Chain/H1Geometry.lean` and `Pencil/SelfDual.lean` call `lem:free` in this
form, with the basis conditions as a conjunction. -/

/-- `exists_homogeneousBasis` at `P = GradedPresentation.of K a`,
with the basis conditions spelled out. -/
theorem saturated_free {r : ℕ} (a : Fin r → ℤ)
    (S : Submodule (Poly K) (Fin r → Poly K)) (hgr : (GradedPresentation.of K a).IsGraded S)
    (hsat : ∀ (f : Poly K) (x : Fin r → Poly K), f ≠ 0 → f • x ∈ S → x ∈ S) :
    ∃ (ι : Type) (_ : Fintype ι) (b : ι → ℤ) (u : ι → (Fin r → Poly K)),
      (∀ i, u i ∈ S) ∧ (∀ i, u i ∈ (GradedPresentation.of K a).piece (b i)) ∧
      LinearIndependent (Poly K) u ∧
      Submodule.span (Poly K) (Set.range u) = S := by
  obtain ⟨ι, hι, b, u, H⟩ := exists_homogeneousBasis (GradedPresentation.of K a) S hgr hsat
  exact ⟨ι, hι, b, u, H.mem, H.homog, H.linInd, H.span⟩

end Height.Graded

end
