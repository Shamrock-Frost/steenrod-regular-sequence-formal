/-
The elementary core: isotropy over a discrete valuation ring.
Stated over an arbitrary PID — `IsDiscreteValuationRing`
extends `IsPrincipalIdealRing`, and the DVR `𝒪_{ℙ¹,x}` is the intended
instance.

Main statement: `trace_mem_range`.  The proof runs the paper's steps:

  (i)–(iv)  the regular part `g` (Isotropy.RegularPart), an *integral*
            matrix implementing every flag motion;
  (base)    `B = A − g` then preserves the kernel flag over `K` — the one
            place denominators are cleared, since the flag over `K` is
            spanned by the integral flag (`exists_integral_kernel_vector`);
  (v)       `tr(A₁·Ṗ₂)` splits into integral traces plus `tr((BP−PB)·C)`,
            and `BP−PB` lowers the flag while `C` preserves it, so that
            last term is the trace of a nilpotent: zero.

Mathlib inventory:
  regular part  Submodule.basisOfPid via Module.free_of_finite_type_torsion_free',
                LinearMap.quotKerEquivRange, Module.projective_lifting_property
  base change   IsLocalization.exist_integer_multiples_of_finite,
                IsFractionRing.injective, RingHom.map_mulVec
  step (v)      Matrix.trace_mul_comm, AddMonoidHom.map_trace,
                Matrix.isNilpotent_trace_of_isNilpotent, IsNilpotent.eq_zero
-/
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer
import Mathlib.Tactic.NoncommRing
import Isotropy.Lowering
import Isotropy.RegularPart

namespace Isotropy

open Matrix

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K] {n : ℕ}

/-- Entrywise extension of scalars to the fraction field. -/
abbrev toK (K : Type*) [Field K] [Algebra R K] (M : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin n) (Fin n) K :=
  M.map (algebraMap R K)

/-- Extension of scalars on vectors. -/
abbrev toKv (K : Type*) [Field K] [Algebra R K] (v : Fin n → R) : Fin n → K :=
  fun i => algebraMap R K (v i)

section BaseChange

private theorem toK_eq_mapMatrix (M : Matrix (Fin n) (Fin n) R) :
    toK K M = (algebraMap R K).mapMatrix M := rfl

@[simp] theorem toK_mul (M N : Matrix (Fin n) (Fin n) R) :
    toK K (M * N) = toK K M * toK K N := by
  simp only [toK_eq_mapMatrix, map_mul]

@[simp] theorem toK_pow (M : Matrix (Fin n) (Fin n) R) (k : ℕ) :
    toK K (M ^ k) = toK K M ^ k := by
  simp only [toK_eq_mapMatrix, map_pow]

@[simp] theorem toK_sub (M N : Matrix (Fin n) (Fin n) R) :
    toK K (M - N) = toK K M - toK K N := by
  simp only [toK_eq_mapMatrix, map_sub]

theorem toK_dpow (P Q : Matrix (Fin n) (Fin n) R) (k : ℕ) :
    toK K (dpow P Q k) = dpow (toK K P) (toK K Q) k := by
  simp only [dpow, toK_eq_mapMatrix, map_sum, map_mul, map_pow]

theorem toK_trace (M : Matrix (Fin n) (Fin n) R) :
    algebraMap R K (trace M) = trace (toK K M) :=
  AddMonoidHom.map_trace (algebraMap R K) M

theorem toK_mulVec (M : Matrix (Fin n) (Fin n) R) (v : Fin n → R) :
    toK K M *ᵥ toKv K v = toKv K (M *ᵥ v) := by
  funext i
  exact (RingHom.map_mulVec (algebraMap R K) M v i).symm

variable [IsDomain R] [IsFractionRing R K]

/-- Denominator clearing: every vector over `K` is an integral vector
divided by a nonzero scalar. -/
private theorem exists_integral_multiple (v : Fin n → K) :
    ∃ (d : R) (w : Fin n → R), d ≠ 0 ∧ toKv K w = algebraMap R K d • v := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R) v
  choose w hw using fun i => RingHom.mem_rangeS.mp (hb i)
  refine ⟨(b : R), w, nonZeroDivisors.coe_ne_zero b, ?_⟩
  funext i
  show algebraMap R K (w i) = _
  rw [hw i]
  simp [Algebra.smul_def]

/-- The kernel flag over `K` is spanned by the integral kernel flag: this
is the only place denominators appear, and it is what lets an integral
regular part control the flag motions over `K`. -/
theorem exists_integral_kernel_vector {P : Matrix (Fin n) (Fin n) R} {k : ℕ}
    {v : Fin n → K} (hv : v ∈ kerFlag (toK K P) k) :
    ∃ (d : R) (w : Fin n → R), d ≠ 0 ∧ w ∈ kerFlag P k ∧
      toKv K w = algebraMap R K d • v := by
  obtain ⟨d, w, hd, hvec⟩ := exists_integral_multiple (R := R) (K := K) (n := n) v
  refine ⟨d, w, hd, ?_, hvec⟩
  have h1 : toKv K ((P ^ k) *ᵥ w) = 0 := by
    rw [← toK_mulVec, hvec, mulVec_smul, toK_pow, mem_kerFlag.mp hv, smul_zero]
  rw [mem_kerFlag]
  funext i
  have h2 : algebraMap R K (((P ^ k) *ᵥ w) i) = algebraMap R K 0 := by
    simpa using congrFun h1 i
  simpa using IsFractionRing.injective R K h2

end BaseChange

variable [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R K]

/-- Steps (ii)–(iv): the regular part.  Some `g` over `R` implements every
flag motion `φ_k`, so `B = A − g` preserves the kernel flag over `K`. -/
theorem exists_regular_part
    (P Pd : Matrix (Fin n) (Fin n) R) (hP : P ^ n = 0)
    (A : Matrix (Fin n) (Fin n) K)
    (hA : toK K P * A - A * toK K P = toK K Pd)
    (hD : DCond P Pd) :
    ∃ g : Matrix (Fin n) (Fin n) R, ∀ k,
      ∀ v ∈ kerFlag (toK K P) k, (A - toK K g).mulVec v ∈ kerFlag (toK K P) k := by
  obtain ⟨g, hg⟩ := exists_regular_g P Pd hP hD
  refine ⟨g, fun k v hv => ?_⟩
  -- the commutator relation computes the flag motion of `A` …
  have ha : (toK K P) ^ k *ᵥ (A *ᵥ v) = dpow (toK K P) (toK K Pd) k *ᵥ v := by
    have hcomm : dpow (toK K P) (toK K Pd) k
        = (toK K P) ^ k * A - A * (toK K P) ^ k := by
      rw [← hA]; exact dpow_commutator _ _ _
    rw [hcomm, sub_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, mem_kerFlag.mp hv,
      mulVec_zero, sub_zero]
  -- … and the integral regular part matches it, after clearing denominators
  have hb : (toK K P) ^ k *ᵥ (toK K g *ᵥ v) = dpow (toK K P) (toK K Pd) k *ᵥ v := by
    obtain ⟨d, w, hd, hw, hvec⟩ := exists_integral_kernel_vector hv
    have hc : algebraMap R K d ≠ 0 := by
      simpa using (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hd
    refine smul_right_injective _ hc ?_
    have hK := congrArg (toKv K) (hg k w hw)
    simp only [← toK_mulVec, hvec, mulVec_smul, toK_pow, toK_dpow] at hK
    exact hK
  rw [mem_kerFlag, sub_mulVec, mulVec_sub, ha, hb, sub_self]
/-- **The kernel flag does not change rank on passing to the fraction field.**
An `R`-basis of `S_k` is a `K`-basis of the kernel over `K`: it spans because
every kernel vector over `K` is an integral one divided by a scalar
(`exists_integral_kernel_vector`), and it is independent because a `K`-relation
clears denominators to an `R`-relation and `R → K` is injective. -/
theorem finrank_kerFlag_toK (P : Matrix (Fin n) (Fin n) R) (k : ℕ) :
    Module.finrank K (kerFlag (toK K P) k) = Module.finrank R (kerFlag P k) := by
  classical
  set S := kerFlag P k with hS
  set b : Module.Basis (Module.Free.ChooseBasisIndex R S) R S :=
    Module.Free.chooseBasis R S with hb
  set v : Module.Free.ChooseBasisIndex R S → (Fin n → K) :=
    fun i => toKv K ((b i : Fin n → R)) with hv
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hvecinj : ∀ y : Fin n → R, toKv K y = 0 → y = 0 := by
    intro y hy
    funext j
    exact hinj (by simpa using congrFun hy j)
  have hvmem : ∀ i, v i ∈ kerFlag (toK K P) k := by
    intro i
    rw [mem_kerFlag, ← toK_pow, toK_mulVec, mem_kerFlag.mp (b i).2]
    funext j
    simp [toKv]
  have hsmul : ∀ (r : R) (y : Fin n → R), toKv K (r • y) = algebraMap R K r • toKv K y := by
    intro r y
    funext j
    show algebraMap R K (r * y j) = algebraMap R K r * algebraMap R K (y j)
    rw [map_mul]
  have hsum : ∀ (s : Finset (Module.Free.ChooseBasisIndex R S)) (r : _ → R),
      toKv K (∑ j ∈ s, r j • ((b j : Fin n → R)))
        = ∑ j ∈ s, algebraMap R K (r j) • v j := by
    intro s r
    funext j
    simp only [toKv, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul]
    rfl
  -- the images span
  have hspan : Submodule.span K (Set.range v) = kerFlag (toK K P) k := by
    refine le_antisymm ?_ ?_
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hvmem i
    · intro x hx
      obtain ⟨d, w, hd, hw, hvec⟩ := exists_integral_kernel_vector hx
      have hdK : algebraMap R K d ≠ 0 := (map_ne_zero_iff _ hinj).mpr hd
      have h1 : ((∑ i, (b.repr ⟨w, hw⟩ i) • b i : S) : Fin n → R) = w := by
        rw [b.sum_repr]
      have hwsum : w = ∑ i, (b.repr ⟨w, hw⟩ i) • ((b i : Fin n → R)) :=
        h1.symm.trans (by rw [Submodule.coe_sum]; exact Finset.sum_congr rfl fun i _ => rfl)
      have h2 : algebraMap R K d • x
          = ∑ i, algebraMap R K (b.repr ⟨w, hw⟩ i) • v i :=
        hvec.symm.trans ((congrArg (toKv K) hwsum).trans (hsum _ _))
      have h3 : x = (algebraMap R K d)⁻¹ • (∑ i, algebraMap R K (b.repr ⟨w, hw⟩ i) • v i) := by
        rw [← h2, smul_smul, inv_mul_cancel₀ hdK, one_smul]
      rw [h3]
      refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => ?_)
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  -- and they are independent
  have hli : LinearIndependent K v := by
    rw [linearIndependent_iff']
    intro s c hc i hi
    obtain ⟨bd, hbd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors R) s c
    have hex : ∀ j, ∃ rj : R, j ∈ s → algebraMap R K rj = (bd : R) • c j := by
      intro j
      by_cases hj : j ∈ s
      · obtain ⟨rj, hrj⟩ := hbd j hj
        exact ⟨rj, fun _ => hrj⟩
      · exact ⟨0, fun h => absurd h hj⟩
    choose r hr using hex
    have hdK : algebraMap R K (bd : R) ≠ 0 :=
      (map_ne_zero_iff _ hinj).mpr (nonZeroDivisors.coe_ne_zero bd)
    have hzero : toKv K (∑ j ∈ s, r j • ((b j : Fin n → R))) = 0 := by
      rw [hsum]
      have hstep : ∀ j ∈ s, algebraMap R K (r j) • v j
          = algebraMap R K (bd : R) • (c j • v j) := by
        intro j hj
        rw [hr j hj, show ((bd : R) • c j) = algebraMap R K (bd : R) * c j from
          Algebra.smul_def _ _, mul_smul]
      rw [Finset.sum_congr rfl hstep, ← Finset.smul_sum, hc, smul_zero]
    have hRrel : (∑ j ∈ s, r j • ((b j : Fin n → R))) = 0 := hvecinj _ hzero
    have hSrel : (∑ j ∈ s, r j • b j : S) = 0 := by
      refine Subtype.ext ?_
      show ((∑ j ∈ s, r j • b j : S) : Fin n → R) = 0
      rw [Submodule.coe_sum]
      rw [← hRrel]
      exact Finset.sum_congr rfl fun j _ => rfl
    have hbli := b.linearIndependent
    rw [linearIndependent_iff'] at hbli
    have hri : r i = 0 := hbli s r hSrel i hi
    have := hr i hi
    rw [hri, map_zero, Algebra.smul_def] at this
    exact ((mul_eq_zero.mp this.symm).resolve_left hdK)
  rw [← hspan, finrank_span_eq_card hli, Module.finrank_eq_card_chooseBasisIndex]


section Reduce

variable {k : Type*} [Field k] [Algebra k R]

/-- Entrywise reduction of a vector along a retraction `ρ : R → k`. -/
noncomputable def redVec (ρ : R →+* k) (hρ : ∀ c : k, ρ (algebraMap k R c) = c) :
    (Fin n → R) →ₗ[k] (Fin n → k) where
  toFun w := fun i => ρ (w i)
  map_add' w w' := by
    funext i
    simp [map_add]
  map_smul' c w := by
    funext i
    show ρ (c • w i) = c * ρ (w i)
    rw [Algebra.smul_def, map_mul, hρ]

/-- **A saturated submodule reduces to a subspace of its own rank.**  A basis of
`S_m = ker(P^m) ⊆ Rⁿ` reduces to a basis of its image: it spans because the
reduction is `k`-linear, and it is independent because `S_m` is saturated — a
`k`-relation between the reductions lifts to `π` times an element of `Rⁿ`, which
is again in `S_m`, so the coordinates are divisible by `π` and their reductions
vanish.

`Pencil.finrank_fibFlag` is the case `R = K⟦u⟧`, `ρ = constantCoeff`, `π = X`;
the case `R = F[u]`, `ρ = eval 0`, `π = X` is the one that makes the lifts of
the frame's columns polynomial in `u`. -/
theorem finrank_map_kerFlag (ρ : R →+* k) (hρ : ∀ c : k, ρ (algebraMap k R c) = c)
    (π : R) (hπ : π ≠ 0) (hker : ∀ r : R, ρ r = 0 ↔ π ∣ r)
    (P : Matrix (Fin n) (Fin n) R) (m : ℕ) :
    Module.finrank k
        (Submodule.map (redVec ρ hρ) (Submodule.restrictScalars k (kerFlag P m)))
      = Module.finrank R (kerFlag P m) := by
  classical
  set S := kerFlag P m with hS
  have hsat : ∀ w : Fin n → R, π • w ∈ S → w ∈ S := by
    intro w hw
    rw [hS, mem_kerFlag] at hw ⊢
    rw [mulVec_smul] at hw
    funext i
    have := congrFun hw i
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    exact (mul_eq_zero.mp this).resolve_left hπ
  set b : Module.Basis (Module.Free.ChooseBasisIndex R S) R S :=
    Module.Free.chooseBasis R S with hb
  set v : Module.Free.ChooseBasisIndex R S → (Fin n → k) :=
    fun i => redVec ρ hρ ((b i : Fin n → R)) with hv
  have hspan : Submodule.span k (Set.range v)
      = Submodule.map (redVec ρ hρ) (Submodule.restrictScalars k S) := by
    refine le_antisymm ?_ ?_
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨(b i : Fin n → R), (b i).2, rfl⟩
    · rintro _ ⟨w, hw, rfl⟩
      have hwS : w ∈ S := hw
      have h1 : ((∑ i, (b.repr ⟨w, hwS⟩ i) • b i : S) : Fin n → R) = w := by
        rw [b.sum_repr]
      have hwsum : w = ∑ i, (b.repr ⟨w, hwS⟩ i) • ((b i : Fin n → R)) :=
        h1.symm.trans (by rw [Submodule.coe_sum]; exact Finset.sum_congr rfl fun i _ => rfl)
      show redVec ρ hρ w ∈ Submodule.span k (Set.range v)
      rw [hwsum, map_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      have hterm : redVec ρ hρ ((b.repr ⟨w, hwS⟩ i) • ((b i : Fin n → R)))
          = ρ (b.repr ⟨w, hwS⟩ i) • v i := by
        funext j
        show ρ ((b.repr ⟨w, hwS⟩ i) * ((b i : Fin n → R) j))
          = ρ (b.repr ⟨w, hwS⟩ i) * ρ ((b i : Fin n → R) j)
        rw [map_mul]
      rw [hterm]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hli : LinearIndependent k v := by
    rw [linearIndependent_iff']
    intro s c hc i hi
    obtain ⟨w, hw⟩ : ∃ w : Fin n → R,
        w = ∑ j ∈ s, (algebraMap k R (c j)) • ((b j : Fin n → R)) := ⟨_, rfl⟩
    have hwS : w ∈ S := by
      rw [hw]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (b j).2
    have hwzero : redVec ρ hρ w = 0 := by
      funext l
      have hcl := congrFun hc l
      show ρ (w l) = 0
      rw [hw]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, hρ]
      have hrw : ∑ j ∈ s, c j * ρ ((b j : Fin n → R) l) = ∑ j ∈ s, c j * v j l := rfl
      rw [hrw]
      simpa using hcl
    have hdvd : ∀ l, π ∣ w l := fun l => (hker (w l)).1 (congrFun hwzero l)
    choose w' hw' using hdvd
    have hwXw' : w = π • w' := by
      funext l
      rw [Pi.smul_apply, smul_eq_mul, ← hw' l]
    have hw'S : w' ∈ S := hsat w' (by rw [← hwXw']; exact hwS)
    have hcoord : (⟨w, hwS⟩ : S) = π • (⟨w', hw'S⟩ : S) := Subtype.ext hwXw'
    have hrepr1 : b.repr ⟨w, hwS⟩ i = algebraMap k R (c i) := by
      have h1 : (⟨w, hwS⟩ : S) = ∑ j ∈ s, (algebraMap k R (c j)) • b j := by
        refine Subtype.ext ?_
        show w = ((∑ j ∈ s, (algebraMap k R (c j)) • b j : S) : Fin n → R)
        rw [Submodule.coe_sum, hw]
        exact Finset.sum_congr rfl fun j _ => rfl
      have h2 := congrArg (fun x : S => b.repr x i) h1
      simp only [map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply,
        Finsupp.coe_smul, Pi.smul_apply, Module.Basis.repr_self, smul_eq_mul] at h2
      rw [h2, Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        simp [Finsupp.single_apply, Ne.symm hj]
      · intro hns
        exact absurd hi hns
    have hrepr2 : b.repr ⟨w, hwS⟩ i = π * b.repr ⟨w', hw'S⟩ i := by
      rw [hcoord, map_smul]
      rfl
    have hfin : algebraMap k R (c i) = π * b.repr ⟨w', hw'S⟩ i := by
      rw [← hrepr1, hrepr2]
    have hcc := congrArg ρ hfin
    rw [hρ, map_mul, (hker π).2 dvd_rfl, zero_mul] at hcc
    exact hcc
  rw [← hspan, finrank_span_eq_card hli, Module.finrank_eq_card_chooseBasisIndex]

end Reduce


/-- The elementary core: isotropy over a DVR.
If `[P, Aᵢ] = Ṗᵢ` over the fraction field and the kernel-flatness
conditions `DCond` hold over `R`, then `tr(A₁·Ṗ₂)` is integral. -/
theorem trace_mem_range
    (P Pd₁ Pd₂ : Matrix (Fin n) (Fin n) R) (hP : P ^ n = 0)
    (A₁ A₂ : Matrix (Fin n) (Fin n) K)
    (hA₁ : toK K P * A₁ - A₁ * toK K P = toK K Pd₁)
    (hA₂ : toK K P * A₂ - A₂ * toK K P = toK K Pd₂)
    (hD₁ : DCond P Pd₁) (hD₂ : DCond P Pd₂) :
    trace (A₁ * toK K Pd₂) ∈ (algebraMap R K).range := by
  obtain ⟨g₁, hB⟩ := exists_regular_part P Pd₁ hP A₁ hA₁ hD₁
  obtain ⟨g₂, hC⟩ := exists_regular_part P Pd₂ hP A₂ hA₂ hD₂
  set B := A₁ - toK K g₁ with hBdef
  set C := A₂ - toK K g₂ with hCdef
  -- `ad_P` of the flag-preserving part is integral …
  have hL : B * toK K P - toK K P * B = toK K (P * g₁ - g₁ * P - Pd₁) := by
    have h1 : B * toK K P - toK K P * B
        = (toK K P * toK K g₁ - toK K g₁ * toK K P)
          - (toK K P * A₁ - A₁ * toK K P) := by
      rw [hBdef]; noncomm_ring
    rw [h1, hA₁]
    simp only [toK_sub, toK_mul]
  -- … and lowers the flag, so its trace against `C` vanishes
  have hzero : trace ((B * toK K P - toK K P * B) * C) = 0 :=
    trace_eq_zero_of_lowering (toK K P) (by rw [← toK_pow, hP]; simp) _
      (lowering_mul_preserving (lowering_ad_of_preserving hB) hC)
  have hPd₂ : toK K Pd₂ = (toK K P * C - C * toK K P)
      + (toK K P * toK K g₂ - toK K g₂ * toK K P) := by
    rw [← hA₂, hCdef]; noncomm_ring
  have key : trace (B * toK K Pd₂) = trace ((B * toK K P - toK K P * B) * toK K g₂) := by
    rw [hPd₂, mul_add, trace_add, trace_mul_ad, trace_mul_ad, hzero, zero_add]
  refine ⟨trace ((P * g₁ - g₁ * P - Pd₁) * g₂) + trace (g₁ * Pd₂), ?_⟩
  have hsplit : A₁ * toK K Pd₂ = B * toK K Pd₂ + toK K g₁ * toK K Pd₂ := by
    rw [hBdef]; noncomm_ring
  rw [map_add, toK_trace, toK_trace, hsplit, trace_add, key]
  simp only [toK_mul]
  rw [← hL]

end Isotropy
