import Height.Toolbox.JordanBasis
import Height.Toolbox.Jordan
import Height.Toolbox.AdMatrix
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# The dimension of the centraliser of a nilpotent matrix

For a nilpotent `N` the centraliser `{A | A * N = N * A}` has `K`-dimension
`c(N) = Σ_m (λ'_m)²`, where `λ'_m = conj N m` is the kernel-dimension
partition of `Height/Toolbox/Jordan.lean` and `c(N)` is `cOf`.
-/

open Polynomial Module

namespace Height.Toolbox

open scoped BigOperators

universe u v

/-! ## Chain bases -/

section Chain

variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V]

/-- The shift property of a Jordan chain basis: `f` moves each basis vector one
step up its chain, and kills the top of the chain. -/
def IsChainBasis {d : ℕ} (f : Module.End K V) (k : Fin d → ℕ)
    (b : Basis ((i : Fin d) × Fin (k i)) K V) : Prop :=
  ∀ (i : Fin d) (j : Fin (k i)),
    f (b ⟨i, j⟩) = if h : (j : ℕ) + 1 < k i then b ⟨i, ⟨(j : ℕ) + 1, h⟩⟩ else 0

/-- **Jordan chain basis.**  A nilpotent endomorphism of a finite-dimensional
space has a basis indexed by the boxes of a Jordan diagram on which it acts by
the shift.  This is `JordanBasis.exists_shift_basis` with the chain
structure of the index type retained. -/
theorem exists_chainBasis [FiniteDimensional K V] (f : Module.End K V)
    (hf : IsNilpotent f) :
    ∃ (d : ℕ) (k : Fin d → ℕ) (b : Basis ((i : Fin d) × Fin (k i)) K V),
      IsChainBasis f k b := by
  obtain ⟨d, k, ⟨φ⟩⟩ := Module.torsion_by_prime_power_decomposition
    (R := K[X]) (M := Module.AEval' f) Polynomial.irreducible_X
    (JordanBasis.isTorsion'_aeval f hf)
  set ψ : V ≃ₗ[K] DirectSum (Fin d) (fun i => JordanBasis.Quo K (k i)) :=
    (Module.AEval'.of f).trans (φ.restrictScalars K) with hψdef
  have hψ : ∀ v : V, ψ (f v) = (X : K[X]) • ψ v := by
    intro v
    show φ (Module.AEval'.of f (f v)) = (X : K[X]) • φ (Module.AEval'.of f v)
    rw [← Module.AEval'.X_smul_of, map_smul]
  have key : ∀ w, f (ψ.symm w) = ψ.symm ((X : K[X]) • w) := by
    intro w
    apply ψ.injective
    rw [hψ, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  refine ⟨d, k, (JordanBasis.dsBasis k).map ψ.symm, ?_⟩
  intro i j
  rw [Basis.map_apply, key, JordanBasis.X_smul_dsBasis]
  by_cases h : (j : ℕ) + 1 < k i <;> simp [h, Basis.map_apply]

/-! ### Powers and kernels on a chain basis -/

variable {d : ℕ} {f : Module.End K V} {k : Fin d → ℕ}
  {b : Basis ((i : Fin d) × Fin (k i)) K V}

/-- Iterating the shift moves a basis vector `t` steps up its chain. -/
theorem IsChainBasis.pow_apply (hb : IsChainBasis f k b) (i : Fin d) (j : Fin (k i)) (t : ℕ) :
    (f ^ t) (b ⟨i, j⟩) =
      if h : (j : ℕ) + t < k i then b ⟨i, ⟨(j : ℕ) + t, h⟩⟩ else 0 := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [pow_succ', Module.End.mul_apply, ih]
      by_cases h : (j : ℕ) + t < k i
      · rw [dite_eq_left h, hb i ⟨(j : ℕ) + t, h⟩]
        simp only []
        split_ifs <;> first | rfl | omega
      · rw [dite_eq_right h, map_zero, dite_eq_right (show ¬ (j : ℕ) + (t + 1) < k i by omega)]

/-- The chain-basis indices killed by `f ^ t`. -/
def chainKerSet {d : ℕ} (k : Fin d → ℕ) (t : ℕ) : Finset ((i : Fin d) × Fin (k i)) :=
  Finset.univ.filter fun s => k s.1 ≤ (s.2 : ℕ) + t

theorem mem_chainKerSet {d : ℕ} {k : Fin d → ℕ} {t : ℕ} {s : (i : Fin d) × Fin (k i)} :
    s ∈ chainKerSet k t ↔ k s.1 ≤ (s.2 : ℕ) + t := by
  simp [chainKerSet]

/-- On a chain basis the kernel of `f ^ t` is spanned by the basis vectors within
`t` steps of the top of their chain. -/
theorem IsChainBasis.ker_pow (hb : IsChainBasis f k b) (t : ℕ) :
    LinearMap.ker (f ^ t) = Submodule.span K (b '' (chainKerSet k t : Set _)) := by
  apply le_antisymm
  · intro v hv
    rw [Basis.mem_span_image]
    intro s hs
    -- `s` is in the support of `v`, so we must show `s ∈ chainKerSet k t`.
    by_contra hsn
    simp only [Finset.mem_coe, mem_chainKerSet, not_le] at hsn
    have hlt : (s.2 : ℕ) + t < k s.1 := hsn
    -- the functional `b.coord (shift s)` composed with `f ^ t` is `b.coord s`
    set σ : (i : Fin d) × Fin (k i) := ⟨s.1, ⟨(s.2 : ℕ) + t, hlt⟩⟩ with hσ
    have hcomp : (b.coord σ).comp (f ^ t) = b.coord s := by
      apply b.ext
      intro s'
      rw [LinearMap.comp_apply]
      obtain ⟨i', j'⟩ := s'
      rw [hb.pow_apply i' j' t]
      by_cases hj' : (j' : ℕ) + t < k i'
      · rw [dite_eq_left hj', Basis.coord_apply, Basis.coord_apply, Basis.repr_self, Basis.repr_self,
          Finsupp.single_apply, Finsupp.single_apply]
        congr 1
        simp only [eq_iff_iff, hσ]
        constructor
        · rintro h
          obtain ⟨rfl, h2⟩ := Sigma.mk.injEq .. ▸ h
          have : (j' : ℕ) + t = (s.2 : ℕ) + t := congrArg Fin.val (eq_of_heq h2)
          obtain ⟨i0, j0⟩ := s
          simp only at this ⊢
          exact congrArg (Sigma.mk i0) (Fin.ext (by omega))
        · rintro rfl; rfl
      · rw [dite_eq_right hj', map_zero, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
        rw [ite_eq_right]
        intro h
        obtain ⟨rfl, h2⟩ := Sigma.mk.injEq .. ▸ h
        have : (j' : ℕ) = (s.2 : ℕ) := congrArg Fin.val (eq_of_heq h2)
        omega
    have hzero : b.coord s v = 0 := by
      rw [← hcomp, LinearMap.comp_apply, LinearMap.mem_ker.mp hv, map_zero]
    rw [Basis.coord_apply] at hzero
    exact (Finsupp.mem_support_iff.mp hs) hzero
  · rw [Submodule.span_le]
    rintro _ ⟨s, hs, rfl⟩
    simp only [Finset.mem_coe, mem_chainKerSet] at hs
    obtain ⟨i, j⟩ := s
    simp only [SetLike.mem_coe, LinearMap.mem_ker]
    rw [hb.pow_apply i j t, dite_eq_right (by simp only at hs; omega)]

private theorem sum_range_ite (m t : ℕ) :
    (∑ j ∈ Finset.range m, if m ≤ j + t then 1 else 0) = min t m := by
  rw [← Finset.card_filter (fun j => m ≤ j + t) (Finset.range m)]
  have h : ((Finset.range m).filter fun j => m ≤ j + t) = Finset.Ico (m - t) m := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [h, Nat.card_Ico]
  omega

theorem card_chainKerSet {d : ℕ} (k : Fin d → ℕ) (t : ℕ) :
    (chainKerSet k t).card = ∑ i, min t (k i) := by
  have h : chainKerSet k t =
      (Finset.univ : Finset (Fin d)).sigma
        fun i => (Finset.univ : Finset (Fin (k i))).filter fun j : Fin (k i) =>
          k i ≤ (j : ℕ) + t := by
    ext s
    simp [chainKerSet, Finset.mem_sigma]
  rw [h, Finset.card_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.card_filter,
    Fin.sum_univ_eq_sum_range (fun j => if k i ≤ j + t then 1 else 0) (k i)]
  exact sum_range_ite (k i) t

/-- The kernel dimensions of a nilpotent endomorphism read off its chain
lengths. -/
theorem IsChainBasis.finrank_ker_pow (hb : IsChainBasis f k b) (t : ℕ) :
    Module.finrank K (LinearMap.ker (f ^ t)) = ∑ i, min t (k i) := by
  have hli : LinearIndependent K
      (fun x : ((chainKerSet k t : Finset ((i : Fin d) × Fin (k i))) :
          Set ((i : Fin d) × Fin (k i))) => b (x : (i : Fin d) × Fin (k i))) :=
    b.linearIndependent.comp
      (fun x : ((chainKerSet k t : Finset ((i : Fin d) × Fin (k i))) :
          Set ((i : Fin d) × Fin (k i))) => (x : (i : Fin d) × Fin (k i)))
      Subtype.val_injective
  rw [hb.ker_pow t, Set.image_eq_range, finrank_span_eq_card hli]
  rw [show Fintype.card
      ((chainKerSet k t : Finset ((i : Fin d) × Fin (k i))) : Set ((i : Fin d) × Fin (k i)))
      = (chainKerSet k t).card from by simp]
  exact card_chainKerSet k t

/-! ### Column counts -/

/-- The number of Jordan chains of length at least `m`: the `m`-th part of the
conjugate partition, read off the chain lengths. -/
def colCount {d : ℕ} (k : Fin d → ℕ) (m : ℕ) : ℕ :=
  (Finset.univ.filter fun i => m ≤ k i).card

theorem colCount_eq_sum {d : ℕ} (k : Fin d → ℕ) (m : ℕ) :
    colCount k m = ∑ i, if m ≤ k i then 1 else 0 := by
  rw [colCount, Finset.card_filter]

variable [FiniteDimensional K V]

omit [FiniteDimensional K V] in
/-- On a chain basis, `conj` counts the chains of length at least `m`. -/
theorem IsChainBasis.conj_eq (hb : IsChainBasis f k b) {m : ℕ} (hm : 1 ≤ m) :
    conj f m = colCount k m := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hstep : (∑ i, min (m' + 1) (k i)) = (∑ i, min m' (k i)) + colCount k (m' + 1) := by
    rw [colCount_eq_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by split_ifs <;> omega
  unfold conj
  rw [show m' + 1 - 1 = m' from rfl, hb.finrank_ker_pow (m' + 1), hb.finrank_ker_pow m', hstep]
  omega

/-! ### The centraliser -/

omit [FiniteDimensional K V] in
/-- The centraliser of an endomorphism, as a `K`-submodule of `End K V`. -/
def endCentralizer (f : Module.End K V) : Submodule K (Module.End K V) where
  carrier := {g | g * f = f * g}
  add_mem' {a c} ha hc := by
    simp only [Set.mem_ofPred_eq] at *
    rw [add_mul, mul_add, ha, hc]
  zero_mem' := by simp
  smul_mem' c a ha := by
    simp only [Set.mem_ofPred_eq] at *
    rw [smul_mul_assoc, mul_smul_comm, ha]

omit [FiniteDimensional K V] in
@[simp] theorem mem_endCentralizer {f : Module.End K V} {g : Module.End K V} :
    g ∈ endCentralizer f ↔ g * f = f * g := Iff.rfl

/-- The bottom vector of the `i`-th Jordan chain (`0` for an empty chain). -/
noncomputable def chainGen {d : ℕ} (k : Fin d → ℕ)
    (b : Basis ((i : Fin d) × Fin (k i)) K V) (i : Fin d) : V :=
  if h : 0 < k i then b ⟨i, ⟨0, h⟩⟩ else 0

omit [FiniteDimensional K V] in
theorem IsChainBasis.pow_chainGen (hb : IsChainBasis f k b) (i : Fin d) (j : Fin (k i)) :
    (f ^ (j : ℕ)) (chainGen k b i) = b ⟨i, j⟩ := by
  have h : 0 < k i := lt_of_le_of_lt (Nat.zero_le _) j.2
  rw [chainGen, dite_eq_left h, hb.pow_apply i ⟨0, h⟩ (j : ℕ)]
  simp

omit [FiniteDimensional K V] in
theorem IsChainBasis.pow_len_chainGen (hb : IsChainBasis f k b) (i : Fin d) :
    (f ^ k i) (chainGen k b i) = 0 := by
  rw [chainGen]
  by_cases h : 0 < k i
  · rw [dite_eq_left h, hb.pow_apply i ⟨0, h⟩ (k i), dite_eq_right (by simp)]
  · rw [dite_eq_right h, map_zero]

/-- Reading an element of the centraliser off its values on the chain
generators. -/
noncomputable def centralizerToPi (hb : IsChainBasis f k b) :
    endCentralizer f →ₗ[K] ((i : Fin d) → ↥(LinearMap.ker (f ^ k i))) where
  toFun g := fun i => ⟨(g : Module.End K V) (chainGen k b i), by
    have hcomm : Commute (g : Module.End K V) f := mem_endCentralizer.mp g.2
    have hc := congrArg (fun e : Module.End K V => e (chainGen k b i))
      ((hcomm.pow_right (k i)).eq)
    simp only [Module.End.mul_apply] at hc
    rw [LinearMap.mem_ker, ← hc, hb.pow_len_chainGen i, map_zero]⟩
  map_add' g g' := by funext i; exact Subtype.ext rfl
  map_smul' c g := by funext i; exact Subtype.ext rfl

omit [FiniteDimensional K V] in
theorem centralizerToPi_injective (hb : IsChainBasis f k b) :
    Function.Injective (centralizerToPi hb) := by
  rw [injective_iff_map_eq_zero]
  intro g hg
  apply Subtype.ext
  refine b.ext fun s => ?_
  obtain ⟨i, j⟩ := s
  have h0 : (g : Module.End K V) (chainGen k b i) = 0 :=
    congrArg Subtype.val (congrFun hg i)
  have hcomm : Commute (g : Module.End K V) f := mem_endCentralizer.mp g.2
  have hstep : (g : Module.End K V) (b ⟨i, j⟩)
      = (f ^ (j : ℕ)) ((g : Module.End K V) (chainGen k b i)) := by
    rw [← hb.pow_chainGen i j]
    exact congrArg (fun e : Module.End K V => e (chainGen k b i)) ((hcomm.pow_right (j : ℕ)).eq)
  rw [hstep, h0, map_zero]
  rfl

omit [FiniteDimensional K V] in
theorem centralizerToPi_surjective (hb : IsChainBasis f k b) :
    Function.Surjective (centralizerToPi hb) := by
  intro w
  set g : Module.End K V := b.constr K (fun s => (f ^ (s.2 : ℕ)) ((w s.1 : V))) with hgdef
  have hgb : ∀ (i : Fin d) (j : Fin (k i)), g (b ⟨i, j⟩) = (f ^ (j : ℕ)) ((w i : V)) := by
    intro i j
    rw [hgdef, Basis.constr_basis]
  have hmem : g ∈ endCentralizer f := by
    rw [mem_endCentralizer]
    refine b.ext fun s => ?_
    obtain ⟨i, j⟩ := s
    rw [Module.End.mul_apply, Module.End.mul_apply, hb i j]
    by_cases h : (j : ℕ) + 1 < k i
    · rw [dite_eq_left h, hgb i ⟨(j : ℕ) + 1, h⟩, hgb i j]
      simp only []
      rw [pow_succ', Module.End.mul_apply]
    · have hjlt := j.isLt
      rw [dite_eq_right h, map_zero, hgb i j, ← Module.End.mul_apply, ← pow_succ',
        show (j : ℕ) + 1 = k i by omega]
      exact (LinearMap.mem_ker.mp (w i).2).symm
  refine ⟨⟨g, hmem⟩, ?_⟩
  funext i
  by_cases h : 0 < k i
  · apply Subtype.ext
    show g (chainGen k b i) = (w i : V)
    rw [chainGen, dite_eq_left h, hgb i ⟨0, h⟩]
    simp
  · have hk0 : k i = 0 := by omega
    have hsub : Subsingleton ↥(LinearMap.ker (f ^ k i)) := by
      rw [hk0, pow_zero, Module.End.one_eq_id, LinearMap.ker_id]
      infer_instance
    exact Subsingleton.elim _ _

/-- **The centraliser dimension from the chain lengths.** -/
theorem IsChainBasis.finrank_endCentralizer (hb : IsChainBasis f k b) :
    Module.finrank K (endCentralizer f) = ∑ i, ∑ j, min (k i) (k j) := by
  have e : ↥(endCentralizer f) ≃ₗ[K] ((i : Fin d) → ↥(LinearMap.ker (f ^ k i))) :=
    LinearEquiv.ofBijective (centralizerToPi hb)
      ⟨centralizerToPi_injective hb, centralizerToPi_surjective hb⟩
  rw [e.finrank_eq, Module.finrank_pi_fintype]
  exact Finset.sum_congr rfl fun i _ => hb.finrank_ker_pow (k i)

omit [FiniteDimensional K V] in
/-- The chain lengths sum to the dimension of the space. -/
theorem IsChainBasis.sum_chainLengths (_ : IsChainBasis f k b) :
    (∑ i, k i) = Module.finrank K V := by
  rw [Module.finrank_eq_card_basis b, Fintype.card_sigma]
  exact Finset.sum_congr rfl fun i _ => (Fintype.card_fin (k i)).symm

end Chain

/-! ## The numerical identity `Σ_{i,j} min(a_i,a_j) = Σ_m (λ'_m)²` -/

section Counting

private theorem sum_Icc_ite_le (n c : ℕ) (hc : c ≤ n) :
    (∑ m ∈ Finset.Icc 1 n, if m ≤ c then 1 else 0) = c := by
  rw [← Finset.card_filter (fun m => m ≤ c) (Finset.Icc 1 n)]
  have h : ((Finset.Icc 1 n).filter fun m => m ≤ c) = Finset.Icc 1 c := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [h, Nat.card_Icc]
  omega

/-- Counting pairs by the rows they share: `Σ_{i,j} min(a_i,a_j) = Σ_m (λ'_m)²`. -/
theorem sum_min_eq_sum_colCount_sq {d : ℕ} (k : Fin d → ℕ) (n : ℕ) (hk : ∀ i, k i ≤ n) :
    (∑ i, ∑ j, min (k i) (k j)) = ∑ m ∈ Finset.Icc 1 n, (colCount k m) ^ 2 := by
  have step : ∀ i j : Fin d, min (k i) (k j) =
      ∑ m ∈ Finset.Icc 1 n, (if m ≤ k i then 1 else 0) * (if m ≤ k j then 1 else 0) := by
    intro i j
    have h1 : ∀ m : ℕ, ((if m ≤ k i then 1 else 0) * (if m ≤ k j then 1 else 0) : ℕ)
        = if m ≤ min (k i) (k j) then 1 else 0 := by
      intro m
      by_cases h1 : m ≤ k i
      · by_cases h2 : m ≤ k j
        · rw [ite_eq_left h1, ite_eq_left h2, ite_eq_left (show m ≤ min (k i) (k j) by omega), mul_one]
        · rw [ite_eq_left h1, ite_eq_right h2, ite_eq_right (show ¬ m ≤ min (k i) (k j) by omega), mul_zero]
      · rw [ite_eq_right h1, ite_eq_right (show ¬ m ≤ min (k i) (k j) by omega), zero_mul]
    simp only [h1]
    exact (sum_Icc_ite_le n (min (k i) (k j)) (le_trans (min_le_left _ _) (hk i))).symm
  calc (∑ i, ∑ j, min (k i) (k j))
      = ∑ i, ∑ j, ∑ m ∈ Finset.Icc 1 n,
          (if m ≤ k i then 1 else 0) * (if m ≤ k j then 1 else 0) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => step i j
    _ = ∑ i, ∑ m ∈ Finset.Icc 1 n, ∑ j,
          (if m ≤ k i then 1 else 0) * (if m ≤ k j then 1 else 0) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ m ∈ Finset.Icc 1 n, ∑ i, ∑ j,
          (if m ≤ k i then 1 else 0) * (if m ≤ k j then 1 else 0) := Finset.sum_comm
    _ = ∑ m ∈ Finset.Icc 1 n, (colCount k m) ^ 2 := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [colCount_eq_sum, sq, Finset.sum_mul_sum]

end Counting

/-! ## The matrix statements -/

section Matrices

variable {K : Type u} [Field K] {n : ℕ}

/-- The centraliser of a matrix, as a `K`-submodule of the matrix algebra. -/
def centralizer (N : Matrix (Fin n) (Fin n) K) :
    Submodule K (Matrix (Fin n) (Fin n) K) where
  carrier := {A | A * N = N * A}
  add_mem' {a c} ha hc := by
    simp only [Set.mem_ofPred_eq] at *
    rw [add_mul, mul_add, ha, hc]
  zero_mem' := by simp
  smul_mem' c a ha := by
    simp only [Set.mem_ofPred_eq] at *
    rw [smul_mul_assoc, mul_smul_comm, ha]

@[simp] theorem mem_centralizer {N A : Matrix (Fin n) (Fin n) K} :
    A ∈ centralizer N ↔ A * N = N * A := Iff.rfl

/-- Passing to endomorphisms of `Kⁿ` does not change the centraliser dimension. -/
theorem finrank_centralizer_eq_endCentralizer (N : Matrix (Fin n) (Fin n) K) :
    Module.finrank K (centralizer N)
      = Module.finrank K (endCentralizer (Matrix.toLinAlgEquiv' N)) := by
  have key : ∀ A : Matrix (Fin n) (Fin n) K,
      (Matrix.toLinAlgEquiv' A ∈ endCentralizer (Matrix.toLinAlgEquiv' N))
        ↔ A ∈ centralizer N := by
    intro A
    rw [mem_endCentralizer, mem_centralizer, ← map_mul, ← map_mul]
    exact (Matrix.toLinAlgEquiv' (R := K) (n := Fin n)).injective.eq_iff
  let φ : ↥(centralizer N) →ₗ[K] ↥(endCentralizer (Matrix.toLinAlgEquiv' N)) :=
    { toFun := fun A => ⟨Matrix.toLinAlgEquiv' A.1, (key A.1).mpr A.2⟩
      map_add' := fun A B => Subtype.ext (by simp)
      map_smul' := fun c A => Subtype.ext (by simp) }
  have hbij : Function.Bijective φ := by
    constructor
    · intro A B hAB
      exact Subtype.ext ((Matrix.toLinAlgEquiv' (R := K) (n := Fin n)).injective
        (congrArg Subtype.val hAB))
    · rintro ⟨g, hg⟩
      refine ⟨⟨(Matrix.toLinAlgEquiv' (R := K) (n := Fin n)).symm g, ?_⟩, ?_⟩
      · rw [← key]
        simpa using hg
      · exact Subtype.ext (by simp [φ])
  exact (LinearEquiv.ofBijective φ hbij).finrank_eq

/-- **The centraliser dimension of a nilpotent matrix** (`c(N) = Σ_m (λ'_m)²`). -/
theorem finrank_centralizer_eq (N : Matrix (Fin n) (Fin n) K) (hN : IsNilpotent N) :
    Module.finrank K (centralizer N) = cOf N := by
  have hyn : IsNilpotent (Matrix.toLinAlgEquiv' N : Module.End K (Fin n → K)) :=
    hN.map (Matrix.toLinAlgEquiv' (R := K) (n := Fin n))
  obtain ⟨d, k, b, hb⟩ := exists_chainBasis (Matrix.toLinAlgEquiv' N) hyn
  have hsum : (∑ i, k i) = n := by
    rw [hb.sum_chainLengths, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have hk : ∀ i, k i ≤ n := fun i => by
    rw [← hsum]
    exact Finset.single_le_sum (f := k) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  rw [finrank_centralizer_eq_endCentralizer, hb.finrank_endCentralizer,
    sum_min_eq_sum_colCount_sq k n hk, cOf]
  exact Finset.sum_congr rfl fun m hm => by rw [hb.conj_eq (Finset.mem_Icc.mp hm).1]

/-! ### The rank of `ad_N` -/

theorem vecMat_eq_zero_iff {A : Matrix (Fin n) (Fin n) K} :
    vecMat A = 0 ↔ A = 0 := by
  constructor
  · intro h
    exact vecMat_injective (by rw [h]; funext a; rfl)
  · rintro rfl
    funext a
    rfl

theorem mem_ker_adMat_iff (N A : Matrix (Fin n) (Fin n) K) :
    vecMat A ∈ LinearMap.ker (adMat N).mulVecLin
      ↔ A ∈ centralizer N := by
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, adMat_mulVec,
    vecMat_eq_zero_iff, mem_centralizer, sub_eq_zero]
  exact eq_comm

theorem finrank_ker_adMat (N : Matrix (Fin n) (Fin n) K) :
    Module.finrank K (LinearMap.ker (adMat N).mulVecLin)
      = Module.finrank K (centralizer N) := by
  let φ : ↥(centralizer N) →ₗ[K] ↥(LinearMap.ker (adMat N).mulVecLin) :=
    { toFun := fun A => ⟨vecMat A.1, (mem_ker_adMat_iff N A.1).mpr A.2⟩
      map_add' := fun A B => Subtype.ext (by funext a; rfl)
      map_smul' := fun c A => Subtype.ext (by funext a; rfl) }
  have hbij : Function.Bijective φ := by
    constructor
    · intro A B hAB
      exact Subtype.ext (vecMat_injective (congrArg Subtype.val hAB))
    · rintro ⟨w, hw⟩
      obtain ⟨A, rfl⟩ := vecMat_surjective w
      exact ⟨⟨A, (mem_ker_adMat_iff N A).mp hw⟩, Subtype.ext rfl⟩
  exact ((LinearEquiv.ofBijective φ hbij).finrank_eq).symm

/-- **Rank–nullity for `ad_N`**: `rank(ad_N) + c(N) = n²`. -/
theorem rank_adMat_eq (N : Matrix (Fin n) (Fin n) K) (hN : IsNilpotent N) :
    (adMat N).rank + cOf N = n * n := by
  rw [← finrank_centralizer_eq N hN, ← finrank_ker_adMat N]
  show Module.finrank K (LinearMap.range (adMat N).mulVecLin) +
    Module.finrank K (LinearMap.ker (adMat N).mulVecLin) = n * n
  rw [LinearMap.finrank_range_add_finrank_ker, Module.finrank_fintype_fun_eq_card,
    Fintype.card_fin]

/-- The paper's form of the centraliser dimension: `Σ_{i,j} min(a_i, a_j)` over
the Jordan block sizes `a` of `N` (whose conjugate partition is `conj N`). -/
theorem finrank_centralizer_pow (N : Matrix (Fin n) (Fin n) K) (hN : IsNilpotent N) :
    ∃ (d : ℕ) (a : Fin d → ℕ), (∑ i, a i) = n ∧
      (∀ m, 1 ≤ m → conj (Matrix.toLinAlgEquiv' N) m =
        (Finset.univ.filter fun i => m ≤ a i).card) ∧
      Module.finrank K (centralizer N) = ∑ i, ∑ j, min (a i) (a j) := by
  have hyn : IsNilpotent (Matrix.toLinAlgEquiv' N : Module.End K (Fin n → K)) :=
    hN.map (Matrix.toLinAlgEquiv' (R := K) (n := Fin n))
  obtain ⟨d, k, b, hb⟩ := exists_chainBasis (Matrix.toLinAlgEquiv' N) hyn
  refine ⟨d, k, ?_, fun m hm => hb.conj_eq hm, ?_⟩
  · rw [hb.sum_chainLengths, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  · rw [finrank_centralizer_eq_endCentralizer, hb.finrank_endCentralizer]

end Matrices

end Height.Toolbox
