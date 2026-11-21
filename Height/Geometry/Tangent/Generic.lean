import Height.Geometry.Tangent.ArcOfTangent
import Height.Geometry.DimensionFormula
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Height.Toolbox.LocalRing

/-!
# Arcs at tangent-generic points, by the generic-point route

`Height/Geometry/Tangent/ArcOfTangent.lean` reduces the existence of arcs to one
step: at a point `z` of `Z = V(P)` where `f₁, …, f_c ∈ P` have an invertible
`c × c` Jacobian minor, the arc produced by Newton lifting
(`exists_arc_of_jacobian_unit`) lies in `W = V(f₁, …, f_c)`, and it lies in `Z`
as soon as `W = Z` *near* `z`.  The usual argument gets that from "the local
ring of `W` at `z` is regular, hence a domain", which the pinned mathlib does
not have (see the last section of the module docstring of `ArcOfTangent.lean`).
This file uses the **generic-point route** instead: `P` is a minimal prime of
`(f)`, and each of the finitely many other minimal primes misses a dense open
subset of `Z`.

## Contents

* `pointIdeal w` (`= ker (eval w)`, maximal) and `sub_taylor_mem_sq`, the
  first-order Taylor expansion at a `K`-point.
* `pointIdeal_le_sup_sq`: the Jacobian criterion in spanning form.  If the
  `f j` vanish at `w` with invertible minor along `S`, then every ideal `J`
  containing the `f j` and the `card ι - c` coordinates outside `range S`
  satisfies `pointIdeal w ≤ J ⊔ pointIdeal w ^ 2`.
* `ringKrullDim_quotient_le_of_le_sup_sq`: Nakayama in a Noetherian local ring —
  from `𝔪 ≤ (Q + (s)) + 𝔪²` with `s ⊆ 𝔪` finite, `𝔪 = Q + (s)`, so the maximal
  ideal of `A ⧸ Q` needs at most `#s` generators and `dim (A ⧸ Q) ≤ #s`.
* `le_height_of_le_maximal`, `le_height_of_le_pointIdeal` (**step 2**): every
  prime containing the `f j` and contained in `pointIdeal w` has height `≥ c`.
  The local ring at `w` is Cohen–Macaulay of dimension `card ι`
  (`Height.Geometry.height_of_isMaximal` and mathlib's Cohen–Macaulay stack), so the
  Cohen–Macaulay dimension formula
  `Ideal.height_add_ringKrullDim_quotient_eq_ringKrullDim_of_isPrime` turns the
  Nakayama bound `dim (A_w ⧸ Q A_w) ≤ d` into `height Q ≥ c`.
* `mem_minimalPrimes_of_jacobian` (**step 3**): `P` is a minimal prime of `(f)`.
  `height P = c` by the dimension formula
  (`Height.Geometry.mvPolynomial_height_add_ringKrullDim_quotient_of_isPrime`),
  a minimal prime `Q ≤ P` has `height Q ≥ c` by step 2, and `Q < P` would give
  `height Q < height P` (`Order.height_strictMono`).
* `exists_generic_witness` (**step 4**): a single `g ∉ P` such that at every
  point `z'` of `V(P)` with `g (z') ≠ 0`, `P` is the unique minimal prime of
  `(f)` inside the ideal of `z'` — the hypothesis of
  `forall_prime_of_unique_minimal`.  Note that invertibility of the Jacobian
  minor at `z'` is *not* needed for this.
* `exists_arc_of_tangent_generic` (**the main theorem**): assembling, every
  tangent vector at such a `z'` (with the minor invertible there, as Newton
  lifting requires) is an arc velocity.

Everything is over an arbitrary field; algebraic closedness is nowhere used, the
points being `K`-rational by hypothesis.

The dimension of `K[x_ι] ⧸ P` enters as an explicit natural number `d` with
`c + d = Nat.card ι`, rather than through subtraction in `WithBot ℕ∞`.
-/

universe u v

open MvPolynomial

namespace Height.Geometry.Tangent

variable {K : Type u} [Field K] {ι : Type v} [Fintype ι]

/-! ### The maximal ideal of a `K`-point -/

/-- The coordinate function `X i - C (w i)` centred at the point `w`. -/
noncomputable def coordAt (w : ι → K) (i : ι) : MvPolynomial ι K := X i - C (w i)

/-- The ideal of the point `w`, spanned by the centred coordinates. -/
noncomputable def pointIdeal (w : ι → K) : Ideal (MvPolynomial ι K) :=
  Ideal.span (Set.range (coordAt w))

omit [Fintype ι] in
lemma coordAt_mem_pointIdeal (w : ι → K) (i : ι) : coordAt w i ∈ pointIdeal w :=
  Ideal.subset_span ⟨i, rfl⟩

omit [Fintype ι] in
@[simp] lemma eval_coordAt (w : ι → K) (i : ι) : eval w (coordAt w i) = 0 := by
  simp [coordAt]

omit [Fintype ι] in
/-- `aeval` at the constant tuple `C ∘ w` is `C` of the evaluation at `w`. -/
lemma aeval_C_eq (w : ι → K) (g : MvPolynomial ι K) :
    aeval (fun i => (C (w i) : MvPolynomial ι K)) g = C (eval w g) := by
  induction g using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p n hp => simp [hp]

/-- First-order Taylor expansion at a `K`-point: the error lies in the square of
the point ideal. -/
theorem sub_taylor_mem_sq (w : ι → K) (g : MvPolynomial ι K) :
    g - C (eval w g) - ∑ i, C (eval w (pderiv i g)) * coordAt w i ∈ pointIdeal w ^ 2 := by
  have hE := taylorError_mem_sq (A := MvPolynomial ι K) (R := K)
    (pointIdeal w) (x := fun i => (C (w i) : MvPolynomial ι K)) (y := coordAt w)
    (coordAt_mem_pointIdeal w) g
  have hx : ((fun i => (C (w i) : MvPolynomial ι K)) + coordAt w) = (X : ι → MvPolynomial ι K) := by
    funext i; simp [coordAt]
  rw [taylorError_def, hx] at hE
  simpa only [aeval_X_left_apply, aeval_C_eq] using hE

/-- The point ideal is the kernel of evaluation at the point. -/
theorem pointIdeal_eq_ker (w : ι → K) :
    pointIdeal w = RingHom.ker (eval w : MvPolynomial ι K →+* K) := by
  refine le_antisymm ?_ fun g hg => ?_
  · rw [pointIdeal, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simp [RingHom.mem_ker]
  · have hg0 : eval w g = 0 := RingHom.mem_ker.1 hg
    have hE := sub_taylor_mem_sq w g
    rw [hg0, map_zero, sub_zero] at hE
    have hsum : ∑ i, C (eval w (pderiv i g)) * coordAt w i ∈ pointIdeal w :=
      Submodule.sum_mem _ fun i _ =>
        Ideal.mul_mem_left _ _ (coordAt_mem_pointIdeal w i)
    have := Ideal.add_mem _ (Ideal.pow_le_self (n := 2) (by norm_num) hE) hsum
    simpa using this

lemma mem_pointIdeal_iff {w : ι → K} {g : MvPolynomial ι K} :
    g ∈ pointIdeal w ↔ eval w g = 0 := by
  rw [pointIdeal_eq_ker]; exact RingHom.mem_ker

/-- The point ideal is maximal: evaluation at `w` is a surjection onto the field `K`. -/
theorem pointIdeal_isMaximal (w : ι → K) : (pointIdeal w).IsMaximal := by
  rw [pointIdeal_eq_ker]
  exact RingHom.ker_isMaximal_of_surjective _ fun a => ⟨C a, by simp⟩

instance pointIdeal_isPrime (w : ι → K) : (pointIdeal w).IsPrime :=
  (pointIdeal_isMaximal w).isPrime

/-- **The cotangent space of a `K`-point of affine space.**  An element of the point ideal
lies in its square exactly when all its first partial derivatives vanish at the point
(first-order Taylor expansion, `sub_taylor_mem_sq`, and the Leibniz rule).  So
`pointIdeal w ⧸ (pointIdeal w)²` is the dual of `ι → K` through the differentials. -/
theorem mem_pointIdeal_sq_iff {w : ι → K} {g : MvPolynomial ι K} (hg : g ∈ pointIdeal w) :
    g ∈ pointIdeal w ^ 2 ↔ ∀ i, eval w (pderiv i g) = 0 := by
  have hsq : ∀ h ∈ pointIdeal w ^ 2, ∀ i, eval w (pderiv i h) = 0 := by
    intro h hh
    rw [pow_two] at hh
    refine Submodule.mul_induction_on hh ?_ ?_
    · intro a ha b hb i
      rw [pderiv_mul]
      simp [mem_pointIdeal_iff.mp ha, mem_pointIdeal_iff.mp hb]
    · intro y z hy hz i
      rw [map_add, map_add, hy i, hz i, add_zero]
  refine ⟨fun h i => hsq g h i, fun hd => ?_⟩
  have hE := sub_taylor_mem_sq w g
  rw [mem_pointIdeal_iff.mp hg, map_zero, sub_zero] at hE
  have hzero : ∑ i, C (eval w (pderiv i g)) * coordAt w i = 0 :=
    Finset.sum_eq_zero fun i _ => by rw [hd i, map_zero, zero_mul]
  rwa [hzero, sub_zero] at hE

/-! ### The Jacobian spanning lemma -/

/-- **The Jacobian criterion, spanning form.**  Let `f₁, …, f_c` vanish at `w`
and have an invertible `c × c` Jacobian minor at `w` along the embedding `S`.
Then every ideal `J` containing the `f j` and the coordinates `coordAt w i` for
`i` outside the range of `S` contains the point ideal modulo its square.

This is Nakayama's input: after localising at `w` it says that the maximal ideal
of the local ring of `V(f)` at `w` needs at most `card ι - c` generators. -/
theorem pointIdeal_le_sup_sq {c : ℕ} (f : Fin c → MvPolynomial ι K) (w : ι → K)
    (hf : ∀ j, eval w (f j) = 0) (S : Fin c ↪ ι)
    (hJ : IsUnit (Matrix.of fun j k => eval w (pderiv (S k) (f j))).det)
    (J : Ideal (MvPolynomial ι K)) (hJf : ∀ j, f j ∈ J)
    (hJc : ∀ i, i ∉ Set.range S → coordAt w i ∈ J) :
    pointIdeal w ≤ J ⊔ pointIdeal w ^ 2 := by
  classical
  obtain ⟨e, hemem, hekey⟩ : ∃ e : Fin c → MvPolynomial ι K,
      (∀ j, e j ∈ pointIdeal w ^ 2) ∧
      ∀ j, f j = e j + ∑ i, C (eval w (pderiv i (f j))) * coordAt w i := by
    refine ⟨fun j => f j - ∑ i, C (eval w (pderiv i (f j))) * coordAt w i, fun j => ?_,
      fun j => by ring⟩
    have h := sub_taylor_mem_sq w (f j)
    rwa [hf j, map_zero, sub_zero] at h
  refine (Ideal.span_le (s := Set.range (coordAt w))).2 ?_
  rintro _ ⟨i, rfl⟩
  by_cases hi : i ∈ Set.range S
  · obtain ⟨k, rfl⟩ := hi
    set M : Matrix (Fin c) (Fin c) K :=
      Matrix.of fun j k => eval w (pderiv (S k) (f j)) with hMdef
    have hMinv : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hJ
    obtain ⟨b, hb⟩ : ∃ b : ι → K, ∀ i, b i = ∑ j, M⁻¹ k j * eval w (pderiv i (f j)) :=
      ⟨_, fun _ => rfl⟩
    have step1 : ∀ j : Fin c, C (M⁻¹ k j) * f j
        = C (M⁻¹ k j) * e j
          + ∑ i, C (M⁻¹ k j * eval w (pderiv i (f j))) * coordAt w i := by
      intro j
      conv_lhs => rw [hekey j]
      rw [mul_add, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul]
      ring
    have hexp : ∑ j, C (M⁻¹ k j) * f j
        = (∑ j, C (M⁻¹ k j) * e j) + ∑ i, C (b i) * coordAt w i := by
      rw [Finset.sum_congr rfl fun j _ => step1 j, Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hb i, ← Finset.sum_mul, ← map_sum]
    have hb_S : ∀ k' : Fin c, b (S k') = if k = k' then 1 else 0 := by
      intro k'
      rw [hb]
      have hmm : ∑ j, M⁻¹ k j * eval w (pderiv (S k') (f j)) = (M⁻¹ * M) k k' := by
        rw [Matrix.mul_apply]
        exact Finset.sum_congr rfl fun j _ => by rw [hMdef]; rfl
      rw [hmm, hMinv, Matrix.one_apply]
    set T : Finset ι := Finset.univ.image S with hT
    have hsplit : (∑ i, C (b i) * coordAt w i)
        = (∑ i ∈ Finset.univ \ T, C (b i) * coordAt w i) + coordAt w (S k) := by
      rw [← Finset.sum_sdiff (Finset.subset_univ T)]
      congr 1
      rw [hT, Finset.sum_image (fun x _ y _ h => S.injective h)]
      rw [Finset.sum_congr rfl fun k' _ => by rw [hb_S k']]
      simp only [apply_ite C, map_one, map_zero, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    have hfinal : coordAt w (S k)
        = (∑ j, C (M⁻¹ k j) * f j) - (∑ j, C (M⁻¹ k j) * e j)
          - ∑ i ∈ Finset.univ \ T, C (b i) * coordAt w i := by
      rw [hexp, hsplit]; ring
    rw [SetLike.mem_coe, hfinal]
    refine Ideal.sub_mem _ (Ideal.sub_mem _ ?_ ?_) ?_
    · exact Submodule.mem_sup_left
        (Submodule.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hJf j))
    · exact Submodule.mem_sup_right
        (Submodule.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hemem j))
    · refine Submodule.mem_sup_left
        (Submodule.sum_mem _ fun i hi => Ideal.mul_mem_left _ _ (hJc i ?_))
      intro hcon
      obtain ⟨k', rfl⟩ := hcon
      have h2 := (Finset.mem_sdiff.1 hi).2
      rw [hT] at h2
      exact h2 (Finset.mem_image.2 ⟨k', Finset.mem_univ _, rfl⟩)
  · exact Submodule.mem_sup_left (hJc i hi)

/-! ### Nakayama: a local dimension bound from a spanning statement modulo `𝔪²` -/

/-- **Nakayama.**  If the maximal ideal of a Noetherian local ring `A` is contained in
`Q + (s) + 𝔪²` for a finite set `s ⊆ 𝔪`, then the maximal ideal of `A ⧸ Q` is generated by
the image of `s`. -/
theorem maximalIdeal_quotient_eq_span_of_le_sup_sq {A : Type*} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] (Q : Ideal A) (hQ : Q ≠ ⊤) {s : Set A} (_hs : s.Finite)
    (hsm : s ⊆ (IsLocalRing.maximalIdeal A : Set A))
    (hle : IsLocalRing.maximalIdeal A ≤ (Q ⊔ Ideal.span s) ⊔ IsLocalRing.maximalIdeal A ^ 2)
    [IsLocalRing (A ⧸ Q)] :
    IsLocalRing.maximalIdeal (A ⧸ Q) = Ideal.span ((Ideal.Quotient.mk Q) '' s) := by
  classical
  have hQm : Q ≤ IsLocalRing.maximalIdeal A := IsLocalRing.le_maximalIdeal hQ
  have hnak : IsLocalRing.maximalIdeal A ≤ Q ⊔ Ideal.span s := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _)
      (IsLocalRing.maximalIdeal_le_jacobson ⊥) ?_
    have hsq : (IsLocalRing.maximalIdeal A) • (IsLocalRing.maximalIdeal A)
        = IsLocalRing.maximalIdeal A ^ 2 := by rw [Ideal.smul_eq_mul, sq]
    rw [hsq]
    exact hle
  have hmeq : IsLocalRing.maximalIdeal A = Q ⊔ Ideal.span s :=
    le_antisymm hnak (sup_le hQm (Ideal.span_le.2 hsm))
  have hmaxmap : (Ideal.map (Ideal.Quotient.mk Q) (IsLocalRing.maximalIdeal A)).IsMaximal := by
    rcases Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk Q)
        Ideal.Quotient.mk_surjective (IsLocalRing.maximalIdeal.isMaximal A) with h | h
    · exfalso
      have hc : Ideal.comap (Ideal.Quotient.mk Q)
          (Ideal.map (Ideal.Quotient.mk Q) (IsLocalRing.maximalIdeal A))
          = IsLocalRing.maximalIdeal A := by
        rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
          ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
        exact sup_eq_left.2 hQm
      rw [h, Ideal.comap_top] at hc
      exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top hc.symm
    · exact h
  rw [← IsLocalRing.eq_maximalIdeal hmaxmap, hmeq, Ideal.map_sup, Ideal.map_quotient_self,
    bot_sup_eq, Ideal.map_span]

/-- If the maximal ideal of a Noetherian local ring `A` is contained in
`Q + (s) + 𝔪²` for a finite set `s ⊆ 𝔪`, then `𝔪 = Q + (s)` (Nakayama), so the
maximal ideal of `A ⧸ Q` is generated by the image of `s` and Krull's height
theorem bounds `dim (A ⧸ Q)` by the cardinality of `s`. -/
theorem ringKrullDim_quotient_le_of_le_sup_sq {A : Type*} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] (Q : Ideal A) (hQ : Q ≠ ⊤) {s : Set A} (hs : s.Finite)
    (hsm : s ⊆ (IsLocalRing.maximalIdeal A : Set A))
    (hle : IsLocalRing.maximalIdeal A ≤ (Q ⊔ Ideal.span s) ⊔ IsLocalRing.maximalIdeal A ^ 2) :
    ringKrullDim (A ⧸ Q) ≤ (s.ncard : WithBot ℕ∞) := by
  have _ : Nontrivial (A ⧸ Q) := Ideal.Quotient.nontrivial_iff.mpr hQ
  have _ : IsLocalRing (A ⧸ Q) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk Q) Ideal.Quotient.mk_surjective
  refine le_trans (ringKrullDim_le_spanFinrank_maximalIdeal (A ⧸ Q)) ?_
  rw [maximalIdeal_quotient_eq_span_of_le_sup_sq Q hQ hs hsm hle]
  exact_mod_cast le_trans (Submodule.spanFinrank_span_le_ncard_of_finite (hs.image _))
    (Set.ncard_image_le hs)

/-- **Nakayama, regularity form.**  Under the hypotheses of
`ringKrullDim_quotient_le_of_le_sup_sq`, if moreover `dim (A ⧸ Q)` is at least the
cardinality of `s`, then `A ⧸ Q` is a regular local ring: its embedding dimension is at most
`s.ncard ≤ dim (A ⧸ Q)`, and the reverse inequality always holds (Krull's height theorem). -/
theorem isRegularLocalRing_quotient_of_le_sup_sq {A : Type*} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] (Q : Ideal A) (hQ : Q ≠ ⊤) {s : Set A} (hs : s.Finite)
    (hsm : s ⊆ (IsLocalRing.maximalIdeal A : Set A))
    (hle : IsLocalRing.maximalIdeal A ≤ (Q ⊔ Ideal.span s) ⊔ IsLocalRing.maximalIdeal A ^ 2)
    (hdim : (s.ncard : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ Q)) :
    IsRegularLocalRing (A ⧸ Q) := by
  have _ : Nontrivial (A ⧸ Q) := Ideal.Quotient.nontrivial_iff.mpr hQ
  have _ : IsLocalRing (A ⧸ Q) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk Q) Ideal.Quotient.mk_surjective
  refine IsRegularLocalRing.of_spanFinrank_maximalIdeal_le (A ⧸ Q) (le_trans ?_ hdim)
  rw [maximalIdeal_quotient_eq_span_of_le_sup_sq Q hQ hs hsm hle]
  exact_mod_cast le_trans (Submodule.spanFinrank_span_le_ncard_of_finite (hs.image _))
    (Set.ncard_image_le hs)

/-! ### The local ring of a complete intersection at the point -/


/-- **Step 4.**  A complete intersection cut out by `c` equations with an invertible `c × c`
Jacobian minor at a `K`-point `w` has a regular local ring there. -/
theorem isRegularLocalRing_quotient_map_of_jacobian {c d : ℕ} (hcd : c + d = Nat.card ι)
    {f : Fin c → MvPolynomial ι K} {w : ι → K} (hf : ∀ j, eval w (f j) = 0) (S : Fin c ↪ ι)
    (hJ : IsUnit (Matrix.of fun j k => eval w (pderiv (S k) (f j))).det) :
    IsRegularLocalRing ((Localization.AtPrime (pointIdeal w)) ⧸
      (Ideal.span (Set.range f)).map
        (algebraMap (MvPolynomial ι K) (Localization.AtPrime (pointIdeal w)))) := by
  classical
  have hmmax : (pointIdeal w).IsMaximal := pointIdeal_isMaximal w
  have hmp : (pointIdeal w).IsPrime := hmmax.isPrime
  set φ := algebraMap (MvPolynomial ι K) (Localization.AtPrime (pointIdeal w)) with hφ
  have hN : IsNoetherianRing (Localization.AtPrime (pointIdeal w)) :=
    IsLocalization.isNoetherianRing (pointIdeal w).primeCompl _ inferInstance
  have hAdim : ringKrullDim (Localization.AtPrime (pointIdeal w))
      = (Nat.card ι : WithBot ℕ∞) := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height (pointIdeal w)
      (Localization.AtPrime (pointIdeal w)), height_of_isMaximal K ι (pointIdeal w) hmmax]
    simp
  have hmA : Ideal.map φ (pointIdeal w)
      = IsLocalRing.maximalIdeal (Localization.AtPrime (pointIdeal w)) :=
    IsLocalization.AtPrime.map_eq_maximalIdeal (pointIdeal w) _
  have hJm : Ideal.span (Set.range f) ≤ pointIdeal w := by
    rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    exact mem_pointIdeal_iff.2 (hf j)
  have hsfin : (coordAt w '' (Set.range S)ᶜ).Finite := Set.Finite.image _ (Set.toFinite _)
  have hsm : (coordAt w '' (Set.range S)ᶜ) ⊆ (pointIdeal w : Set (MvPolynomial ι K)) := by
    rintro _ ⟨i, -, rfl⟩
    exact coordAt_mem_pointIdeal w i
  have hsc : (coordAt w '' (Set.range S)ᶜ).ncard ≤ d := by
    refine le_trans (Set.ncard_image_le (Set.toFinite _)) ?_
    have h1 : (Set.range S).ncard = c := by
      rw [Set.ncard_range_of_injective S.injective]; simp
    have h2 : (Set.range S).ncard + ((Set.range S)ᶜ).ncard = Nat.card ι :=
      Set.ncard_add_ncard_compl _
    rw [h1] at h2
    omega
  have hle : pointIdeal w ≤
      (Ideal.span (Set.range f) ⊔ Ideal.span (coordAt w '' (Set.range S)ᶜ)) ⊔ pointIdeal w ^ 2 :=
    pointIdeal_le_sup_sq f w hf S hJ _
      (fun j => Submodule.mem_sup_left (Ideal.subset_span ⟨j, rfl⟩))
      (fun i hi => Submodule.mem_sup_right (Ideal.subset_span ⟨i, hi, rfl⟩))
  have hQle : (Ideal.span (Set.range f)).map φ ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime (pointIdeal w)) := by
    rw [← hmA]
    exact Ideal.map_mono hJm
  have hQtop : (Ideal.span (Set.range f)).map φ ≠ ⊤ := fun h =>
    (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.mp (h ▸ hQle))
  have hleA : IsLocalRing.maximalIdeal (Localization.AtPrime (pointIdeal w)) ≤
      ((Ideal.span (Set.range f)).map φ ⊔ Ideal.span (⇑φ '' (coordAt w '' (Set.range S)ᶜ)))
        ⊔ IsLocalRing.maximalIdeal (Localization.AtPrime (pointIdeal w)) ^ 2 := by
    have h := Ideal.map_mono (f := φ) hle
    simp only [Ideal.map_sup, Ideal.map_pow, Ideal.map_span, hmA] at h
    simpa only [Ideal.map_span] using h
  have hsmA : (⇑φ '' (coordAt w '' (Set.range S)ᶜ)) ⊆
      (IsLocalRing.maximalIdeal (Localization.AtPrime (pointIdeal w)) : Set _) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← hmA]
    exact Ideal.mem_map_of_mem _ (hsm hx)
  -- the dimension lower bound
  have _ : Nontrivial (Localization.AtPrime (pointIdeal w) ⧸ (Ideal.span (Set.range f)).map φ) :=
    Ideal.Quotient.nontrivial_iff.mpr hQtop
  have hspan : ((Ideal.span (Set.range f)).map φ).spanFinrank ≤ c := by
    rw [Ideal.map_span]
    refine le_trans (Submodule.spanFinrank_span_le_ncard_of_finite
      ((Set.finite_range f).image _)) ?_
    refine le_trans (Set.ncard_image_le (Set.finite_range f)) ?_
    rw [← Set.image_univ]
    exact le_trans (Set.ncard_image_le Set.finite_univ) (by simp [Set.ncard_univ])
  have hjac : (Ideal.span (Set.range f)).map φ ≤
      Ring.jacobson (Localization.AtPrime (pointIdeal w)) := by
    rw [← Ideal.jacobson_bot]
    exact le_trans hQle (IsLocalRing.maximalIdeal_le_jacobson ⊥)
  have hkey := ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank _ hjac
  rw [hAdim] at hkey
  have hnb : ringKrullDim (Localization.AtPrime (pointIdeal w) ⧸
      (Ideal.span (Set.range f)).map φ) ≠ ⊥ := by
    rw [Ne, ringKrullDim_eq_bot_iff_subsingleton]
    exact not_subsingleton _
  obtain ⟨v, hv⟩ := WithBot.ne_bot_iff_exists.mp hnb
  have hkey2 : ((Nat.card ι : ℕ) : WithBot ℕ∞) ≤ (v : WithBot ℕ∞) + (c : WithBot ℕ∞) := by
    refine le_trans hkey ?_
    rw [hv]
    exact add_le_add le_rfl (by exact_mod_cast hspan)
  have hdv : (d : ℕ∞) ≤ v := by
    have h1 : ((Nat.card ι : ℕ) : ℕ∞) ≤ v + (c : ℕ∞) := by exact_mod_cast hkey2
    rw [← hcd] at h1
    push_cast at h1
    rw [add_comm (c : ℕ∞) (d : ℕ∞)] at h1
    exact (ENat.add_le_add_iff_right (by simp)).mp h1
  refine isRegularLocalRing_quotient_of_le_sup_sq _ hQtop (hsfin.image _) hsmA hleA ?_
  rw [← hv]
  refine le_trans ?_ (by exact_mod_cast hdv : ((d : ℕ∞) : WithBot ℕ∞) ≤ (v : WithBot ℕ∞))
  exact_mod_cast le_trans (Set.ncard_image_le hsfin) hsc
/-! ### The height of a prime through a tangent-generic point -/

/-- **Step 2, abstract form.**  In `MvPolynomial ι K` with `c + d = card ι`, let `m`
be a maximal ideal, `Q ≤ m` a prime, and `s` a set of at most `d` elements of `m`
with `m ≤ (Q + (s)) + m²`.  Then `height Q ≥ c`.

The local ring at `m` is Cohen–Macaulay of dimension `card ι`
(`Height.Geometry.height_of_isMaximal`), Nakayama gives
`dim (A_m ⧸ Q A_m) ≤ d` (`ringKrullDim_quotient_le_of_le_sup_sq`), and the
Cohen–Macaulay dimension formula does the rest. -/
theorem le_height_of_le_maximal {c d : ℕ} (hcd : c + d = Nat.card ι)
    (m : Ideal (MvPolynomial ι K)) (hm : m.IsMaximal)
    (Q : Ideal (MvPolynomial ι K)) [hQp : Q.IsPrime] (hQm : Q ≤ m)
    {s : Set (MvPolynomial ι K)} (hs : s.Finite) (hsm : s ⊆ (m : Set (MvPolynomial ι K)))
    (hsc : s.ncard ≤ d) (hle : m ≤ (Q ⊔ Ideal.span s) ⊔ m ^ 2) :
    (c : ℕ∞) ≤ Q.height := by
  classical
  have hmp : m.IsPrime := hm.isPrime
  have hN : IsNoetherianRing (Localization.AtPrime m) :=
    IsLocalization.isNoetherianRing m.primeCompl _ inferInstance
  have hcmA : IsCohenMacaulayLocalRing (Localization.AtPrime m) :=
    (isCohenMacaulayRing_def (MvPolynomial ι K)).mp
      (isCohenMacaulayRing_mvPolynomial K ι) m hm.isPrime
  set φ := algebraMap (MvPolynomial ι K) (Localization.AtPrime m) with hφ
  have hdisj : Disjoint (m.primeCompl : Set (MvPolynomial ι K)) (Q : Set (MvPolynomial ι K)) :=
    Set.disjoint_left.mpr fun a ha hb => ha (hQm hb)
  have hQAp : (Q.map φ).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint m.primeCompl _ Q hQp hdisj
  have hQAht : (Q.map φ).height = Q.height :=
    IsLocalization.height_map_of_disjoint m.primeCompl Q hdisj
  have hAdim : ringKrullDim (Localization.AtPrime m) = (Nat.card ι : WithBot ℕ∞) := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height m (Localization.AtPrime m),
      height_of_isMaximal K ι m hm]
    simp
  have hmA : Ideal.map φ m = IsLocalRing.maximalIdeal (Localization.AtPrime m) :=
    IsLocalization.AtPrime.map_eq_maximalIdeal m (Localization.AtPrime m)
  have hleA : IsLocalRing.maximalIdeal (Localization.AtPrime m)
      ≤ (Q.map φ ⊔ Ideal.span (⇑φ '' s))
        ⊔ IsLocalRing.maximalIdeal (Localization.AtPrime m) ^ 2 := by
    have h := Ideal.map_mono (f := φ) hle
    rwa [Ideal.map_sup, Ideal.map_sup, Ideal.map_pow, Ideal.map_span, hmA] at h
  have hsmA : (⇑φ '' s) ⊆ (IsLocalRing.maximalIdeal (Localization.AtPrime m) : Set _) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← hmA]
    exact Ideal.mem_map_of_mem _ (hsm hx)
  have hquot := ringKrullDim_quotient_le_of_le_sup_sq (Q.map φ) hQAp.ne_top (hs.image _) hsmA hleA
  have hcard : (⇑φ '' s).ncard ≤ d := le_trans (Set.ncard_image_le hs) hsc
  have hquot' : ringKrullDim (Localization.AtPrime m ⧸ Q.map φ) ≤ (d : WithBot ℕ∞) :=
    le_trans hquot (by exact_mod_cast hcard)
  have key := Ideal.height_add_ringKrullDim_quotient_eq_ringKrullDim_of_isPrime
    (R := Localization.AtPrime m) (Q.map φ)
  rw [hAdim] at key
  have hge : (Nat.card ι : WithBot ℕ∞) ≤ ((Q.map φ).height : WithBot ℕ∞) + (d : WithBot ℕ∞) := by
    rw [← key]
    exact add_le_add le_rfl hquot'
  have hge' : (Nat.card ι : ℕ∞) ≤ (Q.map φ).height + (d : ℕ∞) := by exact_mod_cast hge
  rw [← hcd] at hge'
  push_cast at hge'
  rw [← hQAht]
  exact (ENat.add_le_add_iff_right (by simp)).mp hge'

/-- **Step 2.**  Every prime containing `f₁, …, f_c` and contained in the ideal of
a point `w` at which the `f j` vanish with invertible Jacobian minor has height
at least `c`. -/
theorem le_height_of_le_pointIdeal {c d : ℕ} (hcd : c + d = Nat.card ι)
    {f : Fin c → MvPolynomial ι K} {w : ι → K} (hf : ∀ j, eval w (f j) = 0)
    (S : Fin c ↪ ι)
    (hJ : IsUnit (Matrix.of fun j k => eval w (pderiv (S k) (f j))).det)
    (Q : Ideal (MvPolynomial ι K)) [Q.IsPrime]
    (hfQ : ∀ j, f j ∈ Q) (hQw : Q ≤ pointIdeal w) :
    (c : ℕ∞) ≤ Q.height := by
  classical
  have hsfin : (coordAt w '' (Set.range S)ᶜ).Finite := Set.Finite.image _ (Set.toFinite _)
  have hsm : (coordAt w '' (Set.range S)ᶜ) ⊆ (pointIdeal w : Set (MvPolynomial ι K)) := by
    rintro _ ⟨i, -, rfl⟩
    exact coordAt_mem_pointIdeal w i
  have hsc : (coordAt w '' (Set.range S)ᶜ).ncard ≤ d := by
    refine le_trans (Set.ncard_image_le (Set.toFinite _)) ?_
    have h1 : (Set.range S).ncard = c := by
      rw [Set.ncard_range_of_injective S.injective]; simp
    have h2 : (Set.range S).ncard + ((Set.range S)ᶜ).ncard = Nat.card ι :=
      Set.ncard_add_ncard_compl _
    rw [h1] at h2
    omega
  have hle : pointIdeal w ≤ (Q ⊔ Ideal.span (coordAt w '' (Set.range S)ᶜ)) ⊔ pointIdeal w ^ 2 := by
    refine pointIdeal_le_sup_sq f w hf S hJ _ (fun j => Submodule.mem_sup_left (hfQ j))
      (fun i hi => Submodule.mem_sup_right (Ideal.subset_span ⟨i, hi, rfl⟩))
  exact le_height_of_le_maximal hcd (pointIdeal w) (pointIdeal_isMaximal w) Q hQw hsfin hsm hsc hle

/-! ### `P` is a minimal prime of the complete intersection -/

/-- **Step 3.**  With `c + d = card ι`, `dim (R ⧸ P) = d` and `f₁, …, f_c ∈ P`
having an invertible Jacobian minor at a point `z` of `V(P)`, the prime `P` is a
minimal prime of `(f₁, …, f_c)`.

`height P = c` by the dimension formula; any minimal prime `Q ≤ P` of
`(f)` has `height Q ≥ c` by `le_height_of_le_pointIdeal`, and a strict
containment of primes would force `height Q < height P`. -/
theorem mem_minimalPrimes_of_jacobian {c d : ℕ} (hcd : c + d = Nat.card ι)
    (P : Ideal (MvPolynomial ι K)) [hP : P.IsPrime]
    (hdim : ringKrullDim (MvPolynomial ι K ⧸ P) = (d : WithBot ℕ∞))
    {f : Fin c → MvPolynomial ι K} (hfP : ∀ j, f j ∈ P) {z : ι → K}
    (hz : ∀ g ∈ P, eval z g = 0) (S : Fin c ↪ ι)
    (hJ : IsUnit (Matrix.of fun j k => eval z (pderiv (S k) (f j))).det) :
    P ∈ (Ideal.span (Set.range f)).minimalPrimes := by
  classical
  have hPz : P ≤ pointIdeal z := fun g hg => mem_pointIdeal_iff.2 (hz g hg)
  have hfz : ∀ j, eval z (f j) = 0 := fun j => hz _ (hfP j)
  have hPh : P.height = (c : ℕ∞) := by
    have h := mvPolynomial_height_add_ringKrullDim_quotient_of_isPrime K ι P
    rw [hdim, ← hcd] at h
    have h' : P.height + (d : ℕ∞) = (c : ℕ∞) + (d : ℕ∞) := by exact_mod_cast h
    exact le_antisymm ((ENat.add_le_add_iff_right (by simp)).mp h'.le)
      ((ENat.add_le_add_iff_right (by simp)).mp h'.ge)
  have hfspan : Ideal.span (Set.range f) ≤ P :=
    Ideal.span_le.2 (by rintro _ ⟨j, rfl⟩; exact hfP j)
  obtain ⟨Q, hQmin, hQP⟩ := Ideal.exists_minimalPrimes_le (J := P) hfspan
  have hQprime : Q.IsPrime := hQmin.isPrime
  have hQh : (c : ℕ∞) ≤ Q.height :=
    le_height_of_le_pointIdeal hcd hfz S hJ Q
      (fun j => hQmin.le (Ideal.subset_span ⟨j, rfl⟩)) (hQP.trans hPz)
  have hQeq : Q = P := by
    by_contra hne
    have hlt : (⟨Q, hQprime⟩ : PrimeSpectrum (MvPolynomial ι K)) < ⟨P, hP⟩ :=
      lt_of_le_of_ne hQP fun h => hne (congrArg PrimeSpectrum.asIdeal h)
    have h1 : (⟨Q, hQprime⟩ : PrimeSpectrum (MvPolynomial ι K)).asIdeal.height
        = Order.height (⟨Q, hQprime⟩ : PrimeSpectrum (MvPolynomial ι K)) :=
      PrimeSpectrum.height_eq_orderHeight _
    have h2 : (⟨P, hP⟩ : PrimeSpectrum (MvPolynomial ι K)).asIdeal.height
        = Order.height (⟨P, hP⟩ : PrimeSpectrum (MvPolynomial ι K)) :=
      PrimeSpectrum.height_eq_orderHeight _
    have hfinQ : Q.height ≠ ⊤ := Ideal.height_ne_top hQprime.ne_top
    have hstrict := Order.height_strictMono hlt (by rw [← h1]; exact Ne.lt_top hfinQ)
    rw [← h1, ← h2] at hstrict
    simp only at hstrict
    rw [hPh] at hstrict
    exact absurd hQh (not_le.2 hstrict)
  rwa [← hQeq]

/-! ### The generic-point witness -/

/-- **The generic-point step.**  There is a function `g ∉ P` such that at every
point `z'` of `V(P)` with `g (z') ≠ 0`, the prime `P` is the *only* minimal prime
of `(f₁, …, f_c)` contained in the ideal of `z'`.

`P` is one of the finitely many minimal primes of `(f)` (`Step 3`); each of the
others fails to be contained in `P`, so a witness `g_Q ∈ Q ∖ P` can be chosen and
`g` is their product. -/
theorem exists_generic_witness {c d : ℕ} (hcd : c + d = Nat.card ι)
    (P : Ideal (MvPolynomial ι K)) [hP : P.IsPrime]
    (hdim : ringKrullDim (MvPolynomial ι K ⧸ P) = (d : WithBot ℕ∞))
    {f : Fin c → MvPolynomial ι K} (hfP : ∀ j, f j ∈ P) {z : ι → K}
    (hz : ∀ g ∈ P, eval z g = 0) (S : Fin c ↪ ι)
    (hJ : IsUnit (Matrix.of fun j k => eval z (pderiv (S k) (f j))).det) :
    ∃ g : MvPolynomial ι K, g ∉ P ∧ ∀ z' : ι → K, eval z' g ≠ 0 →
      ∀ Q ∈ (Ideal.span (Set.range f)).minimalPrimes, Q ≤ pointIdeal z' → Q = P := by
  classical
  have hPmin : P ∈ (Ideal.span (Set.range f)).minimalPrimes :=
    mem_minimalPrimes_of_jacobian hcd P hdim hfP hz S hJ
  have : Finite (Ideal.span (Set.range f)).minimalPrimes :=
    Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial ι K) (Ideal.span (Set.range f))
  have hfin : (Ideal.span (Set.range f)).minimalPrimes.Finite := Set.toFinite _
  have hchoice : ∀ Q ∈ hfin.toFinset, Q ≠ P → ∃ x, x ∈ Q ∧ x ∉ P := by
    intro Q hQF hQP
    have hQmin : Q ∈ (Ideal.span (Set.range f)).minimalPrimes := hfin.mem_toFinset.1 hQF
    by_contra hcon
    push Not at hcon
    exact hQP (le_antisymm (fun x hx => hcon x hx)
      (hPmin.2 ⟨hQmin.isPrime, hQmin.le⟩ (fun x hx => hcon x hx)))
  choose! gg hgg1 hgg2 using hchoice
  refine ⟨∏ Q ∈ hfin.toFinset.filter (fun Q => Q ≠ P), gg Q, ?_, ?_⟩
  · refine Finset.prod_induction _ (fun x => x ∉ P) (fun a b ha hb hab => ?_)
      (fun h => hP.ne_top ((Ideal.eq_top_iff_one P).2 h)) (fun Q hQ => ?_)
    · exact (hP.mem_or_mem hab).elim ha hb
    · rw [Finset.mem_filter] at hQ
      exact hgg2 Q hQ.1 hQ.2
  · intro z' hgz' Q hQmin hQz'
    by_contra hne
    have hQF : Q ∈ hfin.toFinset := hfin.mem_toFinset.2 hQmin
    have h0 : eval z' (gg Q) = 0 := mem_pointIdeal_iff.1 (hQz' (hgg1 Q hQF hne))
    exact hgz' (by rw [map_prod]; exact Finset.prod_eq_zero (Finset.mem_filter.2 ⟨hQF, hne⟩) h0)

/-! ### Arcs at tangent-generic points -/

/-- Let `P` be a prime of `K[x_ι]` with `dim (K[x_ι] ⧸ P) = d` and
`c + d = card ι`, and let `f₁, …, f_c ∈ P` have an invertible `c × c` Jacobian
minor along `S` at some point `z` of the zero locus of `P`.

Then there is `g ∉ P` such that at *every* point `z'` of the zero locus of `P`
with `g (z') ≠ 0` and the same minor invertible, every tangent vector of the zero
locus at `z'` is the velocity of an arc lying in the zero locus.

The step "`W = Z` near `z`" is supplied by `exists_generic_witness`, which uses
the generic-point argument in place of the implication "regular local ring ⇒
domain". -/
theorem exists_arc_of_tangent_generic {c d : ℕ} (hcd : c + d = Nat.card ι)
    (P : Ideal (MvPolynomial ι K)) [hP : P.IsPrime]
    (hdim : ringKrullDim (MvPolynomial ι K ⧸ P) = (d : WithBot ℕ∞))
    (f : Fin c → MvPolynomial ι K) (hfP : ∀ j, f j ∈ P) (z : ι → K)
    (hz : ∀ g ∈ P, eval z g = 0) (S : Fin c ↪ ι)
    (hJ : IsUnit (Matrix.of fun j k => eval z (pderiv (S k) (f j))).det) :
    ∃ g : MvPolynomial ι K, g ∉ P ∧
      ∀ z' : ι → K, (∀ h ∈ P, eval z' h = 0) → eval z' g ≠ 0 →
        IsUnit (Matrix.of fun j k => eval z' (pderiv (S k) (f j))).det →
        ∀ v : ι → K, (∀ h ∈ P, ∑ i, eval z' (pderiv i h) * v i = 0) →
          ∃ a : ι → PowerSeries K, (∀ i, PowerSeries.constantCoeff (a i) = z' i) ∧
            (∀ i, PowerSeries.coeff 1 (a i) = v i) ∧ ∀ h ∈ P, aeval a h = 0 := by
  obtain ⟨g, hgP, hg⟩ := exists_generic_witness hcd P hdim hfP hz S hJ
  refine ⟨g, hgP, fun z' hz' hgz' hJ' v hv => ?_⟩
  refine exists_arc_of_tangent_of_forall_prime P f hfP z' S hJ' hz' ?_ v hv
  intro Q hQp hfQ hQz
  exact forall_prime_of_unique_minimal (Ideal.span (Set.range f)) (pointIdeal z') P
    (fun Q' hQ'min hQ'le => hg z' hgz' Q' hQ'min hQ'le) Q hQp hfQ
    (fun x hx => mem_pointIdeal_iff.2 (hQz x hx))

end Height.Geometry.Tangent
