import Mathlib.LinearAlgebra.Matrix.Rank
import Height.Orbital.Arcs

/-!
# The range of a matrix of constant rank over `K⟦s⟧` is saturated

Let `A` be a matrix over the discrete valuation ring
`R = K⟦s⟧`, with fraction field `L = K⸨s⸩` and residue field `K`.  If the rank
of `A` over `L` equals the rank of its constant term over `K` — which, along
an arc in a chain stratum, is what `conj_of_inStratum` provides — then
the image of `A` over `R` is *saturated*: a vector of `R^m` that lies in the
image after inverting `s` already lies in the image over `R`.

The proof is by Smith normal form (`Submodule.smithNormalForm`).
Writing `N = im A ⊆ R^m` in Smith normal form
`bN i = a i • bM (f i)` with `k` diagonal entries:

* the `k` vectors `bM (f i)` become, over `L`, an independent family inside
  `im A_L`, so `k ≤ rank_L A_L` (denominator clearing preserves independence);
* modulo `s`, `N` is spanned by those `bM (f i)` with `a i` a unit, because a
  non-unit of `K⟦s⟧` has zero constant term, so
  `rank_K A_0 ≤ #{i : a i is a unit}`.

The rank hypothesis squeezes `k ≤ #{i : a i is a unit} ≤ k`, so every `a i` is
a unit, `N` is spanned by part of a basis of `R^m`, and saturation is a
coordinate computation.
-/

namespace Height.Orbital

open Matrix
open Height.Toolbox

universe u

section Saturation

variable {K : Type u} [Field K]

private theorem constantCoeff_eq_zero_of_not_isUnit {φ : PowerSeries K} (h : ¬ IsUnit φ) :
    PowerSeries.constantCoeff φ = 0 := by
  by_contra hne
  exact h (PowerSeries.isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr hne))

private theorem vecC_sum {p : ℕ} {ι : Type*} (s : Finset ι)
    (F : ι → (Fin p → PowerSeries K)) :
    vecC (∑ i ∈ s, F i) = ∑ i ∈ s, vecC (F i) := by
  funext j
  simp only [vecC, Finset.sum_apply, map_sum]

private theorem vecC_smul {p : ℕ} (c : PowerSeries K) (v : Fin p → PowerSeries K) :
    vecC (c • v) = PowerSeries.constantCoeff c • vecC v := by
  funext j
  simp [vecC]

/-- Denominator clearing preserves linear independence: an `R`-independent
family of vectors over `K⟦s⟧` stays independent over `K⸨s⸩`. -/
private theorem linearIndependent_algebraMap {p q : ℕ}
    {V : Fin p → (Fin q → PowerSeries K)}
    (hV : LinearIndependent (PowerSeries K) V) :
    LinearIndependent (LaurentSeries K)
      (fun i => fun j => algebraMap (PowerSeries K) (LaurentSeries K) (V i j)) := by
  have hinj : Function.Injective (algebraMap (PowerSeries K) (LaurentSeries K)) :=
    IsFractionRing.injective (PowerSeries K) (LaurentSeries K)
  rw [linearIndependent_iff']
  intro s g hg i hi
  obtain ⟨dd, hdd⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors (PowerSeries K)) g
  choose e he using fun i => RingHom.mem_rangeS.mp (hdd i)
  have hdne : algebraMap (PowerSeries K) (LaurentSeries K) (dd : PowerSeries K) ≠ 0 := by
    simpa using (map_ne_zero_iff _ hinj).mpr (nonZeroDivisors.coe_ne_zero dd)
  have hzero : ∑ i ∈ s, e i • V i = 0 := by
    funext j
    apply hinj
    have hgj : ∑ i ∈ s, g i * algebraMap (PowerSeries K) (LaurentSeries K) (V i j) = 0 := by
      have := congrFun hg j
      simpa [Finset.sum_apply, smul_eq_mul] using this
    calc algebraMap (PowerSeries K) (LaurentSeries K) ((∑ i ∈ s, e i • V i) j)
        = ∑ i ∈ s, algebraMap (PowerSeries K) (LaurentSeries K) (e i) *
            algebraMap (PowerSeries K) (LaurentSeries K) (V i j) := by
          simp [Finset.sum_apply, map_sum, smul_eq_mul]
      _ = ∑ i ∈ s, algebraMap (PowerSeries K) (LaurentSeries K) (dd : PowerSeries K) *
            (g i * algebraMap (PowerSeries K) (LaurentSeries K) (V i j)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [he i]
          simp [Algebra.smul_def, mul_assoc]
      _ = algebraMap (PowerSeries K) (LaurentSeries K) (dd : PowerSeries K) *
            ∑ i ∈ s, g i * algebraMap (PowerSeries K) (LaurentSeries K) (V i j) := by
          rw [Finset.mul_sum]
      _ = algebraMap (PowerSeries K) (LaurentSeries K) 0 := by rw [hgj, mul_zero, map_zero]
  have hei := (linearIndependent_iff'.mp hV) s e hzero i hi
  have h1 : algebraMap (PowerSeries K) (LaurentSeries K) (dd : PowerSeries K) * g i = 0 := by
    have h2 := he i
    rw [hei, map_zero, Algebra.smul_def] at h2
    exact h2.symm
  rcases mul_eq_zero.mp h1 with h | h
  · exact absurd h hdne
  · exact h

/-- Saturation for an arbitrary matrix over `K⟦s⟧` whose rank over
`K⸨s⸩` equals the rank of its constant term: the image of `A` over `K⟦s⟧` is
saturated. -/
theorem PowerSeries.range_saturated_of_rank_eq {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) (PowerSeries K))
    (hrank : (A.map (algebraMap (PowerSeries K) (LaurentSeries K))).rank =
      (A.map (PowerSeries.constantCoeff (R := K))).rank)
    {b : Fin m → PowerSeries K}
    (hb : (fun i => algebraMap (PowerSeries K) (LaurentSeries K) (b i)) ∈
      LinearMap.range (A.map (algebraMap (PowerSeries K) (LaurentSeries K))).mulVecLin) :
    b ∈ LinearMap.range A.mulVecLin := by
  classical
  have hinj : Function.Injective (algebraMap (PowerSeries K) (LaurentSeries K)) :=
    IsFractionRing.injective (PowerSeries K) (LaurentSeries K)
  obtain ⟨k, snf⟩ :=
    Submodule.smithNormalForm (Pi.basisFun (PowerSeries K) (Fin m))
      (LinearMap.range A.mulVecLin)
  -- the diagonal entries are nonzero
  have hane : ∀ i, snf.a i ≠ 0 := by
    intro i hai
    have h0 : ((snf.bN i : LinearMap.range A.mulVecLin) : Fin m → PowerSeries K) = 0 := by
      rw [snf.snf i, hai, zero_smul]
    exact snf.bN.ne_zero i (Subtype.ext h0)
  -- every element of the range is an explicit combination of the `bM (f i)`
  have hdecomp : ∀ p ∈ LinearMap.range A.mulVecLin, ∃ r : Fin k → PowerSeries K,
      p = ∑ i, (r i * snf.a i) • snf.bM (snf.f i) := by
    intro p hp
    refine ⟨fun i => snf.bN.repr ⟨p, hp⟩ i, ?_⟩
    have h2 := congrArg (Submodule.subtype (LinearMap.range A.mulVecLin))
      (snf.bN.sum_repr ⟨p, hp⟩)
    rw [map_sum] at h2
    simp only [map_smul, Submodule.subtype_apply] at h2
    exact h2.symm.trans (Finset.sum_congr rfl fun i _ => by rw [snf.snf i, smul_smul])
  -- (E) over `L`, the `bM (f i)` are `k` independent vectors of the image
  have hmemL : ∀ i : Fin k,
      (fun j => algebraMap (PowerSeries K) (LaurentSeries K) (snf.bM (snf.f i) j)) ∈
        LinearMap.range (A.map (algebraMap (PowerSeries K) (LaurentSeries K))).mulVecLin := by
    intro i
    obtain ⟨wi, hwi⟩ : ∃ wi, A *ᵥ wi = snf.a i • snf.bM (snf.f i) := by
      have := (snf.bN i).2
      rw [snf.snf i] at this
      exact this
    have hai : algebraMap (PowerSeries K) (LaurentSeries K) (snf.a i) ≠ 0 :=
      (map_ne_zero_iff _ hinj).mpr (hane i)
    refine ⟨(algebraMap (PowerSeries K) (LaurentSeries K) (snf.a i))⁻¹ •
      (fun j => algebraMap (PowerSeries K) (LaurentSeries K) (wi j)), ?_⟩
    show (A.map (algebraMap (PowerSeries K) (LaurentSeries K))) *ᵥ _ = _
    rw [Matrix.mulVec_smul]
    funext j
    have hj : ((A.map (algebraMap (PowerSeries K) (LaurentSeries K))) *ᵥ
        (fun j => algebraMap (PowerSeries K) (LaurentSeries K) (wi j))) j =
        algebraMap (PowerSeries K) (LaurentSeries K) ((A *ᵥ wi) j) :=
      (RingHom.map_mulVec _ A wi j).symm
    rw [Pi.smul_apply, hj, hwi]
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    rw [← mul_assoc, inv_mul_cancel₀ hai, one_mul]
  have hliL : LinearIndependent (LaurentSeries K)
      (fun i : Fin k => fun j =>
        algebraMap (PowerSeries K) (LaurentSeries K) (snf.bM (snf.f i) j)) :=
    linearIndependent_algebraMap (snf.bM.linearIndependent.comp snf.f snf.f.injective)
  have hkle : k ≤ (A.map (algebraMap (PowerSeries K) (LaurentSeries K))).rank := by
    have hsub : LinearIndependent (LaurentSeries K)
        (fun i : Fin k => (⟨_, hmemL i⟩ :
          LinearMap.range (A.map (algebraMap (PowerSeries K) (LaurentSeries K))).mulVecLin)) := by
      apply LinearIndependent.of_comp
        (LinearMap.range (A.map (algebraMap (PowerSeries K) (LaurentSeries K))).mulVecLin).subtype
      exact hliL
    simpa [Matrix.rank] using hsub.fintype_card_le_finrank
  -- (F) modulo `s`, the image is spanned by the unit part of the diagonal
  have hspanle :
      LinearMap.range (A.map (PowerSeries.constantCoeff (R := K))).mulVecLin ≤
        Submodule.span K (Set.range fun i : {i : Fin k // IsUnit (snf.a i)} =>
          vecC (snf.bM (snf.f i))) := by
    rintro y ⟨z, rfl⟩
    have hz : (A.map (PowerSeries.constantCoeff (R := K))) *ᵥ z =
        vecC (A *ᵥ fun j => PowerSeries.C (z j)) := by
      funext i
      show _ = PowerSeries.constantCoeff ((A *ᵥ fun j => PowerSeries.C (z j)) i)
      have hcz : (PowerSeries.constantCoeff (R := K) : PowerSeries K → K) ∘
          (fun j => PowerSeries.C (z j)) = z := by
        funext j
        simp
      rw [RingHom.map_mulVec PowerSeries.constantCoeff A (fun j => PowerSeries.C (z j)) i, hcz]
    show (A.map (PowerSeries.constantCoeff (R := K))) *ᵥ z ∈ _
    rw [hz]
    obtain ⟨r, hr⟩ := hdecomp (A *ᵥ fun j => PowerSeries.C (z j))
      ⟨fun j => PowerSeries.C (z j), rfl⟩
    rw [hr, vecC_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [vecC_smul]
    by_cases hu : IsUnit (snf.a i)
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, hu⟩, rfl⟩)
    · rw [map_mul, constantCoeff_eq_zero_of_not_isUnit hu, mul_zero, zero_smul]
      exact Submodule.zero_mem _
  have hrankle : (A.map (PowerSeries.constantCoeff (R := K))).rank ≤
      Fintype.card {i : Fin k // IsUnit (snf.a i)} := by
    calc (A.map (PowerSeries.constantCoeff (R := K))).rank
        ≤ Module.finrank K (Submodule.span K (Set.range fun i : {i : Fin k // IsUnit (snf.a i)} =>
            vecC (snf.bM (snf.f i)))) := Submodule.finrank_mono hspanle
      _ ≤ Fintype.card {i : Fin k // IsUnit (snf.a i)} :=
          finrank_range_le_card _
  -- the squeeze: every diagonal entry is a unit
  have hallunit : ∀ i, IsUnit (snf.a i) := by
    have hcard : k ≤ (Finset.univ.filter fun i : Fin k => IsUnit (snf.a i)).card := by
      have := hkle.trans (le_of_eq hrank) |>.trans hrankle
      rwa [Fintype.card_subtype] at this
    have huniv : (Finset.univ.filter fun i : Fin k => IsUnit (snf.a i)) = Finset.univ :=
      Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
        (by simpa using hcard)
    intro i
    have := Finset.filter_eq_self.mp huniv i (Finset.mem_univ i)
    exact this
  -- the `bM (f i)` themselves lie in the image
  have hbMmem : ∀ i, snf.bM (snf.f i) ∈ LinearMap.range A.mulVecLin := by
    intro i
    obtain ⟨u, hu⟩ := hallunit i
    have h1 : (snf.bN i : Fin m → PowerSeries K) ∈ LinearMap.range A.mulVecLin := (snf.bN i).2
    have h2 : snf.bM (snf.f i) = (↑u⁻¹ : PowerSeries K) • (snf.bN i : Fin m → PowerSeries K) := by
      rw [snf.snf i, smul_smul, ← hu]
      simp
    rw [h2]
    exact Submodule.smul_mem _ _ h1
  -- (A) denominator clearing: some nonzero multiple of `b` is in the image
  obtain ⟨z, hz⟩ := hb
  obtain ⟨dd, hdd⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors (PowerSeries K)) z
  choose w hw using fun i => RingHom.mem_rangeS.mp (hdd i)
  have hdb : A *ᵥ w = (dd : PowerSeries K) • b := by
    funext i
    apply hinj
    rw [RingHom.map_mulVec (algebraMap (PowerSeries K) (LaurentSeries K)) A w i]
    have hwz : (algebraMap (PowerSeries K) (LaurentSeries K) :
          PowerSeries K → LaurentSeries K) ∘ w =
        algebraMap (PowerSeries K) (LaurentSeries K) (dd : PowerSeries K) • z := by
      funext j
      show algebraMap (PowerSeries K) (LaurentSeries K) (w j) = _
      rw [hw j]
      simp [Algebra.smul_def]
    rw [hwz, Matrix.mulVec_smul]
    have hzi : ((A.map (algebraMap (PowerSeries K) (LaurentSeries K))) *ᵥ z) i =
        algebraMap (PowerSeries K) (LaurentSeries K) (b i) := congrFun hz i
    rw [Pi.smul_apply, hzi, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul]
  -- (H) coordinates of `b` outside the range of `f` vanish
  have hddne : (dd : PowerSeries K) ≠ 0 := nonZeroDivisors.coe_ne_zero dd
  have hcoord : ∀ j : Fin m, j ∉ Set.range snf.f → snf.bM.repr b j = 0 := by
    intro j hj
    have hmem : (dd : PowerSeries K) • b ∈ LinearMap.range A.mulVecLin := ⟨w, hdb⟩
    have h0 := snf.repr_eq_zero_of_notMem_range ⟨_, hmem⟩ hj
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at h0
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h hddne
    · exact h
  -- assemble
  have hsum := snf.bM.sum_repr b
  rw [← hsum]
  refine Submodule.sum_mem _ fun j _ => ?_
  by_cases hj : j ∈ Set.range snf.f
  · obtain ⟨i, rfl⟩ := hj
    exact Submodule.smul_mem _ _ (hbMmem i)
  · rw [hcoord j hj, zero_smul]
    exact Submodule.zero_mem _

/-! ### The specialisation used by the arc layer -/

/-- Along a chain stratum the rank of every power is determined by the column
sequence (`finrank_ker_pow_of_inStratum`), so it is the same at the base point
and at the generic point of an arc. -/
theorem rank_pow_of_inStratum {F : Type*} [Field F] {p : ℕ} {T : Fin p → ℕ}
    {x : Matrix (Fin p) (Fin p) F} (h : inStratum T x) (c : ℕ) :
    (x ^ c).rank = p - (Finset.univ.filter fun i => T i ≤ c).card := by
  have heq : ((Matrix.toLinAlgEquiv' x) ^ c : Module.End F (Fin p → F)) = (x ^ c).mulVecLin := by
    rw [← map_pow]
    rfl
  have hker : Module.finrank F (LinearMap.ker ((x ^ c).mulVecLin)) =
      (Finset.univ.filter fun i => T i ≤ c).card := by
    rw [← finrank_ker_pow_of_inStratum h c, heq]
  have hrn := LinearMap.finrank_range_add_finrank_ker ((x ^ c).mulVecLin)
  rw [Module.finrank_fin_fun] at hrn
  have hrank : (x ^ c).rank = Module.finrank F (LinearMap.range ((x ^ c).mulVecLin)) := rfl
  omega

/-- Saturation in the form used by the transporter induction: along an arc whose
base point and generic point both lie in the stratum `A_T`, the incidence
equation `y_gen^{c-1} v_gen ∈ im y_gen^c` at the generic point already has a
solution over `K⟦s⟧`. -/
theorem exists_lift_of_arc {n : ℕ} (Y : Matrix (Fin n) (Fin n) (PowerSeries K))
    (v : Fin n → PowerSeries K) (T : Fin n → ℕ) (c : ℕ) (hc : 1 ≤ c)
    (hbase : inStratum T (matC Y))
    (hgen : inStratum T (Isotropy.toK (LaurentSeries K) Y))
    (hmem : Isotropy.toKv (LaurentSeries K) v ∈
      kernelRange (Matrix.toLinAlgEquiv' (Isotropy.toK (LaurentSeries K) Y)) c) :
    ∃ u : Fin n → PowerSeries K, (Y ^ c) *ᵥ u = (Y ^ (c - 1)) *ᵥ v := by
  have hpowL : (Y ^ c).map (algebraMap (PowerSeries K) (LaurentSeries K)) =
      (Isotropy.toK (LaurentSeries K) Y) ^ c := Isotropy.toK_pow Y c
  have hpowK : (Y ^ c).map (PowerSeries.constantCoeff (R := K)) = (matC Y) ^ c := matC_pow Y c
  have hrank : ((Y ^ c).map (algebraMap (PowerSeries K) (LaurentSeries K))).rank =
      ((Y ^ c).map (PowerSeries.constantCoeff (R := K))).rank := by
    rw [hpowL, hpowK, rank_pow_of_inStratum hgen c, rank_pow_of_inStratum hbase c]
  have hb : (fun i => algebraMap (PowerSeries K) (LaurentSeries K)
        (((Y ^ (c - 1)) *ᵥ v) i)) ∈
      LinearMap.range ((Y ^ c).map (algebraMap (PowerSeries K) (LaurentSeries K))).mulVecLin := by
    obtain ⟨z, hz⟩ := (pow_pred_mem_range_pow_iff_mem_kernelRange
      (Matrix.toLinAlgEquiv' (Isotropy.toK (LaurentSeries K) Y))
      (Isotropy.toKv (LaurentSeries K) v) c hc).mpr hmem
    refine ⟨z, ?_⟩
    have hz' : ((Isotropy.toK (LaurentSeries K) Y) ^ c) *ᵥ z =
        ((Isotropy.toK (LaurentSeries K) Y) ^ (c - 1)) *ᵥ
          (Isotropy.toKv (LaurentSeries K) v) := by
      have h1 : ((Matrix.toLinAlgEquiv' (Isotropy.toK (LaurentSeries K) Y)) ^ c) z =
          ((Isotropy.toK (LaurentSeries K) Y) ^ c) *ᵥ z := by
        rw [← map_pow]
        rfl
      have h2 : ((Matrix.toLinAlgEquiv' (Isotropy.toK (LaurentSeries K) Y)) ^ (c - 1))
            (Isotropy.toKv (LaurentSeries K) v) =
          ((Isotropy.toK (LaurentSeries K) Y) ^ (c - 1)) *ᵥ
            (Isotropy.toKv (LaurentSeries K) v) := by
        rw [← map_pow]
        rfl
      rw [← h1, ← h2, hz]
    show ((Y ^ c).map (algebraMap (PowerSeries K) (LaurentSeries K))) *ᵥ z = _
    rw [hpowL, hz', ← Isotropy.toK_pow, Isotropy.toK_mulVec]
  obtain ⟨u, hu⟩ := PowerSeries.range_saturated_of_rank_eq (Y ^ c) hrank hb
  exact ⟨u, hu⟩

end Saturation

end Height.Orbital
