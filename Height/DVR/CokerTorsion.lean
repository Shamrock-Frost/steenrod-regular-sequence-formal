import Height.DVR.SmithUnique
import Height.Toolbox.BaseChange

/-!
# The torsion of a cokernel over `K⟦u⟧` (`lem:selfdual-degree`, step 5)

For a matrix `A` over `R = K⟦u⟧` with Smith diagonalisation `U · A · V = diagonal g`,
the torsion submodule of `coker A` is `sat (im A) / im A` and has `K`-dimension
`∑ᵢ ord (gᵢ)`.  This is `finrank_quot_comap_eq_sum_order`, stated through an
injective `Θ` with `range Θ = sat (im A)` so that it applies verbatim to a
presentation of the saturation by a free module — which is how `C^⊥` presents
`sat (im ad_P)` in `Pencil/SelfDual.lean`.

The mechanism: after the change of basis `U` the saturation is `{z | gᵢ = 0 → zᵢ = 0}`
and the image is `{z | gᵢ ∣ zᵢ}`, so on the saturation membership of the image is
`u^{ord gᵢ} ∣ zᵢ` coordinatewise (`dvd_iff_X_pow_order_dvd`, and vacuous where
`gᵢ = 0`).  The quotient is therefore cut out by `truncPi K (fun i => ord gᵢ)`.
-/

namespace Height.DVR

open Matrix PowerSeries Height.Toolbox

universe u v

section Torsion

variable {K : Type u} [Field K] {ι : Type v} [Fintype ι] [DecidableEq ι]

/-- After the change of basis `U`, the image of `A` is the image of the diagonal
matrix. -/
theorem mem_range_mulVec_U {A U V : Matrix ι ι (PowerSeries K)} {g : ι → PowerSeries K}
    (hU : IsUnit U.det) (hV : IsUnit V.det) (hdiag : U * A * V = Matrix.diagonal g)
    (y : ι → PowerSeries K) :
    y ∈ LinearMap.range A.mulVecLin ↔
      U *ᵥ y ∈ LinearMap.range (Matrix.diagonal g).mulVecLin := by
  have hUA : U * A = Matrix.diagonal g * V⁻¹ := by
    rw [← hdiag, Matrix.mul_assoc, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hV, Matrix.mul_one]
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨V⁻¹ *ᵥ z, ?_⟩
    show Matrix.diagonal g *ᵥ (V⁻¹ *ᵥ z) = U *ᵥ (A *ᵥ z)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hUA]
  · rintro ⟨w, hw⟩
    refine ⟨V *ᵥ w, ?_⟩
    show A *ᵥ (V *ᵥ w) = y
    have h1 : U *ᵥ (A *ᵥ (V *ᵥ w)) = U *ᵥ y := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hdiag]
      exact hw
    have hinjU : Function.Injective fun x : ι → PowerSeries K => U *ᵥ x := by
      intro s t hst
      have h2 := congrArg (fun x => U⁻¹ *ᵥ x) hst
      simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hU, Matrix.one_mulVec] using h2
    exact hinjU h1

theorem mem_satOf_range_mulVec_U {A U V : Matrix ι ι (PowerSeries K)} {g : ι → PowerSeries K}
    (hU : IsUnit U.det) (hV : IsUnit V.det) (hdiag : U * A * V = Matrix.diagonal g)
    (y : ι → PowerSeries K) :
    y ∈ satOf (LinearMap.range A.mulVecLin) ↔
      U *ᵥ y ∈ satOf (LinearMap.range (Matrix.diagonal g).mulVecLin) := by
  constructor
  · rintro ⟨f, hf, hfy⟩
    refine ⟨f, hf, ?_⟩
    rw [← Matrix.mulVec_smul]
    exact (mem_range_mulVec_U hU hV hdiag _).1 hfy
  · rintro ⟨f, hf, hfy⟩
    refine ⟨f, hf, (mem_range_mulVec_U hU hV hdiag _).2 ?_⟩
    rwa [Matrix.mulVec_smul]

/-- A free coordinate of the diagonal matrix vanishes on the saturation. -/
theorem eq_zero_of_mem_satOf_diagonal {g z : ι → PowerSeries K}
    (hz : z ∈ satOf (LinearMap.range (Matrix.diagonal g).mulVecLin)) {i : ι} (hg : g i = 0) :
    z i = 0 := by
  obtain ⟨f, hf, hfz⟩ := hz
  have h := (mem_range_mulVecLin_diagonal.1 hfz) i
  rw [hg, zero_dvd_iff, Pi.smul_apply, smul_eq_mul] at h
  exact (mul_eq_zero.mp h).resolve_left hf

/-- On the saturation, membership of the image of the diagonal matrix is
coordinatewise divisibility by `u^{ord gᵢ}` -- vacuous where `gᵢ = 0`. -/
theorem mem_range_diagonal_iff_X_pow_dvd {g z : ι → PowerSeries K} {m : ι → ℕ}
    (hm : ∀ i, m i = (g i).order.toNat) (hz : ∀ i, g i = 0 → z i = 0) :
    z ∈ LinearMap.range (Matrix.diagonal g).mulVecLin ↔
      ∀ i, (X : PowerSeries K) ^ m i ∣ z i := by
  rw [mem_range_mulVecLin_diagonal]
  refine forall_congr' fun i => ?_
  rw [hm i]
  by_cases hgi : g i = 0
  · rw [hgi, hz i hgi]
    simp
  · exact dvd_iff_X_pow_order_dvd hgi _

/-- **The torsion of the cokernel.**  If `Θ` is an injective presentation of the
saturation of the image of `A`, then the quotient of the free module by the
preimage of the image of `A` has `K`-dimension `∑ᵢ ord (gᵢ)` for any Smith
diagonalisation `U · A · V = diagonal g`. -/
theorem finrank_quot_comap_eq_sum_order {r : ℕ} {A U V : Matrix ι ι (PowerSeries K)}
    {g : ι → PowerSeries K} (hU : IsUnit U.det) (hV : IsUnit V.det)
    (hdiag : U * A * V = Matrix.diagonal g)
    (Θ : (Fin r → PowerSeries K) →ₗ[PowerSeries K] (ι → PowerSeries K))
    (hrange : LinearMap.range Θ = satOf (LinearMap.range A.mulVecLin)) :
    Module.finrank K ((Fin r → PowerSeries K) ⧸
        Submodule.comap Θ (LinearMap.range A.mulVecLin))
      = ∑ i, (g i).order.toNat := by
  classical
  set m : ι → ℕ := fun i => (g i).order.toNat with hm
  set Φ : (Fin r → PowerSeries K) →ₗ[PowerSeries K] (ι → PowerSeries K) :=
    U.mulVecLin.comp Θ with hΦ
  set π : (Fin r → PowerSeries K) →ₗ[K] ((i : ι) → Fin (m i) → K) :=
    (truncPi K m).comp (Φ.restrictScalars K) with hπ
  -- every value of `Θ` lands in the saturation, where the two descriptions agree
  have hzero : ∀ x : Fin r → PowerSeries K, ∀ i, g i = 0 → (U *ᵥ Θ x) i = 0 := by
    intro x i hgi
    refine eq_zero_of_mem_satOf_diagonal ?_ hgi
    refine (mem_satOf_range_mulVec_U hU hV hdiag _).1 ?_
    rw [← hrange]
    exact ⟨x, rfl⟩
  have hker : LinearMap.ker π
      = (Submodule.comap Θ (LinearMap.range A.mulVecLin)).restrictScalars K := by
    ext x
    have h1 : π x = 0 ↔ (U *ᵥ Θ x) ∈ LinearMap.ker (truncPi K m) := Iff.rfl
    show π x = 0 ↔ Θ x ∈ LinearMap.range A.mulVecLin
    rw [mem_range_mulVec_U hU hV hdiag, h1, mem_ker_truncPi,
      ← mem_range_diagonal_iff_X_pow_dvd (fun i => rfl) (hzero x)]
  have hsurj : Function.Surjective π := by
    intro c
    obtain ⟨w, hw⟩ := truncPi_surjective (K := K) m c
    set z : ι → PowerSeries K := fun i => if g i = 0 then 0 else w i with hz
    have hztr : truncPi K m z = c := by
      rw [← hw]
      funext i j
      by_cases hgi : g i = 0
      · have hmi : m i = 0 := by simp [hm, hgi]
        exact absurd j.2 (by omega)
      · show truncCoeffsₗ K (m i) (z i) j = truncCoeffsₗ K (m i) (w i) j
        rw [hz]
        simp [hgi]
    have hzsat : z ∈ satOf (LinearMap.range (Matrix.diagonal g).mulVecLin) := by
      refine ⟨∏ i, (if g i = 0 then 1 else g i), ?_, ?_⟩
      · refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
        by_cases hgi : g i = 0
        · simp [hgi]
        · rw [ite_eq_right hgi]
          exact hgi
      · refine mem_range_mulVecLin_diagonal.2 fun i => ?_
        by_cases hgi : g i = 0
        · simp [hz, hgi]
        · refine Dvd.dvd.mul_right ?_ _
          have h := Finset.dvd_prod_of_mem (fun i => if g i = 0 then 1 else g i)
            (Finset.mem_univ i)
          rwa [ite_eq_right hgi] at h
    have hymem : U⁻¹ *ᵥ z ∈ LinearMap.range Θ := by
      rw [hrange]
      refine (mem_satOf_range_mulVec_U hU hV hdiag _).2 ?_
      rwa [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hU, Matrix.one_mulVec]
    obtain ⟨x, hx⟩ := hymem
    refine ⟨x, ?_⟩
    show truncPi K m (U *ᵥ Θ x) = c
    rw [hx, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hU, Matrix.one_mulVec, hztr]
  have hfin := (LinearMap.quotKerEquivOfSurjective π hsurj).finrank_eq
  rw [hker] at hfin
  rw [← (Submodule.Quotient.restrictScalarsEquiv K
    (Submodule.comap Θ (LinearMap.range A.mulVecLin))).finrank_eq, hfin,
    Module.finrank_pi_fintype]
  exact Finset.sum_congr rfl fun i _ => Module.finrank_fin_fun K

end Torsion

end Height.DVR
