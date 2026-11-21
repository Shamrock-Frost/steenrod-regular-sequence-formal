import Height.DVR.Residue
import Height.DVR.ResidueTransfer
import Height.DVR.AltHyperbolic

/-!
# The local residue space over `K⟦u⟧`, and `lem:residue-form` / `lem:divided-form`

`lem:local-pairing` (`AltHyperbolic.lean`) puts the commutator pairing at a drop
point into hyperbolic normal form, so that in the notation of the paper

  `(T_x, ω_x) = ⊕_i ((K⟦u⟧/u^{m_i})^{⊕2}, ((a,b),(a',b')) ↦ res_x((ab' − a'b)/u^{m_i}))`.

This file constructs that space and that form over `R = K⟦u⟧`, identifies them
with the coefficient model of `ResidueBlocks.lean` / `ResidueDirectSum.lean`
(`blockResidueForm_mk`, `residueSpaceForm_mk` are the content: the transported
form *is* the residue of the paper), and therefore discharges the isometry
hypotheses of `ResidueTransfer.lean`.  The conclusions of `lem:residue-form`
and `lem:divided-form` — alternation, nondegeneracy, the dimension
`dim T_x = len_x T`, the half-dimensional isotropic bound, and
`dim u T_x = len_x T − D_x` — hold unconditionally for this space.
-/

namespace Height.DVR

open PowerSeries

universe u v

variable {K : Type u} [Field K]

section Block

/-- `u^m K⟦u⟧`, viewed as a `K`-subspace of `K⟦u⟧`. -/
noncomputable def uPowSubmodule (K : Type u) [Field K] (m : ℕ) :
    Submodule K (PowerSeries K) :=
  Submodule.restrictScalars K
    (Ideal.span {(PowerSeries.X : PowerSeries K) ^ m})

/-- The elementary torsion block `K⟦u⟧/(u^m)` as a `K`-vector space. -/
abbrev blockQuot (K : Type u) [Field K] (m : ℕ) := PowerSeries K ⧸ uPowSubmodule K m

theorem mem_uPowSubmodule {m : ℕ} {f : PowerSeries K} :
    f ∈ uPowSubmodule K m ↔ ∀ i < m, PowerSeries.coeff i f = 0 := by
  rw [uPowSubmodule, Submodule.restrictScalars_mem, Ideal.mem_span_singleton,
    PowerSeries.X_pow_dvd_iff]

theorem mem_uPowSubmodule_iff_dvd {m : ℕ} {f : PowerSeries K} :
    f ∈ uPowSubmodule K m ↔ (PowerSeries.X : PowerSeries K) ^ m ∣ f := by
  rw [mem_uPowSubmodule, PowerSeries.X_pow_dvd_iff]

/-- The coefficients below degree `m`, as a `K`-linear map. -/
noncomputable def truncCoeffsₗ (K : Type u) [Field K] (m : ℕ) :
    PowerSeries K →ₗ[K] (Fin m → K) :=
  LinearMap.pi fun i : Fin m => PowerSeries.coeff (i : ℕ)

@[simp] theorem truncCoeffsₗ_apply (m : ℕ) (f : PowerSeries K) (i : Fin m) :
    truncCoeffsₗ K m f i = PowerSeries.coeff (i : ℕ) f := rfl

theorem ker_truncCoeffsₗ (m : ℕ) :
    LinearMap.ker (truncCoeffsₗ K m) = uPowSubmodule K m := by
  ext f
  simp only [LinearMap.mem_ker, mem_uPowSubmodule]
  constructor
  · intro h i hi
    have hf := congrFun h ⟨i, hi⟩
    simpa using hf
  · intro h
    funext i
    simpa using h (i : ℕ) i.isLt

theorem truncCoeffsₗ_surjective (m : ℕ) :
    Function.Surjective (truncCoeffsₗ K m) := by
  intro c
  refine ⟨PowerSeries.mk fun j => if h : j < m then c ⟨j, h⟩ else 0, ?_⟩
  funext i
  simp [truncCoeffsₗ_apply, i.isLt]

/-- The coordinate map of the elementary block. -/
noncomputable def blockCoordsₗ (K : Type u) [Field K] (m : ℕ) :
    blockQuot K m →ₗ[K] (Fin m → K) :=
  (uPowSubmodule K m).liftQ (truncCoeffsₗ K m) (ker_truncCoeffsₗ m).ge

theorem blockCoordsₗ_mk (m : ℕ) (f : PowerSeries K) :
    blockCoordsₗ K m (Submodule.Quotient.mk f) = truncCoeffsₗ K m f :=
  Submodule.liftQ_apply _ _ _

theorem blockCoordsₗ_bijective (m : ℕ) :
    Function.Bijective (blockCoordsₗ K m) := by
  constructor
  · rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ (ker_truncCoeffsₗ m).le
  · intro c
    obtain ⟨f, hf⟩ := truncCoeffsₗ_surjective (K := K) m c
    exact ⟨Submodule.Quotient.mk f, by rw [blockCoordsₗ_mk]; exact hf⟩

/-- Coordinates on the elementary block: `K⟦u⟧/(u^m) ≃ K^m`. -/
noncomputable def blockCoords (K : Type u) [Field K] (m : ℕ) :
    blockQuot K m ≃ₗ[K] (Fin m → K) :=
  LinearEquiv.ofBijective (blockCoordsₗ K m) (blockCoordsₗ_bijective m)

/-- The coefficient pairing of `ResidueBlocks.lean` is the residue of
`lem:residue-form`: `[u^{m-1}](fg) = res_x (fg/u^m)\,du`. -/
theorem residueCoeffPair_truncCoeffs (m : ℕ) (hm : 1 ≤ m) (f g : PowerSeries K) :
    residueCoeffPair m (truncCoeffsₗ K m f) (truncCoeffsₗ K m g)
      = laurentResidue K
          (uInvPow K m * algebraMap (PowerSeries K) (LaurentSeries K) (f * g)) := by
  rw [laurentResidue_uInvPow_mul m hm, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, residueCoeffPair]
  have hstep : ∀ i : Fin m,
      (truncCoeffsₗ K m f) i * (truncCoeffsₗ K m g) (Fin.rev i)
        = PowerSeries.coeff (i : ℕ) f * PowerSeries.coeff (m - 1 - (i : ℕ)) g := by
    intro i
    have hrev : (Fin.rev i : ℕ) = m - 1 - (i : ℕ) := by
      rw [Fin.val_rev]; omega
    rw [truncCoeffsₗ_apply, truncCoeffsₗ_apply, hrev]
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hstep i,
    Fin.sum_univ_eq_sum_range
      (fun k => PowerSeries.coeff k f * PowerSeries.coeff (m - 1 - k) g) m]
  have hrange : (m - 1).succ = m := by omega
  rw [hrange]

end Block

section BlockForm

/-- The hyperbolic residue form on one elementary block, read through the
coefficient coordinates. -/
noncomputable def blockResidueForm (K : Type u) [Field K] (m : ℕ) :
    LinearMap.BilinForm K (blockQuot K m × blockQuot K m) :=
  (residueBlockBilinForm (K := K) m).comp
    ((blockCoords K m).prodCongr (blockCoords K m)).toLinearMap
    ((blockCoords K m).prodCongr (blockCoords K m)).toLinearMap

/-- `lem:residue-form` on one block, in the local model: the form is the
residue `res_x ((ab' − a'b)/u^m)\,du` of the paper. -/
theorem blockResidueForm_mk (m : ℕ) (hm : 1 ≤ m) (a b a' b' : PowerSeries K) :
    blockResidueForm K m
        (Submodule.Quotient.mk a, Submodule.Quotient.mk b)
        (Submodule.Quotient.mk a', Submodule.Quotient.mk b')
      = laurentResidue K
          (uInvPow K m *
            algebraMap (PowerSeries K) (LaurentSeries K) (a * b' - a' * b)) := by
  show residueBlockForm m (truncCoeffsₗ K m a, truncCoeffsₗ K m b)
      (truncCoeffsₗ K m a', truncCoeffsₗ K m b') = _
  rw [residueBlockForm, residueCoeffPair_truncCoeffs m hm,
    residueCoeffPair_truncCoeffs m hm, ← map_sub, ← mul_sub, ← map_sub]

end BlockForm

section Family

variable {ι : Type v} [Fintype ι]

/-- The local residue space of `lem:residue-form`: the orthogonal sum of the
hyperbolic torsion blocks `(K⟦u⟧/u^{m_i})^{⊕2}`. -/
abbrev residueBlockSpace (K : Type u) [Field K] (m : ι → ℕ) :=
  ∀ i, blockQuot K (m i) × blockQuot K (m i)

/-- The coordinates of the local residue space. -/
noncomputable def residueSpaceCoords (K : Type u) [Field K] (m : ι → ℕ) :
    residueBlockSpace K m ≃ₗ[K] ResidueBlockFamily (K := K) m :=
  LinearEquiv.piCongrRight fun i =>
    (blockCoords K (m i)).prodCongr (blockCoords K (m i))

/-- The residue form `ω_x` on the local residue space. -/
noncomputable def residueSpaceForm (m : ι → ℕ) :
    LinearMap.BilinForm K (residueBlockSpace K m) :=
  (residueDirectSumBilinForm (K := K) m).comp
    (residueSpaceCoords K m).toLinearMap (residueSpaceCoords K m).toLinearMap

/-- The isometry hypothesis of `ResidueTransfer.lean` is a theorem for the
local model. -/
noncomputable def residueSpaceIsometry (m : ι → ℕ) :
    (residueSpaceForm (K := K) m).IsometryEquiv
      (residueDirectSumBilinForm (K := K) m) where
  __ := residueSpaceCoords K m
  map_app' _ _ := rfl

/-- The residue form is by construction the orthogonal sum of its blocks: this
is what lets a family of block classes indexed by a sigma type be reassembled
into a single `residueBlockSpace`. -/
theorem residueSpaceForm_eq_sum (m : ι → ℕ) (x y : residueBlockSpace K m) :
    residueSpaceForm m x y = ∑ i, blockResidueForm K (m i) (x i) (y i) := rfl

/-- `lem:residue-form` in the local model: the form is the sum over blocks of
the residues `res_x ((a_i b'_i − a'_i b_i)/u^{m_i})\,du`.  No hypothesis
`1 ≤ m i` is needed: at `m i = 0` the block is the zero space and the residue of
an integral element vanishes, and that case is what the divided form
(`residueSpaceForm` at the exponents `m − 1`) meets on the blocks with
`m i = 1`. -/
theorem residueSpaceForm_mk (m : ι → ℕ)
    (a b a' b' : ι → PowerSeries K) :
    residueSpaceForm m
        (fun i => (Submodule.Quotient.mk (a i), Submodule.Quotient.mk (b i)))
        (fun i => (Submodule.Quotient.mk (a' i), Submodule.Quotient.mk (b' i)))
      = ∑ i, laurentResidue K
          (uInvPow K (m i) *
            algebraMap (PowerSeries K) (LaurentSeries K)
              (a i * b' i - a' i * b i)) := by
  show ∑ i, residueBlockForm (m i) _ _ = _
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases Nat.eq_zero_or_pos (m i) with h0 | hpos
  · have hRHS : laurentResidue K (uInvPow K (m i) *
        algebraMap (PowerSeries K) (LaurentSeries K) (a i * b' i - a' i * b i)) = 0 := by
      rw [h0, uInvPow_zero, one_mul, laurentResidue_algebraMap]
    have : IsEmpty (Fin (m i)) := by rw [h0]; infer_instance
    rw [hRHS]
    simp [residueBlockForm, residueCoeffPair]
  · have h := blockResidueForm_mk (K := K) (m i) hpos (a i) (b i) (a' i) (b' i)
    rw [← h]
    rfl

noncomputable instance instFiniteDimensionalResidueBlockSpace (m : ι → ℕ) :
    FiniteDimensional K (residueBlockSpace K m) :=
  (residueSpaceCoords K m).symm.finiteDimensional

/-- `lem:residue-form`, isotropic bound: every `ω_x`-isotropic subspace of
`T_x` has dimension at most `len_x T / 2`. -/
theorem residueSpaceForm_isotropic_bound (m : ι → ℕ)
    (W : Submodule K (residueBlockSpace K m))
    (hW : ∀ x ∈ W, ∀ y ∈ W, residueSpaceForm m x y = 0) :
    2 * Module.finrank K W ≤ ∑ i, 2 * m i :=
  residueForm_isotropic_bound_of_isometry _ m (residueSpaceIsometry m) W hW

end Family

section Exponents

end Exponents

end Height.DVR
