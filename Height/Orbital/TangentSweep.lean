import Height.Orbital.Tangent
import Height.Orbital.Transporter
import Height.Toolbox.Sweep

/-!
# From the tangent equation to a centralizer correction

The differentiated lifting equation puts the residual last-column velocity in
`K_c(y)`.  The centralizer sweep equality then produces exactly the correction
term used in the transporter argument.  The sweep equality remains an explicit
hypothesis here, isolating its cyclic-decomposition proof from the elementary
matrix calculation; the last two results discharge it at the actual box
column, using the general sweep theorem `Height.Toolbox.sweep`.
-/

namespace Height.Orbital

open Matrix
open Height.Toolbox

variable {K : Type*} [Field K] {n : ℕ}

/-- The differentiated lifting equation places the residual velocity in the
kernel-range subspace `K_c(y)`. -/
theorem tangent_residual_mem_kernelRange
    (y dy γ : Matrix (Fin n) (Fin n) K)
    (u du v dv : Fin n → K) (c : ℕ) (hc : 1 ≤ c)
    (hdy : dy = γ * y - y * γ)
    (hbase : (y ^ c).mulVec u = (y ^ (c - 1)).mulVec v)
    (htangent :
      (Isotropy.dpow y dy (c - 1)).mulVec v + (y ^ (c - 1)).mulVec dv =
        (Isotropy.dpow y dy c).mulVec u + (y ^ c).mulVec du) :
    dv - γ.mulVec v ∈
      kernelRange (Matrix.toLinAlgEquiv' y) c := by
  apply (pow_pred_mem_range_pow_iff_mem_kernelRange
    (Matrix.toLinAlgEquiv' y) (dv - γ.mulVec v) c hc).mp
  refine ⟨du - γ.mulVec u, ?_⟩
  have h := tangent_equation y dy γ u du v dv c hdy hbase htangent
  simpa only [← map_pow, Matrix.toLinAlgEquiv'_apply] using h.symm

/-- Assuming the centralizer sweep equality at column `c`, the tangent
residual admits the correction required in the transporter construction. -/
theorem tangent_exists_endomorphism_correction
    (y dy γ : Matrix (Fin n) (Fin n) K)
    (u du v dv : Fin n → K) (c : ℕ) (hc : 1 ≤ c)
    (hdy : dy = γ * y - y * γ)
    (hbase : (y ^ c).mulVec u = (y ^ (c - 1)).mulVec v)
    (htangent :
      (Isotropy.dpow y dy (c - 1)).mulVec v + (y ^ (c - 1)).mulVec dv =
        (Isotropy.dpow y dy c).mulVec u + (y ^ c).mulVec du)
    (hsweep :
      sweepSpace (Matrix.toLinAlgEquiv' y) v =
        kernelRange (Matrix.toLinAlgEquiv' y) c) :
    ∃ (A : Module.End K (Fin n → K)) (z : Fin n → K),
      Commute A (Matrix.toLinAlgEquiv' y) ∧
        dv - γ.mulVec v = A v - Matrix.toLinAlgEquiv' y z := by
  apply (mem_sweepSpace_iff_sub (Matrix.toLinAlgEquiv' y) v
    (dv - γ.mulVec v)).mp
  rw [hsweep]
  exact tangent_residual_mem_kernelRange y dy γ u du v dv c hc hdy hbase htangent

/-- Matrix form of the centralizer correction extracted from the tangent
equation and the sweep equality. -/
theorem tangent_exists_matrix_correction
    (y dy γ : Matrix (Fin n) (Fin n) K)
    (u du v dv : Fin n → K) (c : ℕ) (hc : 1 ≤ c)
    (hdy : dy = γ * y - y * γ)
    (hbase : (y ^ c).mulVec u = (y ^ (c - 1)).mulVec v)
    (htangent :
      (Isotropy.dpow y dy (c - 1)).mulVec v + (y ^ (c - 1)).mulVec dv =
        (Isotropy.dpow y dy c).mulVec u + (y ^ c).mulVec du)
    (hsweep :
      sweepSpace (Matrix.toLinAlgEquiv' y) v =
        kernelRange (Matrix.toLinAlgEquiv' y) c) :
    ∃ (ζ : Matrix (Fin n) (Fin n) K) (z : Fin n → K),
      y * ζ = ζ * y ∧ dv - γ.mulVec v = ζ.mulVec v - y.mulVec z := by
  obtain ⟨A, z, hA, hz⟩ :=
    tangent_exists_endomorphism_correction y dy γ u du v dv c hc hdy
      hbase htangent hsweep
  let ζ := Matrix.toLinAlgEquiv'.symm A
  refine ⟨ζ, z, ?_, ?_⟩
  · have hcomm := congrArg Matrix.toLinAlgEquiv'.symm hA.eq
    simpa [ζ] using hcomm.symm
  · calc
      dv - γ.mulVec v = A v - y.mulVec z := hz
      _ = ζ.mulVec v - y.mulVec z := by
        congr 1
        symm
        change Matrix.toLinAlgEquiv' ζ v = A v
        dsimp only [ζ]
        rw [Matrix.toLinAlgEquiv'.apply_symm_apply]

/-- A centralizing correction turns the residual vector equation into the
block commutator representing the full tangent direction. -/
theorem blockTransporter_corrects_tangent
    (y dy γ ζ : Matrix (Fin n) (Fin n) K)
    (v dv z : Fin n → K)
    (hdy : dy = γ * y - y * γ)
    (hζ : y * ζ = ζ * y)
    (hcorr : dv - γ.mulVec v = ζ.mulVec v - y.mulVec z) :
    blockTransporter (γ + ζ) z * blockExtension y v -
        blockExtension y v * blockTransporter (γ + ζ) z =
      Matrix.fromBlocks dy (lastColumn dv) 0 0 := by
  have hdy' : (γ + ζ) * y - y * (γ + ζ) = dy := by
    rw [add_mul, mul_add, hζ]
    simpa only [add_sub_add_right_eq_sub] using hdy.symm
  have hdv' : (γ + ζ).mulVec v - y.mulVec z = dv := by
    calc
      (γ + ζ).mulVec v - y.mulVec z =
          γ.mulVec v + (ζ.mulVec v - y.mulVec z) := by
            rw [add_mulVec]
            abel
      _ = γ.mulVec v + (dv - γ.mulVec v) := by rw [← hcorr]
      _ = dv := by abel
  rw [transporter_commutator, hdy', hdv']

/-- Adding centralizing corrections to transporter representatives does not
change their lower-dimensional Kostant--Kirillov pairing. -/
theorem kkForm_add_centralizer_corrections
    (y γ₁ γ₂ ζ₁ ζ₂ : Matrix (Fin n) (Fin n) K)
    (hζ₁ : y * ζ₁ = ζ₁ * y)
    (hζ₂ : y * ζ₂ = ζ₂ * y) :
    kkForm y (γ₁ + ζ₁) (γ₂ + ζ₂) = kkForm y γ₁ γ₂ := by
  apply kk_wellDefined
  · rw [add_mul, mul_add, hζ₁]
    abel
  · rw [add_mul, mul_add, hζ₂]
    abel

/-- Two corrected block transporters inherit isotropy from their
lower-dimensional representatives. -/
theorem corrected_blockTransporters_isotropic
    (y dy₁ dy₂ γ₁ γ₂ ζ₁ ζ₂ : Matrix (Fin n) (Fin n) K)
    (v dv₁ dv₂ z₁ z₂ : Fin n → K)
    (hdy₁ : dy₁ = γ₁ * y - y * γ₁)
    (hdy₂ : dy₂ = γ₂ * y - y * γ₂)
    (hζ₁ : y * ζ₁ = ζ₁ * y)
    (hζ₂ : y * ζ₂ = ζ₂ * y)
    (hcorr₁ : dv₁ - γ₁.mulVec v = ζ₁.mulVec v - y.mulVec z₁)
    (hcorr₂ : dv₂ - γ₂.mulVec v = ζ₂.mulVec v - y.mulVec z₂)
    (hlower : kkForm y γ₁ γ₂ = 0) :
    blockTransporter (γ₁ + ζ₁) z₁ * blockExtension y v -
          blockExtension y v * blockTransporter (γ₁ + ζ₁) z₁ =
        Matrix.fromBlocks dy₁ (lastColumn dv₁) 0 0 ∧
      blockTransporter (γ₂ + ζ₂) z₂ * blockExtension y v -
          blockExtension y v * blockTransporter (γ₂ + ζ₂) z₂ =
        Matrix.fromBlocks dy₂ (lastColumn dv₂) 0 0 ∧
      kkForm (blockExtension y v)
          (blockTransporter (γ₁ + ζ₁) z₁)
          (blockTransporter (γ₂ + ζ₂) z₂) = 0 := by
  refine ⟨blockTransporter_corrects_tangent y dy₁ γ₁ ζ₁ v dv₁ z₁
      hdy₁ hζ₁ hcorr₁,
    blockTransporter_corrects_tangent y dy₂ γ₂ ζ₂ v dv₂ z₂
      hdy₂ hζ₂ hcorr₂, ?_⟩
  rw [kkForm_blockExtension_transporters,
    kkForm_add_centralizer_corrections y γ₁ γ₂ ζ₁ ζ₂ hζ₁ hζ₂,
    hlower]

/-- Conditional algebraic induction step for `prop:transporter`: two
differentiated lifts satisfying the same sweep hypothesis are represented by
full block transporters, and lower-dimensional isotropy implies their full
Kostant--Kirillov isotropy. -/
theorem tangent_pair_isotropic_of_sweep
    (y dy₁ dy₂ γ₁ γ₂ : Matrix (Fin n) (Fin n) K)
    (u₁ du₁ u₂ du₂ v dv₁ dv₂ : Fin n → K)
    (c : ℕ) (hc : 1 ≤ c)
    (hdy₁ : dy₁ = γ₁ * y - y * γ₁)
    (hdy₂ : dy₂ = γ₂ * y - y * γ₂)
    (hbase₁ : (y ^ c).mulVec u₁ = (y ^ (c - 1)).mulVec v)
    (hbase₂ : (y ^ c).mulVec u₂ = (y ^ (c - 1)).mulVec v)
    (htangent₁ :
      (Isotropy.dpow y dy₁ (c - 1)).mulVec v +
          (y ^ (c - 1)).mulVec dv₁ =
        (Isotropy.dpow y dy₁ c).mulVec u₁ + (y ^ c).mulVec du₁)
    (htangent₂ :
      (Isotropy.dpow y dy₂ (c - 1)).mulVec v +
          (y ^ (c - 1)).mulVec dv₂ =
        (Isotropy.dpow y dy₂ c).mulVec u₂ + (y ^ c).mulVec du₂)
    (hsweep :
      sweepSpace (Matrix.toLinAlgEquiv' y) v =
        kernelRange (Matrix.toLinAlgEquiv' y) c)
    (hlower : kkForm y γ₁ γ₂ = 0) :
    ∃ (ζ₁ ζ₂ : Matrix (Fin n) (Fin n) K) (z₁ z₂ : Fin n → K),
      y * ζ₁ = ζ₁ * y ∧ y * ζ₂ = ζ₂ * y ∧
      blockTransporter (γ₁ + ζ₁) z₁ * blockExtension y v -
            blockExtension y v * blockTransporter (γ₁ + ζ₁) z₁ =
          Matrix.fromBlocks dy₁ (lastColumn dv₁) 0 0 ∧
      blockTransporter (γ₂ + ζ₂) z₂ * blockExtension y v -
            blockExtension y v * blockTransporter (γ₂ + ζ₂) z₂ =
          Matrix.fromBlocks dy₂ (lastColumn dv₂) 0 0 ∧
      kkForm (blockExtension y v)
          (blockTransporter (γ₁ + ζ₁) z₁)
          (blockTransporter (γ₂ + ζ₂) z₂) = 0 := by
  obtain ⟨ζ₁, z₁, hζ₁, hcorr₁⟩ :=
    tangent_exists_matrix_correction y dy₁ γ₁ u₁ du₁ v dv₁ c hc
      hdy₁ hbase₁ htangent₁ hsweep
  obtain ⟨ζ₂, z₂, hζ₂, hcorr₂⟩ :=
    tangent_exists_matrix_correction y dy₂ γ₂ u₂ du₂ v dv₂ c hc
      hdy₂ hbase₂ htangent₂ hsweep
  obtain ⟨hfull₁, hfull₂, hiso⟩ :=
    corrected_blockTransporters_isotropic y dy₁ dy₂ γ₁ γ₂ ζ₁ ζ₂
      v dv₁ dv₂ z₁ z₂ hdy₁ hdy₂ hζ₁ hζ₂ hcorr₁ hcorr₂ hlower
  exact ⟨ζ₁, ζ₂, z₁, z₂, hζ₁, hζ₂, hfull₁, hfull₂, hiso⟩

/-- Intrinsic-box-column form of the algebraic transporter induction.  This
is the form used when `c` is defined from the chain tableau rather than
carried with a separate minimality hypothesis. -/
theorem tangent_pair_isotropic_at_boxColumn
    (y dy₁ dy₂ γ₁ γ₂ : Matrix (Fin n) (Fin n) K)
    (u₁ du₁ u₂ du₂ v dv₁ dv₂ : Fin n → K)
    (c : ℕ) (hy : IsNilpotent (Matrix.toLinAlgEquiv' y))
    (hc : c = boxColumn (Matrix.toLinAlgEquiv' y) v hy)
    (hdy₁ : dy₁ = γ₁ * y - y * γ₁)
    (hdy₂ : dy₂ = γ₂ * y - y * γ₂)
    (hbase₁ : (y ^ c).mulVec u₁ = (y ^ (c - 1)).mulVec v)
    (hbase₂ : (y ^ c).mulVec u₂ = (y ^ (c - 1)).mulVec v)
    (htangent₁ :
      (Isotropy.dpow y dy₁ (c - 1)).mulVec v +
          (y ^ (c - 1)).mulVec dv₁ =
        (Isotropy.dpow y dy₁ c).mulVec u₁ + (y ^ c).mulVec du₁)
    (htangent₂ :
      (Isotropy.dpow y dy₂ (c - 1)).mulVec v +
          (y ^ (c - 1)).mulVec dv₂ =
        (Isotropy.dpow y dy₂ c).mulVec u₂ + (y ^ c).mulVec du₂)
    (hlower : kkForm y γ₁ γ₂ = 0) :
    ∃ (ζ₁ ζ₂ : Matrix (Fin n) (Fin n) K) (z₁ z₂ : Fin n → K),
      y * ζ₁ = ζ₁ * y ∧ y * ζ₂ = ζ₂ * y ∧
      blockTransporter (γ₁ + ζ₁) z₁ * blockExtension y v -
            blockExtension y v * blockTransporter (γ₁ + ζ₁) z₁ =
          Matrix.fromBlocks dy₁ (lastColumn dv₁) 0 0 ∧
      blockTransporter (γ₂ + ζ₂) z₂ * blockExtension y v -
            blockExtension y v * blockTransporter (γ₂ + ζ₂) z₂ =
          Matrix.fromBlocks dy₂ (lastColumn dv₂) 0 0 ∧
      kkForm (blockExtension y v)
          (blockTransporter (γ₁ + ζ₁) z₁)
          (blockTransporter (γ₂ + ζ₂) z₂) = 0 := by
  have hcpos : 1 ≤ c := by
    rw [hc]
    exact (boxColumn_spec (Matrix.toLinAlgEquiv' y) v hy).1
  have hsweep := sweep_at_boxColumn (Matrix.toLinAlgEquiv' y) v hy
  rw [← hc] at hsweep
  exact tangent_pair_isotropic_of_sweep y dy₁ dy₂ γ₁ γ₂
    u₁ du₁ u₂ du₂ v dv₁ dv₂ c hcpos hdy₁ hdy₂ hbase₁ hbase₂
      htangent₁ htangent₂ hsweep hlower

end Height.Orbital
