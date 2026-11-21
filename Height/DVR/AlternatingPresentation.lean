import Height.DVR.AltInvariantFactors
import Height.DVR.ResidueModel
import Height.DVR.ResidueForm
import Height.DVR.CokerTorsion
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# `AlternatingPresentation`: the Smith datum of an alternating matrix over `K⟦u⟧`

## What this file is for

A *raw* Smith datum for an alternating matrix `A` over `K⟦u⟧` (for `ad_P`,
`A = adMat P`) is two change-of-basis matrices `U`, `V`, invariant factors
`g : Fin m → K⟦u⟧` and the conditions relating them.  Every use of such a datum
needs two further properties: that it is compatible with the ambient pairing
(self-duality) and that the invariant factors are honest powers of the
uniformiser (normalisation).

`AlternatingPresentation K m σ A` is such a datum **self-dual and normalised
by construction**:

* the right change of basis is not a field but the *definition* `dualMat σ U`
  (`V a b = U (blockInvol b) (σ a)`), so self-duality is `rfl` (`V_apply`);
* the invariant factors are not a field but the *definition*
  `normFactor K m e = hypRow (u^{e ·})`, so normalisation is
  `g_eq_X_pow_mExp`, the pairing `g (blockInvol i) = -g i` is
  `hypRow_blockInvol`, and the fixed-point condition is
  `blockInvol_ne_of_hypRow_ne_zero` — none of them fields.

Two data fields (`U`, `e`) and two proof fields (`hU`, `hdiag`) remain.

## The two involutions

`σ : Equiv.Perm (Fin m)` is the *duality* of the ambient pairing: `A` is
alternating for `(x, y) ↦ x ⬝ᵥ (A *ᵥ y)` read through `σ`, i.e.
`IsAltMatrix (Aᵀ.submatrix id σ)`.  For `A = adMat P` and `σ = swapIdx n` this
is `Pencil.gramMat_isAlt`, and `x ⬝ᵥ ((adMat P) *ᵥ (y ∘ σ))` is
`trace ([P, X] Y)` in the standard basis of `gl_n`.

`blockInvol : Equiv.Perm (Fin m)` (`AltInvariantFactors.lean`) is the *block*
involution pairing the two coordinates of each hyperbolic block; it is a
property of the normal form, not of `A`.

## Indexing

The coordinates, the exponent bookkeeping (`mExp`), the blocks (`Blocks`, a
subtype of `Fin m`) and the free indices (`Frees`) are indexed by `Fin m`; only
the exponent field `e` is indexed by `ℕ`, the block index of `hypNF`/`hypRow`,
which is what makes the pairing of the invariant factors hold by construction
rather than by a field.  `mExp_eq_toNat_e` is the agreement of `mExp` with `e`
on the even representatives; off `[0, m)` the field `e` is junk-valued, as
`hypNF`'s block data is.
-/

namespace Height.DVR

open Matrix PowerSeries

universe u v

/-! ### Normalised invariant factors -/

section NormalisedFactors

variable {K : Type u} [Field K]

/-- `u^e` for `e : ℕ∞`, with the convention `u^⊤ = 0`: the normalised
invariant factor of order `e` in `K⟦u⟧`.  `⊤` is the free (rank-defect) case,
where the invariant factor vanishes. -/
noncomputable def uOrdPow (K : Type u) [Field K] (e : ℕ∞) : PowerSeries K :=
  if e = ⊤ then 0 else (PowerSeries.X : PowerSeries K) ^ e.toNat

/-- The normalised invariant factors of a hyperbolic presentation with block
exponents `e`: `u^{e k}` on the even representative of the `k`-th block and its
negative on the partner (`hypRow`). -/
noncomputable def normFactor (K : Type u) [Field K] (m : ℕ) (e : ℕ → ℕ∞) :
    Fin m → PowerSeries K :=
  hypRow (n := m) fun k => uOrdPow K (e k)

@[simp] theorem uOrdPow_top : uOrdPow K ⊤ = 0 := ite_eq_left rfl

@[simp] theorem uOrdPow_natCast (k : ℕ) :
    uOrdPow K (k : ℕ∞) = (PowerSeries.X : PowerSeries K) ^ k := by
  rw [uOrdPow, ite_eq_right (by simp), ENat.toNat_natCast]

/-- The order of `u^e` is `e`; with `order 0 = ⊤` this covers the free case. -/
@[simp] theorem order_uOrdPow (e : ℕ∞) : (uOrdPow K e).order = e := by
  induction e using ENat.recTopCoe with
  | top => rw [uOrdPow_top, PowerSeries.order_zero]
  | coe k => rw [uOrdPow_natCast, PowerSeries.order_X_pow]

/-- The normalised factors pair up under `blockInvol`. -/
theorem normFactor_blockInvol {m : ℕ} (e : ℕ → ℕ∞) (i : Fin m) :
    normFactor K m e (blockInvol i) = -normFactor K m e i :=
  hypRow_blockInvol _ i

/-- The block involution has no fixed point where the factor is nonzero. -/
theorem blockInvol_ne_of_normFactor_ne_zero {m : ℕ} (e : ℕ → ℕ∞) {i : Fin m}
    (h : normFactor K m e i ≠ 0) : blockInvol i ≠ i :=
  blockInvol_ne_of_hypRow_ne_zero _ i h

/-- On an even representative the factor is the honest power `u^{e k}`, with no
unit. -/
theorem normFactor_of_even {m : ℕ} (e : ℕ → ℕ∞) {i : Fin m}
    (h : Even ((i : ℕ) + m)) :
    normFactor K m e i = uOrdPow K (e (i : ℕ)) := by
  rw [normFactor, hypRow, ite_eq_left h]

end NormalisedFactors

/-! ### The dual change of basis -/

section DualMat

variable {R : Type u} {m : ℕ}

/-- The right change of basis determined by the left one and the duality `σ`:
`dualMat σ U a b = U (blockInvol b) (σ a)`.  Self-duality of the Smith datum
is this *definition*. -/
def dualMat (σ : Equiv.Perm (Fin m)) (U : Matrix (Fin m) (Fin m) R) :
    Matrix (Fin m) (Fin m) R :=
  Uᵀ.submatrix σ blockInvol

@[simp] theorem dualMat_apply (σ : Equiv.Perm (Fin m))
    (U : Matrix (Fin m) (Fin m) R) (a b : Fin m) :
    dualMat σ U a b = U (blockInvol b) (σ a) := rfl

/-- The dual change of basis is invertible when the original one is: it is the
transpose reindexed by two permutations. -/
theorem isUnit_det_dualMat [CommRing R] {σ : Equiv.Perm (Fin m)}
    {U : Matrix (Fin m) (Fin m) R} (hU : IsUnit U.det) :
    IsUnit (dualMat σ U).det := by
  have hsign : ∀ τ : Equiv.Perm (Fin m), IsUnit ((Equiv.Perm.sign τ : ℤ) : R) := by
    intro τ
    rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h <;> rw [h] <;> simp
  have hsplit : dualMat σ U = (Uᵀ.submatrix σ id).submatrix id blockInvol := rfl
  rw [hsplit, Matrix.det_permute', Matrix.det_permute, Matrix.det_transpose]
  exact (hsign _).mul ((hsign _).mul hU)

end DualMat

/-! ### The presentation -/

/-- A **Smith presentation of an alternating matrix over `K⟦u⟧`**, self-dual and
normalised by construction.

`A` is alternating for the `σ`-twisted pairing (`IsAltMatrix (Aᵀ.submatrix id σ)`;
for `A = adMat P`, `σ = swapIdx n` this is `Pencil.gramMat_isAlt`).  The
presentation records a left change of basis `U` and the block exponents `e`; the
right change of basis is `dualMat σ U` and the invariant factors are
`normFactor K m e`, so that

* **self-duality** `V a b = U (blockInvol b) (σ a)` (`V_apply`) and
* **normalisation** `g i = u^{m_i}` on the even representatives
  (`g_eq_X_pow_mExp`)

hold by construction rather than as hypotheses. -/
structure AlternatingPresentation (K : Type u) [Field K] (m : ℕ)
    (σ : Equiv.Perm (Fin m)) (A : Matrix (Fin m) (Fin m) (PowerSeries K)) where
  /-- The left change of basis. -/
  U : Matrix (Fin m) (Fin m) (PowerSeries K)
  /-- The left change of basis is invertible. -/
  hU : IsUnit U.det
  /-- The exponent of the `k`-th hyperbolic block, `⊤` on the free blocks. -/
  e : ℕ → ℕ∞
  /-- The diagonalisation.  Both the right factor `dualMat σ U` and the
  invariant factors `normFactor K m e` are determined by `U` and `e`. -/
  hdiag : U * A * dualMat σ U = Matrix.diagonal (normFactor K m e)

namespace AlternatingPresentation

variable {K : Type u} [Field K] {m : ℕ} {σ : Equiv.Perm (Fin m)}
  {A : Matrix (Fin m) (Fin m) (PowerSeries K)}

/-! #### The derived Smith datum -/

/-- The right change of basis. -/
def V (p : AlternatingPresentation K m σ A) : Matrix (Fin m) (Fin m) (PowerSeries K) :=
  dualMat σ p.U

/-- **Self-duality, by construction.** -/
theorem V_apply (p : AlternatingPresentation K m σ A) (a b : Fin m) :
    p.V a b = p.U (blockInvol b) (σ a) := rfl

/-- The invariant factors. -/
noncomputable def g (p : AlternatingPresentation K m σ A) : Fin m → PowerSeries K :=
  normFactor K m p.e

/-- The right change of basis is invertible. -/
theorem hV (p : AlternatingPresentation K m σ A) : IsUnit p.V.det :=
  isUnit_det_dualMat p.hU

/-- `hdiag` spelled with the derived names. -/
theorem hdiag_V (p : AlternatingPresentation K m σ A) :
    p.U * A * p.V = Matrix.diagonal p.g := p.hdiag

/-- The invariant factors pair up under `blockInvol`. -/
theorem g_blockInvol (p : AlternatingPresentation K m σ A) (i : Fin m) :
    p.g (blockInvol i) = -p.g i :=
  normFactor_blockInvol p.e i

/-- The block involution has no fixed point where the invariant factor is
nonzero. -/
theorem blockInvol_ne (p : AlternatingPresentation K m σ A) {i : Fin m}
    (h : p.g i ≠ 0) : blockInvol i ≠ i :=
  blockInvol_ne_of_normFactor_ne_zero p.e h

/-- The valuation of the `i`-th invariant factor (`0` at the free indices). -/
noncomputable def mExp (p : AlternatingPresentation K m σ A) (i : Fin m) : ℕ :=
  (p.g i).order.toNat

/-- On the even representatives the exponent bookkeeping is the field `e`
itself; `mExp_blockInvol` transports this to the partners. -/
theorem mExp_eq_toNat_e (p : AlternatingPresentation K m σ A) {i : Fin m}
    (hev : Even ((i : ℕ) + m)) : p.mExp i = (p.e (i : ℕ)).toNat := by
  rw [mExp, g, normFactor_of_even p.e hev, order_uOrdPow]

/-- The exponent is `0` where the invariant factor vanishes. -/
theorem mExp_of_g_eq_zero (p : AlternatingPresentation K m σ A) {i : Fin m}
    (h : p.g i = 0) : p.mExp i = 0 := by
  simp [mExp, h]

/-- A positive exponent means a nonzero invariant factor. -/
theorem g_ne_zero_of_one_le_mExp (p : AlternatingPresentation K m σ A) {i : Fin m}
    (h : 1 ≤ p.mExp i) : p.g i ≠ 0 := by
  intro hz
  rw [p.mExp_of_g_eq_zero hz] at h
  exact absurd h (by omega)

/-- The exponent is invariant under `blockInvol`. -/
theorem mExp_blockInvol (p : AlternatingPresentation K m σ A) (i : Fin m) :
    p.mExp (blockInvol i) = p.mExp i := by
  rw [mExp, mExp, p.g_blockInvol i, PowerSeries.order_neg]

/-- **Normalisation, by construction.** -/
theorem g_eq_X_pow_mExp (p : AlternatingPresentation K m σ A) {i : Fin m}
    (hev : Even ((i : ℕ) + m)) (hne : p.g i ≠ 0) :
    p.g i = (PowerSeries.X : PowerSeries K) ^ p.mExp i := by
  have hval : p.g i = uOrdPow K (p.e (i : ℕ)) := normFactor_of_even p.e hev
  have hne' : p.e (i : ℕ) ≠ ⊤ := fun hc => hne (by rw [hval, hc, uOrdPow_top])
  rw [p.mExp_eq_toNat_e hev, hval, uOrdPow, ite_eq_right hne']

/-- Normalisation on the odd representative: `g (blockInvol b) = -u^{m_b}`. -/
theorem g_blockInvol_eq_neg_X_pow_mExp (p : AlternatingPresentation K m σ A)
    {i : Fin m} (hev : Even ((i : ℕ) + m)) (hne : p.g i ≠ 0) :
    p.g (blockInvol i) = -(PowerSeries.X : PowerSeries K) ^ p.mExp i := by
  rw [p.g_blockInvol i, p.g_eq_X_pow_mExp hev hne]

/-- A nonzero invariant factor is a unit times `u^{mExp i}`: the general
power-series fact `exists_unit_mul_X_pow`, in the form `Pencil/Marked.lean`
calls. -/
theorem exists_unit_mul_pow (p : AlternatingPresentation K m σ A) {i : Fin m}
    (h : p.g i ≠ 0) :
    ∃ v : (PowerSeries K)ˣ,
      p.g i = (v : PowerSeries K) * (PowerSeries.X : PowerSeries K) ^ p.mExp i :=
  exists_unit_mul_X_pow h

/-- Divisibility by a nonzero invariant factor is divisibility by `u^{mExp i}`. -/
theorem dvd_iff_X_pow_dvd (p : AlternatingPresentation K m σ A) {i : Fin m}
    (h : p.g i ≠ 0) (c : PowerSeries K) :
    p.g i ∣ c ↔ (PowerSeries.X : PowerSeries K) ^ p.mExp i ∣ c :=
  dvd_iff_X_pow_order_dvd h c

/-! #### Blocks and free indices -/

/-- The hyperbolic blocks of the torsion: one representative of each
`blockInvol`-pair carrying a nontrivial invariant factor. -/
def Blocks (p : AlternatingPresentation K m σ A) : Type :=
  {i : Fin m // Even ((i : ℕ) + m) ∧ 1 ≤ p.mExp i}

instance instFiniteBlocks (p : AlternatingPresentation K m σ A) : Finite p.Blocks := by
  show Finite {i : Fin m // Even ((i : ℕ) + m) ∧ 1 ≤ p.mExp i}
  infer_instance

noncomputable instance instFintypeBlocks (p : AlternatingPresentation K m σ A) :
    Fintype p.Blocks := Fintype.ofFinite _

/-- The exponents of the hyperbolic blocks. -/
noncomputable def mBlk (p : AlternatingPresentation K m σ A) (b : p.Blocks) : ℕ :=
  p.mExp b.val

/-- The free coordinates: the indices where the invariant factor vanishes. -/
def Frees (p : AlternatingPresentation K m σ A) : Type := {i : Fin m // p.g i = 0}

/-- `T_x`, the local torsion model. -/
@[reducible] noncomputable def torsion (p : AlternatingPresentation K m σ A) : Type u :=
  residueBlockSpace K p.mBlk

/-- `u T_x`, the divided torsion model. -/
@[reducible] noncomputable def dividedTorsion (p : AlternatingPresentation K m σ A) :
    Type u :=
  residueBlockSpace K fun b => p.mBlk b - 1

/-! #### The class map, in vector coordinates

`Pencil/Local.lean` composes these with `vecMat` to get the class map of a
matrix direction (`LocalData.coords`, `LocalData.blockClass`,
`LocalData.freeClass`, `LocalData.cls`). -/

/-- The Smith coordinates of a vector: `U · x`. -/
noncomputable def coordsOfL (p : AlternatingPresentation K m σ A) :
    (Fin m → PowerSeries K) →ₗ[PowerSeries K] (Fin m → PowerSeries K) :=
  p.U.mulVecLin

/-- The Smith coordinates as a `K`-linear map. -/
noncomputable def coordsOfK (p : AlternatingPresentation K m σ A) :
    (Fin m → PowerSeries K) →ₗ[K] (Fin m → PowerSeries K) :=
  p.coordsOfL.restrictScalars K

/-- The block coordinates of a vector, at arbitrary exponents. -/
noncomputable def blockClassOf (p : AlternatingPresentation K m σ A)
    (e : p.Blocks → ℕ) :
    (Fin m → PowerSeries K) →ₗ[K] residueBlockSpace K e :=
  LinearMap.pi fun b : p.Blocks =>
    LinearMap.prod
      ((uPowSubmodule K (e b)).mkQ ∘ₗ LinearMap.proj b.val ∘ₗ p.coordsOfK)
      ((uPowSubmodule K (e b)).mkQ ∘ₗ LinearMap.proj (blockInvol b.val) ∘ₗ p.coordsOfK)

@[simp] theorem blockClassOf_apply (p : AlternatingPresentation K m σ A)
    (e : p.Blocks → ℕ) (x : Fin m → PowerSeries K) (b : p.Blocks) :
    p.blockClassOf e x b =
      (Submodule.Quotient.mk (p.coordsOfL x b.val),
        Submodule.Quotient.mk (p.coordsOfL x (blockInvol b.val))) := rfl

/-- The free coordinates of a vector. -/
noncomputable def freeClassOf (p : AlternatingPresentation K m σ A) :
    (Fin m → PowerSeries K) →ₗ[K] (p.Frees → PowerSeries K) :=
  LinearMap.pi fun i : p.Frees => LinearMap.proj i.val ∘ₗ p.coordsOfK

@[simp] theorem freeClassOf_apply (p : AlternatingPresentation K m σ A)
    (x : Fin m → PowerSeries K) (i : p.Frees) :
    p.freeClassOf x i = p.coordsOfL x i.val := rfl

/-- The class map: the torsion classes together with the free coordinates. -/
noncomputable def clsOf (p : AlternatingPresentation K m σ A) :
    (Fin m → PowerSeries K) →ₗ[K] p.torsion × (p.Frees → PowerSeries K) :=
  LinearMap.prod (p.blockClassOf p.mBlk) p.freeClassOf

/-! #### The Smith-form criterion -/

/-- Divisibility of the Smith coordinates by the invariant factors is exactly
membership of the image.  (For `A = adMat P` and `x = vecMat Q`, membership of
the image says that `Q` is a commutator `P * B - B * P`.) -/
theorem dvd_coordsOf_iff_mem_range (p : AlternatingPresentation K m σ A)
    (x : Fin m → PowerSeries K) :
    (∀ i, p.g i ∣ p.coordsOfL x i) ↔ x ∈ LinearMap.range A.mulVecLin :=
  (mem_range_mulVecLin_diagonal (g := p.g) (x := p.U *ᵥ x)).symm.trans
    (mem_range_mulVec_U p.hU p.hV p.hdiag_V x).symm

/-- **The class map detects the image.** -/
theorem clsOf_eq_zero_iff (p : AlternatingPresentation K m σ A)
    (x : Fin m → PowerSeries K) :
    p.clsOf x = 0 ↔ x ∈ LinearMap.range A.mulVecLin := by
  rw [← p.dvd_coordsOf_iff_mem_range x]
  constructor
  · intro h
    have h1 : p.blockClassOf p.mBlk x = 0 := congrArg Prod.fst h
    have h2 : p.freeClassOf x = 0 := congrArg Prod.snd h
    have hblk : ∀ b : p.Blocks,
        (PowerSeries.X : PowerSeries K) ^ p.mBlk b ∣ p.coordsOfL x b.val ∧
          (PowerSeries.X : PowerSeries K) ^ p.mBlk b ∣
            p.coordsOfL x (blockInvol b.val) := by
      intro b
      have hb := congrFun h1 b
      rw [blockClassOf_apply] at hb
      have hb1 : (Submodule.Quotient.mk (p.coordsOfL x b.val) :
          PowerSeries K ⧸ uPowSubmodule K (p.mBlk b)) = 0 := congrArg Prod.fst hb
      have hb2 : (Submodule.Quotient.mk (p.coordsOfL x (blockInvol b.val)) :
          PowerSeries K ⧸ uPowSubmodule K (p.mBlk b)) = 0 := congrArg Prod.snd hb
      exact ⟨mem_uPowSubmodule_iff_dvd.mp ((Submodule.Quotient.mk_eq_zero _).mp hb1),
        mem_uPowSubmodule_iff_dvd.mp ((Submodule.Quotient.mk_eq_zero _).mp hb2)⟩
    have hfree : ∀ i : p.Frees, p.coordsOfL x i.val = 0 := by
      intro i
      have hi := congrFun h2 i
      rwa [freeClassOf_apply] at hi
    intro i
    by_cases hg : p.g i = 0
    · rw [hg, zero_dvd_iff]
      exact hfree ⟨i, hg⟩
    rw [p.dvd_iff_X_pow_dvd hg]
    rcases Nat.eq_zero_or_pos (p.mExp i) with hm | hm
    · simp [hm]
    by_cases hev : Even ((i : ℕ) + m)
    · exact (hblk ⟨i, hev, hm⟩).1
    · have hne : blockInvol i ≠ i := p.blockInvol_ne hg
      have hi0 : (i : ℕ) ≠ 0 := by
        intro h0
        exact hne (by rw [blockInvol_apply]; exact blockInvolFun_of_odd_zero hev h0)
      have hval : ((blockInvol i : Fin m) : ℕ) = (i : ℕ) - 1 := by
        rw [blockInvol_apply]
        exact blockInvolFun_of_odd_pos hev hi0
      have hev' : Even (((blockInvol i : Fin m) : ℕ) + m) := by
        rw [hval]
        have hi := i.isLt
        rw [Nat.even_iff] at hev ⊢
        omega
      have hm' : 1 ≤ p.mExp (blockInvol i) := by rw [p.mExp_blockInvol]; exact hm
      have hb := (hblk ⟨blockInvol i, hev', hm'⟩).2
      rw [show ((⟨blockInvol i, hev', hm'⟩ : p.Blocks) : Fin m) = blockInvol i from rfl,
        blockInvol_involutive] at hb
      have hmm : p.mBlk ⟨blockInvol i, hev', hm'⟩ = p.mExp i := p.mExp_blockInvol i
      rwa [hmm] at hb
  · intro hdvd
    have hfree : ∀ i : p.Frees, p.coordsOfL x i.val = 0 := by
      intro i
      have hi := hdvd i.val
      rw [i.2] at hi
      exact zero_dvd_iff.mp hi
    have hblk : ∀ b : p.Blocks, p.blockClassOf p.mBlk x b = 0 := by
      intro b
      have hgb : p.g b.val ≠ 0 := p.g_ne_zero_of_one_le_mExp b.2.2
      have hgb' : p.g (blockInvol b.val) ≠ 0 := by
        rw [p.g_blockInvol]
        simpa using hgb
      have h1 : (PowerSeries.X : PowerSeries K) ^ p.mBlk b ∣ p.coordsOfL x b.val :=
        (p.dvd_iff_X_pow_dvd hgb _).mp (hdvd b.val)
      have h2 : (PowerSeries.X : PowerSeries K) ^ p.mBlk b ∣
          p.coordsOfL x (blockInvol b.val) := by
        have h2' := (p.dvd_iff_X_pow_dvd hgb' _).mp (hdvd (blockInvol b.val))
        rwa [p.mExp_blockInvol] at h2'
      rw [blockClassOf_apply]
      refine Prod.ext_iff.mpr ⟨?_, ?_⟩
      · exact (Submodule.Quotient.mk_eq_zero _).mpr (mem_uPowSubmodule_iff_dvd.mpr h1)
      · exact (Submodule.Quotient.mk_eq_zero _).mpr (mem_uPowSubmodule_iff_dvd.mpr h2)
    refine Prod.ext_iff.mpr ⟨?_, ?_⟩
    · show p.blockClassOf p.mBlk x = 0
      funext b
      exact hblk b
    · show p.freeClassOf x = 0
      funext i
      rw [freeClassOf_apply]
      exact hfree i

/-! #### The divided criterion -/

/-- The block classes at exponents `e` vanish exactly when the Smith
coordinates of both members of each block are divisible by `u^{e b}`.  This is
the divisibility bookkeeping inside `clsOf_eq_zero_iff`, at arbitrary
exponents. -/
theorem blockClassOf_eq_zero_iff (p : AlternatingPresentation K m σ A)
    (e : p.Blocks → ℕ) (x : Fin m → PowerSeries K) :
    p.blockClassOf e x = 0 ↔ ∀ b : p.Blocks,
      (PowerSeries.X : PowerSeries K) ^ e b ∣ p.coordsOfL x b.val ∧
        (PowerSeries.X : PowerSeries K) ^ e b ∣ p.coordsOfL x (blockInvol b.val) := by
  constructor
  · intro h b
    have hb := congrFun h b
    rw [blockClassOf_apply] at hb
    have hb1 : (Submodule.Quotient.mk (p.coordsOfL x b.val) :
        PowerSeries K ⧸ uPowSubmodule K (e b)) = 0 := congrArg Prod.fst hb
    have hb2 : (Submodule.Quotient.mk (p.coordsOfL x (blockInvol b.val)) :
        PowerSeries K ⧸ uPowSubmodule K (e b)) = 0 := congrArg Prod.snd hb
    exact ⟨mem_uPowSubmodule_iff_dvd.mp ((Submodule.Quotient.mk_eq_zero _).mp hb1),
      mem_uPowSubmodule_iff_dvd.mp ((Submodule.Quotient.mk_eq_zero _).mp hb2)⟩
  · intro h
    funext b
    rw [blockClassOf_apply]
    exact Prod.ext_iff.mpr
      ⟨(Submodule.Quotient.mk_eq_zero _).mpr (mem_uPowSubmodule_iff_dvd.mpr (h b).1),
        (Submodule.Quotient.mk_eq_zero _).mpr (mem_uPowSubmodule_iff_dvd.mpr (h b).2)⟩

/-- **The divided criterion.**  Reading `x` at the *lowered* exponents
`m_b − 1` sees exactly what reading `u · x` at `m_b` sees.

Every block has `1 ≤ m_b`, so the single power of the uniformiser cancels in
the Smith coordinates — `K⟦u⟧` is a domain — and no information is lost either
way.  This is the model form of `lem:marked-shift`: `Pencil/Marked.lean` reads
a shifted representative `Ṙ = u S` at the exponents `m − 1`, and the two
consequences the paper draws from `μ_x = [Q̇] + ṫ c₀` both come from here. -/
theorem blockClassOf_pred_eq_zero_iff (p : AlternatingPresentation K m σ A)
    (x : Fin m → PowerSeries K) :
    p.blockClassOf (fun b => p.mBlk b - 1) x = 0
      ↔ p.blockClassOf p.mBlk ((PowerSeries.X : PowerSeries K) • x) = 0 := by
  have hcoord : ∀ i, p.coordsOfL ((PowerSeries.X : PowerSeries K) • x) i
      = (PowerSeries.X : PowerSeries K) * p.coordsOfL x i := by
    intro i; rw [map_smul]; rfl
  have hcancel : ∀ (b : p.Blocks) (c : PowerSeries K),
      ((PowerSeries.X : PowerSeries K) ^ (p.mBlk b - 1) ∣ c
        ↔ (PowerSeries.X : PowerSeries K) ^ p.mBlk b
            ∣ (PowerSeries.X : PowerSeries K) * c) := by
    intro b c
    obtain ⟨k, hk⟩ : ∃ k, p.mBlk b = k + 1 := ⟨p.mBlk b - 1, by
      have h1 : 1 ≤ p.mBlk b := b.2.2
      omega⟩
    rw [hk]
    simp only [Nat.add_sub_cancel, pow_succ, mul_comm _ (PowerSeries.X : PowerSeries K)]
    exact (mul_dvd_mul_iff_left (PowerSeries.X_ne_zero (R := K))).symm
  rw [p.blockClassOf_eq_zero_iff, p.blockClassOf_eq_zero_iff]
  simp only [hcoord, ← hcancel]

/-- **The divided vanishing criterion.**  If `u · x` lies in the image of `A`,
then all block classes of `x` at the lowered exponents `m_b − 1` vanish: two
marking witnesses change `Ṙ` by a commutator, i.e. change `u S` by an element
of the image, and the divided torsion cannot see that. -/
theorem blockClassOf_pred_eq_zero (p : AlternatingPresentation K m σ A)
    (x : Fin m → PowerSeries K)
    (hx : (PowerSeries.X : PowerSeries K) • x ∈ LinearMap.range A.mulVecLin) :
    p.blockClassOf (fun b => p.mBlk b - 1) x = 0 :=
  (p.blockClassOf_pred_eq_zero_iff x).mpr (congrArg Prod.fst ((p.clsOf_eq_zero_iff _).mpr hx))

/-! #### Summing over the hyperbolic blocks -/

/-- A function vanishing off the torsion indices is summed pair by pair over
the blocks: the indices with `1 ≤ mExp` are exactly `Blocks ⊔ blockInvol Blocks`. -/
theorem sum_eq_sum_blocks {M : Type*} [AddCommMonoid M]
    (p : AlternatingPresentation K m σ A) (F : Fin m → M)
    (hF : ∀ a, p.mExp a = 0 → F a = 0) :
    ∑ a : Fin m, F a = ∑ b : p.Blocks, (F b.val + F (blockInvol b.val)) := by
  classical
  set q : Fin m → Prop := fun a => Even ((a : ℕ) + m) ∧ 1 ≤ p.mExp a with hq
  set B : Finset (Fin m) := Finset.univ.filter q with hBdef
  set S : Finset (Fin m) := Finset.univ.filter (fun a => 1 ≤ p.mExp a) with hSdef
  have hodd : ∀ a : Fin m, Even ((a : ℕ) + m) →
      ¬ Even (((blockInvol a : Fin m) : ℕ) + m) := by
    intro a ha
    rw [blockInvol_apply, blockInvolFun_of_even ha]
    rw [Nat.even_iff] at ha ⊢
    omega
  have heven : ∀ a : Fin m, ¬ Even ((a : ℕ) + m) → (a : ℕ) ≠ 0 →
      Even (((blockInvol a : Fin m) : ℕ) + m) := by
    intro a ha h0
    rw [blockInvol_apply, blockInvolFun_of_odd_pos ha h0]
    have := a.isLt
    rw [Nat.even_iff] at ha ⊢
    omega
  have hne : ∀ a : Fin m, 1 ≤ p.mExp a → blockInvol a ≠ a := fun a ha =>
    p.blockInvol_ne (p.g_ne_zero_of_one_le_mExp ha)
  have hzero : ∀ a ∈ (Finset.univ : Finset (Fin m)), a ∉ S → F a = 0 := by
    intro a _ ha
    refine hF a ?_
    simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at ha
    omega
  have h1 : ∑ a : Fin m, F a = ∑ a ∈ S, F a :=
    (Finset.sum_subset (Finset.subset_univ S) hzero).symm
  have hBS : B ⊆ S := by
    intro a ha
    simp only [hBdef, hq, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ha.2
  have himS : B.image blockInvol ⊆ S := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    simp only [hBdef, hq, Finset.mem_filter, Finset.mem_univ, true_and] at hb
    simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [p.mExp_blockInvol]
    exact hb.2
  have hdisj : Disjoint B (B.image blockInvol) := by
    rw [Finset.disjoint_right]
    intro a ha haB
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    simp only [hBdef, hq, Finset.mem_filter, Finset.mem_univ, true_and] at hb haB
    exact hodd b hb.1 haB.1
  have hunion : S = B ∪ B.image blockInvol := by
    refine Finset.Subset.antisymm ?_ (Finset.union_subset hBS himS)
    intro a ha
    simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    by_cases hev : Even ((a : ℕ) + m)
    · exact Finset.mem_union_left _ (by
        simp only [hBdef, hq, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hev, ha⟩)
    · have h0 : (a : ℕ) ≠ 0 := by
        intro hc
        exact hne a ha (by rw [blockInvol_apply]; exact blockInvolFun_of_odd_zero hev hc)
      refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨blockInvol a, ?_, ?_⟩)
      · simp only [hBdef, hq, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨heven a hev h0, by rw [p.mExp_blockInvol]; exact ha⟩
      · exact blockInvol_involutive a
  have h2 : ∑ a ∈ S, F a = ∑ a ∈ B, F a + ∑ a ∈ B, F (blockInvol a) := by
    rw [hunion, Finset.sum_union hdisj]
    congr 1
    exact Finset.sum_image fun x _ y _ h => (blockInvol (n := m)).injective h
  have h3 : ∑ a ∈ B, F a + ∑ a ∈ B, F (blockInvol a)
      = ∑ a ∈ B, (F a + F (blockInvol a)) := (Finset.sum_add_distrib).symm
  have h4 : ∑ a ∈ B, (F a + F (blockInvol a))
      = ∑ b : p.Blocks, (F b.val + F (blockInvol b.val)) :=
    Finset.sum_subtype B (fun x => by simp [hBdef, hq]) _
  rw [h1, h2, h3, h4]

/-- The number of torsion indices is twice the number of blocks — the rank
defect `D_x`. -/
theorem card_filter_mExp (p : AlternatingPresentation K m σ A) :
    (Finset.univ.filter fun a : Fin m => 1 ≤ p.mExp a).card
      = 2 * Fintype.card p.Blocks := by
  classical
  have h := p.sum_eq_sum_blocks (M := ℕ) (fun a => if 1 ≤ p.mExp a then 1 else 0)
    (fun a ha => by simp [ha])
  rw [Finset.card_filter]
  rw [h, Finset.sum_congr rfl fun b (_ : b ∈ Finset.univ) => ?_,
    Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
  rw [ite_eq_left b.2.2, p.mExp_blockInvol, ite_eq_left b.2.2]

/-- **The length.**  The total block length is the sum of the valuations of the
invariant factors.  (`Pencil.lenX` and
`Pencil/SelfDual.finrank_localQuot_eq_lenX` use it.) -/
theorem sum_two_mBlk (p : AlternatingPresentation K m σ A) :
    ∑ b : p.Blocks, 2 * p.mBlk b = ∑ a : Fin m, p.mExp a := by
  rw [p.sum_eq_sum_blocks (M := ℕ) p.mExp fun a ha => ha]
  exact Finset.sum_congr rfl fun b _ => by
    rw [p.mExp_blockInvol]
    show 2 * p.mExp b.val = _
    ring

/-! #### Rank and the rank defect -/

/-- The rank of a specialisation is the number of invariant factors that
survive it. -/
theorem rank_map (p : AlternatingPresentation K m σ A) {F : Type v} [Field F]
    [DecidableEq F] (φ : PowerSeries K →+* F) :
    (A.map φ).rank = Nat.card {i : Fin m // φ (p.g i) ≠ 0} := by
  have hdetU : (p.U.map (φ : PowerSeries K → F)).det = φ p.U.det :=
    (RingHom.map_det φ p.U).symm
  have hdetV : (p.V.map (φ : PowerSeries K → F)).det = φ p.V.det :=
    (RingHom.map_det φ p.V).symm
  have hUφ : IsUnit (p.U.map (φ : PowerSeries K → F)).det := by
    rw [hdetU]; exact p.hU.map φ
  have hVφ : IsUnit (p.V.map (φ : PowerSeries K → F)).det := by
    rw [hdetV]; exact p.hV.map φ
  have hdiag : p.U.map φ * A.map φ * p.V.map φ
      = Matrix.diagonal fun i => φ (p.g i) := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, p.hdiag_V, Matrix.diagonal_map (map_zero φ)]
  have hrank : (A.map φ).rank = (Matrix.diagonal fun i => φ (p.g i)).rank := by
    rw [← hdiag, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hVφ,
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ hUφ]
  rw [hrank, Matrix.rank_diagonal, Nat.card_eq_fintype_card]

/-- **The rank defect.**  Twice the number of blocks is the drop in the rank of
`A` between the generic fibre (over `K⸨u⸩`) and the special fibre (over the
residue field `K`).  (`Pencil.DX_add_rank` uses it.) -/
theorem two_card_blocks_add_rank (p : AlternatingPresentation K m σ A) :
    2 * Fintype.card p.Blocks + (A.map (PowerSeries.constantCoeff (R := K))).rank
      = (A.map (algebraMap (PowerSeries K) (LaurentSeries K))).rank := by
  classical
  rw [p.rank_map (algebraMap (PowerSeries K) (LaurentSeries K)),
    p.rank_map (PowerSeries.constantCoeff (R := K)), Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card, Fintype.card_subtype, Fintype.card_subtype,
    ← p.card_filter_mExp]
  have hgen : (Finset.univ.filter fun i : Fin m =>
      algebraMap (PowerSeries K) (LaurentSeries K) (p.g i) ≠ 0)
      = Finset.univ.filter fun i : Fin m => p.g i ≠ 0 := by
    refine Finset.filter_congr fun i _ => ?_
    constructor
    · intro h hc
      exact h (by rw [hc, map_zero])
    · intro h hc
      refine h (IsFractionRing.injective (PowerSeries K) (LaurentSeries K) ?_)
      rw [map_zero]
      exact hc
  have hspec : (Finset.univ.filter fun i : Fin m =>
      PowerSeries.constantCoeff (p.g i) ≠ 0)
      = Finset.univ.filter fun i : Fin m => p.g i ≠ 0 ∧ p.mExp i = 0 := by
    refine Finset.filter_congr fun i _ => ?_
    constructor
    · intro h
      have hne : p.g i ≠ 0 := fun hc => h (by rw [hc, map_zero])
      refine ⟨hne, ?_⟩
      have h0 : (p.g i).order = 0 := by
        by_contra hc
        exact h (PowerSeries.order_ne_zero_iff_constCoeff_eq_zero.mp hc)
      rw [mExp, h0]
      rfl
    · rintro ⟨hne, hm⟩
      intro hc
      have h1 : (p.g i).order ≠ ⊤ := fun hcc => hne (PowerSeries.order_eq_top.mp hcc)
      have h2 : (p.g i).order = 0 := by
        rw [mExp] at hm
        exact (ENat.toNat_eq_zero.mp hm).resolve_right h1
      exact (PowerSeries.order_ne_zero_iff_constCoeff_eq_zero.mpr hc) h2
  rw [hgen, hspec]
  have hdisj : Disjoint (Finset.univ.filter fun i : Fin m => 1 ≤ p.mExp i)
      (Finset.univ.filter fun i : Fin m => p.g i ≠ 0 ∧ p.mExp i = 0) := by
    rw [Finset.disjoint_left]
    intro a ha ha'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ha'
    omega
  have hunion : (Finset.univ.filter fun i : Fin m => 1 ≤ p.mExp i)
      ∪ (Finset.univ.filter fun i : Fin m => p.g i ≠ 0 ∧ p.mExp i = 0)
      = Finset.univ.filter fun i : Fin m => p.g i ≠ 0 := by
    ext a
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (h | h)
      · exact p.g_ne_zero_of_one_le_mExp h
      · exact h.1
    · intro h
      rcases Nat.eq_zero_or_pos (p.mExp a) with hm | hm
      · exact Or.inr ⟨h, hm⟩
      · exact Or.inl hm
  rw [← hunion, Finset.card_union_of_disjoint hdisj]

/-! #### The torsion of the cokernel -/

/-- The `K`-dimension of the torsion of `coker A` is the length: for an
injective presentation `Θ` of the saturation of the image,
`dim ((K⟦u⟧)^r / Θ⁻¹ (im A)) = ∑_b 2 m_b`.  This is
`finrank_quot_comap_eq_sum_order` (`DVR/CokerTorsion.lean`) in the shape the
presentation gives. -/
theorem finrank_quot_comap_eq_sum_two_mBlk (p : AlternatingPresentation K m σ A)
    {r : ℕ} (Θ : (Fin r → PowerSeries K) →ₗ[PowerSeries K] (Fin m → PowerSeries K))
    (hrange : LinearMap.range Θ = Height.Toolbox.satOf (LinearMap.range A.mulVecLin)) :
    Module.finrank K ((Fin r → PowerSeries K) ⧸
        Submodule.comap Θ (LinearMap.range A.mulVecLin))
      = ∑ b : p.Blocks, 2 * p.mBlk b := by
  rw [p.sum_two_mBlk]
  exact finrank_quot_comap_eq_sum_order p.hU p.hV p.hdiag_V Θ hrange

/-! #### Laurent coordinates and the residue form

`Pencil/Torsion.lean` states these for matrix directions `Q` and transporters
`A₁` over `K⸨u⸩` through `trace (A₁ Q₂) = ∑ a, vecMat A₁ a · vecMat Q₂ (σ a)`
(`Pencil.trace_mul_eq_sum_vecMat`).  Here they are in vector coordinates, where
they are statements about `U`, `V = dualMat σ U` and `g` alone. -/

/-- If `x` is in the image of `A` over `K⸨u⸩`, its Smith coordinates are `g`
times the coordinates of a preimage; in particular the free coordinates of `x`
vanish. -/
theorem exists_coordsOf_eq_mul (p : AlternatingPresentation K m σ A)
    (x : Fin m → PowerSeries K) (w : Fin m → LaurentSeries K)
    (hw : A.map (algebraMap (PowerSeries K) (LaurentSeries K)) *ᵥ w
      = fun i => algebraMap (PowerSeries K) (LaurentSeries K) (x i)) :
    ∃ y : Fin m → LaurentSeries K,
      p.V.map (algebraMap (PowerSeries K) (LaurentSeries K)) *ᵥ y = w ∧
      ∀ a, algebraMap (PowerSeries K) (LaurentSeries K) (p.coordsOfL x a)
        = algebraMap (PowerSeries K) (LaurentSeries K) (p.g a) * y a := by
  set φ := algebraMap (PowerSeries K) (LaurentSeries K) with hφ
  refine ⟨p.V⁻¹.map φ *ᵥ w, ?_, ?_⟩
  · rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ p.hV]
    simp
  · intro a
    have hVw : p.V.map φ *ᵥ (p.V⁻¹.map φ *ᵥ w) = w := by
      rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ p.hV]
      simp
    have key : p.U.map φ *ᵥ (fun i => φ (x i))
        = (Matrix.diagonal p.g).map φ *ᵥ (p.V⁻¹.map φ *ᵥ w) := by
      rw [← p.hdiag_V, Matrix.map_mul, Matrix.map_mul, ← Matrix.mulVec_mulVec,
        ← Matrix.mulVec_mulVec, hVw, ← hw]
    have hlhs : (p.U.map φ *ᵥ fun i => φ (x i)) a = φ (p.coordsOfL x a) :=
      (RingHom.map_mulVec φ p.U x a).symm
    have hrhs := congrFun key a
    rw [hlhs, Matrix.diagonal_map (map_zero φ), Matrix.mulVec_diagonal] at hrhs
    exact hrhs

/-- **Self-duality in use.**  The `σ`-twisted pairing is read off the Smith
coordinates: `∑ a, w a · x (σ a) = ∑ a, y a · coords x (blockInvol a)` whenever
`V · y = w`.  (The self-duality it uses is `V_apply`, true by `rfl`.) -/
theorem pairing_eq_sum_coordsOf (p : AlternatingPresentation K m σ A)
    (w y : Fin m → LaurentSeries K)
    (hy : p.V.map (algebraMap (PowerSeries K) (LaurentSeries K)) *ᵥ y = w)
    (x : Fin m → PowerSeries K) :
    ∑ a : Fin m, w a * algebraMap (PowerSeries K) (LaurentSeries K) (x (σ a))
      = ∑ a : Fin m, y a *
          algebraMap (PowerSeries K) (LaurentSeries K)
            (p.coordsOfL x (blockInvol a)) := by
  set φ := algebraMap (PowerSeries K) (LaurentSeries K) with hφ
  calc ∑ a : Fin m, w a * φ (x (σ a))
      = ∑ a : Fin m, ∑ b : Fin m, y b * (φ (p.V a b) * φ (x (σ a))) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← hy]
        show (∑ b, (p.V.map φ) a b * y b) * _ = _
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun b _ => by rw [Matrix.map_apply]; ring
    _ = ∑ b : Fin m, ∑ a : Fin m, y b * (φ (p.V a b) * φ (x (σ a))) := Finset.sum_comm
    _ = ∑ b : Fin m, y b * φ (p.coordsOfL x (blockInvol b)) := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [← Finset.mul_sum]
        congr 1
        have h1 : ∀ a : Fin m, φ (p.V a b) * φ (x (σ a))
            = φ (p.U (blockInvol b) (σ a) * x (σ a)) := by
          intro a
          rw [map_mul, p.V_apply a b]
        rw [Finset.sum_congr rfl fun a (_ : a ∈ Finset.univ) => h1 a, ← map_sum]
        congr 1
        exact Equiv.sum_comp σ fun c => p.U (blockInvol b) c * x c

/-- **`lem:residue-form` and `lem:divided-form`, evaluation on representatives.**
For two vectors `x_i = u^k · s_i` in the image of `A` over `K⸨u⸩`, the residue
form of `DVR/ResidueModel.lean` at the exponents `m − k`, applied to the block
classes of the `s_i`, is the residue of `u^{-k}` times the `σ`-twisted pairing
of `w₁` and `x₂`.

`k = 0` is `lem:residue-form` (`Pencil.LocalData.omega_eq_residue`) and `k = 1`
is `lem:divided-form` (`Pencil/Marked.lean` states that case separately as
`LocalData.dividedForm_eq_residue`).  `hk` is what
makes `k ≤ m_b` on every block, `1 ≤ m_b` holding by definition of `Blocks`.

Both membership hypotheses are needed: `hw₂` is what makes the free coordinates
of `x₂` vanish, and without it the residue sees the non-torsion part of the
class of `x₂` in `coker A`, which the block space does not record. -/
theorem residueSpaceForm_blockClassOf (p : AlternatingPresentation K m σ A)
    (k : ℕ) (hk : k ≤ 1) (x₁ x₂ s₁ s₂ : Fin m → PowerSeries K)
    (hs₁ : (PowerSeries.X : PowerSeries K) ^ k • s₁ = x₁)
    (hs₂ : (PowerSeries.X : PowerSeries K) ^ k • s₂ = x₂)
    (w₁ w₂ : Fin m → LaurentSeries K)
    (hw₁ : A.map (algebraMap (PowerSeries K) (LaurentSeries K)) *ᵥ w₁
      = fun i => algebraMap (PowerSeries K) (LaurentSeries K) (x₁ i))
    (hw₂ : A.map (algebraMap (PowerSeries K) (LaurentSeries K)) *ᵥ w₂
      = fun i => algebraMap (PowerSeries K) (LaurentSeries K) (x₂ i)) :
    residueSpaceForm (fun b => p.mBlk b - k)
        (p.blockClassOf (fun b => p.mBlk b - k) s₁)
        (p.blockClassOf (fun b => p.mBlk b - k) s₂)
      = laurentResidue K (uInvPow K k * ∑ a : Fin m,
          w₁ a * algebraMap (PowerSeries K) (LaurentSeries K) (x₂ (σ a))) := by
  classical
  set φ := algebraMap (PowerSeries K) (LaurentSeries K) with hφ
  obtain ⟨y₁, hy₁, hc₁⟩ := p.exists_coordsOf_eq_mul x₁ w₁ hw₁
  obtain ⟨y₂, hy₂, hc₂⟩ := p.exists_coordsOf_eq_mul x₂ w₂ hw₂
  -- the coordinates of `x` are `u^k` times those of `s`
  have hcX : ∀ x s : Fin m → PowerSeries K,
      (PowerSeries.X : PowerSeries K) ^ k • s = x →
      ∀ a, p.coordsOfL x a = PowerSeries.X ^ k * p.coordsOfL s a := by
    intro x s hx a
    have h : p.coordsOfL (((PowerSeries.X : PowerSeries K) ^ k) • s)
        = ((PowerSeries.X : PowerSeries K) ^ k) • p.coordsOfL s :=
      p.coordsOfL.map_smul _ _
    rw [← hx, h]
    rfl
  have hX₁ := hcX x₁ s₁ hs₁
  have hX₂ := hcX x₂ s₂ hs₂
  have hφX : φ ((PowerSeries.X : PowerSeries K) ^ k) ≠ 0 :=
    (map_ne_zero_iff _
      (IsFractionRing.injective (PowerSeries K) (LaurentSeries K))).2
        (pow_ne_zero k (PowerSeries.X_ne_zero (R := K)))
  set F : Fin m → K := fun a =>
    laurentResidue K (y₁ a * φ (p.coordsOfL s₂ (blockInvol a))) with hFdef
  -- the right-hand side is the sum of the `F a`
  have hRHS : laurentResidue K (uInvPow K k *
      ∑ a : Fin m, w₁ a * φ (x₂ (σ a))) = ∑ a : Fin m, F a := by
    have h1 : uInvPow K k * φ ((PowerSeries.X : PowerSeries K) ^ k) = 1 :=
      uInvPow_mul_uPow _
    rw [p.pairing_eq_sum_coordsOf w₁ y₁ hy₁ x₂, Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    congr 1
    rw [hX₂ (blockInvol a), map_mul]
    calc uInvPow K k * (y₁ a * (φ ((PowerSeries.X : PowerSeries K) ^ k) *
            φ (p.coordsOfL s₂ (blockInvol a))))
        = (uInvPow K k * φ ((PowerSeries.X : PowerSeries K) ^ k)) *
            (y₁ a * φ (p.coordsOfL s₂ (blockInvol a))) := by ring
      _ = y₁ a * φ (p.coordsOfL s₂ (blockInvol a)) := by rw [h1, one_mul]
  -- the left-hand side is the sum over the blocks
  have hLHS : residueSpaceForm (fun b => p.mBlk b - k)
      (p.blockClassOf (fun b => p.mBlk b - k) s₁)
      (p.blockClassOf (fun b => p.mBlk b - k) s₂)
      = ∑ b : p.Blocks, laurentResidue K (uInvPow K (p.mBlk b - k) *
          φ (p.coordsOfL s₁ b.val * p.coordsOfL s₂ (blockInvol b.val)
            - p.coordsOfL s₂ b.val * p.coordsOfL s₁ (blockInvol b.val))) :=
    residueSpaceForm_mk (fun b => p.mBlk b - k) (fun b => p.coordsOfL s₁ b.val)
      (fun b => p.coordsOfL s₁ (blockInvol b.val)) (fun b => p.coordsOfL s₂ b.val)
      (fun b => p.coordsOfL s₂ (blockInvol b.val))
  -- off the torsion indices the terms vanish
  have hFzero : ∀ a : Fin m, p.mExp a = 0 → F a = 0 := by
    intro a ha
    by_cases hg : p.g a = 0
    · have hg' : p.g (blockInvol a) = 0 := by rw [p.g_blockInvol a, hg, neg_zero]
      have hz : φ (p.coordsOfL x₂ (blockInvol a)) = 0 := by
        rw [hc₂ (blockInvol a), hg', map_zero, zero_mul]
      rw [hX₂ (blockInvol a), map_mul] at hz
      have hz' : φ (p.coordsOfL s₂ (blockInvol a)) = 0 :=
        (mul_eq_zero.mp hz).resolve_left hφX
      rw [hFdef]
      simp only [hz', mul_zero, map_zero]
    · obtain ⟨v, hv⟩ := p.exists_unit_mul_pow hg
      rw [ha, pow_zero, mul_one] at hv
      have hy : y₁ a = φ ((↑v⁻¹ : PowerSeries K) * p.coordsOfL x₁ a) := by
        rw [map_mul, hc₁ a, hv, ← mul_assoc, ← map_mul]
        rw [show (↑v⁻¹ : PowerSeries K) * (v : PowerSeries K) = 1 from v.inv_mul]
        rw [map_one, one_mul]
      rw [hFdef]
      simp only [hy, ← map_mul]
      exact laurentResidue_algebraMap _
  -- and on a block the two sides match pairwise
  have hpairterm : ∀ b : p.Blocks,
      laurentResidue K (uInvPow K (p.mBlk b - k) *
        φ (p.coordsOfL s₁ b.val * p.coordsOfL s₂ (blockInvol b.val)
          - p.coordsOfL s₂ b.val * p.coordsOfL s₁ (blockInvol b.val)))
      = F b.val + F (blockInvol b.val) := by
    intro b
    have hkb : k ≤ p.mBlk b := le_trans hk b.2.2
    have hgb : p.g b.val ≠ 0 := p.g_ne_zero_of_one_le_mExp b.2.2
    have hgval : p.g b.val = (PowerSeries.X : PowerSeries K) ^ p.mBlk b :=
      p.g_eq_X_pow_mExp b.2.1 hgb
    have hgi : p.g (blockInvol b.val) = -(PowerSeries.X : PowerSeries K) ^ p.mBlk b :=
      p.g_blockInvol_eq_neg_X_pow_mExp b.2.1 hgb
    have hum : uInvPow K (p.mBlk b) *
        φ ((PowerSeries.X : PowerSeries K) ^ p.mBlk b) = 1 := uInvPow_mul_uPow _
    -- `u^{-m} · u^k = u^{-(m-k)}`
    have hu : uInvPow K (p.mBlk b) * φ ((PowerSeries.X : PowerSeries K) ^ k)
        = uInvPow K (p.mBlk b - k) := by
      have h2 : uInvPow K (p.mBlk b - k) *
          φ ((PowerSeries.X : PowerSeries K) ^ (p.mBlk b - k)) = 1 := uInvPow_mul_uPow _
      have hsplit : (PowerSeries.X : PowerSeries K) ^ p.mBlk b
          = PowerSeries.X ^ k * PowerSeries.X ^ (p.mBlk b - k) := by
        rw [← pow_add]
        congr 1
        omega
      have hne : φ ((PowerSeries.X : PowerSeries K) ^ (p.mBlk b - k)) ≠ 0 :=
        (map_ne_zero_iff _
          (IsFractionRing.injective (PowerSeries K) (LaurentSeries K))).2
            (pow_ne_zero (p.mBlk b - k) (PowerSeries.X_ne_zero (R := K)))
      refine mul_right_cancel₀ hne ?_
      rw [h2, ← hum, hsplit, map_mul]
      ring
    -- the coordinates of `w₁` at the two ends of the block
    have e1 : φ ((PowerSeries.X : PowerSeries K) ^ k) * φ (p.coordsOfL s₁ b.val)
        = φ ((PowerSeries.X : PowerSeries K) ^ p.mBlk b) * y₁ b.val := by
      rw [← map_mul, ← hX₁ b.val, hc₁ b.val, hgval]
    have e2 : φ ((PowerSeries.X : PowerSeries K) ^ k) *
        φ (p.coordsOfL s₁ (blockInvol b.val))
        = -(φ ((PowerSeries.X : PowerSeries K) ^ p.mBlk b) * y₁ (blockInvol b.val)) := by
      rw [← map_mul, ← hX₁ (blockInvol b.val), hc₁ (blockInvol b.val), hgi, map_neg,
        neg_mul]
    have hy1b : y₁ b.val = uInvPow K (p.mBlk b - k) * φ (p.coordsOfL s₁ b.val) := by
      linear_combination (-(uInvPow K (p.mBlk b))) * e1 +
        φ (p.coordsOfL s₁ b.val) * hu - y₁ b.val * hum
    have hy1i : y₁ (blockInvol b.val)
        = -(uInvPow K (p.mBlk b - k) * φ (p.coordsOfL s₁ (blockInvol b.val))) := by
      linear_combination (uInvPow K (p.mBlk b)) * e2 -
        φ (p.coordsOfL s₁ (blockInvol b.val)) * hu - y₁ (blockInvol b.val) * hum
    have key : uInvPow K (p.mBlk b - k) *
        φ (p.coordsOfL s₁ b.val * p.coordsOfL s₂ (blockInvol b.val)
          - p.coordsOfL s₂ b.val * p.coordsOfL s₁ (blockInvol b.val))
        = y₁ b.val * φ (p.coordsOfL s₂ (blockInvol b.val))
          + y₁ (blockInvol b.val) * φ (p.coordsOfL s₂ b.val) := by
      rw [map_sub, map_mul, map_mul, hy1b, hy1i]
      ring
    rw [key, map_add, hFdef]
    congr 2
    rw [blockInvol_involutive]
  rw [hLHS, hRHS,
    Finset.sum_congr rfl fun b (_ : b ∈ Finset.univ) => hpairterm b,
    p.sum_eq_sum_blocks F hFzero]

end AlternatingPresentation

/-! ### Existence -/

section Exists

open Equiv

variable {K : Type u} [Field K] {m : ℕ}

/-- Shifting a column permutation of the left factor to a row permutation of
the right factor, for an involutive index permutation. -/
private theorem submatrix_perm_mul {σ : Equiv.Perm (Fin m)}
    (hσ : Function.Involutive σ) (X Y : Matrix (Fin m) (Fin m) (PowerSeries K)) :
    X.submatrix id σ * Y = X * Y.submatrix σ id := by
  refine Matrix.ext fun a b => ?_
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, id_eq]
  refine Eq.trans ?_ (Equiv.sum_comp σ fun c => X a c * Y (σ c) b)
  exact Finset.sum_congr rfl fun c _ => by rw [hσ c]

private theorem blockInvol_symm : (blockInvol (n := m)).symm = blockInvol :=
  Equiv.ext fun i => (Equiv.symm_apply_eq _).mpr (blockInvol_involutive i).symm

/-- **Every `σ`-alternating matrix over `K⟦u⟧` has a presentation.**  The
congruence comes from the hyperbolic normal form of `Aᵀ.submatrix id σ`
(`alt_hyperbolic`), and normalisation from one diagonal rescaling of `U` on the
even representatives, matched on the right automatically because the right
factor is `dualMat σ U`.

`Pencil.localData` is the instance of this theorem at `A = adMat P`,
`σ = swapIdx n`. -/
theorem exists_alternatingPresentation (σ : Equiv.Perm (Fin m))
    (hσ : Function.Involutive σ) (A : Matrix (Fin m) (Fin m) (PowerSeries K))
    (hA : IsAltMatrix (Aᵀ.submatrix id σ)) :
    Nonempty (AlternatingPresentation K m σ A) := by
  classical
  obtain ⟨W, d, hWdet, hW⟩ := alt_hyperbolic (R := PowerSeries K) m _ hA
  set G : Matrix (Fin m) (Fin m) (PowerSeries K) := Aᵀ.submatrix id σ with hG
  set Pi : Matrix (Fin m) (Fin m) (PowerSeries K) :=
    Perm.permMatrix (PowerSeries K) (blockInvol (n := m)) with hPi
  set U₀ : Matrix (Fin m) (Fin m) (PowerSeries K) :=
    Wᵀ.submatrix (blockInvol (n := m)) σ with hU₀def
  have hPimul : ∀ M : Matrix (Fin m) (Fin m) (PowerSeries K),
      Pi * M = M.submatrix (blockInvol (n := m)) id := fun M =>
    PEquiv.toMatrix_toPEquiv_mul _ M
  have hmulPi : ∀ M : Matrix (Fin m) (Fin m) (PowerSeries K),
      M * Pi = M.submatrix id (blockInvol (n := m)) := by
    intro M
    rw [hPi, PEquiv.mul_toMatrix_toPEquiv, blockInvol_symm]
  have hsign : ∀ τ : Equiv.Perm (Fin m),
      IsUnit ((Perm.sign τ : ℤ) : PowerSeries K) := by
    intro τ
    rcases Int.units_eq_one_or (Perm.sign τ) with h | h <;> rw [h] <;> simp
  have hU₀det : IsUnit U₀.det := by
    have hsplit : U₀ = (Wᵀ.submatrix (blockInvol (n := m)) id).submatrix id σ := rfl
    rw [hsplit, Matrix.det_permute', Matrix.det_permute, Matrix.det_transpose]
    exact (hsign _).mul ((hsign _).mul hWdet)
  have hAsub : A.submatrix σ id = -G := by
    refine Matrix.ext fun a b => ?_
    show G b a = -(G a b)
    exact hA.skew a b
  have hU₀eq : U₀ = Pi * Wᵀ.submatrix id σ := by
    rw [hPimul]
    rfl
  have hV₀ : dualMat σ U₀ = W := by
    refine Matrix.ext fun a b => ?_
    rw [dualMat_apply, hU₀def, Matrix.submatrix_apply, Matrix.transpose_apply,
      hσ a, blockInvol_involutive]
  have hprod : U₀ * A * W = Matrix.diagonal (hypRow (n := m) d) := by
    have h1 : U₀ * A = Pi * (Wᵀ * (A.submatrix σ id)) := by
      rw [hU₀eq, Matrix.mul_assoc, submatrix_perm_mul hσ]
    have h2 : U₀ * A * W = Pi * (Wᵀ * (A.submatrix σ id) * W) := by
      rw [h1, Matrix.mul_assoc]
    rw [h2, hAsub]
    have h3 : Wᵀ * (-G) * W = -(Wᵀ * G * W) := by
      simp only [Matrix.mul_neg, Matrix.neg_mul]
    rw [h3, hW, hypNF_eq_diagonal_mul_permMatrix, Matrix.mul_neg, ← hPi,
      ← Matrix.mul_assoc, hPimul, hmulPi]
    refine Matrix.ext fun a b => ?_
    simp only [Matrix.neg_apply, Matrix.submatrix_apply, id_eq]
    by_cases hab : a = b
    · subst hab
      rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, hypRow_blockInvol, neg_neg]
    · have hne : (blockInvol (n := m)) a ≠ blockInvol b := fun hc =>
        hab ((blockInvol (n := m)).injective hc)
      rw [Matrix.diagonal_apply_ne _ hne, Matrix.diagonal_apply_ne _ hab, neg_zero]
  -- rescale the even coordinates so that the diagonal entries are honest powers of `u`
  have hvex : ∀ k : ℕ, ∃ w : (PowerSeries K)ˣ, d k ≠ 0 →
      d k = (w : PowerSeries K) * PowerSeries.X ^ (d k).order.toNat := by
    intro k
    by_cases h : d k = 0
    · exact ⟨1, fun hc => absurd h hc⟩
    · obtain ⟨w, hw⟩ := exists_unit_mul_X_pow h
      exact ⟨w, fun _ => hw⟩
  choose w hw using hvex
  set δ : ℕ → (PowerSeries K)ˣ := fun k => if d k = 0 then 1 else (w k)⁻¹ with hδ
  set c : Fin m → PowerSeries K :=
    fun a => if Even ((a : ℕ) + m) then (δ (a : ℕ) : PowerSeries K) else 1 with hc
  set e : ℕ → ℕ∞ := fun k => (d k).order with he
  have hdetDv : IsUnit (Matrix.diagonal c).det := by
    rw [Matrix.det_diagonal]
    refine IsUnit.prod_univ_iff.mpr fun a => ?_
    by_cases hev : Even ((a : ℕ) + m)
    · rw [hc]; simp only; rw [ite_eq_left hev]; exact (δ (a : ℕ)).isUnit
    · rw [hc]; simp only; rw [ite_eq_right hev]; exact isUnit_one
  have hkey : ∀ i : Fin m,
      c i * hypRow (n := m) d i * c (blockInvol i) = normFactor K m e i := by
    intro i
    have hi := i.isLt
    by_cases hev : Even ((i : ℕ) + m)
    · have hodd : ¬ Even (((blockInvol (n := m) i : Fin m) : ℕ) + m) := by
        rw [blockInvol_apply, blockInvolFun_of_even hev]
        rw [Nat.even_iff] at hev ⊢
        omega
      rw [hc]
      simp only
      rw [ite_eq_left hev, ite_eq_right hodd, mul_one, normFactor, hypRow,
        ite_eq_left hev, hypRow, ite_eq_left hev]
      by_cases hd : d (i : ℕ) = 0
      · rw [hd, mul_zero, he]
        simp only [hd, PowerSeries.order_zero, uOrdPow_top]
      · have hδi : δ (i : ℕ) = (w (i : ℕ))⁻¹ := by
          simp only [hδ]
          exact ite_eq_right hd
        rw [hδi, hw (i : ℕ) hd, ← mul_assoc, ← Units.val_mul, inv_mul_cancel,
          Units.val_one, one_mul, he, uOrdPow,
          ite_eq_right (fun hcc => hd (PowerSeries.order_eq_top.mp hcc))]
    · rw [hc]
      simp only
      rw [ite_eq_right hev]
      by_cases h0 : (i : ℕ) = 0
      · have hfix : blockInvol (n := m) i = i := by
          rw [blockInvol_apply]; exact blockInvolFun_of_odd_zero hev h0
        rw [hfix, ite_eq_right hev, mul_one, one_mul, normFactor, hypRow,
          ite_eq_right hev, ite_eq_left h0, hypRow, ite_eq_right hev, ite_eq_left h0]
      · have hE : Even (((blockInvol (n := m) i : Fin m) : ℕ) + m) := by
          rw [blockInvol_apply, blockInvolFun_of_odd_pos hev h0]
          rw [Nat.even_iff] at hev ⊢
          omega
        have hidx : ((blockInvol (n := m) i : Fin m) : ℕ) = (i : ℕ) - 1 := by
          rw [blockInvol_apply]
          exact blockInvolFun_of_odd_pos hev h0
        rw [ite_eq_left hE, one_mul, hidx, normFactor, hypRow, ite_eq_right hev,
          ite_eq_right h0, hypRow, ite_eq_right hev, ite_eq_right h0]
        by_cases hd : d ((i : ℕ) - 1) = 0
        · rw [hd, neg_zero, zero_mul, he]
          simp only [hd, PowerSeries.order_zero, uOrdPow_top, neg_zero]
        · have hδi : δ ((i : ℕ) - 1) = (w ((i : ℕ) - 1))⁻¹ := by
            simp only [hδ]
            exact ite_eq_right hd
          rw [hδi, hw ((i : ℕ) - 1) hd, neg_mul, mul_comm, ← mul_assoc,
            ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul, he, uOrdPow,
            ite_eq_right (fun hcc => hd (PowerSeries.order_eq_top.mp hcc))]
  refine ⟨⟨Matrix.diagonal c * U₀, ?_, e, ?_⟩⟩
  · rw [Matrix.det_mul]
    exact hdetDv.mul hU₀det
  · have hdual : dualMat σ (Matrix.diagonal c * U₀)
        = W * Matrix.diagonal fun a => c (blockInvol a) := by
      refine Matrix.ext fun a b => ?_
      rw [dualMat_apply, Matrix.mul_diagonal, ← hV₀, dualMat_apply,
        Matrix.diagonal_mul]
      ring
    rw [hdual, show Matrix.diagonal c * U₀ * A * (W * Matrix.diagonal
        fun a => c (blockInvol a))
        = Matrix.diagonal c * (U₀ * A * W) * Matrix.diagonal
            fun a => c (blockInvol a) by simp only [Matrix.mul_assoc], hprod,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    exact congrArg Matrix.diagonal (funext hkey)

end Exists

end Height.DVR
