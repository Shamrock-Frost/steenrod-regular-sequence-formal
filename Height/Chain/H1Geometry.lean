import Height.Geometry.TangentGeneric
import Height.Chain.H1
import Height.Pencil.Centralizer
import Height.Pencil.RealizedLes
import Height.Pencil.SelfDual
import Height.Pencil.ArcsLocal
import Height.Geometry.Dimension.Components
import Height.Chain.Hyps

/-!
# `thm:h1`, the geometry: the node (H1)

The paper, `thm:h1`,
`subsec:realized`, `cor:arc-torsion`, `thm:isotropy`, `lem:residue-form`.

The file is in two halves, and ends with the node
`Height.Chain.pencilIncidenceBound`.

## The pencil half

`tangentDatum` builds, from a single point `(N, M)` of the locus whose member
at infinity has the generic type and from a space `T` of *realised* directions,
the whole numerical datum of `thm:h1`: the exponents `E`, the class map
`α`, and the three inequalities.  A direction is realised (`IsRealizedDir`)
when it is a commutator with the pencil over the function field of `ℙ¹`
(`cor:arc-torsion`) and kernel flat at every finite point (`lem:flag-flat`(1)).
The two pencil inputs enter here: `Pencil.realizedDimStmt` bounds `dim ker α`
and `Pencil.selfDualGapStmt` supplies the accounting
`½ Σ_x len_x = dim Fl − Σ b_i`.

## The variety half

`exists_pencilComponent_arcTangent` is the geometry that produces that point and
that space of directions, for a nonempty locus: the decomposition of `Î_{τ,d}`
into irreducible pieces (`Geometry.constructible_irreducible_pieces` on
`isConstructible_pencilLocus`), the three dense opens (the piece's own `D(q)`,
tangent genericity through `Geometry.exists_tangentGeneric_pt`, and the minors
of `M ^ k` that make `HasType (pairMatM w) τ` an open condition on the locus,
`hasType_of_le_rank_pow`), and the passage from a tangent vector to an arc
(`Geometry.exists_tangentGeneric_pt` again, through the pair-arc bridge
`isArcIn_of_arc`).  The shear that puts the generic type at infinity is the
*lower* shear `(N, M) ↦ (N, M + c N)` of `Chain/Substitution.lean`
(`pencilLocus_shear`), applied to the chosen piece: the affine reparametrisation
group alone fixes the member at infinity up to a scalar.  The remaining
pencil-side input, that an arc based at a point of the dense piece
has the right multidegree at its Laurent point, is `hasMultidegree_of_isArcIn`.
-/

namespace Height.Chain

open Matrix Height.Pencil Height.DVR Height.Graded Height.Steenrod
open Height.Geometry (affineDim pairCoords PairIndex fstMat sndMat matCoords)

universe u

section Pairs

variable {K : Type u} [Field K] {n : ℕ}

/-- The first matrix of a point of the space of pairs. -/
def pairMatN (w : PairIndex (Fin n) → K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => w (Sum.inl (i, j))

/-- The second matrix of a point of the space of pairs. -/
def pairMatM (w : PairIndex (Fin n) → K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => w (Sum.inr (i, j))

omit [Field K] in
@[simp] theorem pairMatN_apply (w : PairIndex (Fin n) → K) (i j : Fin n) :
    pairMatN w i j = w (Sum.inl (i, j)) := rfl

omit [Field K] in
@[simp] theorem pairMatM_apply (w : PairIndex (Fin n) → K) (i j : Fin n) :
    pairMatM w i j = w (Sum.inr (i, j)) := rfl

theorem pairCoords_pairMat (w : PairIndex (Fin n) → K) :
    pairCoords (pairMatN w, pairMatM w) = w := by
  funext x
  cases x <;> rfl

/-- Reading a point of the pair space as a pair of matrices is an isomorphism;
it is the inverse of `Chain.pairCoords`. -/
def pairMatEquiv :
    (PairIndex (Fin n) → K) ≃ₗ[K] Matrix (Fin n) (Fin n) K × Matrix (Fin n) (Fin n) K where
  toFun w := (pairMatN w, pairMatM w)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun p := pairCoords p
  left_inv w := pairCoords_pairMat w
  right_inv _ := rfl

/-- Evaluating a polynomial in the pair coordinates at a point of the pair
space is `Height.Pencil.pairEval` at the corresponding pair of matrices. -/
theorem pairEval_pairMat (w : PairIndex (Fin n) → K) :
    pairEval (pairMatN w) (pairMatM w) = (MvPolynomial.eval w : MvPolynomial (PairIndex (Fin n)) K →+* K) := by
  rw [pairEval]
  congr 1
  funext x
  cases x <;> rfl

end Pairs

section Chart

variable {K : Type u} [Field K] {n : ℕ}

/-- The entrywise form of `Pencil.Pat_eq_add_smul`: the pencil in the chart at
`t₀` has entries `Ṅ_{ij} + Ṁ_{ij}(t₀ + u)`. -/
theorem Pat_apply_eq (A B : Matrix (Fin n) (Fin n) K) (t₀ : K) (i j : Fin n) :
    Pat A B t₀ i j
      = PowerSeries.C (A i j) + PowerSeries.C (B i j) * (PowerSeries.C t₀ + PowerSeries.X) := by
  have h : pencil A B i j
      = MvPolynomial.C (A i j) * mu + MvPolynomial.C (B i j) * nu := rfl
  rw [Pat_apply, h, map_add, map_mul, map_mul, atPoint_mu, atPoint_nu, atPoint_C,
    atPoint_C, mul_one]

/-- The pencil direction of a point of the pair space, in the chart at `t₀`,
as a `K`-linear map. -/
noncomputable def patLin (t₀ : K) :
    (PairIndex (Fin n) → K) →ₗ[K] Matrix (Fin n) (Fin n) (PowerSeries K) where
  toFun w := Pat (pairMatN w) (pairMatM w) t₀
  map_add' v w := by
    refine Matrix.ext fun i j => ?_
    rw [Matrix.add_apply, Pat_apply_eq, Pat_apply_eq, Pat_apply_eq]
    simp only [pairMatN_apply, pairMatM_apply, Pi.add_apply, map_add]
    ring
  map_smul' c w := by
    refine Matrix.ext fun i j => ?_
    rw [Matrix.smul_apply, Pat_apply_eq, Pat_apply_eq]
    simp only [pairMatN_apply, pairMatM_apply, Pi.smul_apply, smul_eq_mul, map_mul, RingHom.id_apply, PowerSeries.smul_eq_C_mul]
    ring

end Chart

/-! ### Realised directions -/

section Realized

variable {K : Type u} [Field K] {n : ℕ}

/-- A pencil direction `(Ṅ, Ṁ)` is *realised* at the pencil `(N, M)`: it is a
commutator with the pencil over the function field `K(ℙ¹)` (`cor:arc-torsion`,
`Pencil/Arcs.lean`) and kernel flat at every finite point of `ℙ¹`
(`lem:flag-flat`(1), `Pencil/ArcsLocal.lean`).  These are exactly the two
consequences of lying on an arc of the incidence that the isotropy theorem and
the realised bound consume. -/
structure IsRealizedDir (N M Nd Md : Matrix (Fin n) (Fin n) K) : Prop where
  /-- the direction is a commutator with the pencil over the function field -/
  commutator : ∃ A : Matrix (Fin n) (Fin n) (FF K),
    pencilFF Nd Md = pencilFF N M * A - A * pencilFF N M
  /-- the direction is kernel flat at every finite point of `ℙ¹` -/
  kernelFlat : ∀ t₀ : K, KernelFlat (Pat N M t₀) (Qat (pencil Nd Md) t₀)

end Realized

/-! ### The centraliser has a homogeneous basis -/

section Centralizer

variable {K : Type u} [Field K] {n : ℕ}

/-- **`lem:free` for the centraliser**: `C` has a homogeneous basis, i.e. a
`Height.Pencil.CentralizerBasis`.  This is what `Pencil.realizedDimStmt` and
`Pencil.selfDualGapStmt` quantify over. -/
theorem exists_centralizerBasis (N M : Matrix (Fin n) (Fin n) K) :
    ∃ (ι : Type) (_ : Fintype ι) (b : ι → ℤ) (u : ι → (Fin (n * n) → Graded.Poly K)),
      CentralizerBasis N M b u := by
  obtain ⟨ι, hι, b, u, h1, h2, h3, h4⟩ :=
    Graded.saturated_free _ _ (isGraded_centralizerSub N M)
      (saturated_centralizerSub N M)
  exact ⟨ι, hι, b, u, ⟨h1, h2, h3, h4⟩⟩

/-- The sum of the degrees of a homogeneous basis of `C` is nonnegative. -/
theorem centralizerBasis_sum_nonneg {N M : Matrix (Fin n) (Fin n) K} {ι : Type} [Fintype ι]
    {b : ι → ℤ} {u : ι → (Fin (n * n) → Graded.Poly K)}
    (hu : CentralizerBasis N M b u) : 0 ≤ ∑ i, b i :=
  Finset.sum_nonneg fun i _ => hu.b_nonneg i

end Centralizer

/-! ### The class map at the drop points -/

section ClassMap

variable {K : Type u} [Field K] {n : ℕ}

/-- The index set of the class map for a finite set `F` of points of `𝔸¹`: one
hyperbolic block for each block of the local torsion at each point of `F`.  It
is a sigma type so that `residueSpaceForm` on the concatenated exponents is the
orthogonal sum of the forms `ω_x`. -/
abbrev blkIdx (N M : Matrix (Fin n) (Fin n) K) (F : Finset K) : Type u :=
  Σ x : {t : K // t ∈ F}, (txData N M x.val).Blocks

/-- The concatenated block exponents. -/
noncomputable def blkExp (N M : Matrix (Fin n) (Fin n) K) (F : Finset K)
    (s : blkIdx N M F) : ℕ :=
  (txData N M s.1.val).mBlk s.2

/-- **The class map** `α` of `thm:h1` before restriction to the tangent space:
a pencil direction goes to its torsion class in the chart at each point of `F`,
block by block. -/
noncomputable def blkClass (N M : Matrix (Fin n) (Fin n) K) (F : Finset K) :
    (PairIndex (Fin n) → K) →ₗ[K] residueBlockSpace K (blkExp N M F) :=
  LinearMap.pi fun s : blkIdx N M F =>
    (LinearMap.proj s.2).comp
      (((txData N M s.1.val).blockClass (txData N M s.1.val).mBlk).comp (patLin s.1.val))

/-- **`thm:isotropy`** at one point for realised directions: the block classes
of two realised directions are orthogonal for the residue form `ω_x`.  The two
Laurent commutators are `cor:arc-torsion` in the chart
(`exists_laurent_commutator_of_chart`), kernel flatness is part of
`IsRealizedDir`, and the local datum is self-dual and normalised by
construction. -/
theorem residueSpaceForm_blockClass_eq_zero {N M : Matrix (Fin n) (Fin n) K}
    (hnil : pencil N M ^ n = 0) (t₀ : K)
    {Nd₁ Md₁ Nd₂ Md₂ : Matrix (Fin n) (Fin n) K}
    (h₁ : IsRealizedDir N M Nd₁ Md₁) (h₂ : IsRealizedDir N M Nd₂ Md₂) :
    residueSpaceForm (txData N M t₀).mBlk
        ((txData N M t₀).blockClass (txData N M t₀).mBlk (Qat (pencil Nd₁ Md₁) t₀))
        ((txData N M t₀).blockClass (txData N M t₀).mBlk (Qat (pencil Nd₂ Md₂) t₀)) = 0 := by
  obtain ⟨A₁, hA₁⟩ :=
    exists_laurent_commutator_of_chart N M Nd₁ Md₁ (Graded.Chart.atPoint t₀) h₁.1
  obtain ⟨A₂, hA₂⟩ :=
    exists_laurent_commutator_of_chart N M Nd₂ Md₂ (Graded.Chart.atPoint t₀) h₂.1
  exact (txData N M t₀).omega_eq_zero (Pat_pow_eq_zero N M t₀ n hnil) _ _ A₁ A₂ hA₁.symm hA₂.symm (h₁.2 t₀) (h₂.2 t₀)

/-- Off the drop points there is no local torsion: `D_x = 0` by
`lem:local-pairing`. -/
theorem isEmpty_blocks_of_hasType [Infinite K] {N M : Matrix (Fin n) (Fin n) K}
    {τ : Nat.Partition n} (hnil : NilpotentPencil N M) (hgen : GenericType N M τ)
    {t₀ : K} (ht : HasType (N + t₀ • M) τ) : IsEmpty (txData N M t₀).Blocks := by
  have h := DX_add_cType N M τ t₀ hnil hgen
  rw [cOf_eq_cType_of_hasType ht] at h
  have h0 : Fintype.card (txData N M t₀).Blocks = 0 := by
    rw [DX] at h
    omega
  exact Fintype.card_eq_zero_iff.mp h0

/-- There is no local torsion at infinity when the member at infinity has the
generic type: the chart at infinity is the chart at `0` of the swapped pencil
(`PatInf_eq_Pat_zero`), which again has generic type `τ`
(`genericType_swap`). -/
theorem isEmpty_blocks_atInf [Infinite K] {N M : Matrix (Fin n) (Fin n) K}
    {τ : Nat.Partition n} (hnil : NilpotentPencil N M) (hgen : GenericType N M τ)
    (hMty : HasType M τ) : IsEmpty (localData (PatInf N M)).Blocks := by
  have hnil' : NilpotentPencil M N := (Height.Steenrod.nilpotentPencil_comm N M).mp hnil
  have hgen' : GenericType M N τ := genericType_swap hgen
  have hty : HasType (M + (0 : K) • N) τ := by simpa using hMty
  rw [PatInf_eq_Pat_zero]
  exact isEmpty_blocks_of_hasType hnil' hgen' hty

/-- **The kernel half of `thm:h1`**: a realised direction whose block classes
vanish at every drop point is a commutator with the localised pencil at every
point of `ℙ¹`.  At a finite point this is `cls_eq_zero_iff`, with the free part
killed by `cor:arc-torsion` and the torsion part either by hypothesis (at the
drop points) or because there is none (elsewhere); at infinity the torsion is
again absent because the member there has the generic type. -/
theorem isLocalCommutator_of_blockClass [Infinite K] {N M : Matrix (Fin n) (Fin n) K}
    {τ : Nat.Partition n} (hnil : NilpotentPencil N M) (hgen : GenericType N M τ)
    (hMty : HasType M τ) {F : Finset K} (hF : ∀ t₀ ∉ F, ¬ IsDropPoint N M t₀ τ)
    {Nd Md : Matrix (Fin n) (Fin n) K}
    (hA : ∃ A : Matrix (Fin n) (Fin n) (FF K),
      pencilFF Nd Md = pencilFF N M * A - A * pencilFF N M)
    (hblk : ∀ t₀ ∈ F, (txData N M t₀).blockClass (txData N M t₀).mBlk
      (Qat (pencil Nd Md) t₀) = 0) :
    IsLocalCommutator N M (pencil Nd Md) := by
  constructor
  · intro t₀
    refine (cls_eq_zero_iff N M t₀ (Qat (pencil Nd Md) t₀)).mp (Prod.ext_iff.mpr ⟨?_, ?_⟩)
    · show (txData N M t₀).blockClass (txData N M t₀).mBlk (Qat (pencil Nd Md) t₀) = 0
      by_cases ht : t₀ ∈ F
      · exact hblk t₀ ht
      · have hemp := isEmpty_blocks_of_hasType hnil hgen (not_not.mp (hF t₀ ht))
        funext b
        exact hemp.elim b
    · show (txData N M t₀).freeClass (Qat (pencil Nd Md) t₀) = 0
      exact freeClass_eq_zero N M Nd Md t₀ hA
  · refine ((localData (PatInf N M)).cls_eq_zero_iff ((pencil Nd Md).map atInf)).mp
      (Prod.ext_iff.mpr ⟨?_, ?_⟩)
    · show (localData (PatInf N M)).blockClass (localData (PatInf N M)).mBlk
        ((pencil Nd Md).map atInf) = 0
      have hemp := isEmpty_blocks_atInf hnil hgen hMty
      funext b
      exact hemp.elim b
    · show (localData (PatInf N M)).freeClass ((pencil Nd Md).map atInf) = 0
      exact freeClass_eq_zero_atInf N M Nd Md hA

end ClassMap

/-! ### The tangent datum -/

section TangentDatum

variable {K : Type u} [Field K] [Infinite K] {n : ℕ}

/-- **The pencil half of `thm:h1`.**  Let `(N, M)` be a nilpotent pencil of
generic type `τ` whose member at infinity has type `τ`, and let `T` be a space
of *realised* directions at it (`IsRealizedDir`).  Then the whole numerical
datum of `thm:h1` exists for `T`: the concatenated block exponents
`E` at the drop points, the class map `α`, the isotropy of its image
(`thm:isotropy`), the bound on its kernel (`Pencil.realizedDimStmt`,
`thm:realized-bound`) and the accounting (`Pencil.selfDualGapStmt`,
`lem:selfdual-degree`). -/
theorem tangentDatum [IsAlgClosed K]
    {N M : Matrix (Fin n) (Fin n) K} {τ : Nat.Partition n}
    (hnil : NilpotentPencil N M) (hgen : GenericType N M τ) (hMty : HasType M τ)
    (T : Submodule K (PairIndex (Fin n) → K))
    (hT : ∀ v ∈ T, IsRealizedDir N M (pairMatN v) (pairMatM v)) :
    ∃ (m : ℕ) (E : Fin m → ℕ) (α : T →ₗ[K] residueBlockSpace K E) (sumb : ℕ),
      (∀ x ∈ LinearMap.range α, ∀ y ∈ LinearMap.range α,
          residueSpaceForm E x y = 0) ∧
        Module.finrank K (LinearMap.ker α) ≤ 2 * dimFl τ + sumb ∧
        (∑ ξ, 2 * E ξ) + 2 * sumb ≤ 2 * dimFl τ := by
  classical
  obtain ⟨F, hF⟩ := finite_dropPoints hgen
  obtain ⟨ι₀, hι₀, b, u, hbasis⟩ := exists_centralizerBasis N M
  have hnilP : pencil N M ^ n = 0 := pencil_pow_eq_zero_of_nilpotentPencil hnil
  obtain ⟨σ⟩ : Nonempty (Fin (Fintype.card (blkIdx N M F)) ≃ blkIdx N M F) :=
    ⟨(Fintype.equivFin (blkIdx N M F)).symm⟩
  have hb0 : (0 : ℤ) ≤ ∑ i, b i := centralizerBasis_sum_nonneg hbasis
  have hcast : (((∑ i, b i).toNat : ℕ) : ℤ) = ∑ i, b i := Int.toNat_of_nonneg hb0
  -- the reindexing of the block spaces along `σ`
  have hreixinj : Function.Injective
      (LinearMap.pi (fun ξ : Fin (Fintype.card (blkIdx N M F)) =>
        LinearMap.proj (R := K) (φ := fun s : blkIdx N M F =>
          blockQuot K (blkExp N M F s) × blockQuot K (blkExp N M F s)) (σ ξ))) := by
    intro x y hxy
    funext s
    obtain ⟨ξ, rfl⟩ := σ.surjective s
    exact congrFun hxy ξ
  refine ⟨Fintype.card (blkIdx N M F), fun ξ => blkExp N M F (σ ξ),
    (LinearMap.pi fun ξ => LinearMap.proj (σ ξ)) ∘ₗ (blkClass N M F ∘ₗ T.subtype),
    (∑ i, b i).toNat, ?_, ?_, ?_⟩
  · -- `hiso`: the image is isotropic, by `thm:isotropy` at each drop point
    rintro x ⟨v, rfl⟩ y ⟨w, rfl⟩
    set f : blkIdx N M F → K := fun s =>
      blockResidueForm K (blkExp N M F s)
        (blkClass N M F v.val s) (blkClass N M F w.val s) with hf
    have hzero : ∀ x : {t : K // t ∈ F}, ∑ c : (txData N M x.val).Blocks, f ⟨x, c⟩ = 0 := by
      intro x
      have h := residueSpaceForm_blockClass_eq_zero hnilP x.val (hT v.val v.2) (hT w.val w.2)
      rw [residueSpaceForm_eq_sum] at h
      exact h
    have key : ∑ s : blkIdx N M F, f s = 0 := by
      rw [Fintype.sum_sigma f]
      exact Finset.sum_eq_zero fun x _ => hzero x
    have h2 : ∑ ξ : Fin (Fintype.card (blkIdx N M F)), f (σ ξ) = 0 := by
      rw [Equiv.sum_comp σ f]
      exact key
    exact h2
  · -- `hker`: the kernel consists of local commutators, so `thm:realized-bound` applies
    set g : T →ₗ[K] Matrix (Fin n) (Fin n) K × Matrix (Fin n) (Fin n) K :=
      pairMatEquiv.toLinearMap ∘ₗ T.subtype with hg
    have hginj : Function.Injective g :=
      pairMatEquiv.injective.comp (Submodule.injective_subtype T)
    have hloc : ∀ p ∈ (LinearMap.ker ((LinearMap.pi fun ξ => LinearMap.proj (σ ξ)) ∘ₗ
        (blkClass N M F ∘ₗ T.subtype))).map g,
        IsLocalCommutator N M (pencil p.1 p.2) := by
      rintro p ⟨v, hv, rfl⟩
      have h0 : blkClass N M F v.val = 0 := hreixinj (by rw [map_zero]; exact hv)
      refine isLocalCommutator_of_blockClass hnil hgen hMty hF (hT v.val v.2).1 ?_
      intro t₀ ht₀
      funext c
      exact congrFun h0 ⟨⟨t₀, ht₀⟩, c⟩
    have hrank := (Submodule.equivMapOfInjective g hginj
      (LinearMap.ker ((LinearMap.pi fun ξ => LinearMap.proj (σ ξ)) ∘ₗ
        (blkClass N M F ∘ₗ T.subtype)))).finrank_eq
    have h := realizedDimStmt N M τ hnil hgen b u hbasis _ hloc
    rw [← hrank] at h
    have hc := cType_le τ
    have h2 := two_dimFl τ
    omega
  · -- `hlen`: the accounting of `lem:selfdual-degree`
    have hsum : ∑ ξ : Fin (Fintype.card (blkIdx N M F)), 2 * blkExp N M F (σ ξ)
        = ∑ t₀ ∈ F, lenX N M t₀ := by
      rw [Equiv.sum_comp σ (fun s => 2 * blkExp N M F s), Fintype.sum_sigma,
        ← Finset.sum_coe_sort F (fun t₀ => lenX N M t₀)]
      rfl
    have hg := selfDualGapStmt N M τ hnil hgen hMty b u hbasis F
      (fun t₀ hd => by by_contra hc; exact hF t₀ hc hd)
    rw [hsum]
    omega

end TangentDatum

/-! ### Arcs realise directions -/

section Arc

open Height.Orbital

variable {K : Type u} [Field K] {n : ℕ}

/-- An arc of pencils inside `V(I)`, based at `w` with velocity `v`: the pair of
power-series matrices `(Ns, Ms)` has constant term `w`, linear term `v`, and every
element of `I` vanishes along it. -/
structure IsArcIn (I : Ideal (MvPolynomial (PairIndex (Fin n)) K)) (w v : PairIndex (Fin n) → K)
    (Ns Ms : Matrix (Fin n) (Fin n) (PowerSeries K)) : Prop where
  /-- the constant term of `Ns` is the `N`-half of the base point -/
  matC_N : matC Ns = pairMatN w
  /-- the constant term of `Ms` is the `M`-half of the base point -/
  matC_M : matC Ms = pairMatM w
  /-- the linear term of `Ns` is the `N`-half of the velocity -/
  matD_N : matD Ns = pairMatN v
  /-- the linear term of `Ms` is the `M`-half of the velocity -/
  matD_M : matD Ms = pairMatM v
  /-- the arc lies in `V(I)` -/
  vanish : ∀ f ∈ I, pairArcHom Ns Ms f = 0

end Arc

/-! ### The pair-arc bridge

`IsArcIn` is the coordinate form of a `Height.Geometry.Arc` at
`ι = PairIndex (Fin n)`; the chart is `Height.Geometry.pairCoords` at the
coefficient ring `K⟦u⟧`, exactly as `Pencil.siArcEquiv` and
`Orbital.matArcEquiv` do for their index types.  The general lemma both are
built from is `Height.Geometry.arcEquiv`.

The geometry API ties the index universe of `𝔸(ι)` to that of `K`,
and `PairIndex (Fin n) : Type`, so — as in
`Pencil/Marked.lean`'s shifted-isotropy section — the bridge lives at
`K : Type`, which is where the chain runs. -/

section Bridge

variable {K : Type} [Field K] {n : ℕ}

open Height.Orbital

/-- Evaluation of the pair coordinates along a pair of power-series matrices is
`aeval` at the corresponding tuple of power series. -/
theorem pairArcHom_eq_aeval (Ns Ms : Matrix (Fin n) (Fin n) (PowerSeries K))
    (f : MvPolynomial (PairIndex (Fin n)) K) :
    pairArcHom Ns Ms f = MvPolynomial.aeval (pairCoords (K := PowerSeries K) (Ns, Ms)) f := by
  rw [MvPolynomial.aeval_def]
  rfl

/-- **The bridge, from the API to coordinates**: an arc of `V(I)` in the pair space
is an arc of pencils based at its base point with its velocity. -/
theorem isArcIn_of_arc {I : Ideal (MvPolynomial (PairIndex (Fin n)) K)}
    (a : Height.Geometry.Arc I) :
    IsArcIn I a.base a.vel (fstMat a.coords) (sndMat a.coords) where
  matC_N := Matrix.ext fun _ _ => rfl
  matC_M := Matrix.ext fun _ _ => rfl
  matD_N := Matrix.ext fun _ _ => rfl
  matD_M := Matrix.ext fun _ _ => rfl
  vanish f hf := by
    rw [pairArcHom_eq_aeval, Height.Geometry.pairCoords_fstMat_sndMat]
    exact a.aeval_coords f hf

end Bridge

section Arc

open Height.Orbital

variable {K : Type u} [Field K] {n : ℕ}

/-- **Nilpotence along an arc.**  If every point of `V(I)` off `V(q)` carries a
nilpotent pencil then the pencil of any arc in `V(I)` is nilpotent over
`K⟦s⟧[μ, ν]`: the coefficients of `P^n` vanish on a dense open of `V(I)`, so `q`
times each of them lies in `I(V(I)) = I` (Nullstellensatz for the prime `I`),
hence each of them lies in `I` and is killed along the arc. -/
theorem pencilR_pow_eq_zero_of_arc [IsAlgClosed K] [Infinite K]
    (I : Ideal (MvPolynomial (PairIndex (Fin n)) K)) [hI : I.IsPrime]
    {q : MvPolynomial (PairIndex (Fin n)) K} (hq : q ∉ I)
    (hnil : ∀ w ∈ MvPolynomial.zeroLocus K I, MvPolynomial.eval w q ≠ 0 →
      NilpotentPencil (pairMatN w) (pairMatM w))
    {Ns Ms : Matrix (Fin n) (Fin n) (PowerSeries K)}
    (harc : ∀ f ∈ I, pairArcHom Ns Ms f = 0) :
    (pencil Ns Ms) ^ n = 0 := by
  classical
  set G : Matrix (Fin n) (Fin n) (Graded.Poly (MvPolynomial (PairIndex (Fin n)) K)) :=
    (genPencil K n) ^ n with hG
  have hcoeff : ∀ (i j : Fin n) (c : Fin 2 →₀ ℕ), (G i j).coeff c ∈ I := by
    intro i j c
    have hmul : q * (G i j).coeff c
        ∈ MvPolynomial.vanishingIdeal K (MvPolynomial.zeroLocus K I) := by
      intro w hw
      show MvPolynomial.eval w (q * (G i j).coeff c) = 0
      by_cases hqw : MvPolynomial.eval w q = 0
      · rw [map_mul, hqw, zero_mul]
      · have hz : pencil (pairMatN w) (pairMatM w) ^ n = 0 :=
          pencil_pow_eq_zero_of_nilpotentPencil (hnil w hw hqw)
        have hmap : G.map (MvPolynomial.map (pairEval (pairMatN w) (pairMatM w)))
            = pencil (pairMatN w) (pairMatM w) ^ n := by
          show (MvPolynomial.map (pairEval (pairMatN w) (pairMatM w))).mapMatrix G = _
          rw [hG, map_pow]
          congr 1
          exact genPencil_map_pairEval (pairMatN w) (pairMatM w)
        have hij : MvPolynomial.map (pairEval (pairMatN w) (pairMatM w)) (G i j) = 0 := by
          have h := congrFun (congrFun (hmap.trans hz) i) j
          simpa using h
        have hc : MvPolynomial.eval w ((G i j).coeff c) = 0 := by
          have h2 := congrArg (fun F : Graded.Poly K => F.coeff c) hij
          simpa [MvPolynomial.coeff_map, pairEval_pairMat] using h2
        rw [map_mul, hc, mul_zero]
    rw [MvPolynomial.IsPrime.vanishingIdeal_zeroLocus] at hmul
    exact (hI.mem_or_mem hmul).resolve_left hq
  have harcmap : (pencil Ns Ms) ^ n = G.map (MvPolynomial.map (pairArcHom Ns Ms)) := by
    show _ = (MvPolynomial.map (pairArcHom Ns Ms)).mapMatrix G
    rw [hG, map_pow]
    congr 1
    exact (genPencil_map_pairArcHom Ns Ms).symm
  rw [harcmap]
  refine Matrix.ext fun i j => ?_
  show MvPolynomial.map (pairArcHom Ns Ms) (G i j) = 0
  refine MvPolynomial.ext _ _ fun c => ?_
  rw [MvPolynomial.coeff_map]
  simpa using harc _ (hcoeff i j c)

/-- **An arc realises its velocity.**  `cor:arc-torsion` (`exists_commutator_of_arc`)
gives the commutator over `K(ℙ¹)` and `lem:flag-flat`(1) (`dcond_of_arc`) gives
kernel flatness at every finite point. -/
theorem isRealizedDir_of_arc (Ns Ms : Matrix (Fin n) (Fin n) (PowerSeries K))
    (τ : Nat.Partition n) (d : ℕ → ℕ)
    (hnil : (pencil Ns Ms) ^ n = 0) (hrank : ∀ k ≤ n, ArcRankEq Ns Ms k)
    (hbase : HasMultidegree (matC Ns) (matC Ms) τ d)
    (hgen : HasMultidegree (Ns.map (algebraMap (PowerSeries K) (LaurentSeries K)))
      (Ms.map (algebraMap (PowerSeries K) (LaurentSeries K))) τ d) :
    IsRealizedDir (matC Ns) (matC Ms) (matD Ns) (matD Ms) :=
  ⟨exists_commutator_of_arc Ns Ms hnil hrank,
    fun t₀ => (kernelFlat_iff_DCond _ _).mpr (dcond_of_arc Ns Ms τ d hbase hgen t₀)⟩

end Arc

/-! ### The lower shear and the type at infinity, in the pair coordinates -/

section Shear

variable {K : Type u} [Field K] {n : ℕ}

/-- **The lower shear** `(N, M) ↦ (N, M + c N)` in the pair coordinates; the
reparametrisation of `ℙ¹` that moves the member at the parameter `c⁻¹` to
infinity (`Chain.pencilLocus_shear`). -/
def lowerShear (c : K) (w : PairIndex (Fin n) → K) : PairIndex (Fin n) → K :=
  Sum.elim (fun ij : Fin n × Fin n => w (Sum.inl ij))
    (fun ij : Fin n × Fin n => w (Sum.inr ij) + c * w (Sum.inl ij))

@[simp] theorem pairMatN_lowerShear (c : K) (w : PairIndex (Fin n) → K) :
    pairMatN (lowerShear c w) = pairMatN w := rfl

@[simp] theorem pairMatM_lowerShear (c : K) (w : PairIndex (Fin n) → K) :
    pairMatM (lowerShear c w) = pairMatM w + c • pairMatN w := by
  refine Matrix.ext fun i j => ?_
  show w (Sum.inr (i, j)) + c * w (Sum.inl (i, j)) = _
  rw [Matrix.add_apply, Matrix.smul_apply, pairMatM_apply, pairMatN_apply, smul_eq_mul]

theorem lowerShear_lowerShear (c : K) (w : PairIndex (Fin n) → K) :
    lowerShear (-c) (lowerShear c w) = w := by
  funext x
  cases x with
  | inl ij => rfl
  | inr ij =>
      show w (Sum.inr ij) + c * w (Sum.inl ij) + -c * w (Sum.inl ij) = w (Sum.inr ij)
      ring

theorem isPolyMap_lowerShear (c : K) :
    Height.Geometry.IsPolyMap (lowerShear (n := n) c) :=
  ⟨Sum.elim (fun ij : Fin n × Fin n => MvPolynomial.X (Sum.inl ij))
      (fun ij : Fin n × Fin n =>
        MvPolynomial.X (Sum.inr ij) + MvPolynomial.C c * MvPolynomial.X (Sum.inl ij)),
    fun y x => by cases x <;> simp [lowerShear]⟩

theorem lowerShear_pairCoords (c : K) (p : Matrix (Fin n) (Fin n) K × Matrix (Fin n) (Fin n) K) :
    lowerShear c (pairCoords p) = pairCoords (p.1, p.2 + c • p.1) := by
  funext x
  cases x with
  | inl ij => rfl
  | inr ij =>
      show p.2 ij.1 ij.2 + c * p.1 ij.1 ij.2 = (p.2 + c • p.1) ij.1 ij.2
      rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]

/-- The image of the pencil locus in the pair coordinates is stable under the lower
shear. -/
theorem lowerShear_mem_image (c : K) {τ : Nat.Partition n} {d : ℕ → ℕ}
    {w : PairIndex (Fin n) → K} (hw : w ∈ pairCoords '' pencilLocus (K := K) τ d) :
    lowerShear c w ∈ pairCoords '' pencilLocus (K := K) τ d := by
  obtain ⟨p, hp, rfl⟩ := hw
  exact ⟨(p.1, p.2 + c • p.1), pencilLocus_shear c hp, (lowerShear_pairCoords c p).symm⟩

/-- The generic member at infinity, as a matrix of coordinate variables. -/
noncomputable def genMatM : Matrix (Fin n) (Fin n) (MvPolynomial (PairIndex (Fin n)) K) :=
  coordMat (fun ij : Fin n × Fin n => (Sum.inr ij : PairIndex (Fin n)))

theorem map_genMatM (w : PairIndex (Fin n) → K) :
    (genMatM (K := K) (n := n)).map (MvPolynomial.aeval w) = pairMatM w := by
  rw [genMatM, map_genMat]
  rfl

theorem map_genMatM_pow (w : PairIndex (Fin n) → K) (k : ℕ) :
    ((genMatM (K := K) (n := n)) ^ k).map (MvPolynomial.aeval w) = pairMatM w ^ k := by
  have h : ((MvPolynomial.aeval w : MvPolynomial (PairIndex (Fin n)) K →ₐ[K] K).mapMatrix :
      Matrix (Fin n) (Fin n) (MvPolynomial (PairIndex (Fin n)) K) →ₐ[K] _)
      (genMatM ^ k) = ((MvPolynomial.aeval w).mapMatrix genMatM) ^ k := map_pow _ _ _
  rw [AlgHom.mapMatrix_apply, AlgHom.mapMatrix_apply, map_genMatM] at h
  exact h

/-- A minor of a power of the member at infinity, as a polynomial in the pair
coordinates.  The nonvanishing of one of these for each `k` is exactly the open half
of `HasType (pairMatM w) τ` (`Chain.hasType_of_le_rank_pow`). -/
noncomputable def minorAtInf (k r : ℕ) (f g : Fin r → Fin n) :
    MvPolynomial (PairIndex (Fin n)) K :=
  (((genMatM (K := K) (n := n)) ^ k).submatrix f g).det

theorem eval_minorAtInf (k r : ℕ) (f g : Fin r → Fin n) (w : PairIndex (Fin n) → K) :
    MvPolynomial.eval w (minorAtInf (K := K) k r f g)
      = (((pairMatM w) ^ k).submatrix f g).det := by
  rw [minorAtInf, ← MvPolynomial.aeval_eq_eval, AlgHom.map_det, AlgHom.mapMatrix_apply,
    ← Matrix.submatrix_map, map_genMatM_pow]

end Shear

/-! ### The component and its tangent-generic point -/

section Hyps

open Height.Orbital

variable {K : Type u} [Field K] {n : ℕ}

variable (K) in
/-- An irreducible component `V(I)` of (the closure of) the pencil locus `Î_{τ,d}`,
with a dense open `V(I) ∩ D(q)` of it inside the locus. -/
structure PencilComponent (τ : Nat.Partition n) (d : ℕ → ℕ) where
  /-- the prime of the component -/
  I : Ideal (MvPolynomial (PairIndex (Fin n)) K)
  prime : I.IsPrime
  /-- the function cutting out the dense open -/
  q : MvPolynomial (PairIndex (Fin n)) K
  notMem : q ∉ I
  /-- the open `V(I) ∩ D(q)` lies in the locus -/
  locus : ∀ w ∈ MvPolynomial.zeroLocus K I, MvPolynomial.eval w q ≠ 0 →
    (pairMatN w, pairMatM w) ∈ pencilLocus τ d

/-- **The multidegree along an arc** (it is
`hasMultidegree_of_pairArc`, `Chain/LocalFlat.lean`): an arc in a pencil component,
based at a point of its dense open, has multidegree `d` at its Laurent point. -/
theorem hasMultidegree_of_isArcIn [IsAlgClosed K] {τ : Nat.Partition n} {d : ℕ → ℕ}
    (C : PencilComponent K τ d) {w v : PairIndex (Fin n) → K}
    (_hw : w ∈ MvPolynomial.zeroLocus K C.I) (hq : MvPolynomial.eval w C.q ≠ 0)
    {Ns Ms : Matrix (Fin n) (Fin n) (PowerSeries K)} (hin : IsArcIn C.I w v Ns Ms) :
    HasMultidegree (Ns.map (algebraMap (PowerSeries K) (LaurentSeries K)))
      (Ms.map (algebraMap (PowerSeries K) (LaurentSeries K))) τ d :=
  hasMultidegree_of_pairArc C.prime C.notMem (fun z hz hz' => C.locus z hz hz') Ns Ms
    hin.vanish (by rw [hin.matC_N, hin.matC_M, pairEval_pairMat]; exact hq)

/-- A tangent-generic point of a pencil component, off a further hypersurface
`V(g)`: a point `w` of the dense open whose member at infinity has the generic
type, carrying a space `T` of directions each realised by an arc in `V(I)`, with
`dim Î_{τ,d} ≤ dim T`. -/
structure ArcTangentPoint {τ : Nat.Partition n} {d : ℕ → ℕ} (C : PencilComponent K τ d)
    (g : MvPolynomial (PairIndex (Fin n)) K) where
  /-- the point -/
  w : PairIndex (Fin n) → K
  /-- the space of realised directions -/
  T : Submodule K (PairIndex (Fin n) → K)
  mem : w ∈ MvPolynomial.zeroLocus K C.I
  q_ne : MvPolynomial.eval w C.q ≠ 0
  g_ne : MvPolynomial.eval w g ≠ 0
  /-- the member at infinity has the generic type -/
  type : HasType (pairMatM w) τ
  /-- every direction in `T` is realised by an arc in `V(I)` -/
  arcs : ∀ v ∈ T, ∃ Ns Ms : Matrix (Fin n) (Fin n) (PowerSeries K), IsArcIn C.I w v Ns Ms
  /-- the dimension bound `dim Î_{τ,d} ≤ dim T` -/
  affineDim_le : affineDim (pairCoords '' pencilLocus (K := K) τ d)
    ≤ ((Module.finrank K T : ℕ) : WithBot ℕ∞)

end Hyps

/-! ### The variety half of `thm:h1`

The geometry API ties the index universe of `𝔸(ι)` to that of `K`, and
`PairIndex (Fin n) : Type`, so this lives at `K : Type` — which is where the
chain runs (`Kbar p r : Type`), and where `Chain.pencilIncidenceBound` and
`Chain/H2.lean` already are. -/

section Variety

open Height.Orbital

variable {K : Type} [Field K] {n : ℕ}

variable (K n) in
/-- **The variety half of `thm:h1`.**

For a nonempty `Î_{τ,d}` there is an irreducible `V(I)` and a `q ∉ I` such that
`V(I) ∖ V(q)` lies in `Î_{τ,d}` and `dim V(I) = dim Î_{τ,d}`, and, for every
further nonvanishing condition `g ∉ I`, a point `w` of `V(I)` off `V(q)` and off
`V(g)` whose member at infinity has the generic type, carrying a space `T` of
directions each realised by an arc in `V(I)` based at `w`, with
`dim Î_{τ,d} ≤ dim T`.

Route.  Step 1: `Î_{τ,d}` is constructible (`isConstructible_pencilLocus`), so it
is a finite union of dense basic opens `C ∩ D(q)` of irreducible closed sets
(`Geometry.constructible_irreducible_pieces`); take one of maximal dimension, so
that `dim (C ∩ D(q)) = dim Î_{τ,d} = dim C` (`affineDim_inter_dense`).  Step 2,
the shear: `C` itself need not carry a point whose member *at infinity* has the
generic type — the affine reparametrisation group of `Chain/Substitution.lean`
fixes that member up to a scalar — so the component is moved by the *lower*
shear `(N, M) ↦ (N, M + c N)` (`Chain.pencilLocus_shear`, the swap conjugate of
the affine reparametrisation), with `c = t⁻¹` for a `t` at which the member of a
chosen point of `C ∩ D(q)` has type `τ`.  On the sheared component
`C' = σ_c(C)` — again irreducible, again of dimension `dim Î_{τ,d}`, again with
a dense open inside `Î_{τ,d}` — the condition `HasType (pairMatM w) τ` is *open*
(`Chain.hasType_of_le_rank_pow`: the other inequality is automatic on the locus)
and nonempty, so one minor `minorAtInf` per `k` is a further nonvanishing
condition.  Step 3: `Geometry.exists_tangentGeneric_pt` at `V(I)` with all these
conditions gives the point, the dimension bound and the arcs; the arcs become
`IsArcIn` through the pair-arc bridge `isArcIn_of_arc`.

The nonemptiness hypothesis is necessary and not implied by `d ≠ 0`: the
conclusion produces a point of `Î_{τ,d}` (a nonempty basic open of an
irreducible `V(I)` over an algebraically closed field has a `K`-point), so it is
false whenever the locus is empty.  `pencilIncidenceBound` discharges that case
directly, `affineDim ∅ = ⊥`. -/
theorem exists_pencilComponent_arcTangent [IsAlgClosed K] [Infinite K]
    (τ : Nat.Partition n) (d : ℕ → ℕ) (_hd : d ≠ 0)
    (hne : (pencilLocus (K := K) τ d).Nonempty) :
    ∃ C : PencilComponent K τ d, ∀ g ∉ C.I, Nonempty (ArcTangentPoint C g) := by
  classical
  -- Step 1: an irreducible piece of maximal dimension
  obtain ⟨J, hJ, C, q, hCprime, hCcl, hcov⟩ :=
    Height.Geometry.constructible_irreducible_pieces (isConstructible_pencilLocus (K := K) τ d)
  have _ : Finite J := hJ
  obtain ⟨y₀, hy₀⟩ : (pairCoords '' pencilLocus (K := K) τ d).Nonempty := hne.image _
  obtain ⟨a₀, -⟩ := Set.mem_iUnion.1 (hcov ▸ hy₀)
  have _ : Nonempty J := ⟨a₀⟩
  obtain ⟨a, hmax⟩ := Finite.exists_max
    fun j : J => affineDim (C j ∩ {y | MvPolynomial.aeval y (q j) ≠ 0})
  have hdimpiece : affineDim (pairCoords '' pencilLocus (K := K) τ d)
      = affineDim (C a ∩ {y | MvPolynomial.aeval y (q a) ≠ 0}) := by
    rw [hcov, Height.Geometry.affineDim_iUnion]
    exact le_antisymm (iSup_le hmax)
      (le_iSup (fun j : J => affineDim (C j ∩ {y | MvPolynomial.aeval y (q j) ≠ 0})) a)
  have hpne : (C a ∩ {y | MvPolynomial.aeval y (q a) ≠ 0}).Nonempty := by
    rcases Set.eq_empty_or_nonempty (C a ∩ {y | MvPolynomial.aeval y (q a) ≠ 0}) with hemp | h
    · refine absurd ?_ (Set.nonempty_iff_ne_empty.mp ⟨y₀, hy₀⟩)
      rw [← Height.Geometry.affineDim_eq_bot_iff, hdimpiece, hemp]
      exact (Height.Geometry.affineDim_eq_bot_iff _).mpr rfl
    · exact h
  obtain ⟨w₀, hw₀C, hw₀q⟩ := hpne
  have hqa : q a ∉ MvPolynomial.vanishingIdeal K (C a) := fun hmem => hw₀q (hmem _ hw₀C)
  have hdimC : affineDim (pairCoords '' pencilLocus (K := K) τ d) = affineDim (C a) := by
    rw [hdimpiece, Height.Geometry.affineDim_inter_dense (hCprime a) hqa]
  -- Step 2: the shear that puts a generic member at infinity
  have hw₀Y : w₀ ∈ pairCoords '' pencilLocus (K := K) τ d := by
    rw [hcov]; exact Set.mem_iUnion.2 ⟨a, hw₀C, hw₀q⟩
  obtain ⟨p₀, hp₀, hp₀eq⟩ := hw₀Y
  obtain ⟨F, hF⟩ := hp₀.2.1
  obtain ⟨t, ht⟩ : ∃ t : K, t ∉ insert (0 : K) F := by
    obtain ⟨t, ht⟩ := Set.Infinite.nonempty
      ((((insert (0 : K) F : Finset K) : Set K)).toFinite.infinite_compl)
    exact ⟨t, by simpa using ht⟩
  have ht0 : t ≠ 0 := fun h => ht (by rw [h]; exact Finset.mem_insert_self 0 F)
  have htF : t ∉ F := fun h => ht (Finset.mem_insert_of_mem h)
  have hc0 : t⁻¹ ≠ 0 := inv_ne_zero ht0
  have hmat : pairMatM w₀ + t⁻¹ • pairMatN w₀ = t⁻¹ • (p₀.1 + t • p₀.2) := by
    rw [← hp₀eq]
    have h1 : pairMatN (pairCoords p₀) = p₀.1 := rfl
    have h2 : pairMatM (pairCoords p₀) = p₀.2 := rfl
    rw [h1, h2, smul_add, smul_smul, inv_mul_cancel₀ ht0, one_smul]
    abel
  have htype₀ : HasType (pairMatM w₀ + t⁻¹ • pairMatN w₀) τ := by
    rw [hmat]
    exact (hasType_smul hc0).mpr (hF t htF)
  -- the sheared component
  have hinv : ∀ y : PairIndex (Fin n) → K, lowerShear (-t⁻¹) (lowerShear t⁻¹ y) = y :=
    lowerShear_lowerShear t⁻¹
  have hinv' : ∀ y : PairIndex (Fin n) → K, lowerShear t⁻¹ (lowerShear (-t⁻¹) y) = y := by
    intro y
    have h := lowerShear_lowerShear (-t⁻¹) y
    rwa [neg_neg] at h
  set C' : Set (PairIndex (Fin n) → K) := lowerShear t⁻¹ '' C a with hC'def
  have hC'pre : C' = lowerShear (-t⁻¹) ⁻¹' C a := by
    ext y
    exact ⟨by rintro ⟨x, hx, rfl⟩; rw [Set.mem_preimage, hinv x]; exact hx,
      fun hy => ⟨lowerShear (-t⁻¹) y, hy, hinv' y⟩⟩
  have hC'cl : Height.Geometry.zclosure C' = C' := by
    rw [hC'pre]
    exact Height.Geometry.zclosure_preimage (isPolyMap_lowerShear (-t⁻¹)) (hCcl a)
  have hC'prime : (MvPolynomial.vanishingIdeal K C').IsPrime :=
    Height.Geometry.irreducible_image (isPolyMap_lowerShear t⁻¹) (hCprime a)
  have hC'dim : affineDim C' = affineDim (C a) :=
    Height.Geometry.affineDim_image_eq (isPolyMap_lowerShear t⁻¹)
      (isPolyMap_lowerShear (-t⁻¹)) fun y _ => hinv y
  -- the function cutting out the dense open of the sheared component
  obtain ⟨Fneg, hFneg⟩ := isPolyMap_lowerShear (K := K) (n := n) (-t⁻¹)
  set q' : MvPolynomial (PairIndex (Fin n)) K := MvPolynomial.aeval Fneg (q a) with hq'def
  have hq'eval : ∀ y : PairIndex (Fin n) → K,
      MvPolynomial.aeval y q' = MvPolynomial.aeval (lowerShear (-t⁻¹) y) (q a) := fun y => by
    have hpt : (fun j => MvPolynomial.aeval y (Fneg j)) = lowerShear (-t⁻¹) y := by
      funext j
      exact (hFneg y j).symm
    rw [hq'def, Height.Geometry.aeval_aeval, hpt]
  have hw₁C' : lowerShear t⁻¹ w₀ ∈ C' := ⟨w₀, hw₀C, rfl⟩
  have hw₁q : MvPolynomial.aeval (lowerShear t⁻¹ w₀) q' ≠ 0 := by
    rw [hq'eval, hinv w₀]; exact hw₀q
  have hq'notMem : q' ∉ MvPolynomial.vanishingIdeal K C' := fun hmem => hw₁q (hmem _ hw₁C')
  have hlocus : ∀ w ∈ MvPolynomial.zeroLocus K (MvPolynomial.vanishingIdeal K C'),
      MvPolynomial.eval w q' ≠ 0 → (pairMatN w, pairMatM w) ∈ pencilLocus τ d := by
    intro w hw hwq
    have hwC' : w ∈ C' := by rw [← hC'cl]; exact hw
    rw [hC'pre] at hwC'
    have hxpiece : lowerShear (-t⁻¹) w ∈ C a ∩ {y | MvPolynomial.aeval y (q a) ≠ 0} := by
      refine ⟨hwC', ?_⟩
      show MvPolynomial.aeval (lowerShear (-t⁻¹) w) (q a) ≠ 0
      rw [← hq'eval w]
      rwa [MvPolynomial.aeval_eq_eval]
    have hxY : lowerShear (-t⁻¹) w ∈ pairCoords '' pencilLocus (K := K) τ d := by
      rw [hcov]; exact Set.mem_iUnion.2 ⟨a, hxpiece⟩
    have hwY := lowerShear_mem_image t⁻¹ hxY
    rw [hinv' w] at hwY
    obtain ⟨p, hp, hpe⟩ := hwY
    have hpair : (pairMatN w, pairMatM w) = p := by rw [← hpe]; rfl
    rw [hpair]
    exact hp
  refine ⟨⟨MvPolynomial.vanishingIdeal K C', hC'prime, q', hq'notMem, hlocus⟩, ?_⟩
  intro g hg
  -- the minors of the powers of the member at infinity, nonzero at the sheared point
  have hminor : ∀ k : ℕ, ∃ fg : (Fin (n - mk τ k) → Fin n) × (Fin (n - mk τ k) → Fin n),
      MvPolynomial.eval (lowerShear t⁻¹ w₀)
        (minorAtInf (K := K) k (n - mk τ k) fg.1 fg.2) ≠ 0 := by
    intro k
    have hrk : n - mk τ k ≤ Matrix.rank ((pairMatM (lowerShear t⁻¹ w₀)) ^ k) := by
      by_cases hk : 1 ≤ k ∧ k ≤ n
      · have hty : HasType (pairMatM (lowerShear t⁻¹ w₀)) τ := by
          rw [pairMatM_lowerShear]; exact htype₀
        have h := hasType_iff_rank_le.mp hty k hk.1 hk.2
        omega
      · rcases Nat.eq_zero_or_pos k with rfl | hk1
        · rw [mk_zero, pow_zero, Nat.sub_zero]
          have h1 : Matrix.rank (1 : Matrix (Fin n) (Fin n) K) = n := by simp
          omega
        · rw [mk_eq_of_le (by omega : n ≤ k)]
          simp
    obtain ⟨f₀, g₀, hfg⟩ := Height.Toolbox.exists_submatrix_det_ne_zero _ hrk
    exact ⟨(f₀, g₀), by rw [eval_minorAtInf]; exact hfg⟩
  choose fg hfg using hminor
  set s : Finset (MvPolynomial (PairIndex (Fin n)) K) :=
    insert q' (insert g ((Finset.Icc 1 n).image
      fun k => minorAtInf (K := K) k (n - mk τ k) (fg k).1 (fg k).2)) with hsdef
  have hsI : ∀ h ∈ s, h ∉ MvPolynomial.vanishingIdeal K C' := by
    intro h hh
    rw [hsdef, Finset.mem_insert, Finset.mem_insert, Finset.mem_image] at hh
    rcases hh with rfl | rfl | ⟨k, -, rfl⟩
    · exact hq'notMem
    · exact hg
    · intro hmem
      refine hfg k ?_
      rw [← MvPolynomial.aeval_eq_eval]
      exact hmem _ hw₁C'
  have _ : (MvPolynomial.vanishingIdeal K C').IsPrime := hC'prime
  obtain ⟨w, hwV, hws, hwdim, hwarcs⟩ :=
    Height.Geometry.exists_tangentGeneric_pt (MvPolynomial.vanishingIdeal K C') s hsI
  have hwq : MvPolynomial.eval w q' ≠ 0 := hws _ (Finset.mem_insert_self _ _)
  have hwg : MvPolynomial.eval w g ≠ 0 :=
    hws _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have hwloc := hlocus w hwV hwq
  refine ⟨{ w := w
            T := Height.Geometry.jacobianKernel (MvPolynomial.vanishingIdeal K C') w
            mem := hwV
            q_ne := hwq
            g_ne := hwg
            type := ?_
            arcs := ?_
            affineDim_le := ?_ }⟩
  · refine hasType_of_le_rank_pow hwloc.2.1 fun k hk1 hkn => ?_
    refine Height.Toolbox.le_rank_of_submatrix_det_ne_zero _ (fg k).1 (fg k).2 ?_
    rw [← eval_minorAtInf]
    exact hws _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_image.2 ⟨k, Finset.mem_Icc.2 ⟨hk1, hkn⟩, rfl⟩)))
  · intro v hv
    obtain ⟨arc, hbase, hvel⟩ := hwarcs v hv
    have harc := isArcIn_of_arc arc
    rw [hbase, show arc.vel = v from funext hvel] at harc
    exact ⟨_, _, harc⟩
  · have hz : MvPolynomial.zeroLocus K (MvPolynomial.vanishingIdeal K C') = C' := hC'cl
    rw [hz] at hwdim
    rw [hdimC, ← hC'dim]
    exact hwdim

end Variety

/-! ### `thm:h1`: the tangent datum -/

section Main

open Height.Orbital

/-- **`thm:h1`, the node (H1)**: for `d ≠ 0` the cone over the incidence
`Î_{τ,d}` has dimension at most `3 dim Fl_{τ'}`.

The arcs supplied by `exists_pencilComponent_arcTangent` realise their
velocities (`isRealizedDir_of_arc`, using `arc_rank_eq` for the rank profile and
`pencilR_pow_eq_zero_of_arc` for nilpotence along the arc), `tangentDatum` turns
that space of realised directions into the exponents `E`, the class map `α` and
the three inequalities, and `pencilIncidenceBound_of_bounds` is the count.  An
empty locus is bounded directly, `affineDim ∅ = ⊥`. -/
theorem pencilIncidenceBound {K : Type} [Field K] [IsAlgClosed K] [Infinite K] {n : ℕ}
    (τ : Nat.Partition n) (d : ℕ → ℕ) (hd : d ≠ 0) :
    PencilIncidenceBound (K := K) τ d := by
  rcases Set.eq_empty_or_nonempty (pencilLocus (K := K) τ d) with hemp | hne
  · show affineDim (pairCoords '' pencilLocus (K := K) τ d) ≤ _
    rw [hemp, Set.image_empty, (Height.Geometry.affineDim_eq_bot_iff _).2 rfl]
    exact bot_le
  obtain ⟨C, hpt⟩ := exists_pencilComponent_arcTangent K n τ d hd hne
  have := C.prime
  obtain ⟨g, hgI, hgrk⟩ := arc_rank_eq (K := K) (n := n) n C.I
  obtain ⟨P⟩ := hpt g hgI
  obtain ⟨hnilw, hgenw, hmulw⟩ := C.locus P.w P.mem P.q_ne
  have hT : ∀ v ∈ P.T,
      IsRealizedDir (pairMatN P.w) (pairMatM P.w) (pairMatN v) (pairMatM v) := by
    intro v hv
    obtain ⟨Ns, Ms, hin⟩ := P.arcs v hv
    have hnilArc : (pencil Ns Ms) ^ n = 0 :=
      pencilR_pow_eq_zero_of_arc C.I C.notMem
        (fun w' hw' hq' => (C.locus w' hw' hq').1) hin.vanish
    have hev : ∀ f ∈ C.I, pairEval (pairMatN P.w) (pairMatM P.w) f = 0 := by
      simp only [pairEval_pairMat]
      exact fun f hf => P.mem f hf
    have hevg : pairEval (pairMatN P.w) (pairMatM P.w) g ≠ 0 := by
      rw [pairEval_pairMat]; exact P.g_ne
    have hrk : ∀ k ≤ n, ArcRankEq Ns Ms k :=
      hgrk (pairMatN P.w) (pairMatM P.w) hev hevg Ns Ms hin.vanish hin.matC_N hin.matC_M
    have hbase : HasMultidegree (matC Ns) (matC Ms) τ d := by
      rw [hin.matC_N, hin.matC_M]; exact hmulw
    have hlaur := hasMultidegree_of_isArcIn C P.mem P.q_ne hin
    have hreal' := isRealizedDir_of_arc Ns Ms τ d hnilArc hrk hbase hlaur
    rwa [hin.matC_N, hin.matC_M, hin.matD_N, hin.matD_M] at hreal'
  obtain ⟨m, E, α, sumb, hiso, hker, hlen⟩ :=
    tangentDatum hnilw hgenw P.type P.T hT
  exact pencilIncidenceBound_of_bounds ⟨m, E, P.T, α, dimFl τ, sumb⟩
    ⟨hiso, hker, hlen, two_dimFl τ, P.affineDim_le⟩

end Main

end Height.Chain
