import Height.Chain.H2
import Height.Chain.SIComponents

/-!
# `thm:h2-conditional`, the geometry: the component of `Ŷ` and the point

The paper, `thm:h2-conditional`.

This file is the two-parameter analogue of the variety half of
`Chain/H1Geometry.lean`: `MarkedComponent` and `MarkedArcTangentPoint` mirror
`PencilComponent` and `ArcTangentPoint`, and
`exists_markedComponent_arcTangent` mirrors `exists_pencilComponent_arcTangent`.
It produces, for a nonempty `Ŷ = markedLocus τ d N₀`, an irreducible `V(I)` with
a dense open inside `Ŷ` and of at least the dimension of `Ŷ`, and in it a
tangent-generic point whose member at infinity has the generic type, carrying a
space `T` of tangent directions each the velocity of an arc of `V(I)`.

## The one difference from (H1): the shear

`Chain/H1Geometry.lean` moves a generic member of the pencil to infinity with
the *lower* shear `(N, M) ↦ (N, M + c N)`, which in the pair coordinates is
linear, hence a polynomial automorphism of the ambient space; the component may
simply be replaced by its image.  In the marked coordinates the same
reparametrisation must move the two marked parameters, and it moves them by the
Möbius map `t ↦ t/(1 − c t)` (`Chain.markedLocus_shear`), which is *not*
polynomial: no reparametrisation of `ℙ¹` that moves a finite member to infinity
is affine on the parameter.

The device is the graph.  Over the basic open where the denominators are
invertible, the shear becomes the polynomial map `markedShear` of
`Geometry.graphSet C (r · shearDenom c)` — one extra coordinate inverting
`r · (1 − c t₁)(1 − c t₂)` turns each `1/(1 − c t_i)` into a polynomial — and
that map is injective there (`markedShear_injOn`), so
`Geometry.affineDim_of_finite_fibres_locClosed` gives its image the dimension of
the graph, which is that of the component.

Consequently the shear is used *once*, inside `exists_markedTypeAtInf`, and only
to prove a dimension statement: the part of `Ŷ` where the member at infinity has
type `τ` (cut out by one nonvanishing minor per `k`, `markedMinor`) already has
the full dimension of `Ŷ`.  The component is then taken inside *that*
constructible set, and the generic type at infinity comes for free at the
tangent-generic point, exactly as the minors do on the (H1) side.
-/

namespace Height.Chain

open Matrix Height.Pencil Height.Steenrod Height.Orbital
open Height.Toolbox (cOf)
open Height.Geometry (affineDim graphSet markedCoords MarkedIndex PairIndex pairCoords projSum
  SIIndex siCoords
  fstMat sndMat)

section Shear

variable {K : Type} [Field K] {n : ℕ}

/-- There are two marked parameters. -/
theorem mark_eq_zero_or_one (i : Fin 2) : i = 0 ∨ i = 1 := by
  have hlt := i.isLt
  have h : i.val = 0 ∨ i.val = 1 := by omega
  exact h.imp Fin.ext Fin.ext

/-- The marked parameter other than `i`. -/
def otherMark : Fin 2 → Fin 2 := ![1, 0]

@[simp] theorem otherMark_zero : otherMark 0 = 1 := rfl

@[simp] theorem otherMark_one : otherMark 1 = 0 := rfl

/-- The product of the two denominators of the marked lower shear,
`(1 − c t₁)(1 − c t₂)`: the shear at `c` is defined exactly on `D(shearDenom c)`,
the complement of the two hyperplanes on which a marked parameter is the one the
shear sends to infinity. -/
noncomputable def shearDenom (c : K) : MvPolynomial (MarkedIndex (Fin n)) K :=
  (1 - MvPolynomial.C c * MvPolynomial.X (Sum.inr 0)) *
    (1 - MvPolynomial.C c * MvPolynomial.X (Sum.inr 1))

/-- The value of the two denominators at a point of the marked space. -/
theorem aeval_shearDenom (c : K) (x : MarkedIndex (Fin n) → K) :
    MvPolynomial.aeval x (shearDenom c)
      = (1 - c * x (Sum.inr 0)) * (1 - c * x (Sum.inr 1)) := by
  simp [shearDenom]

/-- **The marked lower shear on the graph**, as a tuple of polynomials.  The
matrix half is the linear shear `(N, M) ↦ (N, M + c N)`; the parameter half is
`t_i ↦ t_i · s · r · (1 − c t_{3−i})`, which on the graph
`s · r · (1 − c t₁)(1 − c t₂) = 1` is the Möbius map `t_i ↦ t_i/(1 − c t_i)` of
`Chain.markedLocus_shear`. -/
noncomputable def markedShearPoly (c : K) (r : MvPolynomial (MarkedIndex (Fin n)) K) :
    MarkedIndex (Fin n) → MvPolynomial (MarkedIndex (Fin n) ⊕ Unit) K
  | Sum.inl (Sum.inl ij) => MvPolynomial.X (Sum.inl (Sum.inl (Sum.inl ij)))
  | Sum.inl (Sum.inr ij) => MvPolynomial.X (Sum.inl (Sum.inl (Sum.inr ij)))
      + MvPolynomial.C c * MvPolynomial.X (Sum.inl (Sum.inl (Sum.inl ij)))
  | Sum.inr i => MvPolynomial.X (Sum.inl (Sum.inr i)) * MvPolynomial.X (Sum.inr ())
      * MvPolynomial.rename Sum.inl r
      * (1 - MvPolynomial.C c * MvPolynomial.X (Sum.inl (Sum.inr (otherMark i))))

/-- The marked lower shear on the graph of `1/(r · shearDenom c)`. -/
noncomputable def markedShear (c : K) (r : MvPolynomial (MarkedIndex (Fin n)) K)
    (z : MarkedIndex (Fin n) ⊕ Unit → K) : MarkedIndex (Fin n) → K :=
  fun j => MvPolynomial.aeval z (markedShearPoly c r j)

/-- The shear is a polynomial map: it is `aeval` at `markedShearPoly` by
definition.  This is the whole point of passing to the graph. -/
theorem isPolyMap_markedShear (c : K) (r : MvPolynomial (MarkedIndex (Fin n)) K) :
    Height.Geometry.IsPolyMap (markedShear c r) :=
  ⟨markedShearPoly c r, fun _ _ => rfl⟩

/-- The shear does not move the `N`-entries. -/
@[simp] theorem markedShear_inl_inl (c : K) (r : MvPolynomial (MarkedIndex (Fin n)) K)
    (z : MarkedIndex (Fin n) ⊕ Unit → K) (ij : Fin n × Fin n) :
    markedShear c r z (Sum.inl (Sum.inl ij)) = projSum z (Sum.inl (Sum.inl ij)) := by
  simp [markedShear, markedShearPoly, projSum]

/-- The shear adds `c` times the `N`-entry to the `M`-entry. -/
@[simp] theorem markedShear_inl_inr (c : K) (r : MvPolynomial (MarkedIndex (Fin n)) K)
    (z : MarkedIndex (Fin n) ⊕ Unit → K) (ij : Fin n × Fin n) :
    markedShear c r z (Sum.inl (Sum.inr ij))
      = projSum z (Sum.inl (Sum.inr ij)) + c * projSum z (Sum.inl (Sum.inl ij)) := by
  simp [markedShear, markedShearPoly, projSum]

/-- The shear on the marked parameters, before the graph relation is used to
recognise it as `t ↦ t/(1 − c t)`. -/
theorem markedShear_inr (c : K) (r : MvPolynomial (MarkedIndex (Fin n)) K)
    (z : MarkedIndex (Fin n) ⊕ Unit → K) (i : Fin 2) :
    markedShear c r z (Sum.inr i)
      = projSum z (Sum.inr i) * z (Sum.inr ()) * MvPolynomial.aeval (projSum z) r
        * (1 - c * projSum z (Sum.inr (otherMark i))) := by
  simp only [markedShear, markedShearPoly, map_mul, map_sub, map_one, MvPolynomial.aeval_X,
    MvPolynomial.aeval_C, MvPolynomial.aeval_rename]
  rfl

/-- The `N`-half of a point of the marked space is untouched by the shear. -/
theorem pairMatN_markedShear (c : K) (r : MvPolynomial (MarkedIndex (Fin n)) K)
    (z : MarkedIndex (Fin n) ⊕ Unit → K) :
    pairMatN (markedDirPair (markedShear c r z)) = pairMatN (markedDirPair (projSum z)) :=
  Matrix.ext fun _ _ => by simp [markedDirPair]

/-- The shear adds `c N` to the member at infinity. -/
theorem pairMatM_markedShear (c : K) (r : MvPolynomial (MarkedIndex (Fin n)) K)
    (z : MarkedIndex (Fin n) ⊕ Unit → K) :
    pairMatM (markedDirPair (markedShear c r z))
      = pairMatM (markedDirPair (projSum z)) + c • pairMatN (markedDirPair (projSum z)) :=
  Matrix.ext fun _ _ => by simp [markedDirPair]

/-- The denominators are invertible on the graph. -/
theorem shearDenom_ne_zero_of_mem_graphSet {c : K} {r : MvPolynomial (MarkedIndex (Fin n)) K}
    {Z : Set (MarkedIndex (Fin n) → K)} {z : MarkedIndex (Fin n) ⊕ Unit → K}
    (hz : z ∈ graphSet Z (r * shearDenom c)) (i : Fin 2) :
    1 - c * projSum z (Sum.inr i) ≠ 0 := by
  obtain ⟨-, hgr⟩ := hz
  rw [map_mul, aeval_shearDenom] at hgr
  intro hj
  rcases mark_eq_zero_or_one i with rfl | rfl <;> rw [hj] at hgr <;> simp at hgr

/-- On the graph the parameter half of the shear is the Möbius map
`t ↦ t/(1 − c t)`. -/
theorem markedShear_inr_eq_div {c : K} {r : MvPolynomial (MarkedIndex (Fin n)) K}
    {Z : Set (MarkedIndex (Fin n) → K)} {z : MarkedIndex (Fin n) ⊕ Unit → K}
    (hz : z ∈ graphSet Z (r * shearDenom c)) (i : Fin 2) :
    markedShear c r z (Sum.inr i)
      = projSum z (Sum.inr i) / (1 - c * projSum z (Sum.inr i)) := by
  have hden := fun j => shearDenom_ne_zero_of_mem_graphSet hz j
  obtain ⟨-, hgr⟩ := hz
  rw [map_mul, aeval_shearDenom] at hgr
  rw [markedShear_inr, eq_div_iff (hden i)]
  rcases mark_eq_zero_or_one i with rfl | rfl
  · rw [otherMark_zero]
    linear_combination projSum z (Sum.inr 0) * hgr
  · rw [otherMark_one]
    linear_combination projSum z (Sum.inr 1) * hgr

/-- The polynomial `r` is invertible on the graph. -/
theorem aeval_ne_zero_of_mem_graphSet {c : K} {r : MvPolynomial (MarkedIndex (Fin n)) K}
    {Z : Set (MarkedIndex (Fin n) → K)} {z : MarkedIndex (Fin n) ⊕ Unit → K}
    (hz : z ∈ graphSet Z (r * shearDenom c)) :
    MvPolynomial.aeval (projSum z) r ≠ 0 := by
  obtain ⟨-, hgr⟩ := hz
  rw [map_mul] at hgr
  intro h
  rw [h] at hgr
  simp at hgr

/-- **The shear is injective on the graph.**  The matrix half is the linear
shear, and `t ↦ t/(1 − c t)` is injective where its denominator is invertible;
the graph coordinate is then determined by its base point.  This is what
`Geometry.affineDim_of_finite_fibres_locClosed` consumes. -/
theorem markedShear_injOn (c : K) (r : MvPolynomial (MarkedIndex (Fin n)) K)
    (Z : Set (MarkedIndex (Fin n) → K)) :
    Set.InjOn (markedShear c r) (graphSet Z (r * shearDenom c)) := by
  intro z hz z' hz' heq
  have hbase : projSum z = projSum z' := by
    funext j
    rcases j with (ij | ij) | i
    · have h := congrFun heq (Sum.inl (Sum.inl ij))
      rwa [markedShear_inl_inl, markedShear_inl_inl] at h
    · have h := congrFun heq (Sum.inl (Sum.inr ij))
      rw [markedShear_inl_inr, markedShear_inl_inr] at h
      have hN := congrFun heq (Sum.inl (Sum.inl ij))
      rw [markedShear_inl_inl, markedShear_inl_inl] at hN
      rw [hN] at h
      exact add_right_cancel h
    · have h := congrFun heq (Sum.inr i)
      rw [markedShear_inr_eq_div hz, markedShear_inr_eq_div hz',
        div_eq_div_iff (shearDenom_ne_zero_of_mem_graphSet hz i)
          (shearDenom_ne_zero_of_mem_graphSet hz' i)] at h
      linear_combination h
  funext j
  rcases j with j | u
  · have h : projSum z j = projSum z' j := by rw [hbase]
    exact h
  · cases u
    obtain ⟨-, hgr⟩ := hz
    obtain ⟨-, hgr'⟩ := hz'
    rw [hbase] at hgr
    have hg : MvPolynomial.aeval (projSum z') (r * shearDenom c) ≠ 0 := by
      intro h
      rw [h, mul_zero] at hgr'
      exact zero_ne_one hgr'
    exact mul_right_cancel₀ hg (hgr.trans hgr'.symm)

end Shear

/-! ### The member at infinity, in the marked coordinates -/

section Minors

variable {K : Type} [Field K] {n : ℕ}

/-- A point of the marked space, unpacked: the two matrices and the two
parameters. -/
theorem markedCoords_symm_eq (x : MarkedIndex (Fin n) → K) :
    markedCoords.symm x
      = (pairMatN (markedDirPair x), pairMatM (markedDirPair x),
          x (Sum.inr 0), x (Sum.inr 1)) := rfl

/-- Membership of `Ŷ` in the marked coordinates. -/
theorem mem_image_markedLocus_iff {τ : Nat.Partition n} {d : ℕ → ℕ}
    {N₀ : Matrix (Fin n) (Fin n) K} (x : MarkedIndex (Fin n) → K) :
    x ∈ markedCoords '' markedLocus τ d N₀ ↔ markedCoords.symm x ∈ markedLocus τ d N₀ := by
  rw [markedCoords.image_eq_preimage_symm]
  exact Iff.rfl

/-- The member at infinity of the pencil sheared by `c`, as a matrix of
coordinate polynomials on the marked space: `M + c N`. -/
noncomputable def genMarkedShiftM (c : K) :
    Matrix (Fin n) (Fin n) (MvPolynomial (MarkedIndex (Fin n)) K) :=
  coordMat (K := K) (fun ij : Fin n × Fin n => (Sum.inl (Sum.inr ij) : MarkedIndex (Fin n)))
    + c • coordMat (K := K) (fun ij : Fin n × Fin n => (Sum.inl (Sum.inl ij) : MarkedIndex (Fin n)))

/-- The generic sheared member at infinity specialises to `M + c N`. -/
theorem map_genMarkedShiftM (c : K) (x : MarkedIndex (Fin n) → K) :
    (genMarkedShiftM c).map (MvPolynomial.aeval x)
      = pairMatM (markedDirPair x) + c • pairMatN (markedDirPair x) :=
  Matrix.ext fun i j => by
    simp [genMarkedShiftM, coordMat, markedDirPair, Matrix.add_apply, Matrix.smul_apply]

/-- Its powers specialise to the powers of `M + c N`. -/
theorem map_genMarkedShiftM_pow (c : K) (x : MarkedIndex (Fin n) → K) (k : ℕ) :
    ((genMarkedShiftM c) ^ k).map (MvPolynomial.aeval x)
      = (pairMatM (markedDirPair x) + c • pairMatN (markedDirPair x)) ^ k := by
  have h : ((MvPolynomial.aeval x : MvPolynomial (MarkedIndex (Fin n)) K →ₐ[K] K).mapMatrix :
      Matrix (Fin n) (Fin n) (MvPolynomial (MarkedIndex (Fin n)) K) →ₐ[K] _)
      ((genMarkedShiftM c) ^ k)
      = ((MvPolynomial.aeval x).mapMatrix (genMarkedShiftM c)) ^ k := map_pow _ _ _
  rw [AlgHom.mapMatrix_apply, AlgHom.mapMatrix_apply, map_genMarkedShiftM] at h
  exact h

/-- A minor of a power of `M + c N`, as a polynomial on the marked space.  At
`c = 0` these are the minors of the member at infinity itself, whose
nonvanishing is the open half of `HasType (pairMatM (markedDirPair x)) τ`
(`Chain.hasType_of_le_rank_pow`); at a general `c` they are the same minors read
through the shear. -/
noncomputable def markedMinor (c : K) (k r : ℕ) (f g : Fin r → Fin n) :
    MvPolynomial (MarkedIndex (Fin n)) K :=
  (((genMarkedShiftM c) ^ k).submatrix f g).det

/-- The value of a marked minor: the corresponding minor of `(M + c N)^k`. -/
theorem eval_markedMinor (c : K) (k r : ℕ) (f g : Fin r → Fin n)
    (x : MarkedIndex (Fin n) → K) :
    MvPolynomial.eval x (markedMinor c k r f g)
      = (((pairMatM (markedDirPair x) + c • pairMatN (markedDirPair x)) ^ k).submatrix
          f g).det := by
  rw [markedMinor, ← MvPolynomial.aeval_eq_eval, AlgHom.map_det, AlgHom.mapMatrix_apply,
    ← Matrix.submatrix_map, map_genMarkedShiftM_pow]

/-- At `c = 0` a marked minor is a minor of a power of the member at infinity
itself. -/
theorem eval_markedMinor_zero (k r : ℕ) (f g : Fin r → Fin n)
    (x : MarkedIndex (Fin n) → K) :
    MvPolynomial.eval x (markedMinor 0 k r f g)
      = (((pairMatM (markedDirPair x)) ^ k).submatrix f g).det := by
  rw [eval_markedMinor]
  simp

/-- One minor per `k`, multiplied together: the open condition on the marked
space that forces the member at infinity of a point of `Ŷ` to have type `τ`. -/
noncomputable def typeAtInfPoly (τ : Nat.Partition n)
    (fg : ∀ k : ℕ, (Fin (n - mk τ k) → Fin n) × (Fin (n - mk τ k) → Fin n)) :
    MvPolynomial (MarkedIndex (Fin n)) K :=
  ∏ k ∈ Finset.Icc 1 n, markedMinor (0 : K) k (n - mk τ k) (fg k).1 (fg k).2

/-- **The generic type at infinity is an open condition on `Ŷ`.**  On the locus
the inequality `n − m_k ≤ rank (M^k)` is the whole of `HasType M τ`
(`Chain.hasType_of_le_rank_pow`: the other one is automatic), and one nonzero
minor per `k` is that inequality. -/
theorem hasType_of_typeAtInfPoly_ne_zero [Infinite K] {τ : Nat.Partition n} {d : ℕ → ℕ}
    {N₀ : Matrix (Fin n) (Fin n) K}
    {fg : ∀ k : ℕ, (Fin (n - mk τ k) → Fin n) × (Fin (n - mk τ k) → Fin n)}
    {x : MarkedIndex (Fin n) → K} (hx : x ∈ markedCoords '' markedLocus τ d N₀)
    (hP : MvPolynomial.eval x (typeAtInfPoly (K := K) τ fg) ≠ 0) :
    HasType (pairMatM (markedDirPair x)) τ := by
  rw [mem_image_markedLocus_iff, markedCoords_symm_eq] at hx
  refine hasType_of_le_rank_pow hx.1.2.1 fun k hk1 hkn => ?_
  refine Height.Toolbox.le_rank_of_submatrix_det_ne_zero _ (fg k).1 (fg k).2 fun h0 => hP ?_
  rw [typeAtInfPoly, map_prod]
  refine Finset.prod_eq_zero (Finset.mem_Icc.2 ⟨hk1, hkn⟩) ?_
  rw [eval_markedMinor_zero]
  exact h0

end Minors

/-! ### The shear step -/

section TypeAtInf

variable {K : Type} [Field K] {n : ℕ}

/-- **The shear step of `thm:h2-conditional`** (the marked analogue of
step 2 of `exists_pencilComponent_arcTangent`).

The part of `Ŷ` on which the member at infinity has the generic type — cut out
by one minor per `k`, `typeAtInfPoly` — already has the dimension of `Ŷ`.

Route.  Take a piece `C ∩ D(q)` of `Ŷ` of maximal dimension
(`Geometry.constructible_irreducible_pieces` on `isConstructible_markedLocus`,
`affineDim_inter_dense`) and a point `w₀` of it; at a parameter `t` off the
finite bad set of the pencil of `w₀` — and off the two marked parameters of
`w₀`, which is the new exclusion — the member has type `τ`, so the lower shear
at `c = t⁻¹` puts a member of type `τ` at infinity.  That shear is *not*
polynomial on the marked space: it moves the marked parameters by
`t ↦ t/(1 − c t)` (`Chain.markedLocus_shear`).  It becomes polynomial on the
graph of `1/(r · (1 − c t₁)(1 − c t₂))`, where `r` collects `q` and the minors
of the sheared member at infinity that are nonzero at `w₀`; on that graph it is
`markedShear`, it is injective (`markedShear_injOn`), and its image lies in `Ŷ`
(`markedLocus_shear`) inside `D(typeAtInfPoly)` (the minors are factors of `r`).
`Geometry.affineDim_of_finite_fibres_locClosed` then gives the image the
dimension of the graph, which is that of `C ∩ D(r · shearDenom c)`, which is
that of `C` and hence of `Ŷ`. -/
theorem exists_markedTypeAtInf [IsAlgClosed K] [Infinite K]
    (τ : Nat.Partition n) (d : ℕ → ℕ) (N₀ : Matrix (Fin n) (Fin n) K)
    (hne : (markedLocus (K := K) τ d N₀).Nonempty) :
    ∃ fg : ∀ k : ℕ, (Fin (n - mk τ k) → Fin n) × (Fin (n - mk τ k) → Fin n),
      affineDim (markedCoords '' markedLocus (K := K) τ d N₀)
        ≤ affineDim (markedCoords '' markedLocus (K := K) τ d N₀ ∩
            {x | MvPolynomial.aeval x (typeAtInfPoly (K := K) τ fg) ≠ 0}) := by
  classical
  -- a piece of maximal dimension, and a point of it
  obtain ⟨J, hJ, C, q, hCprime, hCcl, hcov⟩ :=
    Height.Geometry.constructible_irreducible_pieces
      (isConstructible_markedLocus (K := K) τ d N₀)
  have _ : Finite J := hJ
  obtain ⟨y₀, hy₀⟩ : (markedCoords '' markedLocus (K := K) τ d N₀).Nonempty := hne.image _
  obtain ⟨a₀, -⟩ := Set.mem_iUnion.1 (hcov ▸ hy₀)
  have _ : Nonempty J := ⟨a₀⟩
  obtain ⟨a, hmax⟩ := Finite.exists_max
    fun j : J => affineDim (C j ∩ {y | MvPolynomial.aeval y (q j) ≠ 0})
  have hdimpiece : affineDim (markedCoords '' markedLocus (K := K) τ d N₀)
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
  have hdimC : affineDim (markedCoords '' markedLocus (K := K) τ d N₀) = affineDim (C a) := by
    rw [hdimpiece, Height.Geometry.affineDim_inter_dense (hCprime a) hqa]
  have hpiece_sub : C a ∩ {y | MvPolynomial.aeval y (q a) ≠ 0}
      ⊆ markedCoords '' markedLocus (K := K) τ d N₀ := fun y hy => by
    rw [hcov]; exact Set.mem_iUnion.2 ⟨a, hy⟩
  have hw₀Y : markedCoords.symm w₀ ∈ markedLocus (K := K) τ d N₀ :=
    (mem_image_markedLocus_iff w₀).1 (hpiece_sub ⟨hw₀C, hw₀q⟩)
  -- the parameter that is moved to infinity: generic, and not a marked one
  obtain ⟨F, hF⟩ := hw₀Y.1.2.1
  obtain ⟨t, ht⟩ : ∃ t : K,
      t ∉ insert (0 : K) (insert (w₀ (Sum.inr 0)) (insert (w₀ (Sum.inr 1)) F)) := by
    obtain ⟨t, ht⟩ := Set.Infinite.nonempty
      ((((insert (0 : K) (insert (w₀ (Sum.inr 0)) (insert (w₀ (Sum.inr 1)) F))
        : Finset K)) : Set K).toFinite.infinite_compl)
    exact ⟨t, by simpa using ht⟩
  simp only [Finset.mem_insert, not_or] at ht
  obtain ⟨ht0, ht₁, ht₂, htF⟩ := ht
  set c : K := t⁻¹ with hcdef
  have hc0 : c ≠ 0 := inv_ne_zero ht0
  have hden₀ : ∀ i : Fin 2, 1 - c * w₀ (Sum.inr i) ≠ 0 := by
    intro i h
    have h1 : c * w₀ (Sum.inr i) = 1 := by linear_combination -h
    have h2 : w₀ (Sum.inr i) = t := by
      rw [hcdef, inv_mul_eq_one₀ ht0] at h1
      exact h1.symm
    rcases mark_eq_zero_or_one i with rfl | rfl
    · exact ht₁ h2.symm
    · exact ht₂ h2.symm
  have htype₀ : HasType (pairMatM (markedDirPair w₀) + c • pairMatN (markedDirPair w₀)) τ := by
    have hmat : pairMatM (markedDirPair w₀) + c • pairMatN (markedDirPair w₀)
        = c • (pairMatN (markedDirPair w₀) + t • pairMatM (markedDirPair w₀)) := by
      rw [smul_add, smul_smul, hcdef, inv_mul_cancel₀ ht0, one_smul]
      abel
    rw [hmat]
    exact (hasType_smul hc0).mpr (hF t htF)
  -- one nonzero minor of each power of the sheared member at infinity
  have hminor : ∀ k : ℕ, ∃ fg : (Fin (n - mk τ k) → Fin n) × (Fin (n - mk τ k) → Fin n),
      MvPolynomial.eval w₀ (markedMinor c k (n - mk τ k) fg.1 fg.2) ≠ 0 := by
    intro k
    have hrk : n - mk τ k
        ≤ Matrix.rank ((pairMatM (markedDirPair w₀) + c • pairMatN (markedDirPair w₀)) ^ k) := by
      by_cases hk : 1 ≤ k ∧ k ≤ n
      · have h := hasType_iff_rank_le.mp htype₀ k hk.1 hk.2
        omega
      · rcases Nat.eq_zero_or_pos k with rfl | hk1
        · rw [mk_zero, pow_zero, Nat.sub_zero]
          have h1 : Matrix.rank (1 : Matrix (Fin n) (Fin n) K) = n := by simp
          omega
        · rw [mk_eq_of_le (by omega : n ≤ k)]
          simp
    obtain ⟨f₀, g₀, hfg⟩ := Height.Toolbox.exists_submatrix_det_ne_zero _ hrk
    exact ⟨(f₀, g₀), by rw [eval_markedMinor]; exact hfg⟩
  choose fg hfg using hminor
  refine ⟨fg, ?_⟩
  -- the polynomial inverted on the graph: the piece's own `q` and those minors
  set r : MvPolynomial (MarkedIndex (Fin n)) K :=
    q a * ∏ k ∈ Finset.Icc 1 n, markedMinor c k (n - mk τ k) (fg k).1 (fg k).2 with hrdef
  have hr₀ : MvPolynomial.aeval w₀ r ≠ 0 := by
    rw [hrdef, map_mul, map_prod]
    refine mul_ne_zero hw₀q (Finset.prod_ne_zero_iff.2 fun k _ => ?_)
    rw [MvPolynomial.aeval_eq_eval]
    exact hfg k
  have hgI : r * shearDenom c ∉ MvPolynomial.vanishingIdeal K (C a) := by
    refine fun hmem => ?_
    have h0 : MvPolynomial.aeval w₀ (r * shearDenom c) = 0 := hmem _ hw₀C
    rw [map_mul, aeval_shearDenom] at h0
    exact (mul_ne_zero hr₀ (mul_ne_zero (hden₀ 0) (hden₀ 1))) h0
  set S : Set (MarkedIndex (Fin n) ⊕ Unit → K) := graphSet (C a) (r * shearDenom c) with hSdef
  have hScl : Height.Geometry.zclosure S = S := Height.Geometry.zclosure_graphSet (hCcl a) _
  have hSdim : affineDim S = affineDim (C a) := by
    rw [hSdef, Height.Geometry.affineDim_graphSet (hCcl a),
      Height.Geometry.affineDim_inter_dense (hCprime a) hgI]
  -- the sheared piece lies in `Ŷ`, with the generic type at infinity
  have hsub : markedShear c r '' S
      ⊆ markedCoords '' markedLocus (K := K) τ d N₀ ∩
          {x | MvPolynomial.aeval x (typeAtInfPoly (K := K) τ fg) ≠ 0} := by
    rintro _ ⟨z, hz, rfl⟩
    have hrne : MvPolynomial.aeval (projSum z) r ≠ 0 := aeval_ne_zero_of_mem_graphSet hz
    have hqne : MvPolynomial.aeval (projSum z) (q a) ≠ 0 := by
      rw [hrdef, map_mul] at hrne
      exact left_ne_zero_of_mul hrne
    have hxY : markedCoords.symm (projSum z) ∈ markedLocus (K := K) τ d N₀ :=
      (mem_image_markedLocus_iff _).1 (hpiece_sub ⟨hz.1, hqne⟩)
    have hden : ∀ i : Fin 2, 1 - c * projSum z (Sum.inr i) ≠ 0 :=
      fun i => shearDenom_ne_zero_of_mem_graphSet hz i
    have hshear := markedLocus_shear (τ := τ) (d := d) (N₀ := N₀) c (hden 0) (hden 1) hxY
    have heq : markedCoords.symm (markedShear c r z)
        = ((markedCoords.symm (projSum z)).1,
            (markedCoords.symm (projSum z)).2.1 + c • (markedCoords.symm (projSum z)).1,
            (markedCoords.symm (projSum z)).2.2.1 /
              (1 - c * (markedCoords.symm (projSum z)).2.2.1),
            (markedCoords.symm (projSum z)).2.2.2 /
              (1 - c * (markedCoords.symm (projSum z)).2.2.2)) := by
      rw [markedCoords_symm_eq, markedCoords_symm_eq, pairMatN_markedShear, pairMatM_markedShear,
        markedShear_inr_eq_div hz 0, markedShear_inr_eq_div hz 1]
    refine ⟨(mem_image_markedLocus_iff _).2 (by rw [heq]; exact hshear), ?_⟩
    show MvPolynomial.aeval (markedShear c r z) (typeAtInfPoly τ fg) ≠ 0
    rw [typeAtInfPoly, map_prod]
    refine Finset.prod_ne_zero_iff.2 fun k hk => ?_
    rw [MvPolynomial.aeval_eq_eval, eval_markedMinor_zero, pairMatM_markedShear,
      ← eval_markedMinor]
    intro h0
    refine hrne ?_
    rw [hrdef, map_mul, map_prod,
      Finset.prod_eq_zero hk (by rw [MvPolynomial.aeval_eq_eval]; exact h0), mul_zero]
  -- the shear is injective on the graph, so the image has the graph's dimension
  have hfin : ∀ x ∈ markedShear c r '' S, (S ∩ markedShear c r ⁻¹' {x}).Finite := by
    intro x _
    refine Set.Subsingleton.finite fun z hz z' hz' => ?_
    exact markedShear_injOn c r (C a) hz.1 hz'.1 (hz.2.trans hz'.2.symm)
  have himgdim : affineDim S = affineDim (markedShear c r '' S) :=
    Height.Geometry.affineDim_of_finite_fibres_locClosed (isPolyMap_markedShear c r) S _
      (Height.Geometry.IsLocClosed.of_zclosure hScl) rfl hfin
  calc affineDim (markedCoords '' markedLocus (K := K) τ d N₀)
      = affineDim (C a) := hdimC
    _ = affineDim S := hSdim.symm
    _ = affineDim (markedShear c r '' S) := himgdim
    _ ≤ _ := Height.Geometry.affineDim_mono hsub

end TypeAtInf

/-! ### The component and its tangent-generic point -/

section Hyps

variable {K : Type} [Field K] {n : ℕ}

variable (K n) in
/-- An irreducible component `V(I)` of (the closure of) the marked locus `Ŷ`,
with a dense open `V(I) ∩ D(q)` of it inside the locus.  The two-parameter
analogue of `PencilComponent`. -/
structure MarkedComponent (τ : Nat.Partition n) (d : ℕ → ℕ)
    (N₀ : Matrix (Fin n) (Fin n) K) where
  /-- the prime of the component -/
  I : Ideal (MvPolynomial (MarkedIndex (Fin n)) K)
  prime : I.IsPrime
  /-- the function cutting out the dense open -/
  q : MvPolynomial (MarkedIndex (Fin n)) K
  notMem : q ∉ I
  /-- the open `V(I) ∩ D(q)` lies in `Ŷ` -/
  locus : ∀ w ∈ MvPolynomial.zeroLocus K I, MvPolynomial.eval w q ≠ 0 →
    markedCoords.symm w ∈ markedLocus τ d N₀

/-- A tangent-generic point of a marked component, off a further hypersurface
`V(g)`: a point `w` of the dense open whose member at infinity has the generic
type, carrying a space `T` of directions each the velocity of an arc of `V(I)`
based at `w`, with `dim Ŷ ≤ dim T`.

The two-parameter analogue of `ArcTangentPoint`.  The arcs are the raw
`Geometry.Arc`s: the marked space has no `IsArcIn`, and the three arc structures
`thm:h2-conditional` consumes (`PencilArcData` and a `Pencil.MemberArc` at each
marked point, `Chain/H2.lean`) are built from these. -/
structure MarkedArcTangentPoint {τ : Nat.Partition n} {d : ℕ → ℕ}
    {N₀ : Matrix (Fin n) (Fin n) K} (C : MarkedComponent K n τ d N₀)
    (g : MvPolynomial (MarkedIndex (Fin n)) K) where
  /-- the point -/
  w : MarkedIndex (Fin n) → K
  /-- the space of directions -/
  T : Submodule K (MarkedIndex (Fin n) → K)
  mem : w ∈ MvPolynomial.zeroLocus K C.I
  q_ne : MvPolynomial.eval w C.q ≠ 0
  g_ne : MvPolynomial.eval w g ≠ 0
  /-- the member at infinity has the generic type -/
  type : HasType (pairMatM (markedDirPair w)) τ
  /-- every direction in `T` is the velocity of an arc of `V(I)` at `w` -/
  arcs : ∀ v ∈ T, ∃ a : Height.Geometry.Arc C.I, a.base = w ∧ a.vel = v
  /-- the dense-open half of the variety input of `thm:h2-conditional`:
  `dim Ŷ ≤ dim T` -/
  affineDim_le : affineDim (markedCoords '' markedLocus τ d N₀)
    ≤ ((Module.finrank K T : ℕ) : WithBot ℕ∞)

end Hyps

/-! ### The variety half of `thm:h2-conditional` -/

section Variety

variable {K : Type} [Field K] {n : ℕ}

/-- **The variety half of `thm:h2-conditional`**,
the two-parameter analogue of `exists_pencilComponent_arcTangent`.

For a nonempty `Ŷ = markedLocus τ d N₀` there is an irreducible `V(I)` and a
`q ∉ I` such that `V(I) ∖ V(q)` lies in `Ŷ` and `dim Ŷ ≤ dim V(I)`, and, for
every further nonvanishing condition `g ∉ I`, a point `w` of `V(I)` off `V(q)`
and off `V(g)` whose member at infinity has the generic type, carrying a space
`T` of directions each the velocity of an arc of `V(I)` based at `w`, with
`dim Ŷ ≤ dim T`.

Route.  `exists_markedTypeAtInf` does the shear, and delivers the minors `fg`
whose product `typeAtInfPoly τ fg` cuts out of `Ŷ` a constructible set `W` of
the full dimension of `Ŷ` on which the member at infinity has type `τ`.  The
component is then a piece of `W` of maximal dimension
(`Geometry.constructible_irreducible_pieces`, `affineDim_inter_dense`), and
`Geometry.exists_tangentGeneric_pt` at it — with `q`, `g` and
`typeAtInfPoly τ fg` as the nonvanishing conditions — gives the point, the
dimension bound and the arcs; the type at infinity is
`hasType_of_typeAtInfPoly_ne_zero`.

The nonemptiness hypothesis is necessary and not implied by `d ≠ 0`, for the
reason recorded at `exists_siComponents_realizedBounds`: the conclusion produces
a `K`-point of `Ŷ`, so it is false whenever `Ŷ` is empty. -/
theorem exists_markedComponent_arcTangent [IsAlgClosed K] [Infinite K]
    (τ : Nat.Partition n) (d : ℕ → ℕ) (N₀ : Matrix (Fin n) (Fin n) K)
    (hne : (markedLocus (K := K) τ d N₀).Nonempty) :
    ∃ C : MarkedComponent K n τ d N₀, ∀ g ∉ C.I, Nonempty (MarkedArcTangentPoint C g) := by
  classical
  obtain ⟨fg, hdimW⟩ := exists_markedTypeAtInf τ d N₀ hne
  set P : MvPolynomial (MarkedIndex (Fin n)) K := typeAtInfPoly τ fg with hPdef
  set W : Set (MarkedIndex (Fin n) → K) :=
    markedCoords '' markedLocus (K := K) τ d N₀ ∩ {x | MvPolynomial.aeval x P ≠ 0} with hWdef
  have hWc : Height.Geometry.IsAffineConstructible W :=
    (isConstructible_markedLocus τ d N₀).inter (isLocClosed_principalOpen P).isConstructible
  -- a piece of `W` of maximal dimension
  obtain ⟨J, hJ, C, q, hCprime, hCcl, hcov⟩ :=
    Height.Geometry.constructible_irreducible_pieces hWc
  have _ : Finite J := hJ
  have hYbot : affineDim (markedCoords '' markedLocus (K := K) τ d N₀) ≠ ⊥ := by
    rw [Ne, Height.Geometry.affineDim_eq_bot_iff]
    exact (hne.image _).ne_empty
  have hbot : ∀ S : Set (MarkedIndex (Fin n) → K),
      affineDim (markedCoords '' markedLocus (K := K) τ d N₀) ≤ affineDim S → S.Nonempty := by
    intro S hS
    rcases Set.eq_empty_or_nonempty S with rfl | h
    · rw [Height.Geometry.affineDim_empty, le_bot_iff] at hS
      exact absurd hS hYbot
    · exact h
  obtain ⟨y₀, hy₀⟩ := hbot W hdimW
  obtain ⟨a₀, -⟩ := Set.mem_iUnion.1 (hcov ▸ hy₀)
  have _ : Nonempty J := ⟨a₀⟩
  obtain ⟨a, hmax⟩ := Finite.exists_max
    fun j : J => affineDim (C j ∩ {y | MvPolynomial.aeval y (q j) ≠ 0})
  have hdimpiece : affineDim W = affineDim (C a ∩ {y | MvPolynomial.aeval y (q a) ≠ 0}) := by
    rw [hcov, Height.Geometry.affineDim_iUnion]
    exact le_antisymm (iSup_le hmax)
      (le_iSup (fun j : J => affineDim (C j ∩ {y | MvPolynomial.aeval y (q j) ≠ 0})) a)
  obtain ⟨w₀, hw₀C, hw₀q⟩ := hbot _ (hdimW.trans hdimpiece.le)
  have hqa : q a ∉ MvPolynomial.vanishingIdeal K (C a) := fun hmem => hw₀q (hmem _ hw₀C)
  have hpiece_sub : C a ∩ {y | MvPolynomial.aeval y (q a) ≠ 0} ⊆ W := fun y hy => by
    rw [hcov]; exact Set.mem_iUnion.2 ⟨a, hy⟩
  have hPa : P ∉ MvPolynomial.vanishingIdeal K (C a) :=
    fun hmem => (hpiece_sub ⟨hw₀C, hw₀q⟩).2 (hmem _ hw₀C)
  have hdimC : affineDim (markedCoords '' markedLocus (K := K) τ d N₀) ≤ affineDim (C a) := by
    refine hdimW.trans ?_
    rw [hdimpiece, Height.Geometry.affineDim_inter_dense (hCprime a) hqa]
  have hzero : MvPolynomial.zeroLocus K (MvPolynomial.vanishingIdeal K (C a)) = C a := hCcl a
  have hlocus : ∀ w ∈ MvPolynomial.zeroLocus K (MvPolynomial.vanishingIdeal K (C a)),
      MvPolynomial.eval w (q a) ≠ 0 → markedCoords.symm w ∈ markedLocus (K := K) τ d N₀ := by
    intro w hw hwq
    have hwC : w ∈ C a := by rw [← hzero]; exact hw
    have hwq' : MvPolynomial.aeval w (q a) ≠ 0 := by rwa [MvPolynomial.aeval_eq_eval]
    exact (mem_image_markedLocus_iff w).1 (hpiece_sub ⟨hwC, hwq'⟩).1
  refine ⟨⟨MvPolynomial.vanishingIdeal K (C a), hCprime a, q a, hqa, hlocus⟩, ?_⟩
  intro g hg
  have _ : (MvPolynomial.vanishingIdeal K (C a)).IsPrime := hCprime a
  have hsI : ∀ h ∈ ({q a, g, P} : Finset (MvPolynomial (MarkedIndex (Fin n)) K)),
      h ∉ MvPolynomial.vanishingIdeal K (C a) := by
    intro h hh
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh
    rcases hh with rfl | rfl | rfl
    exacts [hqa, hg, hPa]
  obtain ⟨w, hwV, hws, hwdim, hwarcs⟩ :=
    Height.Geometry.exists_tangentGeneric_pt (MvPolynomial.vanishingIdeal K (C a)) _ hsI
  have hwq : MvPolynomial.eval w (q a) ≠ 0 := hws _ (by simp)
  have hwg : MvPolynomial.eval w g ≠ 0 := hws _ (by simp)
  have hwP : MvPolynomial.eval w P ≠ 0 := hws _ (by simp)
  refine ⟨{ w := w
            T := Height.Geometry.jacobianKernel (MvPolynomial.vanishingIdeal K (C a)) w
            mem := hwV
            q_ne := hwq
            g_ne := hwg
            type := ?_
            arcs := ?_
            affineDim_le := ?_ }⟩
  · exact hasType_of_typeAtInfPoly_ne_zero
      ((mem_image_markedLocus_iff w).2 (hlocus w hwV hwq)) hwP
  · intro v hv
    obtain ⟨arc, hbase, hvel⟩ := hwarcs v hv
    exact ⟨arc, hbase, funext hvel⟩
  · calc affineDim (markedCoords '' markedLocus (K := K) τ d N₀)
        ≤ affineDim (C a) := hdimC
      _ = affineDim (MvPolynomial.zeroLocus K (MvPolynomial.vanishingIdeal K (C a))) := by
          rw [hzero]
      _ ≤ _ := hwdim

end Variety


/-! ### The pencil half of a marked component

The two-point incidence projects three ways: to the pencil coordinates
(forgetting both marked parameters) and to the two single-point incidences
(forgetting one).  `Chain/SIComponents.lean` does the latter; this section does
the former, and the payoff is large — a `PencilComponent` under the marked one
gives an `IsArcIn` for the pencil half of every marked arc, hence
`arc_rank_eq` for the rank profile, `hasMultidegree_of_isArcIn` for the
multidegree, and `pencilR_pow_eq_zero_of_arc` for nilpotence: all three
remaining fields of `PencilArcData`. -/

section PairProjection

variable {K : Type} [Field K] {n : ℕ}

/-- The polynomials defining the pencil projection. -/
noncomputable def pairProjPoly : PairIndex (Fin n) → MvPolynomial (MarkedIndex (Fin n)) K :=
  fun j => MvPolynomial.X (Sum.inl j)

theorem markedDirPair_apply (x : MarkedIndex (Fin n) → K) (j : PairIndex (Fin n)) :
    markedDirPair x j = MvPolynomial.aeval x (pairProjPoly (K := K) (n := n) j) := by
  simp [markedDirPair, pairProjPoly]

theorem isPolyMap_markedDirPair : Height.Geometry.IsPolyMap (markedDirPair (K := K) (n := n)) :=
  ⟨pairProjPoly, markedDirPair_apply⟩

/-- Forgetting both marked points carries `Ŷ` into `Î_{τ,d}`. -/
theorem markedDirPair_mem_pencilLocus {τ : Nat.Partition n} {d : ℕ → ℕ}
    {N₀ : Matrix (Fin n) (Fin n) K} {x : MarkedIndex (Fin n) → K}
    (hx : x ∈ markedCoords '' markedLocus (K := K) τ d N₀) :
    markedDirPair x ∈ pairCoords '' pencilLocus (K := K) τ d := by
  obtain ⟨p, hp, rfl⟩ := hx
  exact ⟨(p.1, p.2.1), hp.1, rfl⟩

/-- **The pencil component under a marked component**: project, close up, read
off a dense open inside `Î_{τ,d}`.  As for the single-point incidences, the
ideal is the contraction along the projection, which is what carries arcs. -/
theorem exists_pencilComponent_of_markedComponent [IsAlgClosed K] [Infinite K]
    (τ : Nat.Partition n) (d : ℕ → ℕ) (N₀ : Matrix (Fin n) (Fin n) K)
    {I : Ideal (MvPolynomial (MarkedIndex (Fin n)) K)} (hIp : I.IsPrime)
    {q : MvPolynomial (MarkedIndex (Fin n)) K} (hq : q ∉ I)
    (hlocus : ∀ y ∈ MvPolynomial.zeroLocus K I, MvPolynomial.aeval y q ≠ 0 →
      y ∈ markedCoords '' markedLocus (K := K) τ d N₀) :
    ∃ C : PencilComponent K τ d,
      C.I = I.comap (MvPolynomial.aeval (pairProjPoly (K := K) (n := n)) :
          MvPolynomial (PairIndex (Fin n)) K →ₐ[K] MvPolynomial (MarkedIndex (Fin n)) K) ∧
      ∀ y ∈ MvPolynomial.zeroLocus K I, MvPolynomial.aeval y q ≠ 0 →
        markedDirPair y ∈ MvPolynomial.zeroLocus K C.I := by
  classical
  have hz : MvPolynomial.vanishingIdeal K (MvPolynomial.zeroLocus K I) = I :=
    MvPolynomial.IsPrime.vanishingIdeal_zeroLocus I
  have hzp : (MvPolynomial.vanishingIdeal K (MvPolynomial.zeroLocus K I)).IsPrime := by
    rw [hz]; exact hIp
  set W : Set (MarkedIndex (Fin n) → K) :=
    MvPolynomial.zeroLocus K I ∩ {y | MvPolynomial.aeval y q ≠ 0} with hWdef
  have hWne : W.Nonempty :=
    Height.Geometry.nonempty_inter_nonvanishing (by rw [hz]; exact hq)
  have hWvi : MvPolynomial.vanishingIdeal K W = I := by
    rw [hWdef, Height.Geometry.vanishingIdeal_inter_dense hzp hWne, hz]
  have hWp : (MvPolynomial.vanishingIdeal K W).IsPrime := by rw [hWvi]; exact hIp
  set V : Set (PairIndex (Fin n) → K) :=
    Height.Geometry.zclosure (markedDirPair '' W) with hVdef
  have hVcl : Height.Geometry.zclosure V = V := Height.Geometry.zclosure_zclosure _
  have hVvi : MvPolynomial.vanishingIdeal K V
      = I.comap (MvPolynomial.aeval (pairProjPoly (K := K) (n := n)) :
          MvPolynomial (PairIndex (Fin n)) K →ₐ[K] MvPolynomial (MarkedIndex (Fin n)) K) := by
    rw [hVdef, Height.Geometry.vanishingIdeal_zclosure,
      Height.Geometry.vanishingIdeal_image markedDirPair_apply W, hWvi]
  have hVp : (MvPolynomial.vanishingIdeal K V).IsPrime := by
    rw [hVdef, Height.Geometry.vanishingIdeal_zclosure]
    exact Height.Geometry.irreducible_image isPolyMap_markedDirPair hWp
  have hSsub : markedDirPair '' W ⊆ pairCoords '' pencilLocus (K := K) τ d := by
    rintro _ ⟨y, hy, rfl⟩
    exact markedDirPair_mem_pencilLocus (hlocus y hy.1 hy.2)
  have hdense : Height.Geometry.zclosure
      ((pairCoords '' pencilLocus (K := K) τ d) ∩ V) = V := by
    refine le_antisymm ?_ ?_
    · conv_rhs => rw [← hVcl]
      exact Height.Geometry.zclosure_mono Set.inter_subset_right
    · exact Height.Geometry.zclosure_mono fun x hx =>
        ⟨hSsub hx, Height.Geometry.subset_zclosure _ hx⟩
  obtain ⟨g, hgI, hgsub⟩ := Height.Geometry.exists_nonvanishing_subset_of_constructible
    (isConstructible_pencilLocus τ d) hVcl hVp hdense
  refine ⟨⟨MvPolynomial.vanishingIdeal K V, hVp, g, hgI, ?_⟩, hVvi, fun y hy hqy => ?_⟩
  · intro w hw hgw
    have hwV : w ∈ V := hVcl ▸ hw
    obtain ⟨p, hp, hpw⟩ := hgsub ⟨hwV, by
      show MvPolynomial.aeval w g ≠ 0
      rw [MvPolynomial.aeval_eq_eval]
      exact hgw⟩
    have : (pairMatN w, pairMatM w) = p := by rw [← hpw]; rfl
    rw [this]
    exact hp
  · have hmem : markedDirPair y ∈ V :=
      Height.Geometry.subset_zclosure _ ⟨y, ⟨hy, hqy⟩, rfl⟩
    show markedDirPair y ∈ Height.Geometry.zclosure V
    rw [hVcl]
    exact hmem


/-- Evaluating a pulled-back polynomial is evaluating at the projected point. -/
theorem eval_pairProjPoly (y : MarkedIndex (Fin n) → K)
    (f : MvPolynomial (PairIndex (Fin n)) K) :
    MvPolynomial.eval y (MvPolynomial.aeval (pairProjPoly (K := K) (n := n)) f)
      = MvPolynomial.eval (markedDirPair y) f := by
  have hfun : (fun j => MvPolynomial.aeval y (pairProjPoly (K := K) (n := n) j))
      = markedDirPair y := by
    funext j
    rw [← markedDirPair_apply]
  rw [← MvPolynomial.aeval_eq_eval, ← MvPolynomial.aeval_eq_eval,
    Height.Geometry.aeval_aeval, hfun]

/-- Evaluating a polynomial pulled back along the `i`-th single-point projection
is evaluating at the projected point. -/
theorem eval_siProjPoly (i : Fin 2) (y : MarkedIndex (Fin n) → K)
    (f : MvPolynomial (SIIndex (Fin n)) K) :
    MvPolynomial.eval y (MvPolynomial.aeval (siProjPoly (K := K) (n := n) i) f)
      = MvPolynomial.eval (siProj i y) f := by
  have hfun : (fun j => MvPolynomial.aeval y (siProjPoly (K := K) (n := n) i j))
      = siProj i y := by
    funext j
    rw [← siProj_apply]
  rw [← MvPolynomial.aeval_eq_eval, ← MvPolynomial.aeval_eq_eval,
    Height.Geometry.aeval_aeval, hfun]

end PairProjection

/-! ### Unpacking a marked arc

An arc of the marked component carries all three kinds of arc data the count
needs.  Reading it off is definitional in every coefficient; the only content is
that the arc kills the projected ideals, which is the contraction identity the
three projections return. -/

section Unpack

variable {K : Type} [Field K] {n : ℕ}

/-- The pencil half of a marked arc's coordinates. -/
noncomputable def arcPairCoords {I : Ideal (MvPolynomial (MarkedIndex (Fin n)) K)}
    (a : Height.Geometry.Arc I) : PairIndex (Fin n) → PowerSeries K :=
  fun j => a.coords (Sum.inl j)

/-- The two marked parameters of a marked arc. -/
noncomputable def arcTdot {I : Ideal (MvPolynomial (MarkedIndex (Fin n)) K)}
    (a : Height.Geometry.Arc I) (i : Fin 2) : PowerSeries K :=
  a.coords (Sum.inr i)

/-- Evaluating the marked coordinates at a point is evaluating at the point. -/
theorem markedEval_eq_eval (w : MarkedIndex (Fin n) → K)
    (f : MvPolynomial (MarkedIndex (Fin n)) K) :
    Height.Pencil.markedEval (pairMatN (markedDirPair w)) (pairMatM (markedDirPair w))
      (fun i => markedTdot i w) f = MvPolynomial.eval w f := by
  have htup : (Sum.elim (Sum.elim (fun ij : Fin n × Fin n => pairMatN (markedDirPair w) ij.1 ij.2)
      (fun ij : Fin n × Fin n => pairMatM (markedDirPair w) ij.1 ij.2))
      (fun i => markedTdot i w)) = w := by
    funext x
    rcases x with (ij | ij) | i <;> rfl
  rw [Height.Pencil.markedEval, htup]

/-- Evaluating the marked coordinates along an arc is evaluating along the
arc. -/
theorem markedArcHom_eq_aeval {I : Ideal (MvPolynomial (MarkedIndex (Fin n)) K)}
    (a : Height.Geometry.Arc I) (f : MvPolynomial (MarkedIndex (Fin n)) K) :
    Height.Pencil.markedArcHom (fstMat (arcPairCoords a)) (sndMat (arcPairCoords a))
      (arcTdot a) f = MvPolynomial.aeval a.coords f := by
  have htup : (Sum.elim (Sum.elim
      (fun ij : Fin n × Fin n => fstMat (arcPairCoords a) ij.1 ij.2)
      (fun ij : Fin n × Fin n => sndMat (arcPairCoords a) ij.1 ij.2)) (arcTdot a)) = a.coords := by
    funext x
    rcases x with (ij | ij) | i <;> rfl
  rw [Height.Pencil.markedArcHom, htup, MvPolynomial.aeval_def]
  rfl

/-- **The pencil half of a marked arc is an arc of the pencil component.** -/
theorem isArcIn_of_markedArc
    {I : Ideal (MvPolynomial (MarkedIndex (Fin n)) K)}
    {J : Ideal (MvPolynomial (PairIndex (Fin n)) K)}
    (hJ : J = I.comap (MvPolynomial.aeval (pairProjPoly (K := K) (n := n)) :
        MvPolynomial (PairIndex (Fin n)) K →ₐ[K] MvPolynomial (MarkedIndex (Fin n)) K))
    (a : Height.Geometry.Arc I) :
    IsArcIn J (markedDirPair a.base) (markedDirPair a.vel)
      (fstMat (arcPairCoords a)) (sndMat (arcPairCoords a)) where
  matC_N := Matrix.ext fun _ _ => rfl
  matC_M := Matrix.ext fun _ _ => rfl
  matD_N := Matrix.ext fun _ _ => rfl
  matD_M := Matrix.ext fun _ _ => rfl
  vanish f hf := by
    rw [pairArcHom_eq_aeval, Height.Geometry.pairCoords_fstMat_sndMat]
    have hmem : MvPolynomial.aeval (pairProjPoly (K := K) (n := n)) f ∈ I := by
      rw [hJ] at hf; exact hf
    have h := a.aeval_coords _ hmem
    rw [Height.Geometry.aeval_aeval] at h
    have hfun : (fun j => MvPolynomial.aeval a.coords (pairProjPoly (K := K) (n := n) j))
        = arcPairCoords a := by
      funext j
      simp [pairProjPoly, arcPairCoords]
    rw [hfun] at h
    exact h

end Unpack

/-! ### `thm:h2-conditional`: the two single-point incidences and the datum -/

section Residue

variable {K : Type} [Field K] {n : ℕ}

/-- **The geometry of `thm:h2-conditional`**: the two single-point incidences,
and — once (SI) is known on a dense open of each — the realised datum at a
tangent-generic point of a component of the cone `Ŷ`.

The proof is the whole of this file and of `Chain/SIComponents.lean`, assembled:

* `exists_markedComponent_arcTangent` gives a component `V(I)` of `Ŷ` and, for
  any single multiplier `g ∉ I`, a tangent-generic point of it with its tangent
  space `T`, the type at infinity, arcs realising every direction of `T`, and
  `dim Ŷ ≤ dim T`;
* the three projections of that component — `exists_pencilComponent_of_markedComponent`
  and `exists_siComponent_of_markedComponent` at either marked parameter — give
  the `PencilComponent` and the two `SIComponent`s, each with its ideal the
  *contraction* along the projection;
* the multiplier `g` is the product of seven pullbacks: the two dense-open
  multipliers of the projected components, the genericity witnesses of
  `arc_rank_eq` and of `member_arc_rank_eq` at either parameter, and the two
  `SIVanishing` multipliers `h₁, h₂`.  One point is then generic for all of
  them at once (`eval_pairProjPoly`, `eval_siProjPoly`);
* each arc of `V(I)` through the point unpacks three ways
  (`isArcIn_of_markedArc`): a `PencilArcData` for its pencil half, a
  `Pencil.MemberArc` at either marked parameter, and a `Pencil.MarkedArc` of
  either `SIComponent` — and `markedIsotropic_of_siVanishing` turns (SI) into
  the isotropy the count consumes;
* `exists_markedRealizedDatum_of_arcs` is the count.

The nonemptiness hypothesis is necessary, and is `markedLocus` rather than
`singleMarkedLocus`: the conclusion produces two `SIComponent`s, hence (over an
algebraically closed field, a nonempty basic open of an irreducible `V(I)`
having a `K`-point) asserts that `𝒴_λ` is nonempty; and the datum's
`length_le` is a statement about a genuine point, so an empty `Ŷ` is not enough
either.  `markedIncidenceBound` (`Chain/Edges.lean`) discharges the empty case
directly, `affineDim ∅ = ⊥`, and supplies this hypothesis otherwise. -/
theorem exists_siComponents_realizedBounds [IsAlgClosed K]
    (τ : Nat.Partition n) (d : ℕ → ℕ) (N₀ : Matrix (Fin n) (Fin n) K)
    (_hd : d ≠ 0) (hnil : IsNilpotent N₀) (_hdeg : IsDegeneration τ N₀)
    (_hc : cType τ < cOf N₀) (hne : (markedLocus (K := K) τ d N₀).Nonempty) :
    ∃ C₁ C₂ : SIComponent τ d N₀,
      ∀ h₁ ∉ C₁.I, ∀ h₂ ∉ C₂.I,
        SIVanishing C₁.I h₁ → SIVanishing C₂.I h₂ →
        ∃ R : RealizedDatum K (MarkedIndex (Fin n)),
          R.Bounds τ (cOf N₀ - cType τ) 2 (markedCoords '' markedLocus (K := K) τ d N₀) := by
  classical
  obtain ⟨C, hCpt⟩ := exists_markedComponent_arcTangent τ d N₀ hne
  have _ := C.prime
  have hlocus : ∀ y ∈ MvPolynomial.zeroLocus K C.I, MvPolynomial.aeval y C.q ≠ 0 →
      y ∈ markedCoords '' markedLocus (K := K) τ d N₀ := by
    intro y hy hq
    refine ⟨markedCoords.symm y, C.locus y hy ?_, markedCoords.apply_symm_apply y⟩
    rwa [MvPolynomial.aeval_eq_eval] at hq
  obtain ⟨Cp, hCpI, hCppt⟩ :=
    exists_pencilComponent_of_markedComponent τ d N₀ C.prime C.notMem hlocus
  obtain ⟨C₁, hC₁I, hC₁pt⟩ :=
    exists_siComponent_of_markedComponent τ d N₀ 0 C.prime C.notMem hlocus
  obtain ⟨C₂, hC₂I, hC₂pt⟩ :=
    exists_siComponent_of_markedComponent τ d N₀ 1 C.prime C.notMem hlocus
  refine ⟨C₁, C₂, fun h₁ hh₁ h₂ hh₂ hv₁ hv₂ => ?_⟩
  have _ := Cp.prime
  obtain ⟨grk, hgrkI, hgrk⟩ := arc_rank_eq (K := K) (n := n) n Cp.I
  obtain ⟨gm₀, hgm₀I, hgm₀⟩ := member_arc_rank_eq (K := K) (n := n) n 0 C.I
  obtain ⟨gm₁, hgm₁I, hgm₁⟩ := member_arc_rank_eq (K := K) (n := n) n 1 C.I
  -- one multiplier making every projected point generic at once
  have hmul : ∀ a b : MvPolynomial (MarkedIndex (Fin n)) K, a ∉ C.I → b ∉ C.I → a * b ∉ C.I :=
    fun a b ha hb h => (C.prime.mem_or_mem h).elim ha hb
  have hpullnot : ∀ f : MvPolynomial (PairIndex (Fin n)) K, f ∉ Cp.I →
      MvPolynomial.aeval (pairProjPoly (K := K) (n := n)) f ∉ C.I :=
    fun f hf hmem => hf (by rw [hCpI]; exact hmem)
  have hnot₁ : ∀ f : MvPolynomial (SIIndex (Fin n)) K, f ∉ C₁.I →
      MvPolynomial.aeval (siProjPoly (K := K) (n := n) 0) f ∉ C.I :=
    fun f hf hmem => hf (by rw [hC₁I]; exact hmem)
  have hnot₂ : ∀ f : MvPolynomial (SIIndex (Fin n)) K, f ∉ C₂.I →
      MvPolynomial.aeval (siProjPoly (K := K) (n := n) 1) f ∉ C.I :=
    fun f hf hmem => hf (by rw [hC₂I]; exact hmem)
  have hggI :
      MvPolynomial.aeval (pairProjPoly (K := K) (n := n)) Cp.q *
        (MvPolynomial.aeval (pairProjPoly (K := K) (n := n)) grk *
          (gm₀ * (gm₁ *
            (MvPolynomial.aeval (siProjPoly (K := K) (n := n) 0) C₁.g *
              (MvPolynomial.aeval (siProjPoly (K := K) (n := n) 1) C₂.g *
                (MvPolynomial.aeval (siProjPoly (K := K) (n := n) 0) h₁ *
                  MvPolynomial.aeval (siProjPoly (K := K) (n := n) 1) h₂)))))) ∉ C.I :=
    hmul _ _ (hpullnot _ Cp.notMem) (hmul _ _ (hpullnot _ hgrkI)
      (hmul _ _ hgm₀I (hmul _ _ hgm₁I (hmul _ _ (hnot₁ _ C₁.locus.notMem)
        (hmul _ _ (hnot₂ _ C₂.locus.notMem) (hmul _ _ (hnot₁ _ hh₁) (hnot₂ _ hh₂)))))))
  obtain ⟨P⟩ := hCpt _ hggI
  -- split the nonvanishing into its factors
  have hne0 : ∀ a b : MvPolynomial (MarkedIndex (Fin n)) K,
      MvPolynomial.eval P.w (a * b) ≠ 0 →
      MvPolynomial.eval P.w a ≠ 0 ∧ MvPolynomial.eval P.w b ≠ 0 := by
    intro a b h
    rw [map_mul] at h
    exact ⟨left_ne_zero_of_mul h, right_ne_zero_of_mul h⟩
  obtain ⟨hqCp, hg1⟩ := hne0 _ _ P.g_ne
  obtain ⟨hgrkne, hg2⟩ := hne0 _ _ hg1
  obtain ⟨hm0ne, hg3⟩ := hne0 _ _ hg2
  obtain ⟨hm1ne, hg4⟩ := hne0 _ _ hg3
  obtain ⟨hC₁gne, hg5⟩ := hne0 _ _ hg4
  obtain ⟨hC₂gne, hg6⟩ := hne0 _ _ hg5
  obtain ⟨hh₁ne, hh₂ne⟩ := hne0 _ _ hg6
  rw [eval_pairProjPoly] at hqCp hgrkne
  rw [eval_siProjPoly] at hC₁gne hh₁ne
  rw [eval_siProjPoly] at hC₂gne hh₂ne
  -- the point of the marked locus
  have hwloc : markedCoords.symm P.w ∈ markedLocus (K := K) τ d N₀ := C.locus P.w P.mem P.q_ne
  -- the numerical data at the point
  have hwloc' : (((pairMatN (markedDirPair P.w)), (pairMatM (markedDirPair P.w)))
        ∈ pencilLocus (K := K) τ d) ∧
      markedTdot 0 P.w ≠ markedTdot 1 P.w ∧
      pairMatN (markedDirPair P.w) + markedTdot 0 P.w • pairMatM (markedDirPair P.w)
        ∈ orbitClosure N₀ ∧
      pairMatN (markedDirPair P.w) + markedTdot 1 P.w • pairMatM (markedDirPair P.w)
        ∈ orbitClosure N₀ := hwloc
  obtain ⟨hpl, htne, hmem₀, hmem₁⟩ := hwloc'
  obtain ⟨hnilw, hgenw, hmulw⟩ := hpl
  have hCpw : markedDirPair P.w ∈ MvPolynomial.zeroLocus K Cp.I := hCppt P.w P.mem P.q_ne
  have hev : ∀ f ∈ Cp.I,
      pairEval (pairMatN (markedDirPair P.w)) (pairMatM (markedDirPair P.w)) f = 0 := by
    intro f hf
    rw [pairEval_pairMat]
    exact hCpw f hf
  have hevg : pairEval (pairMatN (markedDirPair P.w)) (pairMatM (markedDirPair P.w)) grk ≠ 0 := by
    rw [pairEval_pairMat]
    exact hgrkne
  have harcdata : ∀ v : P.T, ∃ a : Height.Geometry.Arc C.I, a.base = P.w ∧ a.vel = v.val :=
    fun v => P.arcs v.val v.2
  -- the pencil arcs
  have hpencil : ∀ v : P.T, Nonempty (PencilArcData (pairMatN (markedDirPair P.w))
      (pairMatM (markedDirPair P.w)) (pairMatN (markedDirPair v.val))
      (pairMatM (markedDirPair v.val)) τ d) := by
    intro v
    obtain ⟨a, hb, hv⟩ := harcdata v
    have hin := isArcIn_of_markedArc hCpI a
    rw [hb, hv] at hin
    have hnilarc : (pencil (fstMat (arcPairCoords a)) (sndMat (arcPairCoords a))) ^ n = 0 :=
      pencilR_pow_eq_zero_of_arc Cp.I Cp.notMem
        (fun w' hw' hq' => (Cp.locus w' hw' hq').1) hin.vanish
    exact ⟨⟨fstMat (arcPairCoords a), sndMat (arcPairCoords a), hin.matC_N, hin.matC_M,
      hin.matD_N, hin.matD_M, hnilarc,
      hgrk _ _ hev hevg _ _ hin.vanish hin.matC_N hin.matC_M,
      by rw [hin.matC_N, hin.matC_M]; exact hmulw,
      hasMultidegree_of_isArcIn Cp hCpw hqCp hin⟩⟩
  -- the marked-coordinate evaluations at the point and along an arc
  have hIw : ∀ f ∈ C.I, Height.Pencil.markedEval (pairMatN (markedDirPair P.w))
      (pairMatM (markedDirPair P.w)) (fun i => markedTdot i P.w) f = 0 := by
    intro f hf
    rw [markedEval_eq_eval]
    exact P.mem f hf
  have harcvan : ∀ a : Height.Geometry.Arc C.I, ∀ f ∈ C.I,
      Height.Pencil.markedArcHom (fstMat (arcPairCoords a)) (sndMat (arcPairCoords a))
        (arcTdot a) f = 0 := by
    intro a f hf
    rw [markedArcHom_eq_aeval]
    exact a.aeval_coords f hf
  -- the member arcs at either marked parameter
  have hmemgen : ∀ (i : Fin 2) (gm : MvPolynomial (MarkedIndex (Fin n)) K),
      (∀ (N M : Matrix (Fin n) (Fin n) K) (tt : Fin 2 → K),
        (∀ f ∈ C.I, Height.Pencil.markedEval N M tt f = 0) →
        Height.Pencil.markedEval N M tt gm ≠ 0 →
        ∀ (Ns Ms : Matrix (Fin n) (Fin n) (PowerSeries K)) (tts : Fin 2 → PowerSeries K),
          (∀ f ∈ C.I, Height.Pencil.markedArcHom Ns Ms tts f = 0) →
          matC Ns = N → matC Ms = M →
          (fun j => PowerSeries.constantCoeff (tts j)) = tt →
          ∀ k ≤ n, Height.Pencil.MatArcRankEq (Ns + tts i • Ms) k) →
      MvPolynomial.eval P.w gm ≠ 0 →
      ∀ v : P.T, Nonempty (Height.Pencil.MemberArc (pairMatN (markedDirPair P.w))
        (pairMatM (markedDirPair P.w)) (markedTdot i P.w)
        (pairMatN (markedDirPair v.val)) (pairMatM (markedDirPair v.val))
        (markedTdot i v.val)) := by
    intro i gm hgm hgmne v
    obtain ⟨a, hb, hv⟩ := harcdata v
    have hin := isArcIn_of_markedArc hCpI a
    rw [hb, hv] at hin
    have hnilarc : (pencil (fstMat (arcPairCoords a)) (sndMat (arcPairCoords a))) ^ n = 0 :=
      pencilR_pow_eq_zero_of_arc Cp.I Cp.notMem
        (fun w' hw' hq' => (Cp.locus w' hw' hq').1) hin.vanish
    have hct : (fun j => PowerSeries.constantCoeff (arcTdot a j))
        = fun j => markedTdot j P.w := by
      funext j
      show PowerSeries.constantCoeff (a.coords (Sum.inr j)) = _
      rw [← hb]
      rfl
    have hdt : PowerSeries.coeff 1 (arcTdot a i) = markedTdot i v.val := by
      show PowerSeries.coeff 1 (a.coords (Sum.inr i)) = _
      rw [← hv]
      rfl
    have hrank := hgm _ _ _ hIw (by rw [markedEval_eq_eval]; exact hgmne)
      (fstMat (arcPairCoords a)) (sndMat (arcPairCoords a)) (arcTdot a)
      (harcvan a) hin.matC_N hin.matC_M hct
    have hnilmem : ((fstMat (arcPairCoords a))
        + (arcTdot a i) • (sndMat (arcPairCoords a))) ^ n = 0 :=
      Height.Pencil.member_pow_eq_zero hnilarc
    have hma := Height.Pencil.MemberArc.ofRank hnilmem hrank
    rw [hin.matC_N, hin.matC_M, hin.matD_N, hin.matD_M, congrFun hct i, hdt] at hma
    exact ⟨hma⟩
  have hmem0 := hmemgen 0 gm₀ hgm₀ hm0ne
  have hmem1 := hmemgen 1 gm₁ hgm₁ hm1ne
  -- the marked arcs of the two single-point components, for (SI)
  have hmarcgen : ∀ (i : Fin 2) (Ci : SIComponent τ d N₀),
      Ci.I = C.I.comap (MvPolynomial.aeval (siProjPoly (K := K) (n := n) i) :
        MvPolynomial (SIIndex (Fin n)) K →ₐ[K] MvPolynomial (MarkedIndex (Fin n)) K) →
      (∀ v : P.T, Nonempty (Height.Pencil.MemberArc (pairMatN (markedDirPair P.w))
        (pairMatM (markedDirPair P.w)) (markedTdot i P.w)
        (pairMatN (markedDirPair v.val)) (pairMatM (markedDirPair v.val))
        (markedTdot i v.val))) →
      ∀ v : P.T, ∃ m : Height.Pencil.MarkedArc Ci.I (siProj i P.w),
        m.a.vel = (pairMatN (markedDirPair v.val), pairMatM (markedDirPair v.val),
          markedTdot i v.val) := by
    intro i Ci hCiI hmem v
    obtain ⟨a, hb, hv⟩ := harcdata v
    have hin := isArcIn_of_markedArc hCpI a
    rw [hb, hv] at hin
    have hct : (fun j => PowerSeries.constantCoeff (arcTdot a j))
        = fun j => markedTdot j P.w := by
      funext j
      show PowerSeries.constantCoeff (a.coords (Sum.inr j)) = _
      rw [← hb]
      rfl
    have hdt : PowerSeries.coeff 1 (arcTdot a i) = markedTdot i v.val := by
      show PowerSeries.coeff 1 (a.coords (Sum.inr i)) = _
      rw [← hv]
      rfl
    obtain ⟨Z, hZ⟩ := (hmem v).some.exists_markedWith
    refine ⟨⟨⟨⟨fstMat (arcPairCoords a), sndMat (arcPairCoords a), arcTdot a i⟩, ?_, ?_⟩,
      Z, ?_⟩, ?_⟩
    · intro f hf
      have hmemI : MvPolynomial.aeval (siProjPoly (K := K) (n := n) i) f ∈ C.I := by
        rw [hCiI] at hf; exact hf
      have h := a.aeval_coords _ hmemI
      rw [Height.Geometry.aeval_aeval] at h
      have hfun : (fun j => MvPolynomial.aeval a.coords (siProjPoly (K := K) (n := n) i j))
          = Height.Pencil.SIArc.coords
              ⟨fstMat (arcPairCoords a), sndMat (arcPairCoords a), arcTdot a i⟩ := by
        funext j
        rcases j with (jj | jj) | u <;>
          simp [siProjPoly, Height.Pencil.SIArc.coords, arcPairCoords, arcTdot]
      rw [hfun] at h
      exact h
    · show ((matC (fstMat (arcPairCoords a))), matC (sndMat (arcPairCoords a)),
        PowerSeries.constantCoeff (arcTdot a i)) = _
      rw [hin.matC_N, hin.matC_M, congrFun hct i]
      rfl
    · show Height.Pencil.MarkedWith _ _ _
        (pencil (matD (fstMat (arcPairCoords a))) (matD (sndMat (arcPairCoords a))))
        (PowerSeries.coeff 1 (arcTdot a i)) Z
      rw [hin.matD_N, hin.matD_M, hdt]
      exact hZ
    · show ((matD (fstMat (arcPairCoords a))), matD (sndMat (arcPairCoords a)),
        PowerSeries.coeff 1 (arcTdot a i)) = _
      rw [hin.matD_N, hin.matD_M, hdt]
  have hSI₁ : MarkedIsotropic (pairMatN (markedDirPair P.w)) (pairMatM (markedDirPair P.w))
      (markedTdot 0 P.w) 0 P.T :=
    markedIsotropic_of_siVanishing hv₁ (hC₁pt P.w P.mem P.q_ne) hh₁ne rfl
      (hmarcgen 0 C₁ hC₁I hmem0)
  have hSI₂ : MarkedIsotropic (pairMatN (markedDirPair P.w)) (pairMatM (markedDirPair P.w))
      (markedTdot 1 P.w) 1 P.T :=
    markedIsotropic_of_siVanishing hv₂ (hC₂pt P.w P.mem P.q_ne) hh₂ne rfl
      (hmarcgen 1 C₂ hC₂I hmem1)
  exact exists_markedRealizedDatum_of_arcs hnilw hgenw P.type htne hnil hmem₀ hmem₁ P.T
    hpencil hmem0 hmem1 hSI₁ hSI₂ P.affineDim_le

end Residue
end Height.Chain
