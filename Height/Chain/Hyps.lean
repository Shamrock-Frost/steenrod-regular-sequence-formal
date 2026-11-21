import Height.Chain.LocalFlat
import Height.Chain.Untwist
import Height.Chain.Springer
import Height.Chain.Constructible
import Height.Chain.Multidegree
import Height.Chain.PencilPoly
import Height.Pencil.Arcs
import Height.Pencil.ArcsLocal
import Height.Geometry.Tangent.Newton

/-!
# The fibration counts, and `thm:conditional-height`

Three geometric inputs of the conditional height count
are proved here — the orbit-dimension formula (`affineDim_conjOrbit`), the
reparametrisation fibration of the marked locus
(`affineDim_markedPair_add_two`) and the conjugation fibration of the pair locus
(`affineDim_pairSet`); a fourth, the multidegree at the generic point of an arc
(`hasMultidegreeGen`), is in `Chain/LocalFlat.lean` — and the count itself
is assembled at the end (`affineDim_flaglessPartners_le_of_bounds`), whose
only hypotheses are (H1) and (H2′).
-/

-- Triple tensor products of coordinate rings need one more level of pending synthesis than
-- the default (as in `Geometry/Group.lean`).
set_option maxSynthPendingDepth 4

namespace Height.Chain

open Height.Pencil

open MvPolynomial Height.Geometry Height.Chain.Untwisting
open Height.Toolbox (cOf)

universe u

/-! ### The closed pair model of `GL_n` has dimension `n²` -/

section PairModel

variable {K : Type} [Field K] [IsAlgClosed K] [Infinite K] {n : ℕ}

omit [IsAlgClosed K] [Infinite K] in
/-- The first block of the pair model is `GL_n` in entry coordinates. -/
theorem fstMat_image_glPair :
    (fun x : PairIndex (Fin n) → K => matCoords (fstMat x)) '' glPair K n
      = matCoords '' {M : Matrix (Fin n) (Fin n) K | IsUnit M.det} := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨fstMat x, Matrix.isUnit_det_of_right_inverse hx.1, rfl⟩
  · rintro _ ⟨A, hA, rfl⟩
    exact ⟨pairCoords (A, A⁻¹), ⟨Matrix.mul_nonsing_inv A hA, Matrix.nonsing_inv_mul A hA⟩, rfl⟩

omit [IsAlgClosed K] [Infinite K] in
/-- The first block determines the pair. -/
theorem glPair_fibre_subsingleton (y : Fin n × Fin n → K) :
    (glPair K n ∩ (fun x : PairIndex (Fin n) → K => matCoords (fstMat x)) ⁻¹' {y}).Subsingleton := by
  intro a ha b hb
  have hfst : fstMat a = fstMat b := matCoords.injective (ha.2.trans hb.2.symm)
  have hsnd : sndMat a = sndMat b := by
    have h1 : (fstMat a)⁻¹ = sndMat a := Matrix.inv_eq_right_inv ha.1.1
    have h2 : (fstMat b)⁻¹ = sndMat b := Matrix.inv_eq_right_inv hb.1.1
    rw [← h1, ← h2, hfst]
  have h : pairCoords ((fstMat a), (sndMat a)) = pairCoords ((fstMat b), (sndMat b)) := by rw [hfst, hsnd]
  rwa [pairCoords_fstMat_sndMat, pairCoords_fstMat_sndMat] at h

omit [Infinite K] in
/-- **`dim GL_n = n²`** in the closed pair model. -/
theorem affineDim_glPair :
    affineDim (glPair K n) = ((n * n : ℕ) : WithBot ℕ∞) := by
  have h := affineDim_of_finite_fibres (isPolyMap_fstMat (K := K) (μ := Fin n)) (glPair K n)
    (matCoords '' {M : Matrix (Fin n) (Fin n) K | IsUnit M.det}) zclosure_glPair
    fstMat_image_glPair (fun y _ => (glPair_fibre_subsingleton y).finite)
  rw [h, affineDim_generalLinear]
  simp

omit [IsAlgClosed K] [Infinite K] in
/-- The conjugation map carries the pair model onto the orbit. -/
theorem conjMap_image_glPair (N : Matrix (Fin n) (Fin n) K) :
    conjMap N '' glPair K n = matCoords '' Chain.conjOrbit N := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨fstMat x * N * sndMat x, ⟨pairUnit hx, rfl⟩, rfl⟩
  · rintro _ ⟨M, ⟨g, rfl⟩, rfl⟩
    exact ⟨pairCoords ((g : Matrix (Fin n) (Fin n) K), ((g⁻¹ : (Matrix (Fin n) (Fin n) K)ˣ) :
      Matrix (Fin n) (Fin n) K)), pairCoords_unit_mem g, rfl⟩

/-- **The orbit-dimension formula**: `dim O_N + c(N) = n²`. -/
theorem affineDim_conjOrbit_add_cdim (N : Matrix (Fin n) (Fin n) K) :
    affineDim (matCoords '' Chain.conjOrbit N) + ((cdim N : ℕ) : WithBot ℕ∞)
      = ((n * n : ℕ) : WithBot ℕ∞) := by
  have h := affineDim_conj_fibration_of_zclosure N Set.univ zclosure_univ
  rw [Set.preimage_univ, Set.inter_univ, conjMap_image_glPair N, affineDim_glPair] at h
  exact h

/-- **The dimension of a nilpotent orbit** is
`n² − c(N)`. -/
theorem affineDim_conjOrbit (N : Matrix (Fin n) (Fin n) K) (hN : IsNilpotent N) :
    affineDim (matCoords '' Chain.conjOrbit N) = (((n * n - cOf N : ℕ) : ℕ∞) : WithBot ℕ∞) := by
  have h := affineDim_conjOrbit_add_cdim N
  rw [show Untwisting.cdim N = cOf N from Height.Toolbox.finrank_centralizer_eq N hN] at h
  have hle : cOf N ≤ n * n := cOf_le_sq hN
  have hback : (((n * n - cOf N : ℕ) : ℕ∞) : WithBot ℕ∞) + ((cOf N : ℕ) : WithBot ℕ∞)
      = ((n * n : ℕ) : WithBot ℕ∞) := by
    norm_cast
    omega
  exact Toolbox.add_natCast_right_cancel (h.trans hback.symm)

omit [IsAlgClosed K] [Infinite K] in
/-- An orbit lies in the corresponding orbit closure. -/
theorem conjOrbit_subset_orbitClosure (N : Matrix (Fin n) (Fin n) K) :
    Chain.conjOrbit N ⊆ orbitClosure N := by
  rintro _ ⟨g, rfl⟩ k
  rw [Chain.rank_pow_conj]

end PairModel

/-! ### The reparametrisation action on the marked locus -/

section MarkedFibration

open AlgebraicGeometry Topology
open scoped TensorProduct

variable {K : Type} [Field K] {n : ℕ}

/-- Coordinates of the affine group of the line, in the chart which inverts the
scaling: `(a, b, s)` with `s b = 1`. -/
abbrev AffIndex : Type := Fin 2 ⊕ Unit

/-- The affine group of the line `t ↦ (t - a) / b`, in the chart `s b = 1`. -/
def affGroup (K : Type u) [Field K] : Set (AffIndex → K) :=
  graphSet (Set.univ : Set (Fin 2 → K)) (MvPolynomial.X 1 : MvPolynomial (Fin 2) K)

theorem mem_affGroup_iff (g : AffIndex → K) :
    g ∈ affGroup K ↔ g (Sum.inr ()) * g (Sum.inl 1) = 1 := by
  constructor
  · rintro ⟨-, h⟩
    simpa [projSum] using h
  · intro h
    exact ⟨Set.mem_univ _, by simpa [projSum] using h⟩

theorem affGroup_scale_ne_zero {g : AffIndex → K} (hg : g ∈ affGroup K) :
    g (Sum.inl 1) ≠ 0 := by
  intro h0
  have h := (mem_affGroup_iff g).1 hg
  rw [h0, mul_zero] at h
  exact zero_ne_one h

theorem affGroup_inv_ne_zero {g : AffIndex → K} (hg : g ∈ affGroup K) :
    g (Sum.inr ()) ≠ 0 := by
  intro h0
  have h := (mem_affGroup_iff g).1 hg
  rw [h0, zero_mul] at h
  exact zero_ne_one h

/-- The reparametrisation `(N, M, α, β) ↦ (N + a M, b M, (α - a) s, (β - a) s)`
in marked coordinates. -/
def markAct (g : AffIndex → K) (x : MarkedIndex (Fin n) → K) : MarkedIndex (Fin n) → K :=
  Sum.elim
    (Sum.elim
      (fun ij => x (Sum.inl (Sum.inl ij)) + g (Sum.inl 0) * x (Sum.inl (Sum.inr ij)))
      (fun ij => g (Sum.inl 1) * x (Sum.inl (Sum.inr ij))))
    (fun j => (x (Sum.inr j) - g (Sum.inl 0)) * g (Sum.inr ()))

@[simp] theorem markAct_inl_inl (g : AffIndex → K) (x : MarkedIndex (Fin n) → K) (ij : Fin n × Fin n) :
    markAct g x (Sum.inl (Sum.inl ij))
      = x (Sum.inl (Sum.inl ij)) + g (Sum.inl 0) * x (Sum.inl (Sum.inr ij)) := rfl

@[simp] theorem markAct_inl_inr (g : AffIndex → K) (x : MarkedIndex (Fin n) → K) (ij : Fin n × Fin n) :
    markAct g x (Sum.inl (Sum.inr ij)) = g (Sum.inl 1) * x (Sum.inl (Sum.inr ij)) := rfl

@[simp] theorem markAct_inr (g : AffIndex → K) (x : MarkedIndex (Fin n) → K) (j : Fin 2) :
    markAct g x (Sum.inr j) = (x (Sum.inr j) - g (Sum.inl 0)) * g (Sum.inr ()) := rfl

@[simp] theorem markOf_markAct_fst (g : AffIndex → K) (x : MarkedIndex (Fin n) → K) :
    (markedCoords.symm (markAct g x)).1 = (markedCoords.symm x).1 + g (Sum.inl 0) • (markedCoords.symm x).2.1 := by
  ext i j
  simp [Matrix.add_apply]

@[simp] theorem markOf_markAct_snd (g : AffIndex → K) (x : MarkedIndex (Fin n) → K) :
    (markedCoords.symm (markAct g x)).2.1 = g (Sum.inl 1) • (markedCoords.symm x).2.1 := by
  ext i j
  simp

variable (K n) in
/-- The reparametrisation, as polynomials in the group and space coordinates. -/
noncomputable def markActPoly :
    MarkedIndex (Fin n) → MvPolynomial (AffIndex ⊕ MarkedIndex (Fin n)) K :=
  Sum.elim
    (Sum.elim
      (fun ij => MvPolynomial.X (Sum.inr (Sum.inl (Sum.inl ij)))
        + MvPolynomial.X (Sum.inl (Sum.inl 0))
          * MvPolynomial.X (Sum.inr (Sum.inl (Sum.inr ij))))
      (fun ij => MvPolynomial.X (Sum.inl (Sum.inl 1))
        * MvPolynomial.X (Sum.inr (Sum.inl (Sum.inr ij)))))
    (fun j => (MvPolynomial.X (Sum.inr (Sum.inr j)) - MvPolynomial.X (Sum.inl (Sum.inl 0)))
      * MvPolynomial.X (Sum.inl (Sum.inr ())))

variable (K n) in
/-- The reparametrisation action of the affine group of the line on the marked pencil
coordinates, as `ActionData` on all of `𝔸(MarkedIndex (Fin n))`. -/
noncomputable def markActionData : ActionData (AffLine.affData K) (MarkedIndex (Fin n)) where
  J := ⊥
  act := markActPoly K n
  act_mem := by
    intro f hf
    rw [Ideal.mem_bot] at hf
    subst hf
    simp

@[simp] theorem markActionData_act : (markActionData K n).act = markActPoly K n := rfl

/-- The action on `K`-points is the reparametrisation `markAct`. -/
theorem markActionData_actPt (g : AffIndex → K) (x : MarkedIndex (Fin n) → K) :
    (markActionData K n).actPt g x = markAct g x := by
  funext i
  match i with
  | Sum.inl (Sum.inl ij) => simp [ActionData.actPt, markActPoly, markAct_inl_inl]
  | Sum.inl (Sum.inr ij) => simp [ActionData.actPt, markActPoly, markAct_inl_inr]
  | Sum.inr j => simp [ActionData.actPt, markActPoly, markAct_inr]

variable (K n) in
/-- **The reparametrisation action**, as an `ActionPresentation` of the affine group of the
line on the marked pencil coordinates.  The two comodule axioms are the two action laws as
polynomial identities (`ActionPresentation.ofLaws`): `1 · x = x` holds on the nose, and
`b · (a · x) = (b a) · x` holds on the nose on the two matrix blocks and modulo the chart
relation `s b − 1` of the *first* group block on the two markers, where the residue is
`a₂ s₂ (s₁ b₁ − 1)`. -/
noncomputable def markAction : ActionPresentation (AffLine.affLine K) (MarkedIndex (Fin n)) :=
  ActionPresentation.ofLaws (markActionData K n)
    (by
      rintro ((ij | ij) | j) <;>
        exact sub_mem_of_eq (by simp [ActionData.oneAct, markActPoly, AffLine.affOnePt]))
    (by
      rintro ((ij | ij) | j)
      · exact sub_mem_of_eq (by
          simp [ActionData.actAct, ActionData.mulAct, ActionData.act1, GroupData.mulFlip,
            markActPoly, AffLine.affMulPoly]
          ring)
      · exact sub_mem_of_eq (by
          simp [ActionData.actAct, ActionData.mulAct, ActionData.act1, GroupData.mulFlip,
            markActPoly, AffLine.affMulPoly]
          ring)
      · exact mem_ideal_of_eq
          (show (markActionData K n).actAct (Sum.inr j)
                - (markActionData K n).mulAct (Sum.inr j)
              = (MvPolynomial.X (Sum.inr (Sum.inl (Sum.inl 0)))
                  * MvPolynomial.X (Sum.inr (Sum.inl (Sum.inr ()))))
                * MvPolynomial.rename Sum.inl (AffLine.affRel K) by
            simp [ActionData.actAct, ActionData.mulAct, ActionData.act1, GroupData.mulFlip,
              markActPoly, AffLine.affMulPoly, AffLine.affRel, AffLine.sVar, AffLine.bVar]
            ring)
          (Ideal.mul_mem_left _ _ (renameL_mem_sumIdeal (AffLine.affRel_mem K))))

@[simp] theorem markAction_toActionData :
    (markAction K n).toActionData = markActionData K n := rfl

theorem markAction_J : (markAction K n).J = ⊥ := rfl

/-- The reparametrisation action on `K`-points. -/
theorem markAction_actPt (g : AffIndex → K) (x : MarkedIndex (Fin n) → K) :
    (markAction K n).actPt g x = markAct g x := markActionData_actPt g x

/-- **The `K`-points of the affine group of the line are the reparametrisations.** -/
theorem affLine_pts : (AffLine.affLine K).pts = affGroup K := by
  ext g
  rw [AffLine.mem_affLine_pts_iff, mem_affGroup_iff]

/-! #### The orbits are two-dimensional -/

theorem isLocClosed_affGroup : IsLocClosed (affGroup K) :=
  IsLocClosed.of_zclosure (zclosure_graphSet zclosure_univ _)

theorem affineDim_affGroup [IsAlgClosed K] :
    affineDim (affGroup K) = ((2 : ℕ) : WithBot ℕ∞) := by
  have hq : (MvPolynomial.X 1 : MvPolynomial (Fin 2) K)
      ∉ MvPolynomial.vanishingIdeal K (Set.univ : Set (Fin 2 → K)) := by
    rw [vanishingIdeal_univ, Ideal.mem_bot]
    exact MvPolynomial.X_ne_zero (R := K) (1 : Fin 2)
  rw [affGroup, affineDim_graphSet zclosure_univ _,
    affineDim_inter_dense isPrime_vanishingIdeal_univ hq, affineDim_univ]
  simp

/-- A reparametrisation is determined by its effect on a pair of distinct
parameters. -/
theorem markAct_inj {x : MarkedIndex (Fin n) → K} (hx : x (Sum.inr 0) ≠ x (Sum.inr 1))
    {g h : AffIndex → K} (hg : g ∈ affGroup K) (hh : h ∈ affGroup K)
    (hgh : markAct g x = markAct h x) : g = h := by
  have e0 := congrFun hgh (Sum.inr 0)
  have e1 := congrFun hgh (Sum.inr 1)
  rw [markAct_inr, markAct_inr] at e0
  rw [markAct_inr, markAct_inr] at e1
  have hne : x (Sum.inr 1) - x (Sum.inr 0) ≠ 0 := sub_ne_zero.2 (Ne.symm hx)
  have hs : g (Sum.inr ()) = h (Sum.inr ()) := by
    refine mul_left_cancel₀ hne ?_
    linear_combination e1 - e0
  have hs0 : g (Sum.inr ()) ≠ 0 := affGroup_inv_ne_zero hg
  have ha : g (Sum.inl 0) = h (Sum.inl 0) := by
    have h1 : x (Sum.inr 0) - g (Sum.inl 0) = x (Sum.inr 0) - h (Sum.inl 0) := by
      refine mul_right_cancel₀ hs0 ?_
      rw [e0, hs]
    exact sub_right_inj.1 h1
  have hb : g (Sum.inl 1) = h (Sum.inl 1) := by
    refine mul_left_cancel₀ hs0 ?_
    rw [(mem_affGroup_iff g).1 hg, hs, (mem_affGroup_iff h).1 hh]
  funext i
  rcases i with j | u
  · fin_cases j
    · exact ha
    · exact hb
  · cases u
    exact hs

theorem isPolyMap_markAct (x : MarkedIndex (Fin n) → K) :
    IsPolyMap (fun g : AffIndex → K => markAct g x) := by
  refine ⟨Sum.elim (Sum.elim
    (fun ij => MvPolynomial.C (x (Sum.inl (Sum.inl ij)))
      + MvPolynomial.X (Sum.inl 0) * MvPolynomial.C (x (Sum.inl (Sum.inr ij))))
    (fun ij => MvPolynomial.X (Sum.inl 1) * MvPolynomial.C (x (Sum.inl (Sum.inr ij)))))
    (fun j => (MvPolynomial.C (x (Sum.inr j)) - MvPolynomial.X (Sum.inl 0))
      * MvPolynomial.X (Sum.inr ())), ?_⟩
  intro g i
  match i with
  | Sum.inl (Sum.inl ij) => simp
  | Sum.inl (Sum.inr ij) => simp
  | Sum.inr j => simp

/-- **Every orbit of the reparametrisation action on a marked pencil has
dimension `2`.** -/
theorem affineDim_markOrbit [IsAlgClosed K] {x : MarkedIndex (Fin n) → K}
    (hx : x (Sum.inr 0) ≠ x (Sum.inr 1)) :
    affineDim ((fun g : AffIndex → K => markAct g x) '' affGroup K)
      = ((2 : ℕ) : WithBot ℕ∞) := by
  have hfin : ∀ z ∈ (fun g : AffIndex → K => markAct g x) '' affGroup K,
      (affGroup K ∩ (fun g : AffIndex → K => markAct g x) ⁻¹' {z}).Finite := by
    intro z _
    refine Set.Subsingleton.finite fun a ha b hb => ?_
    refine markAct_inj hx ha.1 hb.1 ?_
    have h1 : markAct a x = z := ha.2
    have h2 : markAct b x = z := hb.2
    rw [h1, h2]
  have h := affineDim_of_finite_fibres_locClosed (isPolyMap_markAct x) (affGroup K)
    ((fun g : AffIndex → K => markAct g x) '' affGroup K) isLocClosed_affGroup rfl hfin
  rw [← h, affineDim_affGroup]

/-- The orbits of `markAction` are the reparametrisation orbits. -/
theorem markOrbit_eq (x : MarkedIndex (Fin n) → K) :
    {z : MarkedIndex (Fin n) → K |
        ∃ g ∈ (AffLine.affLine K).pts, (markAction K n).actPt g x = z}
      = (fun g : AffIndex → K => markAct g x) '' affGroup K := by
  ext z
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, (Set.ext_iff.1 affLine_pts g).1 hg, (markAction_actPt g x).symm⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, (Set.ext_iff.1 affLine_pts g).2 hg, markAction_actPt g x⟩

/-! #### The fibration `ψ : Ŷ → Mat × Mat` -/

/-- The two marked members of a marked pencil, in pair coordinates. -/
def markPairMap (x : MarkedIndex (Fin n) → K) : PairIndex (Fin n) → K := pairCoords (markedPair (markedCoords.symm x))

variable (K n) in
/-- The two marked members, as polynomials in the marked coordinates. -/
noncomputable def markPairPoly :
    PairIndex (Fin n) → MvPolynomial (MarkedIndex (Fin n)) K :=
  Sum.elim
    (fun ij => MvPolynomial.X (Sum.inl (Sum.inl ij))
      + MvPolynomial.X (Sum.inr 0) * MvPolynomial.X (Sum.inl (Sum.inr ij)))
    (fun ij => MvPolynomial.X (Sum.inl (Sum.inl ij))
      + MvPolynomial.X (Sum.inr 1) * MvPolynomial.X (Sum.inl (Sum.inr ij)))

theorem aeval_markPairPoly (y : MarkedIndex (Fin n) → K) :
    (fun j => MvPolynomial.aeval y (markPairPoly K n j)) = markPairMap y := by
  funext j
  match j with
  | Sum.inl ij =>
      simp [markPairPoly, markPairMap, markedPair]
  | Sum.inr ij =>
      simp [markPairPoly, markPairMap, markedPair]

theorem isPolyMap_markPairMap : IsPolyMap (markPairMap (K := K) (n := n)) :=
  ⟨markPairPoly K n, fun y j => (congrFun (aeval_markPairPoly y) j).symm⟩

/-- The marked members are invariant under reparametrisation. -/
theorem markPairMap_markAct {g : AffIndex → K} (hg : g ∈ affGroup K) (x : MarkedIndex (Fin n) → K) :
    markPairMap (markAct g x) = markPairMap x := by
  have hg' := (mem_affGroup_iff g).1 hg
  funext j
  match j with
  | Sum.inl ij =>
      show (markedCoords.symm (markAct g x)).1 ij.1 ij.2
          + markAct g x (Sum.inr 0) * (markedCoords.symm (markAct g x)).2.1 ij.1 ij.2
        = (markedCoords.symm x).1 ij.1 ij.2 + x (Sum.inr 0) * (markedCoords.symm x).2.1 ij.1 ij.2
      rw [markOf_markAct_fst, markOf_markAct_snd, markAct_inr]
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      linear_combination ((markedCoords.symm x).2.1 ij.1 ij.2 * (x (Sum.inr 0) - g (Sum.inl 0))) * hg'
  | Sum.inr ij =>
      show (markedCoords.symm (markAct g x)).1 ij.1 ij.2
          + markAct g x (Sum.inr 1) * (markedCoords.symm (markAct g x)).2.1 ij.1 ij.2
        = (markedCoords.symm x).1 ij.1 ij.2 + x (Sum.inr 1) * (markedCoords.symm x).2.1 ij.1 ij.2
      rw [markOf_markAct_fst, markOf_markAct_snd, markAct_inr]
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      linear_combination ((markedCoords.symm x).2.1 ij.1 ij.2 * (x (Sum.inr 1) - g (Sum.inl 0))) * hg'

/-- The marked locus is stable under reparametrisation. -/
theorem markedLocus_markAct {τ : Nat.Partition n} {d : ℕ → ℕ}
    {N₀ : Matrix (Fin n) (Fin n) K} {g : AffIndex → K} (hg : g ∈ affGroup K)
    {x : MarkedIndex (Fin n) → K} (hx : markedCoords.symm x ∈ markedLocus τ d N₀) :
    markedCoords.symm (markAct g x) ∈ markedLocus τ d N₀ := by
  have hb : g (Sum.inl 1) ≠ 0 := affGroup_scale_ne_zero hg
  have hinv : (g (Sum.inl 1))⁻¹ = g (Sum.inr ()) :=
    inv_eq_of_mul_eq_one_left ((mem_affGroup_iff g).1 hg)
  have h := markedLocus_subst (g (Sum.inl 0)) hb hx
  have heq : markedCoords.symm (markAct g x)
      = ((markedCoords.symm x).1 + g (Sum.inl 0) • (markedCoords.symm x).2.1, g (Sum.inl 1) • (markedCoords.symm x).2.1,
          ((markedCoords.symm x).2.2.1 - g (Sum.inl 0)) / g (Sum.inl 1),
          ((markedCoords.symm x).2.2.2 - g (Sum.inl 0)) / g (Sum.inl 1)) := by
    refine Prod.ext_iff.2 ⟨markOf_markAct_fst g x, Prod.ext_iff.2
      ⟨markOf_markAct_snd g x, Prod.ext_iff.2 ⟨?_, ?_⟩⟩⟩
    · show (x (Sum.inr 0) - g (Sum.inl 0)) * g (Sum.inr ())
        = (x (Sum.inr 0) - g (Sum.inl 0)) / g (Sum.inl 1)
      rw [div_eq_mul_inv, hinv]
    · show (x (Sum.inr 1) - g (Sum.inl 0)) * g (Sum.inr ())
        = (x (Sum.inr 1) - g (Sum.inl 0)) / g (Sum.inl 1)
      rw [div_eq_mul_inv, hinv]
  rw [heq]
  exact h

/-- The reparametrisation with shift `a`, scaling `b` and inverse scaling `s`. -/
def affElt (a b s : K) : AffIndex → K := Sum.elim ![a, b] (fun _ => s)

omit [Field K] in
@[simp] theorem affElt_scale (a b s : K) : affElt a b s (Sum.inl 1) = b := rfl

omit [Field K] in
@[simp] theorem affElt_inv (a b s : K) : affElt a b s (Sum.inr ()) = s := rfl

/-- **Simple transitivity on the fibres of `ψ`**: two marked pencils with the
same pair of marked members differ by a reparametrisation. -/
theorem exists_markAct_of_markPairMap_eq {τ : Nat.Partition n} {d : ℕ → ℕ}
    {N₀ : Matrix (Fin n) (Fin n) K} {x y : MarkedIndex (Fin n) → K}
    (hx : markedCoords.symm x ∈ markedLocus τ d N₀) (hy : markedCoords.symm y ∈ markedLocus τ d N₀)
    (h : markPairMap x = markPairMap y) :
    ∃ g ∈ affGroup K, markAct g x = y := by
  have hxne : x (Sum.inr 0) ≠ x (Sum.inr 1) := hx.2.1
  have hyne : y (Sum.inr 0) ≠ y (Sum.inr 1) := hy.2.1
  have hd : x (Sum.inr 1) - x (Sum.inr 0) ≠ 0 := sub_ne_zero.2 (Ne.symm hxne)
  have hd' : y (Sum.inr 1) - y (Sum.inr 0) ≠ 0 := sub_ne_zero.2 (Ne.symm hyne)
  have hpair : markedPair (markedCoords.symm x) = markedPair (markedCoords.symm y) := by
    have hc := congrArg pairCoords.symm h
    rwa [markPairMap, markPairMap, pairCoords.symm_apply_apply, pairCoords.symm_apply_apply] at hc
  have hP : ∀ i j, (markedCoords.symm x).1 i j + x (Sum.inr 0) * (markedCoords.symm x).2.1 i j
      = (markedCoords.symm y).1 i j + y (Sum.inr 0) * (markedCoords.symm y).2.1 i j := by
    intro i j
    have hc := congrArg (fun q : Matrix (Fin n) (Fin n) K × Matrix (Fin n) (Fin n) K => q.1 i j)
      hpair
    simp only [markedPair, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at hc
    exact hc
  have hQ : ∀ i j, (markedCoords.symm x).1 i j + x (Sum.inr 1) * (markedCoords.symm x).2.1 i j
      = (markedCoords.symm y).1 i j + y (Sum.inr 1) * (markedCoords.symm y).2.1 i j := by
    intro i j
    have hc := congrArg (fun q : Matrix (Fin n) (Fin n) K × Matrix (Fin n) (Fin n) K => q.2 i j)
      hpair
    simp only [markedPair, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at hc
    exact hc
  set b : K := (x (Sum.inr 1) - x (Sum.inr 0)) / (y (Sum.inr 1) - y (Sum.inr 0)) with hbdef
  set s : K := (y (Sum.inr 1) - y (Sum.inr 0)) / (x (Sum.inr 1) - x (Sum.inr 0)) with hsdef
  set a : K := x (Sum.inr 0) - b * y (Sum.inr 0) with hadef
  have hbs : s * b = 1 := by
    rw [hsdef, hbdef]
    field_simp
  have hM : ∀ i j, (markedCoords.symm y).2.1 i j = b * (markedCoords.symm x).2.1 i j := by
    intro i j
    have hsub : (x (Sum.inr 1) - x (Sum.inr 0)) * (markedCoords.symm x).2.1 i j
        = (y (Sum.inr 1) - y (Sum.inr 0)) * (markedCoords.symm y).2.1 i j := by
      linear_combination hQ i j - hP i j
    rw [hbdef, div_mul_eq_mul_div, eq_div_iff hd']
    linear_combination -hsub
  have hN : ∀ i j, (markedCoords.symm y).1 i j = (markedCoords.symm x).1 i j + a * (markedCoords.symm x).2.1 i j := by
    intro i j
    rw [hadef]
    linear_combination -hP i j - y (Sum.inr 0) * hM i j
  refine ⟨affElt a b s,
    (mem_affGroup_iff _).2 (by simpa [affElt_scale, affElt_inv] using hbs), ?_⟩
  funext i
  match i with
  | Sum.inl (Sum.inl ij) =>
      show (markedCoords.symm x).1 ij.1 ij.2 + a * (markedCoords.symm x).2.1 ij.1 ij.2 = (markedCoords.symm y).1 ij.1 ij.2
      exact (hN ij.1 ij.2).symm
  | Sum.inl (Sum.inr ij) =>
      show b * (markedCoords.symm x).2.1 ij.1 ij.2 = (markedCoords.symm y).2.1 ij.1 ij.2
      exact (hM ij.1 ij.2).symm
  | Sum.inr j =>
      fin_cases j
      · show (x (Sum.inr 0) - a) * s = y (Sum.inr 0)
        rw [hadef]
        have : b * y (Sum.inr 0) * s = y (Sum.inr 0) := by
          calc b * y (Sum.inr 0) * s = (s * b) * y (Sum.inr 0) := by ring
            _ = y (Sum.inr 0) := by rw [hbs, one_mul]
        linear_combination this
      · show (x (Sum.inr 1) - a) * s = y (Sum.inr 1)
        rw [hadef, hbdef, hsdef]
        field_simp
        ring

/-- **The marked fibration.**  `Ŷ` fibres over the pairs of marked members with
fibres the two-dimensional orbits of the reparametrisation group. -/
theorem affineDim_markedPair_add_two [IsAlgClosed K] (τ : Nat.Partition n) (d : ℕ → ℕ)
    (N₀ : Matrix (Fin n) (Fin n) K) :
    affineDim (pairCoords '' (markedPair '' markedLocus τ d N₀)) + ((2 : ℕ) : WithBot ℕ∞)
      = affineDim (markedCoords '' markedLocus τ d N₀) := by
  classical
  have hmemY : ∀ z : MarkedIndex (Fin n) → K,
      z ∈ markedCoords '' markedLocus τ d N₀ ↔ markedCoords.symm z ∈ markedLocus τ d N₀ := by
    intro z
    rw [markedCoords.image_eq_preimage_symm]
    rfl
  have hmemP : ∀ g : AffIndex → K, g ∈ (AffLine.affLine K).pts ↔ g ∈ affGroup K :=
    fun g => Set.ext_iff.1 affLine_pts g
  have hP : (MvPolynomial.vanishingIdeal K (AffLine.affLine K).pts).IsPrime := by
    rw [affLine_pts, affGroup]
    refine isPrime_vanishingIdeal_graphSet isPrime_vanishingIdeal_univ ?_
    rw [vanishingIdeal_univ, Ideal.mem_bot]
    exact MvPolynomial.X_ne_zero (R := K) (1 : Fin 2)
  have himg : markPairMap '' (markedCoords '' markedLocus τ d N₀)
      = pairCoords '' (markedPair '' markedLocus τ d N₀) := by
    rw [Set.image_image, Set.image_image]
    exact Set.image_congr fun q _ => by
      rw [markPairMap, markedCoords.symm_apply_apply]
  have h := (AffLine.affLine K).affineDim_of_orbit_fibration (e := 2) hP (markAction K n)
    markAction_J isPolyMap_markPairMap (isConstructible_markedLocus τ d N₀) ?_ ?_ ?_ ?_
  · rwa [himg] at h
  · intro g hg z hz
    rw [markAction_actPt]
    exact (hmemY _).2 (markedLocus_markAct ((hmemP g).1 hg) ((hmemY z).1 hz))
  · intro g hg z _
    rw [markAction_actPt, markPairMap_markAct ((hmemP g).1 hg)]
  · rintro w ⟨y, hyY, rfl⟩
    refine ⟨y, hyY, ?_⟩
    ext z
    constructor
    · rintro ⟨hzY, hzw⟩
      rw [Set.mem_preimage, Set.mem_singleton_iff] at hzw
      obtain ⟨g, hg, hgz⟩ := exists_markAct_of_markPairMap_eq
        ((hmemY y).1 hyY) ((hmemY z).1 hzY) hzw.symm
      exact ⟨g, (hmemP g).2 hg, by rw [markAction_actPt]; exact hgz⟩
    · rintro ⟨g, hg, rfl⟩
      rw [markAction_actPt]
      exact ⟨(hmemY _).2 (markedLocus_markAct ((hmemP g).1 hg) ((hmemY y).1 hyY)),
        by rw [Set.mem_preimage, Set.mem_singleton_iff, markPairMap_markAct ((hmemP g).1 hg)]⟩
  · intro z hz
    rw [markOrbit_eq]
    exact affineDim_markOrbit ((hmemY z).1 hz).2.1

end MarkedFibration

/-! ### The reparametrisation fibration over `Kbar` -/

/-! ### The conjugation fibration in constructible form -/

section Tools

variable {K : Type u} [Field K] [IsAlgClosed K] {n : ℕ}

end Tools

/-! ### The doubled pair model

The conjugation fibration of the pair locus is assembled from two orbit fibrations on
the space of *pairs* of elements of `GL_n`: the centraliser acting on one half
(`dblLeftAction`) and on both halves (`dblBothAction`). -/

section Doubled

open AlgebraicGeometry Topology

variable {K : Type} [Field K] {n : ℕ}

/-- Index set for a pair of points of the pair model of `GL_n`. -/
abbrev DblIdx (n : ℕ) : Type := PairIndex (Fin n) ⊕ PairIndex (Fin n)

/-- The left half of a point of the doubled pair model. -/
abbrev dblL (z : DblIdx n → K) : PairIndex (Fin n) → K := fun i => z (Sum.inl i)

/-- The right half of a point of the doubled pair model. -/
abbrev dblR (z : DblIdx n → K) : PairIndex (Fin n) → K := fun i => z (Sum.inr i)

omit [Field K] in
@[simp] theorem elim_dblL_dblR (z : DblIdx n → K) : Sum.elim (dblL z) (dblR z) = z := by
  funext i
  cases i <;> rfl

/-! #### Polynomial calculus for reindexings -/

/-- A reindexing of coordinates is a polynomial map. -/
theorem isPolyMap_reindex {ι κ : Type} (ρ : κ → ι) :
    IsPolyMap fun w : ι → K => fun j => w (ρ j) :=
  ⟨fun j => MvPolynomial.X (ρ j), fun _ _ => by simp⟩

/-- Assembling two polynomial maps into a sum-indexed one. -/
theorem isPolyMap_elim {ι α β : Type} {u : (ι → K) → (α → K)} {v : (ι → K) → (β → K)}
    (hu : IsPolyMap u) (hv : IsPolyMap v) : IsPolyMap fun x => Sum.elim (u x) (v x) := by
  obtain ⟨P, hP⟩ := hu
  obtain ⟨Q, hQ⟩ := hv
  refine ⟨Sum.elim P Q, fun x i => ?_⟩
  cases i with
  | inl a => exact hP x a
  | inr b => exact hQ x b

/-- The first block of a reindexed pair of matrices is polynomial. -/
theorem isPolyMap_fstMat_comp {ι : Type} (ρ : PairIndex (Fin n) → ι) :
    IsPolyMap fun w : ι → K => matCoords (fstMat fun i => w (ρ i)) :=
  ⟨fun ij => MvPolynomial.X (ρ (Sum.inl ij)), fun _ _ => by simp⟩

/-- The second block of a reindexed pair of matrices is polynomial. -/
theorem isPolyMap_sndMat_comp {ι : Type} (ρ : PairIndex (Fin n) → ι) :
    IsPolyMap fun w : ι → K => matCoords (sndMat fun i => w (ρ i)) :=
  ⟨fun ij => MvPolynomial.X (ρ (Sum.inr ij)), fun _ _ => by simp⟩

/-- A product of two constructible sets is constructible. -/
theorem isConstructible_sumProd {α β : Type} {S : Set (α → K)} {T : Set (β → K)}
    (hS : IsAffineConstructible S) (hT : IsAffineConstructible T) : IsAffineConstructible (sumProd S T) :=
  IsAffineConstructible.inter (IsAffineConstructible.preimage (isPolyMap_reindex Sum.inl) hS)
    (IsAffineConstructible.preimage (isPolyMap_reindex Sum.inr) hT)

/-! #### Products in the pair model -/

/-! #### The centraliser action on the left half

`Geometry/Group.lean`'s `ActionPresentation.prodLeft` turns the regular action of the
centraliser on the pair model into an action on the *doubled* pair model that leaves the
right half alone; as in `Chain/Untwist`'s conjugation fibration, `actPt a` is right
multiplication by `a⁻¹`. -/

variable (K n) in
/-- The right half of the doubled pair model, as polynomials. -/
noncomputable def dblRPoly : PairIndex (Fin n) → MvPolynomial (DblIdx n) K :=
  fun j => MvPolynomial.X (Sum.inr j)

theorem aeval_dblRPoly (z : DblIdx n → K) :
    (fun j => MvPolynomial.aeval z (dblRPoly K n j)) = dblR z := by
  funext j
  simp [dblRPoly]

/-- The centraliser of `N` acting on the left half of the doubled pair model. -/
noncomputable def dblLeftAction (N : Matrix (Fin n) (Fin n) K) :
    ActionPresentation (GLPair.centralizer K n N) (DblIdx n) :=
  (GLPair.centRegularAction K n N).prodLeft (PairIndex (Fin n))

theorem dblLeftAction_J (N : Matrix (Fin n) (Fin n) K) : (dblLeftAction N).J = ⊥ :=
  ActionData.prodLeft_J_eq_bot _ _ (GLPair.centRegularAction_J N)

theorem dblLeftAction_actPt [IsAlgClosed K] (N : Matrix (Fin n) (Fin n) K) (a : PairIndex (Fin n) → K)
    (z : DblIdx n → K) :
    (dblLeftAction N).actPt a z = Sum.elim ((cAction N).act a (dblL z)) (dblR z) := by
  show ((GLPair.centRegularAction K n N).toActionData.prodLeft (PairIndex (Fin n))).actPt a z = _
  rw [ActionData.prodLeft_actPt]
  rfl

/-! #### Orbits of the centraliser -/

/-- An orbit of the centraliser action on the pair model is a fibre of the
conjugation map, hence Zariski closed. -/
theorem corbit_eq [IsAlgClosed K] [Infinite K] (N : Matrix (Fin n) (Fin n) K)
    {x : PairIndex (Fin n) → K} (hx : x ∈ glPair K n) :
    (cAction N).orbit x = glPair K n ∩ conjMap N ⁻¹' {conjMap N x} := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩
    rw [cAction_G] at ha
    exact ⟨actPt_mem_glPair ha hx, conjMap_actPt ha x⟩
  · rintro z ⟨hz, hzc⟩
    obtain ⟨a, ha, rfl⟩ := exists_actPt_of_conjMap_eq hx hz hzc
    exact ⟨a, by rw [cAction_G]; exact ha, rfl⟩

theorem isLocClosed_corbit [IsAlgClosed K] [Infinite K] (N : Matrix (Fin n) (Fin n) K)
    {x : PairIndex (Fin n) → K} (hx : x ∈ glPair K n) : IsLocClosed ((cAction N).orbit x) := by
  rw [corbit_eq N hx]
  exact IsLocClosed.of_zclosure (zclosure_inter zclosure_glPair
    (zclosure_preimage (isPolyMap_conjMap N) (zclosure_singleton _)))

theorem corbit_subset_glPair [IsAlgClosed K] [Infinite K] (N : Matrix (Fin n) (Fin n) K)
    {x : PairIndex (Fin n) → K} (hx : x ∈ glPair K n) : (cAction N).orbit x ⊆ glPair K n := by
  rw [corbit_eq N hx]
  exact Set.inter_subset_left

/-- An orbit of the centraliser is stable under the centraliser. -/
theorem cact_mem_corbit [IsAlgClosed K] [Infinite K] (N : Matrix (Fin n) (Fin n) K)
    {x₀ x : PairIndex (Fin n) → K} (hx : x ∈ (cAction N).orbit x₀)
    {a : PairIndex (Fin n) → K} (ha : a ∈ cgroup N) :
    (cAction N).act a x ∈ (cAction N).orbit x₀ := by
  rw [← (cAction N).orbit_eq_of_mem (by simp) hx]
  exact (cAction N).act_mem_orbit (by rw [cAction_G]; exact ha) x

/-- The orbits of `dblLeftAction` are products of a centraliser orbit and a point. -/
theorem dblLeftAction_orbit [IsAlgClosed K] [Infinite K] (N : Matrix (Fin n) (Fin n) K) (z : DblIdx n → K) :
    {w : DblIdx n → K | ∃ a ∈ (GLPair.centralizer K n N).pts, (dblLeftAction N).actPt a z = w}
      = sumProd ((cAction N).orbit (dblL z)) {dblR z} := by
  have hmemP : ∀ a : PairIndex (Fin n) → K,
      a ∈ (GLPair.centralizer K n N).pts ↔ a ∈ cgroup N := fun a => by rw [centralizer_pts]
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩
    rw [dblLeftAction_actPt]
    exact ⟨⟨a, by rw [cAction_G]; exact (hmemP a).1 ha, rfl⟩, rfl⟩
  · rintro w ⟨⟨a, ha, hL⟩, hR⟩
    rw [cAction_G] at ha
    refine ⟨a, (hmemP _).2 ha, ?_⟩
    have hR' : dblR z = dblR w := (Set.mem_singleton_iff.1 hR).symm
    rw [dblLeftAction_actPt, hL, hR', elim_dblL_dblR]

/-- **The product of a centraliser orbit with a constructible set**: its
dimension exceeds that of the second factor by `dim Z(N)`. -/
theorem affineDim_sumProd_corbit [IsAlgClosed K] [Infinite K] (N : Matrix (Fin n) (Fin n) K)
    {x₀ : PairIndex (Fin n) → K} (hx₀ : x₀ ∈ glPair K n) {T : Set (PairIndex (Fin n) → K)}
    (hT : IsAffineConstructible T) :
    affineDim T + ((cdim N : ℕ) : WithBot ℕ∞)
      = affineDim (sumProd ((cAction N).orbit x₀) T) := by
  classical
  have hScon : IsAffineConstructible (sumProd ((cAction N).orbit x₀) T) :=
    isConstructible_sumProd (isLocClosed_corbit N hx₀).isConstructible hT
  have hmemP : ∀ a : PairIndex (Fin n) → K,
      a ∈ (GLPair.centralizer K n N).pts ↔ a ∈ cgroup N := fun a => by rw [centralizer_pts]
  have hP : (MvPolynomial.vanishingIdeal K (GLPair.centralizer K n N).pts).IsPrime := by
    rw [centralizer_pts]; exact irreducible_cgroup N
  have hpoly : IsPolyMap (dblR : (DblIdx n → K) → PairIndex (Fin n) → K) :=
    ⟨dblRPoly K n, fun z j => (congrFun (aeval_dblRPoly z) j).symm⟩
  have himg : (dblR : (DblIdx n → K) → _) '' sumProd ((cAction N).orbit x₀) T = T := by
    refine Set.Subset.antisymm (fun t ht => ?_) (fun t ht => ?_)
    · obtain ⟨z, hz, rfl⟩ := ht
      exact hz.2
    · exact ⟨Sum.elim x₀ t, ⟨(cAction N).mem_orbit_self (by simp), ht⟩, rfl⟩
  have h := (GLPair.centralizer K n N).affineDim_of_orbit_fibration (e := cdim N) hP
    (dblLeftAction N) (dblLeftAction_J N) hpoly hScon ?_ ?_ ?_ ?_
  · rwa [himg] at h
  · intro a ha z hz
    rw [dblLeftAction_actPt]
    exact ⟨cact_mem_corbit N hz.1 ((hmemP a).1 ha), hz.2⟩
  · intro a _ z _
    rw [dblLeftAction_actPt]
    rfl
  · rw [himg]
    intro w hwT
    refine ⟨Sum.elim x₀ w, ⟨(cAction N).mem_orbit_self (by simp), hwT⟩, ?_⟩
    ext z
    constructor
    · rintro ⟨hzS, hzw⟩
      rw [Set.mem_preimage, Set.mem_singleton_iff] at hzw
      obtain ⟨a, ha, haz⟩ := hzS.1
      rw [cAction_G] at ha
      refine ⟨a, (hmemP _).2 ha, ?_⟩
      rw [dblLeftAction_actPt]
      show Sum.elim ((cAction N).act a x₀) w = z
      rw [show (cAction N).act a x₀ = dblL z from haz, ← hzw, elim_dblL_dblR]
    · rintro ⟨a, ha, rfl⟩
      rw [dblLeftAction_actPt]
      refine ⟨⟨?_, hwT⟩, rfl⟩
      exact cact_mem_corbit N ((cAction N).mem_orbit_self (by simp)) ((hmemP a).1 ha)
  · intro z hz
    rw [dblLeftAction_orbit, affineDim_sumProd_singleton]
    exact affineDim_orbit N (corbit_subset_glPair N hx₀ hz.1)

/-! #### The centraliser acting on both halves -/

/-- The group of the two-sided action: two copies of the centraliser
(`GroupPresentation.prod`). -/
noncomputable def dblGroup (N : Matrix (Fin n) (Fin n) K) :
    GroupPresentation K (PairIndex (Fin n) ⊕ PairIndex (Fin n)) :=
  (GLPair.centralizer K n N).prod (GLPair.centralizer K n N)

theorem dblGroup_pts (N : Matrix (Fin n) (Fin n) K) :
    (dblGroup N).pts = sumProd (cgroup N) (cgroup N) := by
  rw [dblGroup, GroupPresentation.prod_pts, centralizer_pts]
  rfl

/-- Two copies of the centraliser of `N` acting on the two halves of the doubled pair
model (`ActionPresentation.prod`). -/
noncomputable def dblBothAction (N : Matrix (Fin n) (Fin n) K) :
    ActionPresentation (dblGroup N) (DblIdx n) :=
  (GLPair.centRegularAction K n N).prod (GLPair.centRegularAction K n N)

theorem dblBothAction_J (N : Matrix (Fin n) (Fin n) K) : (dblBothAction N).J = ⊥ :=
  ActionData.prod_J_eq_bot _ _ (GLPair.centRegularAction_J N) (GLPair.centRegularAction_J N)

theorem dblBothAction_actPt [IsAlgClosed K] (N : Matrix (Fin n) (Fin n) K) (c z : DblIdx n → K) :
    (dblBothAction N).actPt c z
      = Sum.elim ((cAction N).act (dblL c) (dblL z)) ((cAction N).act (dblR c) (dblR z)) := by
  show ((GLPair.centRegularAction K n N).toActionData.prod
    (GLPair.centRegularAction K n N).toActionData).actPt c z = _
  rw [ActionData.prod_actPt]
  rfl

/-- The orbits of the two-sided action are products of centraliser orbits. -/
theorem dblBothAction_orbit [IsAlgClosed K] [Infinite K] (N : Matrix (Fin n) (Fin n) K) (z : DblIdx n → K) :
    {w : DblIdx n → K | ∃ c ∈ (dblGroup N).pts, (dblBothAction N).actPt c z = w}
      = sumProd ((cAction N).orbit (dblL z)) ((cAction N).orbit (dblR z)) := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨c, hc, rfl⟩
    rw [dblGroup_pts] at hc
    rw [dblBothAction_actPt]
    exact ⟨⟨dblL c, by rw [cAction_G]; exact hc.1, rfl⟩,
      ⟨dblR c, by rw [cAction_G]; exact hc.2, rfl⟩⟩
  · rintro w ⟨⟨a, ha, hL⟩, ⟨b, hb, hR⟩⟩
    rw [cAction_G] at ha hb
    refine ⟨Sum.elim a b, by rw [dblGroup_pts]; exact ⟨ha, hb⟩, ?_⟩
    rw [dblBothAction_actPt]
    show Sum.elim ((cAction N).act a (dblL z)) ((cAction N).act b (dblR z)) = w
    rw [show (cAction N).act a (dblL z) = dblL w from hL,
      show (cAction N).act b (dblR z) = dblR w from hR, elim_dblL_dblR]

/-- **The orbits of the two-sided action have dimension `2 dim Z(N)`.** -/
theorem affineDim_dblBothAction_orbit [IsAlgClosed K] [Infinite K]
    (N : Matrix (Fin n) (Fin n) K) {z : DblIdx n → K} (hL : dblL z ∈ glPair K n)
    (hR : dblR z ∈ glPair K n) :
    affineDim {w : DblIdx n → K | ∃ c ∈ (dblGroup N).pts, (dblBothAction N).actPt c z = w}
      = ((2 * cdim N : ℕ) : WithBot ℕ∞) := by
  have h := affineDim_sumProd_corbit N hL (isLocClosed_corbit N hR).isConstructible
  rw [affineDim_orbit N hR] at h
  rw [dblBothAction_orbit, ← h, two_mul, Nat.cast_add]

/-! #### The pencil loci in the doubled model -/

/-- The conjugate of `N` by a point of the pair model. -/
def dblConj (N : Matrix (Fin n) (Fin n) K) (x : PairIndex (Fin n) → K) : Matrix (Fin n) (Fin n) K :=
  fstMat x * N * sndMat x

theorem dblConj_mem_conjOrbit {N : Matrix (Fin n) (Fin n) K} {x : PairIndex (Fin n) → K}
    (hx : x ∈ glPair K n) : dblConj N x ∈ Chain.conjOrbit N :=
  ⟨pairUnit hx, rfl⟩

/-- Right multiplication conjugates the conjugate. -/
theorem dblConj_cact (N : Matrix (Fin n) (Fin n) K) (a x : PairIndex (Fin n) → K) :
    dblConj N ((GLPair.glPresentation K n).mulPt x a) = fstMat x * dblConj N a * sndMat x := by
  rw [glPresentation_mulPt]
  show fstMat x * fstMat a * N * (sndMat a * sndMat x)
    = fstMat x * (fstMat a * N * sndMat a) * sndMat x
  simp only [mul_assoc]

theorem isPolyMap_dblConj_comp {ι : Type} (N : Matrix (Fin n) (Fin n) K) (ρ : PairIndex (Fin n) → ι) :
    IsPolyMap fun w : ι → K => matCoords (dblConj N fun i => w (ρ i)) :=
  isPolyMap_matMul (isPolyMap_matMul (isPolyMap_fstMat_comp ρ) (isPolyMap_matConst N))
    (isPolyMap_sndMat_comp ρ)

/-- `F̃`: the elements of `GL_n` whose conjugate of `N` spans with `N` a pencil
of type `(τ, d)`. -/
def fibreGroup (N : Matrix (Fin n) (Fin n) K) (τ : Nat.Partition n) (d : ℕ → ℕ) :
    Set (PairIndex (Fin n) → K) :=
  {x | x ∈ glPair K n ∧ (N, dblConj N x - N) ∈ pencilLocus τ d}

/-- `F`: the fibre of the pair locus over `N`. -/
def fibreSet (N : Matrix (Fin n) (Fin n) K) (τ : Nat.Partition n) (d : ℕ → ℕ) :
    Set (Matrix (Fin n) (Fin n) K) :=
  {B | B ∈ Chain.conjOrbit N ∧ (N, B - N) ∈ pencilLocus τ d}

/-- `Z'`: pairs of conjugates of `N` spanning a pencil of type `(τ, d)`. -/
def pairSet (N : Matrix (Fin n) (Fin n) K) (τ : Nat.Partition n) (d : ℕ → ℕ) :
    Set (Matrix (Fin n) (Fin n) K × Matrix (Fin n) (Fin n) K) :=
  {q | q.1 ∈ Chain.conjOrbit N ∧ q.2 ∈ Chain.conjOrbit N ∧ (q.1, q.2 - q.1) ∈ pencilLocus τ d}

/-- `Ŵ`: pairs of elements of `GL_n` whose conjugates of `N` span a pencil of
type `(τ, d)`. -/
def dblLocus (N : Matrix (Fin n) (Fin n) K) (τ : Nat.Partition n) (d : ℕ → ℕ) :
    Set (DblIdx n → K) :=
  {z | dblL z ∈ glPair K n ∧ dblR z ∈ glPair K n ∧
    (dblConj N (dblL z), dblConj N (dblR z) - dblConj N (dblL z)) ∈ pencilLocus τ d}

/-- The sheared pair of conjugates, in pair coordinates. -/
def dblShear (N : Matrix (Fin n) (Fin n) K) (z : DblIdx n → K) : PairIndex (Fin n) → K :=
  pairCoords ((dblConj N (dblL z)), (dblConj N (dblR z) - dblConj N (dblL z)))

/-- The two conjugates, in pair coordinates: the map of the conjugation fibration. -/
def dblPair (N : Matrix (Fin n) (Fin n) K) (z : DblIdx n → K) : PairIndex (Fin n) → K :=
  pairCoords ((dblConj N (dblL z)), (dblConj N (dblR z)))

theorem isPolyMap_dblShear (N : Matrix (Fin n) (Fin n) K) :
    IsPolyMap (dblShear N : (DblIdx n → K) → PairIndex (Fin n) → K) :=
  isPolyMap_pairCoords (isPolyMap_dblConj_comp N Sum.inl)
    (isPolyMap_matSub (isPolyMap_dblConj_comp N Sum.inr) (isPolyMap_dblConj_comp N Sum.inl))

/-- The two conjugates, as polynomials on the doubled pair model (`Chain/Untwist`'s
`conjPoly`, renamed into each half). -/
noncomputable def dblPairPoly (N : Matrix (Fin n) (Fin n) K) :
    PairIndex (Fin n) → MvPolynomial (DblIdx n) K :=
  Sum.elim (fun ij => MvPolynomial.rename Sum.inl (conjPoly N ij))
    (fun ij => MvPolynomial.rename Sum.inr (conjPoly N ij))

theorem aeval_dblPairPoly (N : Matrix (Fin n) (Fin n) K) (z : DblIdx n → K) :
    (fun j => MvPolynomial.aeval z (dblPairPoly N j)) = dblPair N z := by
  funext j
  cases j with
  | inl ij =>
      show MvPolynomial.aeval z (MvPolynomial.rename Sum.inl (conjPoly N ij)) = _
      rw [MvPolynomial.aeval_rename]
      exact congrFun (aeval_conjPoly N (dblL z)) ij
  | inr ij =>
      show MvPolynomial.aeval z (MvPolynomial.rename Sum.inr (conjPoly N ij)) = _
      rw [MvPolynomial.aeval_rename]
      exact congrFun (aeval_conjPoly N (dblR z)) ij

/-- **`Ŵ` is constructible.** -/
theorem isConstructible_dblLocus [Infinite K] (N : Matrix (Fin n) (Fin n) K)
    (τ : Nat.Partition n) (d : ℕ → ℕ) : IsAffineConstructible (dblLocus N τ d) := by
  have hset : dblLocus N τ d =
      ((fun z : DblIdx n → K => dblL z) ⁻¹' glPair K n) ∩
        (((fun z : DblIdx n → K => dblR z) ⁻¹' glPair K n) ∩
          (dblShear N ⁻¹' (pairCoords '' pencilLocus (K := K) τ d))) := by
    rw [pairCoords.image_eq_preimage_symm]
    rfl
  rw [hset]
  exact IsAffineConstructible.inter
    (IsAffineConstructible.preimage (isPolyMap_reindex Sum.inl)
      (IsLocClosed.of_zclosure zclosure_glPair).isConstructible)
    (IsAffineConstructible.inter
      (IsAffineConstructible.preimage (isPolyMap_reindex Sum.inr)
        (IsLocClosed.of_zclosure zclosure_glPair).isConstructible)
      (IsAffineConstructible.preimage (isPolyMap_dblShear N) (isConstructible_pencilLocus τ d)))

/-- **`F̃` is constructible.** -/
theorem isConstructible_fibreGroup [Infinite K] (N : Matrix (Fin n) (Fin n) K)
    (τ : Nat.Partition n) (d : ℕ → ℕ) : IsAffineConstructible (fibreGroup N τ d) := by
  have hset : fibreGroup N τ d =
      glPair K n ∩
        ((fun x : PairIndex (Fin n) → K => pairCoords (N, (dblConj N x - N))) ⁻¹'
          (pairCoords '' pencilLocus (K := K) τ d)) := by
    rw [pairCoords.image_eq_preimage_symm]
    rfl
  rw [hset]
  exact IsAffineConstructible.inter (IsLocClosed.of_zclosure zclosure_glPair).isConstructible
    (IsAffineConstructible.preimage
      (isPolyMap_pairCoords (isPolyMap_matConst N)
        (isPolyMap_matSub (isPolyMap_conjMap N) (isPolyMap_matConst N)))
      (isConstructible_pencilLocus τ d))

/-! #### The fibre group fibres over the fibre `F` -/

theorem fibreGroup_eq (N : Matrix (Fin n) (Fin n) K) (τ : Nat.Partition n) (d : ℕ → ℕ) :
    fibreGroup N τ d = glPair K n ∩ conjMap N ⁻¹' (matCoords '' fibreSet N τ d) := by
  refine Set.Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
  · exact ⟨hx.1, ⟨dblConj N x, ⟨dblConj_mem_conjOrbit hx.1, hx.2⟩, rfl⟩⟩
  · obtain ⟨hx1, B, hB, hBx⟩ := hx
    have hBe : B = dblConj N x := matCoords.injective hBx
    rw [hBe] at hB
    exact ⟨hx1, hB.2⟩

theorem conjMap_image_fibreGroup (N : Matrix (Fin n) (Fin n) K) (τ : Nat.Partition n)
    (d : ℕ → ℕ) : conjMap N '' fibreGroup N τ d = matCoords '' fibreSet N τ d := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨dblConj N x, ⟨dblConj_mem_conjOrbit hx.1, hx.2⟩, rfl⟩
  · rintro _ ⟨B, ⟨⟨g, rfl⟩, hp⟩, rfl⟩
    exact ⟨pairCoords ((g : Matrix (Fin n) (Fin n) K), ((g⁻¹ : (Matrix (Fin n) (Fin n) K)ˣ) : Matrix (Fin n) (Fin n) K)),
      ⟨pairCoords_unit_mem g, hp⟩, rfl⟩

/-- **The fibre group fibres over `F` with fibre `Z(N)`.** -/
theorem affineDim_fibreSet_add_cdim [IsAlgClosed K] [Infinite K]
    (N : Matrix (Fin n) (Fin n) K) (τ : Nat.Partition n) (d : ℕ → ℕ) :
    affineDim (matCoords '' fibreSet N τ d) + ((cdim N : ℕ) : WithBot ℕ∞)
      = affineDim (fibreGroup N τ d) := by
  have hcon : IsAffineConstructible (glPair K n ∩ conjMap N ⁻¹' (matCoords '' fibreSet N τ d)) := by
    rw [← fibreGroup_eq]
    exact isConstructible_fibreGroup N τ d
  have h := affineDim_conj_fibration N (matCoords '' fibreSet N τ d) hcon
  rw [← fibreGroup_eq, conjMap_image_fibreGroup] at h
  exact h

/-! #### `Ŵ` is a product -/

/-- Gluing a pair `(g, k)` to the pair `(g, g k)`. -/
noncomputable def dblGlue (z : DblIdx n → K) : DblIdx n → K := Sum.elim (dblL z) ((GLPair.glPresentation K n).mulPt (dblL z) (dblR z))

/-- Its inverse, `(g, h) ↦ (g, g⁻¹ h)`. -/
noncomputable def dblUnglue (w : DblIdx n → K) : DblIdx n → K :=
  Sum.elim (dblL w) ((GLPair.glPresentation K n).mulPt ((GLPair.glPresentation K n).invPt (dblL w)) (dblR w))

theorem isPolyMap_dblGlue : IsPolyMap (dblGlue : (DblIdx n → K) → DblIdx n → K) := by
  unfold dblGlue
  simp only [glPresentation_mulPt, glPresentation_invPt]
  show IsPolyMap fun z : DblIdx n → K =>
    Sum.elim (fun i => z (Sum.inl i))
      (pairCoords (((fstMat fun i => z (Sum.inl i)) * (fstMat fun i => z (Sum.inr i))), ((sndMat fun i => z (Sum.inr i)) * (sndMat fun i => z (Sum.inl i)))))
  exact isPolyMap_elim (isPolyMap_reindex Sum.inl)
    (isPolyMap_pairCoords
      (isPolyMap_matMul (isPolyMap_fstMat_comp Sum.inl) (isPolyMap_fstMat_comp Sum.inr))
      (isPolyMap_matMul (isPolyMap_sndMat_comp Sum.inr) (isPolyMap_sndMat_comp Sum.inl)))

theorem isPolyMap_dblUnglue : IsPolyMap (dblUnglue : (DblIdx n → K) → DblIdx n → K) := by
  unfold dblUnglue
  simp only [glPresentation_mulPt, glPresentation_invPt]
  show IsPolyMap fun w : DblIdx n → K =>
    Sum.elim (fun i => w (Sum.inl i))
      (pairCoords (((sndMat fun i => w (Sum.inl i)) * (fstMat fun i => w (Sum.inr i))), ((sndMat fun i => w (Sum.inr i)) * (fstMat fun i => w (Sum.inl i)))))
  exact isPolyMap_elim (isPolyMap_reindex Sum.inl)
    (isPolyMap_pairCoords
      (isPolyMap_matMul (isPolyMap_sndMat_comp Sum.inl) (isPolyMap_fstMat_comp Sum.inr))
      (isPolyMap_matMul (isPolyMap_sndMat_comp Sum.inr) (isPolyMap_fstMat_comp Sum.inl)))

theorem dblUnglue_dblGlue {z : DblIdx n → K} (hz : dblL z ∈ glPair K n) :
    dblUnglue (dblGlue z) = z := by
  simp only [dblGlue, dblUnglue, glPresentation_mulPt, glPresentation_invPt,
    fstMat_pairCoords, sndMat_pairCoords]
  show Sum.elim (dblL z)
    (pairCoords ((sndMat (dblL z) * (fstMat (dblL z) * fstMat (dblR z))), (sndMat (dblR z) * sndMat (dblL z) * fstMat (dblL z)))) = z
  rw [← mul_assoc, hz.2, one_mul, mul_assoc, hz.2, mul_one, pairCoords_fstMat_sndMat, elim_dblL_dblR]

theorem dblGlue_dblUnglue {w : DblIdx n → K} (hw : dblL w ∈ glPair K n) :
    dblGlue (dblUnglue w) = w := by
  simp only [dblGlue, dblUnglue, glPresentation_mulPt, glPresentation_invPt,
    fstMat_pairCoords, sndMat_pairCoords]
  show Sum.elim (dblL w)
    (pairCoords ((fstMat (dblL w) * (sndMat (dblL w) * fstMat (dblR w))), (sndMat (dblR w) * fstMat (dblL w) * sndMat (dblL w)))) = w
  rw [← mul_assoc, hw.1, one_mul, mul_assoc, hw.1, mul_one, pairCoords_fstMat_sndMat, elim_dblL_dblR]

/-- **Gluing identifies `GL_n × F̃` with `Ŵ`.** -/
theorem dblGlue_image (N : Matrix (Fin n) (Fin n) K) (τ : Nat.Partition n) (d : ℕ → ℕ) :
    dblGlue '' sumProd (glPair K n) (fibreGroup N τ d) = dblLocus N τ d := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨z, ⟨hg, hk⟩, rfl⟩
    refine ⟨hg, ?_, ?_⟩
    · rw [glPair_eq_pts]
      exact (GLPair.glPresentation K n).mulPt_mem ((by rw [← glPair_eq_pts]; exact hg)) ((by rw [← glPair_eq_pts]; exact hk.1))
    have hc := pencilLocus_conj (pairUnit hg) hk.2
    have he : dblConj N ((GLPair.glPresentation K n).mulPt (dblL z) (dblR z)) - dblConj N (dblL z)
        = fstMat (dblL z) * (dblConj N (dblR z) - N) * sndMat (dblL z) := by
      rw [dblConj_cact, mul_sub, sub_mul]
      rfl
    show (dblConj N (dblL z), dblConj N ((GLPair.glPresentation K n).mulPt (dblL z) (dblR z)) - dblConj N (dblL z))
      ∈ pencilLocus τ d
    rw [he]
    exact hc
  · intro w hw
    refine ⟨dblUnglue w, ⟨hw.1, ?_, ?_⟩, dblGlue_dblUnglue hw.1⟩
    · rw [glPair_eq_pts]
      exact (GLPair.glPresentation K n).mulPt_mem
        ((GLPair.glPresentation K n).invPt_mem ((by rw [← glPair_eq_pts]; exact hw.1)))
        ((by rw [← glPair_eq_pts]; exact hw.2.1))
    · have hN : sndMat (dblL w) * dblConj N (dblL w) * fstMat (dblL w) = N := by
        show sndMat (dblL w) * (fstMat (dblL w) * N * sndMat (dblL w)) * fstMat (dblL w) = N
        rw [← mul_assoc, ← mul_assoc, hw.1.2, one_mul, mul_assoc, hw.1.2, mul_one]
      have hk2 : dblConj N ((GLPair.glPresentation K n).mulPt ((GLPair.glPresentation K n).invPt (dblL w)) (dblR w)) - N
          = sndMat (dblL w) * (dblConj N (dblR w) - dblConj N (dblL w)) * fstMat (dblL w) := by
        rw [dblConj_cact, glPresentation_invPt, fstMat_pairCoords, sndMat_pairCoords]
        show sndMat (dblL w) * dblConj N (dblR w) * fstMat (dblL w) - N = _
        rw [mul_sub, sub_mul, hN]
      have hc := pencilLocus_conj (pairUnit hw.1)⁻¹ hw.2.2
      have hpair : (N, dblConj N ((GLPair.glPresentation K n).mulPt ((GLPair.glPresentation K n).invPt (dblL w)) (dblR w)) - N)
          = (sndMat (dblL w) * dblConj N (dblL w) * fstMat (dblL w),
            sndMat (dblL w) * (dblConj N (dblR w) - dblConj N (dblL w)) * fstMat (dblL w)) := by
        rw [hk2, hN]
      show (N, dblConj N ((GLPair.glPresentation K n).mulPt ((GLPair.glPresentation K n).invPt (dblL w)) (dblR w)) - N) ∈ pencilLocus τ d
      rw [hpair]
      exact hc

/-- **`dim Ŵ = dim (GL_n × F̃)`.** -/
theorem affineDim_dblLocus [IsAlgClosed K] (N : Matrix (Fin n) (Fin n) K)
    (τ : Nat.Partition n) (d : ℕ → ℕ) :
    affineDim (dblLocus N τ d) = affineDim (sumProd (glPair K n) (fibreGroup N τ d)) := by
  rw [← dblGlue_image]
  exact affineDim_image_eq isPolyMap_dblGlue isPolyMap_dblUnglue fun z hz =>
    dblUnglue_dblGlue hz.1

/-! #### The dimension of `GL_n × F̃` -/

theorem cgroup_zero : cgroup (0 : Matrix (Fin n) (Fin n) K) = glPair K n := by
  ext x
  rw [mem_cgroup]
  simp

theorem corbit_cone_zero [IsAlgClosed K] [Infinite K] :
    (cAction (0 : Matrix (Fin n) (Fin n) K)).orbit ((GLPair.glPresentation K n).one) = glPair K n := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩
    rw [cAction_G, cgroup_zero] at ha
    rw [cAction_act_one, glPair_eq_pts]
    exact (GLPair.glPresentation K n).invPt_mem ((by rw [← glPair_eq_pts]; exact ha))
  · intro x hx
    refine ⟨(GLPair.glPresentation K n).invPt x, ?_, ?_⟩
    · rw [cAction_G, cgroup_zero, glPair_eq_pts]
      exact (GLPair.glPresentation K n).invPt_mem ((by rw [← glPair_eq_pts]; exact hx))
    · rw [cAction_act_one, glPresentation_invPt_invPt]

theorem cdim_zero [IsAlgClosed K] [Infinite K] :
    cdim (0 : Matrix (Fin n) (Fin n) K) = n * n := by
  have h := affineDim_cgroup (0 : Matrix (Fin n) (Fin n) K)
  rw [cgroup_zero, affineDim_glPair] at h
  exact_mod_cast h.symm

/-- **The product of `GL_n` with a constructible set** has dimension `n²` more
than the second factor. -/
theorem affineDim_glPair_sumProd [IsAlgClosed K] [Infinite K] {T : Set (PairIndex (Fin n) → K)}
    (hT : IsAffineConstructible T) :
    affineDim T + ((n * n : ℕ) : WithBot ℕ∞) = affineDim (sumProd (glPair K n) T) := by
  have h := affineDim_sumProd_corbit (0 : Matrix (Fin n) (Fin n) K)
    (by rw [glPair_eq_pts]; exact (GLPair.glPresentation K n).one_mem_pts) hT
  rwa [corbit_cone_zero, cdim_zero] at h

/-! #### The fibration `Ŵ → Z'` -/

theorem dblConj_act_of_mem_cgroup [IsAlgClosed K] {N : Matrix (Fin n) (Fin n) K}
    {a : PairIndex (Fin n) → K} (ha : a ∈ cgroup N) (x : PairIndex (Fin n) → K) :
    dblConj N ((cAction N).act a x) = dblConj N x :=
  matCoords.injective (conjMap_actPt ha x)

theorem dblBothAction_mem_dblLocus [IsAlgClosed K] {N : Matrix (Fin n) (Fin n) K} {τ : Nat.Partition n}
    {d : ℕ → ℕ} {c : DblIdx n → K} (hc : c ∈ (dblGroup N).pts) {z : DblIdx n → K}
    (hz : z ∈ dblLocus N τ d) : (dblBothAction N).actPt c z ∈ dblLocus N τ d := by
  rw [dblGroup_pts] at hc
  rw [dblBothAction_actPt]
  refine ⟨actPt_mem_glPair hc.1 hz.1, actPt_mem_glPair hc.2 hz.2.1, ?_⟩
  show (dblConj N ((cAction N).act (dblL c) (dblL z)),
    dblConj N ((cAction N).act (dblR c) (dblR z))
      - dblConj N ((cAction N).act (dblL c) (dblL z))) ∈ pencilLocus τ d
  rw [dblConj_act_of_mem_cgroup hc.1, dblConj_act_of_mem_cgroup hc.2]
  exact hz.2.2

theorem dblPair_dblBothAction [IsAlgClosed K] {N : Matrix (Fin n) (Fin n) K} {c : DblIdx n → K}
    (hc : c ∈ (dblGroup N).pts) (z : DblIdx n → K) :
    dblPair N ((dblBothAction N).actPt c z) = dblPair N z := by
  rw [dblGroup_pts] at hc
  rw [dblBothAction_actPt]
  show pairCoords ((dblConj N ((cAction N).act (dblL c) (dblL z))),
      (dblConj N ((cAction N).act (dblR c) (dblR z))))
    = pairCoords ((dblConj N (dblL z)), (dblConj N (dblR z)))
  rw [dblConj_act_of_mem_cgroup hc.1, dblConj_act_of_mem_cgroup hc.2]

/-- The image of `Ŵ` under the two conjugates is `Z'`. -/
theorem dblPair_image (N : Matrix (Fin n) (Fin n) K) (τ : Nat.Partition n) (d : ℕ → ℕ) :
    dblPair N '' dblLocus N τ d = pairCoords '' pairSet N τ d := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨z, hz, rfl⟩
    exact ⟨(dblConj N (dblL z), dblConj N (dblR z)),
      ⟨dblConj_mem_conjOrbit hz.1, dblConj_mem_conjOrbit hz.2.1, hz.2.2⟩, rfl⟩
  · rintro _ ⟨q, ⟨⟨g, hg⟩, ⟨h, hh⟩, hp⟩, rfl⟩
    refine ⟨Sum.elim
      (pairCoords ((g : Matrix (Fin n) (Fin n) K), ((g⁻¹ : (Matrix (Fin n) (Fin n) K)ˣ) : Matrix (Fin n) (Fin n) K)))
      (pairCoords ((h : Matrix (Fin n) (Fin n) K), ((h⁻¹ : (Matrix (Fin n) (Fin n) K)ˣ) : Matrix (Fin n) (Fin n) K))),
      ⟨pairCoords_unit_mem g, pairCoords_unit_mem h, ?_⟩, ?_⟩
    · show ((g : Matrix (Fin n) (Fin n) K) * N *
          ((g⁻¹ : (Matrix (Fin n) (Fin n) K)ˣ) : Matrix (Fin n) (Fin n) K),
        (h : Matrix (Fin n) (Fin n) K) * N *
            ((h⁻¹ : (Matrix (Fin n) (Fin n) K)ˣ) : Matrix (Fin n) (Fin n) K) -
          (g : Matrix (Fin n) (Fin n) K) * N *
            ((g⁻¹ : (Matrix (Fin n) (Fin n) K)ˣ) : Matrix (Fin n) (Fin n) K))
        ∈ pencilLocus τ d
      rw [← hg, ← hh]
      exact hp
    · show pairCoords (((g : Matrix (Fin n) (Fin n) K) * N *
          ((g⁻¹ : (Matrix (Fin n) (Fin n) K)ˣ) : Matrix (Fin n) (Fin n) K)), ((h : Matrix (Fin n) (Fin n) K) * N *
          ((h⁻¹ : (Matrix (Fin n) (Fin n) K)ˣ) : Matrix (Fin n) (Fin n) K))) = pairCoords q
      rw [← hg, ← hh]

/-- **The fibration `Ŵ → Z'`**: its fibres are the orbits of the two-sided
centraliser action. -/
theorem affineDim_pairSet_add_two_cdim [IsAlgClosed K] [Infinite K]
    (N : Matrix (Fin n) (Fin n) K) (τ : Nat.Partition n) (d : ℕ → ℕ) :
    affineDim (pairCoords '' pairSet N τ d) + ((2 * cdim N : ℕ) : WithBot ℕ∞)
      = affineDim (dblLocus N τ d) := by
  classical
  have hP : (MvPolynomial.vanishingIdeal K (dblGroup N).pts).IsPrime := by
    rw [dblGroup_pts]
    exact irreducible_prod (irreducible_cgroup N) (irreducible_cgroup N)
  have hpoly : IsPolyMap (dblPair N) :=
    ⟨dblPairPoly N, fun z j => (congrFun (aeval_dblPairPoly N z) j).symm⟩
  have h := (dblGroup N).affineDim_of_orbit_fibration (e := 2 * cdim N) hP (dblBothAction N)
    (dblBothAction_J N) hpoly (isConstructible_dblLocus N τ d) ?_ ?_ ?_ ?_
  · rwa [dblPair_image N τ d] at h
  · intro c hc z hz
    exact dblBothAction_mem_dblLocus hc hz
  · intro c hc z _
    rw [dblPair_dblBothAction hc]
  · rintro w ⟨y, hy, rfl⟩
    refine ⟨y, hy, ?_⟩
    ext z
    constructor
    · rintro ⟨hzD, hzw⟩
      rw [Set.mem_preimage, Set.mem_singleton_iff] at hzw
      have h1 : conjMap N (dblL z) = conjMap N (dblL y) := by
        funext ij
        exact congrFun hzw (Sum.inl ij)
      have h2 : conjMap N (dblR z) = conjMap N (dblR y) := by
        funext ij
        exact congrFun hzw (Sum.inr ij)
      obtain ⟨a, ha, haz⟩ := exists_actPt_of_conjMap_eq hy.1 hzD.1 h1
      obtain ⟨b, hb, hbz⟩ := exists_actPt_of_conjMap_eq hy.2.1 hzD.2.1 h2
      refine ⟨Sum.elim a b, by rw [dblGroup_pts]; exact ⟨ha, hb⟩, ?_⟩
      rw [dblBothAction_actPt]
      show Sum.elim ((cAction N).act a (dblL y)) ((cAction N).act b (dblR y)) = z
      rw [show (cAction N).act a (dblL y) = dblL z from haz,
        show (cAction N).act b (dblR y) = dblR z from hbz, elim_dblL_dblR]
    · rintro ⟨c, hc, rfl⟩
      exact ⟨dblBothAction_mem_dblLocus hc hy, by
        rw [Set.mem_preimage, Set.mem_singleton_iff, dblPair_dblBothAction hc]⟩
  · intro z hz
    exact affineDim_dblBothAction_orbit N hz.1 hz.2.1

/-- **The conjugation fibration of the pair locus, over an algebraically closed field**: the
dimension of `Z'` is that of the orbit plus that of the fibre `F`. -/
theorem affineDim_pairSet [IsAlgClosed K] [Infinite K] (N : Matrix (Fin n) (Fin n) K)
    (τ : Nat.Partition n) (d : ℕ → ℕ) :
    affineDim (pairCoords '' pairSet N τ d)
      = affineDim (matCoords '' Chain.conjOrbit N) + affineDim (matCoords '' fibreSet N τ d) := by
  refine Toolbox.add_natCast_right_cancel (c := 2 * cdim N) ?_
  rw [affineDim_pairSet_add_two_cdim, affineDim_dblLocus,
    ← affineDim_glPair_sumProd (isConstructible_fibreGroup N τ d),
    ← affineDim_fibreSet_add_cdim, ← affineDim_conjOrbit_add_cdim N, two_mul, Nat.cast_add]
  abel

end Doubled

/-! ### `thm:conditional-height`: (H1) and (H2′) give `cor:flagless`

The objects (the shear
`(A, B) ↦ (A, B − A)`, the marking map `ψ = markedPair`, the finite index type
`Strata n`) are in `Chain/Conditional.lean`; the count lives here because it
consumes the fibration theorems above. -/

section ConditionalCount

variable {K : Type} [Field K] [IsAlgClosed K] [Infinite K] {n : ℕ}

/-- **The per-stratum count** `f_{τ,d} ≤ dim Fl_{τ'} ≤ C(n,2)`, split as
in the paper into the case `c(λ) ≤ c(τ)` — where the shear
`(A, B) ↦ (A, B − A)` (`Height.Geometry.affineDim_image_eq`) sends `Z'` into
`Î_{τ,d}` and (H1) applies — and the case `c(τ) < c(λ)`, where `Z'` lies in the
image of the marked incidence under `ψ = markedPair` and (H2′) applies. -/
theorem affineDim_fibreSet_le (N : Matrix (Fin n) (Fin n) K) (hN : IsNilpotent N)
    (τ : Nat.Partition n) (d : ℕ → ℕ)
    (h1 : PencilIncidenceBound (K := K) τ d)
    (h2 : IsDegeneration τ N → cType τ < cOf N → MarkedIncidenceBound τ d N) :
    affineDim (matCoords '' fibreSet N τ d) ≤ (((n.choose 2 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
  classical
  rcases Set.eq_empty_or_nonempty (fibreSet N τ d) with hemp | ⟨B₀, hB₀⟩
  · rw [hemp, Set.image_empty, (Height.Geometry.affineDim_eq_bot_iff _).2 rfl]
    exact bot_le
  have h2D := Height.Pencil.two_dimFl τ
  have hcn := le_cType τ
  have hcle := Height.Pencil.cType_le τ
  have hch := two_mul_choose_two_add n
  have hfibeq := affineDim_pairSet N τ d
  rw [affineDim_conjOrbit N hN] at hfibeq
  by_cases hcase : cOf N ≤ cType τ
  · -- Case `τ = λ`: (H1) through the shear `(A, B) ↦ (A, B - A)`.
    have hshear : shearPair '' (pairCoords '' pairSet N τ d)
        ⊆ pairCoords '' pencilLocus (K := K) τ d := by
      rintro _ ⟨_, ⟨q, hq, rfl⟩, rfl⟩
      exact ⟨(q.1, q.2 - q.1), hq.2.2, (shearPair_pairCoords q.1 q.2).symm⟩
    have hdimshear : affineDim (shearPair '' (pairCoords '' pairSet N τ d))
        = affineDim (pairCoords '' pairSet N τ d) :=
      Height.Geometry.affineDim_image_eq isPolyMap_shearPair isPolyMap_unshearPair
        fun x _ => unshear_shear x
    have hle : affineDim (pairCoords '' pairSet N τ d)
        ≤ (((3 * Height.Pencil.dimFl τ : ℕ) : ℕ∞) : WithBot ℕ∞) := by
      rw [← hdimshear]
      exact le_trans (Height.Geometry.affineDim_mono hshear) h1
    rw [hfibeq] at hle
    exact le_natCast_of_add_le hle fun cf hcf => by omega
  · -- Case `λ ◁ τ`: (H2′) through the marked incidence.
    rw [not_le] at hcase
    have hdegen : IsDegeneration τ N := isDegeneration_of_genericType hB₀.2.2.1
    have hsub : pairCoords '' pairSet N τ d
        ⊆ pairCoords '' (markedPair '' markedLocus (K := K) τ d N) := by
      rintro _ ⟨q, hq, rfl⟩
      have h1' : q.1 + (0 : K) • (q.2 - q.1) = q.1 := by simp
      have h2' : q.1 + (1 : K) • (q.2 - q.1) = q.2 := by rw [one_smul]; abel
      refine ⟨markedPair (q.1, q.2 - q.1, 0, 1), ⟨(q.1, q.2 - q.1, 0, 1),
        ⟨hq.2.2, zero_ne_one, ?_, ?_⟩, rfl⟩, ?_⟩
      · show q.1 + (0 : K) • (q.2 - q.1) ∈ orbitClosure N
        rw [h1']
        exact conjOrbit_subset_orbitClosure N hq.1
      · show q.1 + (1 : K) • (q.2 - q.1) ∈ orbitClosure N
        rw [h2']
        exact conjOrbit_subset_orbitClosure N hq.2.1
      · show pairCoords (q.1 + (0 : K) • (q.2 - q.1), q.1 + (1 : K) • (q.2 - q.1)) = pairCoords q
        rw [h1', h2']
    have hmark : affineDim (pairCoords '' (markedPair '' markedLocus (K := K) τ d N))
        + (((2 : ℕ) : ℕ∞) : WithBot ℕ∞)
        = affineDim (markedCoords '' markedLocus τ d N) := by
      exact_mod_cast affineDim_markedPair_add_two τ d N
    have hle : affineDim (pairCoords '' pairSet N τ d) +
        (((2 : ℕ) : ℕ∞) : WithBot ℕ∞) + (((cOf N - cType τ : ℕ) : ℕ∞) : WithBot ℕ∞)
        ≤ (((3 * Height.Pencil.dimFl τ + 2 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
      refine le_trans (add_le_add (add_le_add (Height.Geometry.affineDim_mono hsub) le_rfl)
        le_rfl) ?_
      rw [hmark]
      exact h2 hdegen hcase
    rw [hfibeq] at hle
    have hle' : ((((n * n - cOf N) + 2 + (cOf N - cType τ) : ℕ) : ℕ∞) : WithBot ℕ∞) +
        affineDim (matCoords '' fibreSet N τ d)
        ≤ (((3 * Height.Pencil.dimFl τ + 2 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
      refine le_trans (le_of_eq ?_) hle
      push_cast
      ring
    exact le_natCast_of_add_le hle' fun cf hcf => by omega

omit [IsAlgClosed K] in
/-- **The covering**: the flagless partners in the orbit are covered by the finitely
many strata `(τ, d)` with `d ≠ 0` and `d_k ≤ k(n − m_k)`. -/
theorem flaglessPartner_subset_iUnion (N : Matrix (Fin n) (Fin n) K) :
    Height.Steenrod.flaglessPartnerLocus n N ∩ Chain.conjOrbit N ⊆
      ⋃ q : Strata n, fibreSet N q.1.1 q.1.2 := by
  rintro B ⟨hflag, horb⟩
  have hnil : Height.Steenrod.NilpotentPencil N (B - N) := by
    have h := hflag.1.linearCombination 1 0 (-1) 1
    simpa [neg_add_eq_sub] using h
  have hflag' : Height.Steenrod.FlaglessPencil K n N (B - N) := by
    refine ⟨hnil, fun htri => hflag.2 ?_⟩
    obtain ⟨g, hg1, hg2⟩ := htri
    refine ⟨g, hg1, ?_⟩
    have hsplit : (↑g⁻¹ : Matrix (Fin n) (Fin n) K) * B * (g : Matrix (Fin n) (Fin n) K)
        = (↑g⁻¹ : Matrix (Fin n) (Fin n) K) * N * (g : Matrix (Fin n) (Fin n) K) +
          (↑g⁻¹ : Matrix (Fin n) (Fin n) K) * (B - N) * (g : Matrix (Fin n) (Fin n) K) := by
      rw [← Matrix.add_mul, ← Matrix.mul_add]
      congr 2
      abel
    rw [hsplit]
    exact Submodule.add_mem _ hg1 hg2
  obtain ⟨τ, d, hgen, hmulti, hbound⟩ := exists_multidegree hnil
  have hd : d ≠ 0 := multidegree_ne_zero_of_flagless hflag' hmulti
  exact Set.mem_iUnion.2 ⟨⟨(τ, d), hd, hbound⟩, horb, hnil, hgen, hmulti⟩

/-- **`thm:conditional-height`**: (H1) and (H2′) bound the flagless partners of a
nilpotent `N` inside its orbit by `C(n,2)`.  The hypotheses are the paper's, and
nothing else. -/
theorem affineDim_flaglessPartners_le_of_bounds
    (h1 : ∀ (τ : Nat.Partition n) (d : ℕ → ℕ), d ≠ 0 → PencilIncidenceBound (K := K) τ d)
    (h2 : ∀ (τ : Nat.Partition n) (d : ℕ → ℕ) (N₀ : Matrix (Fin n) (Fin n) K), d ≠ 0 →
      IsNilpotent N₀ → IsDegeneration τ N₀ → cType τ < cOf N₀ → MarkedIncidenceBound τ d N₀)
    (N : Matrix (Fin n) (Fin n) K) (hN : IsNilpotent N) :
    affineDim (matCoords '' (Height.Steenrod.flaglessPartnerLocus n N ∩ Chain.conjOrbit N))
      ≤ (((n.choose 2 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
  classical
  refine le_trans (Height.Geometry.affineDim_mono
    (Set.image_mono (flaglessPartner_subset_iUnion N))) ?_
  rw [Set.image_iUnion, Height.Geometry.affineDim_iUnion]
  refine iSup_le fun q => ?_
  exact affineDim_fibreSet_le N hN q.1.1 q.1.2 (h1 q.1.1 q.1.2 q.2.1)
    fun hdeg hc => h2 q.1.1 q.1.2 N q.2.1 hN hdeg hc

end ConditionalCount

end Height.Chain
