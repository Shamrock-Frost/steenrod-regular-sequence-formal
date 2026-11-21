import Height.Chain.Star
import Height.Chain.Incidence
import Height.Orbital.OrbitArc
import Height.Orbital.KKConjugation
import Height.Pencil.FlagVelocityArc

/-!
# `thm:reduction`: shifted isotropy from `(∗)`

The paper, `thm:reduction`.  The node of the chain is `Height.Chain.shiftedIsotropy`
(`Chain/Edges.lean`); this file proves its core, `siPairing_eq_zero_of_psiMap`.

## What is proved here

`siPairing_eq_zero_of_psiMap`: on a component `V(I)` of the incidence, given

* the map `ψ` of `thm:reduction` as a `PsiMap C.I` — the geometric content of
  the theorem, built in `Chain/Psi.lean` from the frame;
* kernel flatness (`Isotropy.DCond` over `K⟦u⟧`, `lem:flag-flat`(1)) for the
  two marked arcs at hand — proved in `Chain/LocalFlat.lean` (`siLocalFlat`);
  see `Pencil/LocalModel.lean` for why the function-field form does
  not suffice, and note that the `∂_u P` half is proved outright
  (`Pencil.dcond_dPat`),

one gets the vanishing of the shifted pairing on a dense open of `V(I)`.  The
mathematics of the step is `lem:flag-velocity`
(`Pencil/FlagVelocityArc.lean`): the shifted pairing at the marked point *is*
the Kostant–Kirillov pairing of the fibre motions, and `(∗)` kills the latter
as soon as they are velocities of arcs in an irreducible `Z ⊆ 𝔫` at a generic
point of `Z` — which is what `PsiMap` provides.  `star_kk_vanishing` is `(∗)`
in exactly that form (the passage from the transporters produced by
`star_general` to the flag representatives `W_i` is `kk_wellDefined`); the
point of `Z` is the *conjugate* `ψ(z)` of the member at the moving point, not
the member itself, so `PsiMap` carries the conjugating matrix and the transfer
uses `kkForm_matrixConjugation`.

## Where `PsiMap` comes from

The paper builds it from the fibre-flag morphism `Φ` on `𝒴_λ`, a big-cell
section `g` of `GL_n → Fl_{τ'}` with `g(V_•) = 1`, and
`ψ(z') := g(Φ(z'))⁻¹ P'(x') g(Φ(z'))`, taking `Z :=` the closure of `ψ(V)`
intersected with `O_λ` and refining the fibre flag to a complete flag so that
`Z ⊆ O_λ ∩ 𝔫_F`; `dψ` carries the arc velocities of `V` to the fibre motions
of `lem:local-model`(3), and the two dense opens are matched by pulling `g`
back along `ψ`.  `Chain/Psi.lean` reduces the construction to an adapted
frame, and `Chain/Frame.lean` to the geometric frame, which is proved there
(`nonempty_geometricFrame`).
-/

namespace Height.Chain

open Matrix Height.Orbital Height.Steenrod Height.Pencil
open Height.Geometry (SIIndex SIPoint siCoords PairIndex pairCoords fstMat sndMat matCoords
  MarkedIndex markedCoords)

universe u

section General

variable {K : Type u} [Field K] {n : ℕ}

/-- Conjugation by an invertible matrix is multiplicative. -/
theorem matConj_mul (c : (Matrix (Fin n) (Fin n) K)ˣ) (A B : Matrix (Fin n) (Fin n) K) :
    Height.Toolbox.matrixConjugationLinearEquiv K n c (A * B)
      = Height.Toolbox.matrixConjugationLinearEquiv K n c A *
          Height.Toolbox.matrixConjugationLinearEquiv K n c B := by
  simp only [Height.Toolbox.matrixConjugationLinearEquiv_apply]
  simp [Matrix.mul_assoc]

/-- Over an infinite field a nilpotent pencil is nilpotent as a matrix over
`K[μ,ν]`: the entries of `P^n` are polynomials vanishing at every point, by
Cayley–Hamilton on the members. -/
theorem pencil_pow_eq_zero_of_nilpotentPencil [Infinite K]
    {N M : Matrix (Fin n) (Fin n) K} (hnil : NilpotentPencil N M) :
    pencil N M ^ n = 0 := by
  refine Matrix.ext fun i j => ?_
  show (pencil N M ^ n) i j = 0
  refine MvPolynomial.funext fun x => ?_
  have hmap : (pencil N M ^ n).map (MvPolynomial.eval x)
      = ((pencil N M).map (MvPolynomial.eval x)) ^ n := by
    show ((MvPolynomial.eval x).mapMatrix (pencil N M ^ n)) = _
    rw [map_pow]
    rfl
  have hval : (pencil N M).map (MvPolynomial.eval x) = x 0 • N + x 1 • M := by
    ext a b
    show MvPolynomial.eval x
        (MvPolynomial.C (N a b) * Height.Graded.mu + MvPolynomial.C (M a b) * Height.Graded.nu)
      = _
    simp [Height.Graded.mu, Height.Graded.nu, Matrix.add_apply, mul_comm]
  have h0 : (pencil N M ^ n).map (MvPolynomial.eval x) = 0 := by
    rw [hmap, hval]
    exact Height.Orbital.pow_card_eq_zero_of_isNilpotent (hnil (x 0) (x 1))
  have h1 := congrFun (congrFun h0 i) j
  simpa using h1

/-- A decomposition `Ṙ = [P, W] + U` of the shifted velocity representative at
the marked point `q` for the marked velocity `v` with witness `Z`
(`lem:local-model`(3)): `W` moves the frame, `U` lowers the fibre flag. -/
structure IsVelocityDecomp (q v : SIPoint (Fin n) K) (Z : Matrix (Fin n) (Fin n) K)
    (W U : Matrix (Fin n) (Fin n) (PowerSeries K)) : Prop where
  rdot : Rdot q.1 q.2.1 q.2.2 (pencil v.1 v.2.1) v.2.2 Z
    = (Pat q.1 q.2.1 q.2.2 * W - W * Pat q.1 q.2.1 q.2.2) + U
  lowering : Lowering (Pat q.1 q.2.1 q.2.2) U

/-- A witness that `Y` is a fibre motion of the marked velocity `v` with
witness `Z`: a decomposition of `lem:local-model`(3) whose lowering part has
value `Y` at the point. -/
structure SIFibreMotion (q v : SIPoint (Fin n) K) (Z Y : Matrix (Fin n) (Fin n) K) where
  /-- the frame motion -/
  W : Matrix (Fin n) (Fin n) (PowerSeries K)
  /-- the lowering part -/
  U : Matrix (Fin n) (Fin n) (PowerSeries K)
  decomp : IsVelocityDecomp q v Z W U
  value : Y = matC U

/-- An arc in `Z = V(P)` based at `w` with velocity `Y`. -/
structure NilArc (P : Ideal (MvPolynomial (Fin n × Fin n) K)) (w : Fin n × Fin n → K)
    (Y : Matrix (Fin n) (Fin n) K) where
  /-- the arc -/
  b : Matrix (Fin n) (Fin n) (PowerSeries K)
  inLocus : ArcInLocus P b
  base : matC b = matCoords.symm w
  vel : matD b = Y

/-- The image of a point `z` of the incidence under the map `ψ` of
`thm:reduction`, off `V(g)`: a point `w ∈ Z ∖ V(g)` and a conjugation `c`
(`g(Φ)` of the paper) carrying the member at the marked point of `z` to
`w`, under which every fibre motion of a marked arc at `z` becomes the
velocity of an arc in `Z` at `w`. -/
structure PsiImage (I : Ideal (MvPolynomial (SIIndex (Fin n)) K))
    (P : Ideal (MvPolynomial (Fin n × Fin n) K)) (g : MvPolynomial (Fin n × Fin n) K)
    (z : SIIndex (Fin n) → K) where
  /-- the point of `Z` -/
  w : Fin n × Fin n → K
  /-- the conjugation -/
  c : (Matrix (Fin n) (Fin n) K)ˣ
  mem : w ∈ MvPolynomial.zeroLocus K P
  g_ne : MvPolynomial.eval w g ≠ 0
  conj : matCoords.symm w
    = Height.Toolbox.matrixConjugationLinearEquiv K n c (siMember (siCoords.symm z))
  /-- `dψ` carries fibre motions to velocities of arcs in `Z` -/
  arcs : ∀ (m : MarkedArc I z) (Y : Matrix (Fin n) (Fin n) K),
    SIFibreMotion (siCoords.symm z) m.a.vel m.Z Y →
    Nonempty (NilArc P w (Height.Toolbox.matrixConjugationLinearEquiv K n c Y))

/-- The map `ψ` of `thm:reduction` on a component `V(I)` of the incidence: an
irreducible `Z = V(P) ⊆ 𝔫`, and above every dense open `Z ∖ V(g)` a dense open
`V(I) ∖ V(h)` each of whose points has a `ψ`-image in it. -/
structure PsiMap (I : Ideal (MvPolynomial (SIIndex (Fin n)) K)) where
  /-- the prime of `Z` -/
  P : Ideal (MvPolynomial (Fin n × Fin n) K)
  prime : P.IsPrime
  /-- `Z` lies in the strictly upper triangular matrices -/
  upper : ∀ x ∈ MvPolynomial.zeroLocus K P, IsStrictlyUpper (matCoords.symm x)
  image : ∀ g ∉ P, ∃ h ∉ I, ∀ z ∈ MvPolynomial.zeroLocus K I,
    MvPolynomial.eval z h ≠ 0 → Nonempty (PsiImage I P g z)

end General

/-! ## The node `(∗)` in coordinates

These two live at `K : Type` because they mention the geometry API's
`KKIsotropic` (the scheme `Vsch I` is a `Type`-level object); the chain runs at
`Kbar p r : Type`. -/

section Node

variable {K : Type} [Field K] {n : ℕ}

/-- **The node `(∗)` read in coordinates**: at a generic point of an irreducible
`Z = V(P) ⊆ 𝔫`, the Kostant–Kirillov form kills any two matrices whose
commutators with the point are velocities of arcs in `Z`.  The hypothesis is the
node `Height.Chain.nilcone_kkIsotropic` (`Chain/Star.lean`); the arcs cross by
`Height.Orbital.matArcEquiv`, and the passage from the witness directions of
`KKWitness` to arbitrary representatives is `kk_wellDefined`. -/
theorem star_kk_vanishing [IsAlgClosed K]
    (P : Ideal (MvPolynomial (Fin n × Fin n) K)) (hP : P.IsPrime)
    (hstar : Height.Orbital.KKIsotropic P) :
    ∃ g ∉ P, ∀ z ∈ MvPolynomial.zeroLocus K P, MvPolynomial.eval z g ≠ 0 →
      ∀ b₁ b₂ : Matrix (Fin n) (Fin n) (PowerSeries K),
        ArcInLocus P b₁ → ArcInLocus P b₂ →
        matC b₁ = matCoords.symm z → matC b₂ = matCoords.symm z →
        ∀ W₁ W₂ : Matrix (Fin n) (Fin n) K,
          matD b₁ = W₁ * matCoords.symm z - matCoords.symm z * W₁ →
          matD b₂ = W₂ * matCoords.symm z - matCoords.symm z * W₂ →
          kkForm (matCoords.symm z) W₁ W₂ = 0 := by
  have := hP
  rw [Height.Orbital.KKIsotropic, Height.Geometry.genericPts_iff] at hstar
  obtain ⟨g, hg, hmain⟩ := hstar
  refine ⟨g, hg, fun z hz hgz b₁ b₂ hb₁ hb₂ hc₁ hc₂ W₁ W₂ hW₁ hW₂ => ?_⟩
  have hgz' : MvPolynomial.aeval z g ≠ 0 := by rwa [MvPolynomial.aeval_eq_eval]
  have hbase : ∀ (b : Matrix (Fin n) (Fin n) (PowerSeries K)) (hb : ArcInLocus P b),
      matC b = matCoords.symm z →
      ((Height.Orbital.matArcEquiv P).symm ⟨b, hb⟩).base = z := by
    intro b hb hc
    rw [Height.Orbital.base_matArcEquiv_symm, hc, LinearEquiv.apply_symm_apply]
  have hvel : ∀ (b : Matrix (Fin n) (Fin n) (PowerSeries K)) (hb : ArcInLocus P b),
      matCoords.symm ((Height.Orbital.matArcEquiv P).symm ⟨b, hb⟩).vel = matD b := by
    intro b hb
    rw [Height.Orbital.vel_matArcEquiv_symm, LinearEquiv.symm_apply_apply]
  obtain ⟨w⟩ := hmain z hz hgz'
    ((Height.Orbital.matArcEquiv P).symm ⟨b₁, hb₁⟩)
    ((Height.Orbital.matArcEquiv P).symm ⟨b₂, hb₂⟩)
    (hbase b₁ hb₁ hc₁) (hbase b₂ hb₂ hc₂)
  have h₁ : matD b₁ = w.α₁ * matCoords.symm z - matCoords.symm z * w.α₁ := by
    rw [← hvel b₁ hb₁]; exact w.eq₁
  have h₂ : matD b₂ = w.α₂ * matCoords.symm z - matCoords.symm z * w.α₂ := by
    rw [← hvel b₂ hb₂]; exact w.eq₂
  refine Eq.trans (kk_wellDefined ?_ ?_) w.kk
  · rw [← hW₁, ← h₁]
  · rw [← hW₂, ← h₂]

/-- **`thm:reduction`**, modulo the geometry of `ψ`: on a dense open of the
component `V(I)` the shifted classes of the velocities of marked arcs are
`Ω_x`-orthogonal, granted the map `ψ` (`PsiMap`) and kernel flatness
(`Isotropy.DCond`, `lem:flag-flat`(1)) for the two arcs at hand.

`ψ` supplies, for every dense open `Z ∖ V(g)` of an irreducible `Z = V(P) ⊆ 𝔫`,
a dense open `V ∖ V(h)` such that at every point of the latter a conjugate of
the member at the moving point lies in the former and the correspondingly
conjugated fibre motions of the velocities of arcs in `V` are velocities of
arcs in `Z` there (`PsiImage`).  The conjugation is `g(Φ)` of the paper:
`ψ` conjugates the moving fibre flag onto the fixed one, and is the identity at
the base point. -/
theorem siPairing_eq_zero_of_psiMap [IsAlgClosed K] [Infinite K]
    {τ : Nat.Partition n} {d : ℕ → ℕ} {N₀ : Matrix (Fin n) (Fin n) K}
    (C : SIComponent τ d N₀) (ψ : PsiMap C.I) :
    ∃ h ∉ C.I, ∀ z ∈ MvPolynomial.zeroLocus K C.I, MvPolynomial.eval z h ≠ 0 →
      ∀ m₁ m₂ : MarkedArc C.I z,
        Isotropy.DCond (Pat (siCoords.symm z).1 (siCoords.symm z).2.1 (siCoords.symm z).2.2)
          (Qat (pencil m₁.a.vel.1 m₁.a.vel.2.1) (siCoords.symm z).2.2) →
        Isotropy.DCond (Pat (siCoords.symm z).1 (siCoords.symm z).2.1 (siCoords.symm z).2.2)
          (Qat (pencil m₂.a.vel.1 m₂.a.vel.2.1) (siCoords.symm z).2.2) →
        siPairing (siCoords.symm z) m₁.a.vel m₂.a.vel m₁.Z m₂.Z = 0 := by
  obtain ⟨I, g₀, hloc⟩ := C
  have := ψ.prime
  obtain ⟨g, hg, hstar'⟩ := star_kk_vanishing ψ.P ψ.prime
    (nilcone_kkIsotropic ψ.P
      (Height.Orbital.strictUpperIdeal_le_of_forall_isStrictlyUpper ψ.P ψ.upper))
  obtain ⟨h, hh, htrans⟩ := ψ.image g hg
  refine ⟨g₀ * h, hloc.mul_notMem hh, fun z hz hgz m₁ m₂ hQ₁ hQ₂ => ?_⟩
  rw [map_mul, mul_ne_zero_iff] at hgz
  have hsub := hloc.locus z hz hgz.1
  -- the pencil at the point is nilpotent over `K⟦u⟧`
  have hnilP : NilpotentPencil (siCoords.symm z).1 (siCoords.symm z).2.1 := hsub.1.1
  have hnil : Pat (siCoords.symm z).1 (siCoords.symm z).2.1 (siCoords.symm z).2.2 ^ n = 0 :=
    Pat_pow_eq_zero _ _ _ _ (pencil_pow_eq_zero_of_nilpotentPencil hnilP)
  -- kernel flatness at the point gives the decompositions of `lem:local-model`(3)
  have hD₁ := dcond_Rdot (siCoords.symm z).1 (siCoords.symm z).2.1 (siCoords.symm z).2.2
    (pencil m₁.a.vel.1 m₁.a.vel.2.1) m₁.a.vel.2.2 m₁.Z hQ₁
  have hD₂ := dcond_Rdot (siCoords.symm z).1 (siCoords.symm z).2.1 (siCoords.symm z).2.2
    (pencil m₂.a.vel.1 m₂.a.vel.2.1) m₂.a.vel.2.2 m₂.Z hQ₂
  obtain ⟨W₁, U₁, hdec₁, hU₁⟩ := exists_velocity_decomposition _ _ hnil hD₁
  obtain ⟨W₂, U₂, hdec₂, hU₂⟩ := exists_velocity_decomposition _ _ hnil hD₂
  -- `lem:flag-velocity`
  obtain ⟨hv₁, hv₂, -, hkk⟩ :=
    flag_velocity_of_decomposition (siCoords.symm z).1 (siCoords.symm z).2.1 (siCoords.symm z).2.2 hnil
      (pencil m₁.a.vel.1 m₁.a.vel.2.1) (pencil m₂.a.vel.1 m₂.a.vel.2.1)
      m₁.a.vel.2.2 m₂.a.vel.2.2 m₁.Z m₂.Z m₁.marked m₂.marked W₁ W₂ U₁ U₂
      hdec₁ hdec₂ hU₁ hU₂
  -- transfer to the orbital side
  obtain ⟨φ⟩ := htrans z hz hgz.2
  obtain ⟨⟨b₁, hb1, hc1, hd1⟩⟩ := φ.arcs m₁ (matC U₁) ⟨W₁, U₁, ⟨hdec₁, hU₁⟩, rfl⟩
  obtain ⟨⟨b₂, hb2, hc2, hd2⟩⟩ := φ.arcs m₂ (matC U₂) ⟨W₂, U₂, ⟨hdec₂, hU₂⟩, rfl⟩
  have hU₁val : matC U₁ = matC W₁ * siMember (siCoords.symm z) - siMember (siCoords.symm z) * matC W₁ := by
    rw [show matC U₁ = -(siMember (siCoords.symm z) * matC W₁ - matC W₁ * siMember (siCoords.symm z)) from
      eq_neg_of_add_eq_zero_right hv₁, neg_sub]
  have hU₂val : matC U₂ = matC W₂ * siMember (siCoords.symm z) - siMember (siCoords.symm z) * matC W₂ := by
    rw [show matC U₂ = -(siMember (siCoords.symm z) * matC W₂ - matC W₂ * siMember (siCoords.symm z)) from
      eq_neg_of_add_eq_zero_right hv₂, neg_sub]
  -- the velocities of the arcs in `Z` are the conjugated fibre motions
  set cj := Height.Toolbox.matrixConjugationLinearEquiv K n φ.c with hcj
  have hvel : ∀ W Y : Matrix (Fin n) (Fin n) K,
      Y = W * siMember (siCoords.symm z) - siMember (siCoords.symm z) * W →
      cj Y = cj W * matCoords.symm φ.w - matCoords.symm φ.w * cj W := by
    intro W Y hY
    rw [hY, φ.conj, map_sub, hcj, matConj_mul, matConj_mul]
  have hzero := hstar' φ.w φ.mem φ.g_ne b₁ b₂ hb1 hb2 hc1 hc2 (cj (matC W₁)) (cj (matC W₂))
    (by rw [hd1, hvel (matC W₁) (matC U₁) hU₁val])
    (by rw [hd2, hvel (matC W₂) (matC U₂) hU₂val])
  show siPairing (siCoords.symm z) m₁.a.vel m₂.a.vel m₁.Z m₂.Z = 0
  rw [siPairing, hkk]
  show kkForm (siMember (siCoords.symm z)) (matC W₁) (matC W₂) = 0
  rw [φ.conj] at hzero
  rw [← kkForm_matrixConjugation φ.c (siMember (siCoords.symm z)) (matC W₁) (matC W₂)]
  exact hzero

end Node

end Height.Chain
