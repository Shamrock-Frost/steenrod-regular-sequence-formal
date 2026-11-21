import Height.Chain.Psi
import Height.Chain.Multidegree
import Height.Pencil.LocalModel
import Height.Toolbox.DualMatrix
import Height.Toolbox.FlagFrame
import Height.Toolbox.JordanBasis
import Mathlib.RingTheory.Localization.Integer

/-!
# The adapted frame in affine coordinates

`Chain/Psi.lean` reduces the node `shiftedIsotropy` to an
`AdaptedFrame`: a tuple `Ψ` of polynomials and, at each point `z` of a dense
open of `V(I) ⊆ 𝒴_λ`, an invertible frame `c(z)` with

* `Ψ(z) = c(z)⁻¹ (N + tM)(z) c(z)` in the nilradical of a fixed coordinate
  flag, and
* `c(z)⁻¹ Y c(z) = ∂_s(Ψ ∘ a) + [Ψ(z), D]`, `D` in the parabolic, for every
  fibre motion `Y` of the velocity of an arc `a` of `V(I)`.

This file cuts the adapted frame down to its geometric core.  Everything that is
*affine algebra* — that a frame given by polynomials in `z` produces a
polynomial `Ψ`, and that the arc clause is the marking equation plus the
Leibniz rule — is proved here; what is left is the `GeometricFrame`, one statement
about a single matrix of polynomials per irreducible `V(I)`.

## No denominators are needed

One might expect the statement to need denominators: `c(z)⁻¹ =
adj(c)/h₀`, so `c(z)⁻¹ (N + tM)(z) c(z)` has entries in `K[V][1/h₀]` and need
not be the value of a polynomial.  It does not, because the frame may be
rescaled:  if `c` carries the coordinate flag of `lvl` onto the fibre flag then
so does `c · diag(h₀^{lvl i})` — a diagonal matrix lies in the parabolic — and
conjugating by the diagonal factor multiplies the `(i,j)` entry by
`h₀^{lvl j − lvl i}`.  The conjugated member is *strictly* block upper for
`lvl`, so every entry that survives has `lvl i < lvl j` and picks up at least
one factor `h₀`, which cancels the denominator.  This is
`GeometricFrame.toAlgebraic` below, and it is why the adapted frame is
proved here exactly as `Chain/Psi.lean` states it.

## What is proved

```
GeometricFrame.toAlgebraic : AlgebraicFrame I    (from a GeometricFrame I)
AlgebraicFrame.toAdapted   : AdaptedFrame I      (from an AlgebraicFrame I)
```

`GeometricFrame` is `lem:local-model`(1),(3) made algebraic in the point: for
every `SILocus τ d N₀ I g` there are a monotone level function `lvl`, a matrix
`C` of polynomials with `det C ∉ I` and an auxiliary `h ∉ I` such that

1. `C⁻¹ (N + tM) C` is strictly block upper for `lvl` on `V(I)` — in the
   denominator-free form `(adj C · (N + tM) · C) i j ∈ I` for `lvl j ≤ lvl i`.
   This is `lem:local-model`(1): the frame carries the coordinate flag of `lvl`
   onto the fibre flag of the pencil at the marked point, which the member
   lowers; and
2. for every arc `a` of `V(I)` through a point `z` of the dense open
   `V ∖ V(det C · h)`, every marking witness `Zw` and every decomposition
   `Ṙ = [P, W] + U` of `lem:local-model`(3), the matrix
   `C(z)⁻¹ (W(x) + Zw) C(z) + C(z)⁻¹ ∂_s C(a)` lies in the parabolic of `lvl`.

Clause 2 is the normalisation `ĥ(s, x_s) = c(a(s))` of `thm:reduction`: it says
that the velocity of the frame is, modulo the parabolic, the transporter that
turns the shifted representative into the fibre motion.  Given it, the fibre
motion `Y = [W(x), N]` conjugates to `∂_s(Ψ ∘ a)` up to `[Ψ(z), D]`, which is
the arc clause of `AdaptedFrame`.

**Clause 1** is `exists_fibreFrame` and
`FibreFrame.strict`.  There are two flags that the member lowers at a marked
point — its own kernel flag `ker (N + tM)^•`, and the *fibre* flag
`V_k = S_k(x)`, the reduction modulo `u` of the pencil's kernel flag over
`K⟦u⟧` — and they differ, because the type drops at a marked point.  `strict`
holds for either, but only the fibre flag makes clause 2 true, so the frame is
built from the fibre flag:

* the generic pencil is nilpotent modulo `I` (`siGenPencil_pow_map_eq_zero`:
  every coefficient of `(μN + νM)^n` vanishes on the dense open, and `I` is
  prime), so over the function field `F = Frac(K[V]/I)` its fibre flag
  `siFibFlag` runs from `⊥` to `⊤` and is lowered by the member;
* a basis adapted to it (`Toolbox.exists_flagFrame`) gives the frame and its
  jump pattern `lvl`, and clearing the denominators
  (`IsLocalization.exist_integer_multiples`) brings the frame back to `K[V]`
  with `det ∉ I` — rescaling by a nonzero element of `F` changes neither the
  flag the frame carries nor the nonvanishing of its determinant;
* `strict` is then `Toolbox.blockStrict_of_adapted`: the `j`-th column of the
  frame lies in `V (lvl j)`, so the member carries it into `V (lvl j − 1)`.

**Clause 2** is `exists_frameNorm`.  It does *not*
need the two-parameter trivialisation `ĥ(s, u)` of `lem:local-model`(3):
everything is first order in the arc parameter, and the motion of the kernel
flag is computed by `Isotropy.dpow`.  `Isotropy.dpow_vanishing_of_lowering` says
a lowering perturbation does not move the flag to first order, so only the
commutator part of `Ṗ = [P, W + Zw] + U` moves it, and the frame velocity is
forced.  The two inputs are `Pencil.fibFlag_Pat_eq_map_polyKerFlag` (the lift of
a fibre-flag vector may be taken polynomial in `u`, so its denominators clear
into a single `h ∉ I` and it specialises to `K[ε]` at the point `z + ε ż`) and
`exists_finrank_fibFlag_open` (the fibre flag at `z` has the dimension it has at
the generic point).  Read `exists_frameNorm`'s docstring for the derivation.
-/

namespace Height.Chain

open Matrix Height.Orbital Height.Steenrod Height.Pencil
open Height.Geometry (SIIndex SIPoint siCoords PairIndex pairCoords fstMat sndMat matCoords
  MarkedIndex markedCoords)

universe u

/-! ### Matrices of polynomials in the coordinates of the incidence -/

section Generic

variable {K : Type u} [Field K] {n : ℕ}

/-- The entries of a matrix of polynomials, as a tuple: `polyMat` and
`polyMatArc` of `Chain/Psi.lean` read tuples. -/
def matTup (C : Matrix (Fin n) (Fin n) (MvPolynomial (SIIndex (Fin n)) K)) :
    Fin n × Fin n → MvPolynomial (SIIndex (Fin n)) K := fun ij => C ij.1 ij.2

/-- The member of the pencil at the marked point, as a matrix of polynomials in
the coordinates of the single-point incidence: `N + t M`. -/
noncomputable def siGenMember : Matrix (Fin n) (Fin n) (MvPolynomial (SIIndex (Fin n)) K) :=
  Matrix.of fun i j => MvPolynomial.X (Sum.inl (Sum.inl (i, j)))
    + MvPolynomial.X (Sum.inr ()) * MvPolynomial.X (Sum.inl (Sum.inr (i, j)))

/-- Evaluation along an arc, as a ring map. -/
noncomputable def siArcHom (a : SIArc n K) : MvPolynomial (SIIndex (Fin n)) K →+* PowerSeries K :=
  (MvPolynomial.aeval a.coords : MvPolynomial (SIIndex (Fin n)) K →ₐ[K] PowerSeries K).toRingHom

theorem siArcHom_apply (a : SIArc n K) (f : MvPolynomial (SIIndex (Fin n)) K) :
    siArcHom a f = MvPolynomial.aeval a.coords f := rfl

/-- The frame at a point of the incidence. -/
noncomputable def frameAt (C : Matrix (Fin n) (Fin n) (MvPolynomial (SIIndex (Fin n)) K))
    (z : SIIndex (Fin n) → K) : Matrix (Fin n) (Fin n) K :=
  C.map (MvPolynomial.eval z)

/-- The frame along an arc of the incidence. -/
noncomputable def frameArc (C : Matrix (Fin n) (Fin n) (MvPolynomial (SIIndex (Fin n)) K))
    (a : SIArc n K) : Matrix (Fin n) (Fin n) (PowerSeries K) :=
  C.map (siArcHom a)

theorem polyMat_matTup (C : Matrix (Fin n) (Fin n) (MvPolynomial (SIIndex (Fin n)) K))
    (z : SIIndex (Fin n) → K) : polyMat (matTup C) z = frameAt C z := rfl

theorem polyMatArc_matTup (C : Matrix (Fin n) (Fin n) (MvPolynomial (SIIndex (Fin n)) K))
    (a : SIArc n K) : polyMatArc (matTup C) a = frameArc C a := rfl

theorem det_frameAt (C : Matrix (Fin n) (Fin n) (MvPolynomial (SIIndex (Fin n)) K))
    (z : SIIndex (Fin n) → K) : (frameAt C z).det = MvPolynomial.eval z C.det :=
  det_map (MvPolynomial.eval z) C

theorem isUnit_det_frameAt {C : Matrix (Fin n) (Fin n) (MvPolynomial (SIIndex (Fin n)) K)}
    {z : SIIndex (Fin n) → K} (h : MvPolynomial.eval z C.det ≠ 0) : IsUnit (frameAt C z).det := by
  rw [det_frameAt]
  exact isUnit_iff_ne_zero.mpr h

theorem isUnit_det_frameArc {C : Matrix (Fin n) (Fin n) (MvPolynomial (SIIndex (Fin n)) K)}
    {a : SIArc n K} {z : SIIndex (Fin n) → K} (hb : a.base = siCoords.symm z)
    (h : MvPolynomial.eval z C.det ≠ 0) : IsUnit (frameArc C a).det := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  have hC : PowerSeries.constantCoeff (frameArc C a).det = (frameAt C z).det := by
    rw [← det_map (PowerSeries.constantCoeff (R := K)) (frameArc C a)]
    congr 1
    rw [show (frameArc C a).map (PowerSeries.constantCoeff (R := K))
        = matC (frameArc C a) from rfl, ← polyMatArc_matTup, matC_polyMatArc (matTup C) hb,
      polyMat_matTup]
  rw [hC, det_frameAt]
  exact isUnit_iff_ne_zero.mpr h

/-- The frame at the base point of an arc is the value of the frame along the
arc. -/
theorem matC_frameArc (C : Matrix (Fin n) (Fin n) (MvPolynomial (SIIndex (Fin n)) K))
    {a : SIArc n K} {z : SIIndex (Fin n) → K} (hb : a.base = siCoords.symm z) :
    matC (frameArc C a) = frameAt C z := by
  rw [← polyMatArc_matTup, matC_polyMatArc (matTup C) hb, polyMat_matTup]

/-- The generic member evaluated at a point is the member at the marked
point. -/
theorem frameAt_siGenMember (z : SIIndex (Fin n) → K) :
    frameAt (siGenMember (K := K) (n := n)) z = siMember (siCoords.symm z) := by
  ext i j
  show MvPolynomial.eval z
      (MvPolynomial.X (Sum.inl (Sum.inl (i, j)))
        + MvPolynomial.X (Sum.inr ()) * MvPolynomial.X (Sum.inl (Sum.inr (i, j)))) = _
  rw [map_add, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_X, MvPolynomial.eval_X]
  rfl

/-- The generic member along an arc is the member of the arc at its moving
marked point. -/
theorem frameArc_siGenMember (a : SIArc n K) :
    frameArc (siGenMember (K := K) (n := n)) a = a.N + a.t • a.M := by
  refine Matrix.ext fun i j => ?_
  have h1 : frameArc (siGenMember (K := K) (n := n)) a i j
      = siArcHom a (siGenMember i j) := rfl
  have h2 : (a.N + a.t • a.M) i j = a.N i j + a.t * a.M i j := rfl
  have h3 : (siGenMember (K := K) (n := n)) i j
      = MvPolynomial.X (Sum.inl (Sum.inl (i, j)))
        + MvPolynomial.X (Sum.inr ()) * MvPolynomial.X (Sum.inl (Sum.inr (i, j))) := rfl
  rw [h1, h2, h3, map_add, map_mul, siArcHom_apply, siArcHom_apply, siArcHom_apply,
    MvPolynomial.aeval_X, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
  rfl

/-- The first matrix of the generic pencil of the single-point incidence. -/
noncomputable def siGenN : Matrix (Fin n) (Fin n) (MvPolynomial (SIIndex (Fin n)) K) :=
  Matrix.of fun i j => MvPolynomial.X (Sum.inl (Sum.inl (i, j)))

/-- The second matrix of the generic pencil of the single-point incidence. -/
noncomputable def siGenM : Matrix (Fin n) (Fin n) (MvPolynomial (SIIndex (Fin n)) K) :=
  Matrix.of fun i j => MvPolynomial.X (Sum.inl (Sum.inr (i, j)))

/-- The generic marked parameter. -/
noncomputable def siGenT : MvPolynomial (SIIndex (Fin n)) K := MvPolynomial.X (Sum.inr ())

theorem map_siGenN (z : SIIndex (Fin n) → K) :
    (siGenN (K := K) (n := n)).map (MvPolynomial.eval z) = (siCoords.symm z).1 := by
  refine Matrix.ext fun i j => ?_
  show MvPolynomial.eval z (MvPolynomial.X (Sum.inl (Sum.inl (i, j)))) = _
  rw [MvPolynomial.eval_X]
  rfl

theorem map_siGenM (z : SIIndex (Fin n) → K) :
    (siGenM (K := K) (n := n)).map (MvPolynomial.eval z) = (siCoords.symm z).2.1 := by
  refine Matrix.ext fun i j => ?_
  show MvPolynomial.eval z (MvPolynomial.X (Sum.inl (Sum.inr (i, j)))) = _
  rw [MvPolynomial.eval_X]
  rfl

theorem eval_siGenT (z : SIIndex (Fin n) → K) :
    MvPolynomial.eval z (siGenT (K := K) (n := n)) = (siCoords.symm z).2.2 := by
  show MvPolynomial.eval z (MvPolynomial.X (Sum.inr ())) = _
  rw [MvPolynomial.eval_X]
  rfl

/-- The generic member is the member of the generic pencil at the generic
marked parameter. -/
theorem siGenMember_map {S : Type u} [CommRing S]
    (φ : MvPolynomial (SIIndex (Fin n)) K →+* S) :
    (siGenMember (K := K) (n := n)).map φ
      = (siGenN.map φ) + (φ siGenT) • (siGenM.map φ) := by
  refine Matrix.ext fun i j => ?_
  show φ (MvPolynomial.X (Sum.inl (Sum.inl (i, j)))
      + MvPolynomial.X (Sum.inr ()) * MvPolynomial.X (Sum.inl (Sum.inr (i, j))))
    = φ (MvPolynomial.X (Sum.inl (Sum.inl (i, j))))
      + φ (MvPolynomial.X (Sum.inr ())) * φ (MvPolynomial.X (Sum.inl (Sum.inr (i, j))))
  rw [map_add, map_mul]

/-- The pencil commutes with a coefficient map. -/
theorem map_pencil_map {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    (N M : Matrix (Fin n) (Fin n) A) :
    (pencil N M).map (MvPolynomial.map φ) = pencil (N.map φ) (M.map φ) := by
  refine Matrix.ext fun i j => ?_
  show MvPolynomial.map φ (MvPolynomial.C (N i j) * Height.Graded.mu
      + MvPolynomial.C (M i j) * Height.Graded.nu)
    = MvPolynomial.C (φ (N i j)) * Height.Graded.mu
      + MvPolynomial.C (φ (M i j)) * Height.Graded.nu
  rw [map_add, map_mul, map_mul, MvPolynomial.map_C, MvPolynomial.map_C]
  congr 1 <;> congr 1 <;>
    simp [Height.Graded.mu, Height.Graded.nu]

end Generic

/-! ### The frame as a unit, and conjugation modulo `I` -/

section Frame

variable {K : Type u} [Field K] {n : ℕ}

open Classical in
/-- The frame at a point, as a unit of the matrix ring; the junk value `1`
where the frame degenerates. -/
noncomputable def frameUnit (C : Matrix (Fin n) (Fin n) (MvPolynomial (SIIndex (Fin n)) K))
    (z : SIIndex (Fin n) → K) : (Matrix (Fin n) (Fin n) K)ˣ :=
  if h : IsUnit (frameAt C z) then h.unit else 1

theorem frameUnit_val {C : Matrix (Fin n) (Fin n) (MvPolynomial (SIIndex (Fin n)) K)}
    {z : SIIndex (Fin n) → K} (h : IsUnit (frameAt C z)) :
    (frameUnit C z : Matrix (Fin n) (Fin n) K) = frameAt C z := by
  classical
  rw [frameUnit]
  split
  · exact IsUnit.unit_spec _
  · exact absurd h (by assumption)

theorem frameUnit_inv_val {C : Matrix (Fin n) (Fin n) (MvPolynomial (SIIndex (Fin n)) K)}
    {z : SIIndex (Fin n) → K} (h : IsUnit (frameAt C z)) :
    (((frameUnit C z)⁻¹ : (Matrix (Fin n) (Fin n) K)ˣ) : Matrix (Fin n) (Fin n) K)
      = (frameAt C z)⁻¹ := by
  rw [Matrix.coe_units_inv, frameUnit_val h]

/-- Reduction at the base point of an arc is the matrix ring map of
`PowerSeries.constantCoeff`. -/
theorem matC_eq_mapMatrix (A : Matrix (Fin n) (Fin n) (PowerSeries K)) :
    matC A = (PowerSeries.constantCoeff (R := K)).mapMatrix A := rfl

/-- Reduction of a commutator plus a remainder. -/
theorem matC_commutator_add (P W U : Matrix (Fin n) (Fin n) (PowerSeries K)) :
    matC ((P * W - W * P) + U) = (matC P * matC W - matC W * matC P) + matC U := by
  rw [matC_eq_mapMatrix, map_add, map_sub, map_mul, map_mul]
  rfl

/-- Conjugation by a matrix with a right inverse is multiplicative. -/
theorem conj_mul_conj_eq {c A B : Matrix (Fin n) (Fin n) K} (h : c * c⁻¹ = 1) :
    (c⁻¹ * A * c) * (c⁻¹ * B * c) = c⁻¹ * (A * B) * c := by
  calc (c⁻¹ * A * c) * (c⁻¹ * B * c) = c⁻¹ * A * (c * c⁻¹) * B * c := by noncomm_ring
    _ = c⁻¹ * (A * B) * c := by rw [h]; noncomm_ring

/-- `Ψ` is the conjugate `C⁻¹ (N + tM) C` of the member at the marked point,
modulo `I`: the identity `(N + tM) C = C Ψ` in the coordinate ring. -/
def IsFrameConj (I : Ideal (MvPolynomial (SIIndex (Fin n)) K))
    (C Ψ : Matrix (Fin n) (Fin n) (MvPolynomial (SIIndex (Fin n)) K)) : Prop :=
  ∀ i j, ((siGenMember (K := K) (n := n)) * C - C * Ψ) i j ∈ I

/-- Two matrices of polynomials conjugate modulo `I` are conjugate under every
ring map that kills `I`. -/
theorem map_conj_of_mem_ideal {S : Type*} [CommRing S]
    {I : Ideal (MvPolynomial (SIIndex (Fin n)) K)}
    {C Ψ : Matrix (Fin n) (Fin n) (MvPolynomial (SIIndex (Fin n)) K)}
    (φ : MvPolynomial (SIIndex (Fin n)) K →+* S) (hφ : ∀ f ∈ I, φ f = 0)
    (h : IsFrameConj I C Ψ) :
    (siGenMember (K := K) (n := n)).map φ * C.map φ = C.map φ * Ψ.map φ := by
  rw [← Matrix.map_mul, ← Matrix.map_mul]
  refine Matrix.ext fun i j => ?_
  have h1 : φ (((siGenMember (K := K) (n := n)) * C - C * Ψ) i j) = 0 := hφ _ (h i j)
  rw [Matrix.sub_apply, map_sub, sub_eq_zero] at h1
  exact h1

/-- The conjugation identity at a point of `V(I)` off the frame's
discriminant. -/
theorem frame_conj_at {I : Ideal (MvPolynomial (SIIndex (Fin n)) K)}
    {C Ψ : Matrix (Fin n) (Fin n) (MvPolynomial (SIIndex (Fin n)) K)}
    (hcj : IsFrameConj I C Ψ)
    {z : SIIndex (Fin n) → K} (hz : z ∈ MvPolynomial.zeroLocus K I)
    (hne : MvPolynomial.eval z C.det ≠ 0) :
    polyMat (matTup Ψ) z = (frameAt C z)⁻¹ * siMember (siCoords.symm z) * frameAt C z := by
  have hev : ∀ f ∈ I, MvPolynomial.eval z f = 0 := by
    intro f hf
    have := hz f hf
    rwa [MvPolynomial.aeval_eq_eval] at this
  have h : siMember (siCoords.symm z) * frameAt C z = frameAt C z * polyMat (matTup Ψ) z := by
    rw [← frameAt_siGenMember z]
    exact map_conj_of_mem_ideal (MvPolynomial.eval z) hev hcj
  have hu : IsUnit (frameAt C z).det := isUnit_det_frameAt hne
  calc polyMat (matTup Ψ) z
      = ((frameAt C z)⁻¹ * frameAt C z) * polyMat (matTup Ψ) z := by
        rw [Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
    _ = (frameAt C z)⁻¹ * (frameAt C z * polyMat (matTup Ψ) z) := by rw [Matrix.mul_assoc]
    _ = (frameAt C z)⁻¹ * (siMember (siCoords.symm z) * frameAt C z) := by rw [h]
    _ = (frameAt C z)⁻¹ * siMember (siCoords.symm z) * frameAt C z := by rw [Matrix.mul_assoc]

/-- The conjugation identity along an arc of `V(I)`. -/
theorem frame_conj_arc {I : Ideal (MvPolynomial (SIIndex (Fin n)) K)}
    {C Ψ : Matrix (Fin n) (Fin n) (MvPolynomial (SIIndex (Fin n)) K)}
    (hcj : IsFrameConj I C Ψ)
    {a : SIArc n K} (ha : a.InLocus I) {z : SIIndex (Fin n) → K} (hb : a.base = siCoords.symm z)
    (hne : MvPolynomial.eval z C.det ≠ 0) :
    polyMatArc (matTup Ψ) a
      = (frameArc C a)⁻¹ * frameArc siGenMember a * frameArc C a := by
  have hev : ∀ f ∈ I, siArcHom a f = 0 := fun f hf => ha f hf
  have h : frameArc siGenMember a * frameArc C a
      = frameArc C a * polyMatArc (matTup Ψ) a := map_conj_of_mem_ideal (siArcHom a) hev hcj
  have hu : IsUnit (frameArc C a).det := isUnit_det_frameArc hb hne
  calc polyMatArc (matTup Ψ) a
      = ((frameArc C a)⁻¹ * frameArc C a) * polyMatArc (matTup Ψ) a := by
        rw [Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
    _ = (frameArc C a)⁻¹ * (frameArc C a * polyMatArc (matTup Ψ) a) := by rw [Matrix.mul_assoc]
    _ = (frameArc C a)⁻¹ * (frameArc siGenMember a * frameArc C a) := by rw [h]
    _ = (frameArc C a)⁻¹ * frameArc siGenMember a * frameArc C a := by rw [Matrix.mul_assoc]

end Frame

/-! ### The frame and its normalisation -/

section Norm

variable {K : Type u} [Field K] {n : ℕ}

/-- **The normalisation of `lem:local-model`(3)** for the frame `C`: at every
point `z` of the dense open `D(det C) ∩ V(I)`, along every arc `a` of `V(I)`
through `z`, the velocity `∂_s C(a)` of the frame is — modulo the parabolic of
the coordinate flag of `lvl` — the transporter that turns the shifted
representative into the fibre motion.

This is the paper's normalisation `ĥ(s, x_s) = g(Φ(P_s, x_s))` of the
two-parameter trivialisation: with it, `W(x) + Zw + ∂_s C(a) · C(z)⁻¹` lies in
the parabolic of the *fibre* flag, i.e. its conjugate

```
C(z)⁻¹ (W(x) + Zw) C(z) + C(z)⁻¹ ∂_s C(a)
```

lies in the parabolic of the coordinate flag of `lvl`; that is what makes
`∂_s(Ψ ∘ a)` the conjugated fibre motion up to a commutator with the parabolic.
The displayed form — rather than `C(z)⁻¹ (W + Zw + ∂_s C(a) C(z)⁻¹) C(z)`, to
which it is equal — is the one that transforms cleanly under a rescaling of the
frame (`frameNorm_rescale`).

The normalisation is only asked for on the dense open `V ∖ V(det C · h)`: the
auxiliary `h` is where a construction of the frame is allowed to break down,
and it reappears in the dense open of `AdaptedFrame`. -/
def FrameNorm (lvl : Fin n → ℕ)
    (C : Matrix (Fin n) (Fin n) (MvPolynomial (SIIndex (Fin n)) K))
    (h : MvPolynomial (SIIndex (Fin n)) K)
    (I : Ideal (MvPolynomial (SIIndex (Fin n)) K)) : Prop :=
  ∀ z ∈ MvPolynomial.zeroLocus K I, MvPolynomial.eval z C.det ≠ 0 →
    MvPolynomial.eval z h ≠ 0 →
    ∀ (m : MarkedArc I z) (W U : Matrix (Fin n) (Fin n) (PowerSeries K)),
      IsVelocityDecomp (siCoords.symm z) m.a.vel m.Z W U →
      IsBlockUpper lvl ((frameAt C z)⁻¹ * (matC W + m.Z) * frameAt C z
        + (frameAt C z)⁻¹ * matD (frameArc C m.a))

/-- **An adapted frame on `V(I)`, algebraic form**: a monotone level function
`lvl`, a polynomial frame `C` invertible on the dense open `D(det C)`, a
polynomial conjugate `Ψ` of the member `N + tM` (`IsFrameConj`) lying in the
nilradical of the coordinate flag of `lvl` modulo `I`, and an auxiliary `h ∉ I`
off which the frame is normalised along arcs (`FrameNorm`). -/
structure AlgebraicFrame (I : Ideal (MvPolynomial (SIIndex (Fin n)) K)) where
  /-- the level function of the coordinate flag -/
  lvl : Fin n → ℕ
  /-- the frame -/
  C : Matrix (Fin n) (Fin n) (MvPolynomial (SIIndex (Fin n)) K)
  /-- the conjugate `C⁻¹ (N + tM) C` -/
  Ψ : Matrix (Fin n) (Fin n) (MvPolynomial (SIIndex (Fin n)) K)
  /-- the auxiliary hypersurface off which the frame is normalised -/
  h : MvPolynomial (SIIndex (Fin n)) K
  mono : Monotone lvl
  det_notMem : C.det ∉ I
  h_notMem : h ∉ I
  /-- `Ψ` is block strictly upper for `lvl` on `V(I)` -/
  strict : ∀ i j : Fin n, lvl j ≤ lvl i → Ψ i j ∈ I
  conj : IsFrameConj I C Ψ
  norm : FrameNorm lvl C h I

/-- **An adapted frame on `V(I)`, geometric form**: as `AlgebraicFrame`, but the
conjugate is the rational `C⁻¹ (N + tM) C`, recorded through the adjugate
`adj(C) (N + tM) C = det(C) · C⁻¹ (N + tM) C`; `GeometricFrame.toAlgebraic`
clears the denominator. -/
structure GeometricFrame (I : Ideal (MvPolynomial (SIIndex (Fin n)) K)) where
  /-- the level function of the coordinate flag -/
  lvl : Fin n → ℕ
  /-- the frame -/
  C : Matrix (Fin n) (Fin n) (MvPolynomial (SIIndex (Fin n)) K)
  /-- the auxiliary hypersurface off which the frame is normalised -/
  h : MvPolynomial (SIIndex (Fin n)) K
  mono : Monotone lvl
  det_notMem : C.det ∉ I
  h_notMem : h ∉ I
  /-- `adj(C) (N + tM) C` is block strictly upper for `lvl` on `V(I)` -/
  strict : ∀ i j : Fin n, lvl j ≤ lvl i →
    (C.adjugate * siGenMember (K := K) (n := n) * C) i j ∈ I
  norm : FrameNorm lvl C h I

end Norm

/-! ### Rescaling the frame

`lem:local-model`(1) gives a frame `C` whose conjugate `C⁻¹ (N + tM) C` is
block strict on `V(I)`; its entries are *rational*, with denominator `det C`.
`AdaptedFrame` asks for a matrix of *polynomials*.  Rescaling the columns of the
frame by the powers `det(C)^{lvl j}` — a diagonal, hence parabolic, change of
frame that does not move the flag — multiplies the `(i,j)` entry of the
conjugate by `det(C)^{lvl j - lvl i}`, so on the entries that survive (those
with `lvl i < lvl j`) it clears the single denominator, and the entries that do
not survive vanish on `V(I)` anyway.
-/

section Rescale

variable {K : Type u} [Field K] {n : ℕ}

theorem isBlockUpper_diagonal {R : Type*} [Zero R] {lvl : Fin n → ℕ} (d : Fin n → R) :
    IsBlockUpper lvl (Matrix.diagonal d) := by
  intro i j hij
  refine Matrix.diagonal_apply_ne d fun e => absurd hij ?_
  rw [e]
  exact lt_irrefl _

/-- The diagonal rescaling `diag(h ^ lvl i)` attached to a level function. -/
noncomputable def levelDiag {R : Type*} [CommRing R] (h : R) (lvl : Fin n → ℕ) :
    Matrix (Fin n) (Fin n) R :=
  Matrix.diagonal fun i => h ^ lvl i

theorem det_levelDiag {R : Type*} [CommRing R] (h : R) (lvl : Fin n → ℕ) :
    (levelDiag h lvl).det = h ^ ∑ i, lvl i := by
  rw [levelDiag, Matrix.det_diagonal, Finset.prod_pow_eq_pow_sum]

theorem frameAt_mul (C C' : Matrix (Fin n) (Fin n) (MvPolynomial (SIIndex (Fin n)) K))
    (z : SIIndex (Fin n) → K) : frameAt (C * C') z = frameAt C z * frameAt C' z :=
  Matrix.map_mul

theorem frameArc_mul (C C' : Matrix (Fin n) (Fin n) (MvPolynomial (SIIndex (Fin n)) K))
    (a : SIArc n K) : frameArc (C * C') a = frameArc C a * frameArc C' a :=
  Matrix.map_mul

theorem frameAt_levelDiag (h : MvPolynomial (SIIndex (Fin n)) K) (lvl : Fin n → ℕ)
    (z : SIIndex (Fin n) → K) :
    frameAt (levelDiag h lvl) z = levelDiag (MvPolynomial.eval z h) lvl := by
  refine Matrix.ext fun i j => ?_
  show MvPolynomial.eval z (levelDiag h lvl i j) = levelDiag (MvPolynomial.eval z h) lvl i j
  by_cases hij : i = j
  · subst hij
    rw [levelDiag, levelDiag, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, map_pow]
  · rw [levelDiag, levelDiag, Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ hij,
      map_zero]

/-- The velocity of a diagonal rescaling is diagonal, hence parabolic. -/
theorem isBlockUpper_matD_frameArc_levelDiag {lvl lvl' : Fin n → ℕ}
    (h : MvPolynomial (SIIndex (Fin n)) K) (a : SIArc n K) :
    IsBlockUpper lvl (matD (frameArc (levelDiag h lvl') a)) :=
  IsBlockUpper.map (PowerSeries.coeff (R := K) 1)
    (IsBlockUpper.map (siArcHom a) (isBlockUpper_diagonal _))

/-- **The rescaled frame** `C · diag(det(C) ^ lvl i)`. -/
noncomputable def rescaleFrame (C : Matrix (Fin n) (Fin n) (MvPolynomial (SIIndex (Fin n)) K))
    (lvl : Fin n → ℕ) : Matrix (Fin n) (Fin n) (MvPolynomial (SIIndex (Fin n)) K) :=
  C * levelDiag C.det lvl

/-- **The conjugate by the rescaled frame**, as a matrix of polynomials: the
`(i,j)` entry of `C⁻¹ (N + tM) C` is `(adj C · (N + tM) · C) i j / det C`, and
the rescaling multiplies it by `det(C) ^ (lvl j - lvl i)`; on the entries with
`lvl i < lvl j` that is a polynomial, and the other entries are set to `0`
(they vanish on `V(I)`). -/
noncomputable def rescaleConj (C : Matrix (Fin n) (Fin n) (MvPolynomial (SIIndex (Fin n)) K))
    (lvl : Fin n → ℕ) : Matrix (Fin n) (Fin n) (MvPolynomial (SIIndex (Fin n)) K) :=
  Matrix.of fun i j =>
    if lvl i < lvl j then
      C.det ^ (lvl j - lvl i - 1) * (C.adjugate * siGenMember (K := K) (n := n) * C) i j
    else 0

theorem rescaleConj_apply_of_le {C : Matrix (Fin n) (Fin n) (MvPolynomial (SIIndex (Fin n)) K)}
    {lvl : Fin n → ℕ} {i j : Fin n} (hij : lvl j ≤ lvl i) : rescaleConj C lvl i j = 0 :=
  ite_eq_right (not_lt.mpr hij)

theorem det_rescaleFrame (C : Matrix (Fin n) (Fin n) (MvPolynomial (SIIndex (Fin n)) K))
    (lvl : Fin n → ℕ) : (rescaleFrame C lvl).det = C.det ^ (1 + ∑ i, lvl i) := by
  rw [rescaleFrame, Matrix.det_mul, det_levelDiag, pow_add, pow_one]

theorem det_rescaleFrame_notMem {I : Ideal (MvPolynomial (SIIndex (Fin n)) K)} (hI : I.IsPrime)
    {C : Matrix (Fin n) (Fin n) (MvPolynomial (SIIndex (Fin n)) K)} (lvl : Fin n → ℕ)
    (h : C.det ∉ I) : (rescaleFrame C lvl).det ∉ I := by
  rw [det_rescaleFrame]
  exact fun hmem => h ((hI.pow_mem_iff_mem _ (by omega)).mp hmem)

/-- **The rescaled frame conjugates the member into a polynomial matrix.**
The rational identity `C⁻¹ (N + tM) C = adj(C)(N + tM)C / det C` is cleared of
its denominator by the rescaling, entry by entry, using only that the entries
of `adj(C)(N + tM)C` below the flag lie in `I`. -/
theorem isFrameConj_rescale {I : Ideal (MvPolynomial (SIIndex (Fin n)) K)} (hI : I.IsPrime)
    {C : Matrix (Fin n) (Fin n) (MvPolynomial (SIIndex (Fin n)) K)} {lvl : Fin n → ℕ}
    (hdet : C.det ∉ I)
    (hstr : ∀ i j : Fin n, lvl j ≤ lvl i →
      (C.adjugate * siGenMember (K := K) (n := n) * C) i j ∈ I) :
    IsFrameConj I (rescaleFrame C lvl) (rescaleConj C lvl) := by
  classical
  -- `C · adj(C) (N + tM) C = det C · (N + tM) C`
  have hCA : C * (C.adjugate * siGenMember (K := K) (n := n) * C)
      = C.det • (siGenMember (K := K) (n := n) * C) := by
    have hrw : C * (C.adjugate * siGenMember (K := K) (n := n) * C)
        = C * C.adjugate * siGenMember (K := K) (n := n) * C := by noncomm_ring
    rw [hrw, Matrix.mul_adjugate, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul]
  -- the entrywise congruence `A · diag = diag · (det C · Ψ)` modulo `I`
  have hk : ∀ i j : Fin n,
      ((C.adjugate * siGenMember (K := K) (n := n) * C) * levelDiag C.det lvl
        - levelDiag C.det lvl * (C.det • rescaleConj C lvl)) i j ∈ I := by
    intro i j
    have hL : ((C.adjugate * siGenMember (K := K) (n := n) * C) * levelDiag C.det lvl) i j
        = (C.adjugate * siGenMember (K := K) (n := n) * C) i j * C.det ^ lvl j := by
      rw [levelDiag, Matrix.mul_diagonal]
    have hR : (levelDiag C.det lvl * (C.det • rescaleConj C lvl)) i j
        = C.det ^ lvl i * (C.det * rescaleConj C lvl i j) := by
      rw [levelDiag, Matrix.diagonal_mul]
      rfl
    rw [Matrix.sub_apply, hL, hR]
    by_cases hij : lvl i < lvl j
    · have hpow : C.det ^ lvl i * C.det * C.det ^ (lvl j - lvl i - 1) = C.det ^ lvl j := by
        rw [← pow_succ, ← pow_add]
        congr 1
        omega
      have hPsi : rescaleConj C lvl i j
          = C.det ^ (lvl j - lvl i - 1)
            * (C.adjugate * siGenMember (K := K) (n := n) * C) i j := ite_eq_left hij
      rw [hPsi, show C.det ^ lvl i
          * (C.det * (C.det ^ (lvl j - lvl i - 1)
            * (C.adjugate * siGenMember (K := K) (n := n) * C) i j))
        = (C.det ^ lvl i * C.det * C.det ^ (lvl j - lvl i - 1))
            * (C.adjugate * siGenMember (K := K) (n := n) * C) i j from by ring,
        hpow, mul_comm, sub_self]
      exact I.zero_mem
    · rw [rescaleConj_apply_of_le (not_lt.mp hij), mul_zero, mul_zero, sub_zero]
      exact I.mul_mem_right _ (hstr i j (not_lt.mp hij))
  -- multiply by `C` on the left and read off the conjugation identity
  have hCk : ∀ i j : Fin n,
      (C * ((C.adjugate * siGenMember (K := K) (n := n) * C) * levelDiag C.det lvl
        - levelDiag C.det lvl * (C.det • rescaleConj C lvl))) i j ∈ I := by
    intro i j
    rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (hk k j)
  have h1 : C * ((C.adjugate * siGenMember (K := K) (n := n) * C) * levelDiag C.det lvl)
      = C.det • (siGenMember (K := K) (n := n) * rescaleFrame C lvl) := by
    rw [← Matrix.mul_assoc, hCA, Matrix.smul_mul, rescaleFrame, Matrix.mul_assoc]
  have h2 : C * (levelDiag C.det lvl * (C.det • rescaleConj C lvl))
      = C.det • (rescaleFrame C lvl * rescaleConj C lvl) := by
    rw [← Matrix.mul_assoc, Matrix.mul_smul, rescaleFrame]
  have hEq : C * ((C.adjugate * siGenMember (K := K) (n := n) * C) * levelDiag C.det lvl
        - levelDiag C.det lvl * (C.det • rescaleConj C lvl))
      = C.det • (siGenMember (K := K) (n := n) * rescaleFrame C lvl
          - rescaleFrame C lvl * rescaleConj C lvl) := by
    rw [Matrix.mul_sub, h1, h2, smul_sub]
  intro i j
  have hmem := hCk i j
  rw [hEq, Matrix.smul_apply, smul_eq_mul] at hmem
  exact (hI.mem_or_mem hmem).resolve_left hdet

/-- **The normalisation survives the rescaling.**  Along an arc the rescaled
frame `C · D` has velocity `Ċ D + C Ḋ`, so its normalised velocity is
`D(z)⁻¹ X D(z) + D(z)⁻¹ Ḋ` with `X` the normalised velocity of `C`; both
summands are parabolic, since `D` is diagonal. -/
theorem frameNorm_rescale {I : Ideal (MvPolynomial (SIIndex (Fin n)) K)}
    {C : Matrix (Fin n) (Fin n) (MvPolynomial (SIIndex (Fin n)) K)} {lvl : Fin n → ℕ}
    {h : MvPolynomial (SIIndex (Fin n)) K} (hnorm : FrameNorm lvl C h I) :
    FrameNorm lvl (rescaleFrame C lvl) h I := by
  intro z hz hne' hnh m W U hdec
  have hne : MvPolynomial.eval z C.det ≠ 0 := fun h0 =>
    hne' (by rw [det_rescaleFrame, map_pow, h0, zero_pow (by omega)])
  have hX := hnorm z hz hne hnh m W U hdec
  have hCz : frameAt (rescaleFrame C lvl) z
      = frameAt C z * levelDiag (MvPolynomial.eval z C.det) lvl := by
    rw [rescaleFrame, frameAt_mul, frameAt_levelDiag]
  have hDdet : IsUnit (levelDiag (MvPolynomial.eval z C.det) lvl).det := by
    rw [det_levelDiag]
    exact isUnit_iff_ne_zero.mpr (pow_ne_zero _ hne)
  have hCinv : (frameAt C z)⁻¹ * frameAt C z = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_det_frameAt hne)
  have hVel : matD (frameArc (rescaleFrame C lvl) m.a)
      = matD (frameArc C m.a) * levelDiag (MvPolynomial.eval z C.det) lvl
        + frameAt C z * matD (frameArc (levelDiag C.det lvl) m.a) := by
    rw [rescaleFrame, frameArc_mul, matD_mul, matC_frameArc C m.base,
      matC_frameArc (levelDiag C.det lvl) m.base, frameAt_levelDiag]
  rw [hCz, hVel]
  have hid : (frameAt C z * levelDiag (MvPolynomial.eval z C.det) lvl)⁻¹ * (matC W + m.Z)
        * (frameAt C z * levelDiag (MvPolynomial.eval z C.det) lvl)
      + (frameAt C z * levelDiag (MvPolynomial.eval z C.det) lvl)⁻¹
        * (matD (frameArc C m.a) * levelDiag (MvPolynomial.eval z C.det) lvl
          + frameAt C z * matD (frameArc (levelDiag C.det lvl) m.a))
      = (levelDiag (MvPolynomial.eval z C.det) lvl)⁻¹
          * ((frameAt C z)⁻¹ * (matC W + m.Z) * frameAt C z
              + (frameAt C z)⁻¹ * matD (frameArc C m.a))
          * levelDiag (MvPolynomial.eval z C.det) lvl
        + (levelDiag (MvPolynomial.eval z C.det) lvl)⁻¹
          * (((frameAt C z)⁻¹ * frameAt C z)
              * matD (frameArc (levelDiag C.det lvl) m.a)) := by
    rw [Matrix.mul_inv_rev]
    noncomm_ring
  rw [hid, hCinv, Matrix.one_mul]
  have hD : IsBlockUpper lvl (levelDiag (MvPolynomial.eval z C.det) lvl) :=
    isBlockUpper_diagonal _
  exact IsBlockUpper.add ((hD.inv hDdet).mul hX |>.mul hD)
    ((hD.inv hDdet).mul (isBlockUpper_matD_frameArc_levelDiag _ _))

/-- **Clearing the denominator.**  The rational conjugate of a geometric frame
becomes a polynomial one after the diagonal rescaling
`C ↦ C · diag(det(C) ^ lvl i)`, which does not move the coordinate flag. -/
noncomputable def GeometricFrame.toAlgebraic {I : Ideal (MvPolynomial (SIIndex (Fin n)) K)} (hI : I.IsPrime)
    (F : GeometricFrame I) : AlgebraicFrame I where
  lvl := F.lvl
  C := rescaleFrame F.C F.lvl
  Ψ := rescaleConj F.C F.lvl
  h := F.h
  mono := F.mono
  det_notMem := det_rescaleFrame_notMem hI F.lvl F.det_notMem
  h_notMem := F.h_notMem
  strict := fun _ _ hij => by rw [rescaleConj_apply_of_le hij]; exact I.zero_mem
  conj := isFrameConj_rescale hI F.det_notMem F.strict
  norm := frameNorm_rescale F.norm

end Rescale

section Adapted

variable {K : Type u} [Field K] {n : ℕ}

/-- **The point clause of the adapted frame** from the algebraic one: the
conjugation identity `(N + tM) C = C Ψ` evaluated at `z`, in terms of the
frame unit. -/
theorem polyMat_matTup_eq_frameUnit {I : Ideal (MvPolynomial (SIIndex (Fin n)) K)}
    {C Ψ : Matrix (Fin n) (Fin n) (MvPolynomial (SIIndex (Fin n)) K)} (hcj : IsFrameConj I C Ψ)
    {z : SIIndex (Fin n) → K} (hz : z ∈ MvPolynomial.zeroLocus K I)
    (hne : MvPolynomial.eval z C.det ≠ 0) :
    polyMat (matTup Ψ) z
      = (↑(frameUnit C z)⁻¹ : Matrix (Fin n) (Fin n) K) * siMember (siCoords.symm z)
          * (↑(frameUnit C z) : Matrix (Fin n) (Fin n) K) := by
  have huM : IsUnit (frameAt C z) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_det_frameAt hne)
  rw [frameUnit_val huM, frameUnit_inv_val huM]
  exact frame_conj_at hcj hz hne

/-- **The arc clause of the adapted frame** from the algebraic one.  Along `a` the same identity gives
`Ψ ∘ a = E⁻¹ Φ E` with `E = C(a)` and `Φ` the member at the moving marked
point, so by the Leibniz rule (`matD_conj`)

```
∂_s(Ψ ∘ a) = C(z)⁻¹ ( Φ̇ + [N, Ė C(z)⁻¹] ) C(z) ,
```

and `Φ̇ = [N, Zw]` is the marking equation (`SIMarked`), while the fibre motion
is `Y = [W(x), N]` — evaluate `Ṙ = [P, W] + U` at the point, where `Ṙ(x) = 0`
(`matC_Rdot`).  So

```
C(z)⁻¹ Y C(z) − ∂_s(Ψ ∘ a) = [Ψ(z), D] ,  D = −C(z)⁻¹ (W(x) + Zw + Ė C(z)⁻¹) C(z) ,
```

and `D` lies in the parabolic exactly by `FrameNorm`. -/
theorem exists_parabolic_ambiguity {I : Ideal (MvPolynomial (SIIndex (Fin n)) K)}
    {lvl : Fin n → ℕ} {C Ψ : Matrix (Fin n) (Fin n) (MvPolynomial (SIIndex (Fin n)) K)}
    {h : MvPolynomial (SIIndex (Fin n)) K} (hcj : IsFrameConj I C Ψ) (hnorm : FrameNorm lvl C h I)
    {z : SIIndex (Fin n) → K} (hz : z ∈ MvPolynomial.zeroLocus K I)
    (hne : MvPolynomial.eval z C.det ≠ 0) (hnh : MvPolynomial.eval z h ≠ 0)
    (a : SIArc n K) (ha : a.InLocus I) (hb : a.base = siCoords.symm z)
    (Zw : Matrix (Fin n) (Fin n) K) (hm : SIMarked (siCoords.symm z) a.vel Zw)
    (Y : Matrix (Fin n) (Fin n) K) (hY : SIFibreMotion (siCoords.symm z) a.vel Zw Y) :
    ∃ D : Matrix (Fin n) (Fin n) K, IsBlockUpper lvl D ∧
      (↑(frameUnit C z)⁻¹ : Matrix (Fin n) (Fin n) K) * Y
          * (↑(frameUnit C z) : Matrix (Fin n) (Fin n) K)
        = matD (polyMatArc (matTup Ψ) a)
          + (polyMat (matTup Ψ) z * D - D * polyMat (matTup Ψ) z) := by
  have huC : IsUnit (frameAt C z).det := isUnit_det_frameAt hne
  have huM : IsUnit (frameAt C z) := (Matrix.isUnit_iff_isUnit_det _).mpr huC
  have hval : (frameUnit C z : Matrix (Fin n) (Fin n) K) = frameAt C z :=
    frameUnit_val huM
  have hinv : (((frameUnit C z)⁻¹ : (Matrix (Fin n) (Fin n) K)ˣ) :
      Matrix (Fin n) (Fin n) K) = (frameAt C z)⁻¹ := frameUnit_inv_val huM
  have hPsiz : polyMat (matTup Ψ) z
      = (frameAt C z)⁻¹ * siMember (siCoords.symm z) * frameAt C z := frame_conj_at hcj hz hne
  obtain ⟨W, U, ⟨hdec, hlow⟩, hYU⟩ := hY
  -- the fibre motion is the commutator of the member with `W(x)`
  have hmC : matC (Rdot (siCoords.symm z).1 (siCoords.symm z).2.1 (siCoords.symm z).2.2
      (pencil a.vel.1 a.vel.2.1) a.vel.2.2 Zw) = 0 := matC_Rdot hm
  rw [hdec, matC_commutator_add, matC_Pat] at hmC
  have hY0 : Y = matC W * siMember (siCoords.symm z) - siMember (siCoords.symm z) * matC W := by
    rw [hYU, show matC U
        = -(siMember (siCoords.symm z) * matC W - matC W * siMember (siCoords.symm z)) from
      eq_neg_of_add_eq_zero_right hmC, neg_sub]
  -- the velocity of the member at the moving marked point is the marking commutator
  have hM : (siCoords.symm z).2.1 = matC a.M := by rw [← hb]; rfl
  have ht : (siCoords.symm z).2.2 = PowerSeries.constantCoeff a.t := by rw [← hb]; rfl
  have hPhiD : matD (frameArc (siGenMember (K := K)) a)
      = siMember (siCoords.symm z) * Zw - Zw * siMember (siCoords.symm z) := by
    have hmk : matC (Qat (pencil a.vel.1 a.vel.2.1) (siCoords.symm z).2.2)
        + a.vel.2.2 • matD (Pat (siCoords.symm z).1 (siCoords.symm z).2.1 (siCoords.symm z).2.2)
      = siMember (siCoords.symm z) * Zw - Zw * siMember (siCoords.symm z) := hm
    rw [← hmk, matC_Qat_pencil, matD_Pat, frameArc_siGenMember, hM, ht]
    refine Matrix.ext fun i j => ?_
    show PowerSeries.coeff 1 (a.N i j + a.t * a.M i j)
      = PowerSeries.coeff 1 (a.N i j)
        + PowerSeries.constantCoeff a.t * PowerSeries.coeff 1 (a.M i j)
        + PowerSeries.coeff 1 a.t * PowerSeries.constantCoeff (a.M i j)
    rw [map_add, coeff_one_mul]
    ring
  -- the derivative of `Ψ` along the arc
  have hEu : IsUnit (frameArc C a).det := isUnit_det_frameArc hb hne
  have hPsia : polyMatArc (matTup Ψ) a
      = (frameArc C a)⁻¹ * frameArc siGenMember a * frameArc C a :=
    frame_conj_arc hcj ha hb hne
  have hCE : matC (frameArc C a) = frameAt C z := matC_frameArc C hb
  have hCG : matC (frameArc (siGenMember (K := K)) a) = siMember (siCoords.symm z) := by
    rw [matC_frameArc siGenMember hb, frameAt_siGenMember]
  have hDPsia : matD (polyMatArc (matTup Ψ) a)
      = (frameAt C z)⁻¹
          * (siMember (siCoords.symm z) * (Zw + matD (frameArc C a) * (frameAt C z)⁻¹)
            - (Zw + matD (frameArc C a) * (frameAt C z)⁻¹) * siMember (siCoords.symm z))
          * frameAt C z := by
    rw [hPsia, matD_conj hEu, hCE, hCG, hPhiD]
    noncomm_ring
  -- the parabolic ambiguity
  refine ⟨-((frameAt C z)⁻¹
    * (matC W + (Zw + matD (frameArc C a) * (frameAt C z)⁻¹)) * frameAt C z), ?_, ?_⟩
  · refine IsBlockUpper.neg ?_
    have hbu := hnorm z hz hne hnh ⟨⟨a, ha, hb⟩, Zw, hm⟩ W U ⟨hdec, hlow⟩
    have hCC : (frameAt C z)⁻¹ * frameAt C z = 1 := Matrix.nonsing_inv_mul _ huC
    have hrw : (frameAt C z)⁻¹
          * (matC W + (Zw + matD (frameArc C a) * (frameAt C z)⁻¹)) * frameAt C z
        = (frameAt C z)⁻¹ * (matC W + Zw) * frameAt C z
          + (frameAt C z)⁻¹ * (matD (frameArc C a) * ((frameAt C z)⁻¹ * frameAt C z)) := by
      noncomm_ring
    rw [hrw, hCC, Matrix.mul_one]
    exact hbu
  · rw [hval, hinv, hY0, hPsiz, hDPsia]
    have hCX : frameAt C z * (frameAt C z)⁻¹ = 1 := Matrix.mul_nonsing_inv _ huC
    rw [mul_neg, neg_mul, conj_mul_conj_eq hCX, conj_mul_conj_eq hCX]
    noncomm_ring

/-- **The adapted frame from the algebraic frame**: the frame unit of `C`, the
conjugate `Ψ` as a tuple, and the dense open `D(det C · h)`. -/
noncomputable def AlgebraicFrame.toAdapted {I : Ideal (MvPolynomial (SIIndex (Fin n)) K)}
    (hI : I.IsPrime) (F : AlgebraicFrame I) : AdaptedFrame I where
  lvl := F.lvl
  Ψ := matTup F.Ψ
  h₀ := F.C.det * F.h
  cfr := frameUnit F.C
  mono := F.mono
  h₀_notMem := fun hmem => (hI.mem_or_mem hmem).elim F.det_notMem F.h_notMem
  strict := F.strict
  conj := fun z hz hne0 => by
    rw [map_mul] at hne0
    exact polyMat_matTup_eq_frameUnit F.conj hz (left_ne_zero_of_mul hne0)
  arcs := fun z hz hne0 m Y hY => by
    rw [map_mul] at hne0
    exact exists_parabolic_ambiguity F.conj F.norm hz (left_ne_zero_of_mul hne0)
      (right_ne_zero_of_mul hne0) m.a m.inLocus m.base m.Z m.marked Y hY

end Adapted

/-! ### The frame in affine coordinates: `lem:local-model`(1) -/

section Residue

variable {K : Type u} [Field K] [IsAlgClosed K] {n : ℕ}

/-- **The generic pencil is nilpotent modulo `I`.**  Every coefficient of every
entry of `(μN + νM)^n` vanishes at every point of the dense open, where the
pencil is nilpotent (`pencilLocus`); `I` is prime and the open is dense, so the
coefficient lies in `I`. -/
theorem coeff_siGenPencil_pow_mem {τ : Nat.Partition n} {d : ℕ → ℕ}
    {N₀ : Matrix (Fin n) (Fin n) K} (Cc : SIComponent τ d N₀) (i j : Fin n)
    (m : Fin 2 →₀ ℕ) :
    ((pencil (siGenN (K := K) (n := n)) siGenM ^ n) i j).coeff m ∈ Cc.I := by
  classical
  have hI := Cc.locus.prime
  have hz : MvPolynomial.vanishingIdeal K (MvPolynomial.zeroLocus K Cc.I) = Cc.I :=
    MvPolynomial.IsPrime.vanishingIdeal_zeroLocus Cc.I
  have hzp : (MvPolynomial.vanishingIdeal K (MvPolynomial.zeroLocus K Cc.I)).IsPrime := by
    rw [hz]; exact hI
  have hne : (MvPolynomial.zeroLocus K Cc.I ∩
      {y | MvPolynomial.aeval y Cc.g ≠ 0}).Nonempty :=
    Height.Geometry.nonempty_inter_nonvanishing (by rw [hz]; exact Cc.locus.notMem)
  have hvi := Height.Geometry.vanishingIdeal_inter_dense hzp hne
  rw [hz] at hvi
  rw [← hvi]
  refine MvPolynomial.mem_vanishingIdeal_iff.2 fun z hz' => ?_
  obtain ⟨hzI, hzg⟩ := hz'
  have hloc := Cc.locus.locus z hzI (by
    rw [← MvPolynomial.aeval_eq_eval]
    exact hzg)
  have hnil : NilpotentPencil (siCoords.symm z).1 (siCoords.symm z).2.1 := hloc.1.1
  have h0 : (pencil (siCoords.symm z).1 (siCoords.symm z).2.1) ^ n = 0 :=
    pencil_pow_eq_zero_of_nilpotentPencil hnil
  have hmap : ((pencil (siGenN (K := K) (n := n)) siGenM) ^ n).map
      (MvPolynomial.map (MvPolynomial.eval z))
      = (pencil (siCoords.symm z).1 (siCoords.symm z).2.1) ^ n := by
    show ((MvPolynomial.map (MvPolynomial.eval z)).mapMatrix
      ((pencil (siGenN (K := K) (n := n)) siGenM) ^ n)) = _
    rw [map_pow]
    show ((pencil (siGenN (K := K) (n := n)) siGenM).map
      (MvPolynomial.map (MvPolynomial.eval z))) ^ n = _
    rw [map_pencil_map, map_siGenN, map_siGenM]
  have hij := congrFun (congrFun hmap i) j
  rw [h0] at hij
  have hzero : MvPolynomial.map (MvPolynomial.eval z)
      (((pencil (siGenN (K := K) (n := n)) siGenM) ^ n) i j) = 0 := hij
  have hc : (MvPolynomial.eval z)
      ((((pencil (siGenN (K := K) (n := n)) siGenM) ^ n) i j).coeff m) = 0 := by
    rw [← MvPolynomial.coeff_map, hzero]
    simp
  rw [MvPolynomial.aeval_eq_eval]
  exact hc

/-- The generic pencil is nilpotent under any coefficient map killing `I` — in
particular over the function field of the component. -/
theorem siGenPencil_pow_map_eq_zero {τ : Nat.Partition n} {d : ℕ → ℕ}
    {N₀ : Matrix (Fin n) (Fin n) K} (Cc : SIComponent τ d N₀)
    {S : Type u} [CommRing S] (φ : MvPolynomial (SIIndex (Fin n)) K →+* S)
    (hφ : ∀ f ∈ Cc.I, φ f = 0) :
    (pencil ((siGenN (K := K) (n := n)).map φ) (siGenM.map φ)) ^ n = 0 := by
  have hmap : (pencil ((siGenN (K := K) (n := n)).map φ) ((siGenM (K := K) (n := n)).map φ)) ^ n
      = ((pencil (siGenN (K := K) (n := n)) siGenM) ^ n).map (MvPolynomial.map φ) := by
    have h1 : ((pencil (siGenN (K := K) (n := n)) siGenM) ^ n).map (MvPolynomial.map φ)
        = ((MvPolynomial.map φ).mapMatrix ((pencil (siGenN (K := K) (n := n)) siGenM))) ^ n := by
      show ((MvPolynomial.map φ).mapMatrix ((pencil (siGenN (K := K) (n := n)) siGenM) ^ n)) = _
      rw [map_pow]
    rw [h1]
    show _ = ((pencil (siGenN (K := K) (n := n)) siGenM).map (MvPolynomial.map φ)) ^ n
    rw [map_pencil_map]
  rw [hmap]
  refine Matrix.ext fun i j => ?_
  show MvPolynomial.map φ (((pencil (siGenN (K := K) (n := n)) siGenM) ^ n) i j) = 0
  refine MvPolynomial.ext _ _ fun m => ?_
  rw [MvPolynomial.coeff_map]
  have hz0 : ((0 : MvPolynomial (Fin 2) S)).coeff m = 0 := by simp
  rw [hz0]
  exact hφ _ (coeff_siGenPencil_pow_mem Cc i j m)



instance instSIComponentPrime {τ : Nat.Partition n} {d : ℕ → ℕ}
    {N₀ : Matrix (Fin n) (Fin n) K} (Cc : SIComponent τ d N₀) : Cc.I.IsPrime :=
  Cc.locus.prime

variable {τ : Nat.Partition n} {d : ℕ → ℕ} {N₀ : Matrix (Fin n) (Fin n) K}

/-- The function field of a component of the incidence. -/
abbrev siFrac (Cc : SIComponent τ d N₀) : Type u :=
  FractionRing (MvPolynomial (SIIndex (Fin n)) K ⧸ Cc.I)

/-- The specialisation of a polynomial to the generic point of the component. -/
noncomputable def siGen (Cc : SIComponent τ d N₀) :
    MvPolynomial (SIIndex (Fin n)) K →+* siFrac Cc :=
  (algebraMap (MvPolynomial (SIIndex (Fin n)) K ⧸ Cc.I) (siFrac Cc)).comp
    (Ideal.Quotient.mk Cc.I)

theorem siGen_eq_zero_iff (Cc : SIComponent τ d N₀) (f : MvPolynomial (SIIndex (Fin n)) K) :
    siGen Cc f = 0 ↔ f ∈ Cc.I := by
  have hinj : Function.Injective
      (algebraMap (MvPolynomial (SIIndex (Fin n)) K ⧸ Cc.I) (siFrac Cc)) :=
    IsFractionRing.injective _ _
  constructor
  · intro h
    refine Ideal.Quotient.eq_zero_iff_mem.mp (hinj ?_)
    rw [map_zero]
    exact h
  · intro h
    show algebraMap (MvPolynomial (SIIndex (Fin n)) K ⧸ Cc.I) (siFrac Cc)
      (Ideal.Quotient.mk Cc.I f) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr h, map_zero]

/-- The generic pencil of the component, in the chart at the generic marked
point: `N + (t + u) M` over the function field. -/
noncomputable def siGenPat (Cc : SIComponent τ d N₀) :
    Matrix (Fin n) (Fin n) (PowerSeries (siFrac Cc)) :=
  Pat ((siGenN (K := K) (n := n)).map (siGen Cc)) (siGenM.map (siGen Cc)) (siGen Cc siGenT)

theorem siGenPat_pow_eq_zero (Cc : SIComponent τ d N₀) : siGenPat Cc ^ n = 0 := by
  rw [siGenPat, Pat_pow, siGenPencil_pow_map_eq_zero Cc (siGen Cc)
    (fun f hf => (siGen_eq_zero_iff Cc f).2 hf)]
  simp

theorem matC_siGenPat (Cc : SIComponent τ d N₀) :
    matC (siGenPat Cc) = (siGenMember (K := K) (n := n)).map (siGen Cc) := by
  rw [siGenPat, matC_Pat, siGenMember_map]

/-- The fibre flag of the component at its generic point: the reduction modulo
`u` of the kernel flag of the generic pencil over `F⟦u⟧`.  This is the flag
`V_• = S_•(x)` of `lem:local-model`. -/
noncomputable def siFibFlag (Cc : SIComponent τ d N₀) (k : ℕ) :
    Submodule (siFrac Cc) (Fin n → siFrac Cc) :=
  fibFlag (siGenPat Cc) k

theorem siFibFlag_mono (Cc : SIComponent τ d N₀) : Monotone (siFibFlag Cc) :=
  fun _ _ h => fibFlag_mono _ h

theorem siFibFlag_zero (Cc : SIComponent τ d N₀) : siFibFlag Cc 0 = ⊥ :=
  fibFlag_zero _

theorem siFibFlag_top (Cc : SIComponent τ d N₀) : siFibFlag Cc n = ⊤ :=
  fibFlag_eq_top _ (siGenPat_pow_eq_zero Cc)

theorem siFibFlag_lowering (Cc : SIComponent τ d N₀) (k : ℕ) {v : Fin n → siFrac Cc}
    (hv : v ∈ siFibFlag Cc (k + 1)) :
    ((siGenMember (K := K) (n := n)).map (siGen Cc)) *ᵥ v ∈ siFibFlag Cc k := by
  rw [← matC_siGenPat Cc]
  exact matC_mulVec_mem_fibFlag hv


/-- **A frame adapted to the fibre flag** — `lem:local-model`(1) for the
incidence, at the generic point of the component: a monotone level function
`lvl`, a matrix `C` of polynomials invertible on a dense open, and the statement
that over the function field `C` carries the coordinate flag of `lvl` onto the
fibre flag `V_• = S_•(x)` of the generic pencil.

This is the input `exists_frameNorm` needs.  `strict` — that
`C⁻¹ (N + tM) C` is block strict — follows (`FibreFrame.strict`), because the
member lowers the fibre flag. -/
structure FibreFrame (Cc : SIComponent τ d N₀) where
  /-- the level function of the coordinate flag -/
  lvl : Fin n → ℕ
  /-- the frame -/
  C : Matrix (Fin n) (Fin n) (MvPolynomial (SIIndex (Fin n)) K)
  mono : Monotone lvl
  det_notMem : C.det ∉ Cc.I
  /-- the frame carries the coordinate flag of `lvl` onto the fibre flag -/
  adapted : ∀ k, Submodule.map (C.map (siGen Cc)).mulVecLin (Height.Toolbox.levelFlag lvl k)
      = siFibFlag Cc k

theorem FibreFrame.isUnit_det {Cc : SIComponent τ d N₀} (Fr : FibreFrame Cc) :
    IsUnit ((Fr.C.map (siGen Cc)).det) := by
  have hdet : siGen Cc Fr.C.det = ((siGen Cc).mapMatrix Fr.C).det := RingHom.map_det _ _
  have hdet' : (Fr.C.map (siGen Cc)).det = siGen Cc Fr.C.det := hdet.symm
  rw [hdet']
  exact isUnit_iff_ne_zero.mpr fun h0 => Fr.det_notMem ((siGen_eq_zero_iff Cc _).1 h0)

/-- **`lem:local-model`(1)**: a frame adapted to the fibre flag makes the member
block strict, because the member lowers the fibre flag. -/
theorem FibreFrame.strict {Cc : SIComponent τ d N₀} (Fr : FibreFrame Cc) {i j : Fin n}
    (hle : Fr.lvl j ≤ Fr.lvl i) :
    (Fr.C.adjugate * siGenMember (K := K) (n := n) * Fr.C) i j ∈ Cc.I := by
  have hdet := Fr.isUnit_det
  set φ : MvPolynomial (SIIndex (Fin n)) K →+* siFrac Cc := siGen Cc with hφ
  set P : Matrix (Fin n) (Fin n) (siFrac Cc) := Fr.C.map φ with hPdef
  set Mb : Matrix (Fin n) (Fin n) (siFrac Cc) := (siGenMember (K := K) (n := n)).map φ with hMb
  have hA := Height.Toolbox.blockStrict_of_adapted hdet (siFibFlag_zero Cc) Fr.adapted
    (fun k v hv => siFibFlag_lowering Cc k hv) i j hle
  refine (siGen_eq_zero_iff Cc _).1 ?_
  have hm : φ.mapMatrix (Fr.C.adjugate * siGenMember (K := K) (n := n) * Fr.C)
      = P.adjugate * Mb * P := by
    rw [map_mul, map_mul, RingHom.map_adjugate]
    rfl
  have hcomm : Mb * P = P * (P⁻¹ * Mb * P) := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv P hdet, Matrix.one_mul]
  have hfin : P.adjugate * Mb * P = P.det • (P⁻¹ * Mb * P) := by
    rw [Matrix.mul_assoc, hcomm, ← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul,
      Matrix.one_mul]
  have hij := congrFun (congrFun hm i) j
  rw [hfin, Matrix.smul_apply, hA, smul_zero] at hij
  exact hij

/-- **The frame adapted to the fibre flag exists.**  The generic pencil is
nilpotent modulo `I` (`siGenPencil_pow_map_eq_zero`), so over the function field
its fibre flag runs from `⊥` to `⊤`; a basis adapted to it
(`Toolbox.exists_flagFrame`) gives the frame and its jump pattern `lvl`, and
clearing the denominators (`IsLocalization.exist_integer_multiples`) brings the
frame back to `K[V]`, with `det ∉ I` because scaling by a nonzero element of the
function field keeps the determinant nonzero — and rescaling does not change the
flag the frame carries. -/
theorem exists_fibreFrame (Cc : SIComponent τ d N₀) : Nonempty (FibreFrame Cc) := by
  classical
  obtain ⟨lvl, A, P, hmono, hPdet, hAstrict, hMP, hadapt⟩ :=
    Height.Toolbox.exists_blockStrict_of_flag (siFibFlag Cc) (siFibFlag_mono Cc)
      (siFibFlag_zero Cc) (siFibFlag_top Cc) ((siGenMember (K := K) (n := n)).map (siGen Cc))
      (fun k v hv => siFibFlag_lowering Cc k hv)
  set Q := MvPolynomial (SIIndex (Fin n)) K ⧸ Cc.I with hQ
  set ι : Q →+* siFrac Cc := algebraMap Q (siFrac Cc) with hιdef
  have hιinj : Function.Injective ι := IsFractionRing.injective Q (siFrac Cc)
  obtain ⟨bden, hbden⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors Q)
    (Finset.univ : Finset (Fin n × Fin n)) (fun ij => P ij.1 ij.2)
  set c : siFrac Cc := ι (bden : Q) with hc
  have hcne : c ≠ 0 := by
    rw [hc]
    intro h
    exact nonZeroDivisors.ne_zero bden.2 (hιinj (by rw [h, map_zero]))
  have hchoose : ∀ i j : Fin n, ∃ f : MvPolynomial (SIIndex (Fin n)) K,
      siGen Cc f = c * P i j := by
    intro i j
    obtain ⟨q, hq⟩ := hbden (i, j) (Finset.mem_univ _)
    obtain ⟨f, hf⟩ := Ideal.Quotient.mk_surjective q
    refine ⟨f, ?_⟩
    show ι (Ideal.Quotient.mk Cc.I f) = c * P i j
    rw [show Ideal.Quotient.mk Cc.I f = q from hf, hq, hc, Algebra.smul_def]
  choose Cf hCf using hchoose
  have hmapCf : (Matrix.of Cf).map (siGen Cc) = c • P := by
    refine Matrix.ext fun i j => ?_
    rw [Matrix.smul_apply, smul_eq_mul]
    exact hCf i j
  refine ⟨⟨lvl, Matrix.of Cf, hmono, ?_, ?_⟩⟩
  · intro hmem
    have h0 : siGen Cc ((Matrix.of Cf).det) = 0 := (siGen_eq_zero_iff Cc _).2 hmem
    rw [RingHom.map_det] at h0
    rw [show ((siGen Cc).mapMatrix (Matrix.of Cf)) = (Matrix.of Cf).map (siGen Cc) from rfl,
      hmapCf, Matrix.det_smul] at h0
    exact (mul_ne_zero (pow_ne_zero _ hcne) (isUnit_iff_ne_zero.mp hPdet)) h0
  · intro k
    rw [hmapCf, Height.Toolbox.map_smul_mulVecLin hcne]
    exact hadapt k

/-- The generic pencil of a component, as a matrix over `K[V][μ,ν]`. -/
noncomputable def siGenPencil :
    Matrix (Fin n) (Fin n) (Graded.Poly (MvPolynomial (SIIndex (Fin n)) K)) :=
  pencil (siGenN (K := K) (n := n)) siGenM

theorem map_siGenPencil_pow {S : Type u} [CommRing S]
    (φ : MvPolynomial (SIIndex (Fin n)) K →+* S) (k : ℕ) :
    (siGenPencil (K := K) (n := n) ^ k).map (MvPolynomial.map φ)
      = (pencil ((siGenN (K := K) (n := n)).map φ) (siGenM.map φ)) ^ k := by
  have h1 : (siGenPencil (K := K) (n := n) ^ k).map (MvPolynomial.map φ)
      = ((siGenPencil (K := K) (n := n)).map (MvPolynomial.map φ)) ^ k := by
    show ((MvPolynomial.map φ).mapMatrix (siGenPencil (K := K) (n := n) ^ k)) = _
    rw [map_pow]
    rfl
  rw [h1, siGenPencil, map_pencil_map]

/-- **The generic rank of the pencil is the generic-point one on a dense open.**
A minor witnessing the rank at the generic point of `V(I)` has a coefficient
outside `I`; off its zero locus the same minor survives at `z`, while every
larger minor vanishes on all of `V(I)`. -/
theorem exists_pencilGenRank_open (Cc : SIComponent τ d N₀) (k : ℕ) :
    ∃ h ∉ Cc.I, ∀ z ∈ MvPolynomial.zeroLocus K Cc.I, MvPolynomial.eval z h ≠ 0 →
      pencilGenRank (siCoords.symm z).1 (siCoords.symm z).2.1 k
        = pencilGenRank ((siGenN (K := K) (n := n)).map (siGen Cc)) (siGenM.map (siGen Cc)) k := by
  classical
  set φg : MvPolynomial (SIIndex (Fin n)) K →+* siFrac Cc := siGen Cc with hφg
  set r : ℕ := pencilGenRank ((siGenN (K := K) (n := n)).map φg) (siGenM.map φg) k with hr
  obtain ⟨f₀, g₀, hne⟩ := exists_minor_witness ((siGenN (K := K) (n := n)).map φg)
    (siGenM.map φg) k
  set D : Graded.Poly (MvPolynomial (SIIndex (Fin n)) K) :=
    ((siGenPencil (K := K) (n := n) ^ k).submatrix f₀ g₀).det with hD
  have hDF : MvPolynomial.map φg D
      = (((pencil ((siGenN (K := K) (n := n)).map φg) (siGenM.map φg)) ^ k).submatrix f₀ g₀).det := by
    rw [hD, ← det_submatrix_map, map_siGenPencil_pow]
  have hDne : MvPolynomial.map φg D ≠ 0 := by rw [hDF]; exact hne
  obtain ⟨m, hm⟩ : ∃ m, (MvPolynomial.map φg D).coeff m ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hDne (MvPolynomial.ext _ _ fun m => by rw [hcon m]; simp)
  rw [MvPolynomial.coeff_map] at hm
  refine ⟨D.coeff m, fun hmem => hm ((siGen_eq_zero_iff Cc _).2 hmem), ?_⟩
  intro z hz hzne
  set φz : Graded.Poly (MvPolynomial (SIIndex (Fin n)) K) →+* PolyF K :=
    (toPolyF K).comp (MvPolynomial.map (MvPolynomial.eval z)) with hφz
  have hkill : ∀ f ∈ RingHom.ker (MvPolynomial.map φg :
      Graded.Poly (MvPolynomial (SIIndex (Fin n)) K) →+* Graded.Poly (siFrac Cc)), φz f = 0 := by
    intro f hf
    have hf0 : MvPolynomial.map φg f = 0 := hf
    have hcoef : ∀ mm, f.coeff mm ∈ Cc.I := by
      intro mm
      refine (siGen_eq_zero_iff Cc _).1 ?_
      have := congrArg (fun p : Graded.Poly (siFrac Cc) => p.coeff mm) hf0
      rw [MvPolynomial.coeff_map] at this; simpa using this
    have : MvPolynomial.map (MvPolynomial.eval z) f = 0 := by
      refine MvPolynomial.ext _ _ fun mm => ?_
      rw [MvPolynomial.coeff_map]; simp
      exact (MvPolynomial.mem_vanishingIdeal_iff.1 (by
        rw [MvPolynomial.IsPrime.vanishingIdeal_zeroLocus Cc.I]
        exact hcoef mm) z hz).trans rfl
    show toPolyF K (MvPolynomial.map (MvPolynomial.eval z) f) = 0
    rw [this, map_zero]
  have hmapz : (siGenPencil (K := K) (n := n) ^ k).map φz
      = ((pencil (siCoords.symm z).1 (siCoords.symm z).2.1) ^ k).map (toPolyF K) := by
    show ((toPolyF K).mapMatrix ((MvPolynomial.map (MvPolynomial.eval z)).mapMatrix
      (siGenPencil (K := K) (n := n) ^ k))) = _
    rw [show ((MvPolynomial.map (MvPolynomial.eval z)).mapMatrix
        (siGenPencil (K := K) (n := n) ^ k))
      = (siGenPencil (K := K) (n := n) ^ k).map (MvPolynomial.map (MvPolynomial.eval z)) from rfl,
      map_siGenPencil_pow, map_siGenN, map_siGenM]
    rfl
  have hrank := Height.Orbital.rank_map_eq_of_minor_witness
    (siGenPencil (K := K) (n := n) ^ k)
    (RingHom.ker (MvPolynomial.map φg :
      Graded.Poly (MvPolynomial (SIIndex (Fin n)) K) →+* Graded.Poly (siFrac Cc)))
    φz hkill f₀ g₀ ?_ ?_
  · rw [hmapz] at hrank
    exact hrank
  · -- the witness survives at `z`
    show φz D ≠ 0
    intro h0
    have h1 : MvPolynomial.map (MvPolynomial.eval z) D = 0 := by
      have := h0
      rw [hφz] at this
      exact (map_eq_zero_iff _ (IsFractionRing.injective (Graded.Poly K) (PolyF K))).1 this
    have h2 := congrArg (fun p : Graded.Poly K => p.coeff m) h1
    rw [MvPolynomial.coeff_map] at h2; simp at h2
    exact hzne h2
  · -- larger minors vanish on all of `V(I)`
    intro f g
    show MvPolynomial.map φg (((siGenPencil (K := K) (n := n) ^ k).submatrix f g).det) = 0
    rw [← det_submatrix_map, map_siGenPencil_pow]
    exact det_submatrix_succ_eq_zero _ _ k f g

/-- **The fibre flag at a point of a dense open has the dimension it has at the
generic point.**  Both are `n − pencilGenRank`
(`finrank_fibFlag_add_pencilGenRank`), and the two generic ranks agree off
`V(h)` (`exists_pencilGenRank_open`).  This is the dimension half of "the
frame's flag *is* the fibre flag at `z`". -/
theorem exists_finrank_fibFlag_open (Cc : SIComponent τ d N₀) (k : ℕ) :
    ∃ h ∉ Cc.I, ∀ z ∈ MvPolynomial.zeroLocus K Cc.I, MvPolynomial.eval z h ≠ 0 →
      Module.finrank K (fibFlag (Pat (siCoords.symm z).1 (siCoords.symm z).2.1
              (siCoords.symm z).2.2) k)
        = Module.finrank (siFrac Cc) (siFibFlag Cc k) := by
  obtain ⟨h, hh, hz⟩ := exists_pencilGenRank_open Cc k
  refine ⟨h, hh, fun z hzmem hzne => ?_⟩
  have h1 := finrank_fibFlag_add_pencilGenRank (siCoords.symm z).1 (siCoords.symm z).2.1
    (siCoords.symm z).2.2 k
  have h2 := finrank_fibFlag_add_pencilGenRank ((siGenN (K := K) (n := n)).map (siGen Cc))
    (siGenM.map (siGen Cc)) (siGen Cc siGenT) k
  have h4 : Module.finrank (siFrac Cc) (siFibFlag Cc k)
      = Module.finrank (siFrac Cc) (fibFlag (Pat ((siGenN (K := K) (n := n)).map (siGen Cc))
          (siGenM.map (siGen Cc)) (siGen Cc siGenT)) k) := rfl
  have h3 := hz z hzmem hzne
  rw [h4]
  omega

/-- The generic pencil of a component in the chart at its marked point, as a
matrix of *polynomials* in `u`: `(N + tM) + u M`. -/
noncomputable def siGenPatP :
    Matrix (Fin n) (Fin n) (Polynomial (MvPolynomial (SIIndex (Fin n)) K)) :=
  Matrix.of fun i j => Polynomial.C (siGenN i j + siGenT * siGenM i j)
    + Polynomial.X * Polynomial.C (siGenM i j)

theorem map_siGenPatP {S : Type u} [Field S] (φ : MvPolynomial (SIIndex (Fin n)) K →+* S) :
    (siGenPatP (K := K) (n := n)).map (Polynomial.map φ)
      = PatP ((siGenN (K := K) (n := n)).map φ) (siGenM.map φ) (φ siGenT) := by
  refine Matrix.ext fun i j => ?_
  show Polynomial.map φ (Polynomial.C (siGenN i j + siGenT * siGenM i j)
      + Polynomial.X * Polynomial.C (siGenM i j)) = _
  rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
    Polynomial.map_C, map_add, map_mul]
  show Polynomial.C (φ (siGenN i j) + φ siGenT * φ (siGenM i j))
      + Polynomial.X * Polynomial.C (φ (siGenM i j))
    = Polynomial.C ((((siGenN (K := K) (n := n)).map φ)
        + (φ siGenT) • (siGenM.map φ)) i j)
      + Polynomial.X * Polynomial.C ((siGenM.map φ) i j)
  congr 2

/-- Every level of an adapted frame is at most `n`: the coordinate flag at
level `n` is everything, because the fibre flag is. -/
theorem FibreFrame.lvl_le {Cc : SIComponent τ d N₀} (Fr : FibreFrame Cc) (i : Fin n) :
    Fr.lvl i ≤ n := by
  classical
  by_contra hcon
  push_neg at hcon
  have hdet := Fr.isUnit_det
  set P := Fr.C.map (siGen Cc) with hP
  have hinj : Function.Injective (P.mulVecLin) := by
    intro x y hxy
    have h1 : P⁻¹ *ᵥ (P *ᵥ x) = P⁻¹ *ᵥ (P *ᵥ y) := by
      show P⁻¹ *ᵥ (P.mulVecLin x) = P⁻¹ *ᵥ (P.mulVecLin y)
      rw [hxy]
    rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul P hdet,
      Matrix.one_mulVec, Matrix.one_mulVec] at h1
  have htop : Submodule.map P.mulVecLin
      (Height.Toolbox.levelFlag Fr.lvl n) = ⊤ := by
    rw [Fr.adapted n]
    exact siFibFlag_top Cc
  have hsurj : Function.Surjective (P.mulVecLin) := by
    intro y
    refine ⟨P⁻¹ *ᵥ y, ?_⟩
    show P *ᵥ (P⁻¹ *ᵥ y) = y
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv P hdet, Matrix.one_mulVec]
  have h2 : Submodule.map P.mulVecLin ⊤ = (⊤ : Submodule (siFrac Cc) (Fin n → siFrac Cc)) := by
    rw [Submodule.map_top, LinearMap.range_eq_top.2 hsurj]
  have h3 : Height.Toolbox.levelFlag (L := siFrac Cc) Fr.lvl n = ⊤ :=
    Submodule.map_injective_of_injective hinj (htop.trans h2.symm)
  have h4 : (Pi.single i 1 : Fin n → siFrac Cc)
      ∈ Height.Toolbox.levelFlag (L := siFrac Cc) Fr.lvl n := by
    rw [h3]; trivial
  have h5 := h4 i hcon
  simp at h5

/-- **The frame's columns lift polynomially in `u`, over `K[V]` up to one
denominator.**  Over `F = Frac(K[V]/I)` the `i`-th column of an adapted frame
lies in the fibre flag, and by `Pencil.fibFlag_Pat_eq_map_polyKerFlag` the
lifting kernel vector may be taken polynomial in `u`.  A polynomial vector over
`F` has finitely many coefficients, so one `h ∉ I` clears all the denominators.

The conclusion is stated denominator-free: `v` is a kernel vector of the generic
polynomial chart modulo `I`, whose value at `u = 0` is `h` times the column. -/
theorem exists_polyLift {Cc : SIComponent τ d N₀} (Fr : FibreFrame Cc) (k : ℕ) (i : Fin n)
    (hi : Fr.lvl i ≤ k) :
    ∃ (h : MvPolynomial (SIIndex (Fin n)) K), h ∉ Cc.I ∧
      ∃ v : Fin n → Polynomial (MvPolynomial (SIIndex (Fin n)) K),
        (∀ j, Polynomial.map (siGen Cc) ((((siGenPatP (K := K) (n := n)) ^ k) *ᵥ v) j) = 0) ∧
        (∀ j, siGen Cc ((v j).coeff 0) = siGen Cc h * siGen Cc (Fr.C j i)) := by
  classical
  set Q := MvPolynomial (SIIndex (Fin n)) K ⧸ Cc.I with hQ
  set algF : Q →+* siFrac Cc := algebraMap Q (siFrac Cc) with halgF
  set P : Matrix (Fin n) (Fin n) (siFrac Cc) := Fr.C.map (siGen Cc) with hP
  -- the `i`-th column lies in the fibre flag
  have hcol : (fun j => P j i) ∈ siFibFlag Cc k := by
    have h1 : P.mulVecLin (Pi.single i 1) ∈ siFibFlag Cc k := by
      rw [← Fr.adapted k]
      exact ⟨Pi.single i 1, Height.Toolbox.single_mem_levelFlag hi, rfl⟩
    rwa [show P.mulVecLin (Pi.single i 1) = fun j => P j i from
      Height.Toolbox.mulVec_single_one P i] at h1
  -- a polynomial lift over `F`
  rw [siFibFlag, siGenPat, fibFlag_Pat_eq_map_polyKerFlag] at hcol
  obtain ⟨w, hw, hval⟩ := hcol
  have hwk : w ∈ Isotropy.kerFlag (PatP ((siGenN (K := K) (n := n)).map (siGen Cc))
      (siGenM.map (siGen Cc)) (siGen Cc siGenT)) k := hw
  -- clear the denominators
  choose b hbM hbeq using fun j : Fin n =>
    IsLocalization.integerNormalization_spec (nonZeroDivisors Q) (w j)
  set B : Q := ∏ j, b j with hB
  set q : Fin n → Polynomial Q := fun j => (∏ l ∈ Finset.univ.erase j, b l) •
    IsLocalization.integerNormalization (nonZeroDivisors Q) (w j) with hq
  have hqmap : ∀ j, (q j).map algF = algF B • w j := by
    intro j
    rw [hq]
    show Polynomial.map algF ((∏ l ∈ Finset.univ.erase j, b l) •
      IsLocalization.integerNormalization (nonZeroDivisors Q) (w j)) = _
    rw [Polynomial.smul_eq_C_mul, Polynomial.map_mul, Polynomial.map_C, hbeq j,
      show b j • w j = algF (b j) • w j from (algebraMap_smul (siFrac Cc) (b j) (w j)).symm,
      Polynomial.smul_eq_C_mul, Polynomial.smul_eq_C_mul, ← mul_assoc, ← Polynomial.C_mul,
      ← map_mul, hB, Finset.prod_erase_mul _ _ (Finset.mem_univ j)]
  obtain ⟨h, hh⟩ := Ideal.Quotient.mk_surjective B
  choose v hv using fun j => Polynomial.map_surjective (Ideal.Quotient.mk Cc.I)
    Ideal.Quotient.mk_surjective (q j)
  have hsiGen : ∀ j, Polynomial.map (siGen Cc) (v j) = siGen Cc h • w j := by
    intro j
    have h1 : Polynomial.map (siGen Cc) (v j)
        = Polynomial.map algF (Polynomial.map (Ideal.Quotient.mk Cc.I) (v j)) := by
      rw [Polynomial.map_map]
      rfl
    rw [h1, hv j, hqmap j]
    congr 1
    show algF B = algF (Ideal.Quotient.mk Cc.I h)
    rw [hh]
  have hBne : B ≠ 0 := by
    rw [hB]
    exact nonZeroDivisors.ne_zero (Submonoid.prod_mem _ fun j _ => hbM j)
  refine ⟨h, ?_, v, ?_, ?_⟩
  · intro hmem
    exact hBne (by rw [← hh]; exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem)
  · intro j
    have h2 : Polynomial.map (siGen Cc) ((((siGenPatP (K := K) (n := n)) ^ k) *ᵥ v) j)
        = ((((siGenPatP (K := K) (n := n)) ^ k).map (Polynomial.map (siGen Cc)))
            *ᵥ (fun l => Polynomial.map (siGen Cc) (v l))) j :=
      (RingHom.map_mulVec (Polynomial.mapRingHom (siGen Cc))
        ((siGenPatP (K := K) (n := n)) ^ k) v j)
    rw [h2]
    have h3 : (((siGenPatP (K := K) (n := n)) ^ k).map (Polynomial.map (siGen Cc)))
        = (PatP ((siGenN (K := K) (n := n)).map (siGen Cc)) (siGenM.map (siGen Cc))
            (siGen Cc siGenT)) ^ k := by
      show ((Polynomial.mapRingHom (siGen Cc)).mapMatrix
        ((siGenPatP (K := K) (n := n)) ^ k)) = _
      rw [map_pow, ← map_siGenPatP (siGen Cc)]
      rfl
    rw [h3]
    have h4 : (fun l => Polynomial.map (siGen Cc) (v l)) = fun l => siGen Cc h • w l := by
      funext l
      exact hsiGen l
    rw [h4]
    have h5 : (fun l => siGen Cc h • w l) = siGen Cc h • w := rfl
    rw [h5, Matrix.mulVec_smul, Isotropy.mem_kerFlag.mp hwk, smul_zero]
    rfl
  · intro j
    have h6 : siGen Cc ((v j).coeff 0) = (Polynomial.map (siGen Cc) (v j)).coeff 0 :=
      (Polynomial.coeff_map _ _).symm
    rw [h6, hsiGen j, Polynomial.smul_eq_C_mul, Polynomial.coeff_C_mul]
    congr 1
    have h7 : (w j).coeff 0 = P j i := by
      have := congrFun hval j
      rw [← this]
      show (w j).coeff 0 = Polynomial.eval 0 (w j)
      rw [Polynomial.coeff_zero_eq_eval_zero]
    rw [h7]
    rfl


/-- **One denominator for every column.**  `exists_polyLift` gives an `h` per
column; their product works for all of them at once, because both conditions are
linear in the lift, so a lift may be rescaled by the other denominators.

Only the level `k = lvl i` is needed: `IsBlockUpper lvl` is the statement that
each column `j` of a matrix lies in the coordinate flag at level `lvl j`. -/
theorem exists_polyLift_uniform {Cc : SIComponent τ d N₀} (Fr : FibreFrame Cc) :
    ∃ (h : MvPolynomial (SIIndex (Fin n)) K), h ∉ Cc.I ∧
      ∀ i : Fin n, ∃ v : Fin n → Polynomial (MvPolynomial (SIIndex (Fin n)) K),
        (∀ j, Polynomial.map (siGen Cc)
          ((((siGenPatP (K := K) (n := n)) ^ (Fr.lvl i)) *ᵥ v) j) = 0) ∧
        (∀ j, siGen Cc ((v j).coeff 0) = siGen Cc h * siGen Cc (Fr.C j i)) := by
  classical
  choose hI hnot v hv1 hv2 using fun i : Fin n => exists_polyLift Fr (Fr.lvl i) i le_rfl
  refine ⟨∏ i, hI i, ?_, ?_⟩
  · have hgen : ∀ s : Finset (Fin n), (∏ i ∈ s, hI i) ∉ Cc.I := by
      intro s
      induction s using Finset.induction with
      | empty =>
          intro hcon
          exact (Cc.locus.prime).ne_top
            (Ideal.eq_top_of_isUnit_mem _ (by simpa using hcon) isUnit_one)
      | insert a s ha ih =>
          rw [Finset.prod_insert ha]
          intro hcon
          rcases (Cc.locus.prime).mem_or_mem hcon with h1 | h1
          · exact hnot a h1
          · exact ih h1
    exact hgen Finset.univ
  · intro i
    refine ⟨fun j => Polynomial.C (∏ l ∈ Finset.univ.erase i, hI l) * v i j, ?_, ?_⟩
    · intro j
      have hsc : (((siGenPatP (K := K) (n := n)) ^ (Fr.lvl i)) *ᵥ
            fun j => Polynomial.C (∏ l ∈ Finset.univ.erase i, hI l) * v i j)
          = fun j => Polynomial.C (∏ l ∈ Finset.univ.erase i, hI l)
              * ((((siGenPatP (K := K) (n := n)) ^ (Fr.lvl i)) *ᵥ v i) j) := by
        funext l
        show ∑ m, _ * (Polynomial.C _ * v i m) = Polynomial.C _ * ∑ m, _ * v i m
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun m _ => by ring
      rw [hsc]
      show Polynomial.map (siGen Cc) (Polynomial.C _ * _) = 0
      rw [Polynomial.map_mul, hv1 i j, mul_zero]
    · intro j
      show siGen Cc ((Polynomial.C (∏ l ∈ Finset.univ.erase i, hI l) * v i j).coeff 0) = _
      rw [Polynomial.coeff_C_mul, map_mul, hv2 i j, ← mul_assoc, ← map_mul,
        Finset.prod_erase_mul _ _ (Finset.mem_univ i)]

/-- **The frame is adapted at every specialisation in which `h` is invertible.**
The lift of `exists_polyLift_uniform` is denominator-free, so it maps along any
ring homomorphism killing `I`; dividing by the image of `h` turns it into a
kernel vector whose value at `u = 0` is the column itself. -/
theorem exists_polyLift_spec {Cc : SIComponent τ d N₀} (Fr : FibreFrame Cc) :
    ∃ (h : MvPolynomial (SIIndex (Fin n)) K), h ∉ Cc.I ∧
      ∀ (S : Type u) [CommRing S] (φ : MvPolynomial (SIIndex (Fin n)) K →+* S),
        (∀ f ∈ Cc.I, φ f = 0) → IsUnit (φ h) → ∀ i : Fin n,
        ∃ w : Fin n → Polynomial S,
          (((siGenPatP (K := K) (n := n)).map (Polynomial.map φ)) ^ (Fr.lvl i)) *ᵥ w = 0 ∧
          ∀ j, (w j).coeff 0 = φ (Fr.C j i) := by
  classical
  obtain ⟨h, hnot, hlift⟩ := exists_polyLift_uniform Fr
  refine ⟨h, hnot, ?_⟩
  intro S _ φ hφI hφh i
  obtain ⟨v, hv1, hv2⟩ := hlift i
  obtain ⟨uh, huh⟩ := hφh
  refine ⟨fun j => Polynomial.C ((uh⁻¹ : Sˣ) : S) * Polynomial.map φ (v j), ?_, ?_⟩
  · funext j
    have hker : ∀ x : MvPolynomial (SIIndex (Fin n)) K, siGen Cc x = 0 → φ x = 0 :=
      fun x hx => hφI x ((siGen_eq_zero_iff Cc x).1 hx)
    have hzero : Polynomial.map φ ((((siGenPatP (K := K) (n := n)) ^ (Fr.lvl i)) *ᵥ v) j) = 0 := by
      refine Polynomial.ext fun m => ?_
      rw [Polynomial.coeff_map, Polynomial.coeff_zero]
      refine hker _ ?_
      have := congrArg (fun p : Polynomial (siFrac Cc) => p.coeff m) (hv1 j)
      rwa [Polynomial.coeff_map, Polynomial.coeff_zero] at this
    have hsc : ((((siGenPatP (K := K) (n := n)).map (Polynomial.map φ)) ^ (Fr.lvl i)) *ᵥ
          fun j => Polynomial.C ((uh⁻¹ : Sˣ) : S) * Polynomial.map φ (v j)) j
        = Polynomial.C ((uh⁻¹ : Sˣ) : S)
            * Polynomial.map φ ((((siGenPatP (K := K) (n := n)) ^ (Fr.lvl i)) *ᵥ v) j) := by
      have h1 : (((siGenPatP (K := K) (n := n)).map (Polynomial.map φ)) ^ (Fr.lvl i))
          = ((siGenPatP (K := K) (n := n)) ^ (Fr.lvl i)).map (Polynomial.map φ) := by
        show _ = (Polynomial.mapRingHom φ).mapMatrix ((siGenPatP (K := K) (n := n)) ^ (Fr.lvl i))
        rw [map_pow]
        rfl
      rw [h1]
      rw [show Polynomial.map φ ((((siGenPatP (K := K) (n := n)) ^ (Fr.lvl i)) *ᵥ v) j)
          = ((((siGenPatP (K := K) (n := n)) ^ (Fr.lvl i)).map (Polynomial.map φ)) *ᵥ
              fun m => Polynomial.map φ (v m)) j from
        RingHom.map_mulVec (Polynomial.mapRingHom φ)
          ((siGenPatP (K := K) (n := n)) ^ (Fr.lvl i)) v j]
      show ∑ m, _ * (Polynomial.C _ * Polynomial.map φ (v m))
        = Polynomial.C _ * ∑ m, _ * Polynomial.map φ (v m)
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ => by ring
    rw [hsc, hzero, mul_zero]
    rfl
  · intro j
    show ((Polynomial.C ((uh⁻¹ : Sˣ) : S)) * Polynomial.map φ (v j)).coeff 0 = _
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_map]
    have h2 : φ ((v j).coeff 0) = φ h * φ (Fr.C j i) := by
      have hdiff : (v j).coeff 0 - h * Fr.C j i ∈ Cc.I := by
        refine (siGen_eq_zero_iff Cc _).1 ?_
        rw [map_sub, map_mul, hv2 j, sub_self]
      have := hφI _ hdiff
      rw [map_sub, map_mul] at this
      exact sub_eq_zero.mp this
    rw [h2, ← mul_assoc, ← huh]
    rw [show ((uh⁻¹ : Sˣ) : S) * ((uh : Sˣ) : S) = 1 from by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one], one_mul]


/-- The truncation of an arc to first order: a `K[ε]`-point of the incidence. -/
noncomputable def siArcEps (a : SIArc n K) :
    MvPolynomial (SIIndex (Fin n)) K →+* DualNumber K :=
  (PowerSeries.toDualNumber).comp (siArcHom a)

theorem fst_siArcEps (a : SIArc n K) (f : MvPolynomial (SIIndex (Fin n)) K) :
    (siArcEps a f).fst = PowerSeries.constantCoeff (siArcHom a f) := by
  show (PowerSeries.toDualNumber (siArcHom a f)).fst = _
  rw [PowerSeries.fst_toDualNumber]

theorem snd_siArcEps (a : SIArc n K) (f : MvPolynomial (SIIndex (Fin n)) K) :
    (siArcEps a f).snd = PowerSeries.coeff 1 (siArcHom a f) := by
  show (PowerSeries.toDualNumber (siArcHom a f)).snd = _
  rw [PowerSeries.snd_toDualNumber]

/-- The generic polynomial chart along the truncated arc. -/
noncomputable def siPatEps (a : SIArc n K) :
    Matrix (Fin n) (Fin n) (DualNumber (Polynomial K)) :=
  ((siGenPatP (K := K) (n := n)).map (Polynomial.map (siArcEps a))).map Height.Toolbox.polyDual

theorem siPatEps_apply (a : SIArc n K) (i j : Fin n) :
    siPatEps a i j
      = Height.Toolbox.dnC (siArcEps a (siGenN i j + siGenT * siGenM i j))
        + TrivSqZeroExt.inl Polynomial.X
          * Height.Toolbox.dnC (siArcEps a (siGenM i j)) := by
  show Height.Toolbox.polyDual (Polynomial.map (siArcEps a)
      (Polynomial.C (siGenN i j + siGenT * siGenM i j)
        + Polynomial.X * Polynomial.C (siGenM i j))) = _
  rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
    Polynomial.map_C, map_add, map_mul, Height.Toolbox.polyDual_C, Height.Toolbox.polyDual_X,
    Height.Toolbox.polyDual_C]

theorem siArcHom_siGenN (a : SIArc n K) (i j : Fin n) :
    siArcHom a (siGenN i j) = a.N i j := by
  show MvPolynomial.aeval a.coords (MvPolynomial.X (Sum.inl (Sum.inl (i, j)))) = _
  rw [MvPolynomial.aeval_X]
  rfl

theorem siArcHom_siGenM (a : SIArc n K) (i j : Fin n) :
    siArcHom a (siGenM i j) = a.M i j := by
  show MvPolynomial.aeval a.coords (MvPolynomial.X (Sum.inl (Sum.inr (i, j)))) = _
  rw [MvPolynomial.aeval_X]
  rfl

theorem siArcHom_siGenT (a : SIArc n K) :
    siArcHom a (siGenT (K := K) (n := n)) = a.t := by
  show MvPolynomial.aeval a.coords (MvPolynomial.X (Sum.inr ())) = _
  rw [MvPolynomial.aeval_X]
  rfl

/-- The value of the chart along the truncated arc is the chart at the base
point. -/
theorem mfst_siPatEps (a : SIArc n K) :
    Height.Toolbox.mfst (siPatEps a) = PatP a.base.1 a.base.2.1 a.base.2.2 := by
  refine Matrix.ext fun i j => ?_
  rw [Height.Toolbox.mfst_apply, siPatEps_apply]
  show (Height.Toolbox.dnC (siArcEps a (siGenN i j + siGenT * siGenM i j))
      + TrivSqZeroExt.inl Polynomial.X
        * Height.Toolbox.dnC (siArcEps a (siGenM i j))).fst
    = Polynomial.C ((a.base.1 + a.base.2.2 • a.base.2.1) i j)
      + Polynomial.X * Polynomial.C (a.base.2.1 i j)
  rw [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_mul, Height.Toolbox.fst_dnMap,
    Height.Toolbox.fst_dnMap, TrivSqZeroExt.fst_inl, fst_siArcEps, fst_siArcEps,
    map_add, map_mul, siArcHom_siGenN, siArcHom_siGenM, siArcHom_siGenT]
  show Polynomial.C (PowerSeries.constantCoeff (a.N i j + a.t * a.M i j))
      + Polynomial.X * Polynomial.C (PowerSeries.constantCoeff (a.M i j)) = _
  rw [map_add, map_mul]
  rfl

/-- The first-order part of the chart along the truncated arc is the velocity of
the pencil at the moving marked point: `Q̇ + ṫ ∂_u P`. -/
theorem msnd_siPatEps (a : SIArc n K) :
    (Height.Toolbox.msnd (siPatEps a)).map Polynomial.coeToPowerSeries.ringHom
      = Qat (pencil a.vel.1 a.vel.2.1) a.base.2.2 + a.vel.2.2 • dPat a.base.2.1 := by
  refine Matrix.ext fun i j => ?_
  have hL : (Height.Toolbox.msnd (siPatEps a)) i j
      = Polynomial.C (a.vel.1 i j + a.base.2.2 * a.vel.2.1 i j + a.vel.2.2 * a.base.2.1 i j)
        + Polynomial.X * Polynomial.C (a.vel.2.1 i j) := by
    rw [Height.Toolbox.msnd_apply, siPatEps_apply]
    show (Height.Toolbox.dnC (siArcEps a (siGenN i j + siGenT * siGenM i j))
        + TrivSqZeroExt.inl Polynomial.X
          * Height.Toolbox.dnC (siArcEps a (siGenM i j))).snd = _
    rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_mul, Height.Toolbox.snd_dnMap,
      Height.Toolbox.snd_dnMap, TrivSqZeroExt.snd_inl, TrivSqZeroExt.fst_inl,
      smul_zero, add_zero, snd_siArcEps, snd_siArcEps, map_add, map_mul,
      siArcHom_siGenN, siArcHom_siGenM, siArcHom_siGenT]
    congr 1
    · congr 1
      show PowerSeries.coeff 1 (a.N i j + a.t * a.M i j)
        = PowerSeries.coeff 1 (a.N i j)
          + PowerSeries.constantCoeff a.t * PowerSeries.coeff 1 (a.M i j)
          + PowerSeries.coeff 1 a.t * PowerSeries.constantCoeff (a.M i j)
      rw [map_add, coeff_one_mul]
      ring
  have hR : (Qat (pencil a.vel.1 a.vel.2.1) a.base.2.2 + a.vel.2.2 • dPat a.base.2.1) i j
      = PowerSeries.C (a.vel.1 i j + a.base.2.2 * a.vel.2.1 i j + a.vel.2.2 * a.base.2.1 i j)
        + PowerSeries.X * PowerSeries.C (a.vel.2.1 i j) := by
    have h1 : (Qat (pencil a.vel.1 a.vel.2.1) a.base.2.2) i j
        = Graded.atPoint a.base.2.2 (MvPolynomial.C (a.vel.1 i j) * Graded.mu
            + MvPolynomial.C (a.vel.2.1 i j) * Graded.nu) := rfl
    rw [Matrix.add_apply, h1, Matrix.smul_apply, dPat_apply, PowerSeries.smul_eq_C_mul]
    simp only [map_add, map_mul, Graded.atPoint_mu, Graded.atPoint_nu, Graded.atPoint_C]
    ring
  rw [Matrix.map_apply, hL, hR, map_add, map_mul]
  rw [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C, Polynomial.coe_X,
    Polynomial.coe_C]


/-- **The first-order kernel witness along a marked arc.**  Specialising the
polynomial lift of `exists_polyLift_spec` at the dual-number point `z + ε ż` and
splitting into value and first-order part: the `i`-th column of the frame and
its velocity along the arc are the two components of a kernel vector of the
first-order deformation of the pencil. -/
theorem exists_firstOrder_witness {Cc : SIComponent τ d N₀} (Fr : FibreFrame Cc)
    {h₀ : MvPolynomial (SIIndex (Fin n)) K}
    (hspec : ∀ (S : Type u) [CommRing S] (φ : MvPolynomial (SIIndex (Fin n)) K →+* S),
        (∀ f ∈ Cc.I, φ f = 0) → IsUnit (φ h₀) → ∀ i : Fin n,
        ∃ w : Fin n → Polynomial S,
          (((siGenPatP (K := K) (n := n)).map (Polynomial.map φ)) ^ (Fr.lvl i)) *ᵥ w = 0 ∧
          ∀ j, (w j).coeff 0 = φ (Fr.C j i))
    (a : SIArc n K) (ha : a.InLocus Cc.I)
    (hh : PowerSeries.constantCoeff (siArcHom a h₀) ≠ 0) (i : Fin n) :
    ∃ y₀ y₁ : Fin n → PowerSeries K,
      (Pat a.base.1 a.base.2.1 a.base.2.2 ^ (Fr.lvl i)) *ᵥ y₀ = 0 ∧
      (Pat a.base.1 a.base.2.1 a.base.2.2 ^ (Fr.lvl i)) *ᵥ y₁
        + (Isotropy.dpow (Pat a.base.1 a.base.2.1 a.base.2.2)
            (Qat (pencil a.vel.1 a.vel.2.1) a.base.2.2 + a.vel.2.2 • dPat a.base.2.1)
            (Fr.lvl i)) *ᵥ y₀ = 0 ∧
      vecC y₀ = (fun l => matC (frameArc Fr.C a) l i) ∧
      vecC y₁ = (fun l => matD (frameArc Fr.C a) l i) := by
  classical
  set φ : MvPolynomial (SIIndex (Fin n)) K →+* DualNumber K := siArcEps a with hφ
  have hφI : ∀ f ∈ Cc.I, φ f = 0 := by
    intro f hf
    show PowerSeries.toDualNumber (siArcHom a f) = 0
    rw [show siArcHom a f = 0 from ha f hf, map_zero]
  have hφh : IsUnit (φ h₀) := by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, hφ, fst_siArcEps]
    exact isUnit_iff_ne_zero.mpr hh
  obtain ⟨wε, hw1, hw2⟩ := hspec (DualNumber K) φ hφI hφh i
  set Y : Fin n → DualNumber (Polynomial K) := fun l => Height.Toolbox.polyDual (wε l) with hY
  -- the kernel identity transports along `polyDual`
  have hA : ((siPatEps a) ^ (Fr.lvl i)) *ᵥ Y = 0 := by
    funext l
    have h1 : Height.Toolbox.polyDual
        (((((siGenPatP (K := K) (n := n)).map (Polynomial.map φ)) ^ (Fr.lvl i)) *ᵥ wε) l)
        = (((((siGenPatP (K := K) (n := n)).map (Polynomial.map φ)) ^ (Fr.lvl i)).map
            Height.Toolbox.polyDual) *ᵥ Y) l :=
      RingHom.map_mulVec Height.Toolbox.polyDual _ wε l
    have h2 : ((((siGenPatP (K := K) (n := n)).map (Polynomial.map φ)) ^ (Fr.lvl i)).map
        Height.Toolbox.polyDual) = (siPatEps a) ^ (Fr.lvl i) := by
      show (Height.Toolbox.polyDual.mapMatrix
        (((siGenPatP (K := K) (n := n)).map (Polynomial.map φ)) ^ (Fr.lvl i))) = _
      rw [map_pow]
      rfl
    rw [h2] at h1
    rw [← h1, show ((((siGenPatP (K := K) (n := n)).map (Polynomial.map φ)) ^ (Fr.lvl i)) *ᵥ wε) l
      = (0 : Fin n → Polynomial (DualNumber K)) l from by rw [hw1], Pi.zero_apply, map_zero]
    rfl
  -- split into value and first-order part
  have hfst : (Height.Toolbox.mfst (siPatEps a) ^ (Fr.lvl i)) *ᵥ Height.Toolbox.vfst Y = 0 := by
    rw [← Height.Toolbox.mfst_pow, ← Height.Toolbox.vfst_mulVec, hA]
    funext l
    simp [Height.Toolbox.vfst]
  have hsnd : (Height.Toolbox.mfst (siPatEps a) ^ (Fr.lvl i)) *ᵥ Height.Toolbox.vsnd Y
      + (Isotropy.dpow (Height.Toolbox.mfst (siPatEps a)) (Height.Toolbox.msnd (siPatEps a))
          (Fr.lvl i)) *ᵥ Height.Toolbox.vfst Y = 0 := by
    rw [← Height.Toolbox.mfst_pow, ← Height.Toolbox.msnd_pow, ← Height.Toolbox.vsnd_mulVec, hA]
    funext l
    simp [Height.Toolbox.vsnd]
  -- push to power series in `u`
  set ρ : Polynomial K →+* PowerSeries K := Polynomial.coeToPowerSeries.ringHom with hρ
  have hPatmap : (Height.Toolbox.mfst (siPatEps a)).map ρ
      = Pat a.base.1 a.base.2.1 a.base.2.2 := by
    rw [mfst_siPatEps, ← Pat_eq_map_PatP]
  have hval : ∀ l, PowerSeries.constantCoeff (ρ (Height.Toolbox.vfst Y l))
      = matC (frameArc Fr.C a) l i := by
    intro l
    have h1 : PowerSeries.constantCoeff (ρ (Height.Toolbox.vfst Y l))
        = (Height.Toolbox.vfst Y l).coeff 0 := by
      rw [hρ, Polynomial.coeToPowerSeries.ringHom_apply,
        ← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe]
    rw [h1]
    have h2 : (Height.Toolbox.vfst Y l).coeff 0
        = (Height.Toolbox.dnEval0 (Height.Toolbox.polyDual (wε l))).fst := by
      rw [Height.Toolbox.fst_dnMap]
      show _ = Polynomial.eval 0 ((Height.Toolbox.polyDual (wε l)).fst)
      rw [← Polynomial.coeff_zero_eq_eval_zero]
      rfl
    rw [h2, Height.Toolbox.dnEval0_polyDual, hw2 l, hφ, fst_siArcEps]
    rfl
  have hvel : ∀ l, PowerSeries.constantCoeff (ρ (Height.Toolbox.vsnd Y l))
      = matD (frameArc Fr.C a) l i := by
    intro l
    have h1 : PowerSeries.constantCoeff (ρ (Height.Toolbox.vsnd Y l))
        = (Height.Toolbox.vsnd Y l).coeff 0 := by
      rw [hρ, Polynomial.coeToPowerSeries.ringHom_apply,
        ← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe]
    rw [h1]
    have h2 : (Height.Toolbox.vsnd Y l).coeff 0
        = (Height.Toolbox.dnEval0 (Height.Toolbox.polyDual (wε l))).snd := by
      rw [Height.Toolbox.snd_dnMap]
      show _ = Polynomial.eval 0 ((Height.Toolbox.polyDual (wε l)).snd)
      rw [← Polynomial.coeff_zero_eq_eval_zero]
      rfl
    rw [h2, Height.Toolbox.dnEval0_polyDual, hw2 l, hφ, snd_siArcEps]
    rfl
  refine ⟨fun l => ρ (Height.Toolbox.vfst Y l), fun l => ρ (Height.Toolbox.vsnd Y l),
    ?_, ?_, ?_, ?_⟩
  · funext l
    have h1 := RingHom.map_mulVec ρ (Height.Toolbox.mfst (siPatEps a) ^ (Fr.lvl i))
      (Height.Toolbox.vfst Y) l
    have h2 : (Height.Toolbox.mfst (siPatEps a) ^ (Fr.lvl i)).map ρ
        = Pat a.base.1 a.base.2.1 a.base.2.2 ^ (Fr.lvl i) := by
      show (ρ.mapMatrix (Height.Toolbox.mfst (siPatEps a) ^ (Fr.lvl i))) = _
      rw [map_pow]
      show (Height.Toolbox.mfst (siPatEps a)).map ρ ^ (Fr.lvl i) = _
      rw [hPatmap]
    rw [h2] at h1
    show (Pat a.base.1 a.base.2.1 a.base.2.2 ^ (Fr.lvl i) *ᵥ (⇑ρ ∘ Height.Toolbox.vfst Y)) l
      = (0 : Fin n → PowerSeries K) l
    rw [← h1, hfst]
    simp
  · funext l
    have h1 := RingHom.map_mulVec ρ (Height.Toolbox.mfst (siPatEps a) ^ (Fr.lvl i))
      (Height.Toolbox.vsnd Y) l
    have h2 : (Height.Toolbox.mfst (siPatEps a) ^ (Fr.lvl i)).map ρ
        = Pat a.base.1 a.base.2.1 a.base.2.2 ^ (Fr.lvl i) := by
      show (ρ.mapMatrix (Height.Toolbox.mfst (siPatEps a) ^ (Fr.lvl i))) = _
      rw [map_pow]
      show (Height.Toolbox.mfst (siPatEps a)).map ρ ^ (Fr.lvl i) = _
      rw [hPatmap]
    rw [h2] at h1
    have h3 := RingHom.map_mulVec ρ (Isotropy.dpow (Height.Toolbox.mfst (siPatEps a))
      (Height.Toolbox.msnd (siPatEps a)) (Fr.lvl i)) (Height.Toolbox.vfst Y) l
    have h4 : (Isotropy.dpow (Height.Toolbox.mfst (siPatEps a))
        (Height.Toolbox.msnd (siPatEps a)) (Fr.lvl i)).map ρ
        = Isotropy.dpow (Pat a.base.1 a.base.2.1 a.base.2.2)
            (Qat (pencil a.vel.1 a.vel.2.1) a.base.2.2 + a.vel.2.2 • dPat a.base.2.1)
            (Fr.lvl i) := by
      rw [Isotropy.dpow_map, hPatmap, msnd_siPatEps]
    rw [h4] at h3
    have h5 : ρ (((Height.Toolbox.mfst (siPatEps a) ^ (Fr.lvl i)) *ᵥ Height.Toolbox.vsnd Y) l
        + ((Isotropy.dpow (Height.Toolbox.mfst (siPatEps a))
            (Height.Toolbox.msnd (siPatEps a)) (Fr.lvl i)) *ᵥ Height.Toolbox.vfst Y) l) = 0 := by
      have h6 := congrFun hsnd l
      rw [show ((Height.Toolbox.mfst (siPatEps a) ^ (Fr.lvl i)) *ᵥ Height.Toolbox.vsnd Y) l
          + ((Isotropy.dpow (Height.Toolbox.mfst (siPatEps a))
              (Height.Toolbox.msnd (siPatEps a)) (Fr.lvl i)) *ᵥ Height.Toolbox.vfst Y) l
        = 0 from h6, map_zero]
    rw [map_add, h1, h3] at h5
    show (Pat a.base.1 a.base.2.1 a.base.2.2 ^ (Fr.lvl i) *ᵥ (⇑ρ ∘ Height.Toolbox.vsnd Y)) l
        + (Isotropy.dpow (Pat a.base.1 a.base.2.1 a.base.2.2)
            (Qat (pencil a.vel.1 a.vel.2.1) a.base.2.2 + a.vel.2.2 • dPat a.base.2.1)
            (Fr.lvl i) *ᵥ (⇑ρ ∘ Height.Toolbox.vfst Y)) l = (0 : Fin n → PowerSeries K) l
    rw [Pi.zero_apply]
    exact h5
  · funext l
    exact hval l
  · funext l
    exact hvel l


/-- **The frame velocity lands in the fibre flag.**  Feed the velocity
decomposition into the first-order witness: only the commutator part of
`Ṗ = [P, W + Zw] + U` moves the kernel flag
(`Isotropy.dpow_vanishing_of_lowering`), so `y₁ + (W + Zw) y₀` is again in
`ker P^k`, and its value at `u = 0` is the `FrameNorm` column. -/
theorem velocity_mem_fibFlag {Cc : SIComponent τ d N₀} (Fr : FibreFrame Cc)
    {h₀ : MvPolynomial (SIIndex (Fin n)) K}
    (hspec : ∀ (S : Type u) [CommRing S] (φ : MvPolynomial (SIIndex (Fin n)) K →+* S),
        (∀ f ∈ Cc.I, φ f = 0) → IsUnit (φ h₀) → ∀ i : Fin n,
        ∃ w : Fin n → Polynomial S,
          (((siGenPatP (K := K) (n := n)).map (Polynomial.map φ)) ^ (Fr.lvl i)) *ᵥ w = 0 ∧
          ∀ j, (w j).coeff 0 = φ (Fr.C j i))
    (a : SIArc n K) (ha : a.InLocus Cc.I)
    (hh : PowerSeries.constantCoeff (siArcHom a h₀) ≠ 0) (i : Fin n)
    (Zw : Matrix (Fin n) (Fin n) K) (W U : Matrix (Fin n) (Fin n) (PowerSeries K))
    (hdec : IsVelocityDecomp a.base a.vel Zw W U) :
    (fun l => matD (frameArc Fr.C a) l i)
        + (matC W + Zw) *ᵥ (fun l => matC (frameArc Fr.C a) l i)
      ∈ fibFlag (Pat a.base.1 a.base.2.1 a.base.2.2) (Fr.lvl i) := by
  classical
  obtain ⟨y₀, y₁, hk0, hk1, hv0, hv1⟩ :=
    exists_firstOrder_witness Fr hspec a ha hh i
  set P : Matrix (Fin n) (Fin n) (PowerSeries K) := Pat a.base.1 a.base.2.1 a.base.2.2 with hP
  set k : ℕ := Fr.lvl i with hk
  set X : Matrix (Fin n) (Fin n) (PowerSeries K) :=
    W + Zw.map (PowerSeries.C : K →+* PowerSeries K) with hX
  -- the velocity of the pencil is a commutator plus a lowering part
  have hPdot : Qat (pencil a.vel.1 a.vel.2.1) a.base.2.2 + a.vel.2.2 • dPat a.base.2.1
      = (P * X - X * P) + U := by
    have hr := hdec.rdot
    rw [Rdot] at hr
    rw [hX]
    have : Qat (pencil a.vel.1 a.vel.2.1) a.base.2.2 + a.vel.2.2 • dPat a.base.2.1
        = (Qat (pencil a.vel.1 a.vel.2.1) a.base.2.2 + a.vel.2.2 • dPat a.base.2.1
            - (P * Zw.map (PowerSeries.C : K →+* PowerSeries K)
              - Zw.map (PowerSeries.C : K →+* PowerSeries K) * P))
          + (P * Zw.map (PowerSeries.C : K →+* PowerSeries K)
            - Zw.map (PowerSeries.C : K →+* PowerSeries K) * P) := by
      abel
    rw [this, hr]
    noncomm_ring
  -- only the commutator moves the flag
  have hy0mem : y₀ ∈ Isotropy.kerFlag P k := hk0
  have hdU : (Isotropy.dpow P U k) *ᵥ y₀ = 0 :=
    Isotropy.dpow_vanishing_of_lowering hdec.lowering k y₀ hy0mem
  have hdpow : (Isotropy.dpow P
      (Qat (pencil a.vel.1 a.vel.2.1) a.base.2.2 + a.vel.2.2 • dPat a.base.2.1) k) *ᵥ y₀
      = (P ^ k) *ᵥ (X *ᵥ y₀) := by
    rw [hPdot, Isotropy.dpow_add, Isotropy.dpow_commutator, Matrix.add_mulVec, hdU, add_zero,
      Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Isotropy.mem_kerFlag.mp hy0mem, Matrix.mulVec_zero, sub_zero]
  -- so the corrected velocity is again in the kernel
  have hker : (y₁ + X *ᵥ y₀) ∈ Isotropy.kerFlag P k := by
    rw [Isotropy.mem_kerFlag, Matrix.mulVec_add]
    rw [← hdpow]
    exact hk1
  have hvecC : vecC (y₁ + X *ᵥ y₀)
      = (fun l => matD (frameArc Fr.C a) l i)
        + (matC W + Zw) *ᵥ (fun l => matC (frameArc Fr.C a) l i) := by
    funext l
    show PowerSeries.constantCoeff (y₁ l + (X *ᵥ y₀) l) = _
    rw [map_add]
    have h1 : PowerSeries.constantCoeff (y₁ l) = matD (frameArc Fr.C a) l i := by
      have := congrFun hv1 l
      exact this
    have h2 : PowerSeries.constantCoeff ((X *ᵥ y₀) l)
        = ((matC W + Zw) *ᵥ (fun l => matC (frameArc Fr.C a) l i)) l := by
      have h3 : vecC (X *ᵥ y₀) = matC X *ᵥ vecC y₀ := Height.Orbital.vecC_mulVec X y₀
      have h4 : matC X = matC W + Zw := by
        rw [hX]
        refine Matrix.ext fun p q => ?_
        show PowerSeries.constantCoeff (W p q + PowerSeries.C (Zw p q)) = _
        rw [map_add]
        simp
      have h5 := congrFun h3 l
      rw [h4, hv0] at h5
      exact h5
    rw [h1, h2]
    rfl
  rw [← hvecC]
  exact vecC_mem_fibFlag hker


/-- Evaluation along an arc, at the base point, is evaluation at the base
point. -/
theorem constantCoeff_siArcHom {a : SIArc n K} {z : SIIndex (Fin n) → K}
    (hb : a.base = siCoords.symm z) (f : MvPolynomial (SIIndex (Fin n)) K) :
    PowerSeries.constantCoeff (siArcHom a f) = MvPolynomial.eval z f := by
  have hcomp : (PowerSeries.constantCoeff (R := K)).comp
      ((MvPolynomial.aeval a.coords : MvPolynomial (SIIndex (Fin n)) K →ₐ[K] PowerSeries K) :
        MvPolynomial (SIIndex (Fin n)) K →+* PowerSeries K) = MvPolynomial.eval z := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun i => ?_)
    · simp only [RingHom.comp_apply]
      show PowerSeries.constantCoeff ((MvPolynomial.aeval a.coords) (MvPolynomial.C c))
        = MvPolynomial.eval z (MvPolynomial.C c)
      simp
    · simp only [RingHom.comp_apply]
      show PowerSeries.constantCoeff ((MvPolynomial.aeval a.coords) (MvPolynomial.X i))
        = MvPolynomial.eval z (MvPolynomial.X i)
      rw [MvPolynomial.aeval_X, MvPolynomial.eval_X]
      have h1 := SIArc.siCoords_base a
      rw [hb, siCoords.apply_symm_apply] at h1
      exact (congrFun h1 i).symm
  exact congrFun (congrArg (fun g : MvPolynomial (SIIndex (Fin n)) K →+* K => ⇑g) hcomp) f
/-- The frame is invertible as a linear map wherever its determinant is. -/
theorem injective_frameAt {C : Matrix (Fin n) (Fin n) (MvPolynomial (SIIndex (Fin n)) K)}
    {z : SIIndex (Fin n) → K} (hdet : MvPolynomial.eval z C.det ≠ 0) :
    Function.Injective ((frameAt C z).mulVecLin) := by
  intro x y hxy
  have hu := isUnit_det_frameAt hdet
  have h1 : (frameAt C z)⁻¹ *ᵥ ((frameAt C z) *ᵥ x) = (frameAt C z)⁻¹ *ᵥ ((frameAt C z) *ᵥ y) := by
    show (frameAt C z)⁻¹ *ᵥ ((frameAt C z).mulVecLin x)
      = (frameAt C z)⁻¹ *ᵥ ((frameAt C z).mulVecLin y)
    rw [hxy]
  rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu,
    Matrix.one_mulVec, Matrix.one_mulVec] at h1

/-- **The frame's flag is the fibre flag at a point of the dense open.**  The
inclusion is the polynomial lift specialised at `z`; equality is the dimension
count, since both sides have the dimension of the coordinate flag at level `k`. -/
theorem fibFlag_eq_map_frameAt {Cc : SIComponent τ d N₀} (Fr : FibreFrame Cc)
    {h₀ : MvPolynomial (SIIndex (Fin n)) K}
    (hspec : ∀ (S : Type u) [CommRing S] (φ : MvPolynomial (SIIndex (Fin n)) K →+* S),
        (∀ f ∈ Cc.I, φ f = 0) → IsUnit (φ h₀) → ∀ i : Fin n,
        ∃ w : Fin n → Polynomial S,
          (((siGenPatP (K := K) (n := n)).map (Polynomial.map φ)) ^ (Fr.lvl i)) *ᵥ w = 0 ∧
          ∀ j, (w j).coeff 0 = φ (Fr.C j i))
    {z : SIIndex (Fin n) → K} (hz : z ∈ MvPolynomial.zeroLocus K Cc.I)
    (hh0 : MvPolynomial.eval z h₀ ≠ 0)
    (hdet : MvPolynomial.eval z Fr.C.det ≠ 0) (k : ℕ)
    (hdim : Module.finrank K (fibFlag (Pat (siCoords.symm z).1 (siCoords.symm z).2.1
              (siCoords.symm z).2.2) k) = Module.finrank (siFrac Cc) (siFibFlag Cc k)) :
    fibFlag (Pat (siCoords.symm z).1 (siCoords.symm z).2.1 (siCoords.symm z).2.2) k
      = Submodule.map (frameAt Fr.C z).mulVecLin (Height.Toolbox.levelFlag Fr.lvl k) := by
  classical
  set P : Matrix (Fin n) (Fin n) (PowerSeries K) :=
    Pat (siCoords.symm z).1 (siCoords.symm z).2.1 (siCoords.symm z).2.2 with hP
  have hzI : ∀ f ∈ Cc.I, MvPolynomial.eval z f = 0 := by
    intro f hf
    exact hz f hf
  -- every column of level `≤ k` lies in the fibre flag
  have hcol : ∀ i : Fin n, Fr.lvl i ≤ k →
      (fun l => frameAt Fr.C z l i) ∈ fibFlag P k := by
    intro i hi
    obtain ⟨w, hw1, hw2⟩ := hspec K (MvPolynomial.eval z) hzI
      (isUnit_iff_ne_zero.mpr hh0) i
    have hmat : ((siGenPatP (K := K) (n := n)).map (Polynomial.map (MvPolynomial.eval z)))
        = PatP (siCoords.symm z).1 (siCoords.symm z).2.1 (siCoords.symm z).2.2 := by
      rw [map_siGenPatP, map_siGenN, map_siGenM, eval_siGenT]
    rw [hmat] at hw1
    have hmem : (fun l => frameAt Fr.C z l i) ∈ fibFlag P (Fr.lvl i) := by
      rw [hP, fibFlag_Pat_eq_map_polyKerFlag]
      refine ⟨w, hw1, ?_⟩
      funext l
      show Polynomial.eval 0 (w l) = frameAt Fr.C z l i
      rw [← Polynomial.coeff_zero_eq_eval_zero, hw2 l]
      rfl
    exact fibFlag_mono P hi hmem
  have hle : Submodule.map (frameAt Fr.C z).mulVecLin (Height.Toolbox.levelFlag Fr.lvl k)
      ≤ fibFlag P k := by
    rw [Height.Toolbox.levelFlag_eq_span, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨i, hi, rfl⟩, rfl⟩
    show (frameAt Fr.C z).mulVecLin (Pi.single i 1) ∈ fibFlag P k
    rw [show (frameAt Fr.C z).mulVecLin (Pi.single i 1) = fun l => frameAt Fr.C z l i from
      Height.Toolbox.mulVec_single_one _ i]
    exact hcol i hi
  -- the dimensions agree
  have hd1 : Module.finrank K
      (Submodule.map (frameAt Fr.C z).mulVecLin (Height.Toolbox.levelFlag Fr.lvl k))
      = (Finset.univ.filter fun i => Fr.lvl i ≤ k).card := by
    rw [← (Submodule.equivMapOfInjective _ (injective_frameAt hdet)
      (Height.Toolbox.levelFlag Fr.lvl k)).finrank_eq]
    exact Height.Toolbox.finrank_levelFlag Fr.lvl k
  have hd2 : Module.finrank (siFrac Cc) (siFibFlag Cc k)
      = (Finset.univ.filter fun i => Fr.lvl i ≤ k).card := by
    rw [← Fr.adapted k]
    have hinj : Function.Injective ((Fr.C.map (siGen Cc)).mulVecLin) := by
      intro x y hxy
      have hu := Fr.isUnit_det
      have h1 : (Fr.C.map (siGen Cc))⁻¹ *ᵥ ((Fr.C.map (siGen Cc)) *ᵥ x)
          = (Fr.C.map (siGen Cc))⁻¹ *ᵥ ((Fr.C.map (siGen Cc)) *ᵥ y) := by
        show (Fr.C.map (siGen Cc))⁻¹ *ᵥ ((Fr.C.map (siGen Cc)).mulVecLin x)
          = (Fr.C.map (siGen Cc))⁻¹ *ᵥ ((Fr.C.map (siGen Cc)).mulVecLin y)
        rw [hxy]
      rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu,
        Matrix.one_mulVec, Matrix.one_mulVec] at h1
    rw [← (Submodule.equivMapOfInjective _ hinj
      (Height.Toolbox.levelFlag Fr.lvl k)).finrank_eq]
    exact Height.Toolbox.finrank_levelFlag Fr.lvl k
  refine (Submodule.eq_of_le_of_finrank_le hle ?_).symm
  rw [hd1, hdim, hd2]



/-! ### The normalisation of the frame -/

/-- **The normalisation of the frame** — `lem:local-model`(3) for the incidence.

Note the hypothesis: the frame is adapted to the **fibre** flag
(`FibreFrame`), not merely block strict.  That is not decoration.  Two flags are
lowered by the member at a marked point — `ker (N + tM)^•` and the fibre flag
`V_k = S_k(x)`, the reduction modulo `u` of the pencil's kernel flag over
`K⟦u⟧` — and they differ, because the type drops at a marked point.  `strict`
holds for either; `FrameNorm` is true only for the fibre flag.  Stated for an
arbitrary strict frame this theorem would be **false**: take `lvl` injective, a
complete flag refining the kernel flag, and `IsBlockUpper lvl` becomes
upper-triangularity, into which the frame velocity does not normalise.

## The proof: first order, no two-parameter trivialisation

The paper proves this by building `ĥ(s, u)` over `Λ = K⟦u⟧⟦s⟧` and
differentiating.  That is not necessary.  Everything needed is first order in
`s`, and the flag motion is computed by `Isotropy.dpow`.

Fix `z`, an arc `a` at `z`, a marking witness `Zw` and a decomposition
`Ṙ = [P, W] + U`, `Lowering P U`, where `P = Pat N M t` is the pencil at `z` over
`R = K⟦u⟧`.  Since `Ṙ = ∂_s(P ∘ a)|₀ − [P, Zw]`, putting `X := W + Zw` gives

```
Ṗ := ∂_s(P ∘ a)|₀ = [P, X] + U .
```

The deformation `P + εṖ` over `R[ε]` changes `P^k` by `ε·D_k(Ṗ)`
(`Isotropy.dpow`), and

```
D_k(Ṗ) = D_k([P, X]) + D_k(U) = (P^k X − X P^k) + D_k(U) ,
```

by `Isotropy.dpow_commutator`.  On `S_k = ker(P^k)` the term `X P^k` dies and so
does `D_k(U)`, by `Isotropy.dpow_vanishing_of_lowering` — *a lowering
perturbation does not move the kernel flag to first order*, which is exactly the
converse of the lemma the velocity decomposition is built from.  So

```
(D_k(Ṗ)) w₀ = P^k (X w₀)        for w₀ ∈ S_k .                            (∗)
```

Now let `lvl i ≤ k` and suppose the `i`-th column of the frame, at the
*dual-number point* `z + ε ż` of `V(I)`, lies in the fibre flag there: that is,
there are `w₀, w₁ ∈ Rⁿ` with

```
P^k w₀ = 0 ,   P^k w₁ + (D_k(Ṗ)) w₀ = 0 ,   w₀(0) = C(z) eᵢ ,   w₁(0) = Ė eᵢ
```

(`Ė = matD (frameArc C a)`; `C(z + εż) = C(z) + ε Ė` is first-order Taylor,
`PowerSeries.toDualNumber` and `MvPolynomial.aeval_dualNumber` in
`Toolbox/DualNumber.lean`).  By (∗) the second equation reads
`P^k (w₁ + X w₀) = 0`, so `w₁ + X w₀ ∈ S_k` and therefore

```
Ė eᵢ + (matC W + Zw) C(z) eᵢ  =  (w₁ + X w₀)(0)  ∈  V_k(z) .
```

If the frame is adapted at `z`, `V_k(z) = C(z) · levelFlag lvl k`, and applying
`C(z)⁻¹` gives, for every `k` and every `i` of level `≤ k`,

```
C(z)⁻¹ (matC W + Zw) C(z) eᵢ + C(z)⁻¹ Ė eᵢ ∈ levelFlag lvl k ,
```

which is `IsBlockUpper lvl` of that matrix — `FrameNorm`.

## How it is assembled

There are two inputs.

**The polynomial lifts.**  `Pencil.fibFlag_Pat_eq_map_polyKerFlag`: for
`P = Pat N M t₀`, which is affine in `u` (`Pencil.PatP`), every vector of `V_k`
is the value at `u = 0` of a kernel vector of `P^k` with **polynomial** entries.
It is a dimension count, not a structure theorem —
`Isotropy.finrank_map_kerFlag` reduces both flags to the ranks of their kernel
modules, `Isotropy.finrank_kerFlag_toK` turns those into ranks over `F(u)` and
`F⸨u⸩`, and `Orbital.exists_genericRank` at `⊥` says a maximal nonzero minor
over `F[u]` survives both embeddings, so the two ranks agree.

**The dimensions at a point.**  `exists_finrank_fibFlag_open`: `dim V_k(z)`
equals the fibre-flag dimension at the generic point of `V(I)` off a
hypersurface — via `finrank_fibFlag_add_pencilGenRank` (the fibre flag is the
generic jump, at *every* point of `ℙ¹`, because the witnessing minor is
homogeneous and `Graded.atPoint` cannot kill it) and `exists_pencilGenRank_open`.

They are put together in three steps:

1. **Clear the denominators** (`exists_polyLift`, `exists_polyLift_uniform`,
   `exists_polyLift_spec`).  `FibreFrame.adapted` says `C eᵢ ∈ V_k` over
   `F = Frac(K[V]/I)` for `lvl i ≤ k`; by the first theorem the lift is a vector
   of polynomials in `u` over `F`, i.e. finitely many elements of `F`, so one
   `h ∉ I` clears every denominator and the lift maps to any `K`-algebra killing
   `I` in which `h` is a unit.  **This is where the `h` of `FrameNorm` comes
   from.**
2. **Specialise** (`exists_firstOrder_witness`, `fibFlag_eq_map_frameAt`).  At a
   point `z` of `D(h)` the lift gives `C(z) · levelFlag lvl k ⊆ V_k(z)`, and the
   second theorem upgrades that to equality by dimension.  At the dual-number
   point `z + ε ż` — a `K[ε]`-point of `V(I)`, where `h` is still invertible
   because `h(z) ≠ 0` — it gives the pair `(w₀, w₁)`, `C(z + εż) = C(z) + ε Ė`
   being first-order Taylor (`PowerSeries.toDualNumber`,
   `Toolbox.mfst`/`msnd`).
3. **Assemble** (`velocity_mem_fibFlag`), as in the proof above:
   `Isotropy.dpow_commutator` and `Isotropy.dpow_vanishing_of_lowering` give
   `P^k (w₁ + X w₀) = 0`, so
   `Ė eᵢ + (matC W + Zw) C(z) eᵢ ∈ V_k(z) = C(z)·levelFlag lvl k`, which is
   `IsBlockUpper lvl` of the `FrameNorm` matrix. -/
theorem exists_frameNorm {Cc : SIComponent τ d N₀} (Fr : FibreFrame Cc) :
    ∃ h ∉ Cc.I, FrameNorm Fr.lvl Fr.C h Cc.I := by
  classical
  obtain ⟨h₀, hh₀, hspec⟩ := exists_polyLift_spec Fr
  choose hd hdnot hdim using fun j : Fin n => exists_finrank_fibFlag_open Cc (Fr.lvl j)
  refine ⟨h₀ * ∏ j, hd j, ?_, ?_⟩
  · intro hmem
    rcases (Cc.locus.prime).mem_or_mem hmem with h1 | h1
    · exact hh₀ h1
    · have hgen : ∀ s : Finset (Fin n), (∏ j ∈ s, hd j) ∉ Cc.I := by
        intro s
        induction s using Finset.induction with
        | empty =>
            intro hcon
            exact (Cc.locus.prime).ne_top
              (Ideal.eq_top_of_isUnit_mem _ (by simpa using hcon) isUnit_one)
        | insert p s hp ih =>
            rw [Finset.prod_insert hp]
            intro hcon
            rcases (Cc.locus.prime).mem_or_mem hcon with h2 | h2
            · exact hdnot p h2
            · exact ih h2
      exact hgen Finset.univ h1
  · intro z hz hdetne hhne m W U hdec
    intro i j hlt
    set c := frameAt Fr.C z with hc
    have hcu : IsUnit c.det := isUnit_det_frameAt hdetne
    have hb := m.base
    have hh0z : MvPolynomial.eval z h₀ ≠ 0 := by
      intro h0
      exact hhne (by rw [map_mul, h0, zero_mul])
    have hhdz : MvPolynomial.eval z (hd j) ≠ 0 := by
      intro h0
      refine hhne ?_
      rw [map_mul, map_prod, Finset.prod_eq_zero (Finset.mem_univ j) h0, mul_zero]
    have harc : PowerSeries.constantCoeff (siArcHom m.a h₀) ≠ 0 := by
      rw [constantCoeff_siArcHom hb]
      exact hh0z
    have hdec2 : IsVelocityDecomp m.a.base m.a.vel m.Z W U := by
      rw [hb]; exact hdec
    have hmem := velocity_mem_fibFlag Fr hspec m.a m.inLocus harc j m.Z W U hdec2
    rw [hb, matC_frameArc Fr.C hb] at hmem
    have hflag := fibFlag_eq_map_frameAt Fr hspec hz hh0z hdetne (Fr.lvl j)
      (hdim j z hz hhdz)
    rw [hflag] at hmem
    obtain ⟨x, hx, hxv⟩ := hmem
    have hAcol : (c⁻¹ * (matC W + m.Z) * c + c⁻¹ * matD (frameArc Fr.C m.a)) *ᵥ
        (Pi.single j 1 : Fin n → K) = x := by
      have hsplit : c⁻¹ * (matC W + m.Z) * c + c⁻¹ * matD (frameArc Fr.C m.a)
          = c⁻¹ * ((matC W + m.Z) * c + matD (frameArc Fr.C m.a)) := by
        noncomm_ring
      have hcol : ((matC W + m.Z) * c + matD (frameArc Fr.C m.a)) *ᵥ
          (Pi.single j 1 : Fin n → K) = c *ᵥ x := by
        rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, Height.Toolbox.mulVec_single_one c j,
          Height.Toolbox.mulVec_single_one (matD (frameArc Fr.C m.a)) j]
        rw [show (c *ᵥ x) = (fun l => matD (frameArc Fr.C m.a) l j)
            + (matC W + m.Z) *ᵥ (fun l => c l j) from hxv]
        abel
      rw [hsplit, ← Matrix.mulVec_mulVec, hcol, Matrix.mulVec_mulVec,
        Matrix.nonsing_inv_mul c hcu, Matrix.one_mulVec]
    have hij : (c⁻¹ * (matC W + m.Z) * c + c⁻¹ * matD (frameArc Fr.C m.a)) i j = x i := by
      have h1 := congrFun hAcol i
      rw [Height.Toolbox.mulVec_single_one] at h1
      exact h1
    rw [hij]
    exact hx i hlt

/-- **The geometric frame** — `lem:local-model`(1),(3) for the incidence, in the
form the geometry produces them: a frame with a *rational* conjugate.

For every irreducible `V(I)` whose generic member has type `τ` there are a
monotone level function `lvl`, a matrix `C` of polynomials with `det C ∉ I`,
and an auxiliary `h ∉ I`, such that on the dense open `V ∖ V(det C · h)`

* the conjugate `C⁻¹ (N + tM) C` — whose entries are the entries of
  `adj(C) (N + tM) C` divided by `det C` — lies in the nilradical of the
  coordinate flag of `lvl`, which is `lem:local-model`(1): the frame carries
  the coordinate flag onto the fibre flag `V_•(z)`, and the member lowers the
  fibre flag.  This is `exists_fibreFrame` and `FibreFrame.strict`;
* the frame is normalised along arcs (`FrameNorm`), which is
  `lem:local-model`(3): the two-parameter trivialisation of `thm:reduction`.
  This is `exists_frameNorm`.

Nothing here refers to the fibre flag or to the pencil apparatus: these are the
only two consequences of adaptedness that `AdaptedFrame` uses. -/
theorem nonempty_geometricFrame (Cc : SIComponent τ d N₀) :
    Nonempty (GeometricFrame Cc.I) := by
  obtain ⟨Fr⟩ := exists_fibreFrame Cc
  obtain ⟨h, hh, hnorm⟩ := exists_frameNorm Fr
  exact ⟨⟨Fr.lvl, Fr.C, h, Fr.mono, Fr.det_notMem, hh,
    fun _ _ hle => Fr.strict hle, hnorm⟩⟩

end Residue

end Height.Chain
