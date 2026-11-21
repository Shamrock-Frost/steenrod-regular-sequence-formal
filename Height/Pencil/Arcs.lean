import Height.Toolbox.BaseChange
import Height.Pencil.Marked
import Height.Pencil.Commutator
import Height.Orbital.GenericRank

/-!
# Arcs of pencils: kernel flatness and torsion classes

The paper, `lem:flag-flat`(1) and `cor:arc-torsion`, in the arc-of-pencils
form.

## Objects

An arc of pencils is a pair `(Ns, Ms)` of matrices over `K⟦s⟧`; its base point
is `(matC Ns, matC Ms)` and its velocity `(matD Ns, matD Ms)`
(`Height/Orbital/Arcs.lean`).  The two objects this file revolves around
are:

* `pencilFF N M`, the pencil `μN + νM` over the function field
  `FF K = K(μ,ν) = Frac (K[μ,ν])`;
* `arcPencil Ns Ms`, the pencil of the arc, read as a matrix over
  `(FF K)⟦s⟧` through the "swap" homomorphism
  `psSwap : K[μ,ν] ⊗ K⟦s⟧ → K⟦s⟧ ⊗ K[μ,ν]` — a polynomial in `μ, ν` with
  power-series coefficients is a power series with polynomial coefficients.

The point of `arcPencil` is that `(FF K)⟦s⟧` is a *discrete valuation ring
with residue field the function field*: its reduction modulo `s` is
`pencilFF` at the base point (`matC_arcPencil`) and its `s`-linear
coefficient is `pencilFF` at the velocity (`matD_arcPencil`).  Kernel
flatness is then the kernel-lifting lemma `Toolbox.exists_kernel_lift`
applied over that DVR, with no graded bookkeeping at all.

## Remarks on the formulation

1. **Kernel flatness is stated over the function field, not degreewise.**
   The degreewise form takes `v ∈ kerPiece N M k e` and
   `v̇ ∈ (Graded.GradedPresentation.free K (Fin n)).piece e`.
   `cor:arc-torsion` and `thm:realized-bound` use only
   the consequence over `K(ℙ¹)`, and the degreewise statement costs a
   coordinatisation of `B_e` that the function-field statement does not need:
   `(FF K)⟦s⟧` is already a DVR with the right residue field.  What is proved
   is therefore `kernel_flat`: for `v` in the kernel of `P^k` over `FF K`
   there is `v̇` over `FF K` with `D_k(Ṗ) v = − P^k v̇`.  The homogeneity of
   `v̇` is never used in the paper.
2. **`arc_rank_eq` produces constancy of the rank profile, not membership of
   the locus.**  `GenericType` ("all but finitely many members `N + tM`
   have type `τ`") and `HasMultidegree` (a Hilbert-function statement
   for `e ≫ 0`) are not rank conditions on finitely many polynomial matrices
   as they stand: the first quantifies over a finite exceptional set in the
   *base field*, which has no meaning at the generic point of an arc, and the
   second over all large `e`.  What is a rank condition — and what kernel
   flatness actually consumes — is the rank of `P^k` over the function field.
   `arc_rank_eq` gives a `g ∉ P` such that at every point of `V(P) ∖ V(g)`
   every arc in `V(P)` has the same function-field rank profile as its base
   point.  `GenericType`/`HasMultidegree` at the generic point are not derived
   from this here.
3. **Nilpotence of the pencil is a hypothesis, not a consequence.**
   `exists_commutator_fractionRing` needs `P^n = 0` over `K[μ,ν]` at the base
   point, and `exists_commutator_of_arc` needs it over `K⟦s⟧[μ,ν]` along the
   arc (which gives the base-point form, `pencil_pow_matC_eq_zero`, and makes
   the rank hypothesis automatic above level `n`).
   `Chain.NilpotentPencil` — "every `sN + tM` is nilpotent" — implies it only
   over an infinite field, through Cayley–Hamilton and
   `MvPolynomial.funext`; the consumer supplies it, since along an arc it
   comes from the equations of the locus rather than from the base point.

## Theorems

* `arc_rank_eq` — the genericity statement above.
* `kernel_flat` — `lem:flag-flat`(1).
* `exists_commutator_fractionRing`, and its packaged form
  `exists_commutator_of_arc` (which only needs rank constancy up to level `n`,
  the higher levels being supplied by `arcRankEq_of_nilpotent`) —
  `cor:arc-torsion`.
* `freeClass_eq_zero`, `freeClass_eq_zero_atInf` — the free part of the class
  of a realised direction vanishes at every point of `ℙ¹`,
  through the chart-independent `freeClass_eq_zero_of_chart`.
-/

namespace Height.Pencil

open Matrix Height.Graded Height.Orbital Height.Geometry Height.Toolbox

universe u

section Objects

variable {K : Type u} [Field K] {n : ℕ}

/-- `L = K(μ, ν)`, the fraction field of `B = K[μ, ν]`; the function field of
`ℙ¹` in homogeneous form. -/
abbrev FF (K : Type u) [Field K] : Type u := FractionRing (Graded.Poly K)

/-- Scalars into the function field. -/
noncomputable def kFF (K : Type u) [Field K] : K →+* FF K :=
  (algebraMap (Graded.Poly K) (FF K)).comp (MvPolynomial.C : K →+* Graded.Poly K)

/-- The pencil `μN + νM` over the function field. -/
noncomputable def pencilFF (N M : Matrix (Fin n) (Fin n) K) :
    Matrix (Fin n) (Fin n) (FF K) :=
  (pencil N M).map (algebraMap (Graded.Poly K) (FF K))

theorem pencilFF_apply (N M : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    pencilFF N M i j =
      kFF K (N i j) * algebraMap (Graded.Poly K) (FF K) mu +
        kFF K (M i j) * algebraMap (Graded.Poly K) (FF K) nu := by
  show algebraMap (Graded.Poly K) (FF K) (pencil N M i j) = _
  simp [pencil, kFF]

/-- A polynomial in `μ, ν` with power-series coefficients, read as a power
series with polynomial coefficients. -/
noncomputable def psSwap (K : Type u) [Field K] :
    Graded.Poly (PowerSeries K) →+* PowerSeries (Graded.Poly K) :=
  MvPolynomial.eval₂Hom (PowerSeries.map (MvPolynomial.C : K →+* Graded.Poly K))
    (fun i => PowerSeries.C (MvPolynomial.X i))

/-- `psSwap` followed by the inclusion of `B` into the function field. -/
noncomputable def arcHomFF (K : Type u) [Field K] :
    Graded.Poly (PowerSeries K) →+* PowerSeries (FF K) :=
  (PowerSeries.map (algebraMap (Graded.Poly K) (FF K))).comp (psSwap K)

theorem arcHomFF_C (a : PowerSeries K) :
    arcHomFF K (MvPolynomial.C a) = PowerSeries.map (kFF K) a := by
  rw [arcHomFF, RingHom.comp_apply, psSwap, MvPolynomial.eval₂Hom_C, ← RingHom.comp_apply,
    ← PowerSeries.map_comp]
  rfl

theorem arcHomFF_X (i : Fin 2) :
    arcHomFF K (MvPolynomial.X i : Graded.Poly (PowerSeries K)) =
      PowerSeries.C (algebraMap (Graded.Poly K) (FF K) (MvPolynomial.X i)) := by
  rw [arcHomFF, RingHom.comp_apply, psSwap, MvPolynomial.eval₂Hom_X', PowerSeries.map_C]

/-- The pencil of an arc, over `(FF K)⟦s⟧`. -/
noncomputable def arcPencil (Ns Ms : Matrix (Fin n) (Fin n) (PowerSeries K)) :
    Matrix (Fin n) (Fin n) (PowerSeries (FF K)) :=
  (pencil Ns Ms).map (arcHomFF K)

theorem arcPencil_apply (Ns Ms : Matrix (Fin n) (Fin n) (PowerSeries K)) (i j : Fin n) :
    arcPencil Ns Ms i j =
      PowerSeries.map (kFF K) (Ns i j) *
          PowerSeries.C (algebraMap (Graded.Poly K) (FF K) mu) +
        PowerSeries.map (kFF K) (Ms i j) *
          PowerSeries.C (algebraMap (Graded.Poly K) (FF K) nu) := by
  show arcHomFF K (pencil Ns Ms i j) = _
  rw [pencil]
  simp only [Matrix.of_apply, mu, nu, map_add, map_mul, arcHomFF_C, arcHomFF_X]

private theorem constantCoeff_map_apply (f : K →+* FF K) (a : PowerSeries K) :
    PowerSeries.constantCoeff (PowerSeries.map f a) = f (PowerSeries.constantCoeff a) := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply]

/-- The reduction of the arc pencil modulo `s` is the pencil at the base
point, over the function field. -/
theorem matC_arcPencil (Ns Ms : Matrix (Fin n) (Fin n) (PowerSeries K)) :
    matC (arcPencil Ns Ms) = pencilFF (matC Ns) (matC Ms) := by
  ext i j
  show PowerSeries.constantCoeff (arcPencil Ns Ms i j) = _
  rw [arcPencil_apply, pencilFF_apply, map_add, map_mul, map_mul,
    PowerSeries.constantCoeff_C, PowerSeries.constantCoeff_C,
    constantCoeff_map_apply, constantCoeff_map_apply]
  rfl

/-- The `s`-linear coefficient of the arc pencil is the pencil at the
velocity, over the function field. -/
theorem matD_arcPencil (Ns Ms : Matrix (Fin n) (Fin n) (PowerSeries K)) :
    matD (arcPencil Ns Ms) = pencilFF (matD Ns) (matD Ms) := by
  ext i j
  show PowerSeries.coeff 1 (arcPencil Ns Ms i j) = _
  rw [arcPencil_apply, pencilFF_apply, map_add, PowerSeries.coeff_mul_C,
    PowerSeries.coeff_mul_C, PowerSeries.coeff_map, PowerSeries.coeff_map]
  rfl

end Objects

/-! ### Kernel flatness (`lem:flag-flat`(1)) -/

section KernelFlat

variable {K : Type u} [Field K] {n : ℕ}

/-! #### Matrix arcs

`kernel_flat` and `cor:arc-torsion` are stated for an arc of *pencils*, but
nothing in their proofs is about pencils: they are statements about a single
matrix over `K⟦s⟧` whose rank profile does not jump, applied to
`arcPencil Ns Ms` over the function field.  In that generality they also give
the marking condition of `thm:h2-conditional` — the derivative of a member
that stays in its orbit closure lies in `im ad` — which is smoothness of the
nilpotent orbit, with no orbit geometry in the proof. -/

/-- The rank-constancy hypothesis along a matrix arc: the rank of the `k`-th
power at the generic point of the arc equals its rank at the base point. -/
def MatArcRankEq (X : Matrix (Fin n) (Fin n) (PowerSeries K)) (k : ℕ) : Prop :=
  ((X ^ k).map (algebraMap (PowerSeries K) (LaurentSeries K))).rank =
    ((X ^ k).map (PowerSeries.constantCoeff (R := K))).rank

/-- **Kernel flatness for a matrix arc**: along an arc of constant rank profile
every kernel vector `v` of `X₀^k` has a companion `ẇ` with
`D_k(Ẋ) v = − X₀^k ẇ`.  `Toolbox.exists_kernel_lift` is the whole content: the
kernel over the DVR is saturated, so equal generic and special ranks let a
special-fibre kernel vector be lifted. -/
theorem matArc_kernel_flat (X : Matrix (Fin n) (Fin n) (PowerSeries K)) (k : ℕ)
    (hrank : MatArcRankEq X k) (v : Fin n → K)
    (hv : (matC X ^ k) *ᵥ v = 0) :
    ∃ w : Fin n → K, Dk (matC X) (matD X) k *ᵥ v = -((matC X ^ k) *ᵥ w) := by
  have hC : (X ^ k).map (PowerSeries.constantCoeff (R := K)) = matC X ^ k := by
    show matC (X ^ k) = _
    rw [matC_pow]
  have hv' : ((X ^ k).map (PowerSeries.constantCoeff (R := K))) *ᵥ v = 0 := by
    rw [hC]; exact hv
  obtain ⟨w, hw, hwC⟩ := Height.Toolbox.exists_kernel_lift (X ^ k) hrank v hv'
  have hwC' : vecC w = v := hwC
  refine ⟨vecD w, ?_⟩
  have hD := vecD_mulVec (X ^ k) w
  rw [hw, matD_pow, matC_pow, hwC'] at hD
  have hz : vecD (0 : Fin n → PowerSeries K) = 0 := by
    funext i; simp [vecD]
  rw [hz] at hD
  exact eq_neg_of_add_eq_zero_left hD.symm

/-- **The velocity of a matrix arc of constant rank profile is a commutator with
its special fibre.**  This is the smoothness of the nilpotent orbit that the
paper invokes for the marking condition ("`N` is a smooth point of
`cl Orb_λ` with tangent space `im ad_N`"), proved from kernel flatness
(`isCommutator_of_kernelFlat`) instead. -/
theorem exists_commutator_of_matArc (X : Matrix (Fin n) (Fin n) (PowerSeries K))
    (hnil : matC X ^ n = 0) (hrank : ∀ k, MatArcRankEq X k) :
    ∃ Z, matD X = matC X * Z - Z * matC X :=
  isCommutator_of_kernelFlat _ hnil _ fun k v hv => by
    obtain ⟨w, hw⟩ := matArc_kernel_flat X k (hrank k) v hv
    exact ⟨-w, by rw [Matrix.mulVecLin_apply, Matrix.mulVec_neg]; exact hw.symm⟩


/-- **The marking condition, from an arc of the marked member.**  If the member
at the moving marked point traces an arc whose rank profile does not jump, the
velocity is *marked* at the base point.

This is the derivative of the closed condition "the fibre at the moving point
stays in `cl Orb_λ`" that `defn:marked` takes at a smooth point of the orbit
closure.  The smoothness is `exists_commutator_of_matArc`; no orbit geometry
enters, only the fact that the kernel of a power-series matrix is saturated. -/
theorem exists_markedWith_of_memberArc (Ns Ms : Matrix (Fin n) (Fin n) (PowerSeries K))
    (ts : PowerSeries K) (hnil : matC (Ns + ts • Ms) ^ n = 0)
    (hrank : ∀ k, MatArcRankEq (Ns + ts • Ms) k) :
    ∃ Z, MarkedWith (matC Ns) (matC Ms) (PowerSeries.constantCoeff ts)
      (pencil (matD Ns) (matD Ms)) (PowerSeries.coeff 1 ts) Z := by
  obtain ⟨Z, hZ⟩ := exists_commutator_of_matArc (Ns + ts • Ms) hnil hrank
  refine ⟨Z, ?_⟩
  have hC : matC (Ns + ts • Ms) = matC Ns + PowerSeries.constantCoeff ts • matC Ms := by
    rw [matC_add, matC_smul_series]
  have hD : matD (Ns + ts • Ms)
      = matD Ns + PowerSeries.constantCoeff ts • matD Ms
        + PowerSeries.coeff 1 ts • matC Ms := by
    rw [matD_add, matD_smul_series]
    abel
  rw [hC, hD] at hZ
  show matC (Qat (pencil (matD Ns) (matD Ms)) (PowerSeries.constantCoeff ts))
      + PowerSeries.coeff 1 ts • matD (Pat (matC Ns) (matC Ms) (PowerSeries.constantCoeff ts))
    = _
  rw [matC_Qat_pencil, matD_Pat]
  exact hZ
/-- What an arc of the marked incidence supplies at one marked point: arcs of
the two matrices and of the parameter, based at `(N, M, t₀)` with `(Nd, Md, ṫ)`
as velocity, whose marked member `N_s + t_s M_s` is nilpotent of constant rank
profile.  These are exactly the hypotheses of
`exists_markedWith_of_memberArc`. -/
structure MemberArc (N M : Matrix (Fin n) (Fin n) K) (t₀ : K)
    (Nd Md : Matrix (Fin n) (Fin n) K) (tdot : K) where
  /-- the arc of the first matrix -/
  Ns : Matrix (Fin n) (Fin n) (PowerSeries K)
  /-- the arc of the second matrix -/
  Ms : Matrix (Fin n) (Fin n) (PowerSeries K)
  /-- the arc of the marked parameter -/
  ts : PowerSeries K
  matC_N : matC Ns = N
  matC_M : matC Ms = M
  const_t : PowerSeries.constantCoeff ts = t₀
  matD_N : matD Ns = Nd
  matD_M : matD Ms = Md
  coeff_t : PowerSeries.coeff 1 ts = tdot
  /-- the marked member is nilpotent at the base point -/
  nilpotent : matC (Ns + ts • Ms) ^ n = 0
  /-- the rank profile of the marked member does not jump -/
  rank : ∀ k, MatArcRankEq (Ns + ts • Ms) k

/-- A member arc marks its velocity. -/
theorem MemberArc.exists_markedWith {N M : Matrix (Fin n) (Fin n) K} {t₀ : K}
    {Nd Md : Matrix (Fin n) (Fin n) K} {tdot : K} (A : MemberArc N M t₀ Nd Md tdot) :
    ∃ Z, MarkedWith N M t₀ (pencil Nd Md) tdot Z := by
  obtain ⟨Z, hZ⟩ := exists_markedWith_of_memberArc A.Ns A.Ms A.ts A.nilpotent A.rank
  exact ⟨Z, by rwa [A.matC_N, A.matC_M, A.const_t, A.matD_N, A.matD_M, A.coeff_t] at hZ⟩

/-- Above the nilpotency exponent the rank equation is trivial: both sides are
the rank of the zero matrix. -/
theorem matArcRankEq_of_nilpotent {X : Matrix (Fin n) (Fin n) (PowerSeries K)}
    (hnil : X ^ n = 0) {k : ℕ} (hk : n ≤ k) : MatArcRankEq X k := by
  have hz : X ^ k = 0 := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [pow_add, hnil, zero_mul]
  rw [MatArcRankEq, hz, Matrix.map_zero _ (map_zero _), Matrix.map_zero _ (map_zero _)]
  simp

/-- For a nilpotent member arc, constancy of the rank profile up to `n` is
constancy of the whole profile. -/
theorem matArcRankEq_of_le {X : Matrix (Fin n) (Fin n) (PowerSeries K)}
    (hnil : X ^ n = 0) (hrank : ∀ k ≤ n, MatArcRankEq X k) (k : ℕ) : MatArcRankEq X k :=
  if hk : k ≤ n then hrank k hk else matArcRankEq_of_nilpotent hnil (by omega)

/-- **A `MemberArc` from arc data**: the member nilpotent along the arc, with a
rank profile that is constant up to `n`.  Those are exactly what the geometry
supplies — nilpotence from the incidence, rank constancy from
`member_arc_rank_eq` — and everything else in the structure is definitional. -/
noncomputable def MemberArc.ofRank {Ns Ms : Matrix (Fin n) (Fin n) (PowerSeries K)}
    {ts : PowerSeries K} (hnil : (Ns + ts • Ms) ^ n = 0)
    (hrank : ∀ k ≤ n, MatArcRankEq (Ns + ts • Ms) k) :
    MemberArc (matC Ns) (matC Ms) (PowerSeries.constantCoeff ts)
      (matD Ns) (matD Ms) (PowerSeries.coeff 1 ts) where
  Ns := Ns
  Ms := Ms
  ts := ts
  matC_N := rfl
  matC_M := rfl
  const_t := rfl
  matD_N := rfl
  matD_M := rfl
  coeff_t := rfl
  nilpotent := by
    rw [← matC_pow, hnil]
    ext i j
    simp [matC]
  rank := matArcRankEq_of_le hnil hrank

/-- The rank-constancy hypothesis along an arc of pencils: the rank of the
`k`-th power of the pencil at the generic point of the arc equals its rank at
the base point.  This is what membership of `Î_{τ,d}` at both ends of the arc
provides (`arc_rank_eq`), and the only thing kernel flatness consumes. -/
def ArcRankEq (Ns Ms : Matrix (Fin n) (Fin n) (PowerSeries K)) (k : ℕ) : Prop :=
  ((arcPencil Ns Ms ^ k).map
      (algebraMap (PowerSeries (FF K)) (LaurentSeries (FF K)))).rank =
    ((arcPencil Ns Ms ^ k).map (PowerSeries.constantCoeff (R := FF K))).rank

/-- **Kernel flatness**, `lem:flag-flat`(1), over the function field: along an
arc of pencils of constant rank profile, every kernel vector `v` of `P^k` has
a companion `v̇` with `D_k(Ṗ) v = − P^k v̇`. -/
theorem kernel_flat (Ns Ms : Matrix (Fin n) (Fin n) (PowerSeries K)) (k : ℕ)
    (hrank : ArcRankEq Ns Ms k) (v : Fin n → FF K)
    (hv : (pencilFF (matC Ns) (matC Ms) ^ k) *ᵥ v = 0) :
    ∃ w : Fin n → FF K,
      Dk (pencilFF (matC Ns) (matC Ms)) (pencilFF (matD Ns) (matD Ms)) k *ᵥ v
        = -((pencilFF (matC Ns) (matC Ms) ^ k) *ᵥ w) := by
  have h := matArc_kernel_flat (K := FF K) (arcPencil Ns Ms) k hrank v
    (by rw [matC_arcPencil]; exact hv)
  rwa [matC_arcPencil, matD_arcPencil] at h
/-- **`cor:arc-torsion`**: the velocity of an arc of pencils is a commutator
with the pencil over the function field `K(ℙ¹)`.  `hnil` is nilpotence of the
generic member, `P^n = 0` over `K[μ,ν]`. -/
theorem exists_commutator_fractionRing (Ns Ms : Matrix (Fin n) (Fin n) (PowerSeries K))
    (hnil : pencil (matC Ns) (matC Ms) ^ n = 0)
    (hrank : ∀ k, ArcRankEq Ns Ms k) :
    ∃ A : Matrix (Fin n) (Fin n) (FF K),
      pencilFF (matD Ns) (matD Ms)
        = pencilFF (matC Ns) (matC Ms) * A - A * pencilFF (matC Ns) (matC Ms) := by
  refine isCommutator_of_kernelFlat _ ?_ _ ?_
  · have hpow : pencilFF (matC Ns) (matC Ms) ^ n
        = (pencil (matC Ns) (matC Ms) ^ n).map
            (algebraMap (Graded.Poly K) (FF K)) := by
      show ((algebraMap (Graded.Poly K) (FF K)).mapMatrix
        (pencil (matC Ns) (matC Ms))) ^ n = _
      rw [← map_pow]
      rfl
    rw [hpow, hnil]
    ext i j
    simp
  · intro k v hv
    obtain ⟨w, hw⟩ := kernel_flat Ns Ms k (hrank k) v hv
    exact ⟨-w, by rw [Matrix.mulVecLin_apply, Matrix.mulVec_neg]; exact hw.symm⟩

end KernelFlat

/-! ### The free part of a realised direction vanishes -/

section FreeClass

variable {K : Type u} [Field K] {n : ℕ}

/-- If a direction is a commutator with `P` over the *Laurent* series — the
denominators are allowed to be poles — then its free coordinates, the ones
where the invariant factor vanishes, are zero. -/
theorem freeClass_eq_zero_of_laurent {P : Matrix (Fin n) (Fin n) (PowerSeries K)}
    (D : LocalData K n P) (Q : Matrix (Fin n) (Fin n) (PowerSeries K))
    (A : Matrix (Fin n) (Fin n) (LaurentSeries K))
    (h : Q.map (algebraMap (PowerSeries K) (LaurentSeries K)) =
      P.map (algebraMap (PowerSeries K) (LaurentSeries K)) * A -
        A * P.map (algebraMap (PowerSeries K) (LaurentSeries K))) :
    D.freeClass Q = 0 := by
  classical
  set ι : PowerSeries K →+* LaurentSeries K := algebraMap (PowerSeries K) (LaurentSeries K)
    with hιdef
  have hinj : Function.Injective ι := IsFractionRing.injective (PowerSeries K) (LaurentSeries K)
  have hdiagL : (D.U.map ι) * adMat (P.map ι) * (D.V.map ι)
      = Matrix.diagonal (fun i => ι (D.g i)) := by
    have hmap := congrArg (fun X => ι.mapMatrix X) D.hdiag_V
    simp only [map_mul, RingHom.mapMatrix_apply] at hmap
    rw [← adMat_map] at hmap
    rw [hmap, Matrix.diagonal_map (map_zero ι)]
  have hVunit : IsUnit (D.V.map ι).det := by
    rw [show (D.V.map ι).det = ι D.V.det from (RingHom.map_det ι D.V).symm]
    exact D.hV.map ι
  set w : Fin (n * n) → LaurentSeries K := vecMat A with hwdef
  set w' : Fin (n * n) → LaurentSeries K := (D.V.map ι)⁻¹ *ᵥ w with hw'def
  have hVw : (D.V.map ι) *ᵥ w' = w := by
    rw [hw'def, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hVunit, Matrix.one_mulVec]
  have hkey : ∀ i, ι (D.coords Q i) = (Matrix.diagonal (fun i => ι (D.g i)) *ᵥ w') i := by
    intro i
    have h1 : ι (D.coords Q i) = ((D.U.map ι) *ᵥ (fun j => ι (vecMat Q j))) i :=
      RingHom.map_mulVec ι D.U (vecMat Q) i
    have h3 : (fun j => ι (vecMat Q j)) = adMat (P.map ι) *ᵥ w := by
      rw [hwdef, adMat_mulVec, ← h]
      rfl
    rw [h1, h3, ← hVw, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hdiagL]
  funext i
  rw [Pi.zero_apply, LocalData.freeClass_apply]
  apply hinj
  rw [map_zero, hkey i.val, Matrix.mulVec_diagonal, i.2, map_zero, zero_mul]

/-- Denominator clearing: a commutator relation over the function field is a
commutator relation over `B = K[μ,ν]` after multiplying by a nonzero scalar. -/
theorem exists_integral_commutator (N M Nd Md : Matrix (Fin n) (Fin n) K)
    (hA : ∃ A : Matrix (Fin n) (Fin n) (FF K),
      pencilFF Nd Md = pencilFF N M * A - A * pencilFF N M) :
    ∃ (c : Graded.Poly K) (A' : Matrix (Fin n) (Fin n) (Graded.Poly K)), c ≠ 0 ∧
      c • pencil Nd Md
        = pencil N M * A' - A' * pencil N M := by
  classical
  obtain ⟨A, hA⟩ := hA
  set alg := algebraMap (Graded.Poly K) (FF K) with halgdef
  have halg : Function.Injective alg := IsFractionRing.injective (Graded.Poly K) (FF K)
  obtain ⟨dd, hdd⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors (Graded.Poly K)) (fun ij : Fin n × Fin n => A ij.1 ij.2)
  choose B hB using fun ij => RingHom.mem_rangeS.mp (hdd ij)
  set A' : Matrix (Fin n) (Fin n) (Graded.Poly K) := Matrix.of fun i j => B (i, j) with hA'def
  have hA'FF : A'.map alg = alg (dd : Graded.Poly K) • A := by
    ext i j
    show alg (B (i, j)) = _
    rw [hB (i, j)]
    simp [Algebra.smul_def, halgdef]
  refine ⟨(dd : Graded.Poly K), A', nonZeroDivisors.coe_ne_zero dd, ?_⟩
  have hΦinj : ∀ X Y : Matrix (Fin n) (Fin n) (Graded.Poly K),
      X.map alg = Y.map alg → X = Y := by
    intro X Y hXY
    exact Matrix.ext fun i j => halg (congrFun (congrFun hXY i) j)
  refine hΦinj _ _ ?_
  have hLHS : ((dd : Graded.Poly K) • pencil Nd Md).map alg
      = alg (dd : Graded.Poly K) • pencilFF Nd Md := by
    ext i j
    show alg ((dd : Graded.Poly K) * pencil Nd Md i j) = _
    rw [map_mul]
    rfl
  have hRHS : (pencil N M * A' - A' * pencil N M).map alg
      = pencilFF N M * A'.map alg - A'.map alg * pencilFF N M := by
    have hsub := map_sub (alg.mapMatrix (m := Fin n))
      (pencil N M * A') (A' * pencil N M)
    simp only [RingHom.mapMatrix_apply, map_mul] at hsub
    exact hsub
  rw [hLHS, hRHS, hA'FF, Matrix.mul_smul, Matrix.smul_mul, ← smul_sub, ← hA]

/-- A nonzero polynomial has a nonzero homogeneous component. -/
theorem exists_Bproj_ne_zero {c : Graded.Poly K} (hc : c ≠ 0) :
    ∃ e : ℤ, Bproj e c ≠ 0 := by
  classical
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  refine hc ?_
  have hs := sum_Bproj (0 : ℤ) c
    ((Finset.range (c.totalDegree + 1)).image (fun d : ℕ => (0 : ℤ) + (d : ℤ)))
    (fun d hd => Finset.mem_image.2 ⟨d, Finset.mem_range.2 (by omega), rfl⟩)
  rw [← hs]
  exact Finset.sum_eq_zero fun e _ => hcon (e - 0)

/-- The denominator can be taken homogeneous: the homogeneous components of a
commutator relation are again commutator relations, since `P` and `Ṗ` are
homogeneous of degree one. -/
theorem exists_homogeneous_commutator (N M Nd Md : Matrix (Fin n) (Fin n) K)
    (hA : ∃ A : Matrix (Fin n) (Fin n) (FF K),
      pencilFF Nd Md = pencilFF N M * A - A * pencilFF N M) :
    ∃ (e : ℤ) (c : Graded.Poly K) (A' : Matrix (Fin n) (Fin n) (Graded.Poly K)),
      c ∈ Bpiece K e ∧ c ≠ 0 ∧
        c • pencil Nd Md
          = pencil N M * A' - A' * pencil N M := by
  obtain ⟨dd, A', hdd, heq⟩ := exists_integral_commutator N M Nd Md hA
  obtain ⟨e, he⟩ := exists_Bproj_ne_zero hdd
  refine ⟨e, Bproj e dd, A'.map (fun x => Bproj e x), Bproj_mem e dd, he, ?_⟩
  ext i j
  have hij := congrArg (Bproj (e + 1)) (congrFun (congrFun heq i) j)
  have hL : Bproj (e + 1) ((dd • pencil Nd Md) i j)
      = (Bproj e dd • pencil Nd Md) i j := by
    show Bproj (e + 1) (dd * pencil Nd Md i j) = _
    rw [Bproj_smul_of_mem (d := e) dd (pencil_mem_Bpiece Nd Md i j)]
    rfl
  have hR : Bproj (e + 1)
        ((pencil N M * A' - A' * pencil N M) i j)
      = (pencil N M * A'.map (fun x => Bproj e x) -
          A'.map (fun x => Bproj e x) * pencil N M) i j := by
    rw [Matrix.sub_apply, Matrix.sub_apply, map_sub, Matrix.mul_apply, Matrix.mul_apply,
      Matrix.mul_apply, Matrix.mul_apply, map_sum, map_sum]
    congr 1
    · refine Finset.sum_congr rfl fun l _ => ?_
      rw [mul_comm (pencil N M i l) (A' l j),
        Bproj_smul_of_mem (d := e) (A' l j) (pencil_mem_Bpiece N M i l), mul_comm]
      rfl
    · refine Finset.sum_congr rfl fun l _ => ?_
      rw [Bproj_smul_of_mem (d := e) (A' i l) (pencil_mem_Bpiece N M l j)]
      rfl
  rw [← hL, ← hR, hij]

/-- **`cor:arc-torsion`, the commutator half.**  A direction that is a
commutator with the pencil over the function field is a commutator with the
localised pencil over the Laurent series of any chart that does not kill
nonzero homogeneous polynomials: clearing the denominator is
`exists_homogeneous_commutator`, and the chart hypothesis says the
(homogeneous) denominator survives, hence may be inverted in `K⸨u⸩`. -/
theorem exists_laurent_commutator_of_chart (N M Nd Md : Matrix (Fin n) (Fin n) K)
    (χ : Graded.Chart K)
    (hA : ∃ A : Matrix (Fin n) (Fin n) (FF K),
      pencilFF Nd Md = pencilFF N M * A - A * pencilFF N M) :
    ∃ A : Matrix (Fin n) (Fin n) (LaurentSeries K),
      ((pencil Nd Md).map χ.hom).map (algebraMap (PowerSeries K) (LaurentSeries K))
        = ((pencil N M).map χ.hom).map (algebraMap (PowerSeries K) (LaurentSeries K))
              * A
            - A * ((pencil N M).map χ.hom).map
                (algebraMap (PowerSeries K) (LaurentSeries K)) := by
  obtain ⟨e, c, A', hce, hc0, heq⟩ := exists_homogeneous_commutator N M Nd Md hA
  set ι : PowerSeries K →+* LaurentSeries K := algebraMap (PowerSeries K) (LaurentSeries K)
    with hιdef
  set ρ : Graded.Poly K →+* LaurentSeries K := ι.comp χ.hom with hρdef
  have hγ : ι (χ.hom c) ≠ 0 := by
    intro hz
    exact χ.ne_zero hce hc0
      (IsFractionRing.injective (PowerSeries K) (LaurentSeries K) (by rw [hz, map_zero]))
  have hρc : ρ c = ι (χ.hom c) := rfl
  have hmap : (c • pencil Nd Md).map ρ
      = (pencil N M * A' - A' * pencil N M).map ρ := by
    rw [heq]
  have hLHS : (c • pencil Nd Md).map ρ
      = ρ c • (pencil Nd Md).map ρ := by
    refine Matrix.ext fun i j => ?_
    show ρ (c * pencil Nd Md i j) = _
    rw [map_mul]
    rfl
  have hRHS : (pencil N M * A' - A' * pencil N M).map ρ
      = (pencil N M).map ρ * A'.map ρ -
        A'.map ρ * (pencil N M).map ρ := by
    have hsub := map_sub (ρ.mapMatrix (m := Fin n))
      (pencil N M * A') (A' * pencil N M)
    simp only [RingHom.mapMatrix_apply, map_mul] at hsub
    exact hsub
  rw [hLHS, hRHS] at hmap
  refine ⟨(ι (χ.hom c))⁻¹ • A'.map ρ, ?_⟩
  have hmm : ∀ X : Matrix (Fin n) (Fin n) (Graded.Poly K), (X.map χ.hom).map ι = X.map ρ :=
    fun X => Matrix.ext fun i j => rfl
  rw [hmm, hmm, Matrix.mul_smul, Matrix.smul_mul, ← smul_sub, ← hmap, hρc, smul_smul,
    inv_mul_cancel₀ hγ, one_smul]

/-- **Torsion classes** (`cor:arc-torsion`, local form): a direction that is a
commutator with the pencil over the function field has vanishing free class in
every chart that does not kill nonzero homogeneous polynomials. -/
theorem freeClass_eq_zero_of_chart (N M Nd Md : Matrix (Fin n) (Fin n) K)
    (χ : Graded.Chart K)
    (D : LocalData K n ((pencil N M).map χ.hom))
    (hA : ∃ A : Matrix (Fin n) (Fin n) (FF K),
      pencilFF Nd Md = pencilFF N M * A - A * pencilFF N M) :
    D.freeClass ((pencil Nd Md).map χ.hom) = 0 := by
  obtain ⟨A, hAeq⟩ := exists_laurent_commutator_of_chart N M Nd Md χ hA
  exact freeClass_eq_zero_of_laurent D _ A hAeq

/-- **`cor:arc-torsion`** at a finite point of `ℙ¹`: the free part of the class
of a realised direction vanishes. -/
theorem freeClass_eq_zero (N M Nd Md : Matrix (Fin n) (Fin n) K) (t₀ : K)
    (hA : ∃ A : Matrix (Fin n) (Fin n) (FF K),
      pencilFF Nd Md = pencilFF N M * A - A * pencilFF N M) :
    (txData N M t₀).freeClass (Qat (pencil Nd Md) t₀) = 0 :=
  freeClass_eq_zero_of_chart N M Nd Md (Graded.Chart.atPoint t₀) (txData N M t₀) hA

/-- **`cor:arc-torsion`** at the point at infinity. -/
theorem freeClass_eq_zero_atInf (N M Nd Md : Matrix (Fin n) (Fin n) K)
    (hA : ∃ A : Matrix (Fin n) (Fin n) (FF K),
      pencilFF Nd Md = pencilFF N M * A - A * pencilFF N M) :
    (localData (PatInf N M)).freeClass ((pencil Nd Md).map atInf) = 0 :=
  freeClass_eq_zero_of_chart N M Nd Md (Graded.Chart.atInf K) (localData (PatInf N M)) hA

end FreeClass

/-! ### Levels above the nilpotency degree, and the packaged corollary -/

section Nilpotent

variable {K : Type u} [Field K] {n : ℕ}

theorem arcPencil_pow (Ns Ms : Matrix (Fin n) (Fin n) (PowerSeries K)) (k : ℕ) :
    arcPencil Ns Ms ^ k = ((pencil Ns Ms) ^ k).map (arcHomFF K) := by
  show ((arcHomFF K).mapMatrix (pencil Ns Ms)) ^ k = _
  rw [← map_pow]
  rfl

/-- Above the nilpotency degree of the arc pencil both ranks vanish, so the
rank hypothesis is automatic. -/
theorem arcRankEq_of_nilpotent {Ns Ms : Matrix (Fin n) (Fin n) (PowerSeries K)}
    (hnil : (pencil Ns Ms) ^ n = 0) {k : ℕ} (hk : n ≤ k) : ArcRankEq Ns Ms k := by
  have hzero : arcPencil Ns Ms ^ k = 0 := by
    obtain ⟨c, rfl⟩ : ∃ c, k = n + c := ⟨k - n, by omega⟩
    rw [arcPencil_pow, pow_add, hnil, zero_mul]
    ext i j
    simp
  rw [ArcRankEq, hzero, Matrix.map_zero _ (map_zero _), Matrix.map_zero _ (map_zero _),
    Matrix.rank_zero, Matrix.rank_zero]

/-- Nilpotence of the arc pencil specialises to the base point. -/
theorem pencil_pow_matC_eq_zero {Ns Ms : Matrix (Fin n) (Fin n) (PowerSeries K)}
    (hnil : (pencil Ns Ms) ^ n = 0) :
    pencil (matC Ns) (matC Ms) ^ n = 0 := by
  set ψ : Graded.Poly (PowerSeries K) →+* Graded.Poly K :=
    MvPolynomial.map (PowerSeries.constantCoeff (R := K)) with hψdef
  have hbase : (pencil Ns Ms).map ψ = pencil (matC Ns) (matC Ms) := by
    refine Matrix.ext fun i j => ?_
    show ψ (pencil Ns Ms i j) = _
    rw [pencil]
    simp only [Matrix.of_apply, mu, nu, map_add, map_mul, hψdef, MvPolynomial.map_C,
      MvPolynomial.map_X]
    rfl
  have hpow : ((pencil Ns Ms) ^ n).map ψ = ((pencil Ns Ms).map ψ) ^ n := by
    show ψ.mapMatrix ((pencil Ns Ms) ^ n) = (ψ.mapMatrix (pencil Ns Ms)) ^ n
    rw [map_pow]
  rw [← hbase, ← hpow, hnil, Matrix.map_zero _ (map_zero _)]

/-- **`cor:arc-torsion`**, packaged: nilpotence of the arc pencil plus rank
constancy up to level `n` gives the commutator over the function field. -/
theorem exists_commutator_of_arc (Ns Ms : Matrix (Fin n) (Fin n) (PowerSeries K))
    (hnil : (pencil Ns Ms) ^ n = 0) (hrank : ∀ k ≤ n, ArcRankEq Ns Ms k) :
    ∃ A : Matrix (Fin n) (Fin n) (FF K),
      pencilFF (matD Ns) (matD Ms)
        = pencilFF (matC Ns) (matC Ms) * A - A * pencilFF (matC Ns) (matC Ms) :=
  exists_commutator_fractionRing Ns Ms (pencil_pow_matC_eq_zero hnil)
    (fun k => if hk : k ≤ n then hrank k hk else arcRankEq_of_nilpotent hnil (by omega))

end Nilpotent

/-! ### Genericity: the rank profile is constant along arcs -/

section Genericity

open Height.Pencil

variable {K : Type u} [Field K] {n : ℕ}

/-- The generic pencil `μ N + ν M` over the coordinate ring of pairs. -/
noncomputable def genPencil (K : Type u) [Field K] (n : ℕ) :
    Matrix (Fin n) (Fin n) (Graded.Poly (MvPolynomial (PairIndex (Fin n)) K)) :=
  pencil (Matrix.of fun i j => MvPolynomial.X (Sum.inl (i, j)))
    (Matrix.of fun i j => MvPolynomial.X (Sum.inr (i, j)))

/-- Evaluation of the coordinates at a pair of matrices. -/
noncomputable def pairEval (N M : Matrix (Fin n) (Fin n) K) :
    MvPolynomial (PairIndex (Fin n)) K →+* K :=
  MvPolynomial.eval (Sum.elim (fun ij : Fin n × Fin n => N ij.1 ij.2)
    (fun ij : Fin n × Fin n => M ij.1 ij.2))

/-- Evaluation of the coordinates along an arc of pencils. -/
noncomputable def pairArcHom (Ns Ms : Matrix (Fin n) (Fin n) (PowerSeries K)) :
    MvPolynomial (PairIndex (Fin n)) K →+* PowerSeries K :=
  MvPolynomial.eval₂Hom (algebraMap K (PowerSeries K))
    (Sum.elim (fun ij : Fin n × Fin n => Ns ij.1 ij.2)
      (fun ij : Fin n × Fin n => Ms ij.1 ij.2))

theorem constantCoeff_comp_pairArcHom (Ns Ms : Matrix (Fin n) (Fin n) (PowerSeries K)) :
    (PowerSeries.constantCoeff (R := K)).comp (pairArcHom Ns Ms)
      = pairEval (matC Ns) (matC Ms) := by
  refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
  · simp [pairArcHom, pairEval, PowerSeries.algebraMap_eq]
  · rcases i with ij | ij <;> simp [pairArcHom, pairEval, matC]

theorem genPencil_map_pairEval (N M : Matrix (Fin n) (Fin n) K) :
    (genPencil K n).map (MvPolynomial.map (pairEval N M)) = pencil N M := by
  refine Matrix.ext fun i j => ?_
  show MvPolynomial.map (pairEval N M) (genPencil K n i j) = _
  rw [genPencil, pencil]
  simp only [Matrix.of_apply, mu, nu, map_add, map_mul, MvPolynomial.map_C, MvPolynomial.map_X, pairEval, MvPolynomial.eval_X, Sum.elim_inl, Sum.elim_inr]
  rfl

theorem genPencil_map_pairArcHom (Ns Ms : Matrix (Fin n) (Fin n) (PowerSeries K)) :
    (genPencil K n).map (MvPolynomial.map (pairArcHom Ns Ms)) = pencil Ns Ms := by
  refine Matrix.ext fun i j => ?_
  show MvPolynomial.map (pairArcHom Ns Ms) (genPencil K n i j) = _
  rw [genPencil, pencil, pencil]
  simp only [Matrix.of_apply, mu, nu, map_add, map_mul, MvPolynomial.map_C, MvPolynomial.map_X, pairArcHom, MvPolynomial.eval₂Hom_X', Sum.elim_inl, Sum.elim_inr]

/-- The ideal of polynomials in `μ, ν` all of whose coefficients lie in `I`. -/
noncomputable def coeffIdeal (I : Ideal (MvPolynomial (PairIndex (Fin n)) K)) :
    Ideal (Graded.Poly (MvPolynomial (PairIndex (Fin n)) K)) :=
  RingHom.ker (MvPolynomial.map (Ideal.Quotient.mk I) :
    Graded.Poly (MvPolynomial (PairIndex (Fin n)) K) →+*
      Graded.Poly (MvPolynomial (PairIndex (Fin n)) K ⧸ I))

theorem mem_coeffIdeal {I : Ideal (MvPolynomial (PairIndex (Fin n)) K)}
    {F : Graded.Poly (MvPolynomial (PairIndex (Fin n)) K)} :
    F ∈ coeffIdeal I ↔ ∀ d, F.coeff d ∈ I := by
  rw [coeffIdeal, RingHom.mem_ker]
  constructor
  · intro h d
    have hd := congrArg (fun G : Graded.Poly (MvPolynomial (PairIndex (Fin n)) K ⧸ I) => G.coeff d) h
    simp only [MvPolynomial.coeff_map] at hd
    refine Ideal.Quotient.eq_zero_iff_mem.mp ?_
    rw [hd]
    rfl
  · intro h
    refine MvPolynomial.ext _ _ fun d => ?_
    rw [MvPolynomial.coeff_map]
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (h d)]
    rfl

theorem coeffIdeal_isPrime (I : Ideal (MvPolynomial (PairIndex (Fin n)) K)) [I.IsPrime] :
    (coeffIdeal I).IsPrime := by
  have : IsDomain (MvPolynomial (PairIndex (Fin n)) K ⧸ I) := Ideal.Quotient.isDomain I
  exact Ideal.comap_isPrime _ ⊥

/-- A polynomial with a coefficient outside `I` is not killed by evaluation at
a point where that coefficient does not vanish. -/
private theorem map_eq_zero_of_coeff_mem {S : Type*} [CommRing S]
    (f : MvPolynomial (PairIndex (Fin n)) K →+* S)
    {F : Graded.Poly (MvPolynomial (PairIndex (Fin n)) K)} (h : ∀ d, f (F.coeff d) = 0) :
    MvPolynomial.map f F = 0 := by
  refine MvPolynomial.ext _ _ fun d => ?_
  simp [MvPolynomial.coeff_map, h d]

/-- The reduction modulo `s` of `arcHomFF`. -/
theorem constantCoeff_arcHomFF (F : Graded.Poly (PowerSeries K)) :
    PowerSeries.constantCoeff (arcHomFF K F)
      = algebraMap (Graded.Poly K) (FF K)
          (MvPolynomial.map (PowerSeries.constantCoeff (R := K)) F) := by
  have h : (PowerSeries.constantCoeff (R := FF K)).comp (arcHomFF K)
      = (algebraMap (Graded.Poly K) (FF K)).comp
        (MvPolynomial.map (PowerSeries.constantCoeff (R := K))) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
    · rw [RingHom.comp_apply, arcHomFF_C, constantCoeff_map_apply, RingHom.comp_apply,
        MvPolynomial.map_C]
      rfl
    · rw [RingHom.comp_apply, arcHomFF_X, PowerSeries.constantCoeff_C, RingHom.comp_apply,
        MvPolynomial.map_X]
  exact congrArg (fun ψ => ψ F) h

/-- **Genericity along arcs.**  For an irreducible subvariety `V(I)` of the
space of pairs there is a `g ∉ I` such that at every point of `V(I) ∖ V(g)`
every arc of pencils in `V(I)` has the same function-field rank profile, up to
level `m`, as its base point.  This is the input `ArcRankEq` of kernel
flatness. -/
theorem arc_rank_eq (m : ℕ) (I : Ideal (MvPolynomial (PairIndex (Fin n)) K)) [I.IsPrime] :
    ∃ g ∉ I, ∀ N M : Matrix (Fin n) (Fin n) K,
      (∀ f ∈ I, pairEval N M f = 0) → pairEval N M g ≠ 0 →
      ∀ Ns Ms : Matrix (Fin n) (Fin n) (PowerSeries K),
        (∀ f ∈ I, pairArcHom Ns Ms f = 0) → matC Ns = N → matC Ms = M →
        ∀ k ≤ m, ArcRankEq Ns Ms k := by
  classical
  have hP : (coeffIdeal I).IsPrime := coeffIdeal_isPrime I
  choose r δ hδ using fun k : ℕ =>
    exists_genericRank (coeffIdeal I) ((genPencil K n) ^ k)
  have hcoeff : ∀ k : ℕ, ∃ d, (δ k).coeff d ∉ I := by
    intro k
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    exact (hδ k).1 (mem_coeffIdeal.mpr hcon)
  choose dd hdd using hcoeff
  refine ⟨∏ k ∈ Finset.range (m + 1), (δ k).coeff (dd k), ?_, ?_⟩
  · intro hmem
    obtain ⟨k, -, hk⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    exact hdd k hk
  intro N M hNM hgz Ns Ms harc hbN hbM k hk
  have hkr : k ∈ Finset.range (m + 1) := Finset.mem_range.2 (by omega)
  have hfac : pairEval N M ((δ k).coeff (dd k)) ≠ 0 := by
    rw [map_prod] at hgz
    exact Finset.prod_ne_zero_iff.mp hgz k hkr
  set φz : Graded.Poly (MvPolynomial (PairIndex (Fin n)) K) →+* FF K :=
    (algebraMap (Graded.Poly K) (FF K)).comp (MvPolynomial.map (pairEval N M)) with hφz
  set φa : Graded.Poly (MvPolynomial (PairIndex (Fin n)) K) →+* LaurentSeries (FF K) :=
    (algebraMap (PowerSeries (FF K)) (LaurentSeries (FF K))).comp
      ((arcHomFF K).comp (MvPolynomial.map (pairArcHom Ns Ms))) with hφa
  have halgFF : Function.Injective (algebraMap (Graded.Poly K) (FF K)) :=
    IsFractionRing.injective (Graded.Poly K) (FF K)
  have halgL : Function.Injective (algebraMap (PowerSeries (FF K)) (LaurentSeries (FF K))) :=
    IsFractionRing.injective (PowerSeries (FF K)) (LaurentSeries (FF K))
  -- the two homomorphisms kill the ideal
  have hφzP : ∀ f ∈ coeffIdeal I, φz f = 0 := by
    intro f hf
    rw [hφz, RingHom.comp_apply,
      map_eq_zero_of_coeff_mem (pairEval N M) (fun d => hNM _ (mem_coeffIdeal.mp hf d)),
      map_zero]
  have hφaP : ∀ f ∈ coeffIdeal I, φa f = 0 := by
    intro f hf
    rw [hφa, RingHom.comp_apply, RingHom.comp_apply,
      map_eq_zero_of_coeff_mem (pairArcHom Ns Ms) (fun d => harc _ (mem_coeffIdeal.mp hf d)),
      map_zero, map_zero]
  -- neither kills the witnessing minor
  have hzne : MvPolynomial.map (pairEval N M) (δ k) ≠ 0 := by
    intro hz
    refine hfac ?_
    have hd := congrArg (fun G : Graded.Poly K => G.coeff (dd k)) hz
    simpa [MvPolynomial.coeff_map] using hd
  have hφzδ : φz (δ k) ≠ 0 := by
    rw [hφz, RingHom.comp_apply]
    intro hz
    exact hzne (halgFF (by rw [hz, map_zero]))
  have hφaδ : φa (δ k) ≠ 0 := by
    rw [hφa, RingHom.comp_apply, RingHom.comp_apply]
    intro hz
    have hps : arcHomFF K (MvPolynomial.map (pairArcHom Ns Ms) (δ k)) = 0 :=
      halgL (by rw [hz, map_zero])
    refine hzne ?_
    have hcc := constantCoeff_arcHomFF (MvPolynomial.map (pairArcHom Ns Ms) (δ k))
    rw [hps, map_zero] at hcc
    have hmm : MvPolynomial.map (PowerSeries.constantCoeff (R := K))
        (MvPolynomial.map (pairArcHom Ns Ms) (δ k))
        = MvPolynomial.map (pairEval N M) (δ k) := by
      rw [MvPolynomial.map_map, constantCoeff_comp_pairArcHom, hbN, hbM]
    rw [hmm] at hcc
    exact halgFF (by rw [← hcc, map_zero])
  -- the two ranks
  have hrz := (hδ k).2 (FF K) φz hφzP hφzδ
  have hra := (hδ k).2 (LaurentSeries (FF K)) φa hφaP hφaδ
  -- identify the mapped matrices
  have hpowz : ((genPencil K n) ^ k).map φz = (pencilFF N M) ^ k := by
    have hb : (genPencil K n).map φz = pencilFF N M := by
      have hcomp : (genPencil K n).map φz
          = ((genPencil K n).map (MvPolynomial.map (pairEval N M))).map
              (algebraMap (Graded.Poly K) (FF K)) := by
        rw [Matrix.map_map]
        rfl
      rw [hcomp, genPencil_map_pairEval]
      rfl
    rw [← hb]
    show φz.mapMatrix ((genPencil K n) ^ k) = (φz.mapMatrix (genPencil K n)) ^ k
    rw [map_pow]
  have hpowa : ((genPencil K n) ^ k).map φa
      = (arcPencil Ns Ms ^ k).map
          (algebraMap (PowerSeries (FF K)) (LaurentSeries (FF K))) := by
    have hb : (genPencil K n).map φa = (arcPencil Ns Ms).map
        (algebraMap (PowerSeries (FF K)) (LaurentSeries (FF K))) := by
      have hcomp : (genPencil K n).map φa
          = (((genPencil K n).map (MvPolynomial.map (pairArcHom Ns Ms))).map
              (arcHomFF K)).map (algebraMap (PowerSeries (FF K)) (LaurentSeries (FF K))) := by
        rw [Matrix.map_map, Matrix.map_map]
        rfl
      rw [hcomp, genPencil_map_pairArcHom]
      rfl
    have h1 : ((genPencil K n) ^ k).map φa = ((genPencil K n).map φa) ^ k := by
      show φa.mapMatrix ((genPencil K n) ^ k) = (φa.mapMatrix (genPencil K n)) ^ k
      rw [map_pow]
    have h2 : (arcPencil Ns Ms ^ k).map
        (algebraMap (PowerSeries (FF K)) (LaurentSeries (FF K)))
        = ((arcPencil Ns Ms).map
            (algebraMap (PowerSeries (FF K)) (LaurentSeries (FF K)))) ^ k := by
      show (algebraMap (PowerSeries (FF K)) (LaurentSeries (FF K))).mapMatrix
        (arcPencil Ns Ms ^ k) = _
      rw [map_pow]
      rfl
    rw [h1, h2, hb]
  have hC : (arcPencil Ns Ms ^ k).map (PowerSeries.constantCoeff (R := FF K))
      = (pencilFF N M) ^ k := by
    show matC (arcPencil Ns Ms ^ k) = _
    rw [matC_pow, matC_arcPencil, hbN, hbM]
  rw [ArcRankEq, hC, ← hpowz, ← hpowa, hrz, hra]

/-! #### The member at a marked parameter

`arc_rank_eq` says the rank profile of the *pencil* does not jump along an arc
of a component.  `member_arc_rank_eq` is the same statement for the *member* at
one of the two marked parameters, and it is the one hypothesis of
`MemberArc` — hence of the marking condition of `thm:h2-conditional` — that the
geometry has to supply.  Both are `Orbital.exists_genericRank` applied to a
universal matrix and read through two homomorphisms, one at the base point and
one at the generic point of the arc; the member version is the simpler of the
two, its universal matrix living over the marked coordinate ring itself rather
than over a graded ring above it. -/

/-- Evaluation of the marked coordinates at a point `(N, M, t)`. -/
noncomputable def markedEval (N M : Matrix (Fin n) (Fin n) K) (tt : Fin 2 → K) :
    MvPolynomial (MarkedIndex (Fin n)) K →+* K :=
  MvPolynomial.eval (Sum.elim
    (Sum.elim (fun ij : Fin n × Fin n => N ij.1 ij.2)
      (fun ij : Fin n × Fin n => M ij.1 ij.2)) tt)

/-- Evaluation of the marked coordinates along an arc. -/
noncomputable def markedArcHom (Ns Ms : Matrix (Fin n) (Fin n) (PowerSeries K))
    (tts : Fin 2 → PowerSeries K) :
    MvPolynomial (MarkedIndex (Fin n)) K →+* PowerSeries K :=
  MvPolynomial.eval₂Hom (algebraMap K (PowerSeries K))
    (Sum.elim
      (Sum.elim (fun ij : Fin n × Fin n => Ns ij.1 ij.2)
        (fun ij : Fin n × Fin n => Ms ij.1 ij.2)) tts)

@[simp] theorem markedEval_X (N M : Matrix (Fin n) (Fin n) K) (tt : Fin 2 → K)
    (x : MarkedIndex (Fin n)) :
    markedEval N M tt (MvPolynomial.X x)
      = Sum.elim (Sum.elim (fun ij : Fin n × Fin n => N ij.1 ij.2)
          (fun ij : Fin n × Fin n => M ij.1 ij.2)) tt x := by
  simp [markedEval]

@[simp] theorem markedArcHom_X (Ns Ms : Matrix (Fin n) (Fin n) (PowerSeries K))
    (tts : Fin 2 → PowerSeries K) (x : MarkedIndex (Fin n)) :
    markedArcHom Ns Ms tts (MvPolynomial.X x)
      = Sum.elim (Sum.elim (fun ij : Fin n × Fin n => Ns ij.1 ij.2)
          (fun ij : Fin n × Fin n => Ms ij.1 ij.2)) tts x := by
  simp [markedArcHom]

/-- The universal member at the `i`-th marked parameter, `N + t_i M`, over the
marked coordinate ring.  `Chain/PencilPoly.lean` reads it at a point
(`aeval_genMember`) to cut out the orbit-closure conditions of the marked
locus. -/
noncomputable def genMember (K : Type u) [Field K] (n : ℕ) (i : Fin 2) :
    Matrix (Fin n) (Fin n) (MvPolynomial (MarkedIndex (Fin n)) K) :=
  Matrix.of fun a b => MvPolynomial.X (Sum.inl (Sum.inl (a, b)))
    + MvPolynomial.X (Sum.inr i) * MvPolynomial.X (Sum.inl (Sum.inr (a, b)))

@[simp] theorem map_genMember_markedEval (N M : Matrix (Fin n) (Fin n) K) (tt : Fin 2 → K)
    (i : Fin 2) :
    (genMember K n i).map (markedEval N M tt) = N + tt i • M := by
  ext a b
  simp [genMember, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]

@[simp] theorem map_genMember_markedArcHom (Ns Ms : Matrix (Fin n) (Fin n) (PowerSeries K))
    (tts : Fin 2 → PowerSeries K) (i : Fin 2) :
    (genMember K n i).map (markedArcHom Ns Ms tts) = Ns + tts i • Ms := by
  ext a b
  simp [genMember, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]

/-- The base point of an arc, read on the coordinates: taking constant terms
after evaluating along the arc is evaluating at the base point. -/
theorem constantCoeff_markedArcHom (Ns Ms : Matrix (Fin n) (Fin n) (PowerSeries K))
    (tts : Fin 2 → PowerSeries K) (f : MvPolynomial (MarkedIndex (Fin n)) K) :
    PowerSeries.constantCoeff (markedArcHom Ns Ms tts f)
      = markedEval (matC Ns) (matC Ms) (fun i => PowerSeries.constantCoeff (tts i)) f := by
  have h : (PowerSeries.constantCoeff (R := K)).comp (markedArcHom Ns Ms tts)
      = markedEval (matC Ns) (matC Ms) (fun i => PowerSeries.constantCoeff (tts i)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [markedArcHom, markedEval]
    · intro x
      simp only [RingHom.comp_apply, markedArcHom_X, markedEval_X]
      match x with
      | Sum.inl (Sum.inl ij) => rfl
      | Sum.inl (Sum.inr ij) => rfl
      | Sum.inr i => rfl
  exact congrArg (fun φ => φ f) h


/-- **The member's rank profile is generically constant along an arc**: the
member analogue of `arc_rank_eq`.  On a dense open of `V(I)` every arc of `V(I)`
has `MatArcRankEq` for the member at the `i`-th marked parameter.

This is the rank-constancy field of `MemberArc`, hence — through
`exists_markedWith_of_memberArc` — the marking condition of
`thm:h2-conditional`.  The proof is `Orbital.exists_genericRank` for the
universal member `genMember`, read at the base point and at the generic point of
the arc: both ranks are the generic rank, so they agree. -/
theorem member_arc_rank_eq (m : ℕ) (i : Fin 2)
    (I : Ideal (MvPolynomial (MarkedIndex (Fin n)) K)) [I.IsPrime] :
    ∃ g ∉ I, ∀ (N M : Matrix (Fin n) (Fin n) K) (tt : Fin 2 → K),
      (∀ f ∈ I, markedEval N M tt f = 0) → markedEval N M tt g ≠ 0 →
      ∀ (Ns Ms : Matrix (Fin n) (Fin n) (PowerSeries K)) (tts : Fin 2 → PowerSeries K),
        (∀ f ∈ I, markedArcHom Ns Ms tts f = 0) →
        matC Ns = N → matC Ms = M →
        (fun j => PowerSeries.constantCoeff (tts j)) = tt →
        ∀ k ≤ m, MatArcRankEq (Ns + tts i • Ms) k := by
  classical
  choose r δ hδ using fun k : ℕ => exists_genericRank I ((genMember K n i) ^ k)
  refine ⟨∏ k ∈ Finset.range (m + 1), δ k, ?_, ?_⟩
  · intro hmem
    obtain ⟨k, -, hk⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    exact (hδ k).1 hk
  intro N M tt hI hg Ns Ms tts harc hbN hbM hbt k hk
  have hkr : k ∈ Finset.range (m + 1) := Finset.mem_range.2 (by omega)
  have hfac : markedEval N M tt (δ k) ≠ 0 := by
    rw [map_prod] at hg
    exact Finset.prod_ne_zero_iff.mp hg k hkr
  -- the rank at the base point
  have hbase : (((genMember K n i) ^ k).map (markedEval N M tt)).rank = r k :=
    (hδ k).2 K (markedEval N M tt) hI hfac
  -- the rank at the generic point of the arc
  set φ : MvPolynomial (MarkedIndex (Fin n)) K →+* LaurentSeries K :=
    (algebraMap (PowerSeries K) (LaurentSeries K)).comp (markedArcHom Ns Ms tts) with hφ
  have hφI : ∀ f ∈ I, φ f = 0 := by
    intro f hf
    rw [hφ, RingHom.comp_apply, harc f hf, map_zero]
  have hδarc : markedArcHom Ns Ms tts (δ k) ≠ 0 := by
    intro h0
    refine hfac ?_
    have hcc := constantCoeff_markedArcHom Ns Ms tts (δ k)
    rw [h0, map_zero, hbN, hbM, hbt] at hcc
    exact hcc.symm
  have hφδ : φ (δ k) ≠ 0 := by
    rw [hφ, RingHom.comp_apply]
    intro h0
    exact hδarc (IsFractionRing.injective (PowerSeries K) (LaurentSeries K)
      (by rw [h0, map_zero]))
  have hgen : (((genMember K n i) ^ k).map φ).rank = r k := (hδ k).2 _ φ hφI hφδ
  -- both sides of `MatArcRankEq` are that rank
  have hpow : ∀ {S : Type u} [CommRing S] (ψ : MvPolynomial (MarkedIndex (Fin n)) K →+* S),
      ((genMember K n i) ^ k).map ψ = ((genMember K n i).map ψ) ^ k := by
    intro S _ ψ
    show ψ.mapMatrix ((genMember K n i) ^ k) = _
    rw [map_pow]
    rfl
  have hmapφ : (genMember K n i).map φ
      = (Ns + tts i • Ms).map (algebraMap (PowerSeries K) (LaurentSeries K)) := by
    rw [hφ, RingHom.coe_comp, ← Matrix.map_map, map_genMember_markedArcHom]
  have hmapb : (genMember K n i).map (markedEval N M tt) = matC (Ns + tts i • Ms) := by
    rw [map_genMember_markedEval, matC_add, matC_smul_series, hbN, hbM, ← hbt]
  have hpowA : ((Ns + tts i • Ms) ^ k).map (algebraMap (PowerSeries K) (LaurentSeries K))
      = ((Ns + tts i • Ms).map (algebraMap (PowerSeries K) (LaurentSeries K))) ^ k := by
    show (algebraMap (PowerSeries K) (LaurentSeries K)).mapMatrix ((Ns + tts i • Ms) ^ k) = _
    rw [map_pow]
    rfl
  rw [MatArcRankEq, hpowA, ← hmapφ, ← hpow φ, hgen]
  show _ = (matC ((Ns + tts i • Ms) ^ k)).rank
  rw [matC_pow, ← hmapb, ← hpow (markedEval N M tt), hbase]
end Genericity
end Height.Pencil
