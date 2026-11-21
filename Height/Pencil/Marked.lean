import Height.Geometry.Interface
import Height.Pencil.Local
import Height.Pencil.Torsion

/-!
# Marked directions, the shifted class `μ_x`, and the statement (SI)

The paper, `lem:marked-shift`, `cor:shifted-eval`, `defn:si`.

## Marked directions

At the point `t₀` of the chart of `Chart.lean` the member of the pencil is
`N₀ = N + t₀ M` and `∂_u P = M`.  A pair `(Q̇, ṫ)` — a pencil direction
`Q̇ ∈ gl_n ⊗ B₁` and a motion `ṫ` of the point — is *marked at `t₀` with witness
`Z`* when

```
MarkedWith N M t₀ Q̇ ṫ Z :  Q̇(t₀) + ṫ · M = N₀ Z − Z N₀ ,
```

which is the algebraic form of the derivative of "the member at the moving
point stays in `cl O_λ`" at `N₀`.  The shifted representative is

```
Ṙ := Q̇ + ṫ ∂_u P − [P, Z]   (over K⟦u⟧),      matC Ṙ = 0   (`matC_Rdot`),
```

so `Ṙ` is divisible by the uniformizer, and the shifted class is the class of
`Ṙ / u` read at the exponents `m − 1`, i.e. an element of `u T_x`:

```
muX N M t₀ Q̇ ṫ Z := blockClass (mBlk − 1) (divX Ṙ)  ∈  uTx N M t₀ .
```
`cor:shifted-eval` (`OmegaX_muX_eq_residue`) is proved here, and so is the last
clause of `lem:marked-shift`, in the only form the local model leaves room for.
The paper's identification `μ_x = [Q̇] + ṫ c₀` is an equation in `coker ad_P`,
where both sides live; in the model `[Q̇]` and `μ_x` lie in *different* spaces
(`T_x` and `u T_x`), so the equation itself cannot be stated.  What it is used
for can, and is: `μ_x` does not depend on the marking witness
(`muX_eq_of_markedWith`) and is linear in the direction (`muX_add`, `muX_smul`),
which is what makes the class map `α` of a `RealizedDatum` well defined on the
marked directions (`Chain/H2.lean`).  The mechanism is
`LocalData.blockClass_pred_eq_zero`: changing the witness changes `Ṙ` — not
`Ṙ / u` — by a commutator, and the divided torsion cannot see a direction whose
product with the uniformiser is one.

`OmegaX_muX_eq_residue` needs the hypothesis that the *second* shifted
representative is also a commutator over `K⸨u⸩` — the same hypothesis as in
`lem:residue-form` (`Pencil/Torsion.lean`); the reason is given at the
theorem.  It is supplied at the call site (`Pencil/FlagVelocityArc.lean`,
`flag_velocity_of_decomposition`) by `nilrad_eq_image`.  Self-duality and
normalisation of the Smith datum `txData` are not hypotheses: a
`DVR.AlternatingPresentation` is self-dual by `V_apply` (`rfl`) and normalised
by `g_eq_X_pow_mExp`.

## (SI)

The single-point marked incidence `𝒴_λ` is, as a set of triples
`(N, M, t)`, `singleMarkedLocus τ d N₀`.  An irreducible subvariety `V` is the
zero locus of a prime ideal `I` of `MvPolynomial (SIIndex (Fin n)) K` contained in it,
an arc in `V` is a `K⟦s⟧`-point of `V` (`SIArc.InLocus`), and (SI) says that
at a generic point of `V` the shifted
classes of arc velocities are `Ω_x`-isotropic.

The statement quantifies over the marking witnesses `Z₁, Z₂` rather than
choosing one, and both nodes (`Chain.shiftedIsotropy`, which produces it, and
`Chain.markedIncidenceBound`, which consumes it) use that form.
-/

namespace Height.Pencil

open Matrix Height.Graded Height.DVR Height.Orbital Height.Geometry

variable {K : Type*} [Field K] {n : ℕ}

/-! ### Division by the uniformizer -/

/-- Division by the uniformizer `u`, as a `K`-linear map: a left inverse of
multiplication by `X`. -/
noncomputable def divX : PowerSeries K →ₗ[K] PowerSeries K where
  toFun f := PowerSeries.mk fun k => PowerSeries.coeff (k + 1) f
  map_add' f g := by ext k; simp
  map_smul' c f := by ext k; simp

@[simp] theorem coeff_divX (f : PowerSeries K) (k : ℕ) :
    PowerSeries.coeff k (divX f) = PowerSeries.coeff (k + 1) f := by
  simp [divX]

/-- `divX` undoes multiplication by the uniformizer on series with vanishing
constant term. -/
theorem X_mul_divX {f : PowerSeries K} (hf : PowerSeries.constantCoeff f = 0) :
    (PowerSeries.X : PowerSeries K) * divX f = f := by
  ext k
  cases k with
  | zero => simpa using hf.symm
  | succ k => simp [PowerSeries.coeff_succ_X_mul]

/-! ### Marked directions -/

/-- `(Q̇, ṫ)` is *marked at `t₀`* for the pencil `(N, M)`, with witness `Z`:
the derivative of the incidence condition at the moving point lies in
`im ad_{N₀}`, `N₀ = N + t₀ M`. -/
def MarkedWith (N M : Matrix (Fin n) (Fin n) K) (t₀ : K)
    (Q : Matrix (Fin n) (Fin n) (Graded.Poly K)) (tdot : K)
    (Z : Matrix (Fin n) (Fin n) K) : Prop :=
  matC (Qat Q t₀) + tdot • matD (Pat N M t₀) = (N + t₀ • M) * Z - Z * (N + t₀ • M)

/-- The shifted representative `Ṙ = Q̇ + ṫ ∂_u P − [P, Z]` of
`lem:marked-shift`. -/
noncomputable def Rdot (N M : Matrix (Fin n) (Fin n) K) (t₀ : K)
    (Q : Matrix (Fin n) (Fin n) (Graded.Poly K)) (tdot : K)
    (Z : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) (PowerSeries K) :=
  Qat Q t₀ + tdot • dPat M -
    (Pat N M t₀ * Z.map (PowerSeries.C : K →+* PowerSeries K) -
      Z.map (PowerSeries.C : K →+* PowerSeries K) * Pat N M t₀)

private theorem matC_add' (A B : Matrix (Fin n) (Fin n) (PowerSeries K)) :
    matC (A + B) = matC A + matC B := by
  ext i j; simp [matC]

private theorem matC_sub' (A B : Matrix (Fin n) (Fin n) (PowerSeries K)) :
    matC (A - B) = matC A - matC B := by
  ext i j; simp [matC]

private theorem matC_smul_dPat (tdot : K) (M : Matrix (Fin n) (Fin n) K) :
    matC (tdot • dPat M) = tdot • M := by
  ext i j
  show PowerSeries.constantCoeff (tdot • (dPat M) i j) = _
  simp [dPat]

/-- `lem:marked-shift`, first half: the shifted representative vanishes at the
point, so it is divisible by the uniformizer. -/
theorem matC_Rdot {N M : Matrix (Fin n) (Fin n) K} {t₀ : K}
    {Q : Matrix (Fin n) (Fin n) (Graded.Poly K)} {tdot : K}
    {Z : Matrix (Fin n) (Fin n) K} (h : MarkedWith N M t₀ Q tdot Z) :
    matC (Rdot N M t₀ Q tdot Z) = 0 := by
  rw [MarkedWith, matD_Pat] at h
  rw [Rdot, matC_sub', matC_add', matC_sub', matC_mul, matC_mul, matC_map_C, matC_Pat,
    matC_smul_dPat, h, sub_self]

/-- The shifted representative is `u` times an integral matrix. -/
theorem X_mul_divX_Rdot {N M : Matrix (Fin n) (Fin n) K} {t₀ : K}
    {Q : Matrix (Fin n) (Fin n) (Graded.Poly K)} {tdot : K}
    {Z : Matrix (Fin n) (Fin n) K} (h : MarkedWith N M t₀ Q tdot Z) :
    (PowerSeries.X : PowerSeries K) • (Rdot N M t₀ Q tdot Z).map (divX (K := K))
      = Rdot N M t₀ Q tdot Z := by
  refine Matrix.ext fun i j => ?_
  show (PowerSeries.X : PowerSeries K) * divX ((Rdot N M t₀ Q tdot Z) i j) = _
  refine X_mul_divX ?_
  have := congrFun (congrFun (matC_Rdot h) i) j
  simpa [matC] using this

/-- The shifted class `μ_x(Q̇, ṫ)` of `lem:marked-shift`, in the model `u T_x`:
the class of `Ṙ / u` at the exponents `m − 1`. -/
noncomputable def muX (N M : Matrix (Fin n) (Fin n) K) (t₀ : K)
    (Q : Matrix (Fin n) (Fin n) (Graded.Poly K)) (tdot : K)
    (Z : Matrix (Fin n) (Fin n) K) : uTx N M t₀ :=
  (txData N M t₀).blockClass (fun b => (txData N M t₀).mBlk b - 1)
    ((Rdot N M t₀ Q tdot Z).map (divX (K := K)))

/-! ### `lem:marked-shift`, last clause: `μ_x` is linear in the direction

The paper states the last clause as `μ_x(Q̇, ṫ) = [Q̇] + ṫ c₀` in
`coker ad_P`, from which independence of the witness `Z` and linearity in
`(Q̇, ṫ)` are read off.  Here `coker ad_P` is replaced by the model, where
`[Q̇]` and `μ_x` live in *different* spaces (`T_x` and `u T_x`), so the equation
itself cannot be written; what it is used for can.  Both consequences are
proved here, and together they are what makes the class map `α` of a
`RealizedDatum` well defined on the marked directions.

The mechanism is `LocalData.blockClass_pred_eq_zero`: two witnesses change `Ṙ`
by the commutator `[P, Z₁ − Z₂]`, hence change `Ṙ / u` by something whose
product with the uniformiser is a commutator, and that is exactly what the
divided torsion cannot see. -/

section Linear

variable {N M : Matrix (Fin n) (Fin n) K} {t₀ : K}

private theorem map_divX_add (A B : Matrix (Fin n) (Fin n) (PowerSeries K)) :
    (A + B).map (divX (K := K)) = A.map (divX (K := K)) + B.map (divX (K := K)) := by
  ext i j; simp [Matrix.map_apply]

private theorem map_divX_sub (A B : Matrix (Fin n) (Fin n) (PowerSeries K)) :
    (A - B).map (divX (K := K)) = A.map (divX (K := K)) - B.map (divX (K := K)) := by
  ext i j; simp [Matrix.map_apply]

private theorem map_divX_smul (c : K) (A : Matrix (Fin n) (Fin n) (PowerSeries K)) :
    (c • A).map (divX (K := K)) = c • A.map (divX (K := K)) := by
  ext i j; simp [Matrix.map_apply]

private theorem map_C_add (Z₁ Z₂ : Matrix (Fin n) (Fin n) K) :
    (Z₁ + Z₂).map (PowerSeries.C : K →+* PowerSeries K)
      = Z₁.map (PowerSeries.C : K →+* PowerSeries K)
        + Z₂.map (PowerSeries.C : K →+* PowerSeries K) := by
  ext i j; simp [Matrix.map_apply]

private theorem map_C_sub (Z₁ Z₂ : Matrix (Fin n) (Fin n) K) :
    (Z₁ - Z₂).map (PowerSeries.C : K →+* PowerSeries K)
      = Z₁.map (PowerSeries.C : K →+* PowerSeries K)
        - Z₂.map (PowerSeries.C : K →+* PowerSeries K) := by
  ext i j; simp [Matrix.map_apply]

private theorem map_C_smul (c : K) (Z : Matrix (Fin n) (Fin n) K) :
    (c • Z).map (PowerSeries.C : K →+* PowerSeries K)
      = c • Z.map (PowerSeries.C : K →+* PowerSeries K) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul,
    PowerSeries.smul_eq_C_mul]

private theorem matC_smul' (c : K) (A : Matrix (Fin n) (Fin n) (PowerSeries K)) :
    matC (c • A) = c • matC A := by
  ext i j
  simp only [matC, Matrix.map_apply, Matrix.smul_apply, PowerSeries.smul_eq_C_mul,
    map_mul, PowerSeries.constantCoeff_C, smul_eq_mul]

/-- The chart map is additive in the direction. -/
theorem Qat_add (Q₁ Q₂ : Matrix (Fin n) (Fin n) (Graded.Poly K)) (t₀ : K) :
    Qat (Q₁ + Q₂) t₀ = Qat Q₁ t₀ + Qat Q₂ t₀ := by
  ext i j; simp [Qat, Matrix.map_apply]

/-- The chart map is homogeneous in the direction. -/
theorem Qat_smul (c : K) (Q : Matrix (Fin n) (Fin n) (Graded.Poly K)) (t₀ : K) :
    Qat (c • Q) t₀ = c • Qat Q t₀ := by
  ext i j
  simp only [Qat, Matrix.map_apply, Matrix.smul_apply, PowerSeries.smul_eq_C_mul,
    MvPolynomial.smul_eq_C_mul, map_mul, atPoint_C]

/-! #### The marked directions form a subspace -/

/-- Marked directions are closed under addition, with the sum of the
witnesses. -/
theorem MarkedWith.add {Q₁ Q₂ : Matrix (Fin n) (Fin n) (Graded.Poly K)} {t₁ t₂ : K}
    {Z₁ Z₂ : Matrix (Fin n) (Fin n) K} (h₁ : MarkedWith N M t₀ Q₁ t₁ Z₁)
    (h₂ : MarkedWith N M t₀ Q₂ t₂ Z₂) :
    MarkedWith N M t₀ (Q₁ + Q₂) (t₁ + t₂) (Z₁ + Z₂) :=
  calc matC (Qat (Q₁ + Q₂) t₀) + (t₁ + t₂) • matD (Pat N M t₀)
      = (matC (Qat Q₁ t₀) + t₁ • matD (Pat N M t₀))
        + (matC (Qat Q₂ t₀) + t₂ • matD (Pat N M t₀)) := by
        rw [Qat_add, matC_add', add_smul]; abel
    _ = ((N + t₀ • M) * Z₁ - Z₁ * (N + t₀ • M))
        + ((N + t₀ • M) * Z₂ - Z₂ * (N + t₀ • M)) := by rw [h₁, h₂]
    _ = (N + t₀ • M) * (Z₁ + Z₂) - (Z₁ + Z₂) * (N + t₀ • M) := by
        generalize (N + t₀ • M) = N₀
        rw [Matrix.mul_add, Matrix.add_mul]
        abel

/-- Marked directions are closed under scalars, with the scaled witness. -/
theorem MarkedWith.smul {Q : Matrix (Fin n) (Fin n) (Graded.Poly K)} {tdot : K}
    {Z : Matrix (Fin n) (Fin n) K} (c : K) (h : MarkedWith N M t₀ Q tdot Z) :
    MarkedWith N M t₀ (c • Q) (c • tdot) (c • Z) :=
  calc matC (Qat (c • Q) t₀) + (c • tdot) • matD (Pat N M t₀)
      = c • (matC (Qat Q t₀) + tdot • matD (Pat N M t₀)) := by
        rw [Qat_smul, matC_smul', smul_add, smul_eq_mul, mul_smul]
    _ = c • ((N + t₀ • M) * Z - Z * (N + t₀ • M)) := by rw [h]
    _ = (N + t₀ • M) * (c • Z) - (c • Z) * (N + t₀ • M) := by
        rw [Matrix.mul_smul, Matrix.smul_mul, smul_sub]
/-! #### The shifted representative is linear -/

/-- `Ṙ` is additive in `(Q̇, ṫ, Z)`. -/
theorem Rdot_add (Q₁ Q₂ : Matrix (Fin n) (Fin n) (Graded.Poly K)) (t₁ t₂ : K)
    (Z₁ Z₂ : Matrix (Fin n) (Fin n) K) :
    Rdot N M t₀ (Q₁ + Q₂) (t₁ + t₂) (Z₁ + Z₂)
      = Rdot N M t₀ Q₁ t₁ Z₁ + Rdot N M t₀ Q₂ t₂ Z₂ := by
  simp only [Rdot, Qat_add, add_smul, map_C_add, Matrix.mul_add, Matrix.add_mul]
  abel

/-- `Ṙ` is homogeneous in `(Q̇, ṫ, Z)`. -/
theorem Rdot_smul (c : K) (Q : Matrix (Fin n) (Fin n) (Graded.Poly K)) (tdot : K)
    (Z : Matrix (Fin n) (Fin n) K) :
    Rdot N M t₀ (c • Q) (c • tdot) (c • Z) = c • Rdot N M t₀ Q tdot Z := by
  simp only [Rdot, Qat_smul, smul_eq_mul, mul_smul, map_C_smul, Matrix.mul_smul,
    Matrix.smul_mul, smul_sub, smul_add]

/-- Two witnesses for the same direction differ by a commutator: the difference
of the shifted representatives is `[P, Z₂ − Z₁]`. -/
theorem Rdot_sub_Rdot (Q : Matrix (Fin n) (Fin n) (Graded.Poly K)) (tdot : K)
    (Z₁ Z₂ : Matrix (Fin n) (Fin n) K) :
    Rdot N M t₀ Q tdot Z₁ - Rdot N M t₀ Q tdot Z₂
      = Pat N M t₀ * ((Z₂ - Z₁).map (PowerSeries.C : K →+* PowerSeries K))
        - ((Z₂ - Z₁).map (PowerSeries.C : K →+* PowerSeries K)) * Pat N M t₀ := by
  simp only [Rdot, map_C_sub, Matrix.mul_sub, Matrix.sub_mul]
  abel

/-! #### `μ_x` -/

/-- **`lem:marked-shift`, the independence clause**: the shifted class does not
depend on the marking witness.

In the paper this is "commutators die in `coker ad_P`"; in the model the
witnesses change `Ṙ` — not `Ṙ / u` — by a commutator, and
`LocalData.blockClass_pred_eq_zero` is what converts the one into the other. -/
theorem muX_eq_of_markedWith {Q : Matrix (Fin n) (Fin n) (Graded.Poly K)} {tdot : K}
    {Z₁ Z₂ : Matrix (Fin n) (Fin n) K} (h₁ : MarkedWith N M t₀ Q tdot Z₁)
    (h₂ : MarkedWith N M t₀ Q tdot Z₂) :
    muX N M t₀ Q tdot Z₁ = muX N M t₀ Q tdot Z₂ := by
  rw [← sub_eq_zero, muX, muX, ← map_sub, ← map_divX_sub]
  refine (txData N M t₀).blockClass_pred_eq_zero
    ⟨(Z₂ - Z₁).map (PowerSeries.C : K →+* PowerSeries K), ?_⟩
  rw [map_divX_sub, smul_sub, X_mul_divX_Rdot h₁, X_mul_divX_Rdot h₂]
  exact Rdot_sub_Rdot Q tdot Z₁ Z₂

/-- **`lem:marked-shift`, additivity**: `μ_x` is additive in the marked
direction, for *any* witness of the sum. -/
theorem muX_add {Q₁ Q₂ : Matrix (Fin n) (Fin n) (Graded.Poly K)} {t₁ t₂ : K}
    {Z₁ Z₂ Z : Matrix (Fin n) (Fin n) K} (h₁ : MarkedWith N M t₀ Q₁ t₁ Z₁)
    (h₂ : MarkedWith N M t₀ Q₂ t₂ Z₂) (h : MarkedWith N M t₀ (Q₁ + Q₂) (t₁ + t₂) Z) :
    muX N M t₀ (Q₁ + Q₂) (t₁ + t₂) Z
      = muX N M t₀ Q₁ t₁ Z₁ + muX N M t₀ Q₂ t₂ Z₂ := by
  rw [muX_eq_of_markedWith h (h₁.add h₂), muX, muX, muX, Rdot_add, map_divX_add, map_add]

/-- **`lem:marked-shift`, homogeneity**: `μ_x` is homogeneous in the marked
direction, for *any* witness of the multiple. -/
theorem muX_smul {Q : Matrix (Fin n) (Fin n) (Graded.Poly K)} {tdot : K}
    {Z Z' : Matrix (Fin n) (Fin n) K} (c : K) (h : MarkedWith N M t₀ Q tdot Z)
    (h' : MarkedWith N M t₀ (c • Q) (c • tdot) Z') :
    muX N M t₀ (c • Q) (c • tdot) Z' = c • muX N M t₀ Q tdot Z := by
  rw [muX_eq_of_markedWith h' (h.smul c), muX, muX, Rdot_smul, map_divX_smul, map_smul]


/-! #### What `μ_x` sees -/

/-- `μ_x` vanishes exactly when the shifted representative has no torsion
class: reading `Ṙ / u` at the exponents `m − 1` loses nothing. -/
theorem muX_eq_zero_iff {Q : Matrix (Fin n) (Fin n) (Graded.Poly K)} {tdot : K}
    {Z : Matrix (Fin n) (Fin n) K} (h : MarkedWith N M t₀ Q tdot Z) :
    muX N M t₀ Q tdot Z = 0
      ↔ (txData N M t₀).blockClass (txData N M t₀).mBlk (Rdot N M t₀ Q tdot Z) = 0 := by
  rw [muX, (txData N M t₀).blockClass_pred_eq_zero_iff, X_mul_divX_Rdot h]

/-- **Where the kernel slack `s = 2` of `thm:h2-conditional` comes from.**  On a
direction that does not move the marked point (`ṫ = 0`) the shifted class
vanishes exactly when the *ordinary* class of the direction does: the marking
witness contributes a commutator, which no torsion class sees.

So the marked class map and the unmarked one have the same kernel on
`{ṫ = 0}`, and the kernel of the marked map exceeds the kernel of the unmarked
one by at most the two `ṫ`-coordinates of the two marked points — which is the
slack `s = 2` of `RealizedDatum.Bounds` (`Chain/H2.lean`), and the reason it is
`2` and not more. -/
theorem muX_eq_zero_iff_blockClass {Q : Matrix (Fin n) (Fin n) (Graded.Poly K)}
    {Z : Matrix (Fin n) (Fin n) K} (h : MarkedWith N M t₀ Q 0 Z) :
    muX N M t₀ Q 0 Z = 0
      ↔ (txData N M t₀).blockClass (txData N M t₀).mBlk (Qat Q t₀) = 0 := by
  rw [muX_eq_zero_iff h]
  have hR : Rdot N M t₀ Q 0 Z
      = Qat Q t₀ - (Pat N M t₀ * Z.map (PowerSeries.C : K →+* PowerSeries K)
          - Z.map (PowerSeries.C : K →+* PowerSeries K) * Pat N M t₀) := by
    simp [Rdot]
  rw [hR, map_sub,
    (txData N M t₀).blockClass_eq_zero_of_isCommutator ⟨_, rfl⟩, sub_zero]
end Linear

/-! ### `cor:shifted-eval` -/

/-- `cor:shifted-eval` in the local model: if `Ṙ_i = u S_i` are commutators over
`K⸨u⸩`, the divided residue form on the classes of the `S_i` at the exponents
`m − 1` is the residue of `u⁻¹ trace(A₁ Ṙ₂)`.

This is `lem:divided-form`, the `k = 1` case of
`DVR.AlternatingPresentation.residueSpaceForm_blockClassOf`, read on the
`vecMat` bridge exactly as `LocalData.omega_eq_residue` (`Pencil/Torsion.lean`)
reads the `k = 0` case. -/
theorem LocalData.dividedForm_eq_residue {P : Matrix (Fin n) (Fin n) (PowerSeries K)}
    (D : LocalData K n P)
    (R₁ R₂ S₁ S₂ : Matrix (Fin n) (Fin n) (PowerSeries K))
    (hS₁ : (PowerSeries.X : PowerSeries K) • S₁ = R₁)
    (hS₂ : (PowerSeries.X : PowerSeries K) • S₂ = R₂)
    (A₁ A₂ : Matrix (Fin n) (Fin n) (LaurentSeries K))
    (hA₁ : Isotropy.toK (LaurentSeries K) P * A₁ - A₁ * Isotropy.toK (LaurentSeries K) P
      = Isotropy.toK (LaurentSeries K) R₁)
    (hA₂ : Isotropy.toK (LaurentSeries K) P * A₂ - A₂ * Isotropy.toK (LaurentSeries K) P
      = Isotropy.toK (LaurentSeries K) R₂) :
    residueSpaceForm (fun b => D.mBlk b - 1)
        (D.blockClass (fun b => D.mBlk b - 1) S₁)
        (D.blockClass (fun b => D.mBlk b - 1) S₂)
      = laurentResidue K (uInvPow K 1 *
          Matrix.trace (A₁ * Isotropy.toK (LaurentSeries K) R₂)) := by
  rw [trace_mul_toK_eq_sum, D.blockClass_eq_blockClassOf, D.blockClass_eq_blockClassOf]
  exact D.residueSpaceForm_blockClassOf 1 le_rfl
    (Height.Toolbox.vecMat R₁) (Height.Toolbox.vecMat R₂)
    (Height.Toolbox.vecMat S₁) (Height.Toolbox.vecMat S₂)
    (by rw [pow_one, ← hS₁]; rfl) (by rw [pow_one, ← hS₂]; rfl)
    (Height.Toolbox.vecMat A₁) (Height.Toolbox.vecMat A₂)
    (mulVec_of_commutator A₁ hA₁) (mulVec_of_commutator A₂ hA₂)

/-- `cor:shifted-eval`: `Ω_x` of two shifted classes is the residue of
`u⁻¹ trace(A₁ Ṙ₂)`.

As in `lem:residue-form` (the module docstring of `Pencil/Torsion.lean`),
*`Ṙ₂` must also be a commutator over `K⸨u⸩`* (`A₂`, `hA₂`).  The right-hand
side is linear in `Ṙ₂` over all of `gl_n(K⟦u⟧)`, while the left-hand side
records only torsion coordinates; on a direction whose class in
`coker ad_P` has a nonzero free part the two sides differ, and `hA₂` is
exactly what makes the free coordinates of `Ṙ₂` vanish.  The paper
assumes it: in `cor:shifted-eval` both `Ṙ_i` have torsion classes by
`cor:arc-torsion`. -/
theorem OmegaX_muX_eq_residue (N M : Matrix (Fin n) (Fin n) K) (t₀ : K)
    (Q₁ Q₂ : Matrix (Fin n) (Fin n) (Graded.Poly K)) (t₁ t₂ : K)
    (Z₁ Z₂ : Matrix (Fin n) (Fin n) K)
    (h₁ : MarkedWith N M t₀ Q₁ t₁ Z₁) (h₂ : MarkedWith N M t₀ Q₂ t₂ Z₂)
    (A₁ A₂ : Matrix (Fin n) (Fin n) (LaurentSeries K))
    (hA₁ : Isotropy.toK (LaurentSeries K) (Pat N M t₀) * A₁ -
      A₁ * Isotropy.toK (LaurentSeries K) (Pat N M t₀)
        = Isotropy.toK (LaurentSeries K) (Rdot N M t₀ Q₁ t₁ Z₁))
    (hA₂ : Isotropy.toK (LaurentSeries K) (Pat N M t₀) * A₂ -
      A₂ * Isotropy.toK (LaurentSeries K) (Pat N M t₀)
        = Isotropy.toK (LaurentSeries K) (Rdot N M t₀ Q₂ t₂ Z₂)) :
    OmegaX N M t₀ (muX N M t₀ Q₁ t₁ Z₁) (muX N M t₀ Q₂ t₂ Z₂)
      = laurentResidue K (uInvPow K 1 *
          Matrix.trace (A₁ * Isotropy.toK (LaurentSeries K) (Rdot N M t₀ Q₂ t₂ Z₂))) :=
  (txData N M t₀).dividedForm_eq_residue _ _ _ _
    (X_mul_divX_Rdot h₁) (X_mul_divX_Rdot h₂) A₁ A₂ hA₁ hA₂

end Height.Pencil

/-! ### The statement (SI) -/

namespace Height.Pencil

open Height.Steenrod Height.Orbital Height.Geometry

section General

variable {K : Type*} [Field K] {n : ℕ}

/-- `𝒴_λ`, the single-point marked incidence of `defn:si`: pencils in
`Î_{τ,d}` together with a point at which the member degenerates into the
closure of the orbit of `N₀`. -/
def singleMarkedLocus (τ : Nat.Partition n) (d : ℕ → ℕ) (N₀ : Matrix (Fin n) (Fin n) K) :
    Set (SIPoint (Fin n) K) :=
  {q | (q.1, q.2.1) ∈ pencilLocus τ d ∧ q.1 + q.2.2 • q.2.1 ∈ orbitClosure N₀}

/-- Forgetting the second marked point sends `Ŷ` into `𝒴_λ`: a pencil marked at
two distinct parameters is in particular marked at the first of them.

This is what makes the nonemptiness of `𝒴_λ` that the proof of (H2′) needs
available from nonemptiness of `markedLocus`, which is the set the bound is
about. -/
theorem singleMarkedLocus_nonempty_of_markedLocus {τ : Nat.Partition n} {d : ℕ → ℕ}
    {N₀ : Matrix (Fin n) (Fin n) K} (h : (markedLocus τ d N₀).Nonempty) :
    (singleMarkedLocus τ d N₀).Nonempty := by
  obtain ⟨q, hq⟩ := h
  exact ⟨(q.1, q.2.1, q.2.2.1), hq.1, hq.2.2.1⟩

/-- An arc of pencils-with-parameter: a `K⟦s⟧`-point of the ambient affine
space. -/
structure SIArc (n : ℕ) (K : Type*) [Field K] where
  /-- The first matrix of the pencil, over `K⟦s⟧`. -/
  N : Matrix (Fin n) (Fin n) (PowerSeries K)
  /-- The second matrix of the pencil, over `K⟦s⟧`. -/
  M : Matrix (Fin n) (Fin n) (PowerSeries K)
  /-- The moving point of `ℙ¹`, over `K⟦s⟧`. -/
  t : PowerSeries K

/-- The coordinate vector of an arc. -/
noncomputable def SIArc.coords (a : SIArc n K) : SIIndex (Fin n) → PowerSeries K :=
  siCoords (a.N, a.M, a.t)

/-- The arc lies in the locus cut out by `I`. -/
def SIArc.InLocus (a : SIArc n K) (I : Ideal (MvPolynomial (SIIndex (Fin n)) K)) : Prop :=
  ∀ f ∈ I, MvPolynomial.aeval a.coords f = 0

/-- The base point of an arc. -/
noncomputable def SIArc.base (a : SIArc n K) : SIPoint (Fin n) K :=
  (matC a.N, matC a.M, PowerSeries.constantCoeff a.t)

/-- The velocity of an arc. -/
noncomputable def SIArc.vel (a : SIArc n K) : SIPoint (Fin n) K :=
  (matD a.N, matD a.M, PowerSeries.coeff 1 a.t)

theorem SIArc.siCoords_base (a : SIArc n K) :
    siCoords a.base = fun i => PowerSeries.constantCoeff (a.coords i) := by
  funext i
  rcases i with (⟨ij⟩ | ⟨ij⟩) | u
  · rfl
  · rfl
  · rfl

theorem SIArc.siCoords_vel (a : SIArc n K) :
    siCoords a.vel = fun i => PowerSeries.coeff 1 (a.coords i) := by
  funext i
  rcases i with (⟨ij⟩ | ⟨ij⟩) | u
  · rfl
  · rfl
  · rfl

/-- **An arc of the incidence is its tuple of coordinates.** -/
noncomputable def SIArc.coordsEquiv : SIArc n K ≃ (SIIndex (Fin n) → PowerSeries K) where
  toFun a := a.coords
  invFun c := ⟨(siCoords.symm c).1, (siCoords.symm c).2.1, (siCoords.symm c).2.2⟩
  left_inv _ := rfl
  right_inv c := siCoords.apply_symm_apply c

/-- A velocity `(Ṅ, Ṁ, ṫ)` of the single-point marked incidence is marked at
the moving point of `q`, with witness `Z`. -/
def SIMarked (q : SIPoint (Fin n) K) (v : SIPoint (Fin n) K) (Z : Matrix (Fin n) (Fin n) K) : Prop :=
  Height.Pencil.MarkedWith q.1 q.2.1 q.2.2 (pencil v.1 v.2.1) v.2.2 Z

/-- The `Ω_x`-pairing of two marked velocities at a point of the single-point
marked incidence. -/
noncomputable def siPairing (q v₁ v₂ : SIPoint (Fin n) K)
    (Z₁ Z₂ : Matrix (Fin n) (Fin n) K) : K :=
  Height.Pencil.OmegaX q.1 q.2.1 q.2.2
    (Height.Pencil.muX q.1 q.2.1 q.2.2 (pencil v₁.1 v₁.2.1) v₁.2.2 Z₁)
    (Height.Pencil.muX q.1 q.2.1 q.2.2 (pencil v₂.1 v₂.2.1) v₂.2.2 Z₂)

/-- The member of the pencil at the marked point of `q`. -/
def siMember (q : SIPoint (Fin n) K) : Matrix (Fin n) (Fin n) K := q.1 + q.2.2 • q.2.1

/-- An arc of the incidence lying in `V(I)` and based at the point `z`. -/
structure ArcAt (I : Ideal (MvPolynomial (SIIndex (Fin n)) K)) (z : SIIndex (Fin n) → K) where
  /-- the arc -/
  a : SIArc n K
  inLocus : a.InLocus I
  base : a.base = siCoords.symm z

/-- An arc in `V(I)` at `z` together with a marking witness for its velocity. -/
structure MarkedArc (I : Ideal (MvPolynomial (SIIndex (Fin n)) K)) (z : SIIndex (Fin n) → K)
    extends ArcAt I z where
  /-- the marking witness -/
  Z : Matrix (Fin n) (Fin n) K
  marked : SIMarked (siCoords.symm z) a.vel Z

/-- `V(I)` is an irreducible subvariety of the single-point marked incidence *on the dense
open `D(g)`*: `I` is prime, `g ∉ I`, and every point of `V(I) ∖ V(g)` lies in
`singleMarkedLocus τ d N₀`.  This is the hypothesis form of every (SI)-layer statement.
Membership on all of `V(I)` is never available — the closure of a component of the cone
contains the zero pencil, of type `1ⁿ ≠ τ` — and the paper's (SI) is for a `V` whose
*generic* member has type `τ`. -/
structure SILocus (τ : Nat.Partition n) (d : ℕ → ℕ) (N₀ : Matrix (Fin n) (Fin n) K)
    (I : Ideal (MvPolynomial (SIIndex (Fin n)) K)) (g : MvPolynomial (SIIndex (Fin n)) K) : Prop where
  prime : I.IsPrime
  notMem : g ∉ I
  /-- the open `V(I) ∩ D(g)` lies in the single-point marked locus -/
  locus : ∀ z ∈ MvPolynomial.zeroLocus K I, MvPolynomial.eval z g ≠ 0 →
    siCoords.symm z ∈ singleMarkedLocus τ d N₀

/-- A dense open of `V(I)` inside `D(g)`: `g * h ∉ I`. -/
theorem SILocus.mul_notMem {τ : Nat.Partition n} {d : ℕ → ℕ} {N₀ : Matrix (Fin n) (Fin n) K}
    {I : Ideal (MvPolynomial (SIIndex (Fin n)) K)} {g : MvPolynomial (SIIndex (Fin n)) K}
    (hl : SILocus τ d N₀ I g) {h : MvPolynomial (SIIndex (Fin n)) K} (hh : h ∉ I) : g * h ∉ I :=
  fun hm => (hl.prime.mem_or_mem hm).elim hl.notMem hh

/-- A single-point incidence: an irreducible component `V(I)` of the cone
together with a dense open `V(I) ∩ D(g)` of it inside the marked locus. -/
structure SIComponent (τ : Nat.Partition n) (d : ℕ → ℕ)
    (N₀ : Matrix (Fin n) (Fin n) K) where
  /-- the prime of the component -/
  I : Ideal (MvPolynomial (SIIndex (Fin n)) K)
  /-- the function cutting out the dense open -/
  g : MvPolynomial (SIIndex (Fin n)) K
  /-- the open `V(I) ∩ D(g)` lies in the marked locus -/
  locus : SILocus τ d N₀ I g

end General

/-! ### Shifted isotropy

The geometry API ties the index universe of `𝔸(ι)` to that of `K`, so the
statements below live at `K : Type` (the chain runs at `Kbar p r : Type`). -/

section ShiftedIsotropy

variable {K : Type} [Field K] {n : ℕ}

/-- **The arcs of `V(I)` as arcs of the incidence**: a `K⟦u⟧`-point of the
closed subscheme `V(I)` of the ambient space of the single-point marked
incidence is exactly an `SIArc` lying in the locus cut out by `I`
(`Geometry.arcEquiv` read through the chart `siCoords`). -/
noncomputable def siArcEquiv (I : Ideal (MvPolynomial (SIIndex (Fin n)) K)) :
    Height.Geometry.Arc I ≃ {a : SIArc n K // a.InLocus I} :=
  (Height.Geometry.arcEquiv I).trans
    (Equiv.subtypeEquiv SIArc.coordsEquiv.symm fun c => by
      show (∀ f ∈ I, MvPolynomial.aeval c f = 0) ↔ (SIArc.coordsEquiv.symm c).InLocus I
      rw [SIArc.InLocus, show (SIArc.coordsEquiv.symm c).coords = c from
        SIArc.coordsEquiv.apply_symm_apply c])

theorem coe_siArcEquiv {I : Ideal (MvPolynomial (SIIndex (Fin n)) K)}
    (a : Height.Geometry.Arc I) :
    ((siArcEquiv I a : SIArc n K)).coords = a.coords :=
  SIArc.coordsEquiv.apply_symm_apply a.coords

theorem coords_siArcEquiv_symm {I : Ideal (MvPolynomial (SIIndex (Fin n)) K)}
    (a : {a : SIArc n K // a.InLocus I}) :
    ((siArcEquiv I).symm a).coords = (a : SIArc n K).coords := by
  rw [siArcEquiv, Equiv.symm_trans_apply, Height.Geometry.coords_arcEquiv_symm]
  rfl

/-- The base point of the API arc is the base point of the `SIArc`. -/
theorem base_siArcEquiv {I : Ideal (MvPolynomial (SIIndex (Fin n)) K)}
    (a : Height.Geometry.Arc I) :
    (siArcEquiv I a : SIArc n K).base = siCoords.symm a.base := by
  rw [← siCoords.symm_apply_apply (siArcEquiv I a : SIArc n K).base,
    SIArc.siCoords_base, coe_siArcEquiv]
  rfl

/-- The velocity of the API arc is the velocity of the `SIArc`. -/
theorem vel_siArcEquiv {I : Ideal (MvPolynomial (SIIndex (Fin n)) K)}
    (a : Height.Geometry.Arc I) :
    (siArcEquiv I a : SIArc n K).vel = siCoords.symm a.vel := by
  rw [← siCoords.symm_apply_apply (siArcEquiv I a : SIArc n K).vel,
    SIArc.siCoords_vel, coe_siArcEquiv]
  rfl

/-- The base point of the `SIArc`, read on the API arc. -/
theorem base_siArcEquiv_symm {I : Ideal (MvPolynomial (SIIndex (Fin n)) K)}
    (a : {a : SIArc n K // a.InLocus I}) :
    ((siArcEquiv I).symm a).base = siCoords (a : SIArc n K).base := by
  rw [SIArc.siCoords_base]
  funext i
  show PowerSeries.constantCoeff (((siArcEquiv I).symm a).coords i) = _
  rw [coords_siArcEquiv_symm]

/-- The velocity of the `SIArc`, read on the API arc. -/
theorem vel_siArcEquiv_symm {I : Ideal (MvPolynomial (SIIndex (Fin n)) K)}
    (a : {a : SIArc n K // a.InLocus I}) :
    ((siArcEquiv I).symm a).vel = siCoords (a : SIArc n K).vel := by
  rw [SIArc.siCoords_vel]
  funext i
  show PowerSeries.coeff 1 (((siArcEquiv I).symm a).coords i) = _
  rw [coords_siArcEquiv_symm]

/-- **The locus bridge**: the dense-open clause of `SILocus` — every point of
`V(I) ∩ D(g)` lies in the single-point marked incidence — is the API's generic
quantifier at the `K`-points of `V(I)` (`Geometry.genericPts_iff`). -/
theorem exists_siLocus_iff [IsAlgClosed K] (τ : Nat.Partition n) (d : ℕ → ℕ)
    (N₀ : Matrix (Fin n) (Fin n) K) (I : Ideal (MvPolynomial (SIIndex (Fin n)) K))
    [hI : I.IsPrime] :
    Height.Geometry.GenericPts I (fun z => siCoords.symm z ∈ singleMarkedLocus τ d N₀) ↔
      ∃ g, SILocus τ d N₀ I g := by
  rw [Height.Geometry.genericPts_iff]
  constructor
  · rintro ⟨g, hg, hmain⟩
    exact ⟨g, hI, hg, fun z hz hne =>
      hmain z hz (by rwa [MvPolynomial.aeval_eq_eval])⟩
  · rintro ⟨g, hloc⟩
    exact ⟨g, hloc.notMem, fun z hz hne =>
      hloc.locus z hz (by rwa [← MvPolynomial.aeval_eq_eval])⟩

/-- **`defn:si`, shifted isotropy** of the closed subscheme `V(I)` of the
single-point marked incidence: generically on `V(I)`, for any two arcs of
`V(I)` through the point and any marking witnesses of their velocities, the
`Ω_x`-pairing of the `μ_x`-classes vanishes. -/
def ShiftedIsotropy (I : Ideal (MvPolynomial (SIIndex (Fin n)) K)) : Prop :=
  Height.Geometry.GenericPts I fun z =>
    ∀ a₁ a₂ : Height.Geometry.Arc I, a₁.base = z → a₂.base = z →
      ∀ Z₁ Z₂ : Matrix (Fin n) (Fin n) K,
        SIMarked (siCoords.symm z) (siCoords.symm a₁.vel) Z₁ →
        SIMarked (siCoords.symm z) (siCoords.symm a₂.vel) Z₂ →
        siPairing (siCoords.symm z) (siCoords.symm a₁.vel) (siCoords.symm a₂.vel) Z₁ Z₂ = 0

end ShiftedIsotropy

end Height.Pencil
