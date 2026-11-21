import Height.Graded.LocalLength
import Height.Pencil.Basic

/-!
# Substitution and conjugation invariance of the pencil loci

Two group actions on the affine
space of pairs `(N, M)` of matrices preserve every condition that cuts out
`pencilLocus` and `markedLocus`:

* the *reparametrisation* action `(N, M) ↦ (N + a M, b M)` of the affine group
  of the line, `b ≠ 0`.  On the graded side it is the substitution
  `μ ↦ μ`, `ν ↦ a μ + b ν` (`substAlg`), a graded automorphism of
  `Graded.Poly K = K[μ, ν]` (`substEquiv`), which carries `pencil N M` to
  `pencil (N + a M) (b M)` (`map_pencil`) and hence the kernel pieces
  `kerPiece` to each other by a `K`-linear isomorphism
  (`substVec_mem_kerPiece`).  The member of the pencil at the parameter `t`
  becomes the member at `(t - a)/b`, so the marking transforms accordingly
  (`markedLocus_subst`);
* the *swap* `μ ↔ ν` (`Graded.swapAlg`), which exchanges the two members of the
  pencil (`pencilLocus_swap`).  It is the reparametrisation of `ℙ¹` the affine
  group is missing, and conjugating the affine reparametrisation by it gives the
  *lower* shear `(N, M) ↦ (N, M + c N)` (`pencilLocus_shear`) — the substitution
  that moves the member at the parameter `c⁻¹` to infinity, which is what
  `Chain/H1Geometry.lean` needs to put a member of the generic type there;
* the *conjugation* action `(N, M) ↦ (g N g⁻¹, g M g⁻¹)`, which on the graded
  side is conjugation of `pencil N M` by the constant matrix `g`.

The output is the stability of `pencilLocus` (`pencilLocus_subst`,
`pencilLocus_swap`, `pencilLocus_shear`, `pencilLocus_conj`) and of
`markedLocus` (`markedLocus_subst`); these are the inputs the homogeneous-fibration lemmas of
`Geometry/Dimension/Homogeneous.lean` need in order to see the fibres of
`(N, M, t₁, t₂) ↦ (N + t₁ M, N + t₂ M)` as orbits of a two-dimensional group.
-/

namespace Height.Chain

open Height.Pencil

open Matrix Height.Graded Height.Steenrod Height.Toolbox

universe u

variable {K : Type u} [Field K] {n : ℕ}

/-! ### The substitution `μ ↦ μ`, `ν ↦ a μ + b ν` -/

/-- The `K`-algebra endomorphism of `K[μ, ν]` with `μ ↦ μ` and
`ν ↦ a μ + b ν`. -/
noncomputable def substAlg (a b : K) : Graded.Poly K →ₐ[K] Graded.Poly K :=
  MvPolynomial.aeval ![(mu : Graded.Poly K), MvPolynomial.C a * mu + MvPolynomial.C b * nu]

@[simp] theorem substAlg_C (a b c : K) :
    substAlg a b (MvPolynomial.C c : Graded.Poly K) = MvPolynomial.C c := by
  simp [substAlg]

@[simp] theorem substAlg_mu (a b : K) : substAlg a b (mu : Graded.Poly K) = mu := by
  simp [substAlg, mu]

@[simp] theorem substAlg_nu (a b : K) :
    substAlg a b (nu : Graded.Poly K) = MvPolynomial.C a * mu + MvPolynomial.C b * nu := by
  simp [substAlg, nu]

theorem substAlg_apply_X (a b : K) (i : Fin 2) :
    substAlg a b (MvPolynomial.X i : Graded.Poly K) =
      ![(mu : Graded.Poly K), MvPolynomial.C a * mu + MvPolynomial.C b * nu] i := by
  simp [substAlg]

/-- `σ_{a',b'} ∘ σ_{a,b} = σ_{a + b a', b b'}`. -/
theorem substAlg_comp (a b a' b' : K) :
    (substAlg a' b').comp (substAlg a b) = substAlg (a + b * a') (b * b') := by
  refine MvPolynomial.algHom_ext fun i => ?_
  fin_cases i <;>
    simp [substAlg_apply_X, mu, nu, MvPolynomial.C_mul, mul_add, mul_comm, mul_left_comm,
      ]; ring

/-- `σ_{0,1}` is the identity. -/
@[simp] theorem substAlg_zero_one : substAlg (0 : K) 1 = AlgHom.id K (Graded.Poly K) := by
  refine MvPolynomial.algHom_ext fun i => ?_
  fin_cases i <;> simp [substAlg_apply_X, mu, nu]

/-! ### The substitution is graded -/

theorem substAlg_mem_Bpiece {a b : K} {e : ℤ} {f : Graded.Poly K} (hf : f ∈ Bpiece K e) :
    substAlg a b f ∈ Bpiece K e := by
  rcases lt_or_ge e 0 with he | he
  · rw [Bpiece_of_neg he] at hf
    have hf0 : f = 0 := by simpa using hf
    rw [hf0, map_zero]
    exact Submodule.zero_mem _
  · lift e to ℕ using he with m
    rw [Bpiece_natCast] at hf ⊢
    have hg : ∀ i : Fin 2,
        (![(mu : Graded.Poly K), MvPolynomial.C a * mu + MvPolynomial.C b * nu] i).IsHomogeneous 1 := by
      intro i
      fin_cases i
      · exact MvPolynomial.isHomogeneous_X K 0
      · exact ((MvPolynomial.isHomogeneous_C _ a).mul (MvPolynomial.isHomogeneous_X K 0)).add
          ((MvPolynomial.isHomogeneous_C _ b).mul (MvPolynomial.isHomogeneous_X K 1))
    have := (MvPolynomial.IsHomogeneous.aeval (φ := f) hf _ hg)
    rwa [one_mul] at this

/-- The substitution acting coordinatewise on `B^n`. -/
noncomputable def substVec (a b : K) (n : ℕ) :
    (Fin n → Graded.Poly K) →ₗ[K] (Fin n → Graded.Poly K) :=
  LinearMap.pi fun i => (substAlg a b).toLinearMap.comp (LinearMap.proj i)

@[simp] theorem substVec_apply (a b : K) (f : Fin n → Graded.Poly K) (i : Fin n) :
    substVec a b n f i = substAlg a b (f i) := rfl

theorem substVec_mem_piece {a b : K} {e : ℤ} {f : Fin n → Graded.Poly K}
    (hf : f ∈ (Graded.GradedPresentation.free K (Fin n)).piece e) :
    substVec a b n f ∈ (Graded.GradedPresentation.free K (Fin n)).piece e := by
  rw [(Graded.GradedPresentation.of K _).mem_piece] at hf ⊢
  intro j
  exact substAlg_mem_Bpiece (hf j)

/-! ### The substitution on pencils -/

theorem map_pencil (a b : K) (N M : Matrix (Fin n) (Fin n) K) :
    (pencil N M).map (substAlg a b) = pencil (N + a • M) (b • M) := by
  ext i j : 2
  simp only [Matrix.map_apply, pencil, Matrix.of_apply, map_add, map_mul, substAlg_mu,
    substAlg_nu, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    substAlg_C]
  ring

theorem map_pencil_pow (a b : K) (N M : Matrix (Fin n) (Fin n) K) (k : ℕ) :
    (pencil N M ^ k).map (substAlg a b) = pencil (N + a • M) (b • M) ^ k := by
  have h : ((substAlg a b).mapMatrix : Matrix (Fin n) (Fin n) (Graded.Poly K) →ₐ[K] _)
      (pencil N M ^ k) = ((substAlg a b).mapMatrix (pencil N M)) ^ k := map_pow _ _ _
  simpa [AlgHom.mapMatrix_apply, map_pencil] using h

/-- The substitution carries the kernel flag of `(N, M)` into that of
`(N + a M, b M)`. -/
theorem substVec_mem_kerFlag {a b : K} {N M : Matrix (Fin n) (Fin n) K} {k : ℕ}
    {f : Fin n → Graded.Poly K} (hf : f ∈ Height.Pencil.kerFlag N M k) :
    substVec a b n f ∈ Height.Pencil.kerFlag (N + a • M) (b • M) k := by
  rw [Height.Pencil.mem_kerFlag] at hf ⊢
  funext i
  have h : substAlg a b (((pencil N M ^ k) *ᵥ f) i) = 0 := by
    simp [hf]
  rw [Matrix.mulVec_apply_eq_sum] at h
  rw [← map_pencil_pow a b N M k, Pi.zero_apply, Matrix.mulVec_apply_eq_sum]
  simpa [map_sum, substVec_apply] using h

theorem substVec_mem_kerPiece {a b : K} {N M : Matrix (Fin n) (Fin n) K} {k e : ℕ}
    {f : Fin n → Graded.Poly K} (hf : f ∈ kerPiece N M k e) :
    substVec a b n f ∈ kerPiece (N + a • M) (b • M) k e := by
  rw [← Height.Pencil.sub_kerFlag] at hf ⊢
  exact ⟨substVec_mem_kerFlag (Submodule.mem_inf.mp hf).1,
    substVec_mem_piece (Submodule.mem_inf.mp hf).2⟩

/-! ### The substitution is invertible on the kernel pieces -/

theorem substAlg_left_inv (a : K) {b : K} (hb : b ≠ 0) (f : Graded.Poly K) :
    substAlg (-(a / b)) b⁻¹ (substAlg a b f) = f := by
  have h := congrArg (fun φ : Graded.Poly K →ₐ[K] Graded.Poly K => φ f)
    (substAlg_comp a b (-(a / b)) b⁻¹)
  simp only [AlgHom.comp_apply] at h
  have h1 : a + b * -(a / b) = 0 := by field_simp; ring
  have h2 : b * b⁻¹ = (1 : K) := mul_inv_cancel₀ hb
  rw [h1, h2, substAlg_zero_one] at h
  simpa using h

theorem substAlg_right_inv (a : K) {b : K} (hb : b ≠ 0) (f : Graded.Poly K) :
    substAlg a b (substAlg (-(a / b)) b⁻¹ f) = f := by
  have h := congrArg (fun φ : Graded.Poly K →ₐ[K] Graded.Poly K => φ f)
    (substAlg_comp (-(a / b)) b⁻¹ a b)
  simp only [AlgHom.comp_apply] at h
  have h1 : -(a / b) + b⁻¹ * a = 0 := by field_simp; ring
  have h2 : b⁻¹ * b = (1 : K) := inv_mul_cancel₀ hb
  rw [h1, h2, substAlg_zero_one] at h
  simpa using h

/-- The inverse substitution sends the transformed pair back to `(N, M)`. -/
theorem subst_fst_inv {a b : K} (hb : b ≠ 0) (N M : Matrix (Fin n) (Fin n) K) :
    (N + a • M) + (-(a / b)) • (b • M) = N := by
  have h : (-(a / b)) • (b • M) = (-a) • M := by
    rw [smul_smul]
    congr 1
    field_simp
  rw [h]
  module

theorem subst_snd_inv {b : K} (hb : b ≠ 0) (M : Matrix (Fin n) (Fin n) K) :
    b⁻¹ • (b • M) = M := by
  rw [smul_smul, inv_mul_cancel₀ hb, one_smul]

/-- The degree-`e` kernel pieces of `(N, M)` and of `(N + a M, b M)` are
isomorphic `K`-vector spaces. -/
noncomputable def kerPieceEquivSubst (a : K) {b : K} (hb : b ≠ 0)
    (N M : Matrix (Fin n) (Fin n) K) (k e : ℕ) :
    kerPiece N M k e ≃ₗ[K] kerPiece (N + a • M) (b • M) k e := by
  refine LinearEquiv.ofLinearMap
    (LinearMap.codRestrict _ ((substVec a b n).comp (Submodule.subtype _))
      (fun x => substVec_mem_kerPiece x.2))
    (LinearMap.codRestrict _ ((substVec (-(a / b)) b⁻¹ n).comp (Submodule.subtype _))
      (fun x => by
        have h := substVec_mem_kerPiece (a := -(a / b)) (b := b⁻¹) x.2
        rwa [subst_fst_inv hb N M, subst_snd_inv hb M] at h)) ?_ ?_
  · refine LinearMap.ext fun x => Subtype.ext (funext fun j => ?_)
    exact substAlg_right_inv a hb _
  · refine LinearMap.ext fun x => Subtype.ext (funext fun j => ?_)
    exact substAlg_left_inv a hb _

theorem finrank_kerPiece_subst (a : K) {b : K} (hb : b ≠ 0)
    (N M : Matrix (Fin n) (Fin n) K) (k e : ℕ) :
    Module.finrank K (kerPiece (N + a • M) (b • M) k e) = Module.finrank K (kerPiece N M k e) :=
  ((kerPieceEquivSubst a hb N M k e).finrank_eq).symm

/-! ### Invariance of the three conditions -/

theorem hasMultidegree_subst (a : K) {b : K} (hb : b ≠ 0) {N M : Matrix (Fin n) (Fin n) K}
    {τ : Nat.Partition n} {d : ℕ → ℕ} (h : HasMultidegree N M τ d) :
    HasMultidegree (N + a • M) (b • M) τ d := by
  intro k hk
  obtain ⟨e₀, he₀⟩ := h k hk
  refine ⟨e₀, fun e he => ?_⟩
  rw [finrank_kerPiece_subst a hb]
  exact he₀ e he

theorem genericType_subst (a : K) {b : K} (hb : b ≠ 0) {N M : Matrix (Fin n) (Fin n) K}
    {τ : Nat.Partition n} (h : GenericType N M τ) : GenericType (N + a • M) (b • M) τ := by
  classical
  obtain ⟨F, hF⟩ := h
  refine ⟨F.image fun s => (s - a) / b, fun t ht => ?_⟩
  have hmem : a + t * b ∉ F := by
    intro hin
    exact ht (Finset.mem_image.mpr ⟨a + t * b, hin, by field_simp; ring⟩)
  have hEq : (N + a • M) + t • (b • M) = N + (a + t * b) • M := by
    rw [smul_smul]
    module
  rw [hEq]
  exact hF _ hmem

theorem nilpotentPencil_subst (a b : K) {N M : Matrix (Fin n) (Fin n) K}
    (h : NilpotentPencil N M) : NilpotentPencil (N + a • M) (b • M) := by
  have := h.linearCombination 1 a 0 b
  simpa using this

/-- `pencilLocus` is stable under `(N, M) ↦ (N + a M, b M)`, `b ≠ 0`. -/
theorem pencilLocus_subst (a : K) {b : K} (hb : b ≠ 0) {τ : Nat.Partition n} {d : ℕ → ℕ}
    {N M : Matrix (Fin n) (Fin n) K} (h : (N, M) ∈ pencilLocus τ d) :
    (N + a • M, b • M) ∈ pencilLocus τ d :=
  ⟨nilpotentPencil_subst a b h.1, genericType_subst a hb h.2.1,
    hasMultidegree_subst a hb h.2.2⟩

/-- `markedLocus` is stable under the reparametrisation action of the
affine group of the line. -/
theorem markedLocus_subst (a : K) {b : K} (hb : b ≠ 0) {τ : Nat.Partition n} {d : ℕ → ℕ}
    {N₀ : Matrix (Fin n) (Fin n) K}
    {q : Matrix (Fin n) (Fin n) K × Matrix (Fin n) (Fin n) K × K × K}
    (h : q ∈ markedLocus τ d N₀) :
    (q.1 + a • q.2.1, b • q.2.1, (q.2.2.1 - a) / b, (q.2.2.2 - a) / b) ∈ markedLocus τ d N₀ := by
  obtain ⟨hpen, hne, h1, h2⟩ := h
  have key : ∀ t : K, (q.1 + a • q.2.1) + ((t - a) / b) • (b • q.2.1) = q.1 + t • q.2.1 := by
    intro t
    have : ((t - a) / b) • (b • q.2.1) = (t - a) • q.2.1 := by
      rw [smul_smul]
      congr 1
      field_simp
    rw [this]
    module
  refine ⟨pencilLocus_subst a hb hpen, ?_, ?_, ?_⟩
  · intro hcontra
    refine hne ?_
    have h' : q.2.2.1 - a = q.2.2.2 - a := by
      have hmul := congrArg (fun x : K => x * b) hcontra
      simpa [div_mul_cancel₀, hb] using hmul
    have := sub_left_inj.mp h'
    exact this
  · rw [key]; exact h1
  · rw [key]; exact h2

/-! ### The swap `μ ↔ ν`, and the lower shear

The affine group of the line is only half the reparametrisation group of `ℙ¹`:
it fixes the member at infinity up to a scalar, so it cannot move a finite
member of the pencil to infinity.  The missing generator is the swap `μ ↔ ν`,
`Graded.swapAlg`, which exchanges the two members `(N, M) ↦ (M, N)`.  It is
graded (`Graded.swapAlg_mem_Bpiece`) and involutive
(`Graded.swapAlg_swapAlg`), so the argument of the previous section applies to
it verbatim, and conjugating the affine reparametrisation by it gives the
*lower* shear `(N, M) ↦ (N, M + c N)` — the substitution `μ ↦ μ + c ν`,
`ν ↦ ν`, which moves the member at the parameter `c⁻¹` to infinity. -/

theorem map_pencil_pow_swap (N M : Matrix (Fin n) (Fin n) K) (k : ℕ) :
    (pencil N M ^ k).map (Graded.swapAlg K) = pencil M N ^ k := by
  have h : ((Graded.swapAlg K).toAlgHom.mapMatrix :
      Matrix (Fin n) (Fin n) (Graded.Poly K) →ₐ[K] _) (pencil N M ^ k)
      = ((Graded.swapAlg K).toAlgHom.mapMatrix (pencil N M)) ^ k := map_pow _ _ _
  have hswap : (pencil N M).map (Graded.swapAlg K) = pencil M N :=
    Height.Pencil.map_swapHom_pencil N M
  simpa [AlgHom.mapMatrix_apply, hswap] using h

/-- The swap carries the kernel flag of `(N, M)` into that of `(M, N)`. -/
theorem swapVec_mem_kerFlag {N M : Matrix (Fin n) (Fin n) K} {k : ℕ}
    {f : Fin n → Graded.Poly K} (hf : f ∈ Height.Pencil.kerFlag N M k) :
    Graded.swapVec K n f ∈ Height.Pencil.kerFlag M N k := by
  rw [Height.Pencil.mem_kerFlag] at hf ⊢
  funext i
  have h : Graded.swapAlg K (((pencil N M ^ k) *ᵥ f) i) = 0 := by simp [hf]
  rw [Matrix.mulVec_apply_eq_sum] at h
  rw [← map_pencil_pow_swap N M k, Pi.zero_apply, Matrix.mulVec_apply_eq_sum]
  simpa [map_sum] using h

theorem swapVec_mem_kerPiece {N M : Matrix (Fin n) (Fin n) K} {k e : ℕ}
    {f : Fin n → Graded.Poly K} (hf : f ∈ kerPiece N M k e) :
    Graded.swapVec K n f ∈ kerPiece M N k e := by
  rw [← Height.Pencil.sub_kerFlag] at hf ⊢
  exact ⟨swapVec_mem_kerFlag (Submodule.mem_inf.mp hf).1,
    Graded.swapVec_mem_piece (Submodule.mem_inf.mp hf).2⟩

/-- The degree-`e` kernel pieces of `(N, M)` and of `(M, N)` are isomorphic
`K`-vector spaces. -/
noncomputable def kerPieceEquivSwap (N M : Matrix (Fin n) (Fin n) K) (k e : ℕ) :
    kerPiece N M k e ≃ₗ[K] kerPiece M N k e where
  toFun x := ⟨Graded.swapVec K n x.1, swapVec_mem_kerPiece x.2⟩
  invFun y := ⟨Graded.swapVec K n y.1, swapVec_mem_kerPiece y.2⟩
  map_add' _ _ := Subtype.ext (map_add (Graded.swapVec K n) _ _)
  map_smul' _ _ := Subtype.ext (map_smul (Graded.swapVec K n) _ _)
  left_inv _ := Subtype.ext (Graded.swapVec_swapVec _)
  right_inv _ := Subtype.ext (Graded.swapVec_swapVec _)

theorem finrank_kerPiece_swap (N M : Matrix (Fin n) (Fin n) K) (k e : ℕ) :
    Module.finrank K (kerPiece M N k e) = Module.finrank K (kerPiece N M k e) :=
  ((kerPieceEquivSwap N M k e).finrank_eq).symm

theorem hasMultidegree_swap {N M : Matrix (Fin n) (Fin n) K} {τ : Nat.Partition n}
    {d : ℕ → ℕ} (h : HasMultidegree N M τ d) : HasMultidegree M N τ d := by
  intro k hk
  obtain ⟨e₀, he₀⟩ := h k hk
  refine ⟨e₀, fun e he => ?_⟩
  rw [finrank_kerPiece_swap N M]
  exact he₀ e he

/-- **`pencilLocus` is symmetric in the two members of the pencil**: the swap
`μ ↔ ν` is a graded automorphism of `K[μ, ν]`. -/
theorem pencilLocus_swap {τ : Nat.Partition n} {d : ℕ → ℕ}
    {N M : Matrix (Fin n) (Fin n) K} (h : (N, M) ∈ pencilLocus τ d) :
    (M, N) ∈ pencilLocus τ d :=
  ⟨(Height.Steenrod.nilpotentPencil_comm N M).mp h.1, genericType_swap h.2.1,
    hasMultidegree_swap h.2.2⟩

/-- **The lower shear.**  `pencilLocus` is stable under `(N, M) ↦ (N, M + c N)`,
the reparametrisation `μ ↦ μ + c ν`, `ν ↦ ν` of `ℙ¹`, obtained by conjugating
the affine reparametrisation by the swap.  For `c ≠ 0` its member at infinity is
`M + c N = c (N + c⁻¹ M)`, the member of the original pencil at the parameter
`c⁻¹`: this is the reparametrisation that puts a chosen finite member at
infinity. -/
theorem pencilLocus_shear (c : K) {τ : Nat.Partition n} {d : ℕ → ℕ}
    {N M : Matrix (Fin n) (Fin n) K} (h : (N, M) ∈ pencilLocus τ d) :
    (N, M + c • N) ∈ pencilLocus τ d := by
  have h3 := pencilLocus_swap (pencilLocus_subst c (one_ne_zero (α := K)) (pencilLocus_swap h))
  simpa using h3

/-- The rank criterion cutting out `orbitClosure` is invariant under nonzero
scalars: `(a X)^k = a^k X^k` and a nonzero scalar does not change the rank of a
matrix.  This is what lets the *lower* shear move the marked members, which it
only fixes up to a scalar. -/
theorem smul_mem_orbitClosure {N₀ X : Matrix (Fin n) (Fin n) K} {a : K} (ha : a ≠ 0)
    (h : X ∈ orbitClosure N₀) : a • X ∈ orbitClosure N₀ := fun k => by
  rw [smul_pow, Matrix.rank_smul_of_mem_nonZeroDivisors _
    (mem_nonZeroDivisors_of_ne_zero (pow_ne_zero k ha))]
  exact h k

/-- **The marked lower shear.**  `markedLocus` is stable under the lower shear
`(N, M) ↦ (N, M + c N)` once the two marked parameters are moved with it: the
member of the sheared pencil at `t' = t/(1 − c t)` is `(1 − c t)⁻¹ (N + t M)`,
the member of the original pencil at `t` up to a nonzero scalar, and
`orbitClosure` is a rank condition (`smul_mem_orbitClosure`).

The reparametrisation is defined at `t` exactly when `1 − c t ≠ 0`, i.e. when
`t` is not the parameter `c⁻¹` that the shear sends to infinity; the two
hypotheses are that neither marked parameter is that one.  This is the marked
analogue of `pencilLocus_shear`, and the counterpart of `markedLocus_subst` for
the half of the reparametrisation group the affine group is missing. -/
theorem markedLocus_shear (c : K) {τ : Nat.Partition n} {d : ℕ → ℕ}
    {N₀ : Matrix (Fin n) (Fin n) K}
    {q : Matrix (Fin n) (Fin n) K × Matrix (Fin n) (Fin n) K × K × K}
    (h₁ : 1 - c * q.2.2.1 ≠ 0) (h₂ : 1 - c * q.2.2.2 ≠ 0) (h : q ∈ markedLocus τ d N₀) :
    (q.1, q.2.1 + c • q.1, q.2.2.1 / (1 - c * q.2.2.1), q.2.2.2 / (1 - c * q.2.2.2))
      ∈ markedLocus τ d N₀ := by
  obtain ⟨hpen, hne, hm₁, hm₂⟩ := h
  have key : ∀ t : K, 1 - c * t ≠ 0 →
      q.1 + (t / (1 - c * t)) • (q.2.1 + c • q.1) = (1 - c * t)⁻¹ • (q.1 + t • q.2.1) := by
    intro t ht
    have ht' : 1 - t * c ≠ 0 := by rw [mul_comm]; exact ht
    match_scalars <;> field_simp
    all_goals ring
  refine ⟨pencilLocus_shear c hpen, ?_, ?_, ?_⟩
  · intro hcon
    rw [div_eq_div_iff h₁ h₂] at hcon
    exact hne (by linear_combination hcon)
  · rw [key q.2.2.1 h₁]
    exact smul_mem_orbitClosure (inv_ne_zero h₁) hm₁
  · rw [key q.2.2.2 h₂]
    exact smul_mem_orbitClosure (inv_ne_zero h₂) hm₂

/-! ### Conjugation invariance -/

/-- A matrix of scalars, read in `K[μ, ν]`. -/
noncomputable def constMat (g : Matrix (Fin n) (Fin n) K) :
    Matrix (Fin n) (Fin n) (Graded.Poly K) :=
  g.map (MvPolynomial.C : K → Graded.Poly K)

theorem constMat_mul (g h : Matrix (Fin n) (Fin n) K) :
    constMat (g * h) = constMat g * constMat h := by
  ext i j : 2
  simp [constMat, Matrix.mul_apply, map_sum]

@[simp] theorem constMat_one : constMat (1 : Matrix (Fin n) (Fin n) K) = 1 := by
  ext i j : 2
  by_cases hij : i = j <;> simp [constMat, Matrix.one_apply, hij]

theorem pencil_eq_smul (N M : Matrix (Fin n) (Fin n) K) :
    pencil N M = (mu : Graded.Poly K) • constMat N + (nu : Graded.Poly K) • constMat M := by
  ext i j : 2
  simp [pencil, constMat, mul_comm]

theorem pencil_conj (g h N M : Matrix (Fin n) (Fin n) K) :
    pencil (g * N * h) (g * M * h) = constMat g * pencil N M * constMat h := by
  rw [pencil_eq_smul, pencil_eq_smul, constMat_mul, constMat_mul, constMat_mul, constMat_mul]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]

theorem constMat_isUnit (g : (Matrix (Fin n) (Fin n) K)ˣ) :
    constMat (g : Matrix (Fin n) (Fin n) K) * constMat (↑g⁻¹ : Matrix (Fin n) (Fin n) K) = 1 := by
  rw [← constMat_mul]
  simp

theorem constMat_isUnit' (g : (Matrix (Fin n) (Fin n) K)ˣ) :
    constMat (↑g⁻¹ : Matrix (Fin n) (Fin n) K) * constMat (g : Matrix (Fin n) (Fin n) K) = 1 := by
  rw [← constMat_mul]
  simp

theorem pencil_conj_pow (g : (Matrix (Fin n) (Fin n) K)ˣ) (N M : Matrix (Fin n) (Fin n) K)
    (k : ℕ) :
    pencil ((g : Matrix (Fin n) (Fin n) K) * N * (↑g⁻¹ : Matrix (Fin n) (Fin n) K))
        ((g : Matrix (Fin n) (Fin n) K) * M * (↑g⁻¹ : Matrix (Fin n) (Fin n) K)) ^ k
      = constMat (g : Matrix (Fin n) (Fin n) K) * pencil N M ^ k *
          constMat (↑g⁻¹ : Matrix (Fin n) (Fin n) K) := by
  induction k with
  | zero => rw [pow_zero, pow_zero, Matrix.mul_one, constMat_isUnit g]
  | succ k ih =>
      rw [pow_succ, ih, pencil_conj, pow_succ]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (constMat (↑g⁻¹ : Matrix (Fin n) (Fin n) K))
        (constMat (g : Matrix (Fin n) (Fin n) K)), constMat_isUnit' g, Matrix.one_mul]

/-- Multiplication by a constant matrix, as a `K`-linear map of `B^n`. -/
noncomputable def constMulVec (g : Matrix (Fin n) (Fin n) K) :
    (Fin n → Graded.Poly K) →ₗ[K] (Fin n → Graded.Poly K) :=
  ((constMat g).mulVecLin).restrictScalars K

@[simp] theorem constMulVec_apply (g : Matrix (Fin n) (Fin n) K) (f : Fin n → Graded.Poly K) :
    constMulVec g f = constMat g *ᵥ f := rfl

theorem constMulVec_mem_piece {g : Matrix (Fin n) (Fin n) K} {e : ℤ}
    {f : Fin n → Graded.Poly K} (hf : f ∈ (Graded.GradedPresentation.free K (Fin n)).piece e) :
    constMulVec g f ∈ (Graded.GradedPresentation.free K (Fin n)).piece e := by
  rw [(Graded.GradedPresentation.of K _).mem_piece] at hf ⊢
  intro i
  rw [constMulVec_apply, Matrix.mulVec_apply_eq_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  have hC : (MvPolynomial.C (g i j) : Graded.Poly K) ∈ Bpiece K 0 := by
    rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) by norm_num, Bpiece_natCast]
    exact MvPolynomial.isHomogeneous_C (Fin 2) _
  have hmul := Bpiece_smul_Bpiece hC (hf j)
  simpa [constMat] using hmul

theorem constMulVec_mem_kerFlag {g : (Matrix (Fin n) (Fin n) K)ˣ}
    {N M : Matrix (Fin n) (Fin n) K} {k : ℕ} {f : Fin n → Graded.Poly K}
    (hf : f ∈ Height.Pencil.kerFlag N M k) :
    constMulVec (g : Matrix (Fin n) (Fin n) K) f ∈
      Height.Pencil.kerFlag ((g : Matrix (Fin n) (Fin n) K) * N *
          (↑g⁻¹ : Matrix (Fin n) (Fin n) K))
        ((g : Matrix (Fin n) (Fin n) K) * M * (↑g⁻¹ : Matrix (Fin n) (Fin n) K)) k := by
  rw [Height.Pencil.mem_kerFlag] at hf ⊢
  have hm : constMat (g : Matrix (Fin n) (Fin n) K) * pencil N M ^ k *
        constMat (↑g⁻¹ : Matrix (Fin n) (Fin n) K) * constMat (g : Matrix (Fin n) (Fin n) K)
      = constMat (g : Matrix (Fin n) (Fin n) K) * pencil N M ^ k := by
    rw [Matrix.mul_assoc, constMat_isUnit' g, Matrix.mul_one]
  rw [pencil_conj_pow, constMulVec_apply, Matrix.mulVec_mulVec, hm, ← Matrix.mulVec_mulVec, hf,
    Matrix.mulVec_zero]

theorem constMulVec_mem_kerPiece {g : (Matrix (Fin n) (Fin n) K)ˣ}
    {N M : Matrix (Fin n) (Fin n) K} {k e : ℕ} {f : Fin n → Graded.Poly K}
    (hf : f ∈ kerPiece N M k e) :
    constMulVec (g : Matrix (Fin n) (Fin n) K) f ∈
      kerPiece ((g : Matrix (Fin n) (Fin n) K) * N * (↑g⁻¹ : Matrix (Fin n) (Fin n) K))
        ((g : Matrix (Fin n) (Fin n) K) * M * (↑g⁻¹ : Matrix (Fin n) (Fin n) K)) k e := by
  rw [← Height.Pencil.sub_kerFlag] at hf ⊢
  exact ⟨constMulVec_mem_kerFlag (Submodule.mem_inf.mp hf).1,
    constMulVec_mem_piece (Submodule.mem_inf.mp hf).2⟩

theorem conj_inv_left (g : (Matrix (Fin n) (Fin n) K)ˣ) (A : Matrix (Fin n) (Fin n) K) :
    (↑g⁻¹ : Matrix (Fin n) (Fin n) K) *
      ((g : Matrix (Fin n) (Fin n) K) * A * (↑g⁻¹ : Matrix (Fin n) (Fin n) K)) *
      (g : Matrix (Fin n) (Fin n) K) = A := by
  simp [Matrix.mul_assoc]

/-- The degree-`e` kernel pieces of `(N, M)` and of its conjugate agree. -/
noncomputable def kerPieceEquivConj (g : (Matrix (Fin n) (Fin n) K)ˣ)
    (N M : Matrix (Fin n) (Fin n) K) (k e : ℕ) :
    kerPiece N M k e ≃ₗ[K]
      kerPiece ((g : Matrix (Fin n) (Fin n) K) * N * (↑g⁻¹ : Matrix (Fin n) (Fin n) K))
        ((g : Matrix (Fin n) (Fin n) K) * M * (↑g⁻¹ : Matrix (Fin n) (Fin n) K)) k e := by
  refine LinearEquiv.ofLinearMap
    (LinearMap.codRestrict _
      ((constMulVec (g : Matrix (Fin n) (Fin n) K)).comp (Submodule.subtype _))
      (fun x => constMulVec_mem_kerPiece x.2))
    (LinearMap.codRestrict _
      ((constMulVec (↑g⁻¹ : Matrix (Fin n) (Fin n) K)).comp (Submodule.subtype _))
      (fun x => by
        have h := constMulVec_mem_kerPiece (g := g⁻¹) x.2
        simp only [inv_inv] at h
        rwa [conj_inv_left g N, conj_inv_left g M] at h)) ?_ ?_
  · refine LinearMap.ext fun x => Subtype.ext ?_
    show constMat (g : Matrix (Fin n) (Fin n) K) *ᵥ
      (constMat (↑g⁻¹ : Matrix (Fin n) (Fin n) K) *ᵥ (x : Fin n → Graded.Poly K)) = _
    rw [Matrix.mulVec_mulVec, constMat_isUnit g, Matrix.one_mulVec]
    rfl
  · refine LinearMap.ext fun x => Subtype.ext ?_
    show constMat (↑g⁻¹ : Matrix (Fin n) (Fin n) K) *ᵥ
      (constMat (g : Matrix (Fin n) (Fin n) K) *ᵥ (x : Fin n → Graded.Poly K)) = _
    rw [Matrix.mulVec_mulVec, constMat_isUnit' g, Matrix.one_mulVec]
    rfl

theorem hasMultidegree_conj (g : (Matrix (Fin n) (Fin n) K)ˣ) {N M : Matrix (Fin n) (Fin n) K}
    {τ : Nat.Partition n} {d : ℕ → ℕ} (h : HasMultidegree N M τ d) :
    HasMultidegree ((g : Matrix (Fin n) (Fin n) K) * N * (↑g⁻¹ : Matrix (Fin n) (Fin n) K))
      ((g : Matrix (Fin n) (Fin n) K) * M * (↑g⁻¹ : Matrix (Fin n) (Fin n) K)) τ d := by
  intro k hk
  obtain ⟨e₀, he₀⟩ := h k hk
  refine ⟨e₀, fun e he => ?_⟩
  rw [← (kerPieceEquivConj g N M k e).finrank_eq]
  exact he₀ e he

/-! ### Jordan type is conjugation invariant -/

theorem toLin_mul_inv (g : (Matrix (Fin n) (Fin n) K)ˣ) (x : Fin n → K) :
    (Matrix.toLinAlgEquiv' (g : Matrix (Fin n) (Fin n) K))
      ((Matrix.toLinAlgEquiv' (↑g⁻¹ : Matrix (Fin n) (Fin n) K)) x) = x := by
  have h : (Matrix.toLinAlgEquiv' ((g : Matrix (Fin n) (Fin n) K) *
      (↑g⁻¹ : Matrix (Fin n) (Fin n) K)) : (Fin n → K) →ₗ[K] (Fin n → K))
      = (Matrix.toLinAlgEquiv' (g : Matrix (Fin n) (Fin n) K)) *
        (Matrix.toLinAlgEquiv' (↑g⁻¹ : Matrix (Fin n) (Fin n) K)) := map_mul _ _ _
  simp only [Units.mul_inv, map_one] at h
  exact congrArg (fun f : (Fin n → K) →ₗ[K] (Fin n → K) => f x) h.symm

theorem toLin_inv_mul (g : (Matrix (Fin n) (Fin n) K)ˣ) (x : Fin n → K) :
    (Matrix.toLinAlgEquiv' (↑g⁻¹ : Matrix (Fin n) (Fin n) K))
      ((Matrix.toLinAlgEquiv' (g : Matrix (Fin n) (Fin n) K)) x) = x := by
  have h : (Matrix.toLinAlgEquiv' ((↑g⁻¹ : Matrix (Fin n) (Fin n) K) *
      (g : Matrix (Fin n) (Fin n) K)) : (Fin n → K) →ₗ[K] (Fin n → K))
      = (Matrix.toLinAlgEquiv' (↑g⁻¹ : Matrix (Fin n) (Fin n) K)) *
        (Matrix.toLinAlgEquiv' (g : Matrix (Fin n) (Fin n) K)) := map_mul _ _ _
  simp only [Units.inv_mul, map_one] at h
  exact congrArg (fun f : (Fin n → K) →ₗ[K] (Fin n → K) => f x) h.symm

theorem toLin_injective (g : (Matrix (Fin n) (Fin n) K)ˣ) :
    Function.Injective
      (Matrix.toLinAlgEquiv' (g : Matrix (Fin n) (Fin n) K) : (Fin n → K) →ₗ[K] (Fin n → K)) := by
  intro x₁ x₂ hx
  rw [← toLin_inv_mul g x₁, ← toLin_inv_mul g x₂, hx]

theorem ker_toLin_conj (g : (Matrix (Fin n) (Fin n) K)ˣ) (A : Matrix (Fin n) (Fin n) K) :
    LinearMap.ker (Matrix.toLinAlgEquiv' ((g : Matrix (Fin n) (Fin n) K) * A *
        (↑g⁻¹ : Matrix (Fin n) (Fin n) K)))
      = (LinearMap.ker (Matrix.toLinAlgEquiv' A)).map
          (Matrix.toLinAlgEquiv' (g : Matrix (Fin n) (Fin n) K)) := by
  have hconj : (Matrix.toLinAlgEquiv' ((g : Matrix (Fin n) (Fin n) K) * A *
      (↑g⁻¹ : Matrix (Fin n) (Fin n) K)) : (Fin n → K) →ₗ[K] (Fin n → K))
      = (Matrix.toLinAlgEquiv' (g : Matrix (Fin n) (Fin n) K)) *
        (Matrix.toLinAlgEquiv' A) *
        (Matrix.toLinAlgEquiv' (↑g⁻¹ : Matrix (Fin n) (Fin n) K)) := by
    rw [← map_mul, ← map_mul]
  ext y
  constructor
  · intro hy
    rw [LinearMap.mem_ker, hconj] at hy
    have hy' : (Matrix.toLinAlgEquiv' A)
        ((Matrix.toLinAlgEquiv' (↑g⁻¹ : Matrix (Fin n) (Fin n) K)) y) = 0 := by
      refine toLin_injective g ?_
      simpa [Module.End.mul_apply] using hy
    exact Submodule.mem_map.mpr ⟨_, LinearMap.mem_ker.mpr hy', toLin_mul_inv g y⟩
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
    rw [LinearMap.mem_ker, hconj]
    simp only [Module.End.mul_apply, toLin_inv_mul g x]
    rw [LinearMap.mem_ker.mp hx, map_zero]

theorem finrank_ker_toLin_conj (g : (Matrix (Fin n) (Fin n) K)ˣ) (A : Matrix (Fin n) (Fin n) K) :
    Module.finrank K (LinearMap.ker (Matrix.toLinAlgEquiv'
        ((g : Matrix (Fin n) (Fin n) K) * A * (↑g⁻¹ : Matrix (Fin n) (Fin n) K))))
      = Module.finrank K (LinearMap.ker (Matrix.toLinAlgEquiv' A)) := by
  rw [ker_toLin_conj]
  exact ((Submodule.equivMapOfInjective _ (toLin_injective g) _).finrank_eq).symm

theorem conj_pow (g : (Matrix (Fin n) (Fin n) K)ˣ) (X : Matrix (Fin n) (Fin n) K) (j : ℕ) :
    ((g : Matrix (Fin n) (Fin n) K) * X * (↑g⁻¹ : Matrix (Fin n) (Fin n) K)) ^ j
      = (g : Matrix (Fin n) (Fin n) K) * X ^ j * (↑g⁻¹ : Matrix (Fin n) (Fin n) K) := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [pow_succ, ih, pow_succ]
      simp [Matrix.mul_assoc]

theorem hasType_conj (g : (Matrix (Fin n) (Fin n) K)ˣ) {X : Matrix (Fin n) (Fin n) K}
    {τ : Nat.Partition n} (h : HasType X τ) :
    HasType ((g : Matrix (Fin n) (Fin n) K) * X * (↑g⁻¹ : Matrix (Fin n) (Fin n) K)) τ := by
  intro m hm
  have key : ∀ j : ℕ, Module.finrank K (LinearMap.ker
      ((Matrix.toLinAlgEquiv' ((g : Matrix (Fin n) (Fin n) K) * X *
        (↑g⁻¹ : Matrix (Fin n) (Fin n) K))) ^ j))
      = Module.finrank K (LinearMap.ker ((Matrix.toLinAlgEquiv' X) ^ j)) := by
    intro j
    rw [← map_pow, ← map_pow, conj_pow g X j]
    exact finrank_ker_toLin_conj g (X ^ j)
  rw [← h m hm]
  unfold Height.Toolbox.conj
  rw [key m, key (m - 1)]

theorem genericType_conj (g : (Matrix (Fin n) (Fin n) K)ˣ) {N M : Matrix (Fin n) (Fin n) K}
    {τ : Nat.Partition n} (h : GenericType N M τ) :
    GenericType ((g : Matrix (Fin n) (Fin n) K) * N * (↑g⁻¹ : Matrix (Fin n) (Fin n) K))
      ((g : Matrix (Fin n) (Fin n) K) * M * (↑g⁻¹ : Matrix (Fin n) (Fin n) K)) τ := by
  obtain ⟨F, hF⟩ := h
  refine ⟨F, fun t ht => ?_⟩
  have hEq : (g : Matrix (Fin n) (Fin n) K) * N * (↑g⁻¹ : Matrix (Fin n) (Fin n) K) +
      t • ((g : Matrix (Fin n) (Fin n) K) * M * (↑g⁻¹ : Matrix (Fin n) (Fin n) K))
      = (g : Matrix (Fin n) (Fin n) K) * (N + t • M) * (↑g⁻¹ : Matrix (Fin n) (Fin n) K) := by
    simp [Matrix.mul_add, Matrix.add_mul]
  rw [hEq]
  exact hasType_conj g (hF t ht)

theorem rank_pow_conj (g : (Matrix (Fin n) (Fin n) K)ˣ) (X : Matrix (Fin n) (Fin n) K) (k : ℕ) :
    Matrix.rank (((g : Matrix (Fin n) (Fin n) K) * X * (↑g⁻¹ : Matrix (Fin n) (Fin n) K)) ^ k)
      = Matrix.rank (X ^ k) := by
  have hdet : IsUnit ((g : Matrix (Fin n) (Fin n) K)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit
  have hdet' : IsUnit ((↑g⁻¹ : Matrix (Fin n) (Fin n) K)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (g⁻¹).isUnit
  rw [conj_pow g X k, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hdet',
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ hdet]

/-- `pencilLocus` is stable under simultaneous conjugation. -/
theorem pencilLocus_conj (g : (Matrix (Fin n) (Fin n) K)ˣ) {τ : Nat.Partition n} {d : ℕ → ℕ}
    {N M : Matrix (Fin n) (Fin n) K} (h : (N, M) ∈ pencilLocus τ d) :
    ((g : Matrix (Fin n) (Fin n) K) * N * (↑g⁻¹ : Matrix (Fin n) (Fin n) K),
      (g : Matrix (Fin n) (Fin n) K) * M * (↑g⁻¹ : Matrix (Fin n) (Fin n) K)) ∈
      pencilLocus τ d := by
  refine ⟨?_, genericType_conj g h.2.1, hasMultidegree_conj g h.2.2⟩
  exact (nilpotentPencil_conjugate_iff (g : Matrix (Fin n) (Fin n) K)
    (↑g⁻¹ : Matrix (Fin n) (Fin n) K) N M (by simp) (by simp)).2 h.1

end Height.Chain
