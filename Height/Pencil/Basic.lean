import Mathlib.LinearAlgebra.Matrix.Rank
import Height.Steenrod.Partner
import Height.Toolbox.Jordan
import Height.Graded.Free
import Height.Graded.ProjectiveLine
import Mathlib.Data.ZMod.Basic

/-!
# The pencil model: `μN + νM`, its loci, and its kernel flag

This file owns the pencil `pencil N M = μN + νM` (over any commutative ring),
its affine chart `pencilPoly N M = N + tM`, the numerical invariants of a
partition (`conjPart`, `mk`, `cType`), the type and multidegree of a pencil
(`HasType`, `GenericType`, `HasMultidegree`), and the loci `pencilLocus`
(`Î_{τ,d}`) and `markedLocus` (`Ŷ`) whose dimensions `Chain/Incidence.lean`
bounds `Chain.PencilIncidenceBound` and `Chain.MarkedIncidenceBound` measure.
Nothing here imports `Height.Chain`.

The paper, `lem:kernel-flag` and the display defining `\Fl_{\tau'}`.

The pencil is `pencil N M = μN + νM`, a matrix over `B = Graded.Poly K`
whose entries are homogeneous of degree `1` (`pencil_mem_Bpiece`).  Its kernel
flag is

```
kerFlag N M k := LinearMap.ker ((pencil N M ^ k).mulVecLin) ⊆ (Fin n → Graded.Poly K),
```

a graded (`isGraded_kerFlag`, for the shift vector `0`) and saturated
(`saturated_kerFlag`) `B`-submodule of `B^n`, whose degree-`e` pieces are the
`kerPiece` (`sub_kerFlag`).  So
`HasMultidegree` is a statement about this flag, and
`Graded.saturated_free` applies to it.

The counts: this file adds `dimFl τ = (n² − c(τ))/2` together with `two_dimFl`, the exactness of the
halving.  The parity input is `sum_conjPart` (`∑_{m=1}^n τ'_m = n`) plus
`x² ≡ x (mod 2)`.

Drop points are the points of `ℙ¹` where the type of the member drops; in the
charts of `Pencil/Chart.lean` the parameter is `t = ν/μ`, so the member at `t₀` is
`N + t₀ M` (`GenericType` uses the same convention) and the point at
infinity carries the member `M`.
-/

namespace Height.Pencil

open Matrix Height.Graded Height.Toolbox Height.Steenrod

/-! ### The pencil and its affine chart -/

section Model

variable {A : Type*} [CommRing A] {n : ℕ}

/-- The pencil `P = μ N + ν M` as a matrix over `B = Graded.Poly A`. -/
noncomputable def pencil (N M : Matrix (Fin n) (Fin n) A) :
    Matrix (Fin n) (Fin n) (Graded.Poly A) :=
  Matrix.of fun i j => MvPolynomial.C (N i j) * mu + MvPolynomial.C (M i j) * nu

/-- **Nilpotence of the pencil passes to every member.**  Substituting
`(μ, ν) ↦ (1, t)` is a ring map, so a power of the pencil that vanishes gives
the same power of `N + t M` vanishing — for `t` anywhere in the base ring, which
is what the arc layer needs (`t` a power series). -/
theorem member_pow_eq_zero {N M : Matrix (Fin n) (Fin n) A} {t : A} {k : ℕ}
    (h : (pencil N M) ^ k = 0) : (N + t • M) ^ k = 0 := by
  set φ : Graded.Poly A →+* A := MvPolynomial.eval₂Hom (RingHom.id A) ![1, t] with hφ
  have hmap : (pencil N M).map φ = N + t • M := by
    ext i j
    show MvPolynomial.eval₂ (RingHom.id A) ![1, t]
      (MvPolynomial.C (N i j) * Graded.mu + MvPolynomial.C (M i j) * Graded.nu) = _
    simp [Graded.mu, Graded.nu, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, mul_comm]
  have hpow : ((pencil N M) ^ k).map φ = ((pencil N M).map φ) ^ k := by
    show φ.mapMatrix ((pencil N M) ^ k) = _
    rw [map_pow]
    rfl
  rw [← hmap, ← hpow, h, Matrix.map_zero _ (map_zero _)]

/-- The affine pencil `N + t M`: the pencil in the chart `μ = 1`, as a matrix
over `A[t]`. -/
noncomputable def pencilPoly (N M : Matrix (Fin n) (Fin n) A) :
    Matrix (Fin n) (Fin n) (Polynomial A) :=
  Matrix.of fun i j => Polynomial.C (N i j) + Polynomial.X * Polynomial.C (M i j)

@[simp] theorem pencilPoly_apply (N M : Matrix (Fin n) (Fin n) A) (i j : Fin n) :
    pencilPoly N M i j = Polynomial.C (N i j) + Polynomial.X * Polynomial.C (M i j) := rfl

theorem pencilPoly_map {B : Type*} [CommRing B] (ψ : A →+* B) (N M : Matrix (Fin n) (Fin n) A) :
    (pencilPoly N M).map (Polynomial.map ψ) = pencilPoly (N.map ψ) (M.map ψ) := by
  refine Matrix.ext fun i j => ?_
  show Polynomial.map ψ (pencilPoly N M i j) = _
  simp

theorem natDegree_pencilPoly_le (N M : Matrix (Fin n) (Fin n) A) (i j : Fin n) :
    (pencilPoly N M i j).natDegree ≤ 1 := by
  rw [pencilPoly_apply]
  refine le_trans (Polynomial.natDegree_add_le _ _) ?_
  rw [Polynomial.natDegree_C]
  refine max_le (Nat.zero_le _) ?_
  exact Polynomial.natDegree_mul_le_of_le Polynomial.natDegree_X_le
    (le_of_eq (Polynomial.natDegree_C _))

end Model

/-! ### Types, multidegrees, and the loci -/

variable {K : Type*} [Field K] {n : ℕ}

/-- `τ'_m`, the `m`-th part of the conjugate partition (`m ≥ 1`). -/
def conjPart (τ : Nat.Partition n) (m : ℕ) : ℕ :=
  (τ.parts.filter fun a => m ≤ a).card

/-- `m_k(τ) = τ'_1 + ⋯ + τ'_k`, the generic kernel dimension of `P^k`. -/
def mk (τ : Nat.Partition n) (k : ℕ) : ℕ :=
  ∑ m ∈ Finset.Icc 1 k, conjPart τ m

/-- `c(τ) = Σ_j (τ'_j)²`, the centralizer dimension of type `τ`. -/
def cType (τ : Nat.Partition n) : ℕ :=
  ∑ m ∈ Finset.Icc 1 n, (conjPart τ m) ^ 2

/-- `X` has Jordan type `τ`. -/
def HasType (X : Matrix (Fin n) (Fin n) K) (τ : Nat.Partition n) : Prop :=
  ∀ m, 1 ≤ m → conj (Matrix.toLinAlgEquiv' X) m = conjPart τ m

/-- The pencil `μN + νM` has generic type `τ`: all but finitely many members
`N + tM` have type `τ`. -/
def GenericType (N M : Matrix (Fin n) (Fin n) K) (τ : Nat.Partition n) : Prop :=
  ∃ F : Finset K, ∀ t ∉ F, HasType (N + t • M) τ

/-- The degree-`e` piece of the kernel flag: `{v ∈ (B^n)_e : P^k v = 0}`, with
`B^n = ⨁_{Fin n} B` the untwisted graded presentation
(`Graded.GradedPresentation.free`). -/
noncomputable def kerPiece (N M : Matrix (Fin n) (Fin n) K) (k e : ℕ) :
    Submodule K (Fin n → Graded.Poly K) :=
  LinearMap.ker ((pencil N M ^ k).mulVecLin.restrictScalars K) ⊓
    (Graded.GradedPresentation.free K (Fin n)).piece (e : ℤ)

/-- The kernel flag of the pencil has multidegree `d`: `dim (S_k)_e = m_k (e+1) - d_k`
for `e ≫ 0` (`lem:degree`; `S_k` is graded free of rank `m_k` and degree `-d_k`). -/
def HasMultidegree (N M : Matrix (Fin n) (Fin n) K) (τ : Nat.Partition n) (d : ℕ → ℕ) : Prop :=
  ∀ k, 1 ≤ k → ∃ e₀, ∀ e, e₀ ≤ e →
    Module.finrank K (kerPiece N M k e) + d k = mk τ k * (e + 1)

/-- `Î_{τ,d}` as a set of pairs: nilpotent pencils of generic type `τ` and
multidegree `d`. -/
def pencilLocus (τ : Nat.Partition n) (d : ℕ → ℕ) :
    Set (Matrix (Fin n) (Fin n) K × Matrix (Fin n) (Fin n) K) :=
  {p | NilpotentPencil p.1 p.2 ∧ GenericType p.1 p.2 τ ∧ HasMultidegree p.1 p.2 τ d}

/-- The closure of the orbit of `N₀`, by the rank conditions. -/
def orbitClosure (N₀ : Matrix (Fin n) (Fin n) K) : Set (Matrix (Fin n) (Fin n) K) :=
  {X | ∀ k, Matrix.rank (X ^ k) ≤ Matrix.rank (N₀ ^ k)}


/-- **The centraliser dimension increases along a degeneration**: a member of
`orbitClosure N₀` has `c` at least that of `N₀`.

`orbitClosure` is the rank criterion, not a topological closure, so this is
combinatorics and not semicontinuity: the ranks bound the kernels, the kernels
are the partial sums of the conjugate partition, and the conjugate partition of
`X` therefore majorizes that of `N₀` — `Toolbox.cOf_le_of_rank_le`.

This is `D ≤ D_x` of `thm:h2-conditional` once `DX_add_cType` converts `c` into
the local torsion count (`Pencil/Realized.lean`). -/
theorem cOf_le_of_mem_orbitClosure {N₀ X : Matrix (Fin n) (Fin n) K}
    (hN₀ : IsNilpotent N₀) (hX : IsNilpotent X) (h : X ∈ orbitClosure N₀) :
    cOf N₀ ≤ cOf X :=
  cOf_le_of_rank_le hX hN₀ h
/-- `N₀` lies in the closure of the orbit of type `τ` (`λ ⊴ τ`). -/
def IsDegeneration (τ : Nat.Partition n) (N₀ : Matrix (Fin n) (Fin n) K) : Prop :=
  ∀ k, 1 ≤ k → Matrix.rank (N₀ ^ k) + mk τ k ≤ n

/-- `Ŷ` (finite part): pencils in `Î_{τ,d}` with two distinct parameters at
which the member lies in the closure of the orbit of `N₀`. -/
def markedLocus (τ : Nat.Partition n) (d : ℕ → ℕ) (N₀ : Matrix (Fin n) (Fin n) K) :
    Set (Matrix (Fin n) (Fin n) K × Matrix (Fin n) (Fin n) K × K × K) :=
  {q | (q.1, q.2.1) ∈ pencilLocus τ d ∧ q.2.2.1 ≠ q.2.2.2 ∧
    q.1 + q.2.2.1 • q.2.1 ∈ orbitClosure N₀ ∧ q.1 + q.2.2.2 • q.2.1 ∈ orbitClosure N₀}

/-- Dehomogenising the pencil `μ N + ν M` gives the polynomial pencil `N + t M`. -/
theorem map_deh_pencil (N M : Matrix (Fin n) (Fin n) K) :
    (pencil N M).map (Graded.deh K).toRingHom = pencilPoly N M := by
  refine Matrix.ext fun i j => ?_
  show Graded.deh K (pencil N M i j) = pencilPoly N M i j
  simp only [pencil, pencilPoly, Matrix.of_apply, map_add, map_mul, Graded.deh_C, Graded.deh_mu,
    Graded.deh_nu, mul_one]
  ring

theorem pencilPoly_map_eval (A B : Matrix (Fin n) (Fin n) K) (t : K) :
    (pencilPoly A B).map (Polynomial.evalRingHom t) = A + t • B := by
  ext i j
  simp [pencilPoly, Matrix.add_apply, Matrix.smul_apply]
  ring

theorem det_submatrix_pencilPoly_eval {k : ℕ} (A B : Matrix (Fin n) (Fin n) K)
    (f g : Fin k → Fin n) (m : ℕ) (t : K) :
    Polynomial.eval t (((pencilPoly A B ^ m).submatrix f g).det)
      = (((A + t • B) ^ m).submatrix f g).det := by
  have hpow : (pencilPoly A B ^ m).map (Polynomial.evalRingHom t) = (A + t • B) ^ m := by
    have hmp := map_pow ((Polynomial.evalRingHom t).mapMatrix (m := Fin n)) (pencilPoly A B) m
    rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply] at hmp
    rw [hmp, pencilPoly_map_eval]
  calc Polynomial.eval t (((pencilPoly A B ^ m).submatrix f g).det)
      = (((pencilPoly A B ^ m).submatrix f g).map (Polynomial.evalRingHom t)).det :=
        RingHom.map_det (Polynomial.evalRingHom t) _
    _ = (((pencilPoly A B ^ m).map (Polynomial.evalRingHom t)).submatrix f g).det := by
        rw [Matrix.submatrix_map]
    _ = (((A + t • B) ^ m).submatrix f g).det := by rw [hpow]


/-! ### The entries of `P ^ k` are homogeneous of degree `k` -/

theorem pencil_mem_Bpiece (N M : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    pencil N M i j ∈ Bpiece K 1 := by
  have hmu : (mu : Graded.Poly K) ∈ Bpiece K 1 := by
    rw [show (1 : ℤ) = ((1 : ℕ) : ℤ) by norm_num, Bpiece_natCast]
    exact MvPolynomial.isHomogeneous_X K 0
  have hnu : (nu : Graded.Poly K) ∈ Bpiece K 1 := by
    rw [show (1 : ℤ) = ((1 : ℕ) : ℤ) by norm_num, Bpiece_natCast]
    exact MvPolynomial.isHomogeneous_X K 1
  have hC : ∀ a : K, (MvPolynomial.C a : Graded.Poly K) ∈ Bpiece K 0 := by
    intro a
    rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) by norm_num, Bpiece_natCast]
    exact MvPolynomial.isHomogeneous_C (Fin 2) a
  have h1 : (MvPolynomial.C (N i j) * mu : Graded.Poly K) ∈ Bpiece K 1 := by
    simpa using Bpiece_smul_Bpiece (hC (N i j)) hmu
  have h2 : (MvPolynomial.C (M i j) * nu : Graded.Poly K) ∈ Bpiece K 1 := by
    simpa using Bpiece_smul_Bpiece (hC (M i j)) hnu
  exact Submodule.add_mem _ h1 h2

theorem pencil_pow_mem_Bpiece (N M : Matrix (Fin n) (Fin n) K) (k : ℕ) (i j : Fin n) :
    (pencil N M ^ k) i j ∈ Bpiece K (k : ℤ) := by
  induction k generalizing i j with
  | zero =>
      rw [pow_zero, Nat.cast_zero, show (0 : ℤ) = ((0 : ℕ) : ℤ) by norm_num,
        Bpiece_natCast]
      by_cases h : i = j
      · simp only [Matrix.one_apply, h, ite_true]
        exact MvPolynomial.isHomogeneous_one _ _
      · simp only [Matrix.one_apply, h, ite_false]
        exact Submodule.zero_mem _
  | succ k ih =>
      rw [pow_succ, Matrix.mul_apply]
      refine Submodule.sum_mem _ fun l _ => ?_
      have := Bpiece_smul_Bpiece (ih i l) (pencil_mem_Bpiece N M l j)
      rwa [show (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) by push_cast; ring] at this

/-! ### The kernel flag -/

/-- `S_k = ker (P^k : B^n → B(k)^n)`, the `k`-th step of the kernel flag of the
pencil `P = μN + νM` (`lem:kernel-flag`). -/
noncomputable def kerFlag (N M : Matrix (Fin n) (Fin n) K) (k : ℕ) :
    Submodule (Graded.Poly K) (Fin n → Graded.Poly K) :=
  LinearMap.ker ((pencil N M ^ k).mulVecLin)

theorem mem_kerFlag {N M : Matrix (Fin n) (Fin n) K} {k : ℕ} {f : Fin n → Graded.Poly K} :
    f ∈ kerFlag N M k ↔ (pencil N M ^ k) *ᵥ f = 0 := Iff.rfl

/-- `lem:kernel-flag`(1): the kernel flag is a graded submodule of `B^n`. -/
theorem isGraded_kerFlag (N M : Matrix (Fin n) (Fin n) K) (k : ℕ) :
    (Graded.GradedPresentation.free K (Fin n)).IsGraded (kerFlag N M k) := by
  intro f hf e
  rw [mem_kerFlag] at hf ⊢
  funext i
  have hf' : ∑ j, (pencil N M ^ k) i j * f j = 0 := congrFun hf i
  show ∑ j, (pencil N M ^ k) i j *
      ((Graded.GradedPresentation.free K (Fin n)).proj e f) j = 0
  have hstep : ∀ j : Fin n,
      (pencil N M ^ k) i j * ((Graded.GradedPresentation.free K (Fin n)).proj e f) j
        = Bproj (e + (k : ℤ)) ((pencil N M ^ k) i j * f j) := by
    intro j
    rw [Graded.GradedPresentation.proj_apply, sub_zero,
      mul_comm ((pencil N M ^ k) i j) (Bproj e (f j)),
      mul_comm ((pencil N M ^ k) i j) (f j)]
    exact (Bproj_smul_of_mem (d := e) (f j) (pencil_pow_mem_Bpiece N M k i j)).symm
  rw [Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => hstep j, ← map_sum, hf',
    map_zero]

/-- `lem:kernel-flag`(1): the kernel flag is saturated, since `B^n / S_k` embeds
in `B^n` through `P^k` and `B` is a domain. -/
theorem saturated_kerFlag (N M : Matrix (Fin n) (Fin n) K) (k : ℕ)
    (g : Graded.Poly K) (x : Fin n → Graded.Poly K) (hg : g ≠ 0) (hx : g • x ∈ kerFlag N M k) :
    x ∈ kerFlag N M k := by
  rw [mem_kerFlag] at hx ⊢
  rw [Matrix.mulVec_smul] at hx
  funext i
  have h : g * ((pencil N M ^ k) *ᵥ x) i = 0 := congrFun hx i
  exact (mul_eq_zero.mp h).resolve_left hg

/-- The degree-`e` piece of the kernel flag is `kerPiece`; so
`HasMultidegree` is a statement about `kerFlag`. -/
theorem sub_kerFlag (N M : Matrix (Fin n) (Fin n) K) (k e : ℕ) :
    (Graded.GradedPresentation.free K (Fin n)).sub (kerFlag N M k) (e : ℤ)
      = kerPiece N M k e := rfl

/-- `lem:kernel-flag`(2): `P S_k ⊆ S_{k-1}(1)`. -/
theorem pencil_mulVec_mem_kerFlag (N M : Matrix (Fin n) (Fin n) K) (k : ℕ)
    (f : Fin n → Graded.Poly K) (hf : f ∈ kerFlag N M (k + 1)) :
    (pencil N M) *ᵥ f ∈ kerFlag N M k := by
  rw [mem_kerFlag] at hf ⊢
  rw [Matrix.mulVec_mulVec, ← pow_succ, hf]

/-! ### The flag dimension `dim Fl_{τ'} = (n² − c(τ))/2` -/

/-- `∑_{m=1}^{n} τ'_m = n`: the conjugate partition has the same size. -/
theorem sum_conjPart (τ : Nat.Partition n) :
    ∑ m ∈ Finset.Icc 1 n, conjPart τ m = n := by
  classical
  have key : ∀ s : Multiset ℕ, (∀ a ∈ s, a ≤ n) →
      ∑ m ∈ Finset.Icc 1 n, (s.filter fun a => m ≤ a).card = s.sum := by
    intro s
    induction s using Multiset.induction with
    | empty => simp
    | cons a s ih =>
        intro h
        have ha : a ≤ n := h a (Multiset.mem_cons_self a s)
        have hs : ∀ b ∈ s, b ≤ n := fun b hb => h b (Multiset.mem_cons_of_mem hb)
        have hcard : ∀ m : ℕ, ((a ::ₘ s).filter fun x => m ≤ x).card
            = (if m ≤ a then 1 else 0) + (s.filter fun x => m ≤ x).card := by
          intro m
          by_cases hm : m ≤ a
          · simp [Multiset.filter_cons_of_pos _ hm, hm, Nat.add_comm]
          · simp [Multiset.filter_cons_of_neg _ hm, hm]
        rw [Finset.sum_congr rfl fun m (_ : m ∈ Finset.Icc 1 n) => hcard m,
          Finset.sum_add_distrib, ih hs, Multiset.sum_cons]
        congr 1
        have hfil : ((Finset.Icc 1 n).filter fun m => m ≤ a) = Finset.Icc 1 a := by
          ext m
          simp only [Finset.mem_filter, Finset.mem_Icc]
          omega
        have hb : ∑ m ∈ Finset.Icc 1 n, (if m ≤ a then 1 else 0)
            = ((Finset.Icc 1 n).filter fun m => m ≤ a).card := by
          rw [Finset.card_filter]
        rw [hb, hfil, Nat.card_Icc]
        omega
  have h := key τ.parts fun a ha => Nat.Partition.le_of_mem_parts ha
  rw [τ.parts_sum] at h
  exact h

/-- `c(τ) ≤ n²`. -/
theorem cType_le (τ : Nat.Partition n) : cType τ ≤ n * n := by
  have hsum := sum_conjPart τ
  calc cType τ = ∑ m ∈ Finset.Icc 1 n, conjPart τ m * conjPart τ m := by
        simp only [cType, pow_two]
    _ ≤ ∑ m ∈ Finset.Icc 1 n, conjPart τ m * n := by
        refine Finset.sum_le_sum fun m hm => Nat.mul_le_mul_left _ ?_
        calc conjPart τ m ≤ ∑ m' ∈ Finset.Icc 1 n, conjPart τ m' :=
              Finset.single_le_sum (fun _ _ => Nat.zero_le _) hm
          _ = n := hsum
    _ = n * n := by rw [← Finset.sum_mul, hsum]

/-- `c(τ) ≡ n (mod 2)`, because `x² ≡ x`. -/
theorem cType_even_iff (τ : Nat.Partition n) : Even (cType τ) ↔ Even n := by
  have hcast : ((cType τ : ℕ) : ZMod 2) = ((n : ℕ) : ZMod 2) := by
    conv_rhs => rw [← sum_conjPart τ]
    rw [cType, Nat.cast_sum, Nat.cast_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Nat.cast_pow]
    exact ZMod.pow_card _
  rw [← ZMod.natCast_eq_zero_iff_even, ← ZMod.natCast_eq_zero_iff_even, hcast]

/-- `dim Fl_{τ'} = (n² − c(τ))/2`, half the dimension of the orbit of type
`τ` (`\Fl_{\tau'}` of the paper). -/
def dimFl (τ : Nat.Partition n) : ℕ := (n * n - cType τ) / 2

/-- The halving in `dimFl` is exact. -/
theorem two_dimFl (τ : Nat.Partition n) : 2 * dimFl τ = n * n - cType τ := by
  have hle := cType_le τ
  have heven : Even (n * n - cType τ) := by
    rw [Nat.even_sub hle]
    constructor
    · intro h
      exact (cType_even_iff τ).2 ((Nat.even_mul.mp h).elim id id)
    · intro h
      exact Nat.even_mul.mpr (Or.inl ((cType_even_iff τ).1 h))
  obtain ⟨c, hc⟩ := heven
  rw [dimFl, hc]
  omega

/-! ### Rescaling and swapping the two members -/

/-- The Jordan type is invariant under rescaling by a nonzero scalar: the
kernels of the powers of `cX` are those of the powers of `X`. -/
theorem hasType_smul {X : Matrix (Fin n) (Fin n) K} {τ : Nat.Partition n} {c : K}
    (hc : c ≠ 0) : HasType (c • X) τ ↔ HasType X τ := by
  have hpow : ∀ m : ℕ, (c • X) ^ m = c ^ m • X ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
        rw [pow_succ, pow_succ, pow_succ, ih, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hker : ∀ m : ℕ,
      LinearMap.ker ((Matrix.toLinAlgEquiv' (c • X)) ^ m)
        = LinearMap.ker ((Matrix.toLinAlgEquiv' X) ^ m) := by
    intro m
    rw [← map_pow, ← map_pow, hpow m, map_smul]
    exact LinearMap.ker_smul _ _ (pow_ne_zero m hc)
  have hconj : ∀ m, Height.Toolbox.conj (Matrix.toLinAlgEquiv' (c • X)) m
      = Height.Toolbox.conj (Matrix.toLinAlgEquiv' X) m := by
    intro m
    rw [Height.Toolbox.conj, Height.Toolbox.conj, hker m, hker (m - 1)]
  constructor <;> intro h m hm
  · rw [← hconj m]; exact h m hm
  · rw [hconj m]; exact h m hm

/-- **Swapping the two members of a pencil.**  The generic type is a property of
the pencil, not of its parametrisation: for `t ≠ 0` the member `M + tN` of the
swapped pencil is `t (N + t⁻¹ M)`, of the same type by `hasType_smul`, and the
parameter `t = 0` (the member `M`, i.e. the member of the original pencil at
infinity) is excluded from the finite exceptional set. -/
theorem genericType_swap {N M : Matrix (Fin n) (Fin n) K} {τ : Nat.Partition n}
    (hgen : GenericType N M τ) : GenericType M N τ := by
  classical
  obtain ⟨F, hF⟩ := hgen
  refine ⟨insert 0 (F.image (fun t => t⁻¹)), fun t ht => ?_⟩
  have h0 : t ≠ 0 := fun hc => ht (by rw [hc]; exact Finset.mem_insert_self 0 _)
  have hinv : t⁻¹ ∉ F := fun hc =>
    ht (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨t⁻¹, hc, inv_inv t⟩))
  have hEq : M + t • N = t • (N + t⁻¹ • M) := by
    rw [smul_add, smul_smul, mul_inv_cancel₀ h0, one_smul]
    abel
  rw [hEq]
  exact (hasType_smul h0).mpr (hF t⁻¹ hinv)

/-! ### Drop points -/

/-- `t₀ : K` is a drop point of the pencil `(N, M)` of generic type `τ`: the
member `N + t₀ M` does not have the generic type.  The parameter convention is
that of `GenericType` (`t = ν/μ`). -/
def IsDropPoint (N M : Matrix (Fin n) (Fin n) K) (t₀ : K) (τ : Nat.Partition n) : Prop :=
  ¬ HasType (N + t₀ • M) τ

/-- Off a finite set there are no drop points. -/
theorem finite_dropPoints {N M : Matrix (Fin n) (Fin n) K} {τ : Nat.Partition n}
    (h : GenericType N M τ) : ∃ F : Finset K, ∀ t₀ ∉ F, ¬ IsDropPoint N M t₀ τ := by
  obtain ⟨F, hF⟩ := h
  exact ⟨F, fun t₀ ht₀ => not_not_intro (hF t₀ ht₀)⟩


/-- The swap `μ ↔ ν` exchanges the two members of a pencil. -/
theorem map_swapHom_pencil {K : Type*} [Field K] {n : ℕ} (N M : Matrix (Fin n) (Fin n) K) :
    (pencil N M).map (Graded.swapHom K) = pencil M N := by
  have hC : ∀ a : K,
      Graded.swapAlg K (MvPolynomial.C a : Graded.Poly K) = MvPolynomial.C a :=
    fun a => by rw [Graded.swapAlg_apply, MvPolynomial.rename_C]
  refine Matrix.ext fun i j => ?_
  show Graded.swapAlg K (pencil N M i j) = pencil M N i j
  simp only [pencil, Matrix.of_apply, map_add, map_mul, Graded.swapAlg_mu, Graded.swapAlg_nu,
    hC]
  ring

end Height.Pencil
