import Height.Pencil.Torsion
import Height.Geometry.Dimension.Affine
import Height.Toolbox.MinorRank
import Height.Toolbox.CentralizerDim
import Height.Graded.Cech
import Height.Graded.LocalLength

/-!
# `lem:local-pairing` in the `c(τ)` form, and the realised bound (`thm:realized-bound`)

The paper, `lem:local-pairing` and `thm:realized-bound`.
-/

namespace Height.Pencil

open Matrix Height.DVR Height.Toolbox Height.Steenrod
open Height.Geometry (affineDim)

universe u

variable {K : Type u} [Field K] {n : ℕ}

/-! ### The generic rank of `ad_P` -/

/-- The centraliser count of a matrix of Jordan type `τ` is `c(τ)`. -/
theorem cOf_eq_cType_of_hasType {X : Matrix (Fin n) (Fin n) K} {τ : Nat.Partition n}
    (h : HasType X τ) : cOf X = cType τ :=
  Finset.sum_congr rfl fun m hm => by rw [h m (Finset.mem_Icc.mp hm).1]

/-- The localised pencil at a finite point is the polynomial pencil of the
member at that point, read as a power series in the uniformizer. -/
theorem Pat_eq_map_pencilPoly (N M : Matrix (Fin n) (Fin n) K) (t₀ : K) :
    Pat N M t₀
      = (pencilPoly (N + t₀ • M) M).map (Polynomial.coeToPowerSeries.ringHom) := by
  rw [Pat_eq_add_smul]
  refine Matrix.ext fun i j => ?_
  show (Matrix.map (N + t₀ • M) (PowerSeries.C : K →+* PowerSeries K)) i j
      + (PowerSeries.X : PowerSeries K) • dPat M i j
    = Polynomial.coeToPowerSeries.ringHom (pencilPoly (N + t₀ • M) M i j)
  have hp : pencilPoly (N + t₀ • M) M i j
      = Polynomial.C ((N + t₀ • M) i j) + Polynomial.X * Polynomial.C (M i j) := by
    show (Matrix.map (N + t₀ • M) (fun a => (Polynomial.C a : Polynomial K))) i j
        + (Polynomial.X : Polynomial K) •
            (Matrix.map M (fun a => (Polynomial.C a : Polynomial K))) i j = _
    simp [Matrix.map_apply, Matrix.smul_apply]
  rw [hp]
  simp only [map_add, map_mul, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coe_C, Polynomial.coe_X, Matrix.map_apply, dPat_apply, smul_eq_mul]

/-- The `t`-specialisation of `ad` of the polynomial pencil. -/
theorem adMat_pencilPoly_map_eval (A B : Matrix (Fin n) (Fin n) K) (t : K) :
    (adMat (pencilPoly A B)).map (Polynomial.evalRingHom t) = adMat (A + t • B) := by
  rw [← adMat_map, pencilPoly_map_eval]

/-- **The generic rank of `ad_P`.**  For a nilpotent pencil of generic type `τ`
over an infinite field, the rank of `ad_P` at the generic point of `ℙ¹` — read
through *any* injective ring map of `K[t]` into a field `L`, e.g. the chart at
a finite point (`K⸨u⸩`) or the function field itself — is `n² − c(τ)`.

Both bounds are the minor criterion: an `r × r` minor of `ad` of the pencil is
a polynomial in the parameter, nonzero in `L` exactly when it is nonzero
as a polynomial, hence nonzero at all but finitely many members. -/
theorem rank_map_adMat_pencilPoly [Infinite K] {L : Type*} [Field L]
    (Φ : Polynomial K →+* L) (hΦinj : Function.Injective Φ)
    (N M : Matrix (Fin n) (Fin n) K)
    (τ : Nat.Partition n) (t₀ : K) (hnil : NilpotentPencil N M)
    (hgen : GenericType N M τ) :
    ((adMat (pencilPoly (N + t₀ • M) M)).map Φ).rank = n * n - cType τ := by
  classical
  set A : Matrix (Fin (n * n)) (Fin (n * n)) (Polynomial K) :=
    adMat (pencilPoly (N + t₀ • M) M) with hA
  -- the specialisations of `A` are the `ad` of the members
  have heval : ∀ s : K, A.map (Polynomial.evalRingHom s) = adMat (N + (t₀ + s) • M) := by
    intro s
    rw [hA, adMat_pencilPoly_map_eval]
    congr 1
    rw [add_smul, ← add_assoc]
  have hdet : ∀ {k : ℕ} (f g : Fin k → Fin (n * n)) (s : K),
      Polynomial.eval s ((A.submatrix f g).det)
        = ((adMat (N + (t₀ + s) • M)).submatrix f g).det := by
    intro k f g s
    calc Polynomial.eval s ((A.submatrix f g).det)
        = ((A.submatrix f g).map (Polynomial.evalRingHom s)).det :=
          RingHom.map_det (Polynomial.evalRingHom s) _
      _ = ((A.map (Polynomial.evalRingHom s)).submatrix f g).det := by
          rw [Matrix.submatrix_map]
      _ = ((adMat (N + (t₀ + s) • M)).submatrix f g).det := by rw [heval s]
  have hdetΦ : ∀ {k : ℕ} (f g : Fin k → Fin (n * n)),
      ((A.map Φ).submatrix f g).det = Φ ((A.submatrix f g).det) := by
    intro k f g
    rw [Matrix.submatrix_map]
    exact (RingHom.map_det Φ _).symm
  -- the rank at a member of generic type
  obtain ⟨F, hF⟩ := hgen
  have hmem : ∀ t : K, t ∉ F → Matrix.rank (adMat (N + t • M)) = n * n - cType τ := by
    intro t ht
    have hnilt : IsNilpotent (N + t • M) := by
      have h := hnil 1 t
      rwa [one_smul] at h
    have h := rank_adMat_eq (N + t • M) hnilt
    rw [cOf_eq_cType_of_hasType (hF t ht)] at h
    omega
  set badF : Finset K := F.image (fun t => t - t₀) with hbadF
  have hbad : ∀ s : K, s ∉ badF → t₀ + s ∉ F := by
    intro s hs hc
    exact hs (Finset.mem_image.mpr ⟨t₀ + s, hc, by ring⟩)
  refine le_antisymm ?_ ?_
  · -- upper bound: a bigger minor would survive to some member
    by_contra hcon
    rw [Nat.not_le] at hcon
    obtain ⟨f, g, hfg⟩ := Height.Toolbox.exists_submatrix_det_ne_zero (A.map Φ) hcon
    have hP : (A.submatrix f g).det ≠ 0 := by
      intro hz
      rw [hdetΦ f g, hz, map_zero] at hfg
      exact hfg rfl
    obtain ⟨s, hs⟩ :=
      (((badF ∪ (A.submatrix f g).det.roots.toFinset : Finset K) : Set K).toFinite.infinite_compl).nonempty
    simp only [Set.mem_compl_iff, Finset.coe_union, Set.mem_union, Finset.mem_coe,
      not_or] at hs
    have hroot : Polynomial.eval s ((A.submatrix f g).det) ≠ 0 := by
      intro hz
      exact hs.2 (Multiset.mem_toFinset.mpr (Polynomial.mem_roots'.mpr ⟨hP, hz⟩))
    have hne : ((adMat (N + (t₀ + s) • M)).submatrix f g).det ≠ 0 := by
      rw [← hdet f g s]; exact hroot
    have hle := Height.Toolbox.le_rank_of_submatrix_det_ne_zero _ f g hne
    rw [hmem (t₀ + s) (hbad s hs.1)] at hle
    omega
  · -- lower bound: the generic rank is achieved at almost every member
    obtain ⟨s, hs⟩ := (((badF : Finset K) : Set K).toFinite.infinite_compl).nonempty
    have hr := hmem (t₀ + s) (hbad s hs)
    obtain ⟨f₀, g₀, hf₀⟩ := Height.Toolbox.exists_submatrix_det_ne_zero
      (adMat (N + (t₀ + s) • M)) hr.ge
    have hP : (A.submatrix f₀ g₀).det ≠ 0 := by
      intro hz
      apply hf₀
      rw [← hdet f₀ g₀ s, hz, Polynomial.eval_zero]
    refine Height.Toolbox.le_rank_of_submatrix_det_ne_zero _ f₀ g₀ ?_
    rw [hdetΦ f₀ g₀]
    intro hz
    exact hP (hΦinj (by rw [hz, map_zero]))

/-- **`lem:local-pairing`, the `c(τ)` form.**  At a finite point `t₀` of `ℙ¹`,
the number `D_x` of nontrivial invariant factors of `ad_P` is
`c(τ(x)) − c(τ)`, where `τ(x)` is the Jordan type of the member `N + t₀ M`.

`Pencil/Torsion.lean`'s `DX_add_rank` is the corank form; the two ranks are
identified with `n² − c(τ(x))` (`Toolbox/CentralizerDim.lean`'s `rank_adMat_eq`,
rank–nullity plus the Jordan description of the centraliser) and `n² − c(τ)`
(`rank_map_adMat_pencilPoly`).  `[Infinite K]` is necessary: over a finite field
`GenericType N M τ` can hold vacuously for every `τ`. -/
theorem DX_add_cType [Infinite K] (N M : Matrix (Fin n) (Fin n) K)
    (τ : Nat.Partition n) (t₀ : K) (hnil : NilpotentPencil N M)
    (hgen : GenericType N M τ) :
    DX N M t₀ + cType τ = cOf (N + t₀ • M) := by
  have h1 := DX_add_rank N M t₀
  have hcoeinj : Function.Injective
      (Polynomial.coeToPowerSeries.ringHom : Polynomial K →+* PowerSeries K) := by
    intro a b h
    rw [Polynomial.coeToPowerSeries.ringHom_apply,
      Polynomial.coeToPowerSeries.ringHom_apply] at h
    exact Polynomial.coe_injective K h
  have hΦinj : Function.Injective
      ((algebraMap (PowerSeries K) (LaurentSeries K)).comp
        Polynomial.coeToPowerSeries.ringHom) :=
    (IsFractionRing.injective (PowerSeries K) (LaurentSeries K)).comp hcoeinj
  have hmap : (adMat (Pat N M t₀)).map (algebraMap (PowerSeries K) (LaurentSeries K))
      = (adMat (pencilPoly (N + t₀ • M) M)).map
          ((algebraMap (PowerSeries K) (LaurentSeries K)).comp
            Polynomial.coeToPowerSeries.ringHom) := by
    rw [Pat_eq_map_pencilPoly, adMat_map, Matrix.map_map]
    rfl
  have h2 : ((adMat (Pat N M t₀)).map
      (algebraMap (PowerSeries K) (LaurentSeries K))).rank = n * n - cType τ := by
    rw [hmap]
    exact rank_map_adMat_pencilPoly _ hΦinj N M τ t₀ hnil hgen
  have hnil0 : IsNilpotent (N + t₀ • M) := by
    have h := hnil 1 t₀
    rwa [one_smul] at h
  have h3 := rank_adMat_eq (N + t₀ • M) hnil0
  have h4 : cType τ ≤ n * n := cType_le τ
  omega

/-- **`D ≤ D_x` at a marked point.**  The defect `D = c(N₀) − c(τ)` of
`thm:h2-conditional` is at most the local torsion count `D_x` at a point whose
member lies in `orbitClosure N₀`.

`DX_add_cType` turns `D_x` into `c(N + t₀ M) − c(τ)`, and the member being a
degeneration of `N₀` makes its centraliser at least as big
(`cOf_le_of_mem_orbitClosure`).  This is the last input of `length_le` beyond
the two local isotropy bounds. -/
theorem cOf_sub_cType_le_DX [Infinite K] (N M N₀ : Matrix (Fin n) (Fin n) K)
    (τ : Nat.Partition n) (t₀ : K) (hnil : NilpotentPencil N M)
    (hgen : GenericType N M τ) (hN₀ : IsNilpotent N₀)
    (hmem : N + t₀ • M ∈ orbitClosure N₀) :
    cOf N₀ - cType τ ≤ DX N M t₀ := by
  have h1 := DX_add_cType N M τ t₀ hnil hgen
  have hnil0 : IsNilpotent (N + t₀ • M) := by
    have h := hnil 1 t₀
    rwa [one_smul] at h
  have h2 := cOf_le_of_mem_orbitClosure hN₀ hnil0 hmem
  omega


/-! ### `thm:realized-bound`: the dimension of `𝒩` -/

section Realized

open Height.Graded

/-! ### The (H1) count at a tangent-generic point -/

/-- **The count of `thm:h1` and of `thm:h2-conditional`.**  At a
tangent-generic point the class map `α : T → ⊕_x T_x` has isotropic image
(`thm:isotropy`, through `Pencil/Torsion.lean`'s `LocalData.omega_eq_zero`)
and kernel inside `𝒩` up to a slack `s` (`thm:realized-bound`), so

```
dim T + D = dim im α + dim ker α + D ≤ (dim Fl − Σb − D) + D + (2 dim Fl + Σb) + s
          = 3 dim Fl + s .
```

* `hiso` is `thm:isotropy`: the realised classes are isotropic at every drop
  point, hence isotropic for the orthogonal sum `residueSpaceForm E`;
* `hker` is the kernel half of `thm:realized-bound`, with slack `s` (`s = 0`
  for `thm:h1`; `s = 2` for `thm:h2-conditional`, the two parameters
  `ṫ₁, ṫ₂`);
* `hlen` is `lem:selfdual-degree` (`½ Σ_x len_x = dim Fl − Σ b_i`) with the
  drop `D` of `lem:local-pairing` subtracted at the marked points (`D = 0` for
  `thm:h1`; `D = c(λ) − c(τ)` for `thm:h2-conditional`);
* `hN` is the dimension half of `thm:realized-bound`
  (`dim 𝒩 = n² − c(τ) + Σ b_i = 2 dim Fl + Σ b_i`, `two_dimFl`). -/
theorem realized_count {Ξ : Type*} [Fintype Ξ] (E : Ξ → ℕ)
    {T : Type*} [AddCommGroup T] [Module K T] [FiniteDimensional K T]
    (α : T →ₗ[K] Height.DVR.residueBlockSpace K E)
    (hiso : ∀ x ∈ LinearMap.range α, ∀ y ∈ LinearMap.range α,
      Height.DVR.residueSpaceForm E x y = 0)
    (dimN dimFl sumb D s : ℕ)
    (hker : Module.finrank K (LinearMap.ker α) ≤ dimN + s)
    (hlen : (∑ ξ, 2 * E ξ) + 2 * D + 2 * sumb ≤ 2 * dimFl)
    (hN : dimN = 2 * dimFl + sumb) :
    Module.finrank K T + D ≤ 3 * dimFl + s := by
  have hrn : Module.finrank K (LinearMap.range α) + Module.finrank K (LinearMap.ker α)
      = Module.finrank K T := α.finrank_range_add_finrank_ker
  have himg : 2 * Module.finrank K (LinearMap.range α) ≤ ∑ ξ, 2 * E ξ :=
    Height.DVR.residueSpaceForm_isotropic_bound E (LinearMap.range α) hiso
  omega

/-! ### The realised datum

What `realized_count` consumes, packaged once for `thm:h1` (`Chain/H1.lean`)
and `thm:h2-conditional` (`Chain/H2.lean`). -/

/-- The realised-class datum at a tangent-generic point: a subspace `T` of the
ambient coordinates `ι → K`; the class map `α` into `⊕ₓ T_x`, one
`residueBlockSpace` whose exponents `E` concatenate the block exponents at the
drop points; and the two counts of `lem:selfdual-degree`, `dimFl = dim Fl_{τ'}`
and `sumb = Σ bᵢ`. -/
structure RealizedDatum (K : Type*) [Field K] (ι : Type) where
  /-- the number of blocks -/
  m : ℕ
  /-- the block exponents -/
  E : Fin m → ℕ
  /-- the tangent space -/
  T : Submodule K (ι → K)
  /-- the class map -/
  α : T →ₗ[K] residueBlockSpace K E
  /-- `dim Fl_{τ'}` -/
  dimFl : ℕ
  /-- `Σ bᵢ` -/
  sumb : ℕ

/-- The bounds `realized_count` needs, with defect `D` (`cOf N₀ − c(τ)` in
`thm:h2-conditional`, `0` in `thm:h1`), kernel slack `s` (`2` for the two marked
points in `thm:h2-conditional`, `0` in `thm:h1`), and the set `S` whose
dimension `T` bounds. -/
structure RealizedDatum.Bounds {K : Type*} [Field K] {ι : Type} {n : ℕ}
    (R : RealizedDatum K ι) (τ : Nat.Partition n) (D s : ℕ) (S : Set (ι → K)) : Prop where
  /-- `thm:isotropy`: the image of `α` is isotropic for the residue form. -/
  isotropic : ∀ x ∈ LinearMap.range R.α, ∀ y ∈ LinearMap.range R.α,
    residueSpaceForm R.E x y = 0
  /-- `thm:realized-bound`. -/
  finrank_ker_le : Module.finrank K (LinearMap.ker R.α) ≤ (2 * R.dimFl + R.sumb) + s
  /-- `lem:selfdual-degree`. -/
  length_le : (∑ ξ, 2 * R.E ξ) + 2 * D + 2 * R.sumb ≤ 2 * R.dimFl
  /-- `dim Fl_{τ'}` in terms of `c(τ)`. -/
  two_dimFl : 2 * R.dimFl = n * n - cType τ
  /-- The variety half: `T` dominates `S`. -/
  affineDim_le : affineDim S ≤ ((Module.finrank K R.T : ℕ) : WithBot ℕ∞)

/-- **The count**, packaged: `dim T + D ≤ 3 dim Fl_{τ'} + s`. -/
theorem RealizedDatum.Bounds.finrank_add_le {K : Type*} [Field K] {ι : Type} [Finite ι]
    {n : ℕ} {R : RealizedDatum K ι} {τ : Nat.Partition n} {D s : ℕ} {S : Set (ι → K)}
    (h : R.Bounds τ D s S) : Module.finrank K R.T + D ≤ 3 * R.dimFl + s :=
  realized_count R.E R.α h.isotropic (2 * R.dimFl + R.sumb) R.dimFl R.sumb D s
    h.finrank_ker_le h.length_le rfl

end Realized

/-! ### `lem:selfdual-degree`: the torsion length against the degree -/

section SelfDual

open Height.Graded

variable {r : ℕ}

/-- **`lem:selfdual-degree`.**  `N = C^⊥ / im ad_P` is a torsion module on
`ℙ¹`, so its length is the eventual difference of the two Hilbert functions,
and by `lem:local-length` that length is `∑_x len_x` (`sum_localQuot_eq_len`).
Feeding in the degree count of the paper,
`dim (C^⊥)_e − dim (im ad_P)_e = 2 dim Fl_{τ'} − 2 ∑ b_i` for `e ≫ 0`
(`lem:degree` and `lem:free`, the hypothesis `hgap`), gives

```
∑_x len_x + 2 ∑ b_i = 2 dim Fl_{τ'} ,   i.e.   ∑ b_i = dim Fl_{τ'} − ½ len N .
```

Here `S` is `im ad_P` inside the graded free module `C^⊥ = ⨁_j B(-a j)`, and
`g` is a homogeneous multiplier with `g · C^⊥ ⊆ im ad_P` (the determinant of
`ad_P` on a generic complement) whose leading `ν`-coefficient is nonzero, so
that every drop point is one of the finitely many `t₀ ∈ Tset`. -/
theorem sum_b_add_half_len_eq_dimFl [IsAlgClosed K] (Tset : Finset K)
    {a : Fin r → ℤ} {S : Submodule (Graded.Poly K) (Fin r → Graded.Poly K)}
    (hS : (Graded.GradedPresentation.of K a).IsGraded S) {c : ℤ} {g : Graded.Poly K}
    (hg : g ∈ Bpiece K c) (hgmu : nuLead c g ≠ 0)
    (hgS : ∀ x : Fin r → Graded.Poly K, g • x ∈ S)
    (hTset : ∀ t₀ : K, MvPolynomial.eval ![1, t₀] g = 0 → t₀ ∈ Tset)
    (dimFl sumb : ℕ)
    (hgap : ∃ E₁ : ℤ, ∀ e, E₁ ≤ e →
      Module.finrank K ((Graded.GradedPresentation.of K a).sub S e) + 2 * dimFl
        = Module.finrank K ((Graded.GradedPresentation.of K a).piece e) + 2 * sumb) :
    (∑ t₀ ∈ Tset, Module.finrank K (localQuot K r t₀ S)) + 2 * sumb = 2 * dimFl := by
  obtain ⟨E₁, h₁⟩ := hgap
  obtain ⟨E₂, h₂⟩ := sum_localQuot_eq_len Tset hS hg hgmu hgS hTset
  have p₁ := h₁ (max E₁ E₂) (le_max_left _ _)
  have p₂ := h₂ (max E₁ E₂) (le_max_right _ _)
  omega

end SelfDual

end Height.Pencil
