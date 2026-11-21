import Height.Pencil.LocalModel
import Height.Toolbox.BaseChange

/-!
# Kernel flatness at a point of `ℙ¹`

The paper, `lem:flag-flat`(1), **degreewise** — the paper's
route, as opposed to the function-field form of `Pencil/Arcs.lean`, which
`Pencil/LocalModel.lean` shows to be strictly weaker.  The output is
`Height.Chain.siLocalFlat` (`Chain/LocalFlat.lean`), the analytic input of
`Chain/Reduction.lean`'s `siPairing_eq_zero_of_psiMap` (consumed by the node
`Chain.shiftedIsotropy`), modulo `hasMultidegreeGen`.

## Why the function-field form does not suffice

`Isotropy.DCond P Q` asks for `w` **over `K⟦u⟧`** with `P^k w = D_k(Q) v` for every
`v ∈ ker (P^k)` over `K⟦u⟧`.  The image of `P^k` over `K⟦u⟧` is not saturated, so a solution
over `K⸨u⸩` does not give one over `K⟦u⟧`; and the kernel over `K⟦u⟧` is bigger than the
`K⟦u⟧`-span of any single vector one happens to control.

Both obstructions are removed by working over `K[t]` and specialising afterwards:

* `Toolbox.ker_map_eq_mapSpan` — over a principal ideal domain `D`, `ker A` is spanned by part of a
  Smith basis, so for every injective `φ : D → R` into a domain the kernel of `A.map φ` is
  the `R`-span of the image of `ker A`.  Hence a solution of `P^k w = D_k(Q) v` for every
  *polynomial* kernel vector `v` gives `Isotropy.DCond` after any injective base change
  (`dcond_map_of_dcond`);
* `Graded.iota K t₀ : K[t] →+* K⟦u⟧`, the Taylor expansion at `t = t₀`, is injective
  (`Graded.iota_injective`), and the pencil
  in the finite chart is the expansion of the affine family: `Pat N M t₀ = (N + tM).map
  (Graded.iota K t₀)` (`Pat_eq_map_iota`).  So one integral statement over `K[t]` covers every
  point of `ℙ¹` at once.

## The degreewise argument

Fix `k ≥ 1` and a polynomial kernel vector `v` of `(N + tM)^k`.

1. **Coordinates.**  `cvec E` reads a vector of polynomials of degree `< E` as a vector in
   `K^{n × E}`, and `act Y E F` is the matrix of `v ↦ Y *ᵥ v` in those coordinates
   (`act_mulVec`).
2. **Constant rank.**  `finrank_kerPiece_eq` identifies `dim (S_k)_e` (the graded
   `kerPiece`) with `dim ker (act ((N+tM)^k) (e+1) (e+1+k))`, through the
   dehomogenisation `Graded.deh` — injective on `B_e` and landing in degree `≤ e`.  Membership
   of `Î_{τ,d}` at the base point and `hasMultidegreeGen` at the generic point therefore give
   the *same* kernel dimension in each large degree, hence the same rank
   (`rank_act_eq_of_finrank_eq`).
3. **Lifting.**  `Toolbox.exists_kernel_lift`, for arbitrary finite index types, lifts
   `cvec E v` to a kernel vector of the coefficient matrix of the arc over `K⟦s⟧`;
   re-assembling gives `(N_s + t M_s)^k ṽ = 0` over `K⟦s⟧[t]` with `ṽ ≡ v`.
4. **The `s`-linear term.**  Applying the ring map `dexp : K⟦s⟧[t] → (K[t])[ε]`,
   `f ↦ f(0) + ε f'(0)`, turns that into an identity of dual numbers; its `ε`-component is
   `D_k(Ṗ) v + P^k v̇ = 0` (`map_snd_pow`, `map_snd_mulVec`), an identity of polynomial
   vectors.  `w := −v̇` is the required companion (`exists_velocity_poly`).
5. **Specialisation.**  `dcond_map_of_dcond` along `Graded.iota K t₀` gives
   `Isotropy.DCond (Pat N M t₀) (Qat (pencil Ṅ Ṁ) t₀)` at every `t₀` (`dcond_of_arc`), and
   `siLocalFlat` is that read off an arc of the single-point marked incidence.

## The input from the multidegree layer

`Height.Chain.hasMultidegreeGen K n`: the pencil of an arc in the locus, read over `K⸨s⸩`,
has the same multidegree `d` as the base point.  `Pencil/Arcs.lean`'s `arc_rank_eq` gives the
*rank profile* at the generic point but not this Hilbert-function statement, which is what a
degreewise argument needs; it is proved in `Chain/LocalFlat.lean` from
`Chain/Multidegree.lean`.
-/

namespace Height.Pencil

open Matrix Height.Orbital Height.Toolbox
open Height.Geometry (SIIndex SIPoint siCoords PairIndex pairCoords fstMat sndMat matCoords)

universe u

/-! ### Base change of a kernel along an injective map out of a principal ideal domain -/

section BaseChange

variable {D : Type u} [CommRing D] [IsDomain D] [IsPrincipalIdealRing D]
variable {R : Type u} [CommRing R] [IsDomain R] {n : ℕ}

/-- `D_k` commutes with base change. -/
theorem Dk_map {A B : Type*} [CommRing A] [CommRing B] {m : ℕ} (ψ : A →+* B)
    (P Q : Matrix (Fin m) (Fin m) A) (k : ℕ) :
    (Dk P Q k).map ψ = Dk (P.map ψ) (Q.map ψ) k := by
  show ψ.mapMatrix (Dk P Q k) = _
  simp only [Dk]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_mul, map_pow, map_pow]
  rfl

theorem map_pow_matrix {A B : Type*} [CommRing A] [CommRing B] {m : ℕ} (ψ : A →+* B)
    (P : Matrix (Fin m) (Fin m) A) (k : ℕ) : (P ^ k).map ψ = (P.map ψ) ^ k := by
  show ψ.mapMatrix (P ^ k) = _
  rw [map_pow]
  rfl

/-- **Kernel flatness transports to every point.**  If, over the principal ideal domain `D`,
`D_k(Z)` carries `ker (Y^k)` into `im (Y^k)` for every `k`, then the same holds over `R` for the
images of `Y` and `Z` — that is, `Isotropy.DCond` holds there.  The point is that the kernel over
`R` is *generated* by the kernel over `D` (`ker_map_eq_mapSpan`), which is exactly what the
function-field form of kernel flatness fails to provide. -/
theorem dcond_map_of_dcond (Y Z : Matrix (Fin n) (Fin n) D) (φ : D →+* R)
    (hφ : Function.Injective φ)
    (h : ∀ k, ∀ v : Fin n → D, (Y ^ k) *ᵥ v = 0 →
      ∃ w : Fin n → D, (Y ^ k) *ᵥ w = Dk Y Z k *ᵥ v) :
    Isotropy.DCond (Y.map φ) (Z.map φ) := by
  intro k x hx
  have hpow : (Y.map φ) ^ k = (Y ^ k).map φ := (map_pow_matrix φ Y k).symm
  have hx' : x ∈ LinearMap.ker (((Y ^ k).map φ).mulVecLin) := by
    have : x ∈ LinearMap.ker (((Y.map φ) ^ k).mulVecLin) := hx
    rwa [hpow] at this
  rw [ker_map_eq_mapSpan (Y ^ k) φ hφ] at hx'
  set T : Submodule R (Fin n → R) :=
    (LinearMap.range (((Y ^ k).map φ).mulVecLin)).comap
      ((Dk (Y.map φ) (Z.map φ) k).mulVecLin) with hTdef
  have hgen : mapSpan φ (LinearMap.ker ((Y ^ k).mulVecLin)) ≤ T := by
    rw [mapSpan, Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    have hv' : (Y ^ k) *ᵥ v = 0 := hv
    obtain ⟨w, hw⟩ := h k v hv'
    refine ⟨fun i => φ (w i), ?_⟩
    show ((Y ^ k).map φ) *ᵥ (fun i => φ (w i)) = (Dk (Y.map φ) (Z.map φ) k) *ᵥ (fun i => φ (v i))
    funext r
    have h1 := RingHom.map_mulVec φ (Y ^ k) w r
    have h2 := RingHom.map_mulVec φ (Dk Y Z k) v r
    simp only [Function.comp_def] at h1 h2
    rw [← Dk_map φ Y Z k, ← h1, ← h2, hw]
  obtain ⟨w, hw⟩ := hgen hx'
  exact ⟨w, by rw [hpow]; exact hw⟩

end BaseChange

/-! ### The affine chart: `Graded.iota` expands a polynomial in `t` at the point `t = t₀` -/

section Expand

variable {K : Type u} [Field K] {n : ℕ}

/-- The pencil in the finite chart is the Taylor expansion of the affine family. -/
theorem Pat_eq_map_iota (N M : Matrix (Fin n) (Fin n) K) (t₀ : K) :
    Pat N M t₀ = (pencilPoly N M).map (Graded.iota K t₀) := by
  have hc : (⇑(Graded.atPoint t₀) : Graded.Poly K → PowerSeries K)
      = ⇑(Graded.iota K t₀) ∘ ⇑((Graded.deh K).toRingHom) := by
    rw [Graded.atPoint_eq_comp, RingHom.coe_comp]
  rw [Pat, hc, ← Matrix.map_map, map_deh_pencil]

/-- The same for a pencil direction. -/
theorem Qat_pencil_eq_map_iota (Nd Md : Matrix (Fin n) (Fin n) K) (t₀ : K) :
    Qat (pencil Nd Md) t₀ = (pencilPoly Nd Md).map (Graded.iota K t₀) :=
  Pat_eq_map_iota Nd Md t₀

end Expand

/-! ### Coefficient vectors of vectors of polynomials -/

section Coeffs

variable {A : Type u} [CommRing A] {n : ℕ}

/-- Entrywise degree bound for a product of matrices of polynomials. -/
theorem natDegree_matrix_mul_le {X Y : Matrix (Fin n) (Fin n) (Polynomial A)} {dX dY : ℕ}
    (hX : ∀ i j, (X i j).natDegree ≤ dX) (hY : ∀ i j, (Y i j).natDegree ≤ dY) (i j : Fin n) :
    ((X * Y) i j).natDegree ≤ dX + dY := by
  rw [Matrix.mul_apply]
  exact Polynomial.natDegree_sum_le_of_forall_le _ _ fun l _ =>
    Polynomial.natDegree_mul_le_of_le (hX i l) (hY l j)

/-- Entrywise degree bound for a power of a matrix of polynomials. -/
theorem natDegree_matrix_pow_le {Y : Matrix (Fin n) (Fin n) (Polynomial A)} {d : ℕ}
    (hY : ∀ i j, (Y i j).natDegree ≤ d) (k : ℕ) (i j : Fin n) :
    ((Y ^ k) i j).natDegree ≤ k * d := by
  induction k generalizing i j with
  | zero =>
      rw [pow_zero]
      by_cases h : i = j <;> simp [Matrix.one_apply, h]
  | succ k ih =>
      rw [pow_succ]
      refine le_trans (natDegree_matrix_mul_le (fun a b => ih a b) hY i j) ?_
      exact le_of_eq (Nat.succ_mul k d).symm

/-- The coefficient vector, in degrees `< E`, of a vector of polynomials. -/
def cvec (E : ℕ) (v : Fin n → Polynomial A) : Fin n × Fin E → A :=
  fun p => (v p.1).coeff (p.2 : ℕ)

/-- The vector of polynomials of degree `< E` with a given coefficient vector. -/
noncomputable def pvec (E : ℕ) (c : Fin n × Fin E → A) : Fin n → Polynomial A :=
  fun i => ∑ m : Fin E, Polynomial.C (c (i, m)) * Polynomial.X ^ (m : ℕ)

theorem coeff_pvec (E : ℕ) (c : Fin n × Fin E → A) (i : Fin n) (r : ℕ) :
    (pvec E c i).coeff r = if h : r < E then c (i, ⟨r, h⟩) else 0 := by
  classical
  show (∑ m : Fin E, Polynomial.C (c (i, m)) * Polynomial.X ^ (m : ℕ)).coeff r = _
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  split_ifs with h
  · rw [Finset.sum_eq_single (⟨r, h⟩ : Fin E)]
    · simp
    · intro b _ hb
      have hne : ¬ (r = (b : ℕ)) := fun hrb => hb (Fin.ext hrb.symm)
      simp [hne]
    · intro hmem
      exact absurd (Finset.mem_univ (⟨r, h⟩ : Fin E)) hmem
  · refine Finset.sum_eq_zero fun b _ => ?_
    have hb := b.isLt
    have hne : ¬ (r = (b : ℕ)) := by omega
    simp [hne]

@[simp] theorem cvec_pvec (E : ℕ) (c : Fin n × Fin E → A) : cvec E (pvec E c) = c := by
  funext p
  show (pvec E c p.1).coeff (p.2 : ℕ) = c p
  rw [coeff_pvec]
  split_ifs with h
  · rfl
  · exact absurd p.2.isLt h

theorem pvec_cvec {E : ℕ} (v : Fin n → Polynomial A) (hv : ∀ i, (v i).natDegree < E) :
    pvec E (cvec E v) = v := by
  funext i
  refine Polynomial.ext fun r => ?_
  rw [coeff_pvec]
  split_ifs with h
  · rfl
  · exact (Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_lt_of_le (hv i) (not_lt.1 h))).symm

theorem eq_zero_of_cvec_eq_zero {E : ℕ} {v : Fin n → Polynomial A}
    (hv : ∀ i, (v i).natDegree < E) (h : cvec E v = 0) : v = 0 := by
  have h1 := pvec_cvec v hv
  rw [h] at h1
  refine h1.symm.trans ?_
  funext i
  show (∑ m : Fin E, Polynomial.C ((0 : Fin n × Fin E → A) (i, m)) * Polynomial.X ^ (m : ℕ)) = 0
  simp

/-- The matrix of `v ↦ Y *ᵥ v` on coefficient vectors: columns index the coefficients of
degree `< E` of the argument, rows those of degree `< F` of the value. -/
def act (Y : Matrix (Fin n) (Fin n) (Polynomial A)) (E F : ℕ) :
    Matrix (Fin n × Fin F) (Fin n × Fin E) A :=
  Matrix.of fun p q =>
    if (q.2 : ℕ) ≤ (p.2 : ℕ) then (Y p.1 q.1).coeff ((p.2 : ℕ) - (q.2 : ℕ)) else 0

theorem act_map {B : Type*} [CommRing B] (ψ : A →+* B)
    (Y : Matrix (Fin n) (Fin n) (Polynomial A)) (E F : ℕ) :
    (act Y E F).map ψ = act (Y.map (Polynomial.map ψ)) E F := by
  refine Matrix.ext fun p q => ?_
  show ψ (act Y E F p q) = _
  by_cases h : (q.2 : ℕ) ≤ (p.2 : ℕ) <;>
    simp [act, h, Matrix.map_apply, Polynomial.coeff_map]

private theorem coeff_mul_range (f g : Polynomial A) (l : ℕ) :
    (f * g).coeff l = ∑ m ∈ Finset.range (l + 1), f.coeff (l - m) * g.coeff m := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    ← Finset.sum_range_reflect (fun m => f.coeff (l - m) * g.coeff m) (l + 1)]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' : m ≤ l := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
  rw [show l + 1 - 1 - m = l - m from by omega, show l - (l - m) = m from by omega]

/-- The defining property of `act`: on coefficient vectors of polynomials of degree `< E`
it computes the matrix-vector product. -/
theorem act_mulVec (Y : Matrix (Fin n) (Fin n) (Polynomial A)) {E : ℕ} (F : ℕ)
    (v : Fin n → Polynomial A) (hv : ∀ i, (v i).natDegree < E) :
    act Y E F *ᵥ cvec E v = cvec F (Y *ᵥ v) := by
  classical
  funext p
  obtain ⟨i, l⟩ := p
  have hlhs : (act Y E F *ᵥ cvec E v) (i, l)
      = ∑ j : Fin n, ∑ m ∈ Finset.range E,
          (if m ≤ (l : ℕ) then (Y i j).coeff ((l : ℕ) - m) else 0) * (v j).coeff m := by
    rw [Matrix.mulVec_apply_eq_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact Fin.sum_univ_eq_sum_range
      (fun m => (if m ≤ (l : ℕ) then (Y i j).coeff ((l : ℕ) - m) else 0) * (v j).coeff m) E
  have hrhs : cvec F (Y *ᵥ v) (i, l)
      = ∑ j : Fin n, ∑ m ∈ Finset.range ((l : ℕ) + 1),
          (Y i j).coeff ((l : ℕ) - m) * (v j).coeff m := by
    show ((Y *ᵥ v) i).coeff (l : ℕ) = _
    rw [Matrix.mulVec_apply_eq_sum, Polynomial.finsetSum_coeff]
    exact Finset.sum_congr rfl fun j _ => coeff_mul_range _ _ _
  rw [hlhs, hrhs]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [ite_mul, zero_mul, ← Finset.sum_filter]
  refine Finset.sum_subset ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx
    exact Finset.mem_range.2 (by omega)
  · intro x hx hnx
    simp only [Finset.mem_range] at hx
    simp only [Finset.mem_filter, Finset.mem_range, not_and] at hnx
    have hxE : E ≤ x := by
      by_contra hcon
      exact absurd (hnx (by omega)) (by omega)
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (hv j) hxE), mul_zero]

theorem natDegree_pvec_lt {E : ℕ} (hE : 0 < E) (c : Fin n × Fin E → A) (i : Fin n) :
    (pvec E c i).natDegree < E := by
  have h : (pvec E c i).natDegree ≤ E - 1 := by
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun m _ => ?_
    refine le_trans Polynomial.natDegree_mul_le ?_
    rw [Polynomial.natDegree_C]
    have hm := m.isLt
    have h2 : ((Polynomial.X : Polynomial A) ^ (m : ℕ)).natDegree ≤ (m : ℕ) := by
      simpa using
        Polynomial.natDegree_pow_le_of_le (m : ℕ) (Polynomial.natDegree_X_le (R := A))
    omega
  omega

theorem natDegree_mulVec_lt {Y : Matrix (Fin n) (Fin n) (Polynomial A)} {d : ℕ}
    (hY : ∀ i j, (Y i j).natDegree ≤ d) {E : ℕ} {v : Fin n → Polynomial A}
    (hv : ∀ i, (v i).natDegree < E) (i : Fin n) : ((Y *ᵥ v) i).natDegree < E + d := by
  have hE : 0 < E := lt_of_le_of_lt (Nat.zero_le _) (hv i)
  have h : ((Y *ᵥ v) i).natDegree ≤ d + (E - 1) := by
    rw [Matrix.mulVec_apply_eq_sum]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
    exact Polynomial.natDegree_mul_le_of_le (hY i j) (by have := hv j; omega)
  omega

end Coeffs

/-! ### The `s`-linear term of a relation, through dual numbers -/

section Dual

open TrivSqZeroExt

variable {A : Type*} [CommRing A]

/-- `fst` on dual numbers, as a ring homomorphism. -/
def fstRingHom (A : Type*) [CommRing A] : DualNumber A →+* A where
  toFun := TrivSqZeroExt.fst
  map_one' := TrivSqZeroExt.fst_one
  map_mul' := TrivSqZeroExt.fst_mul
  map_zero' := TrivSqZeroExt.fst_zero
  map_add' := TrivSqZeroExt.fst_add

/-- `snd` on dual numbers, as an additive homomorphism. -/
def sndAddHom (A : Type*) [CommRing A] : DualNumber A →+ A where
  toFun := TrivSqZeroExt.snd
  map_zero' := TrivSqZeroExt.snd_zero
  map_add' := TrivSqZeroExt.snd_add

@[simp] theorem fstRingHom_apply (x : DualNumber A) : fstRingHom A x = x.fst := rfl

@[simp] theorem sndAddHom_apply (x : DualNumber A) : sndAddHom A x = x.snd := rfl

variable {m : ℕ}

theorem map_snd_mul (X Y : Matrix (Fin m) (Fin m) (DualNumber A)) :
    (X * Y).map (sndAddHom A)
      = X.map (fstRingHom A) * Y.map (sndAddHom A)
        + X.map (sndAddHom A) * Y.map (fstRingHom A) := by
  refine Matrix.ext fun i j => ?_
  show (sndAddHom A) ((X * Y) i j) = _
  rw [Matrix.mul_apply, map_sum (sndAddHom A)]
  simp only [Matrix.add_apply, Matrix.mul_apply, sndAddHom_apply, Matrix.map_apply, fstRingHom_apply, DualNumber.snd_mul, ← Finset.sum_add_distrib]

/-- The `ε`-component of a power of a matrix of dual numbers is `D_k`. -/
theorem map_snd_pow (W : Matrix (Fin m) (Fin m) (DualNumber A)) (k : ℕ) :
    (W ^ k).map (sndAddHom A)
      = Isotropy.dpow (W.map (fstRingHom A)) (W.map (sndAddHom A)) k := by
  induction k with
  | zero =>
      rw [pow_zero, Isotropy.dpow_zero]
      refine Matrix.ext fun i j => ?_
      show TrivSqZeroExt.snd ((1 : Matrix (Fin m) (Fin m) (DualNumber A)) i j) = 0
      by_cases h : i = j <;> simp [Matrix.one_apply, h]
  | succ k ih =>
      rw [pow_succ, map_snd_mul, ih, map_pow_matrix (fstRingHom A) W k,
        Isotropy.dpow_succ']
      rw [add_comm]

theorem map_snd_mulVec (V : Matrix (Fin m) (Fin m) (DualNumber A))
    (w : Fin m → DualNumber A) :
    (fun i => TrivSqZeroExt.snd ((V *ᵥ w) i))
      = (V.map (fstRingHom A)) *ᵥ (fun j => TrivSqZeroExt.snd (w j))
        + (V.map (sndAddHom A)) *ᵥ (fun j => TrivSqZeroExt.fst (w j)) := by
  funext i
  show (sndAddHom A) ((V *ᵥ w) i) = _
  rw [Matrix.mulVec_apply_eq_sum, map_sum (sndAddHom A)]
  simp only [Pi.add_apply, Matrix.mulVec_apply_eq_sum, Matrix.map_apply, sndAddHom_apply, fstRingHom_apply, DualNumber.snd_mul, ← Finset.sum_add_distrib]

end Dual

section DualExpand

variable {K : Type u} [Field K]

/-- The constant and linear coefficients of a power series, as a ring map to the dual numbers
over `K[t]`. -/
noncomputable def dcoeff (K : Type u) [Field K] : PowerSeries K →+* DualNumber (Polynomial K) where
  toFun f := TrivSqZeroExt.inl (Polynomial.C (PowerSeries.constantCoeff f))
    + TrivSqZeroExt.inr (Polynomial.C (PowerSeries.coeff 1 f))
  map_one' := by
    refine TrivSqZeroExt.ext ?_ ?_ <;> simp
  map_mul' f g := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, DualNumber.snd_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, zero_add, add_zero]
      rw [Height.Orbital.coeff_one_mul, map_add, map_mul, map_mul]
      ring
  map_zero' := by
    refine TrivSqZeroExt.ext ?_ ?_ <;> simp
  map_add' f g := by
    refine TrivSqZeroExt.ext ?_ ?_ <;> simp

@[simp] theorem fst_dcoeff (f : PowerSeries K) :
    (dcoeff K f).fst = Polynomial.C (PowerSeries.constantCoeff f) := by
  simp [dcoeff]

@[simp] theorem snd_dcoeff (f : PowerSeries K) :
    (dcoeff K f).snd = Polynomial.C (PowerSeries.coeff 1 f) := by
  simp [dcoeff]

/-- The dual-number expansion of a polynomial in `t` with power-series coefficients: it records
the constant term and the `s`-linear term simultaneously. -/
noncomputable def dexp (K : Type u) [Field K] :
    Polynomial (PowerSeries K) →+* DualNumber (Polynomial K) :=
  Polynomial.eval₂RingHom (dcoeff K) (TrivSqZeroExt.inl Polynomial.X)

theorem fstRingHom_comp_dexp :
    (fstRingHom (Polynomial K)).comp (dexp K)
      = Polynomial.mapRingHom (PowerSeries.constantCoeff (R := K)) := by
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  · show ((dexp K) (Polynomial.C a)).fst = _
    rw [dexp, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
    simp
  · show ((dexp K) Polynomial.X).fst = _
    rw [dexp, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
    simp

theorem fst_dexp (f : Polynomial (PowerSeries K)) :
    ((dexp K) f).fst = Polynomial.map (PowerSeries.constantCoeff (R := K)) f :=
  congrArg (fun φ => φ f) fstRingHom_comp_dexp

theorem dexp_penP {n : ℕ} (Ns Ms : Matrix (Fin n) (Fin n) (PowerSeries K)) (i j : Fin n) :
    (dexp K) (pencilPoly Ns Ms i j)
      = TrivSqZeroExt.inl (pencilPoly (Height.Orbital.matC Ns) (Height.Orbital.matC Ms) i j)
        + TrivSqZeroExt.inr (pencilPoly (Height.Orbital.matD Ns) (Height.Orbital.matD Ms) i j) := by
  rw [pencilPoly_apply, map_add, map_mul]
  refine TrivSqZeroExt.ext ?_ ?_
  · show ((dexp K) (Polynomial.C (Ns i j))
      + (dexp K) Polynomial.X * (dexp K) (Polynomial.C (Ms i j))).fst = _
    rw [dexp]
    simp [Polynomial.coe_eval₂RingHom, pencilPoly]
  · show ((dexp K) (Polynomial.C (Ns i j))
      + (dexp K) Polynomial.X * (dexp K) (Polynomial.C (Ms i j))).snd = _
    rw [dexp]
    simp [Polynomial.coe_eval₂RingHom, pencilPoly]

theorem map_fst_dexp_penP {n : ℕ} (Ns Ms : Matrix (Fin n) (Fin n) (PowerSeries K)) :
    ((pencilPoly Ns Ms).map (dexp K)).map (fstRingHom (Polynomial K))
      = pencilPoly (Height.Orbital.matC Ns) (Height.Orbital.matC Ms) := by
  refine Matrix.ext fun i j => ?_
  show ((dexp K) (pencilPoly Ns Ms i j)).fst = _
  rw [dexp_penP]
  simp

theorem map_snd_dexp_penP {n : ℕ} (Ns Ms : Matrix (Fin n) (Fin n) (PowerSeries K)) :
    ((pencilPoly Ns Ms).map (dexp K)).map (sndAddHom (Polynomial K))
      = pencilPoly (Height.Orbital.matD Ns) (Height.Orbital.matD Ms) := by
  refine Matrix.ext fun i j => ?_
  show ((dexp K) (pencilPoly Ns Ms i j)).snd = _
  rw [dexp_penP]
  simp

end DualExpand

/-! ### The graded piece and the affine coefficient vectors -/

section Dictionary

open Height.Graded

variable {K : Type u} [Field K] {n : ℕ}

theorem mulVec_mem_piece (N M : Matrix (Fin n) (Fin n) K) (k e : ℕ)
    {v : Fin n → Graded.Poly K}
    (hv : v ∈ (Graded.GradedPresentation.free K (Fin n)).piece (e : ℤ)) :
    (pencil N M ^ k) *ᵥ v
      ∈ (Graded.GradedPresentation.free K (Fin n)).piece ((e + k : ℕ) : ℤ) := by
  rw [(Graded.GradedPresentation.of K _).mem_piece]
  intro i
  rw [Matrix.mulVec_apply_eq_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  have h1 := pencil_pow_mem_Bpiece N M k i j
  have h2 := ((Graded.GradedPresentation.of K _).mem_piece.1 hv) j
  have h := Bpiece_smul_Bpiece h1 h2
  have hc : ((k : ℤ) + ((e : ℤ) - 0)) = ((e + k : ℕ) : ℤ) - 0 := by push_cast; ring
  rwa [hc] at h

-- The identification of `(⨁ B)_e` with the coefficient vectors of degree `< e+1` is
-- `Graded.coordEquiv K (Fin n) e`, the one coordinate system on an untwisted piece;
-- on a homogeneous `v` it is `cvec (e+1) (deh ∘ v)`, by definition.

/-- The kernel of the `k`-th power of the affine pencil on coefficient vectors of degree
`< E`. -/
noncomputable def kerAct (N M : Matrix (Fin n) (Fin n) K) (k E : ℕ) :
    Submodule K (Fin n × Fin E → K) :=
  LinearMap.ker (act ((pencilPoly N M) ^ k) E (E + k)).mulVecLin

theorem mem_kerAct {N M : Matrix (Fin n) (Fin n) K} {k E : ℕ} {c : Fin n × Fin E → K} :
    c ∈ kerAct N M k E ↔ act ((pencilPoly N M) ^ k) E (E + k) *ᵥ c = 0 := Iff.rfl

theorem pencil_pow_map_deh (N M : Matrix (Fin n) (Fin n) K) (k : ℕ) :
    ((pencil N M) ^ k).map ((Graded.deh K).toRingHom) = (pencilPoly N M) ^ k := by
  rw [map_pow_matrix ((Graded.deh K).toRingHom) (pencil N M) k, map_deh_pencil]

/-- The dictionary: the degree-`e` piece of the kernel flag is the kernel of `act` on
coefficient vectors of degree `< e+1`. -/
theorem map_coordEquiv_kerPiece (N M : Matrix (Fin n) (Fin n) K) (k e : ℕ) :
    Submodule.map (Graded.coordEquiv K (Fin n) e : _ →ₗ[K] _)
        (Submodule.comap
          ((Graded.GradedPresentation.free K (Fin n)).piece (e : ℤ)).subtype
          (kerPiece N M k e))
      = kerAct N M k (e + 1) := by
  have hdeg : ∀ (v : (Graded.GradedPresentation.free K (Fin n)).piece (e : ℤ)) (i : Fin n),
      ((Graded.deh K).toRingHom ((v : Fin n → Graded.Poly K) i)).natDegree < e + 1 := by
    intro v i
    have hb : (v : Fin n → Graded.Poly K) i ∈ Bpiece K (e : ℤ) := by
      simpa using ((Graded.GradedPresentation.of K _).mem_piece.1 v.2) i
    exact lt_of_le_of_lt (Graded.natDegree_deh_le hb) (by omega)
  have hkey : ∀ v : (Graded.GradedPresentation.free K (Fin n)).piece (e : ℤ),
      (Graded.coordEquiv K (Fin n) e v ∈ kerAct N M k (e + 1) ↔
        (pencil N M ^ k) *ᵥ (v : Fin n → Graded.Poly K) = 0) := by
    intro v
    set w : Fin n → Graded.Poly K :=
      (pencil N M ^ k) *ᵥ (v : Fin n → Graded.Poly K) with hw
    have hdw : ∀ i, ((Graded.deh K).toRingHom (w i)).natDegree < (e + 1) + k := by
      intro i
      have hb : w i ∈ Bpiece K ((e + k : ℕ) : ℤ) := by
        simpa using
          ((Graded.GradedPresentation.of K _).mem_piece.1
            (mulVec_mem_piece N M k e v.2)) i
      exact lt_of_le_of_lt (Graded.natDegree_deh_le hb) (by omega)
    have hcomm : (pencilPoly N M ^ k) *ᵥ (fun i => (Graded.deh K).toRingHom ((v : Fin n → Graded.Poly K) i))
        = fun i => (Graded.deh K).toRingHom (w i) := by
      funext i
      have h := RingHom.map_mulVec ((Graded.deh K).toRingHom) (pencil N M ^ k)
        (v : Fin n → Graded.Poly K) i
      rw [pencil_pow_map_deh] at h
      exact h.symm
    rw [mem_kerAct]
    have hact : act ((pencilPoly N M) ^ k) (e + 1) ((e + 1) + k) *ᵥ (Graded.coordEquiv K (Fin n) e v)
        = cvec ((e + 1) + k) (fun i => (Graded.deh K).toRingHom (w i)) := by
      have hm := act_mulVec ((pencilPoly N M) ^ k) ((e + 1) + k)
        (fun i => (Graded.deh K).toRingHom ((v : Fin n → Graded.Poly K) i)) (hdeg v)
      rw [show (Graded.coordEquiv K (Fin n) e v) = cvec (e + 1) (fun i => (Graded.deh K).toRingHom ((v : Fin n → Graded.Poly K) i)) from rfl,
        hm, hcomm]
    rw [hact]
    constructor
    · intro h0
      have hz : (fun i => (Graded.deh K).toRingHom (w i)) = 0 := eq_zero_of_cvec_eq_zero hdw h0
      funext i
      have hbi : w i ∈ Bpiece K ((e + k : ℕ) : ℤ) := by
        simpa using
          ((Graded.GradedPresentation.of K _).mem_piece.1
            (mulVec_mem_piece N M k e v.2)) i
      by_contra hne
      exact Graded.deh_ne_zero_of_ne_zero hbi hne (congrFun hz i)
    · intro h0
      funext p
      show ((Graded.deh K).toRingHom (w p.1)).coeff (p.2 : ℕ) = 0
      rw [h0]
      simp
  refine le_antisymm ?_ ?_
  · rintro _ ⟨v, hv, rfl⟩
    have hv' : (v : Fin n → Graded.Poly K) ∈ kerPiece N M k e := hv
    exact (hkey v).2 hv'.1
  · intro c hc
    obtain ⟨v, rfl⟩ := (Graded.coordEquiv K (Fin n) e).surjective c
    exact ⟨v, ⟨(hkey v).1 hc, v.2⟩, rfl⟩

theorem finrank_kerPiece_eq (N M : Matrix (Fin n) (Fin n) K) (k e : ℕ) :
    Module.finrank K (kerPiece N M k e)
      = Module.finrank K (kerAct N M k (e + 1)) := by
  have hle : kerPiece N M k e
      ≤ (Graded.GradedPresentation.free K (Fin n)).piece (e : ℤ) := inf_le_right
  have h1 := (Submodule.comapSubtypeEquivOfLe hle).finrank_eq
  have h2 := LinearEquiv.finrank_map_eq (Graded.coordEquiv K (Fin n) e)
    (Submodule.comap ((Graded.GradedPresentation.free K (Fin n)).piece (e : ℤ)).subtype
      (kerPiece N M k e))
  rw [map_coordEquiv_kerPiece] at h2
  rw [← h1, ← h2]

end Dictionary

/-! ### The rank of the coefficient matrix is read off the multidegree -/

section RankAct

open Height.Graded

variable {K : Type u} [Field K] {n : ℕ}

theorem rank_add_finrank_kerAct (N M : Matrix (Fin n) (Fin n) K) (k E : ℕ) :
    (act ((pencilPoly N M) ^ k) E (E + k)).rank + Module.finrank K (kerAct N M k E) = n * E := by
  have h := LinearMap.finrank_range_add_finrank_ker
    (act ((pencilPoly N M) ^ k) E (E + k)).mulVecLin
  have hd : Module.finrank K (Fin n × Fin E → K) = n * E := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  rw [hd] at h
  exact h

/-- Two pencils with the same degree-`e` kernel dimension have coefficient matrices of the
same rank, over their (possibly different) ground fields. -/
theorem rank_act_eq_of_finrank_eq {K₁ : Type u} [Field K₁] {K₂ : Type u} [Field K₂]
    (N₁ M₁ : Matrix (Fin n) (Fin n) K₁) (N₂ M₂ : Matrix (Fin n) (Fin n) K₂) (k e : ℕ)
    (h : Module.finrank K₁ (kerPiece N₁ M₁ k e)
      = Module.finrank K₂ (kerPiece N₂ M₂ k e)) :
    (act ((pencilPoly N₁ M₁) ^ k) (e + 1) ((e + 1) + k)).rank
      = (act ((pencilPoly N₂ M₂) ^ k) (e + 1) ((e + 1) + k)).rank := by
  have r1 := rank_add_finrank_kerAct N₁ M₁ k (e + 1)
  have r2 := rank_add_finrank_kerAct N₂ M₂ k (e + 1)
  rw [← finrank_kerPiece_eq] at r1 r2
  omega

theorem map_pvec {A : Type u} [CommRing A] {B : Type u} [CommRing B] (ψ : A →+* B) (E : ℕ)
    (c : Fin n × Fin E → A) (i : Fin n) :
    Polynomial.map ψ (pvec E c i) = pvec E (fun p => ψ (c p)) i := by
  show Polynomial.map ψ (∑ m : Fin E, Polynomial.C (c (i, m)) * Polynomial.X ^ (m : ℕ)) = _
  rw [Polynomial.map_sum]
  exact Finset.sum_congr rfl fun m _ => by simp

theorem act_pow_map {A : Type u} [CommRing A] {B : Type u} [CommRing B] (ψ : A →+* B)
    (N M : Matrix (Fin n) (Fin n) A) (k E F : ℕ) :
    (act ((pencilPoly N M) ^ k) E F).map ψ = act ((pencilPoly (N.map ψ) (M.map ψ)) ^ k) E F := by
  rw [act_map ψ ((pencilPoly N M) ^ k) E F]
  congr 1
  rw [show (Polynomial.map ψ : Polynomial A → Polynomial B)
      = ⇑(Polynomial.mapRingHom ψ) from rfl,
    map_pow_matrix (Polynomial.mapRingHom ψ) (pencilPoly N M) k]
  congr 1
  exact pencilPoly_map ψ N M

end RankAct

/-! ### Kernel flatness of an arc of pencils, degreewise -/

section ArcFlat

open Height.Graded

variable {K : Type u} [Field K] {n : ℕ}

/-- **`lem:flag-flat`(1), integral form.**  Along an arc of pencils whose base point and
generic point have the same multidegree, every polynomial kernel vector of `P^k` has a
*polynomial* companion `w` with `D_k(Ṗ) v = P^k w`. -/
theorem exists_velocity_poly (Ns Ms : Matrix (Fin n) (Fin n) (PowerSeries K))
    (τ : Nat.Partition n) (d : ℕ → ℕ)
    (hbase : HasMultidegree (matC Ns) (matC Ms) τ d)
    (hgen : HasMultidegree
      (Ns.map (algebraMap (PowerSeries K) (LaurentSeries K)))
      (Ms.map (algebraMap (PowerSeries K) (LaurentSeries K))) τ d)
    (k : ℕ) (v : Fin n → Polynomial K)
    (hv : (pencilPoly (matC Ns) (matC Ms) ^ k) *ᵥ v = 0) :
    ∃ w : Fin n → Polynomial K,
      (pencilPoly (matC Ns) (matC Ms) ^ k) *ᵥ w
        = Isotropy.dpow (pencilPoly (matC Ns) (matC Ms)) (pencilPoly (matD Ns) (matD Ms)) k *ᵥ v := by
  classical
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact ⟨0, by rw [Isotropy.dpow_zero, Matrix.zero_mulVec, Matrix.mulVec_zero]⟩
  set ι : PowerSeries K →+* LaurentSeries K := algebraMap (PowerSeries K) (LaurentSeries K) with hι
  obtain ⟨e₁, he₁⟩ := hbase k hk
  obtain ⟨e₂, he₂⟩ := hgen k hk
  set e : ℕ := e₁ + e₂ + ∑ i : Fin n, (v i).natDegree with hedef
  set E : ℕ := e + 1 with hEdef
  have hdegv : ∀ i, (v i).natDegree < E := by
    intro i
    have := Finset.single_le_sum (f := fun i : Fin n => (v i).natDegree)
      (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  -- the rank of the coefficient matrix is the same at the base point and at the generic point
  have hfr : Module.finrank K (kerPiece (matC Ns) (matC Ms) k e)
      = Module.finrank (LaurentSeries K)
        (kerPiece (Ns.map ι) (Ms.map ι) k e) := by
    have h1 := he₁ e (by omega)
    have h2 := he₂ e (by omega)
    omega
  have hrankeq := rank_act_eq_of_finrank_eq (matC Ns) (matC Ms) (Ns.map ι) (Ms.map ι) k e hfr
  -- the coefficient matrix of the arc
  set A : Matrix (Fin n × Fin (E + k)) (Fin n × Fin E) (PowerSeries K) :=
    act ((pencilPoly Ns Ms) ^ k) E (E + k) with hA
  have hAC : A.map (PowerSeries.constantCoeff (R := K))
      = act ((pencilPoly (matC Ns) (matC Ms)) ^ k) E (E + k) :=
    act_pow_map (PowerSeries.constantCoeff (R := K)) Ns Ms k E (E + k)
  have hAL : A.map ι = act ((pencilPoly (Ns.map ι) (Ms.map ι)) ^ k) E (E + k) :=
    act_pow_map ι Ns Ms k E (E + k)
  have hrank : (A.map ι).rank = (A.map (PowerSeries.constantCoeff (R := K))).rank := by
    rw [hAC, hAL]
    exact hrankeq.symm
  -- the base-point coefficient vector lies in the kernel
  have hv0 : (A.map (PowerSeries.constantCoeff (R := K))) *ᵥ cvec E v = 0 := by
    rw [hAC, act_mulVec ((pencilPoly (matC Ns) (matC Ms)) ^ k) (E + k) v hdegv, hv]
    funext p
    show ((0 : Fin n → Polynomial K) p.1).coeff (p.2 : ℕ) = 0
    simp
  obtain ⟨cc, hcc0, hccC⟩ :=
    Height.Toolbox.exists_kernel_lift A hrank (cvec E v) hv0
  -- lift to a polynomial vector over `K⟦s⟧`
  set vv : Fin n → Polynomial (PowerSeries K) := pvec E cc with hvv
  have hdvv : ∀ i, (vv i).natDegree < E := natDegree_pvec_lt (by omega) cc
  have hYdeg : ∀ i j, (((pencilPoly Ns Ms) ^ k) i j).natDegree ≤ k := by
    intro i j
    simpa using natDegree_matrix_pow_le (natDegree_pencilPoly_le Ns Ms) k i j
  have hstar : ((pencilPoly Ns Ms) ^ k) *ᵥ vv = 0 := by
    refine eq_zero_of_cvec_eq_zero (E := E + k)
      (fun i => natDegree_mulVec_lt hYdeg hdvv i) ?_
    rw [← act_mulVec ((pencilPoly Ns Ms) ^ k) (E + k) vv hdvv]
    rw [hvv, cvec_pvec]
    exact hcc0
  -- pass to dual numbers and read the `ε`-component
  set W : Matrix (Fin n) (Fin n) (DualNumber (Polynomial K)) :=
    (pencilPoly Ns Ms).map (dexp K) with hW
  set ww : Fin n → DualNumber (Polynomial K) := fun i => (dexp K) (vv i) with hww
  have hWk : (W ^ k) *ᵥ ww = 0 := by
    funext i
    have h := RingHom.map_mulVec (dexp K) ((pencilPoly Ns Ms) ^ k) vv i
    rw [hstar] at h
    simp only [Pi.zero_apply, map_zero] at h
    rw [hW, ← map_pow_matrix (dexp K) (pencilPoly Ns Ms) k]
    exact h.symm
  have hfstW : W.map (fstRingHom (Polynomial K)) = pencilPoly (matC Ns) (matC Ms) :=
    map_fst_dexp_penP Ns Ms
  have hsndW : W.map (sndAddHom (Polynomial K)) = pencilPoly (matD Ns) (matD Ms) :=
    map_snd_dexp_penP Ns Ms
  have hfstWk : (W ^ k).map (fstRingHom (Polynomial K)) = (pencilPoly (matC Ns) (matC Ms)) ^ k := by
    rw [map_pow_matrix (fstRingHom (Polynomial K)) W k, hfstW]
  have hsndWk : (W ^ k).map (sndAddHom (Polynomial K))
      = Isotropy.dpow (pencilPoly (matC Ns) (matC Ms)) (pencilPoly (matD Ns) (matD Ms)) k := by
    rw [map_snd_pow W k, hfstW, hsndW]
  have hfstww : (fun j => TrivSqZeroExt.fst (ww j)) = v := by
    funext j
    rw [hww]
    show ((dexp K) (vv j)).fst = v j
    rw [fst_dexp, hvv, map_pvec]
    have : (fun p => PowerSeries.constantCoeff (cc p)) = cvec E v := hccC
    rw [this, pvec_cvec v hdegv]
  have hkey := map_snd_mulVec (W ^ k) ww
  rw [hWk, hfstWk, hsndWk, hfstww] at hkey
  have hzero : (fun i => TrivSqZeroExt.snd ((0 : Fin n → DualNumber (Polynomial K)) i))
      = (0 : Fin n → Polynomial K) := by
    funext i
    simp
  rw [hzero] at hkey
  refine ⟨-(fun j => TrivSqZeroExt.snd (ww j)), ?_⟩
  rw [Matrix.mulVec_neg]
  have := hkey.symm
  rw [add_eq_zero_iff_eq_neg] at this
  rw [this, neg_neg]

/-- **Kernel flatness at every point of `ℙ¹`.**  The pencil velocity of an arc whose base and
generic points have the same multidegree satisfies `Isotropy.DCond` in every affine chart. -/
theorem dcond_of_arc (Ns Ms : Matrix (Fin n) (Fin n) (PowerSeries K))
    (τ : Nat.Partition n) (d : ℕ → ℕ)
    (hbase : HasMultidegree (matC Ns) (matC Ms) τ d)
    (hgen : HasMultidegree
      (Ns.map (algebraMap (PowerSeries K) (LaurentSeries K)))
      (Ms.map (algebraMap (PowerSeries K) (LaurentSeries K))) τ d)
    (t₀ : K) :
    Isotropy.DCond (Pat (matC Ns) (matC Ms) t₀)
      (Qat (pencil (matD Ns) (matD Ms)) t₀) := by
  have h := dcond_map_of_dcond (pencilPoly (matC Ns) (matC Ms)) (pencilPoly (matD Ns) (matD Ms))
    (Graded.iota K t₀) (Graded.iota_injective t₀)
    (fun k v hv => exists_velocity_poly Ns Ms τ d hbase hgen k v hv)
  rwa [← Pat_eq_map_iota,
    ← Qat_pencil_eq_map_iota] at h

end ArcFlat

end Height.Pencil
