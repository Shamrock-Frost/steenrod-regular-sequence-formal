import Height.Geometry.Interface
import Height.Geometry.Tangent.Generic
import Height.Toolbox.AffineAlgebra
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The cotangent space of `V(I)` at a `K`-point is dual to the Jacobian kernel

Let `x` be a `K`-point of `V(I)`, `M = pointIdeal x` and `m = M·(K[ι] ⧸ I)`.  The gradient
`grad x : K[ι] →ₗ[K] (ι → K)` kills `M²` and nothing else in `M`
(`Tangent.mem_pointIdeal_sq_iff`), so:

* `cotOfVec I x : (ι → K) →ₗ[K] m.Cotangent`, `v ↦ [∑ vᵢ (Xᵢ - xᵢ)]`, is onto
  (`cotOfVec_surjective`) with kernel the space of gradients of `I` (`ker_cotOfVec`);
* the Jacobian kernel is the annihilator of the image of that space in the dual
  (`jacobianKernel_eq_dualCoannihilator`).

Both `m ⧸ m²` and the Jacobian kernel are therefore `card ι` minus the dimension of the space
of gradients, whence `finrank_cotangent_eq_finrank_jacobianKernel`.  This is the coordinate
half of `Geometry/Spec.tangentDim_eq_finrank_jacobianKernel`; the scheme half — the stalk of
`V(I)` as a localisation — is `Geometry/Stalk.lean`.

An invertible `c × c` Jacobian minor of `c` elements of `I` at `x` therefore bounds the
Jacobian kernel: the `c` differentials are independent, so the kernel has dimension at most
`card ι − c` (`le_finrank_grad_of_isUnit_det`, `finrank_jacobianKernel_le_of_isUnit_det`).
-/

open MvPolynomial AlgebraicGeometry

namespace Height.Geometry

universe u

variable {K : Type u} [Field K] {ι : Type u} [Fintype ι]

/-- The gradient at `x`. -/
noncomputable def grad (x : ι → K) : MvPolynomial ι K →ₗ[K] (ι → K) where
  toFun g := fun i => eval x (pderiv i g)
  map_add' g h := by funext i; simp
  map_smul' c g := by funext i; simp

omit [Fintype ι] in
@[simp] theorem grad_apply (x : ι → K) (g : MvPolynomial ι K) (i : ι) :
    grad x g i = eval x (pderiv i g) := rfl

omit [Fintype ι] in
theorem grad_coordAt_self (x : ι → K) (i : ι) : grad x (Tangent.coordAt x i) i = 1 := by
  simp [Tangent.coordAt]

omit [Fintype ι] in
theorem grad_coordAt_ne (x : ι → K) {i j : ι} (h : j ≠ i) :
    grad x (Tangent.coordAt x i) j = 0 := by
  simp [Tangent.coordAt, pderiv_X_of_ne h.symm]

/-- The `K`-linear combination of the centred coordinates. -/
noncomputable def coordComb (x : ι → K) : (ι → K) →ₗ[K] MvPolynomial ι K :=
  Fintype.linearCombination K (Tangent.coordAt x)

theorem grad_coordComb (x : ι → K) (v : ι → K) : grad x (coordComb x v) = v := by
  funext j
  rw [coordComb, Fintype.linearCombination_apply, map_sum]
  simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single j (fun b _ hb => by rw [grad_coordAt_ne x hb.symm, mul_zero])
    (fun hb => absurd (Finset.mem_univ j) hb), grad_coordAt_self, mul_one]

theorem coordComb_mem (x : ι → K) (v : ι → K) : coordComb x v ∈ Tangent.pointIdeal x := by
  rw [coordComb, Fintype.linearCombination_apply]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [Algebra.smul_def]
  exact Ideal.mul_mem_left _ _ (Tangent.coordAt_mem_pointIdeal x i)

omit [Fintype ι] in
/-- Membership in the image of an ideal under a quotient map. -/
theorem mem_map_mk_iff (I J : Ideal (MvPolynomial ι K)) (g : MvPolynomial ι K) :
    Ideal.Quotient.mk I g ∈ J.map (Ideal.Quotient.mk I) ↔ g ∈ J ⊔ I := by
  rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]

/-- **The cotangent space of `V(I)` at a `K`-point, from tuples**: `v` goes to the class of
`∑ vᵢ (Xᵢ - xᵢ)`. -/
noncomputable def cotOfVec (I : Ideal (MvPolynomial ι K)) (x : ι → K) :
    (ι → K) →ₗ[K] Ideal.Cotangent ((Tangent.pointIdeal x).map (Ideal.Quotient.mk I)) where
  toFun v := Ideal.toCotangent _ ⟨Ideal.Quotient.mk I (coordComb x v),
    Ideal.mem_map_of_mem _ (coordComb_mem x v)⟩
  map_add' v w := by
    rw [← map_add]
    congr 1
    ext
    simp
  map_smul' c v := by
    have h : (Ideal.Quotient.mk I) (coordComb x (c • v)) =
        c • (Ideal.Quotient.mk I) (coordComb x v) := by
      rw [map_smul (coordComb x)]
      exact map_smul (Ideal.Quotient.mkₐ K I) c (coordComb x v)
    exact congrArg (Ideal.toCotangent _) (Subtype.ext h)

theorem grad_eq_zero_of_mem_sq {x : ι → K} {s : MvPolynomial ι K}
    (hs : s ∈ (Tangent.pointIdeal x) ^ 2) : grad x s = 0 := by
  funext i
  exact (Tangent.mem_pointIdeal_sq_iff (Ideal.pow_le_self (by norm_num) hs)).mp hs i

theorem mem_pointIdeal_sq_of_grad_eq_zero {x : ι → K} {s : MvPolynomial ι K}
    (hsM : s ∈ Tangent.pointIdeal x) (h : grad x s = 0) : s ∈ (Tangent.pointIdeal x) ^ 2 :=
  (Tangent.mem_pointIdeal_sq_iff hsM).mpr fun i => congrFun h i

theorem cotOfVec_apply (I : Ideal (MvPolynomial ι K)) (x : ι → K) (v : ι → K) :
    cotOfVec I x v = Ideal.toCotangent _ ⟨Ideal.Quotient.mk I (coordComb x v),
      Ideal.mem_map_of_mem _ (coordComb_mem x v)⟩ := rfl

/-- Every cotangent class at a `K`-point comes from a tuple. -/
theorem cotOfVec_surjective (I : Ideal (MvPolynomial ι K)) (x : ι → K) :
    Function.Surjective (cotOfVec I x) := by
  intro y
  obtain ⟨z, hz⟩ := Submodule.mkQ_surjective _ y
  obtain ⟨g, hgM, hg⟩ :=
    (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp z.2
  refine ⟨grad x g, ?_⟩
  have hsub : coordComb x (grad x g) - g ∈ (Tangent.pointIdeal x) ^ 2 := by
    refine mem_pointIdeal_sq_of_grad_eq_zero
      (Submodule.sub_mem _ (coordComb_mem x _) hgM) ?_
    rw [map_sub, grad_coordComb, sub_self]
  have hgoal : Ideal.toCotangent _ z = y := hz
  rw [← hgoal, cotOfVec_apply, ← sub_eq_zero, ← map_sub, Ideal.toCotangent_eq_zero]
  show Ideal.Quotient.mk I (coordComb x (grad x g)) - (z : MvPolynomial ι K ⧸ I) ∈
    ((Tangent.pointIdeal x).map (Ideal.Quotient.mk I)) ^ 2
  rw [← hg, ← map_sub, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ hsub

/-- **The kernel of `cotOfVec` is the space of gradients of `I`.** -/
theorem ker_cotOfVec (I : Ideal (MvPolynomial ι K)) (x : ι → K)
    (hI : I ≤ Tangent.pointIdeal x) :
    LinearMap.ker (cotOfVec I x) = Submodule.map (grad x) (Submodule.restrictScalars K I) := by
  ext v
  rw [LinearMap.mem_ker, cotOfVec_apply, Ideal.toCotangent_eq_zero]
  show Ideal.Quotient.mk I (coordComb x v) ∈
      ((Tangent.pointIdeal x).map (Ideal.Quotient.mk I)) ^ 2 ↔ _
  rw [← Ideal.map_pow, mem_map_mk_iff, Submodule.mem_map]
  constructor
  · intro h
    obtain ⟨s, hs, f, hf, hsf⟩ := Submodule.mem_sup.mp h
    refine ⟨f, hf, ?_⟩
    have h1 : grad x s + grad x f = v := by rw [← map_add, hsf, grad_coordComb]
    rwa [grad_eq_zero_of_mem_sq hs, zero_add] at h1
  · rintro ⟨f, hf, rfl⟩
    refine Submodule.mem_sup.mpr ⟨coordComb x (grad x f) - f, ?_, f, hf, by ring⟩
    refine mem_pointIdeal_sq_of_grad_eq_zero
      (Submodule.sub_mem _ (coordComb_mem x _) (hI hf)) ?_
    rw [map_sub, grad_coordComb, sub_self]

/-! ### The Jacobian kernel is the annihilator of the gradients -/

/-- The standard pairing `(ι → K) → Dual K (ι → K)`. -/
noncomputable def toDualStd : (ι → K) →ₗ[K] Module.Dual K (ι → K) where
  toFun v := ∑ i, v i • LinearMap.proj i
  map_add' v w := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c v := by simp [smul_smul, Finset.smul_sum]

theorem toDualStd_apply (v w : ι → K) : toDualStd v w = ∑ i, v i * w i := by
  simp [toDualStd]

theorem toDualStd_injective : Function.Injective (toDualStd (K := K) (ι := ι)) := by
  classical
  refine (injective_iff_map_eq_zero _).mpr fun v hv => ?_
  funext j
  have h : toDualStd v (Pi.single j 1) = 0 := by rw [hv]; rfl
  rw [toDualStd_apply, Finset.sum_eq_single j (fun b _ hb => by simp [hb])
    (fun hb => absurd (Finset.mem_univ j) hb)] at h
  simpa using h

/-- **The Jacobian kernel is the annihilator of the gradients of `I`.** -/
theorem jacobianKernel_eq_dualCoannihilator (I : Ideal (MvPolynomial ι K)) (x : ι → K) :
    jacobianKernel I x =
      (Submodule.map toDualStd
        (Submodule.map (grad x) (Submodule.restrictScalars K I))).dualCoannihilator := by
  ext v
  rw [Submodule.mem_dualCoannihilator, mem_jacobianKernel_iff]
  constructor
  · rintro h φ hφ
    obtain ⟨d, hd, rfl⟩ := Submodule.mem_map.mp hφ
    obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hd
    have := h f hf
    simpa [toDualStd] using this
  · intro h f hf
    have hmem : toDualStd (grad x f) ∈ Submodule.map toDualStd
        (Submodule.map (grad x) (Submodule.restrictScalars K I)) :=
      Submodule.mem_map_of_mem (Submodule.mem_map_of_mem hf)
    have := h _ hmem
    simpa [toDualStd] using this

/-- **The cotangent space of `V(I)` at a `K`-point has the dimension of the Jacobian
kernel.**  Both are `card ι` minus the dimension of the space of gradients of `I`: the
cotangent space because `cotOfVec` is onto with that kernel, the Jacobian kernel because it is
the annihilator of the gradients in the dual. -/
theorem finrank_cotangent_eq_finrank_jacobianKernel (I : Ideal (MvPolynomial ι K)) (x : ι → K)
    (hI : I ≤ Tangent.pointIdeal x) :
    Module.finrank K (Ideal.Cotangent ((Tangent.pointIdeal x).map (Ideal.Quotient.mk I))) =
      Module.finrank K (jacobianKernel I x) := by
  set D : Submodule K (ι → K) := Submodule.map (grad x) (Submodule.restrictScalars K I) with hD
  have h1 : Module.finrank K
      (Ideal.Cotangent ((Tangent.pointIdeal x).map (Ideal.Quotient.mk I))) +
      Module.finrank K D = Module.finrank K (ι → K) := by
    have h := LinearMap.finrank_range_add_finrank_ker (cotOfVec I x)
    rw [LinearMap.range_eq_top.mpr (cotOfVec_surjective I x), finrank_top,
      ker_cotOfVec I x hI] at h
    exact h
  have h2 : Module.finrank K D + Module.finrank K (jacobianKernel I x) =
      Module.finrank K (ι → K) := by
    have h := Subspace.finrank_add_finrank_dualCoannihilator_eq (Submodule.map toDualStd D)
    rw [← jacobianKernel_eq_dualCoannihilator I x,
      (Submodule.equivMapOfInjective toDualStd toDualStd_injective D).finrank_eq.symm] at h
    exact h
  omega

/-! ### The point ideal in the quotient -/

theorem pointIdeal_eq_vanishingIdeal (x : ι → K) :
    Tangent.pointIdeal x = MvPolynomial.vanishingIdeal K ({x} : Set (ι → K)) := by
  rw [Tangent.pointIdeal_eq_ker]
  ext f
  rw [RingHom.mem_ker, MvPolynomial.mem_vanishingIdeal_singleton_iff]
  simp

omit [Fintype ι] in
/-- The image of a maximal ideal containing `I` is maximal in the quotient. -/
theorem isMaximal_map_mk {I M : Ideal (MvPolynomial ι K)} (hIM : I ≤ M) (hM : M.IsMaximal) :
    (M.map (Ideal.Quotient.mk I)).IsMaximal := by
  have hcm : Ideal.comap (Ideal.Quotient.mk I) (M.map (Ideal.Quotient.mk I)) = M := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact sup_eq_left.mpr hIM
  have hne : M.map (Ideal.Quotient.mk I) ≠ ⊤ := fun htop =>
    hM.ne_top (by rw [← hcm, htop, Ideal.comap_top])
  exact (Ideal.map_eq_top_or_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
    hM).resolve_left hne

/-- The residue field at a `K`-point of `V(I)` is generated by `K`. -/
theorem algebraMap_quotient_surjective (I : Ideal (MvPolynomial ι K)) (x : ι → K) :
    Function.Surjective (algebraMap K ((MvPolynomial ι K ⧸ I) ⧸
      (Tangent.pointIdeal x).map (Ideal.Quotient.mk I))) := by
  intro y
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective a
  refine ⟨eval x g, ?_⟩
  show Ideal.Quotient.mk _ (Ideal.Quotient.mk I (C (eval x g))) =
    Ideal.Quotient.mk _ (Ideal.Quotient.mk I g)
  rw [Ideal.Quotient.eq, ← map_sub]
  refine Ideal.mem_map_of_mem _ ?_
  rw [Tangent.mem_pointIdeal_iff]
  simp

/-- **The gradients and the Jacobian kernel are complementary in dimension.** -/
theorem finrank_grad_add_finrank_jacobianKernel (I : Ideal (MvPolynomial ι K)) (x : ι → K) :
    Module.finrank K (Submodule.map (grad x) (Submodule.restrictScalars K I))
      + Module.finrank K (jacobianKernel I x) = Module.finrank K (ι → K) := by
  have h := Subspace.finrank_add_finrank_dualCoannihilator_eq
    (Submodule.map toDualStd (Submodule.map (grad x) (Submodule.restrictScalars K I)))
  rw [← jacobianKernel_eq_dualCoannihilator I x,
    (Submodule.equivMapOfInjective toDualStd toDualStd_injective
      (Submodule.map (grad x) (Submodule.restrictScalars K I))).finrank_eq.symm] at h
  exact h

omit [Fintype ι] in
/-- The gradients of `I` span the image of `I` under `grad x`. -/
theorem span_range_grad (I : Ideal (MvPolynomial ι K)) (x : ι → K) :
    Submodule.span K (Set.range fun h : I => grad x (h : MvPolynomial ι K))
      = Submodule.map (grad x) (Submodule.restrictScalars K I) := by
  refine le_antisymm (Submodule.span_le.mpr ?_) ?_
  · rintro _ ⟨h, rfl⟩
    exact Submodule.mem_map_of_mem h.2
  · rintro _ ⟨g, hg, rfl⟩
    exact Submodule.subset_span ⟨⟨g, hg⟩, rfl⟩

/-- **An invertible minor bounds the space of differentials from below**: `c` elements of `I`
whose `c × c` Jacobian minor at `x` is invertible have linearly independent differentials
(`Matrix.linearIndependent_rows_of_isUnit`, through the restriction `(ι → K) → (Fin c → K)`
along `S`), which lie in the image of `I` under `grad x`. -/
theorem le_finrank_grad_of_isUnit_det {c : ℕ} (I : Ideal (MvPolynomial ι K)) (x : ι → K)
    {f : Fin c → MvPolynomial ι K} (hfI : ∀ j, f j ∈ I) (S : Fin c ↪ ι)
    (hdet : IsUnit (Matrix.of fun j k => eval x (pderiv (S k) (f j))).det) :
    c ≤ Module.finrank K (Submodule.map (grad x) (Submodule.restrictScalars K I)) := by
  have hli : LinearIndependent K (fun j => grad x (f j)) := by
    have hA : IsUnit (Matrix.of fun j k => grad x (f j) (S k)) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr hdet
    exact LinearIndependent.of_comp (LinearMap.funLeft K K S)
      (Matrix.linearIndependent_rows_of_isUnit hA)
  have hsub : Submodule.span K (Set.range fun j => grad x (f j))
      ≤ Submodule.map (grad x) (Submodule.restrictScalars K I) :=
    Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact Submodule.mem_map_of_mem (hfI j))
  calc c = Fintype.card (Fin c) := by simp
    _ = Module.finrank K (Submodule.span K (Set.range fun j => grad x (f j))) :=
        (finrank_span_eq_card hli).symm
    _ ≤ _ := Submodule.finrank_mono hsub

/-- **An invertible minor bounds the Jacobian kernel from above**: with `c + d = card ι`, the
`c` independent differentials of `le_finrank_grad_of_isUnit_det` leave at most `d` dimensions
for the kernel (`finrank_grad_add_finrank_jacobianKernel`). -/
theorem finrank_jacobianKernel_le_of_isUnit_det {c d : ℕ} (hcd : c + d = Nat.card ι)
    (I : Ideal (MvPolynomial ι K)) (x : ι → K) {f : Fin c → MvPolynomial ι K}
    (hfI : ∀ j, f j ∈ I) (S : Fin c ↪ ι)
    (hdet : IsUnit (Matrix.of fun j k => eval x (pderiv (S k) (f j))).det) :
    Module.finrank K (jacobianKernel I x) ≤ d := by
  have h1 := finrank_grad_add_finrank_jacobianKernel I x
  have h2 := le_finrank_grad_of_isUnit_det I x hfI S hdet
  have h3 : Module.finrank K (ι → K) = Nat.card ι := by
    rw [Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]
  omega

/-! ### The local ring of `V(I)` at a `K`-point -/

/-- **The Zariski cotangent space of the local ring of `V(I)` at a `K`-point** has the
dimension of the Jacobian kernel: the local ring is the localisation of `K[ι] ⧸ I` at the
maximal ideal `m` of the point, so its cotangent space is `m ⧸ m²`
(`Toolbox.finrank_cotangentSpace_localization_atPrime`), computed over the residue field,
which is `K` because the point is rational (`algebraMap_quotient_surjective`). -/
theorem finrank_cotangentSpace_atPrime_map_mk (I : Ideal (MvPolynomial ι K)) (x : ι → K)
    (hI : I ≤ Tangent.pointIdeal x)
    [((Tangent.pointIdeal x).map (Ideal.Quotient.mk I)).IsPrime] :
    Module.finrank
        (IsLocalRing.ResidueField (Localization.AtPrime
          ((Tangent.pointIdeal x).map (Ideal.Quotient.mk I))))
        (IsLocalRing.CotangentSpace (Localization.AtPrime
          ((Tangent.pointIdeal x).map (Ideal.Quotient.mk I))))
      = Module.finrank K (jacobianKernel I x) := by
  have hmax : ((Tangent.pointIdeal x).map (Ideal.Quotient.mk I)).IsMaximal :=
    isMaximal_map_mk hI (Tangent.pointIdeal_isMaximal x)
  have : Nontrivial ((MvPolynomial ι K ⧸ I) ⧸
      (Tangent.pointIdeal x).map (Ideal.Quotient.mk I)) :=
    Ideal.Quotient.nontrivial_iff.mpr hmax.ne_top
  rw [Height.Toolbox.finrank_cotangentSpace_localization_atPrime,
    Height.Toolbox.finrank_cotangent_eq_of_surjective (S := K) _
      (algebraMap_quotient_surjective I x),
    finrank_cotangent_eq_finrank_jacobianKernel I x hI]

end Height.Geometry
