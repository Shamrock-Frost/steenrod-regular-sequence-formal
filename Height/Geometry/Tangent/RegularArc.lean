import Height.Geometry.Tangent.Dense
import Height.Geometry.Tangent.Cotangent
import Height.Toolbox.LocalizationQuotient
import Height.Toolbox.RegularLocalRing

/-!
# Arcs at a regular `K`-point

`Geometry/Tangent/ArcOfTangent.lean` reduces the statement that every tangent vector at `x`
is the velocity of an arc to the statement that `c` equations `f₁, …, f_c ∈ I` with an
invertible Jacobian
minor at `x` already cut out `I` near `x`.  `Geometry/Tangent/Generic.lean` gets that at a
*generic* point of a prime `I`; here it is obtained at *any* point where the local ring of
`V(I)` is regular, with no hypothesis on `I`.

`exists_arc_of_regular_pt` is the whole argument, in coordinates:

* the differentials of `I` at `x` span a space of dimension `c` (`span_range_grad`), so `c`
  elements `f₁, …, f_c ∈ I` have an invertible `c × c` minor there
  (`Tangent.exists_isUnit_det_of_le_finrank`), and their own differentials already span that
  space — the minor makes them independent (`le_finrank_grad_of_isUnit_det`), so
  `J = (f₁, …, f_c)` and `I` have the same Jacobian kernel, of dimension
  `d = card ι − c` (`finrank_grad_add_finrank_jacobianKernel`);
* `A ⧸ J A` is a regular local ring (`Tangent.isRegularLocalRing_quotient_map_of_jacobian`,
  the Jacobian criterion) and `A ⧸ I A` is one by hypothesis, where `A = K[ι]_x`; both have
  embedding dimension `d` (`finrank_cotangentSpace_atPrime_map_mk` through
  `Toolbox.quotientLocalizationEquiv`), hence Krull dimension `d`
  (`IsRegularLocalRing.iff_finrank_cotangentSpace`);
* a regular local ring is a domain (`Toolbox.isDomain_of_isRegularLocalRing`), so
  `A ⧸ J A ↠ A ⧸ I A` is a surjection of domains of the same finite dimension, therefore
  injective (`injective_of_ringKrullDim_eq`): `I A = J A`;
* every prime `Q` with `J ≤ Q` and `Q ≤ pointIdeal x` then contains `I`, because `Q` is the
  contraction of `Q A` (`IsLocalization.under_map_of_isPrime_disjoint`) and
  `I ≤ I A ∩ K[ι] = J A ∩ K[ι] ≤ Q`.  This is the hypothesis of
  `Tangent.exists_arc_of_tangent_of_forall_prime`.

The scheme-level statements are `Geometry/Spec.lean` §6.
-/

open MvPolynomial AlgebraicGeometry Height.Toolbox

namespace Height.Geometry

universe u

variable {K : Type u} [Field K] {ι : Type u} [Fintype ι]

/-- **Tangent vectors at a regular `K`-point are arc velocities.**  If the local ring of
`V(I)` at the `K`-point `x` — the localisation of `K[ι] ⧸ I` at `x`, presented here as
`K[ι]_x ⧸ I K[ι]_x` — is regular, then every `v` in the Jacobian kernel of `I` at `x` is the
first-order part of a formal solution of `I` with constant part `x`. -/
theorem exists_arc_of_regular_pt {I : Ideal (MvPolynomial ι K)} {x : ι → K}
    (hI : I ≤ Tangent.pointIdeal x)
    (hreg : IsRegularLocalRing (Localization.AtPrime (Tangent.pointIdeal x) ⧸
      I.map (algebraMap (MvPolynomial ι K) (Localization.AtPrime (Tangent.pointIdeal x)))))
    {v : ι → K} (hv : v ∈ jacobianKernel I x) :
    ∃ a : ι → PowerSeries K, (∀ i, PowerSeries.constantCoeff (a i) = x i) ∧
      (∀ i, PowerSeries.coeff 1 (a i) = v i) ∧ ∀ g ∈ I, aeval a g = 0 := by
  classical
  have hmmax : (Tangent.pointIdeal x).IsMaximal := Tangent.pointIdeal_isMaximal x
  have hmp : (Tangent.pointIdeal x).IsPrime := hmmax.isPrime
  set φ := algebraMap (MvPolynomial ι K) (Localization.AtPrime (Tangent.pointIdeal x)) with hφ
  set d := Module.finrank K (jacobianKernel I x) with hd
  set c := Module.finrank K (Submodule.map (grad x) (Submodule.restrictScalars K I)) with hc
  have hcard : Module.finrank K (ι → K) = Nat.card ι := by
    rw [Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]
  have hcd : c + d = Nat.card ι := by
    rw [← hcard]; exact finrank_grad_add_finrank_jacobianKernel I x
  -- the equations
  obtain ⟨fI, S, hdet⟩ := Tangent.exists_isUnit_det_of_le_finrank
    (fun h : I => grad x (h : MvPolynomial ι K)) (c := c)
    (by rw [span_range_grad])
  set f : Fin c → MvPolynomial ι K := fun j => (fI j : MvPolynomial ι K) with hf
  have hfI : ∀ j, f j ∈ I := fun j => (fI j).2
  have hfM : ∀ j, eval x (f j) = 0 := fun j => Tangent.mem_pointIdeal_iff.mp (hI (hfI j))
  have hJdet : IsUnit (Matrix.of fun j k => eval x (pderiv (S k) (f j))).det := hdet
  set J : Ideal (MvPolynomial ι K) := Ideal.span (Set.range f) with hJdef
  have hJI : J ≤ I := Ideal.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hfI j)
  have hJm : J ≤ Tangent.pointIdeal x := hJI.trans hI
  -- the local ring of `V(f)` is regular
  have hregJ : IsRegularLocalRing (Localization.AtPrime (Tangent.pointIdeal x) ⧸ J.map φ) :=
    Tangent.isRegularLocalRing_quotient_map_of_jacobian hcd hfM S hJdet
  -- the differentials of `J` are those of `I`
  have hJgrad : Submodule.map (grad x) (Submodule.restrictScalars K J)
      = Submodule.map (grad x) (Submodule.restrictScalars K I) := by
    refine Submodule.eq_of_le_of_finrank_le (Submodule.map_mono (fun a ha => hJI ha)) ?_
    rw [← hc]
    exact le_finrank_grad_of_isUnit_det J x (fun j => Ideal.subset_span ⟨j, rfl⟩) S hJdet
  have hdJ : Module.finrank K (jacobianKernel J x) = d := by
    have h1 := finrank_grad_add_finrank_jacobianKernel J x
    have h2 := finrank_grad_add_finrank_jacobianKernel I x
    rw [hJgrad] at h1
    omega
  -- both local rings have dimension `d`
  have := hreg
  have := hregJ
  have hpI : ((Tangent.pointIdeal x).map (Ideal.Quotient.mk I)).IsPrime := isPrime_map_mk hI
  have hpJ : ((Tangent.pointIdeal x).map (Ideal.Quotient.mk J)).IsPrime := isPrime_map_mk hJm
  have hdimI : ringKrullDim (Localization.AtPrime (Tangent.pointIdeal x) ⧸ I.map φ)
      = (d : WithBot ℕ∞) := by
    rw [← (IsRegularLocalRing.iff_finrank_cotangentSpace _).mp hreg,
      ← Height.Toolbox.finrank_cotangentSpace_of_ringEquiv (quotientLocalizationEquiv hI),
      finrank_cotangentSpace_atPrime_map_mk I x hI]
  have hdimJ : ringKrullDim (Localization.AtPrime (Tangent.pointIdeal x) ⧸ J.map φ)
      = (d : WithBot ℕ∞) := by
    rw [← (IsRegularLocalRing.iff_finrank_cotangentSpace _).mp hregJ,
      ← Height.Toolbox.finrank_cotangentSpace_of_ringEquiv (quotientLocalizationEquiv hJm),
      finrank_cotangentSpace_atPrime_map_mk J x hJm, hdJ]
  -- so `I` and `J` generate the same ideal at `x`
  have hmapJI : J.map φ ≤ I.map φ := Ideal.map_mono hJI
  have hdomI : IsDomain (Localization.AtPrime (Tangent.pointIdeal x) ⧸ I.map φ) :=
    isDomain_of_isRegularLocalRing (Localization.AtPrime (Tangent.pointIdeal x) ⧸ I.map φ)
  have hdomJ : IsDomain (Localization.AtPrime (Tangent.pointIdeal x) ⧸ J.map φ) :=
    isDomain_of_isRegularLocalRing (Localization.AtPrime (Tangent.pointIdeal x) ⧸ J.map φ)
  have hlift : ∀ a ∈ J.map φ, (Ideal.Quotient.mk (I.map φ)) a = 0 := fun a ha =>
    Ideal.Quotient.eq_zero_iff_mem.mpr (hmapJI ha)
  have hgsurj : Function.Surjective
      (Ideal.Quotient.lift (J.map φ) (Ideal.Quotient.mk (I.map φ)) hlift) := by
    intro y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Ideal.Quotient.mk (J.map φ) a, rfl⟩
  have hginj : Function.Injective
      (Ideal.Quotient.lift (J.map φ) (Ideal.Quotient.mk (I.map φ)) hlift) :=
    injective_of_ringKrullDim_eq (B := Localization.AtPrime (Tangent.pointIdeal x) ⧸ J.map φ)
      (C := Localization.AtPrime (Tangent.pointIdeal x) ⧸ I.map φ) hdimJ hdimI _ hgsurj
  have hmapIJ : I.map φ ≤ J.map φ := by
    intro y hy
    refine Ideal.Quotient.eq_zero_iff_mem.mp (hginj ?_)
    show (Ideal.Quotient.mk (I.map φ)) y = _
    rw [map_zero, Ideal.Quotient.eq_zero_iff_mem.mpr hy]
  -- every prime between `J` and `x` contains `I`
  have hP : ∀ Q : Ideal (MvPolynomial ι K), Q.IsPrime → J ≤ Q →
      (∀ s ∈ Q, eval x s = 0) → I ≤ Q := by
    intro Q hQ hJQ hQz
    have hQM : Q ≤ Tangent.pointIdeal x := fun s hs => Tangent.mem_pointIdeal_iff.mpr (hQz s hs)
    have hdisj : Disjoint ((Tangent.pointIdeal x).primeCompl : Set (MvPolynomial ι K))
        (Q : Set (MvPolynomial ι K)) := Set.disjoint_left.mpr fun a ha hb => ha (hQM hb)
    have heq : Ideal.comap φ (Q.map φ) = Q :=
      IsLocalization.under_map_of_isPrime_disjoint (Tangent.pointIdeal x).primeCompl _ hQ hdisj
    refine le_trans (le_trans Ideal.le_comap_map (Ideal.comap_mono hmapIJ)) ?_
    rw [← heq]
    exact Ideal.comap_mono (Ideal.map_mono hJQ)
  -- and the arc
  exact Tangent.exists_arc_of_tangent_of_forall_prime I f hfI x S hJdet
    (fun g hg => Tangent.mem_pointIdeal_iff.mp (hI hg)) hP v
    ((mem_jacobianKernel_iff I x v).mp hv)

end Height.Geometry
