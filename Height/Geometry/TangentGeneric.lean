import Height.Geometry.Spec
import Height.Geometry.Dimension.LocClosed

/-!
# The tangent-generic point: from the scheme-level tangent theory to coordinates

`Geometry/Spec.lean` §5–6 proves the tangent and
arc statements of the API at a *regular* `K`-point of `V(I)`
(`topologicalKrullDim_le_tangentDim`, `tangentDim_eq_finrank_jacobianKernel`,
`exists_arc_of_mem_jacobianKernel`) and proves that the regular points form a
dense open of the scheme `Vsch I` (`generic_isRegularLocalRing`).  What no file
states is the classical consequence every consumer needs:

> at a *tangent-generic* `K`-point of an irreducible affine variety, the
> dimension of the variety is at most the dimension of its tangent space, and
> every tangent vector there is the velocity of an arc.

`exists_tangentGeneric_pt` is that statement: nonvanishing conditions in, one
`K`-point out with all three conclusions.  It is the converse of
`Geometry/Tangent/Dense.lean`'s `exists_tangent_generic`, which produces the
Jacobian witness but no inequality.

## Route

`generic_isRegularLocalRing` lives on the scheme `Vsch I`; the consumers live on
the `K`-points of `MvPolynomial.zeroLocus K I`.  `generic_V_of_generic_Vsch`
transports the generic quantifier along the closed immersion `Vι I` (whose image
is `V I` and which is a homeomorphism onto it, so a dense open of `Vsch I`
becomes a dense open of `V I`), and `Interface.generic_V_iff` then reads that
dense open as a single polynomial `h ∉ I`.  The finitely many further conditions
are multiplied into `h` (`I` is prime), and a nonempty basic open of `V(I)` has a
`K`-point over an algebraically closed field
(`Dimension/LocClosed.nonempty_inter_nonvanishing` with the Nullstellensatz
`MvPolynomial.IsPrime.vanishingIdeal_zeroLocus`).  At that point the three
conclusions are the three theorems of `Spec.lean` §5–6.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Height.Toolbox

namespace Height.Geometry

universe u

section Transport

variable {K : Type u} [Field K] {ι : Type u}

/-- **The generic quantifier, transported from the subscheme to the ambient space.**
`Vι I` is a closed immersion with image `V I`, hence a homeomorphism onto `V I`, so a
dense open subset of `Vsch I` is the trace on `V I` of an open subset of `𝔸`. -/
theorem generic_V_of_generic_Vsch (I : Ideal (MvPolynomial ι K)) {P : Vsch I → Prop}
    (h : Generic (Set.univ : Set (Vsch I)) P) :
    Generic (V (I : Set (MvPolynomial ι K)))
      (fun y => ∀ p : Vsch I, Vι I p = y → P p) := by
  obtain ⟨U, hUopen, hUdense, hUP⟩ := h
  have hemb : IsClosedEmbedding (Vι I).base := IsClosedImmersion.isClosedEmbedding (Vι I)
  obtain ⟨U', hU'open, hU'⟩ := hemb.isEmbedding.isInducing.isOpen_iff.mp hUopen
  refine ⟨U', hU'open, ?_, ?_⟩
  · have himg : U' ∩ V (I : Set (MvPolynomial ι K)) = (Vι I) '' U := by
      rw [← range_Vι I, ← hU', Set.image_preimage_eq_inter_range]
    have hUuniv : closure U = Set.univ := by
      rw [Set.inter_univ] at hUdense
      exact Set.univ_subset_iff.mp hUdense
    rw [himg, hemb.isClosedMap.closure_image_eq_of_continuous (Vι I).continuous U, hUuniv,
      Set.image_univ, range_Vι]
  · rintro y ⟨hyU', hyV⟩ p hp
    refine hUP p ⟨?_, trivial⟩
    rw [← hU', Set.mem_preimage, hp]
    exact hyU'

end Transport

section TangentGeneric

variable {K : Type u} [Field K] {ι : Type u} [Fintype ι]

/-- **The tangent-generic point.**  For `I` prime over an algebraically closed field and
finitely many `h ∈ s` outside `I`, there is a `K`-point `x` of `V(I)` off every `V(h)` at
which the dimension of `V(I)` is at most the dimension of the Jacobian kernel, and every
Jacobian-kernel vector is the velocity of an arc of `V(I)` based at `x`.

This is the missing classical converter: `Spec.lean` §5–6 has the three conclusions at a
regular `K`-point, and `generic_isRegularLocalRing` has the regular points on a dense open;
here the dense open is intersected with the `D(h)` and a `K`-point is produced in it.

Note that `jacobianKernel I x` **is** a `Submodule K (ι → K)`, so a consumer that needs the
tangent space as a submodule uses it directly. -/
theorem exists_tangentGeneric_pt [IsAlgClosed K] (I : Ideal (MvPolynomial ι K)) [I.IsPrime]
    (s : Finset (MvPolynomial ι K)) (hs : ∀ h ∈ s, h ∉ I) :
    ∃ x ∈ MvPolynomial.zeroLocus K I,
      (∀ h ∈ s, MvPolynomial.eval x h ≠ 0) ∧
      affineDim (MvPolynomial.zeroLocus K I)
          ≤ ((Module.finrank K (jacobianKernel I x) : ℕ) : WithBot ℕ∞) ∧
      ∀ v ∈ jacobianKernel I x, ∃ a : Arc I,
        a.base = x ∧ ∀ i, PowerSeries.coeff 1 (a.coords i) = v i := by
  classical
  -- the regular locus of `V(I)`, as a polynomial `h₀ ∉ I`
  have hgen : Generic (V (I : Set (MvPolynomial ι K)))
      (fun y => ∀ x : ι → K, (ptEquiv K x : 𝔸(ι; Spec (.of K))) = y →
        ∀ p : Vsch I, Vι I p = (ptEquiv K x : 𝔸(ι; Spec (.of K))) →
          IsRegularLocalRing ((Vsch I).presheaf.stalk p)) :=
    (generic_V_of_generic_Vsch I generic_isRegularLocalRing).mono
      fun y hy x hx p hp => hy p (by rw [hp, hx])
  obtain ⟨h₀, hh₀, hreg⟩ := (generic_V_iff _).mp hgen
  -- one polynomial for all the conditions
  set H : MvPolynomial ι K := h₀ * ∏ g ∈ s, g with hH
  have hprod : (∏ g ∈ s, g) ∉ I := by
    refine Finset.prod_induction _ (fun f => f ∉ I) (fun a b ha hb hab => ?_)
      (fun hone => ‹I.IsPrime›.ne_top ((Ideal.eq_top_iff_one I).mpr hone)) hs
    exact (‹I.IsPrime›.mem_or_mem hab).elim ha hb
  have hHI : H ∉ I := fun hmem => (‹I.IsPrime›.mem_or_mem hmem).elim hh₀ hprod
  -- a `K`-point of `V(I)` off `V(H)`
  have hvan : MvPolynomial.vanishingIdeal K (MvPolynomial.zeroLocus K I) = I :=
    MvPolynomial.IsPrime.vanishingIdeal_zeroLocus I
  obtain ⟨x, hxV, hxH⟩ :=
    nonempty_inter_nonvanishing (K := K) (C := MvPolynomial.zeroLocus K I) (g := H)
      (by rw [hvan]; exact hHI)
  have hxH' : MvPolynomial.aeval x H ≠ 0 := hxH
  have hx₀ : MvPolynomial.aeval x h₀ ≠ 0 := by
    rw [hH, map_mul] at hxH'
    exact left_ne_zero_of_mul hxH'
  have hxs : ∀ g ∈ s, MvPolynomial.eval x g ≠ 0 := by
    intro g hg hzero
    refine hxH' ?_
    rw [hH, map_mul, map_prod, Finset.prod_eq_zero hg ?_, mul_zero]
    rwa [MvPolynomial.aeval_eq_eval]
  -- the corresponding point of the subscheme, and its regularity
  have hxI : ∀ f ∈ I, MvPolynomial.aeval x f = 0 := fun f hf => hxV f hf
  obtain ⟨p, hp⟩ : ∃ p : Vsch I, Vι I p = (ptEquiv K x : 𝔸(ι; Spec (.of K))) := by
    have hmem : (ptEquiv K x : 𝔸(ι; Spec (.of K))) ∈ V (I : Set (MvPolynomial ι K)) :=
      (pt_mem_V_iff _ x).2 fun f hf => hxI f hf
    rw [← range_Vι I] at hmem
    exact hmem
  have hregp : IsRegularLocalRing ((Vsch I).presheaf.stalk p) := hreg x hxV hx₀ p hp
  refine ⟨x, hxV, hxs, ?_, fun v hv => exists_arc_of_mem_jacobianKernel p hp hregp hv⟩
  rw [affineDim_zeroLocus, ← topologicalKrullDim_Vsch,
    ← tangentDim_eq_finrank_jacobianKernel x p hp]
  exact topologicalKrullDim_le_tangentDim x p hp

end TangentGeneric

end Height.Geometry
