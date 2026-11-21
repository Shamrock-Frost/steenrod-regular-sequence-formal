import Height.Pencil.ArcsLocal
import Height.Chain.Reduction
import Height.Chain.Constructible
import Height.Chain.Multidegree
import Height.Chain.PencilPoly
import Height.Geometry.Tangent.Newton

/-!
# `lem:flag-flat`(1) at the marked point

The analytic input of the SI reduction (`Chain/Reduction.lean`) is local
flatness: along an arc in a component of the single-point marked incidence,
the kernel flag of the pencil is flat (`Isotropy.DCond`, `siLocalFlat`).  This
file derives it from the degreewise arc theorems of `Pencil/ArcsLocal.lean`
(`exists_velocity_poly` and its companions) through `hasMultidegreeGen`, the
multidegree at the generic point of an arc, which is proved here from
`Chain/Multidegree.lean`.
-/

namespace Height.Chain

open Height.Pencil Height.Orbital
open MvPolynomial Height.Geometry

universe u

/-! ### The multidegree at the generic point of an arc -/

section Arc

variable {K : Type u} [Field K] {ι : Type} {n : ℕ}

/-- Evaluation of a polynomial along an arc, read at the generic point of the
arc, i.e. in the Laurent series. -/
noncomputable def arcSpec (as : ι → PowerSeries K) :
    MvPolynomial ι K →+* LaurentSeries K :=
  (algebraMap (PowerSeries K) (LaurentSeries K)).comp
    ((MvPolynomial.aeval as : MvPolynomial ι K →ₐ[K] PowerSeries K).toRingHom)

@[simp] theorem arcSpec_apply (as : ι → PowerSeries K) (f : MvPolynomial ι K) :
    arcSpec as f
      = algebraMap (PowerSeries K) (LaurentSeries K) (MvPolynomial.aeval as f) := rfl

/-- A function nonvanishing at the base point of an arc is nonzero at the
generic point of the arc. -/
theorem arcSpec_ne_zero (as : ι → PowerSeries K) {f : MvPolynomial ι K}
    (h : MvPolynomial.aeval (fun i => PowerSeries.constantCoeff (as i)) f ≠ 0) :
    arcSpec as f ≠ 0 := by
  have h1 : (MvPolynomial.aeval as f : PowerSeries K) ≠ 0 := fun h0 =>
    h (by rw [MvPolynomial.aeval_eq_eval, ← Tangent.constantCoeff_aeval, h0, map_zero])
  intro h2
  refine h1 (IsFractionRing.injective (PowerSeries K) (LaurentSeries K) ?_)
  rw [map_zero]
  exact h2

theorem arcSpec_eq_zero (as : ι → PowerSeries K) {f : MvPolynomial ι K}
    (h : MvPolynomial.aeval as f = 0) : arcSpec as f = 0 := by
  rw [arcSpec_apply, h, map_zero]

/-- **The multidegree at the generic point of an arc.**  Let `V(P)` be
irreducible and suppose the pair of matrices read off the coordinate functions
`c` lies in `Î_{τ,d}` at every point of the dense open `V(P) ∖ V(q)`.  Then the
pair read along any arc in `V(P)` whose base point lies in `D(q)` has
multidegree `d` at the generic point of the arc.

The closed conditions (vanishing of minors) hold on `V(P) ∖ V(q)`, hence lie in
`P` by the Nullstellensatz and primality, hence vanish along the arc; the open
conditions (some minor nonzero) hold at the base point, hence along the arc,
whose value there has nonzero constant term. -/
theorem hasMultidegree_of_arc [IsAlgClosed K] [Finite ι]
    {τ : Nat.Partition n} {d : ℕ → ℕ}
    {P : Ideal (MvPolynomial ι K)} (hP : P.IsPrime) {q : MvPolynomial ι K} (hq : q ∉ P)
    (c : PairIndex (Fin n) → MvPolynomial ι K)
    (hlocus : ∀ z ∈ MvPolynomial.zeroLocus K P, MvPolynomial.aeval z q ≠ 0 →
      pairCoords.symm (fun i => MvPolynomial.aeval z (c i)) ∈ pencilLocus τ d)
    (as : ι → PowerSeries K) (harc : ∀ f ∈ P, MvPolynomial.aeval as f = 0)
    (hbase : MvPolynomial.aeval (fun i => PowerSeries.constantCoeff (as i)) q ≠ 0) :
    HasMultidegree (pairCoords.symm fun i => arcSpec as (c i)).1
      (pairCoords.symm fun i => arcSpec as (c i)).2 τ d := by
  have : Infinite (LaurentSeries K) :=
    Infinite.of_injective (algebraMap K (LaurentSeries K))
      (algebraMap K (LaurentSeries K)).injective
  refine hasMultidegree_of_hom hP hq c hlocus
    (z₀ := fun i => PowerSeries.constantCoeff (as i)) ?_ hbase (arcSpec as)
    (fun f hf => arcSpec_eq_zero as (harc f hf)) (fun f hf => arcSpec_ne_zero as hf)
  intro f hf
  rw [MvPolynomial.aeval_eq_eval, ← Tangent.constantCoeff_aeval, harc f hf, map_zero]

/-- **The multidegree at the generic point of an arc, in pair coordinates**
(`Pencil/Arcs.lean`: `pairEval`, `pairArcHom`).  This is the shape the (H1)
geometry layer consumes. -/
theorem hasMultidegree_of_pairArc [IsAlgClosed K]
    {τ : Nat.Partition n} {d : ℕ → ℕ}
    {P : Ideal (MvPolynomial (PairIndex (Fin n)) K)} (hP : P.IsPrime)
    {q : MvPolynomial (PairIndex (Fin n)) K} (hq : q ∉ P)
    (hlocus : ∀ z ∈ MvPolynomial.zeroLocus K P, MvPolynomial.eval z q ≠ 0 →
      pairCoords.symm z ∈ pencilLocus τ d)
    (Ns Ms : Matrix (Fin n) (Fin n) (PowerSeries K))
    (harc : ∀ f ∈ P, Height.Pencil.pairArcHom Ns Ms f = 0)
    (hbase : Height.Pencil.pairEval (Height.Orbital.matC Ns) (Height.Orbital.matC Ms) q ≠ 0) :
    HasMultidegree (Ns.map (algebraMap (PowerSeries K) (LaurentSeries K)))
      (Ms.map (algebraMap (PowerSeries K) (LaurentSeries K))) τ d := by
  classical
  have hbc : (fun i => PowerSeries.constantCoeff
        (Sum.elim (fun ij : Fin n × Fin n => Ns ij.1 ij.2)
          (fun ij : Fin n × Fin n => Ms ij.1 ij.2) i))
      = Sum.elim (fun ij : Fin n × Fin n => Height.Orbital.matC Ns ij.1 ij.2)
          (fun ij : Fin n × Fin n => Height.Orbital.matC Ms ij.1 ij.2) := by
    funext i
    cases i <;> rfl
  have h := hasMultidegree_of_arc hP hq
    (MvPolynomial.X : PairIndex (Fin n) → MvPolynomial (PairIndex (Fin n)) K)
    (fun z hz hqz => by
      rw [show (pairCoords.symm fun i => MvPolynomial.aeval z
          (MvPolynomial.X i : MvPolynomial (PairIndex (Fin n)) K)) = pairCoords.symm z by simp]
      exact hlocus z hz hqz)
    (Sum.elim (fun ij : Fin n × Fin n => Ns ij.1 ij.2) (fun ij : Fin n × Fin n => Ms ij.1 ij.2))
    harc (by rw [hbc]; exact hbase)
  have hpair : (pairCoords.symm fun i => arcSpec
        (Sum.elim (fun ij : Fin n × Fin n => Ns ij.1 ij.2)
          (fun ij : Fin n × Fin n => Ms ij.1 ij.2)) (MvPolynomial.X i))
      = (Ns.map (algebraMap (PowerSeries K) (LaurentSeries K)),
          Ms.map (algebraMap (PowerSeries K) (LaurentSeries K))) := by
    refine Prod.ext_iff.2 ⟨?_, ?_⟩ <;> ext i j <;> simp
  rw [hpair] at h
  exact h

/-- **The multidegree at the generic point of an arc.**  For every irreducible
`V ⊆ 𝒴_λ` (the zero locus of the prime `I`, all of whose points on the dense
open `D(g)` lie in the single-point marked incidence of type `τ` and
multidegree `d`) and every arc in `V`, the pencil of the arc read over `K⸨s⸩` —
i.e. at the generic point of the arc — again has multidegree `d`.

This is the one-degree characterisation `hasMultidegree_iff_at`
applied to the generic point.  Note that the *rank profile* at the generic
point is `Pencil/Arcs.lean`'s `arc_rank_eq`; what is needed here is the finer
Hilbert-function statement, since the whole point of the degreewise route is
that the kernel must have constant rank in each degree separately. -/
theorem hasMultidegreeGen (K : Type u) [Field K] [IsAlgClosed K] (n : ℕ) :
    ∀ (τ : Nat.Partition n) (d : ℕ → ℕ) (N₀ : Matrix (Fin n) (Fin n) K)
        (I : Ideal (MvPolynomial (SIIndex (Fin n)) K)) (g : MvPolynomial (SIIndex (Fin n)) K),
      SILocus τ d N₀ I g →
      ∀ a : SIArc n K, a.InLocus I → MvPolynomial.eval (siCoords a.base) g ≠ 0 →
        HasMultidegree (a.N.map (algebraMap (PowerSeries K) (LaurentSeries K)))
          (a.M.map (algebraMap (PowerSeries K) (LaurentSeries K))) τ d := by
  classical
  rintro τ d N₀ I g ⟨hI, hgI, hpts⟩ a ha hbase
  have h := hasMultidegree_of_arc (K := K) (n := n) (τ := τ) (d := d) hI hgI
    (fun i => (MvPolynomial.X (Sum.inl i) : MvPolynomial (SIIndex (Fin n)) K))
    (fun z hz hqz => by
      have hz' : (pairCoords.symm fun i =>
          MvPolynomial.aeval z (MvPolynomial.X (Sum.inl i) :
            MvPolynomial (SIIndex (Fin n)) K))
          = ((siCoords.symm z).1, (siCoords.symm z).2.1) := by
        refine Prod.ext_iff.2 ⟨?_, ?_⟩ <;> ext i j <;>
          simp
      rw [hz']
      exact (hpts z hz hqz).1)
    a.coords ha
    (by
      rw [SIArc.siCoords_base a] at hbase
      exact hbase)
  have hpair : (pairCoords.symm fun i => arcSpec a.coords
        (MvPolynomial.X (Sum.inl i) : MvPolynomial (SIIndex (Fin n)) K))
      = (a.N.map (algebraMap (PowerSeries K) (LaurentSeries K)),
          a.M.map (algebraMap (PowerSeries K) (LaurentSeries K))) := by
    refine Prod.ext_iff.2 ⟨?_, ?_⟩ <;> ext i j <;> simp [SIArc.coords]
  rw [hpair] at h
  exact h

end Arc


/-! ### `lem:flag-flat`(1) at the marked point -/

section Flat

variable {K : Type u} [Field K] [IsAlgClosed K] {n : ℕ}

/-- **`lem:flag-flat`(1) at the marked point**: along an arc of the single-point
marked incidence the pencil velocity is kernel flat over `K⟦u⟧`.

The proof is the paper's degreewise route.  In each degree `e ≫ 0` the kernel
of `P_s^k` on the coefficient vectors has the same dimension at the base point
and at the generic point of the arc — this is exactly what the multidegree gives
at the two ends (`hasMultidegreeGen`) — so the kernel of the coefficient matrix
over `K⟦s⟧` lifts; the `s`-linear term of the lifted relation is
`D_k(Ṗ) v + P^k v̇ = 0` (extracted with dual numbers), and it is an identity of
*polynomial* vectors, hence survives the specialisation `t ↦ t₀ + u` at every
point of `ℙ¹` (`ker_map_eq_mapSpan`: over the principal ideal domain `K[t]` the
kernel generates the kernel after base change, which is what the function-field
form, `kernel_flat` of `Pencil/Arcs.lean`, does not provide).

For the other summand of the shifted representative, `∂_u P`, kernel flatness is
proved outright (`Pencil.dcond_dPat`); the commutator correction is
`Pencil.dcond_commutator`, so `Pencil.dcond_Rdot` needs nothing else.  The velocity decomposition of
`lem:local-model`(3) gives this (`Pencil.exists_velocity_decomposition`); the
converse is not proved in this repository. -/
theorem siLocalFlat :
    ∀ (τ : Nat.Partition n) (d : ℕ → ℕ) (N₀ : Matrix (Fin n) (Fin n) K)
        (C : SIComponent τ d N₀),
      ∀ z ∈ MvPolynomial.zeroLocus K C.I, MvPolynomial.eval z C.g ≠ 0 →
        ∀ m : ArcAt C.I z,
        Isotropy.DCond (Pat (siCoords.symm z).1 (siCoords.symm z).2.1 (siCoords.symm z).2.2)
          (Qat (pencil m.a.vel.1 m.a.vel.2.1) (siCoords.symm z).2.2) := by
  intro τ d N₀ ⟨I, g, hloc⟩ z hz hgz ⟨a, ha, hb⟩
  have hbase : HasMultidegree (Height.Orbital.matC a.N) (Height.Orbital.matC a.M) τ d := by
    have h := (hloc.locus z hz hgz).1.2.2
    rw [← hb] at h
    exact h
  have hg := hasMultidegreeGen K n τ d N₀ I g hloc a ha
    (by rw [hb, siCoords.apply_symm_apply]; exact hgz)
  rw [← hb]
  exact Height.Pencil.dcond_of_arc a.N a.M τ d hbase hg _

end Flat

end Height.Chain
