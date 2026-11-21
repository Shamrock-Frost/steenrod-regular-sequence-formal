import Height.Chain.PencilPoly
import Height.Chain.Frame

/-!
# The single-point incidence `𝒴_λ`: constructibility

`thm:h2-conditional` needs its two single-point incidences as `SIComponent`s —
irreducible subvarieties of the single-point marked locus with a dense open
inside it.  Producing one from an irreducible subvariety whose points lie in the
locus is `Geometry.exists_nonvanishing_subset_of_constructible`, and the input
that lemma asks for is the constructibility of the locus.  This file supplies
it, as the single-point analogue of `isConstructible_markedLocus`: the same
proof with one marked parameter instead of two and no distinctness condition.

The universal member over the single-point coordinate ring is `siGenMember`
(`Chain/Frame.lean`); `Chain/PencilPoly.lean`'s `markMember` is its two-parameter
sibling, and `Pencil.genMember` the same thing again a layer lower.
-/

namespace Height.Chain

open Matrix Height.Pencil Height.Geometry MvPolynomial

universe u

variable {K : Type u} [Field K] {n : ℕ}

/-- The universal member specialised at a point is the member there.  `specMat`
uses `aeval` and `frameAt` uses `eval`; on a `K`-algebra map to `K` they
agree. -/
theorem specMat_siGenMember (x : SIIndex (Fin n) → K) :
    specMat (siGenMember (K := K) (n := n)) x = siMember (siCoords.symm x) := by
  rw [← frameAt_siGenMember x]
  ext i j
  show aeval x _ = eval x _
  rw [MvPolynomial.aeval_eq_eval]

/-- Powers of the universal member specialise to powers of the member. -/
theorem specMat_siGenMember_pow (x : SIIndex (Fin n) → K) (k : ℕ) :
    specMat ((siGenMember (K := K) (n := n)) ^ k) x = (siMember (siCoords.symm x)) ^ k := by
  show (RingHom.mapMatrix (specRing x)) ((siGenMember (K := K) (n := n)) ^ k) = _
  rw [map_pow]
  congr 1
  exact specMat_siGenMember x

/-- **The member lies in the orbit closure**: a Zariski closed condition on the
single-point coordinates, cut out by the minors of the powers of the universal
member.  The single-point analogue of `isLocClosed_member_orbitClosure`. -/
theorem isLocClosed_siMember_orbitClosure (N₀ : Matrix (Fin n) (Fin n) K) :
    IsLocClosed {x : SIIndex (Fin n) → K | siMember (siCoords.symm x) ∈ orbitClosure N₀} := by
  have hset : {x : SIIndex (Fin n) → K | siMember (siCoords.symm x) ∈ orbitClosure N₀}
      = {x : SIIndex (Fin n) → K | ∀ a : (k : ℕ) ×
            ((Fin (Matrix.rank (N₀ ^ k) + 1) → Fin n)
              × (Fin (Matrix.rank (N₀ ^ k) + 1) → Fin n)),
          aeval x ((((siGenMember (K := K) (n := n)) ^ a.1).submatrix a.2.1 a.2.2).det) = 0} := by
    refine Set.Subset.antisymm (fun x hx a => ?_) (fun x hx k => ?_)
    · rw [← det_submatrix_specMat, specMat_siGenMember_pow]
      exact (rank_le_iff_minors _ _).1 (hx a.1) a.2.1 a.2.2
    · rw [← specMat_siGenMember_pow]
      refine (rank_le_iff_minors _ _).2 fun f g => ?_
      rw [det_submatrix_specMat]
      exact hx ⟨k, (f, g)⟩
  rw [hset]
  exact isLocClosed_zeros_family _

/-- **`𝒴_λ` is constructible.**  The single-point analogue of
`isConstructible_markedLocus`: the pencil half is the preimage of `Î_{τ,d}` under
the coordinate projection, and the marked half is the closed condition above. -/
theorem isConstructible_singleMarkedLocus [Infinite K] (τ : Nat.Partition n) (d : ℕ → ℕ)
    (N₀ : Matrix (Fin n) (Fin n) K) :
    IsAffineConstructible (siCoords '' (singleMarkedLocus (K := K) τ d N₀)) := by
  rw [siCoords.image_eq_preimage_symm]
  have hset : siCoords.symm ⁻¹' (singleMarkedLocus (K := K) τ d N₀)
      = ((fun x : SIIndex (Fin n) → K => fun i : PairIndex (Fin n) => x (Sum.inl i)) ⁻¹'
            (pairCoords.symm ⁻¹' pencilLocus (K := K) τ d))
        ∩ {x : SIIndex (Fin n) → K | siMember (siCoords.symm x) ∈ orbitClosure N₀} := by
    ext x
    exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩
  rw [hset]
  refine IsAffineConstructible.inter ?_ (isLocClosed_siMember_orbitClosure N₀).isConstructible
  refine IsAffineConstructible.preimage isPolyMap_restrict_inl ?_
  rw [← pairCoords.image_eq_preimage_symm]
  exact isConstructible_pencilLocus τ d


/-! ### The components -/

/-- **A single-point incidence from a subvariety that lands in the locus.**  If
`V` is irreducible and closed in the single-point coordinates and meets `𝒴_λ` in
a dense subset, then `V` carries an `SIComponent`: the dense open comes from
`Geometry.exists_nonvanishing_subset_of_constructible` fed by
`isConstructible_singleMarkedLocus`.

Membership of *all* of `V` in the locus is never available — the closure of a
component of the cone contains the zero pencil — which is exactly why `SILocus`
asks only for a dense open. -/
theorem exists_siComponent_of_dense [IsAlgClosed K] [Infinite K]
    (τ : Nat.Partition n) (d : ℕ → ℕ) (N₀ : Matrix (Fin n) (Fin n) K)
    {V : Set (SIIndex (Fin n) → K)} (hVcl : zclosure V = V)
    (hVp : (MvPolynomial.vanishingIdeal K V).IsPrime)
    (hdense : zclosure ((siCoords '' singleMarkedLocus (K := K) τ d N₀) ∩ V) = V) :
    ∃ C : SIComponent τ d N₀, C.I = MvPolynomial.vanishingIdeal K V := by
  obtain ⟨g, hgI, hgsub⟩ := Height.Geometry.exists_nonvanishing_subset_of_constructible
    (isConstructible_singleMarkedLocus τ d N₀) hVcl hVp hdense
  refine ⟨⟨MvPolynomial.vanishingIdeal K V, g, hVp, hgI, ?_⟩, rfl⟩
  intro z hz hgz
  have hzV : z ∈ V := hVcl ▸ hz
  obtain ⟨q, hq, hqz⟩ := hgsub ⟨hzV, by
    show MvPolynomial.aeval z g ≠ 0
    rw [MvPolynomial.aeval_eq_eval]
    exact hgz⟩
  rw [← hqz, siCoords.symm_apply_apply]
  exact hq

/-! ### The projection from the two-point incidence -/

/-- The polynomials defining the projection: the pencil coordinates, and the
`i`-th marked parameter. -/
noncomputable def siProjPoly (i : Fin 2) :
    SIIndex (Fin n) → MvPolynomial (MarkedIndex (Fin n)) K :=
  Sum.elim (fun j => MvPolynomial.X (Sum.inl j)) (fun _ => MvPolynomial.X (Sum.inr i))

/-- The projection of the two-point coordinates onto the single-point
coordinates at the `i`-th marked parameter: `(z, x₁, x₂) ↦ (z, x_i)`. -/
def siProj (i : Fin 2) (x : MarkedIndex (Fin n) → K) : SIIndex (Fin n) → K :=
  Sum.elim (fun j => x (Sum.inl j)) (fun _ => x (Sum.inr i))

theorem siProj_apply (i : Fin 2) (x : MarkedIndex (Fin n) → K) (j : SIIndex (Fin n)) :
    siProj i x j = MvPolynomial.aeval x (siProjPoly (K := K) (n := n) i j) := by
  cases j <;> simp [siProj, siProjPoly]

theorem isPolyMap_siProj (i : Fin 2) : IsPolyMap (siProj (K := K) (n := n) i) :=
  ⟨siProjPoly i, siProj_apply i⟩

@[simp] theorem siProj_markedCoords (i : Fin 2)
    (p : Matrix (Fin n) (Fin n) K × Matrix (Fin n) (Fin n) K × K × K) :
    siProj i (markedCoords p) = siCoords (p.1, p.2.1, ![p.2.2.1, p.2.2.2] i) := by
  funext j
  rcases j with (ij | ij) | u <;> rfl

/-- **Forgetting the other marked point carries `Ŷ` into `𝒴_λ`.**  The pointwise
form of `Pencil.singleMarkedLocus_nonempty_of_markedLocus`. -/
theorem siProj_mem_singleMarkedLocus (i : Fin 2) {τ : Nat.Partition n} {d : ℕ → ℕ}
    {N₀ : Matrix (Fin n) (Fin n) K} {x : MarkedIndex (Fin n) → K}
    (hx : x ∈ markedCoords '' markedLocus (K := K) τ d N₀) :
    siProj i x ∈ siCoords '' singleMarkedLocus (K := K) τ d N₀ := by
  obtain ⟨p, hp, rfl⟩ := hx
  refine ⟨(p.1, p.2.1, ![p.2.2.1, p.2.2.2] i), ⟨hp.1, ?_⟩, (siProj_markedCoords i p).symm⟩
  fin_cases i
  · simpa using hp.2.2.1
  · simpa using hp.2.2.2

/-- **The single-point incidence at a marked parameter**, from an irreducible
subvariety of the two-point incidence: project, take the Zariski closure, and
read off a dense open inside the locus.

Two conclusions, both needed downstream.  The ideal of the component is the
*contraction* of `I` along the projection — so an arc killing `I` projects to an
arc killing `C.I`, which is how (SI) for the component reaches a direction of
the two-point incidence.  And the dense open of `V(I)` projects into `V(C.I)`,
which is where (SI) is applied. -/
theorem exists_siComponent_of_markedComponent [IsAlgClosed K] [Infinite K]
    (τ : Nat.Partition n) (d : ℕ → ℕ) (N₀ : Matrix (Fin n) (Fin n) K) (i : Fin 2)
    {I : Ideal (MvPolynomial (MarkedIndex (Fin n)) K)} (hIp : I.IsPrime)
    {q : MvPolynomial (MarkedIndex (Fin n)) K} (hq : q ∉ I)
    (hlocus : ∀ y ∈ MvPolynomial.zeroLocus K I, MvPolynomial.aeval y q ≠ 0 →
      y ∈ markedCoords '' markedLocus (K := K) τ d N₀) :
    ∃ C : SIComponent τ d N₀,
      C.I = I.comap (MvPolynomial.aeval (siProjPoly (K := K) (n := n) i) :
          MvPolynomial (SIIndex (Fin n)) K →ₐ[K] MvPolynomial (MarkedIndex (Fin n)) K) ∧
      ∀ y ∈ MvPolynomial.zeroLocus K I, MvPolynomial.aeval y q ≠ 0 →
        siProj i y ∈ MvPolynomial.zeroLocus K C.I := by
  classical
  have hz : MvPolynomial.vanishingIdeal K (MvPolynomial.zeroLocus K I) = I :=
    MvPolynomial.IsPrime.vanishingIdeal_zeroLocus I
  have hzp : (MvPolynomial.vanishingIdeal K (MvPolynomial.zeroLocus K I)).IsPrime := by
    rw [hz]; exact hIp
  set W : Set (MarkedIndex (Fin n) → K) :=
    MvPolynomial.zeroLocus K I ∩ {y | MvPolynomial.aeval y q ≠ 0} with hWdef
  have hWne : W.Nonempty :=
    Height.Geometry.nonempty_inter_nonvanishing (by rw [hz]; exact hq)
  have hWvi : MvPolynomial.vanishingIdeal K W = I := by
    rw [hWdef, Height.Geometry.vanishingIdeal_inter_dense hzp hWne, hz]
  have hWp : (MvPolynomial.vanishingIdeal K W).IsPrime := by rw [hWvi]; exact hIp
  set V : Set (SIIndex (Fin n) → K) := zclosure (siProj i '' W) with hVdef
  have hVcl : zclosure V = V := zclosure_zclosure _
  have hVvi : MvPolynomial.vanishingIdeal K V
      = I.comap (MvPolynomial.aeval (siProjPoly (K := K) (n := n) i) :
          MvPolynomial (SIIndex (Fin n)) K →ₐ[K] MvPolynomial (MarkedIndex (Fin n)) K) := by
    rw [hVdef, vanishingIdeal_zclosure,
      Height.Geometry.vanishingIdeal_image (siProj_apply i) W, hWvi]
  have hVp : (MvPolynomial.vanishingIdeal K V).IsPrime := by
    rw [hVdef, vanishingIdeal_zclosure]
    exact Height.Geometry.irreducible_image (isPolyMap_siProj i) hWp
  have hSsub : siProj i '' W ⊆ siCoords '' singleMarkedLocus (K := K) τ d N₀ := by
    rintro _ ⟨y, hy, rfl⟩
    exact siProj_mem_singleMarkedLocus i (hlocus y hy.1 hy.2)
  have hdense : zclosure ((siCoords '' singleMarkedLocus (K := K) τ d N₀) ∩ V) = V := by
    refine le_antisymm ?_ ?_
    · conv_rhs => rw [← hVcl]
      exact zclosure_mono Set.inter_subset_right
    · exact zclosure_mono fun x hx => ⟨hSsub hx, subset_zclosure _ hx⟩
  obtain ⟨C, hC⟩ := exists_siComponent_of_dense τ d N₀ hVcl hVp hdense
  refine ⟨C, by rw [hC, hVvi], fun y hy hqy => ?_⟩
  have hmem : siProj i y ∈ V := subset_zclosure _ ⟨y, ⟨hy, hqy⟩, rfl⟩
  rw [hC]
  show siProj i y ∈ zclosure V
  rw [hVcl]
  exact hmem

end Height.Chain
