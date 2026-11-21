import Height.Chain.Statements
import Height.Geometry.Dimension.Affine
import Height.Chain.Descent
import Height.Toolbox.JordanBasis

/-!
# The counting layer below `rem:krull`

`V(J)` is the union, over the finitely many nilpotent `F_q`-matrices `N`, of
its intersections with the orbits `O_N` — the rationality of the Jordan form
(`rationalJordan`) — so a uniform bound on the pieces bounds the Krull
dimension of the coordinate ring
(`ringKrullDim_quotient_steenrodIdeal_le`).  The two bounds on a piece are
`prop:untwist` (`Height.Chain.untwist`, `Chain/Untwist.lean`) and the split of
the partner locus into its triangularizable and flagless parts, whose bounds
are `prop:springer-bound` and `cor:flagless`; the composition is
`steenrod_ringKrullDim_le` in `Chain/Edges.lean`.
-/

namespace Height.Chain

open QSteenrod Height.Steenrod
open Height.Geometry (affineDim matCoords affineDim_union affineDim_mono vanishingIdeal_iUnion
  ringKrullDim_quotient_radical ringKrullDim_quotient_iInf_le)

variable (p r n : ℕ) [Fact p.Prime]

/-- A rational nilpotent, extended to `Kbar`. -/
noncomputable abbrev ext (N : Matrix (Fin n) (Fin n) (GaloisField p r)) :
    Matrix (Fin n) (Fin n) (Kbar p r) :=
  N.map (algebraMap (GaloisField p r) (Kbar p r))

/-- `V(J)` over `Kbar`, as a set of matrices. -/
noncomputable def Vlocus : Set (Matrix (Fin n) (Fin n) (Kbar p r)) :=
  steenrodMatrixZeroLocus p r n (K := Kbar p r)

/-- **The rationality of the Jordan form**: over `Kbar` every nilpotent matrix is
conjugate to one with entries in `F_q`.  Mathlib has no Jordan normal form, and
`Height/Toolbox/Jordan.lean` supplies only the partition (kernel dimensions), not
the conjugacy; it is proved in `Toolbox/JordanBasis.lean` from the PID structure
theorem. -/
theorem rationalJordan :
    ∀ M : Matrix (Fin n) (Fin n) (Kbar p r), IsNilpotent M →
      ∃ N : Matrix (Fin n) (Fin n) (GaloisField p r), IsNilpotent N ∧ M ∈ conjOrbit (ext p r n N) := by
  intro M hM
  obtain ⟨N, hN, g, hg⟩ :=
    Toolbox.JordanBasis.exists_conj_rational (k := GaloisField p r) (L := Kbar p r) M hM
  exact ⟨N, hN, g, hg⟩

/-- **`cor:qfree`**: `V(J)` is the union over the (finitely many, `F_q` being
finite) nilpotent `F_q`-matrices `N` of `V(J) ∩ O_N`, so a bound `c` valid on
every piece bounds the Krull dimension of the coordinate ring of `V(J)`.

The ideal of a union is the infimum of the ideals (`vanishingIdeal_iUnion`),
`ringKrullDim_quotient_iInf_le` turns that infimum into a maximum, and
`ringKrullDim_quotient_vanishingIdeal_eq` (`Chain/Descent.lean`) matches the
`F_q`-coordinate ring of a piece against its dimension over `Kbar`. -/
theorem ringKrullDim_quotient_steenrodIdeal_le (c : WithBot ℕ∞)
    (h : ∀ N : Matrix (Fin n) (Fin n) (GaloisField p r), IsNilpotent N →
      affineDim (matCoords '' (Vlocus p r n ∩ conjOrbit (ext p r n N))) ≤ c) :
    ringKrullDim (GenericMatrixRing p r n ⧸ steenrodIdeal p r n) ≤ c := by
  classical
  -- The finite index set: nilpotent matrices over the finite field `F_q`.
  have hfin : Finite {N : Matrix (Fin n) (Fin n) (GaloisField p r) // IsNilpotent N} := Subtype.finite
  set piece : {N : Matrix (Fin n) (Fin n) (GaloisField p r) // IsNilpotent N} →
      Set (Matrix (Fin n) (Fin n) (Kbar p r)) :=
    fun N => Vlocus p r n ∩ conjOrbit (ext p r n N.1) with hpiece
  have hcover : steenrodMatrixZeroLocus p r n (K := Kbar p r) = ⋃ N, piece N := by
    refine Set.Subset.antisymm (fun M hM => ?_) (Set.iUnion_subset fun _ => Set.inter_subset_left)
    obtain ⟨N, hN, hMN⟩ :=
      rationalJordan p r n M (isNilpotent_of_mem_steenrodMatrixZeroLocus p r n hM)
    exact Set.mem_iUnion.mpr ⟨⟨N, hN⟩, hM, hMN⟩
  have hrad : (steenrodIdeal p r n).radical =
      ⨅ N, MvPolynomial.vanishingIdeal (GaloisField p r) (matCoords '' piece N) := by
    rw [← vanishingIdeal_steenrodMatrixZeroLocus_eq_radical p r n (K := Kbar p r), hcover,
      Set.image_iUnion, vanishingIdeal_iUnion]
  rw [← ringKrullDim_quotient_radical, hrad]
  refine ringKrullDim_quotient_iInf_le _ fun N => ?_
  rw [ringKrullDim_quotient_vanishingIdeal_eq (k := GaloisField p r) (L := Kbar p r)
    (σ := Fin n × Fin n) (matCoords '' piece N)]
  exact h N.1 N.2

/-- The partner locus inside an orbit splits into its triangularizable and its
flagless part (`Height.Steenrod.nilpotentPartnerLocus_eq_union`), so a bound on
both bounds the whole (`affineDim_union`). -/
theorem affineDim_nilpotentPartner_le {c : WithBot ℕ∞}
    (N : Matrix (Fin n) (Fin n) (Kbar p r))
    (hs : affineDim (matCoords '' (triangularizablePartnerLocus n N ∩ conjOrbit N)) ≤ c)
    (hf : affineDim (matCoords '' (flaglessPartnerLocus n N ∩ conjOrbit N)) ≤ c) :
    affineDim (matCoords '' (nilpotentPartnerLocus n N ∩ conjOrbit N)) ≤ c := by
  have hsplit : nilpotentPartnerLocus n N ∩ conjOrbit N =
      (triangularizablePartnerLocus n N ∩ conjOrbit N) ∪
        (flaglessPartnerLocus n N ∩ conjOrbit N) := by
    rw [nilpotentPartnerLocus_eq_union, Set.union_inter_distrib_right]
  rw [hsplit, Set.image_union, affineDim_union]
  exact max_le hs hf

end Height.Chain
