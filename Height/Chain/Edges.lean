import Height.Chain.Counts
import Height.Chain.StrataDim
import Height.Chain.Untwist
import Height.Chain.Frame
import Height.Chain.H1Geometry
import Height.Chain.H2
import Height.Chain.H2Geometry
import Height.Toolbox.KrullArith

/-!
# The proof chain, top down

Each theorem here is one node of the paper's proof, read top down; each is
proved from the next.  Two nodes live beside their proofs instead:
`Height.Chain.nilcone_kkIsotropic` (`(∗)`, `thm:star`, `Chain/Star.lean`) and
`Height.Chain.pencilIncidenceBound` ((H1), `thm:h1`, `Chain/H1Geometry.lean`).

```
thm:main (regular)        Chain/Main.lean, regular_of_boxes
thm:main (height)         steenrodHeight_of_dimFormula
rem:krull                 steenrod_ringKrullDim_le
cor:flagless              affineDim_flaglessPartners_le
thm:h1                    pencilIncidenceBound        (Chain/H1Geometry.lean)
thm:h2-conditional        markedIncidenceBound
defn:si                   shiftedIsotropy
thm:star                  nilcone_kkIsotropic         (Chain/Star.lean)
```
-/

namespace Height.Chain

open Height.Pencil
open QSteenrod Height.Steenrod
open Height.Geometry (affineDim matCoords SIIndex siCoords)
open Height.Toolbox (cOf)

/-! ### `defn:si`: shifted isotropy from `(∗)` -/

section SI

variable {K : Type} [Field K] [IsAlgClosed K] [Infinite K] {n : ℕ}

/-- **`thm:reduction`, the node (SI)**: a closed subscheme `V(I)` of the
single-point marked incidence is shifted isotropic.

The frame (`nonempty_geometricFrame`) gives the map `ψ`
(`GeometricFrame.toAlgebraic`, `AlgebraicFrame.toAdapted`,
`AdaptedFrame.toPsiMap`), kernel flatness along arcs is `siLocalFlat`, and the
reduction itself is `siPairing_eq_zero_of_psiMap`, which consumes `(∗)`
through `star_kk_vanishing`.  The two arc bridges of the geometry API
(`exists_siLocus_iff`, `siArcEquiv`) convert the hypothesis and the conclusion. -/
theorem shiftedIsotropy (τ : Nat.Partition n) (d : ℕ → ℕ)
    (N₀ : Matrix (Fin n) (Fin n) K) (I : Ideal (MvPolynomial (SIIndex (Fin n)) K))
    [I.IsPrime]
    (hloc : Height.Geometry.GenericPts I
      (fun z => siCoords.symm z ∈ singleMarkedLocus τ d N₀)) :
    ShiftedIsotropy I := by
  obtain ⟨g, hlocus⟩ := (exists_siLocus_iff τ d N₀ I).1 hloc
  set C : SIComponent τ d N₀ := ⟨I, g, hlocus⟩ with hC
  obtain ⟨F⟩ := nonempty_geometricFrame C
  obtain ⟨h, hh, hmain⟩ := siPairing_eq_zero_of_psiMap C
    (AdaptedFrame.toPsiMap C.locus.prime
      (AlgebraicFrame.toAdapted C.locus.prime (GeometricFrame.toAlgebraic C.locus.prime F)))
  rw [ShiftedIsotropy, Height.Geometry.genericPts_iff]
  refine ⟨C.g * h, hlocus.mul_notMem hh, fun z hz hne a₁ a₂ hb₁ hb₂ Z₁ Z₂ hm₁ hm₂ => ?_⟩
  rw [MvPolynomial.aeval_eq_eval, map_mul, mul_ne_zero_iff] at hne
  -- the two API arcs as marked arcs of the incidence
  have hbase : ∀ (a : Height.Geometry.Arc I), a.base = z →
      (siArcEquiv I a : SIArc n K).base = siCoords.symm z :=
    fun a ha => by rw [base_siArcEquiv, ha]
  have hvel : ∀ a : Height.Geometry.Arc I,
      (siArcEquiv I a : SIArc n K).vel = siCoords.symm a.vel :=
    fun a => vel_siArcEquiv a
  set m₁ : MarkedArc C.I z :=
    ⟨⟨siArcEquiv I a₁, (siArcEquiv I a₁).2, hbase a₁ hb₁⟩, Z₁, by rw [hvel a₁]; exact hm₁⟩
  set m₂ : MarkedArc C.I z :=
    ⟨⟨siArcEquiv I a₂, (siArcEquiv I a₂).2, hbase a₂ hb₂⟩, Z₂, by rw [hvel a₂]; exact hm₂⟩
  have hflat : ∀ m : MarkedArc C.I z,
      Isotropy.DCond (Pat (siCoords.symm z).1 (siCoords.symm z).2.1 (siCoords.symm z).2.2)
        (Qat (pencil m.a.vel.1 m.a.vel.2.1) (siCoords.symm z).2.2) :=
    fun m => siLocalFlat τ d N₀ C z hz hne.1 m.toArcAt
  have := hmain z hz hne.2 m₁ m₂ (hflat m₁) (hflat m₂)
  rwa [show m₁.a.vel = siCoords.symm a₁.vel from hvel a₁,
    show m₂.a.vel = siCoords.symm a₂.vel from hvel a₂] at this

/-- **`thm:h2-conditional`, the node (H2′)**: shifted isotropy of the two
single-point incidences gives the bound on the marked incidence. -/
theorem markedIncidenceBound (τ : Nat.Partition n) (d : ℕ → ℕ)
    (N₀ : Matrix (Fin n) (Fin n) K) (hd : d ≠ 0) (hnil : IsNilpotent N₀)
    (hdeg : IsDegeneration τ N₀) (hc : cType τ < cOf N₀) :
    MarkedIncidenceBound τ d N₀ := by
  rcases Set.eq_empty_or_nonempty (markedLocus (K := K) τ d N₀) with hemp | hne
  · show affineDim (Height.Geometry.markedCoords '' markedLocus (K := K) τ d N₀) + _ ≤ _
    rw [hemp, Set.image_empty, (Height.Geometry.affineDim_eq_bot_iff _).2 rfl, WithBot.bot_add]
    exact bot_le
  obtain ⟨C₁, C₂, hmain⟩ := exists_siComponents_realizedBounds τ d N₀ hd hnil hdeg hc
    hne
  have hp₁ := C₁.locus.prime
  have hp₂ := C₂.locus.prime
  obtain ⟨h₁, hh₁, hv₁⟩ := exists_siVanishing
    (shiftedIsotropy τ d N₀ C₁.I ((exists_siLocus_iff τ d N₀ C₁.I).2 ⟨C₁.g, C₁.locus⟩))
  obtain ⟨h₂, hh₂, hv₂⟩ := exists_siVanishing
    (shiftedIsotropy τ d N₀ C₂.I ((exists_siLocus_iff τ d N₀ C₂.I).2 ⟨C₂.g, C₂.locus⟩))
  obtain ⟨R, hR⟩ := hmain h₁ hh₁ h₂ hh₂ hv₁ hv₂
  exact markedIncidenceBound_of_bounds R hR

end SI

/-! ### `cor:flagless`, `rem:krull` and the height theorem -/

section Chain

variable (p r n : ℕ) [Fact p.Prime]

/-- `C(n,2) + C(n+1,2) = n²`. -/
theorem choose_two_add_choose_two_succ (n : ℕ) :
    n.choose 2 + (n + 1).choose 2 = n * n := by
  induction n with
  | zero => simp
  | succ m ih =>
      have h1 : (m + 1).choose 2 = m + m.choose 2 := by
        rw [Nat.choose_succ_succ, Nat.choose_one_right]
      have h2 : (m + 1 + 1).choose 2 = (m + 1) + (m + 1).choose 2 := by
        rw [Nat.choose_succ_succ, Nat.choose_one_right]
      rw [h1] at ih
      rw [h2, h1]
      nlinarith [ih]

/-- **`cor:flagless`, the node**: for every rational nilpotent `N` the flagless
partners of `N` lying in the orbit of `N` form a set of dimension at most
`n(n-1)/2`.  This is `thm:conditional-height`
(`affineDim_flaglessPartners_le_of_bounds`) fed with (H1) and (H2′). -/
theorem affineDim_flaglessPartners_le (N : Matrix (Fin n) (Fin n) (GaloisField p r))
    (hN : IsNilpotent N) :
    affineDim (matCoords ''
        (flaglessPartnerLocus n (ext p r n N) ∩ conjOrbit (ext p r n N)))
      ≤ ((n.choose 2 : ℕ) : WithBot ℕ∞) := by
  exact affineDim_flaglessPartners_le_of_bounds
    (fun τ d hd => pencilIncidenceBound τ d hd)
    (fun τ d N₀ hd hnil hdeg hc => markedIncidenceBound τ d N₀ hd hnil hdeg hc)
    (ext p r n N) (isNilpotent_ext p r n hN)

/-- **`rem:krull`, the node**: the coordinate ring of `V(J)` has Krull dimension
at most `n(n-1)/2`.  `V(J)` is covered by its intersections with the finitely
many nilpotent orbits (`ringKrullDim_quotient_steenrodIdeal_le`); on each,
`prop:untwist` (`untwist`) replaces the Steenrod locus by the partner variety,
which splits into its triangularizable and flagless parts, bounded by
`prop:springer-bound` (`springer`) and `cor:flagless`. -/
theorem steenrod_ringKrullDim_le [NeZero r] :
    ringKrullDim (GenericMatrixRing p r n ⧸ steenrodIdeal p r n)
      ≤ ((n.choose 2 : ℕ) : WithBot ℕ∞) := by
  refine ringKrullDim_quotient_steenrodIdeal_le p r n _ fun N hN => ?_
  rw [untwist p r n N hN]
  exact affineDim_nilpotentPartner_le p r n _ (springer p r n N hN)
    (affineDim_flaglessPartners_le p r n N hN)

/-- **`thm:main` in height form**: the Steenrod ideal has height `C(n+1,2)`.

`bb8` is the dimension formula `height J + dim (R/J) = n²` in the polynomial
ring; both terms are finite because the sum is a natural number
(`Toolbox.exists_eq_natCast_of_add_eq_natCast`), `rem:krull` bounds the second
by `C(n,2)`, `steenrodIdeal_height_le` bounds the first by `C(n+1,2)`, and
`C(n,2) + C(n+1,2) = n²` forces both to be exact. -/
theorem steenrodHeight_of_dimFormula [NeZero r]
    (bb8 : ((steenrodIdeal p r n).height : WithBot ℕ∞) +
        ringKrullDim (GenericMatrixRing p r n ⧸ steenrodIdeal p r n)
      = ((n * n : ℕ) : WithBot ℕ∞)) :
    SteenrodHeightStatement p r n := by
  obtain ⟨h, d, hh, hdim, hsum⟩ := Toolbox.exists_eq_natCast_of_add_eq_natCast bb8
  have hle : (steenrodIdeal p r n).height ≤ ((n + 1).choose 2 : ℕ∞) :=
    steenrodIdeal_height_le p r n
  have hh' : (steenrodIdeal p r n).height = (h : ℕ∞) := by exact_mod_cast hh
  rw [hh'] at hle
  have hle' : h ≤ (n + 1).choose 2 := by exact_mod_cast hle
  have hd' : d ≤ n.choose 2 := by
    have := steenrod_ringKrullDim_le p r n
    rw [hdim] at this
    exact_mod_cast this
  have hsq := choose_two_add_choose_two_succ n
  show (steenrodIdeal p r n).height = ((n + 1).choose 2 : ℕ∞)
  rw [hh', show h = (n + 1).choose 2 by omega]

end Chain

end Height.Chain
