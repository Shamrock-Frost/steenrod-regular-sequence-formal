import Height.Geometry.Dimension.Homogeneous

/-!
# Locally closed sources for the homogeneous fibrations

The dimension counts of `Geometry/Dimension/Homogeneous.lean`
(`affineDim_le_add_fibre`, `affineDim_of_finite_fibres`)
require the source `Y` to be Zariski closed, while every consumer has a
source that is only *locally* closed: `GL_n = {det ≠ 0}`, orbits, the Lang
transporter, `pencilLocus`, `markedLocus`.  This file removes that hypothesis.

`IsLocClosed Y` is

```
∃ Z g, zclosure Z = Z ∧ Y = Z ∩ {y | aeval y g ≠ 0}
```

and the main theorems are

```
affineDim_of_finite_fibres_locClosed
affineDim_of_finite_fibres_constructible
affineDim_of_orbit_fibration_constructible
affineDim_of_transitive_fibration_constructible
```

These are the finite-fibre count for a locally closed and for a constructible
source, and the orbit and transitive fibration counts for a constructible source.

## The two devices

The algebraic route would be the localised coordinate ring `(R ⧸ I(Z))[1/g]`.
What is proved here is the same mathematics with the localisation realised
*geometrically*, which lets the fibre-dimension upper bound and the generic
fibre bound be reused verbatim instead of being redone for localisations.

* **The graph** (`graphSet`).  `Ỹ := {(y, s) | y ∈ Z, s · g(y) = 1}` inside the
  affine space on `ι ⊕ Unit` is Zariski closed (`zclosure_graphSet`) and the
  projection `projSum` maps it *bijectively* onto `Y` (`projSum_image_graphSet`,
  `graphSet_fibre_subsingleton`).  So `affineDim Ỹ = affineDim Y` and, for a
  polynomial `f`, `affineDim (Ỹ ∩ (f ∘ projSum)⁻¹ x) = affineDim (Y ∩ f⁻¹ x)`,
  both by the closed form `affineDim_of_finite_fibres`.  Feeding `Ỹ` to
  `affineDim_le_add_fibre` gives the fibre-dimension upper bound for locally closed
  sources (`affineDim_le_add_fibre_locClosed_le`, and its supremum form
  `affineDim_le_add_fibre_locClosed`).  This is the standard
  identification of `Spec (R ⧸ I(Z))[1/g]` with the closed subscheme
  `V(I(Z), s·g - 1)` of `A^ι × A^1`.
* **Density** (`vanishingIdeal_inter_dense`).  If `C` is irreducible and meets
  `D(g)` then `I(C ∩ D(g)) = I(C)`: a `q` vanishing on `C ∩ D(g)` has `q·g`
  vanishing on `C`, and `g ∉ I(C)`.  Hence the traces `C i ∩ Y` of the
  components of `zclosure Y` are irreducible, dense in `C i`, `G`-stable
  (`locClosed_components`), and the generic fibre bound can be run on `C i` while
  the *generic point* is chosen inside the trace (`exists_generic_fibre_dense`),
  which is what the lower bounds need.

Only the `≥`-half of the generic fibre bound is used, so the fibres of the
traces never have to be computed: they merely have to *contain* an orbit, which
stability gives.
-/

universe u v

open MvPolynomial

namespace Height.Geometry

variable {K : Type u} [Field K] {γ ι κ : Type v}

/-! ### Locally closed subsets of affine space -/

/-- A locally closed subset of affine space: a Zariski closed set with a
hypersurface removed. -/
def IsLocClosed (Y : Set (ι → K)) : Prop :=
  ∃ (Z : Set (ι → K)) (g : MvPolynomial ι K),
    zclosure Z = Z ∧ Y = Z ∩ {y | aeval y g ≠ 0}

/-- A Zariski closed set is locally closed. -/
theorem IsLocClosed.of_zclosure {Y : Set (ι → K)} (h : zclosure Y = Y) : IsLocClosed Y :=
  ⟨Y, 1, h, by ext y; simp⟩

/-- The intersection of two locally closed sets is locally closed. -/
theorem IsLocClosed.inter {Y Y' : Set (ι → K)} (hY : IsLocClosed Y) (hY' : IsLocClosed Y') :
    IsLocClosed (Y ∩ Y') := by
  obtain ⟨Z, g, hZ, rfl⟩ := hY
  obtain ⟨Z', g', hZ', rfl⟩ := hY'
  refine ⟨Z ∩ Z', g * g', zclosure_inter hZ hZ', ?_⟩
  ext y
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, map_mul, ne_eq, mul_eq_zero, not_or]
  tauto

/-! ### The graph of a locally closed set -/

/-- The projection `(ι ⊕ Unit → K) → (ι → K)`. -/
def projSum (z : ι ⊕ Unit → K) : ι → K := fun i => z (Sum.inl i)

theorem isPolyMap_projSum : IsPolyMap (projSum (K := K) (ι := ι)) :=
  ⟨fun i => X (Sum.inl i), fun z i => by simp [projSum]⟩

/-- The graph of `Z ∩ D(g)` in one extra variable inverting `g`. -/
def graphSet (Z : Set (ι → K)) (g : MvPolynomial ι K) : Set (ι ⊕ Unit → K) :=
  {z | projSum z ∈ Z ∧ z (Sum.inr ()) * aeval (projSum z) g = 1}

/-- The canonical lift of a point of `Z ∩ D(g)` to the graph. -/
theorem graphSet_lift {Z : Set (ι → K)} {g : MvPolynomial ι K} {y : ι → K}
    (hy : y ∈ Z ∩ {y | aeval y g ≠ 0}) :
    Sum.elim y (fun _ : Unit => (aeval y g)⁻¹) ∈ graphSet Z g ∧
      projSum (Sum.elim y (fun _ : Unit => (aeval y g)⁻¹)) = y := by
  have hproj : projSum (Sum.elim y (fun _ : Unit => (aeval y g)⁻¹)) = y := rfl
  refine ⟨⟨?_, ?_⟩, hproj⟩
  · rw [hproj]; exact hy.1
  · rw [hproj]
    show (aeval y g)⁻¹ * aeval y g = 1
    exact inv_mul_cancel₀ hy.2

theorem projSum_image_graphSet (Z : Set (ι → K)) (g : MvPolynomial ι K) :
    projSum '' graphSet Z g = Z ∩ {y | aeval y g ≠ 0} := by
  ext y
  constructor
  · rintro ⟨z, ⟨hzZ, hzs⟩, rfl⟩
    refine ⟨hzZ, fun h => ?_⟩
    rw [h, mul_zero] at hzs
    exact zero_ne_one hzs
  · intro hy
    obtain ⟨hmem, hproj⟩ := graphSet_lift hy
    exact ⟨_, hmem, hproj⟩

/-- The projection is injective on the graph. -/
theorem graphSet_fibre_subsingleton (Z : Set (ι → K)) (g : MvPolynomial ι K) (y : ι → K) :
    (graphSet Z g ∩ projSum ⁻¹' {y}).Subsingleton := by
  rintro z ⟨⟨-, hz⟩, hzy⟩ w ⟨⟨-, hw⟩, hwy⟩
  have hpz : projSum z = y := hzy
  have hpw : projSum w = y := hwy
  rw [hpz] at hz
  rw [hpw] at hw
  have hg : aeval y g ≠ 0 := by
    intro h
    rw [h, mul_zero] at hz
    exact zero_ne_one hz
  refine _root_.funext fun v => ?_
  cases v with
  | inl i =>
      show z (Sum.inl i) = w (Sum.inl i)
      have h1 : projSum z i = projSum w i := by rw [hpz, hpw]
      exact h1
  | inr u =>
      cases u
      exact mul_right_cancel₀ hg (hz.trans hw.symm)

/-- The graph of a locally closed set is Zariski closed. -/
theorem zclosure_graphSet {Z : Set (ι → K)} (hZ : zclosure Z = Z) (g : MvPolynomial ι K) :
    zclosure (graphSet Z g) = graphSet Z g := by
  obtain ⟨F, hF⟩ := isPolyMap_projSum (K := K) (ι := ι)
  refine le_antisymm (fun z hz => ?_) (subset_zclosure _)
  constructor
  · rw [← hZ]
    intro q hq
    have hmem : aeval F q ∈ MvPolynomial.vanishingIdeal K (graphSet Z g) := by
      intro w hw
      rw [← aeval_polyMap hF]
      exact hq _ hw.1
    have h := hz _ hmem
    rwa [← aeval_polyMap hF] at h
  · have hmem : (X (Sum.inr ()) * aeval F g - 1 : MvPolynomial (ι ⊕ Unit) K) ∈
        MvPolynomial.vanishingIdeal K (graphSet Z g) := by
      intro w hw
      rw [map_sub, map_mul, map_one, aeval_X, ← aeval_polyMap hF, hw.2, sub_self]
    have h := hz _ hmem
    rw [map_sub, map_mul, map_one, aeval_X, ← aeval_polyMap hF] at h
    exact sub_eq_zero.1 h

/-! ### Constructible sets

The loci of `Chain/Incidence.lean` are cut out by rank *equalities*, hence by a
closed condition together with a *union* of basic opens ("some minor is
nonzero"), so they are finite unions of locally closed sets rather than locally
closed.  The dimension counts hold in that generality, by a route that is
in fact simpler than the one used for a single locally closed source:

* `constructible_pieces`: a constructible set is a finite union of *irreducible*
  subsets `W a` of itself.  These come from the graph again — the components of
  the closed set `graphSet Z g` already lie inside it, so their projections lie
  inside `Z ∩ D(g)` and are irreducible by `irreducible_image`.  Density is then
  free: `W a` is dense in `zclosure (W a)` by construction, and no structure
  theorem for constructible sets is needed.
* Instead of asking the pieces to be `G`-stable, the proofs *sweep* the chosen
  piece: `S := A.sweep (W a)` is still irreducible (`irreducible_sweep`), lies
  in `Y`, is `G`-stable, contains `W a`, and is dense in `C := zclosure S`.  The
  generic fibre bound runs on `C` with generic point in `S`.
-/

/-- A constructible subset of affine space: a finite union of locally closed
sets. -/
def IsAffineConstructible (Y : Set (ι → K)) : Prop :=
  ∃ (J : Type) (_ : Finite J) (P : J → Set (ι → K)),
    (∀ j, IsLocClosed (P j)) ∧ Y = ⋃ j, P j

theorem IsLocClosed.isConstructible {Y : Set (ι → K)} (h : IsLocClosed Y) :
    IsAffineConstructible Y :=
  ⟨Unit, inferInstance, fun _ => Y, fun _ => h, (Set.iUnion_const Y).symm⟩

/-- A finite union of constructible sets is constructible. -/
theorem IsAffineConstructible.iUnion {J : Type} [Finite J] {P : J → Set (ι → K)}
    (h : ∀ j, IsAffineConstructible (P j)) : IsAffineConstructible (⋃ j, P j) := by
  choose I hI Q hQlc hQcov using h
  have _ : ∀ j, Finite (I j) := hI
  refine ⟨Σ j : J, I j, inferInstance, fun a => Q a.1 a.2, fun a => hQlc a.1 a.2, ?_⟩
  refine le_antisymm (fun y hy => ?_) (fun y hy => ?_)
  · obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hy
    rw [hQcov j] at hj
    obtain ⟨b, hb⟩ := Set.mem_iUnion.1 hj
    exact Set.mem_iUnion.2 ⟨⟨j, b⟩, hb⟩
  · obtain ⟨⟨j, b⟩, hb⟩ := Set.mem_iUnion.1 hy
    refine Set.mem_iUnion.2 ⟨j, ?_⟩
    rw [hQcov j]
    exact Set.mem_iUnion.2 ⟨b, hb⟩

/-- The union of two constructible sets is constructible. -/
theorem IsAffineConstructible.union {Y Y' : Set (ι → K)} (h : IsAffineConstructible Y)
    (h' : IsAffineConstructible Y') : IsAffineConstructible (Y ∪ Y') := by
  have hcov : Y ∪ Y' = ⋃ b : Bool, cond b Y Y' := by
    ext y
    simp only [Set.mem_union, Set.mem_iUnion, Bool.exists_bool, Bool.cond_false, Bool.cond_true]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  rw [hcov]
  exact IsAffineConstructible.iUnion fun b => by cases b; exacts [h', h]

theorem IsAffineConstructible.empty : IsAffineConstructible (∅ : Set (ι → K)) :=
  ⟨Empty, inferInstance, fun j => j.elim, fun j => j.elim, by simp⟩

/-! ### Finite intersections of locally closed and constructible sets -/

/-- A finite intersection of locally closed sets is locally closed: intersect the
closed parts, multiply the inequations. -/
theorem IsLocClosed.iInter {J : Type} [Fintype J] {P : J → Set (ι → K)}
    (h : ∀ j, IsLocClosed (P j)) : IsLocClosed (⋂ j, P j) := by
  classical
  choose Z g hZ hP using h
  refine ⟨⋂ j, Z j, ∏ j, g j, ?_, ?_⟩
  · refine Set.Subset.antisymm (fun x hx => Set.mem_iInter.2 fun j => ?_) (subset_zclosure _)
    have hsub : zclosure (⋂ j, Z j) ⊆ zclosure (Z j) := zclosure_mono (Set.iInter_subset _ j)
    rw [hZ j] at hsub
    exact hsub hx
  · refine Set.Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
    · have hx1 : ∀ j, x ∈ P j := Set.mem_iInter.1 hx
      refine ⟨Set.mem_iInter.2 fun j => ?_, ?_⟩
      · have hj := hx1 j
        rw [hP j] at hj
        exact hj.1
      · show MvPolynomial.aeval x (∏ j, g j) ≠ 0
        rw [map_prod]
        refine Finset.prod_ne_zero_iff.2 fun j _ => ?_
        have hj := hx1 j
        rw [hP j] at hj
        exact hj.2
    · refine Set.mem_iInter.2 fun j => ?_
      rw [hP j]
      have h2 : MvPolynomial.aeval x (∏ j, g j) ≠ 0 := hx.2
      rw [map_prod] at h2
      exact ⟨Set.mem_iInter.1 hx.1 j, Finset.prod_ne_zero_iff.1 h2 j (Finset.mem_univ j)⟩

/-- An intersection of two constructible sets is constructible. -/
theorem IsAffineConstructible.inter {Y Y' : Set (ι → K)} (hY : IsAffineConstructible Y)
    (hY' : IsAffineConstructible Y') : IsAffineConstructible (Y ∩ Y') := by
  obtain ⟨I, hI, P, hPlc, rfl⟩ := hY
  obtain ⟨I', hI', P', hPlc', rfl⟩ := hY'
  have _ : Finite I := hI
  have _ : Finite I' := hI'
  refine ⟨I × I', inferInstance, fun a => P a.1 ∩ P' a.2,
    fun a => (hPlc a.1).inter (hPlc' a.2), ?_⟩
  ext x
  simp only [Set.mem_inter_iff, Set.mem_iUnion]
  constructor
  · rintro ⟨⟨i, hi⟩, ⟨i', hi'⟩⟩
    exact ⟨(i, i'), hi, hi'⟩
  · rintro ⟨a, ha, ha'⟩
    exact ⟨⟨a.1, ha⟩, ⟨a.2, ha'⟩⟩

/-- A finite intersection of constructible sets is constructible: distribute the
unions over the intersection. -/
theorem IsAffineConstructible.iInter {J : Type} [Fintype J] {P : J → Set (ι → K)}
    (h : ∀ j, IsAffineConstructible (P j)) : IsAffineConstructible (⋂ j, P j) := by
  classical
  choose I hI Q hQlc hQcov using h
  have _ : ∀ j, Finite (I j) := hI
  refine ⟨(j : J) → I j, inferInstance, fun c => ⋂ j, Q j (c j),
    fun c => IsLocClosed.iInter fun j => hQlc j (c j), ?_⟩
  ext x
  simp only [Set.mem_iInter, Set.mem_iUnion]
  constructor
  · intro hx
    have hx' : ∀ j, ∃ i, x ∈ Q j i := by
      intro j
      have hj := hx j
      rw [hQcov j] at hj
      exact Set.mem_iUnion.1 hj
    choose c hc using hx'
    exact ⟨c, hc⟩
  · rintro ⟨c, hc⟩ j
    rw [hQcov j]
    exact Set.mem_iUnion.2 ⟨c j, hc j⟩

/-! ### Preimages under polynomial maps -/

/-- A locally closed set pulls back to a locally closed set along a polynomial
map. -/
theorem IsLocClosed.preimage {F : (κ → K) → (ι → K)} (hF : IsPolyMap F)
    {Y : Set (ι → K)} (hY : IsLocClosed Y) : IsLocClosed (F ⁻¹' Y) := by
  classical
  obtain ⟨Q, hQ⟩ := hF
  obtain ⟨Z, g, hZ, rfl⟩ := hY
  have hsub : ∀ (y : κ → K) (f : MvPolynomial ι K),
      MvPolynomial.aeval (F y) f = MvPolynomial.aeval y (MvPolynomial.aeval Q f) := by
    intro y f
    rw [aeval_aeval, funext (hQ y)]
  refine ⟨F ⁻¹' Z, MvPolynomial.aeval Q g, ?_, ?_⟩
  · have hzeros : F ⁻¹' Z
        = {y : κ → K | ∀ q ∈ (Set.range fun f : MvPolynomial.vanishingIdeal K Z =>
              MvPolynomial.aeval Q (f : MvPolynomial ι K)), MvPolynomial.aeval y q = 0} := by
      refine Set.Subset.antisymm (fun y hy => ?_) (fun y hy => ?_)
      · rintro _ ⟨f, rfl⟩
        rw [← hsub]
        exact subset_zclosure Z hy _ f.2
      · have h1 : F y ∈ zclosure Z := fun f hf => by
          rw [hsub]
          exact hy _ ⟨⟨f, hf⟩, rfl⟩
        rwa [hZ] at h1
    rw [hzeros]
    exact zclosure_zeros _
  · ext y
    simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq, hsub y g]

/-- A constructible set pulls back to a constructible set along a polynomial
map. -/
theorem IsAffineConstructible.preimage {F : (κ → K) → (ι → K)} (hF : IsPolyMap F)
    {Y : Set (ι → K)} (hY : IsAffineConstructible Y) : IsAffineConstructible (F ⁻¹' Y) := by
  obtain ⟨J, hJ, P, hPlc, rfl⟩ := hY
  exact ⟨J, hJ, fun j => F ⁻¹' P j, fun j => IsLocClosed.preimage hF (hPlc j),
    by rw [Set.preimage_iUnion]⟩

variable [IsAlgClosed K] [Finite ι] [Finite κ]

omit [IsAlgClosed K] [Finite ι] in
/-- The sweep of a set contains the orbit of each of its points. -/
theorem PolyAction.orbit_subset_sweep (A : PolyAction K γ ι) {C : Set (ι → K)} (hC : C ⊆ A.S)
    {z : ι → K} (hz : z ∈ A.sweep C) : A.orbit z ⊆ A.sweep C := by
  obtain ⟨g, hg, w, hw, rfl⟩ := hz
  rintro _ ⟨h, hh, rfl⟩
  exact ⟨A.mul h g, A.mul_mem h hh g hg, w, hw, A.act_mul h hh g hg w (hC hw)⟩

/-- A locally closed set is the union of finitely many irreducible subsets of
itself: the projections of the components of its graph. -/
theorem locClosed_pieces {Y : Set (ι → K)} (hY : IsLocClosed Y) :
    ∃ (m : ℕ) (W : Fin m → Set (ι → K)),
      (∀ a, W a ⊆ Y) ∧ Y = ⋃ a, W a ∧
      (∀ a, (MvPolynomial.vanishingIdeal K (W a)).IsPrime) := by
  obtain ⟨Z, g, hZ, rfl⟩ := hY
  obtain ⟨m, C, hCprime, -, -, hcover, -, -⟩ := components (K := K) (graphSet Z g)
  rw [zclosure_graphSet hZ g] at hcover
  refine ⟨m, fun a => projSum '' C a, fun a => ?_, ?_, fun a => ?_⟩
  · rw [← projSum_image_graphSet Z g]
    exact Set.image_mono (hcover ▸ Set.subset_iUnion C a)
  · rw [← projSum_image_graphSet Z g]
    conv_lhs => rw [hcover]
    rw [Set.image_iUnion]
  · exact irreducible_image isPolyMap_projSum (hCprime a)

/-- **The irreducible pieces of a constructible set.** -/
theorem constructible_pieces {Y : Set (ι → K)} (hY : IsAffineConstructible Y) :
    ∃ (J : Type) (_ : Finite J) (W : J → Set (ι → K)),
      (∀ a, W a ⊆ Y) ∧ Y = ⋃ a, W a ∧
      (∀ a, (MvPolynomial.vanishingIdeal K (W a)).IsPrime) := by
  obtain ⟨I, hI, P, hPlc, rfl⟩ := hY
  have _ : Finite I := hI
  choose m W hWsub hWcov hWp using fun i => locClosed_pieces (hPlc i)
  refine ⟨Σ i : I, Fin (m i), inferInstance, fun a => W a.1 a.2, fun a => ?_, ?_, fun a => ?_⟩
  · exact (hWsub a.1 a.2).trans (Set.subset_iUnion P a.1)
  · refine le_antisymm (fun y hy => ?_) (fun y hy => ?_)
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy
      rw [hWcov i] at hi
      obtain ⟨b, hb⟩ := Set.mem_iUnion.1 hi
      exact Set.mem_iUnion.2 ⟨⟨i, b⟩, hb⟩
    · obtain ⟨⟨i, b⟩, hb⟩ := Set.mem_iUnion.1 hy
      refine Set.mem_iUnion.2 ⟨i, ?_⟩
      rw [hWcov i]
      exact Set.mem_iUnion.2 ⟨b, hb⟩
  · exact hWp a.1 a.2

/-- **A constructible set is a finite union of dense basic opens of irreducible closed
sets.**  Refine a presentation of `Y` as a union of locally closed sets `Z ∩ D(g)` by the
irreducible components of the closed parts (`components`): every piece becomes
`C ∩ D(g)` with `C` closed and irreducible, and `C` is then the Zariski closure of the
piece as soon as the piece is nonempty (`vanishingIdeal_inter_dense`).

This is the presentation a consumer needs in order to exhibit a *component of maximal
dimension of the closure of a constructible set together with a dense open of it inside
the set*: the piece of maximal dimension has `affineDim (C a) = affineDim Y`. -/
theorem constructible_irreducible_pieces {Y : Set (ι → K)} (hY : IsAffineConstructible Y) :
    ∃ (J : Type) (_ : Finite J) (C : J → Set (ι → K)) (g : J → MvPolynomial ι K),
      (∀ a, (MvPolynomial.vanishingIdeal K (C a)).IsPrime) ∧
      (∀ a, zclosure (C a) = C a) ∧
      Y = ⋃ a, (C a ∩ {y | aeval y (g a) ≠ 0}) := by
  classical
  obtain ⟨I, hI, P, hPlc, rfl⟩ := hY
  have _ : Finite I := hI
  choose Z g hZ hPeq using hPlc
  choose m C hCprime hCcl _ hcov _ _ using fun i : I => components (K := K) (Z i)
  refine ⟨Σ i : I, Fin (m i), inferInstance, fun a => C a.1 a.2, fun a => g a.1,
    fun a => hCprime a.1 a.2, fun a => hCcl a.1 a.2, ?_⟩
  have hZeq : ∀ i : I, Z i = ⋃ j, C i j := fun i => by rw [← hZ i]; exact hcov i
  refine le_antisymm (fun y hy => ?_) (fun y hy => ?_)
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy
    rw [hPeq i] at hi
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (hZeq i ▸ hi.1)
    exact Set.mem_iUnion.2 ⟨⟨i, j⟩, hj, hi.2⟩
  · obtain ⟨⟨i, j⟩, hj⟩ := Set.mem_iUnion.1 hy
    refine Set.mem_iUnion.2 ⟨i, ?_⟩
    rw [hPeq i]
    exact ⟨hZeq i ▸ Set.mem_iUnion.2 ⟨j, hj.1⟩, hj.2⟩

/-- **A constructible set that is dense in an irreducible closed set contains a
dense basic open of it.**

Decompose the constructible set into irreducible pieces `C_a ∩ D(q_a)`
(`constructible_irreducible_pieces`).  Their traces on `V` cover `L ∩ V`, which
is dense in `V`, so the ideal of `V` is the finite infimum of their ideals;
being prime it equals one of them, and that piece's basic open then lies inside
both `V` and `L`.

This is what turns "the image of a component lands in a locus" into the shape
the (SI) layer asks for — an irreducible `V(I)` with a dense open inside the
locus (`Pencil.SILocus`). -/
theorem exists_nonvanishing_subset_of_constructible
    {L : Set (ι → K)} (hL : IsAffineConstructible L)
    {V : Set (ι → K)} (hVcl : zclosure V = V)
    (hVp : (MvPolynomial.vanishingIdeal K V).IsPrime)
    (hdense : zclosure (L ∩ V) = V) :
    ∃ g ∉ MvPolynomial.vanishingIdeal K V,
      V ∩ {y | MvPolynomial.aeval y g ≠ 0} ⊆ L := by
  classical
  obtain ⟨J, hJ, C, q, hCp, hCcl, hcov⟩ := constructible_irreducible_pieces hL
  have _ : Finite J := hJ
  have _ : Fintype J := Fintype.ofFinite J
  set W : J → Set (ι → K) := fun a => C a ∩ {y | MvPolynomial.aeval y (q a) ≠ 0} ∩ V with hWdef
  have hLV : L ∩ V = ⋃ a, W a := by rw [hWdef, hcov, Set.iUnion_inter]
  -- the ideal of `V` is the infimum of the ideals of the pieces
  have hid : MvPolynomial.vanishingIdeal K V = ⨅ a, MvPolynomial.vanishingIdeal K (W a) := by
    rw [← hdense, vanishingIdeal_zclosure, hLV, vanishingIdeal_iUnion]
  -- primality picks one of them out
  have hle : (Finset.univ : Finset J).inf (fun a => MvPolynomial.vanishingIdeal K (W a))
      ≤ MvPolynomial.vanishingIdeal K V := by
    rw [Finset.inf_univ_eq_iInf, hid]
  obtain ⟨a₀, -, ha₀⟩ := (Ideal.IsPrime.inf_le' hVp).mp hle
  have hsub : MvPolynomial.vanishingIdeal K V ≤ MvPolynomial.vanishingIdeal K (W a₀) :=
    MvPolynomial.vanishingIdeal_anti_mono fun y hy => hy.2
  have heq : MvPolynomial.vanishingIdeal K (W a₀) = MvPolynomial.vanishingIdeal K V :=
    le_antisymm ha₀ hsub
  -- so `V` is the closure of that piece, hence inside its closed part
  have hVC : V ⊆ C a₀ := by
    have hVW : V = zclosure (W a₀) := by
      rw [zclosure, heq, ← zclosure, hVcl]
    rw [hVW]
    calc zclosure (W a₀) ⊆ zclosure (C a₀) := zclosure_mono fun y hy => hy.1.1
      _ = C a₀ := hCcl a₀
  -- and its multiplier does not vanish on `V`
  have hqn : q a₀ ∉ MvPolynomial.vanishingIdeal K V := by
    intro hq
    have hemp : W a₀ = ∅ := by
      ext y
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨⟨-, hyq⟩, hyV⟩
      exact hyq (by
        rw [MvPolynomial.aeval_eq_eval]
        exact MvPolynomial.mem_vanishingIdeal_iff.mp hq y hyV)
    have hone : (1 : MvPolynomial ι K) ∈ MvPolynomial.vanishingIdeal K (W a₀) := by
      rw [hemp]
      exact MvPolynomial.mem_vanishingIdeal_iff.2 fun y hy => hy.elim
    rw [heq] at hone
    exact hVp.ne_top (Ideal.eq_top_of_isUnit_mem _ hone isUnit_one)
  refine ⟨q a₀, hqn, fun y hy => ?_⟩
  rw [hcov]
  exact Set.mem_iUnion.2 ⟨a₀, hVC hy.1, hy.2⟩

/-- The graph has the dimension of the locally closed set it presents. -/
theorem affineDim_graphSet {Z : Set (ι → K)} (hZ : zclosure Z = Z) (g : MvPolynomial ι K) :
    affineDim (graphSet Z g) = affineDim (Z ∩ {y | aeval y g ≠ 0}) :=
  affineDim_of_finite_fibres isPolyMap_projSum _ _ (zclosure_graphSet hZ g)
    (projSum_image_graphSet Z g) fun y _ => (graphSet_fibre_subsingleton Z g y).finite

omit [Finite κ] in
/-- The fibres of a polynomial map on the graph have the dimensions of the fibres
on the locally closed set. -/
theorem affineDim_graphSet_fibre {Z : Set (ι → K)} (hZ : zclosure Z = Z)
    (g : MvPolynomial ι K) {f : (ι → K) → (κ → K)} (hf : IsPolyMap f) (x : κ → K) :
    affineDim (graphSet Z g ∩ (fun z => f (projSum z)) ⁻¹' {x})
      = affineDim ((Z ∩ {y | aeval y g ≠ 0}) ∩ f ⁻¹' {x}) := by
  have hcl : zclosure (graphSet Z g ∩ (fun z => f (projSum z)) ⁻¹' {x})
      = graphSet Z g ∩ (fun z => f (projSum z)) ⁻¹' {x} :=
    zclosure_inter (zclosure_graphSet hZ g)
      (zclosure_preimage (isPolyMap_projSum.comp hf) (zclosure_singleton x))
  refine affineDim_of_finite_fibres isPolyMap_projSum _ _ hcl ?_ ?_
  · ext y
    constructor
    · rintro ⟨z, ⟨hzg, hzx⟩, rfl⟩
      exact ⟨(projSum_image_graphSet Z g) ▸ ⟨z, hzg, rfl⟩, hzx⟩
    · rintro ⟨hy, hyx⟩
      obtain ⟨hmem, hproj⟩ := graphSet_lift hy
      refine ⟨_, ⟨hmem, ?_⟩, hproj⟩
      show f (projSum _) ∈ ({x} : Set (κ → K))
      rw [hproj]
      exact hyx
  · intro y _
    refine Set.Finite.subset (graphSet_fibre_subsingleton Z g y).finite ?_
    rintro z ⟨⟨hz, -⟩, hzy⟩
    exact ⟨hz, hzy⟩

/-! ### The fibre-dimension upper bound for locally closed sources -/

/-- **The upper bound, locally closed form, with an explicit bound.**  If every fibre of a
polynomial map on a locally closed set `Y` has dimension at most `c`, then
`dim Y ≤ dim (f '' Y) + c`. -/
theorem affineDim_le_add_fibre_locClosed_le {f : (ι → K) → (κ → K)} (hf : IsPolyMap f)
    (Y : Set (ι → K)) (hY : IsLocClosed Y) (c : WithBot ℕ∞)
    (hc : ∀ x : κ → K, affineDim (Y ∩ f ⁻¹' {x}) ≤ c) :
    affineDim Y ≤ affineDim (f '' Y) + c := by
  obtain ⟨Z, g, hZ, rfl⟩ := hY
  have himg : (fun z => f (projSum z)) '' graphSet Z g = f '' (Z ∩ {y | aeval y g ≠ 0}) := by
    rw [← projSum_image_graphSet Z g]
    exact (Set.image_image f projSum (graphSet Z g)).symm
  have h := affineDim_le_add_fibre (isPolyMap_projSum.comp hf) (graphSet Z g)
    (zclosure_graphSet hZ g) c fun x => by
      rw [affineDim_graphSet_fibre hZ g hf x]; exact hc x
  rw [affineDim_graphSet hZ g, himg] at h
  exact h

/-- **The upper bound, locally closed form.**  The dimension of a locally closed `Y` is at
most the dimension of the closure of its image plus the supremum of the
dimensions of the fibres **of `Y` itself** (not of its closure). -/
theorem affineDim_le_add_fibre_locClosed {f : (ι → K) → (κ → K)} (hf : IsPolyMap f)
    (Y : Set (ι → K)) (hY : IsLocClosed Y) :
    affineDim Y ≤ affineDim (zclosure (f '' Y))
      + ⨆ x : κ → K, affineDim (Y ∩ f ⁻¹' {x}) := by
  rw [affineDim_zclosure]
  exact affineDim_le_add_fibre_locClosed_le hf Y hY _
    fun x => le_iSup (fun x : κ → K => affineDim (Y ∩ f ⁻¹' {x})) x

/-! ### The generic fibre bound with the generic point chosen in a dense subset -/

/-- **The generic fibre bound, dense form.**  For an irreducible closed `C` there
is a point `x` of the image of a dense subset `W ⊆ C` with
`dim (C ∩ f⁻¹ x) + dim (f '' C) ≤ dim C`. -/
theorem exists_generic_fibre_dense {f : (ι → K) → (κ → K)} (hf : IsPolyMap f)
    {C W : Set (ι → K)} (hCp : (MvPolynomial.vanishingIdeal K C).IsPrime)
    (hCcl : zclosure C = C) (hWC : W ⊆ C)
    (hWd : MvPolynomial.vanishingIdeal K W = MvPolynomial.vanishingIdeal K C) :
    ∃ x ∈ f '' W,
      affineDim (C ∩ f ⁻¹' {x}) + affineDim (f '' C) ≤ affineDim C := by
  obtain ⟨F, hF⟩ := hf
  have _ : (MvPolynomial.vanishingIdeal K C).IsPrime := hCp
  have himg : (MvPolynomial.vanishingIdeal K (f '' C)).IsPrime := irreducible_image ⟨F, hF⟩ hCp
  have _ : (MvPolynomial.vanishingIdeal K (f '' C)).IsPrime := himg
  -- the image of the dense subset is dense in the image
  have hWimg : MvPolynomial.vanishingIdeal K (f '' W)
      = MvPolynomial.vanishingIdeal K (f '' C) := by
    rw [vanishingIdeal_image hF, vanishingIdeal_image hF, hWd]
  have hker : ∀ g : MvPolynomial κ K, g ∈ MvPolynomial.vanishingIdeal K (f '' C) ↔
      aeval F g ∈ MvPolynomial.vanishingIdeal K C := by
    intro g
    rw [vanishingIdeal_image hF]
    exact Iff.rfl
  set φ : MvPolynomial κ K ⧸ MvPolynomial.vanishingIdeal K (f '' C) →ₐ[K]
      MvPolynomial ι K ⧸ MvPolynomial.vanishingIdeal K C :=
    Ideal.Quotient.liftₐ _
      ((Ideal.Quotient.mkₐ K (MvPolynomial.vanishingIdeal K C)).comp (aeval F))
      (fun g hg => Ideal.Quotient.eq_zero_iff_mem.2 ((hker g).1 hg)) with hφ
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective a
    have h0 : Ideal.Quotient.mk (MvPolynomial.vanishingIdeal K C) (aeval F g) = 0 := ha
    rw [Ideal.Quotient.eq_zero_iff_mem] at h0 ⊢
    exact (hker g).2 h0
  obtain ⟨a, ha0, hgen⟩ := exists_fibre_dim_le K _ _ φ hinj
  obtain ⟨ag, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hnot : ag ∉ MvPolynomial.vanishingIdeal K (f '' W) := by
    rw [hWimg]
    intro h
    exact ha0 (Ideal.Quotient.eq_zero_iff_mem.2 h)
  obtain ⟨x, hx, hxa⟩ : ∃ x ∈ f '' W, aeval x ag ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hnot fun x hx => hcon x hx
  refine ⟨x, hx, ?_⟩
  have hxC : x ∈ f '' C := by
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨y, hWC hy, rfl⟩
  have hxle : MvPolynomial.vanishingIdeal K (f '' C) ≤
      MvPolynomial.vanishingIdeal K ({x} : Set (κ → K)) := by
    intro q hq z hz
    rw [Set.mem_singleton_iff] at hz
    exact hz ▸ hq x hxC
  have _ : (MvPolynomial.vanishingIdeal K ({x} : Set (κ → K))).IsMaximal := inferInstance
  have hmmax : ((MvPolynomial.vanishingIdeal K ({x} : Set (κ → K))).map
      (Ideal.Quotient.mk (MvPolynomial.vanishingIdeal K (f '' C)))).IsMaximal := by
    refine Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective ?_
    rw [Ideal.mk_ker]
    exact hxle
  have hanot : Ideal.Quotient.mk (MvPolynomial.vanishingIdeal K (f '' C)) ag ∉
      (MvPolynomial.vanishingIdeal K ({x} : Set (κ → K))).map
        (Ideal.Quotient.mk (MvPolynomial.vanishingIdeal K (f '' C))) := by
    intro h
    obtain ⟨b, hb, hbeq⟩ :=
      (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 h
    have hsub : ag - b ∈ MvPolynomial.vanishingIdeal K (f '' C) := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hbeq, sub_self]
    have hmemx : ag ∈ MvPolynomial.vanishingIdeal K ({x} : Set (κ → K)) := by
      have := add_mem (hxle hsub) hb
      simpa using this
    exact hxa (hmemx x rfl)
  have hkey := hgen _ hmmax hanot
  have hfib : ringKrullDim ((MvPolynomial ι K ⧸ MvPolynomial.vanishingIdeal K C) ⧸
      (((MvPolynomial.vanishingIdeal K ({x} : Set (κ → K))).map
        (Ideal.Quotient.mk (MvPolynomial.vanishingIdeal K (f '' C)))).map
          φ.toRingHom)) = affineDim (C ∩ f ⁻¹' {x}) := by
    have hcomp : φ.toRingHom.comp
          (Ideal.Quotient.mk (MvPolynomial.vanishingIdeal K (f '' C))) =
        (Ideal.Quotient.mk (MvPolynomial.vanishingIdeal K C)).comp
          (aeval F : MvPolynomial κ K →ₐ[K] MvPolynomial ι K).toRingHom :=
      RingHom.ext fun g => rfl
    have hmap : (((MvPolynomial.vanishingIdeal K ({x} : Set (κ → K))).map
        (Ideal.Quotient.mk (MvPolynomial.vanishingIdeal K (f '' C)))).map φ.toRingHom) =
        ((MvPolynomial.vanishingIdeal K ({x} : Set (κ → K))).map
          (aeval F : MvPolynomial κ K →ₐ[K] MvPolynomial ι K).toRingHom).map
          (Ideal.Quotient.mk (MvPolynomial.vanishingIdeal K C)) := by
      rw [Ideal.map_map, Ideal.map_map, hcomp]
    rw [hmap, ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotSup _ _),
      ringKrullDim_fibre hF]
    show affineDim (zclosure C ∩ f ⁻¹' {x}) = _
    rw [hCcl]
  rw [show Ideal.map φ
        ((MvPolynomial.vanishingIdeal K ({x} : Set (κ → K))).map
          (Ideal.Quotient.mk (MvPolynomial.vanishingIdeal K (f '' C)))) =
      Ideal.map φ.toRingHom
        ((MvPolynomial.vanishingIdeal K ({x} : Set (κ → K))).map
          (Ideal.Quotient.mk (MvPolynomial.vanishingIdeal K (f '' C)))) from rfl,
    hfib] at hkey
  exact hkey

/-! ### Density of the traces, and the components of a locally closed set -/

omit [IsAlgClosed K] [Finite ι] in
/-- A nonempty basic open subset of an irreducible set is dense in it. -/
theorem vanishingIdeal_inter_dense {C : Set (ι → K)}
    (hCp : (MvPolynomial.vanishingIdeal K C).IsPrime) {g : MvPolynomial ι K}
    (hne : (C ∩ {y | aeval y g ≠ 0}).Nonempty) :
    MvPolynomial.vanishingIdeal K (C ∩ {y | aeval y g ≠ 0})
      = MvPolynomial.vanishingIdeal K C := by
  refine le_antisymm (fun q hq => ?_)
    (MvPolynomial.vanishingIdeal_anti_mono Set.inter_subset_left)
  obtain ⟨y₀, hy₀C, hy₀g⟩ := hne
  have hg : g ∉ MvPolynomial.vanishingIdeal K C := fun h => hy₀g (h y₀ hy₀C)
  have hmul : q * g ∈ MvPolynomial.vanishingIdeal K C := by
    intro y hy
    rw [map_mul]
    by_cases h : aeval y g = 0
    · rw [h, mul_zero]
    · rw [hq y ⟨hy, h⟩, zero_mul]
  rcases hCp.mem_or_mem hmul with h | h
  · exact h
  · exact absurd h hg

omit [IsAlgClosed K] [Finite ι] in
/-- A basic open is nonempty as soon as its polynomial does not vanish identically. -/
theorem nonempty_inter_nonvanishing {C : Set (ι → K)} {g : MvPolynomial ι K}
    (hg : g ∉ MvPolynomial.vanishingIdeal K C) : (C ∩ {y | aeval y g ≠ 0}).Nonempty := by
  by_contra h
  refine hg fun y hy => ?_
  by_contra hyg
  exact h ⟨y, hy, hyg⟩

omit [IsAlgClosed K] [Finite ι] in
/-- **A dense basic open has the dimension of the irreducible set it sits in.**  The
`affineDim` form of `vanishingIdeal_inter_dense`; `affineDim` is by construction the
dimension of the vanishing ideal, so no dimension theory is involved. -/
theorem affineDim_inter_dense {C : Set (ι → K)}
    (hCp : (MvPolynomial.vanishingIdeal K C).IsPrime) {g : MvPolynomial ι K}
    (hg : g ∉ MvPolynomial.vanishingIdeal K C) :
    affineDim (C ∩ {y | aeval y g ≠ 0}) = affineDim C := by
  unfold affineDim
  rw [vanishingIdeal_inter_dense hCp (nonempty_inter_nonvanishing hg)]

/-! ### Irreducibility of the graph

`graphSet Z g` is the graph of `1/g` over `Z ∩ D(g)`, so it is a copy of that basic open
and inherits its irreducibility.  Classically this is the numerator calculus: modulo the
chart equation `t g − 1` every polynomial in the chart coordinates is a polynomial in the
base coordinates divided by a power of `g`, and a polynomial vanishes on the graph exactly
when its numerator vanishes on the base. -/

/-- The chart equation `t · g − 1` cutting `graphSet Z g` out of `Z × 𝔸¹`. -/
private noncomputable def graphRel (g : MvPolynomial ι K) : MvPolynomial (ι ⊕ Unit) K :=
  X (Sum.inr ()) * rename Sum.inl g - 1

omit [IsAlgClosed K] [Finite ι] in
private theorem aeval_graphRel (g : MvPolynomial ι K) (w : ι ⊕ Unit → K) :
    aeval w (graphRel g) = w (Sum.inr ()) * aeval (projSum w) g - 1 := by
  rw [graphRel, map_sub, map_mul, map_one, aeval_X, aeval_rename]
  rfl

omit [IsAlgClosed K] [Finite ι] in
private theorem aeval_eq_zero_of_mem_graphSpan {Z : Set (ι → K)} {g : MvPolynomial ι K}
    {w : ι ⊕ Unit → K} (hw : w ∈ graphSet Z g)
    {j : MvPolynomial (ι ⊕ Unit) K} (hj : j ∈ Ideal.span {graphRel (K := K) g}) :
    aeval w j = 0 := by
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp hj
  rw [map_mul, aeval_graphRel, hw.2, sub_self, mul_zero]

omit [IsAlgClosed K] [Finite ι] in
/-- **Clearing denominators**: modulo the chart equation every polynomial in the chart
coordinates is a polynomial in the base coordinates divided by a power of `g`. -/
private theorem exists_numerator (g : MvPolynomial ι K) (p : MvPolynomial (ι ⊕ Unit) K) :
    ∃ (d : ℕ) (ν : MvPolynomial ι K),
      (rename Sum.inl g) ^ d * p - rename Sum.inl ν ∈ Ideal.span {graphRel (K := K) g} := by
  induction p using MvPolynomial.induction_on with
  | C a => exact ⟨0, C a, by simp⟩
  | add p₁ p₂ h₁ h₂ =>
      obtain ⟨d₁, ν₁, hh₁⟩ := h₁
      obtain ⟨d₂, ν₂, hh₂⟩ := h₂
      refine ⟨d₁ + d₂, g ^ d₂ * ν₁ + g ^ d₁ * ν₂, ?_⟩
      have hrw : (rename Sum.inl g) ^ (d₁ + d₂) * (p₁ + p₂) -
          rename Sum.inl (g ^ d₂ * ν₁ + g ^ d₁ * ν₂) =
          (rename Sum.inl g) ^ d₂ * ((rename Sum.inl g) ^ d₁ * p₁ - rename Sum.inl ν₁) +
            (rename Sum.inl g) ^ d₁ *
              ((rename Sum.inl g) ^ d₂ * p₂ - rename Sum.inl ν₂) := by
        simp only [map_add, map_mul, map_pow]
        ring
      rw [hrw]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hh₁) (Ideal.mul_mem_left _ _ hh₂)
  | mul_X p j hp =>
      obtain ⟨d, ν, hh⟩ := hp
      cases j with
      | inl i =>
          refine ⟨d, ν * X i, ?_⟩
          have hrw : (rename Sum.inl g) ^ d * (p * X (Sum.inl i)) -
              rename Sum.inl (ν * X i) =
              ((rename Sum.inl g) ^ d * p - rename Sum.inl ν) * X (Sum.inl i) := by
            simp only [map_mul, rename_X]
            ring
          rw [hrw]
          exact Ideal.mul_mem_right _ _ hh
      | inr u =>
          refine ⟨d + 1, ν, ?_⟩
          have hu : u = () := rfl
          subst hu
          have hrw : (rename Sum.inl g) ^ (d + 1) * (p * X (Sum.inr ())) -
                rename Sum.inl ν =
              ((rename Sum.inl g) ^ d * p) * graphRel (K := K) g +
                ((rename Sum.inl g) ^ d * p - rename Sum.inl ν) := by
            rw [graphRel]
            ring
          rw [hrw]
          exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)) hh

omit [IsAlgClosed K] [Finite ι] in
/-- The numerator identity at a point of the graph. -/
private theorem aeval_numerator {Z : Set (ι → K)} {g : MvPolynomial ι K}
    {p : MvPolynomial (ι ⊕ Unit) K} {d : ℕ} {ν : MvPolynomial ι K}
    (h : (rename Sum.inl g) ^ d * p - rename Sum.inl ν ∈ Ideal.span {graphRel (K := K) g})
    {w : ι ⊕ Unit → K} (hw : w ∈ graphSet Z g) :
    (aeval (projSum w) g) ^ d * aeval w p = aeval (projSum w) ν := by
  have h0 := aeval_eq_zero_of_mem_graphSpan hw h
  rw [map_sub, map_mul, map_pow, aeval_rename, aeval_rename, sub_eq_zero] at h0
  exact h0

omit [IsAlgClosed K] [Finite ι] in
/-- **A polynomial vanishes on the graph exactly when its numerator vanishes on the
base.** -/
theorem mem_vanishingIdeal_graphSet_iff {Z : Set (ι → K)} {g : MvPolynomial ι K}
    (hZ : (MvPolynomial.vanishingIdeal K Z).IsPrime)
    (hg : g ∉ MvPolynomial.vanishingIdeal K Z)
    {p : MvPolynomial (ι ⊕ Unit) K} {d : ℕ} {ν : MvPolynomial ι K}
    (h : (rename Sum.inl g) ^ d * p - rename Sum.inl ν ∈ Ideal.span {graphRel (K := K) g}) :
    p ∈ MvPolynomial.vanishingIdeal K (graphSet Z g) ↔
      ν ∈ MvPolynomial.vanishingIdeal K Z := by
  constructor
  · intro hp
    rw [← vanishingIdeal_inter_dense hZ (nonempty_inter_nonvanishing hg)]
    rintro y hy
    obtain ⟨hmem, hproj⟩ := graphSet_lift hy
    have hnum := aeval_numerator h hmem
    rw [hproj, hp _ hmem, mul_zero] at hnum
    exact hnum.symm
  · intro hν w hw
    have hnum := aeval_numerator h hw
    rw [hν _ hw.1] at hnum
    have hgne : aeval (projSum w) g ≠ 0 := by
      intro h0
      have h2 := hw.2
      rw [h0, mul_zero] at h2
      exact zero_ne_one h2
    rcases mul_eq_zero.mp hnum with h1 | h1
    · exact absurd h1 (pow_ne_zero _ hgne)
    · exact h1

omit [IsAlgClosed K] [Finite ι] in
/-- **The graph of an irreducible set along a nonvanishing `g` is irreducible.**  This is
the one property of `graphSet` that `zclosure_graphSet`, `projSum_image_graphSet` and
`graphSet_fibre_subsingleton` do not give: the API's `graphSet` is a copy of the basic open
`Z ∩ D(g)`, which is dense in `Z`. -/
theorem isPrime_vanishingIdeal_graphSet {Z : Set (ι → K)} {g : MvPolynomial ι K}
    (hZ : (MvPolynomial.vanishingIdeal K Z).IsPrime)
    (hg : g ∉ MvPolynomial.vanishingIdeal K Z) :
    (MvPolynomial.vanishingIdeal K (graphSet Z g)).IsPrime := by
  constructor
  · intro htop
    rw [vanishingIdeal_eq_top_iff] at htop
    obtain ⟨hmem, -⟩ := graphSet_lift (nonempty_inter_nonvanishing hg).choose_spec
    exact absurd htop (Set.Nonempty.ne_empty ⟨_, hmem⟩)
  · intro p₁ p₂ hp
    obtain ⟨d₁, ν₁, h₁⟩ := exists_numerator g p₁
    obtain ⟨d₂, ν₂, h₂⟩ := exists_numerator g p₂
    have hmul : (rename Sum.inl g) ^ (d₁ + d₂) * (p₁ * p₂) -
        rename Sum.inl (ν₁ * ν₂) ∈ Ideal.span {graphRel (K := K) g} := by
      have hrw : (rename Sum.inl g) ^ (d₁ + d₂) * (p₁ * p₂) - rename Sum.inl (ν₁ * ν₂) =
          ((rename Sum.inl g) ^ d₁ * p₁ - rename Sum.inl ν₁) *
              ((rename Sum.inl g) ^ d₂ * p₂) +
            rename Sum.inl ν₁ *
              ((rename Sum.inl g) ^ d₂ * p₂ - rename Sum.inl ν₂) := by
        simp only [map_mul]
        ring
      rw [hrw]
      exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ h₁) (Ideal.mul_mem_left _ _ h₂)
    rcases hZ.mem_or_mem ((mem_vanishingIdeal_graphSet_iff hZ hg hmul).mp hp) with h | h
    · exact Or.inl ((mem_vanishingIdeal_graphSet_iff hZ hg h₁).mpr h)
    · exact Or.inr ((mem_vanishingIdeal_graphSet_iff hZ hg h₂).mpr h)

/-- **The components of a locally closed set.**  The traces `C i ∩ Y` of the
irreducible components of `zclosure Y` cover `Y`, are `G`-stable when `Y` is,
and are dense in the components they come from, so their dimensions are those of
the components. -/
theorem locClosed_components (A : PolyAction K γ ι) (Y : Set (ι → K))
    (hY : IsLocClosed Y) (hYS : Y ⊆ A.S) (hst : ∀ g ∈ A.G, ∀ y ∈ Y, A.act g y ∈ Y) :
    ∃ (m : ℕ) (C : Fin m → Set (ι → K)),
      Y = ⋃ i, (C i ∩ Y) ∧
      (∀ i, (MvPolynomial.vanishingIdeal K (C i)).IsPrime) ∧
      (∀ i, zclosure (C i) = C i) ∧
      (∀ i, (C i ∩ Y).Nonempty →
        MvPolynomial.vanishingIdeal K (C i ∩ Y) = MvPolynomial.vanishingIdeal K (C i)) ∧
      (∀ i, ∀ g ∈ A.G, ∀ y ∈ C i ∩ Y, A.act g y ∈ C i ∩ Y) ∧
      affineDim Y = ⨆ i, affineDim (C i ∩ Y) := by
  obtain ⟨Z, g, hZ, hYeq⟩ := hY
  obtain ⟨m, C, hCprime, hCcl, hCsub, hcover, hmax, -⟩ := components (K := K) Y
  -- every component of the closure lies in `Z`
  have hCZ : ∀ i, C i ⊆ Z := by
    intro i
    refine (hCsub i).trans ?_
    rw [← hZ]
    exact zclosure_mono (by rw [hYeq]; exact Set.inter_subset_left)
  -- so the trace of a component is its basic open piece
  have htrace : ∀ i, C i ∩ Y = C i ∩ {y | aeval y g ≠ 0} := by
    intro i
    rw [hYeq]
    ext y
    exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hCZ i h.1, h.2⟩⟩
  have hdense : ∀ i, (C i ∩ Y).Nonempty →
      MvPolynomial.vanishingIdeal K (C i ∩ Y) = MvPolynomial.vanishingIdeal K (C i) := by
    intro i hne
    rw [htrace i] at hne ⊢
    exact vanishingIdeal_inter_dense (hCprime i) hne
  have hclosure : ∀ i, (C i ∩ Y).Nonempty → zclosure (C i ∩ Y) = C i := by
    intro i hne
    show MvPolynomial.zeroLocus K (MvPolynomial.vanishingIdeal K (C i ∩ Y)) = C i
    rw [hdense i hne]
    exact hCcl i
  have hcov : Y = ⋃ i, (C i ∩ Y) := by
    refine le_antisymm (fun y hy => ?_) (Set.iUnion_subset fun i => Set.inter_subset_right)
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hcover ▸ subset_zclosure Y hy)
    exact Set.mem_iUnion.2 ⟨i, hi, hy⟩
  refine ⟨m, C, hcov, hCprime, hCcl, hdense, fun i g' hg' y hy => ⟨?_, hst g' hg' y hy.2⟩, ?_⟩
  · -- stability: the sweep of the trace is irreducible, contains the component, lies in `Y`
    have hne : (C i ∩ Y).Nonempty := ⟨y, hy⟩
    have hprime : (MvPolynomial.vanishingIdeal K (C i ∩ Y)).IsPrime := by
      rw [hdense i hne]; exact hCprime i
    have hsweepY : A.sweep (C i ∩ Y) ⊆ Y := by
      rintro _ ⟨h, hh, z, hz, rfl⟩
      exact hst h hh z hz.2
    have hZp : (MvPolynomial.vanishingIdeal K (zclosure (A.sweep (C i ∩ Y)))).IsPrime := by
      rw [vanishingIdeal_zclosure]
      exact A.irreducible_sweep hprime
    have hCsubs : C i ⊆ zclosure (A.sweep (C i ∩ Y)) := by
      have h1 : zclosure (C i ∩ Y) ⊆ zclosure (A.sweep (C i ∩ Y)) :=
        zclosure_mono (A.subset_sweep (fun w hw => hYS hw.2))
      rwa [hclosure i hne] at h1
    have hsubY : zclosure (A.sweep (C i ∩ Y)) ⊆ zclosure Y := zclosure_mono hsweepY
    exact hmax i _ hZp hCsubs hsubY (subset_zclosure _ ⟨g', hg', y, hy, rfl⟩)
  · have h := affineDim_iUnion fun i => C i ∩ Y
    rwa [← hcov] at h

/-! ### The dimension counts -/

/-- **Finite fibres from an upper bound.**  Finite fibres make the fibre-dimension upper
bound at `c = 0` an equality:
it gives `dim Y ≤ dim (f '' Y)`, and the image of a polynomial map never grows
the dimension.  The locally closed and constructible forms below differ only in which
upper bound they hand to this. -/
private theorem affineDim_of_finite_fibres_of_D2 {f : (ι → K) → (κ → K)} (hf : IsPolyMap f)
    (Y : Set (ι → K)) (X : Set (κ → K)) (hXY : f '' Y = X)
    (hfin : ∀ x ∈ X, (Y ∩ f ⁻¹' {x}).Finite)
    (hD2 : (∀ x : κ → K, affineDim (Y ∩ f ⁻¹' {x}) ≤ 0) →
      affineDim Y ≤ affineDim (f '' Y) + 0) :
    affineDim Y = affineDim X := by
  refine le_antisymm ?_ ?_
  · have h := hD2 ?_
    · rwa [hXY, add_zero] at h
    · intro x
      by_cases hx : x ∈ X
      · exact affineDim_le_zero_of_finite (hfin x hx)
      · have hempty : Y ∩ f ⁻¹' {x} = ∅ :=
          Set.eq_empty_iff_forall_notMem.2 fun y hy => hx (hXY ▸ ⟨y, hy.1, hy.2⟩)
        rw [hempty, affineDim_empty]
        exact bot_le
  · rw [← hXY]
    exact affineDim_image_le hf Y

/-- **Finite fibres, locally closed.**  A polynomial map with finite fibres does not
change the dimension of a locally closed source. -/
theorem affineDim_of_finite_fibres_locClosed {f : (ι → K) → (κ → K)} (hf : IsPolyMap f)
    (Y : Set (ι → K)) (X : Set (κ → K)) (hY : IsLocClosed Y) (hXY : f '' Y = X)
    (hfin : ∀ x ∈ X, (Y ∩ f ⁻¹' {x}).Finite) :
    affineDim Y = affineDim X :=
  affineDim_of_finite_fibres_of_D2 hf Y X hXY hfin
    (affineDim_le_add_fibre_locClosed_le hf Y hY 0)

/-- **The upper bound, constructible form, with an explicit bound.**  If every fibre of a
polynomial map on a constructible set `Y` has dimension at most `c`, then
`dim Y ≤ dim (f '' Y) + c`. -/
theorem affineDim_le_add_fibre_constructible_le {f : (ι → K) → (κ → K)} (hf : IsPolyMap f)
    (Y : Set (ι → K)) (hY : IsAffineConstructible Y) (c : WithBot ℕ∞)
    (hc : ∀ x : κ → K, affineDim (Y ∩ f ⁻¹' {x}) ≤ c) :
    affineDim Y ≤ affineDim (f '' Y) + c := by
  obtain ⟨I, hI, P, hPlc, hcov⟩ := hY
  have _ : Finite I := hI
  have hPY : ∀ i, P i ⊆ Y := fun i => hcov ▸ Set.subset_iUnion P i
  have hdim : affineDim Y = ⨆ i, affineDim (P i) := by
    have h := affineDim_iUnion P
    rwa [← hcov] at h
  rw [hdim]
  refine iSup_le fun i => ?_
  refine le_trans (affineDim_le_add_fibre_locClosed_le hf (P i) (hPlc i) c fun x => ?_) ?_
  · exact le_trans (affineDim_mono (Set.inter_subset_inter_left _ (hPY i))) (hc x)
  · exact add_le_add (affineDim_mono (Set.image_mono (hPY i))) le_rfl

/-- **Finite fibres, constructible.**  A polynomial map with finite fibres does not
change the dimension of a constructible source. -/
theorem affineDim_of_finite_fibres_constructible {f : (ι → K) → (κ → K)} (hf : IsPolyMap f)
    (Y : Set (ι → K)) (X : Set (κ → K)) (hY : IsAffineConstructible Y) (hXY : f '' Y = X)
    (hfin : ∀ x ∈ X, (Y ∩ f ⁻¹' {x}).Finite) :
    affineDim Y = affineDim X :=
  affineDim_of_finite_fibres_of_D2 hf Y X hXY hfin
    (affineDim_le_add_fibre_constructible_le hf Y hY 0)

/-- **The lower half of the orbit fibration, constructible.**  A polynomial map `f` that is
constant along the orbits of `A` on a constructible `A`-stable `Y`, all of whose orbits have
dimension at least `e`, satisfies `dim (f '' Y) + e ≤ dim Y`.

Unlike `affineDim_of_orbit_fibration_constructible` the fibres are *not* assumed to be single
orbits: they may be unions of orbits — as in `Chain/Springer`, where the fibre of the partner
map over `M` is the set of *all* frames adapted to both `N` and `M` — so only this half of the
count is available, and only with the orbit *contained* in the fibre.  The proof sweeps the
piece of `Y` whose image has the largest dimension into an irreducible `A`-stable set and puts
the orbit inside its generic fibre (`exists_generic_fibre_dense`). -/
theorem affineDim_image_add_le_of_orbit_le_constructible (A : PolyAction K γ ι)
    {f : (ι → K) → (κ → K)} (hf : IsPolyMap f)
    (Y : Set (ι → K)) (X : Set (κ → K)) (e : WithBot ℕ∞)
    (hY : IsAffineConstructible Y) (hYS : Y ⊆ A.S) (hXY : f '' Y = X)
    (hstable : ∀ g ∈ A.G, ∀ y ∈ Y, A.act g y ∈ Y)
    (hinv : ∀ g ∈ A.G, ∀ y ∈ Y, f (A.act g y) = f y)
    (horb : ∀ y ∈ Y, e ≤ affineDim (A.orbit y)) :
    affineDim X + e ≤ affineDim Y := by
  rcases Set.eq_empty_or_nonempty X with hX | hX
  · rw [hX, affineDim_empty, WithBot.bot_add]
    exact bot_le
  obtain ⟨J, hJ, W, hWY, hcov, hWp⟩ := constructible_pieces hY
  have _ : Finite J := hJ
  have hXcov : X = ⋃ a, f '' W a := by
    rw [← hXY]
    conv_lhs => rw [hcov]
    rw [Set.image_iUnion]
  have hJne : Nonempty J := by
    rcases isEmpty_or_nonempty J with hemp | hne
    · exfalso
      have hXe : X = ∅ := by rw [hXcov]; simp
      rw [hXe] at hX
      simp at hX
    · exact hne
  obtain ⟨a₀, ha₀⟩ := Finite.exists_max fun a : J => affineDim (f '' W a)
  have hXdim : affineDim X = affineDim (f '' W a₀) := by
    rw [hXcov, affineDim_iUnion]
    exact le_antisymm (iSup_le ha₀) (le_iSup (fun a => affineDim (f '' W a)) a₀)
  set S : Set (ι → K) := A.sweep (W a₀) with hSdef
  have hSY : S ⊆ Y := by
    rintro _ ⟨g, hg, w, hw, rfl⟩
    exact hstable g hg w (hWY a₀ hw)
  have hWS : W a₀ ⊆ S := A.subset_sweep (fun w hw => hYS (hWY a₀ hw))
  have hSp : (MvPolynomial.vanishingIdeal K S).IsPrime := A.irreducible_sweep (hWp a₀)
  have hCp : (MvPolynomial.vanishingIdeal K (zclosure S)).IsPrime := by
    rw [vanishingIdeal_zclosure]; exact hSp
  have hdense : MvPolynomial.vanishingIdeal K S
      = MvPolynomial.vanishingIdeal K (zclosure S) := (vanishingIdeal_zclosure S).symm
  have hfCdim : affineDim (f '' zclosure S) = affineDim X := by
    refine le_antisymm ?_ ?_
    · calc affineDim (f '' zclosure S)
          ≤ affineDim (zclosure (f '' S)) := affineDim_mono (image_zclosure_subset hf S)
        _ = affineDim (f '' S) := affineDim_zclosure _
        _ ≤ affineDim X := by
            rw [← hXY]; exact affineDim_mono (Set.image_mono hSY)
    · rw [hXdim]
      exact affineDim_mono (Set.image_mono (hWS.trans (subset_zclosure S)))
  obtain ⟨x, hxmem, hD3⟩ :=
    exists_generic_fibre_dense hf hCp (zclosure_zclosure S) (subset_zclosure S) hdense
  obtain ⟨z, hzS, hzx⟩ := hxmem
  have horbsub : A.orbit z ⊆ zclosure S ∩ f ⁻¹' {x} := by
    rintro w hw
    obtain ⟨g, hg, rfl⟩ := hw
    refine ⟨subset_zclosure S
      (A.orbit_subset_sweep (fun w hw => hYS (hWY a₀ hw)) hzS ⟨g, hg, rfl⟩), ?_⟩
    rw [Set.mem_preimage, Set.mem_singleton_iff, hinv g hg z (hSY hzS)]
    exact hzx
  have hege : e ≤ affineDim (zclosure S ∩ f ⁻¹' {x}) :=
    le_trans (horb z (hSY hzS)) (affineDim_mono horbsub)
  calc affineDim X + e = e + affineDim (f '' zclosure S) := by rw [hfCdim, add_comm]
    _ ≤ affineDim (zclosure S ∩ f ⁻¹' {x}) + affineDim (f '' zclosure S) :=
        add_le_add hege le_rfl
    _ ≤ affineDim (zclosure S) := hD3
    _ = affineDim S := affineDim_zclosure S
    _ ≤ affineDim Y := affineDim_mono hSY

/-- **The orbit fibration, constructible.**  If a polynomial map `f` on a constructible
`A`-stable `Y` is constant along the orbits of `A`, each of its fibres is a single orbit,
and all orbits have dimension `e`, then `dim (f '' Y) + e = dim Y`. -/
theorem affineDim_of_orbit_fibration_constructible (A : PolyAction K γ ι)
    {f : (ι → K) → (κ → K)} (hf : IsPolyMap f)
    (Y : Set (ι → K)) (X : Set (κ → K)) (e : ℕ)
    (hY : IsAffineConstructible Y) (hYS : Y ⊆ A.S) (hXY : f '' Y = X)
    (hstable : ∀ g ∈ A.G, ∀ y ∈ Y, A.act g y ∈ Y)
    (hinv : ∀ g ∈ A.G, ∀ y ∈ Y, f (A.act g y) = f y)
    (hfib : ∀ x ∈ X, ∃ y ∈ Y, Y ∩ f ⁻¹' {x} = A.orbit y)
    (horb : ∀ y ∈ Y, affineDim (A.orbit y) = (e : WithBot ℕ∞)) :
    affineDim X + (e : WithBot ℕ∞) = affineDim Y := by
  have hout : ∀ x : κ → K, x ∉ X → Y ∩ f ⁻¹' {x} = ∅ := fun x hx =>
    Set.eq_empty_iff_forall_notMem.2 fun y hy => hx (hXY ▸ ⟨y, hy.1, hy.2⟩)
  refine le_antisymm ?_ ?_
  · -- lower bound: the orbits sit inside the fibres
    exact affineDim_image_add_le_of_orbit_le_constructible A hf Y X (e : WithBot ℕ∞) hY hYS hXY
      hstable hinv fun y hy => le_of_eq (horb y hy).symm
  · -- upper bound, through the fibre-dimension bound
    have h := affineDim_le_add_fibre_constructible_le hf Y hY (e : WithBot ℕ∞) ?_
    · rwa [hXY] at h
    · intro x
      by_cases hx : x ∈ X
      · obtain ⟨y, hy, hyeq⟩ := hfib x hx
        rw [hyeq, horb y hy]
      · rw [hout x hx, affineDim_empty]
        exact bot_le

/-- **The transitive fibration, constructible.**  If a polynomial map `f` from a
constructible `A`-stable `Y` onto `X` is equivariant for an action of the group on `X`
that is transitive, then `dim Y = dim X + d`, where `d` is the dimension of the fibre
over a base point `x₀`. -/
theorem affineDim_of_transitive_fibration_constructible (A : PolyAction K γ ι)
    (actX : (γ → K) → (κ → K) → (κ → K)) {f : (ι → K) → (κ → K)} (hf : IsPolyMap f)
    (Y : Set (ι → K)) (X : Set (κ → K)) (x₀ : κ → K) (d : ℕ)
    (hY : IsAffineConstructible Y) (hYS : Y ⊆ A.S) (hXY : f '' Y = X)
    (hstable : ∀ g ∈ A.G, ∀ y ∈ Y, A.act g y ∈ Y)
    (hequiv : ∀ g ∈ A.G, ∀ y ∈ Y, f (A.act g y) = actX g (f y))
    (hinvX : ∀ g ∈ A.G, ∀ x ∈ X, actX (A.inv g) (actX g x) = x)
    (hx₀ : x₀ ∈ X) (htrans : ∀ x ∈ X, ∃ g ∈ A.G, actX g x₀ = x)
    (hd : affineDim (Y ∩ f ⁻¹' {x₀}) = (d : WithBot ℕ∞)) :
    affineDim Y = affineDim X + (d : WithBot ℕ∞) := by
  have htranslate : ∀ S : Set (ι → K), S ⊆ Y → (∀ g ∈ A.G, ∀ y ∈ S, A.act g y ∈ S) →
      ∀ g ∈ A.G, S ∩ f ⁻¹' {actX g x₀} = A.act g '' (S ∩ f ⁻¹' {x₀}) := by
    intro S hSY hSst g hg
    refine le_antisymm ?_ ?_
    · rintro w ⟨hwS, hwf⟩
      rw [Set.mem_preimage, Set.mem_singleton_iff] at hwf
      refine ⟨A.act (A.inv g) w, ⟨hSst _ (A.inv_mem g hg) w hwS, ?_⟩, A.act_inv_right g hg w (hYS (hSY hwS))⟩
      rw [Set.mem_preimage, Set.mem_singleton_iff,
        hequiv _ (A.inv_mem g hg) w (hSY hwS), hwf]
      exact hinvX g hg x₀ hx₀
    · rintro _ ⟨y, ⟨hyS, hyf⟩, rfl⟩
      rw [Set.mem_preimage, Set.mem_singleton_iff] at hyf
      exact ⟨hSst g hg y hyS, by
        rw [Set.mem_preimage, Set.mem_singleton_iff, hequiv g hg y (hSY hyS), hyf]⟩
  have htransdim : ∀ S : Set (ι → K), S ⊆ Y → (∀ g ∈ A.G, ∀ y ∈ S, A.act g y ∈ S) →
      ∀ g ∈ A.G, affineDim (S ∩ f ⁻¹' {actX g x₀}) =
        affineDim (S ∩ f ⁻¹' {x₀}) := by
    intro S hSY hSst g hg
    rw [htranslate S hSY hSst g hg]
    exact affineDim_image_eq (A.act_isPolyMap g) (A.act_isPolyMap (A.inv g))
      fun y hy => A.act_inv_left g hg y (hYS (hSY hy.1))
  have hout : ∀ x : κ → K, x ∉ X → Y ∩ f ⁻¹' {x} = ∅ := fun x hx =>
    Set.eq_empty_iff_forall_notMem.2 fun y hy => hx (hXY ▸ ⟨y, hy.1, hy.2⟩)
  refine le_antisymm ?_ ?_
  · -- upper bound, through the fibre-dimension bound
    have h := affineDim_le_add_fibre_constructible_le hf Y hY (d : WithBot ℕ∞) ?_
    · rwa [hXY] at h
    · intro x
      by_cases hx : x ∈ X
      · obtain ⟨g, hg, rfl⟩ := htrans x hx
        rw [htransdim Y le_rfl hstable g hg, hd]
      · rw [hout x hx, affineDim_empty]
        exact bot_le
  · -- lower bound
    obtain ⟨J, hJ, W, hWY, hcov, hWp⟩ := constructible_pieces hY
    have _ : Finite J := hJ
    have hfibcov : Y ∩ f ⁻¹' {x₀} = ⋃ a, W a ∩ f ⁻¹' {x₀} := by
      conv_lhs => rw [hcov]
      rw [Set.iUnion_inter]
    have hJne : Nonempty J := by
      rcases isEmpty_or_nonempty J with hemp | hne
      · exfalso
        have hYe : Y = ∅ := by rw [hcov]; simp
        have hXe : X = ∅ := by rw [← hXY, hYe]; simp
        rw [hXe] at hx₀
        simp at hx₀
      · exact hne
    obtain ⟨a₀, ha₀⟩ :=
      Finite.exists_max fun a : J => affineDim (W a ∩ f ⁻¹' {x₀})
    have hdi₀ : affineDim (W a₀ ∩ f ⁻¹' {x₀}) = (d : WithBot ℕ∞) := by
      rw [← hd, hfibcov, affineDim_iUnion]
      exact (le_antisymm (iSup_le ha₀)
        (le_iSup (fun a => affineDim (W a ∩ f ⁻¹' {x₀})) a₀)).symm
    have hnefib : (W a₀ ∩ f ⁻¹' {x₀}).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro hemp
      rw [hemp, affineDim_empty] at hdi₀
      exact absurd hdi₀ (by simp)
    obtain ⟨z, hzW, hzx⟩ := hnefib
    set S : Set (ι → K) := A.sweep (W a₀) with hSdef
    have hSY : S ⊆ Y := by
      rintro _ ⟨g, hg, w, hw, rfl⟩
      exact hstable g hg w (hWY a₀ hw)
    have hSst : ∀ g ∈ A.G, ∀ y ∈ S, A.act g y ∈ S := fun g hg y hy =>
      A.orbit_subset_sweep (fun w hw => hYS (hWY a₀ hw)) hy ⟨g, hg, rfl⟩
    have hWS : W a₀ ⊆ S := A.subset_sweep (fun w hw => hYS (hWY a₀ hw))
    have hSp : (MvPolynomial.vanishingIdeal K S).IsPrime := A.irreducible_sweep (hWp a₀)
    have hCp : (MvPolynomial.vanishingIdeal K (zclosure S)).IsPrime := by
      rw [vanishingIdeal_zclosure]; exact hSp
    have hdense : MvPolynomial.vanishingIdeal K S
        = MvPolynomial.vanishingIdeal K (zclosure S) := (vanishingIdeal_zclosure S).symm
    have hzS : z ∈ S := hWS hzW
    have hfSX : f '' S = X := by
      refine le_antisymm ?_ ?_
      · rw [← hXY]; exact Set.image_mono hSY
      · intro x hx
        obtain ⟨g, hg, rfl⟩ := htrans x hx
        refine ⟨A.act g z, hSst g hg z hzS, ?_⟩
        rw [hequiv g hg z (hSY hzS)]
        rw [Set.mem_preimage, Set.mem_singleton_iff] at hzx
        rw [hzx]
    have hfCdim : affineDim (f '' zclosure S) = affineDim X := by
      refine le_antisymm ?_ ?_
      · calc affineDim (f '' zclosure S)
            ≤ affineDim (zclosure (f '' S)) :=
              affineDim_mono (image_zclosure_subset hf S)
          _ = affineDim (f '' S) := affineDim_zclosure _
          _ = affineDim X := by rw [hfSX]
      · rw [← hfSX]
        exact affineDim_mono (Set.image_mono (subset_zclosure S))
    obtain ⟨x, hxmem, hD3⟩ :=
      exists_generic_fibre_dense hf hCp (zclosure_zclosure S) (subset_zclosure S) hdense
    have hxX : x ∈ X := hfSX ▸ hxmem
    obtain ⟨g, hg, hgx⟩ := htrans x hxX
    have hdle : (d : WithBot ℕ∞) ≤ affineDim (zclosure S ∩ f ⁻¹' {x}) := by
      have h1 : affineDim (S ∩ f ⁻¹' {x}) = affineDim (S ∩ f ⁻¹' {x₀}) := by
        rw [← hgx]
        exact htransdim S hSY hSst g hg
      calc (d : WithBot ℕ∞) = affineDim (W a₀ ∩ f ⁻¹' {x₀}) := hdi₀.symm
        _ ≤ affineDim (S ∩ f ⁻¹' {x₀}) :=
            affineDim_mono (Set.inter_subset_inter_left _ hWS)
        _ = affineDim (S ∩ f ⁻¹' {x}) := h1.symm
        _ ≤ affineDim (zclosure S ∩ f ⁻¹' {x}) :=
            affineDim_mono (Set.inter_subset_inter_left _ (subset_zclosure S))
    calc affineDim X + (d : WithBot ℕ∞)
        = (d : WithBot ℕ∞) + affineDim (f '' zclosure S) := by rw [hfCdim, add_comm]
      _ ≤ affineDim (zclosure S ∩ f ⁻¹' {x}) + affineDim (f '' zclosure S) :=
          add_le_add hdle le_rfl
      _ ≤ affineDim (zclosure S) := hD3
      _ = affineDim S := affineDim_zclosure S
      _ ≤ affineDim Y := affineDim_mono hSY

section Matrices

variable {μ : Type v} [Fintype μ] [DecidableEq μ]

end Matrices

end Height.Geometry
