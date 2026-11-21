import Mathlib.RingTheory.CohenMacaulay.Catenary
import Mathlib.RingTheory.CohenMacaulay.Polynomial
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.Jacobson.Ring

/-!
# The dimension formula in a polynomial ring over a field

For an ideal `I ≠ ⊤` of `MvPolynomial ι K` (`K` a field, `ι` finite),

```
I.height + ringKrullDim (MvPolynomial ι K ⧸ I) = Nat.card ι.
```

The Cohen–Macaulay stack in the pinned mathlib supplies the *local* form
(`Ideal.height_add_ringKrullDim_quotient_eq_ringKrullDim_of_isPrime`, valid in
any Cohen–Macaulay local ring); what is proved here is the globalisation, in
four steps.

1. `isCohenMacaulayLocalRing_of_field`, `isCohenMacaulayRing_mvPolynomial`: a
   field is Cohen–Macaulay because its Krull dimension is `0`, hence so is
   `MvPolynomial ι K` by `MvPolynomial.isCM_of_isCM_of_finite`.
2. `height_of_isMaximal`: **every** maximal ideal of `MvPolynomial ι K` has
   height `Nat.card ι`.  This is the equidimensionality input that
   Cohen–Macaulayness alone does not give; the proof is the induction
   `Finite.induction_empty_option` on `ι`, whose step is
   `Polynomial.height_eq_height_add_one` together with the fact that the
   contraction of a maximal ideal of `R[X]` to a Jacobson ring `R` is maximal
   (`Polynomial.isMaximal_comap_C_of_isJacobsonRing`, applicable since
   `MvPolynomial.isJacobsonRing`).
3. `ringKrullDim_quotient_eq_coheight`: for a prime `P`, `ringKrullDim (R ⧸ P)`
   is the order-theoretic coheight of `P` in `PrimeSpectrum R`, since the
   zero locus of `P` is the up-set of `P`.
4. `mvPolynomial_height_add_ringKrullDim_quotient_of_isPrime`: the formula for
   a prime `P`.  `≤` is `Order.krullDim_eq_iSup_height_add_coheight_of_nonempty`
   applied to `PrimeSpectrum (MvPolynomial ι K)`, whose Krull dimension is
   `Nat.card ι`.  `≥` localises at a maximal ideal `m ⊇ P`: the local ring is
   Cohen–Macaulay of dimension `height m = Nat.card ι` by step 2, the local
   formula applies to `P R_m`, whose height is `height P`, and the coheight of
   `P R_m` is at most that of `P` because `PrimeSpectrum.comap` of a
   localisation map is a strictly monotone map sending `P R_m` to `P`.

The general case then follows from the prime case exactly as the local
statement does in mathlib: decompose along the (finitely many) minimal primes
with `Ideal.height_eq_inf_minimalPrimes` and
`ringKrullDim_quotient_eq_iSup_quotient_minimalPrimes`, and note that an
infimum plus a supremum of two families with constant sum is that constant.

The coheight dictionary of step 3 also gives, over an arbitrary ring, the two
statements `eq_bot_of_ringKrullDim_quotient_eq` (in a domain of finite Krull
dimension `d`, a prime whose quotient still has dimension `d` is `⊥`) and
`injective_of_ringKrullDim_eq` (a surjection of domains of the same finite
Krull dimension is injective), which need only the inequality
`height + coheight ≤ krullDim` and no Cohen–Macaulay hypothesis.
-/

universe u v

namespace Height.Geometry

/-! ### A field, and hence a polynomial ring over it, is Cohen–Macaulay -/

/-- A field is a Cohen–Macaulay local ring: its Krull dimension is `0`, which
is at most its depth. -/
theorem isCohenMacaulayLocalRing_of_field (K : Type*) [Field K] :
    IsCohenMacaulayLocalRing K :=
  isCohenMacaulayLocalRing_of_ringKrullDim_le_depth K
    (by rw [ringKrullDim_eq_zero_of_field]; exact_mod_cast (zero_le : (0 : ℕ∞) ≤ _))

/-- A polynomial ring in finitely many variables over a field is a
Cohen–Macaulay ring. -/
theorem isCohenMacaulayRing_mvPolynomial (K : Type u) [Field K] (ι : Type v) [Finite ι] :
    IsCohenMacaulayRing (MvPolynomial ι K) :=
  haveI := isCohenMacaulayLocalRing_of_field K
  haveI := IsCohenMacaulayRing.of_isCohenMacaulayLocalRing K
  MvPolynomial.isCM_of_isCM_of_finite K ι

/-! ### Every maximal ideal of a polynomial ring over a field has height `#ι` -/

/-- Equidimensionality of `MvPolynomial ι K`: every maximal ideal has height
`Nat.card ι`.  Induction on `ι` through `Finite.induction_empty_option`; the
inductive step is `Polynomial.height_eq_height_add_one` applied to a maximal
ideal of `(MvPolynomial α K)[X]`, whose contraction to `MvPolynomial α K` is
maximal because that ring is Jacobson. -/
theorem height_of_isMaximal (K : Type u) [Field K] (ι : Type v) [Finite ι] :
    ∀ (m : Ideal (MvPolynomial ι K)), m.IsMaximal → m.height = (Nat.card ι : ℕ∞) := by
  induction ι using Finite.induction_empty_option with
  | of_equiv e ih =>
      rename_i α β
      intro m hm
      have := hm
      let f : MvPolynomial α K ≃+* MvPolynomial β K := (MvPolynomial.renameEquiv K e).toRingEquiv
      have h1 : (Ideal.comap f m).IsMaximal := Ideal.comap_isMaximal_of_equiv f
      have h2 := ih (Ideal.comap f m) h1
      rw [RingEquiv.height_comap] at h2
      rw [h2, Nat.card_congr e]
  | h_empty =>
      intro m hm
      have := hm
      have hle : (m.height : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial PEmpty.{v + 1} K) :=
        Ideal.height_le_ringKrullDim_of_ne_top hm.ne_top
      rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field] at hle
      simp only [Nat.card_of_isEmpty, Nat.cast_zero, add_zero] at hle ⊢
      exact le_antisymm (by exact_mod_cast hle) zero_le
  | h_option ih =>
      rename_i α _
      intro m hm
      have := hm
      let e : MvPolynomial (Option α) K ≃+* Polynomial (MvPolynomial α K) :=
        (MvPolynomial.optionEquivLeft K α).toRingEquiv
      set M : Ideal (Polynomial (MvPolynomial α K)) := Ideal.map e m with hMdef
      have : M.IsMaximal := Ideal.map_isMaximal_of_equiv e
      have h1 : M.height = m.height := RingEquiv.height_map e m
      have hu : (Ideal.under (MvPolynomial α K) M).IsMaximal := by
        have := Polynomial.isMaximal_comap_C_of_isJacobsonRing (R := MvPolynomial α K) M
        simpa [Ideal.under_def, Polynomial.algebraMap_eq] using this
      have h2 : M.height = (Ideal.under (MvPolynomial α K) M).height + 1 :=
        Polynomial.height_eq_height_add_one _ M
      rw [← h1, h2, ih _ hu, Finite.card_option]
      push_cast
      ring

/-! ### The dimension of a quotient by a prime is a coheight -/

/-- For a prime `P`, the Krull dimension of `R ⧸ P` is the coheight of `P` as a
point of `PrimeSpectrum R`: the zero locus of `P` is the up-set of `P`. -/
theorem ringKrullDim_quotient_eq_coheight {R : Type*} [CommRing R] (P : Ideal R) [hP : P.IsPrime] :
    ringKrullDim (R ⧸ P) = ((Order.coheight (⟨P, hP⟩ : PrimeSpectrum R) : ℕ∞) : WithBot ℕ∞) := by
  have hset : PrimeSpectrum.zeroLocus (R := R) (P : Set R)
      = Set.Ici (⟨P, hP⟩ : PrimeSpectrum R) := by
    ext q
    simp only [PrimeSpectrum.mem_zeroLocus, Set.mem_Ici, SetLike.coe_subset_coe]
    exact Iff.rfl
  rw [ringKrullDim_quotient, hset, Order.coheight_eq_krullDim_Ici]

/-! ### The dimension formula -/

/-- The dimension formula for a prime ideal of `MvPolynomial ι K`. -/
theorem mvPolynomial_height_add_ringKrullDim_quotient_of_isPrime
    (K : Type u) [Field K] (ι : Type v) [Finite ι]
    (P : Ideal (MvPolynomial ι K)) [hP : P.IsPrime] :
    (P.height : WithBot ℕ∞) + ringKrullDim (MvPolynomial ι K ⧸ P) = (Nat.card ι : WithBot ℕ∞) := by
  have hdim : ringKrullDim (MvPolynomial ι K) = (Nat.card ι : WithBot ℕ∞) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  have hdim' : Order.krullDim (PrimeSpectrum (MvPolynomial ι K))
      = ((Nat.card ι : ℕ) : WithBot ℕ∞) := hdim
  set x : PrimeSpectrum (MvPolynomial ι K) := ⟨P, hP⟩ with hx
  have hq : ringKrullDim (MvPolynomial ι K ⧸ P) = ((Order.coheight x : ℕ∞) : WithBot ℕ∞) :=
    ringKrullDim_quotient_eq_coheight P
  have hh : P.height = Order.height x := PrimeSpectrum.height_eq_orderHeight x
  have hle : Order.height x + Order.coheight x ≤ (Nat.card ι : ℕ∞) := by
    have h1 := Order.krullDim_eq_iSup_height_add_coheight_of_nonempty
      (α := PrimeSpectrum (MvPolynomial ι K))
    rw [hdim'] at h1
    have h2 : (⨆ a : PrimeSpectrum (MvPolynomial ι K), Order.height a + Order.coheight a)
        = (Nat.card ι : ℕ∞) := by exact_mod_cast h1.symm
    rw [← h2]
    exact le_iSup (fun a : PrimeSpectrum (MvPolynomial ι K) =>
      Order.height a + Order.coheight a) x
  have hge : (Nat.card ι : ℕ∞) ≤ Order.height x + Order.coheight x := by
    obtain ⟨m, hm, hPm⟩ := Ideal.exists_le_maximal P hP.ne_top
    have := hm
    have hcmA : IsCohenMacaulayLocalRing (Localization.AtPrime m) :=
      (isCohenMacaulayRing_def (MvPolynomial ι K)).mp
        (isCohenMacaulayRing_mvPolynomial K ι) m hm.isPrime
    have hnA : IsNoetherianRing (Localization.AtPrime m) :=
      IsLocalization.isNoetherianRing m.primeCompl _ inferInstance
    have hdisj : Disjoint (m.primeCompl : Set (MvPolynomial ι K)) (P : Set (MvPolynomial ι K)) :=
      Set.disjoint_left.mpr fun a ha hb => ha (hPm hb)
    have hPAp : (P.map (algebraMap (MvPolynomial ι K) (Localization.AtPrime m))).IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint m.primeCompl _ P hP hdisj
    have hPAht : (P.map (algebraMap (MvPolynomial ι K) (Localization.AtPrime m))).height
        = P.height := IsLocalization.height_map_of_disjoint m.primeCompl P hdisj
    have hAdim : ringKrullDim (Localization.AtPrime m) = (Nat.card ι : WithBot ℕ∞) := by
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height m (Localization.AtPrime m),
        height_of_isMaximal K ι m hm]
      simp
    have hcomap : PrimeSpectrum.comap (algebraMap (MvPolynomial ι K) (Localization.AtPrime m))
        ⟨_, hPAp⟩ = x := by
      apply PrimeSpectrum.ext
      exact IsLocalization.under_map_of_isPrime_disjoint m.primeCompl _ hP hdisj
    have hco : Order.coheight (⟨_, hPAp⟩ : PrimeSpectrum (Localization.AtPrime m))
        ≤ Order.coheight x := by
      have hinj := PrimeSpectrum.localization_comap_injective
        (Localization.AtPrime m) m.primeCompl
      have hmono : Monotone
          (PrimeSpectrum.comap (algebraMap (MvPolynomial ι K) (Localization.AtPrime m))) :=
        fun a b h => Ideal.comap_mono h
      have := Order.coheight_le_coheight_apply_of_strictMono _
        (hmono.strictMono_of_injective hinj) (⟨_, hPAp⟩ : PrimeSpectrum (Localization.AtPrime m))
      rwa [hcomap] at this
    have key2 := Ideal.height_add_ringKrullDim_quotient_eq_ringKrullDim_of_isPrime
      (R := Localization.AtPrime m)
      (P.map (algebraMap (MvPolynomial ι K) (Localization.AtPrime m)))
    rw [hAdim, hPAht, ringKrullDim_quotient_eq_coheight
      (P.map (algebraMap (MvPolynomial ι K) (Localization.AtPrime m))), ← WithBot.coe_add] at key2
    have key3 : P.height
        + Order.coheight (⟨_, hPAp⟩ : PrimeSpectrum (Localization.AtPrime m))
        = (Nat.card ι : ℕ∞) := by exact_mod_cast key2
    rw [← key3, hh]
    exact add_le_add le_rfl hco
  rw [hq, hh, ← WithBot.coe_add, le_antisymm hle hge]
  simp

/-- The dimension formula for polynomial rings over a field, with `K` and
`ι` explicit. -/
theorem mvPolynomial_height_add_ringKrullDim_quotient
    (K : Type u) [Field K] (ι : Type v) [Finite ι]
    (I : Ideal (MvPolynomial ι K)) (hI : I ≠ ⊤) :
    (I.height : WithBot ℕ∞) + ringKrullDim (MvPolynomial ι K ⧸ I) = (Nat.card ι : WithBot ℕ∞) := by
  have : Nontrivial (MvPolynomial ι K ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  rw [Ideal.height_eq_inf_minimalPrimes, ringKrullDim_quotient_eq_iSup_quotient_minimalPrimes,
    iSup_subtype', iInf_subtype']
  have fin : Finite (Subtype (Membership.mem I.minimalPrimes)) :=
    Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial ι K) I
  have non : Nonempty (Subtype (Membership.mem I.minimalPrimes)) :=
    Ideal.nonempty_minimalPrimes hI
  apply le_antisymm
  · obtain ⟨p, hp⟩ := exists_eq_ciSup_of_finite
      (f := fun x : Subtype (Membership.mem I.minimalPrimes) =>
        ringKrullDim (MvPolynomial ι K ⧸ x.1))
    have := p.2.isPrime
    rw [← hp, ← mvPolynomial_height_add_ringKrullDim_quotient_of_isPrime K ι p.1]
    exact add_le_add (WithBot.coe_le_coe.mpr (iInf_le_iff.mpr fun b a => a p)) le_rfl
  · obtain ⟨p, hp⟩ := exists_eq_ciInf_of_finite
      (f := fun x : Subtype (Membership.mem I.minimalPrimes) => x.1.height)
    have := p.2.isPrime
    rw [← hp, ← mvPolynomial_height_add_ringKrullDim_quotient_of_isPrime K ι p.1]
    exact add_le_add le_rfl (le_iSup_iff.mpr fun b a => a p)

/-- **The dimension of `K[ι] ⧸ P` is a natural number, and its codimension is its
complement**: both are read off the dimension formula, the height of `P` being finite. -/
theorem exists_ringKrullDim_quotient_eq (K : Type u) [Field K] (ι : Type v) [Finite ι]
    (P : Ideal (MvPolynomial ι K)) [hP : P.IsPrime] :
    ∃ c d : ℕ, c + d = Nat.card ι ∧ P.height = (c : ℕ∞) ∧
      ringKrullDim (MvPolynomial ι K ⧸ P) = (d : WithBot ℕ∞) := by
  have hb := mvPolynomial_height_add_ringKrullDim_quotient_of_isPrime K ι P
  have _ : Nontrivial (MvPolynomial ι K ⧸ P) := Ideal.Quotient.nontrivial_iff.mpr hP.ne_top
  have hbot : ringKrullDim (MvPolynomial ι K ⧸ P) ≠ ⊥ := by
    rw [Ne, ringKrullDim_eq_bot_iff_subsingleton]
    exact not_subsingleton _
  obtain ⟨D, hD⟩ := WithBot.ne_bot_iff_exists.mp hbot
  have hc : (P.height.toNat : ℕ∞) = P.height := ENat.natCast_toNat (Ideal.height_ne_top hP.ne_top)
  rw [← hD, ← hc, ← WithBot.coe_add] at hb
  have hb' : (P.height.toNat : ℕ∞) + D = (Nat.card ι : ℕ∞) := by exact_mod_cast hb
  have hDtop : D ≠ ⊤ := by
    intro h
    rw [h, add_top] at hb'
    exact (ENat.natCast_ne_top (Nat.card ι)) hb'.symm
  refine ⟨P.height.toNat, D.toNat, ?_, hc.symm, ?_⟩
  · have h : (P.height.toNat : ℕ∞) + (D.toNat : ℕ∞) = (Nat.card ι : ℕ∞) := by
      rw [ENat.natCast_toNat hDtop]; exact hb'
    exact_mod_cast h
  · rw [← hD]
    exact congrArg _ (ENat.natCast_toNat hDtop).symm

/-! ### Full-dimensional quotients of a domain -/

/-- **A prime with a full-dimensional quotient is `⊥`.**  In a domain `B` of finite Krull
dimension `d`, a prime `q` with `dim (B ⧸ q) = d` is the zero ideal: the height of `q` and the
dimension of `B ⧸ q` are the height and the coheight of the corresponding point of
`PrimeSpectrum B` (`ringKrullDim_quotient_eq_coheight`), whose sum is at most `krullDim`
(`Order.krullDim_eq_iSup_height_add_coheight_of_nonempty`), so `q` has height `0` and is a
minimal point of the spectrum; in a domain `⊥` is prime, hence `q = ⊥`. -/
theorem eq_bot_of_ringKrullDim_quotient_eq {B : Type*} [CommRing B] [IsDomain B] {d : ℕ}
    (hB : ringKrullDim B = (d : WithBot ℕ∞)) (q : Ideal B) [hq : q.IsPrime]
    (hq' : ringKrullDim (B ⧸ q) = (d : WithBot ℕ∞)) : q = ⊥ := by
  have _ : Nonempty (PrimeSpectrum B) := ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
  set y : PrimeSpectrum B := ⟨q, hq⟩ with hy
  have hco : ((Order.coheight y : ℕ∞) : WithBot ℕ∞) = ((d : ℕ∞) : WithBot ℕ∞) := by
    rw [← ringKrullDim_quotient_eq_coheight q]
    exact_mod_cast hq'
  have hco' : Order.coheight y = (d : ℕ∞) := by exact_mod_cast hco
  have hdim' : Order.krullDim (PrimeSpectrum B) = ((d : ℕ) : WithBot ℕ∞) := hB
  have hle : Order.height y + Order.coheight y ≤ (d : ℕ∞) := by
    have h1 := Order.krullDim_eq_iSup_height_add_coheight_of_nonempty (α := PrimeSpectrum B)
    rw [hdim'] at h1
    have h2 : (⨆ a : PrimeSpectrum B, Order.height a + Order.coheight a) = (d : ℕ∞) := by
      exact_mod_cast h1.symm
    rw [← h2]
    exact le_iSup (fun a : PrimeSpectrum B => Order.height a + Order.coheight a) y
  rw [hco'] at hle
  have hh : Order.height y = 0 := by
    have h3 : Order.height y + (d : ℕ∞) ≤ 0 + (d : ℕ∞) := by rw [zero_add]; exact hle
    exact le_antisymm ((ENat.add_le_add_iff_right (by simp)).mp h3) zero_le
  have hmin : IsMin y := Order.height_eq_zero.mp hh
  have hbot : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum B) ≤ y := bot_le
  exact le_antisymm (hmin hbot) bot_le

/-- A nontrivial ring whose dimension is a natural number `n` minus a natural number `c` has
that difference as its dimension; stated in the form `dim B + c = n` in which the dimension
formulas produce it. -/
theorem ringKrullDim_eq_of_add_eq {B : Type*} [CommRing B] [Nontrivial B] {c n : ℕ}
    (hB : ringKrullDim B + (c : WithBot ℕ∞) = (n : WithBot ℕ∞)) :
    ringKrullDim B = ((n - c : ℕ) : WithBot ℕ∞) := by
  have hbot : ringKrullDim B ≠ ⊥ := by
    rw [Ne, ringKrullDim_eq_bot_iff_subsingleton]
    exact not_subsingleton _
  obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.mp hbot
  rw [← hm] at hB ⊢
  have h1 : m + (c : ℕ∞) = (n : ℕ∞) := by exact_mod_cast hB
  have hmt : m ≠ ⊤ := by
    intro h
    rw [h, top_add] at h1
    exact (ENat.natCast_ne_top n) h1.symm
  obtain ⟨k, rfl⟩ := ENat.ne_top_iff_exists.mp hmt
  have h2 : k + c = n := by exact_mod_cast h1
  rw [show n - c = k by omega]
  norm_cast

/-- **A surjection of domains of the same finite Krull dimension is injective**: its kernel is
a prime with a full-dimensional quotient (`eq_bot_of_ringKrullDim_quotient_eq`). -/
theorem injective_of_ringKrullDim_eq {B C : Type*} [CommRing B] [IsDomain B] [CommRing C]
    [IsDomain C] {d : ℕ} (hB : ringKrullDim B = (d : WithBot ℕ∞))
    (hC : ringKrullDim C = (d : WithBot ℕ∞)) (g : B →+* C) (hg : Function.Surjective g) :
    Function.Injective g := by
  have hq : (RingHom.ker g).IsPrime := RingHom.ker_isPrime g
  have hq' : ringKrullDim (B ⧸ RingHom.ker g) = (d : WithBot ℕ∞) :=
    (ringKrullDim_eq_of_ringEquiv (g.quotientKerEquivOfSurjective hg)).trans hC
  rw [RingHom.injective_iff_ker_eq_bot]
  exact eq_bot_of_ringKrullDim_quotient_eq hB (RingHom.ker g) hq'

end Height.Geometry
