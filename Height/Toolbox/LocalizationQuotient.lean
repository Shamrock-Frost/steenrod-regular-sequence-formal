import Height.Toolbox.LocalRing
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# The localisation of a quotient

For `I ≤ 𝔪` with `𝔪` prime, `R_𝔪 ⧸ I·R_𝔪` is the localisation of `R ⧸ I` at `𝔪 ⧸ I`
(`isLocalization_atPrime_quotient`, `quotientLocalizationEquiv`).  Mathlib has the instance
`IsLocalization (Algebra.algebraMapSubmonoid (R ⧸ I) M) (S ⧸ I·S)` for any localisation `S`
of `R` at `M`; all that is missing is that for `M = 𝔪.primeCompl` the image submonoid is the
prime complement of `𝔪 ⧸ I`, which is where `I ≤ 𝔪` is used.  Mathlib candidates.
-/


namespace Height.Toolbox

variable {R : Type*} [CommRing R] {I m : Ideal R}

theorem isPrime_map_mk [m.IsPrime] (hIm : I ≤ m) :
    (m.map (Ideal.Quotient.mk I)).IsPrime :=
  Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hIm)

theorem mem_map_mk_iff_of_le (hIm : I ≤ m) (r : R) :
    Ideal.Quotient.mk I r ∈ m.map (Ideal.Quotient.mk I) ↔ r ∈ m := by
  rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hIm]

theorem algebraMapSubmonoid_primeCompl_eq [m.IsPrime]
    [(m.map (Ideal.Quotient.mk I)).IsPrime] (hIm : I ≤ m) :
    Algebra.algebraMapSubmonoid (R ⧸ I) m.primeCompl
      = (m.map (Ideal.Quotient.mk I)).primeCompl := by
  ext y
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
  show (∃ s ∈ m.primeCompl, algebraMap R (R ⧸ I) s = Ideal.Quotient.mk I r) ↔
    Ideal.Quotient.mk I r ∉ m.map (Ideal.Quotient.mk I)
  rw [mem_map_mk_iff_of_le hIm]
  constructor
  · rintro ⟨s, hs, hsr⟩ hr
    have heq : Ideal.Quotient.mk I s = Ideal.Quotient.mk I r := hsr
    exact hs ((mem_map_mk_iff_of_le hIm s).mp (heq ▸ (mem_map_mk_iff_of_le hIm r).mpr hr))
  · intro hr
    exact ⟨r, hr, rfl⟩

theorem isLocalization_atPrime_quotient [m.IsPrime]
    [(m.map (Ideal.Quotient.mk I)).IsPrime] (hIm : I ≤ m) :
    IsLocalization.AtPrime
      (Localization.AtPrime m ⧸ I.map (algebraMap R (Localization.AtPrime m)))
      (m.map (Ideal.Quotient.mk I)) := by
  show IsLocalization ((m.map (Ideal.Quotient.mk I)).primeCompl) _
  rw [← algebraMapSubmonoid_primeCompl_eq hIm]
  infer_instance

/-- **The localisation of a quotient**: `R_𝔪 ⧸ I·R_𝔪` is the localisation of `R ⧸ I` at
`𝔪 ⧸ I`. -/
noncomputable def quotientLocalizationEquiv [m.IsPrime]
    [(m.map (Ideal.Quotient.mk I)).IsPrime] (hIm : I ≤ m) :
    Localization.AtPrime (m.map (Ideal.Quotient.mk I)) ≃+*
      (Localization.AtPrime m ⧸ I.map (algebraMap R (Localization.AtPrime m))) :=
  haveI := isLocalization_atPrime_quotient hIm
  (IsLocalization.algEquiv (m.map (Ideal.Quotient.mk I)).primeCompl
    (Localization.AtPrime (m.map (Ideal.Quotient.mk I)))
    (Localization.AtPrime m ⧸ I.map (algebraMap R (Localization.AtPrime m)))).toRingEquiv

end Height.Toolbox
