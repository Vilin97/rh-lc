module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationBoundOfPrimePowDvdMuPowAcris
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.AcrisMuBound

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_bound_of_primePow_dvd_mu_pow_acris :
    ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ ε : OCb l, IsEps ε →
      ∀ (j n : ℕ) (x : ℤ_[l]), x ≠ 0 →
        (l : Per.Acris l) ^ n ∣ algebraMap (Ainf l) (Per.Acris l)
          (muOf ε ^ j * algebraMap ℤ_[l] (Ainf l) x) →
        (l - 1) * n ≤ (l - 1) * x.valuation + 2 * j := by
  intro l hl hl2 ε hε j n x hx h
  have exists_of_dvd {n : ℕ} {y : Ainf l}
      (h : (l : Per.Acris l) ^ n ∣ algebraMap (Ainf l) (Per.Acris l) y) :
      ∃ z ∈ Per.Acris0 l, (l : Per.AinfP l) ^ n * z = algebraMap (Per.Ainf l) (Per.AinfP l) y := by
    obtain ⟨w, hw⟩ := h
    obtain ⟨e, he⟩ := GlobalTheory.AdicMaps.exists_acris_completion l
    have hw' := congrArg e hw
    rw [GlobalTheory.RingIface.tower l y, he, map_mul, map_pow, map_natCast] at hw'
    have h1 := congrArg (AdicCompletion.evalₐ (Ideal.span {(l : Per.Acris0 l)}) n) hw'
    rw [map_mul, map_pow, map_natCast] at h1
    have h0 : ((l : Per.Acris0 l ⧸ Ideal.span {(l : Per.Acris0 l)} ^ n)) ^ n = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk _), ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) n
    have h2 : algebraMap (Per.Ainf l) (Per.Acris0 l) y ∈ Ideal.span {(l : Per.Acris0 l)} ^ n := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      change AdicCompletion.evalₐ _ n (AdicCompletion.of (Ideal.span {(l : Per.Acris0 l)}) _
        (algebraMap (Per.Ainf l) (Per.Acris0 l) y)) = _ at h1
      rw [h0, zero_mul, AdicCompletion.evalₐ_of] at h1
      exact h1
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h2
    obtain ⟨z, hz⟩ := h2
    refine ⟨z, z.2, ?_⟩
    have := congrArg Subtype.val hz
    simpa [mul_comm] using this
  have pow_dvd_cc (hl2 : 2 ≤ l) {ϖ : OCb l} (hϖ : ϖ.untilt = (l : Per.OC l)) {n : ℕ} {y : Ainf l}
      (h : (l : Per.Acris l) ^ n ∣ algebraMap (Ainf l) (Per.Acris l) y) :
      ϖ ^ ((l - 1) * n) ∣ WittVector.constantCoeff y := by
    obtain ⟨z, hz0, hz⟩ := exists_of_dvd h
    obtain ⟨m, a, ha, hza⟩ := acris0_le hl2 hϖ hz0
    have hinj : Function.Injective (algebraMap (Per.Ainf l) (Per.AinfP l)) :=
      IsLocalization.injective (Per.AinfP l) (powers_le_nonZeroDivisors_of_noZeroDivisors l_ne_zero_ainf)
    have h1 : (l : Ainf l) ^ m * y = (l : Ainf l) ^ n * a := by
      apply hinj
      rw [map_mul, map_mul, map_pow, map_pow, map_natCast, ← hz, ← hza]
      ring
    have h2 : y ∈ Iw ϖ ^ n := by
      refine mem_of_l_pow_mul (ne_zero_of_untilt hϖ) m n ?_
      rw [h1, pow_add]
      exact Ideal.mul_mem_mul (Ideal.pow_mem_pow (l_mem_Iw ϖ) n) ha
    have h3 := Ideal.mem_map_of_mem (WittVector.constantCoeff (p := l) (R := OCb l)) h2
    have h4 : Ideal.map (WittVector.constantCoeff (p := l) (R := OCb l)) (Iw ϖ) ≤ Ideal.span {ϖ ^ (l - 1)} := by
      rw [Ideal.map_sup, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton,
        cc_natCast_l, map_pow, cc_teich, Ideal.span_singleton_eq_bot.2 rfl, bot_sup_eq]
    rw [Ideal.map_pow] at h3
    have h5 := Ideal.pow_right_mono h4 n h3
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, ← pow_mul] at h5
    exact h5
  have hl2' : 2 ≤ l := hl.out.two_le
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.MemLoc.FundOnto.untilt_surjective l (l : Per.OC l)
  set u := PadicInt.unitCoeff hx
  set v := x.valuation
  have hxu : algebraMap ℤ_[l] (Ainf l) x = (l : Ainf l) ^ v * algebraMap ℤ_[l] (Ainf l) (u : ℤ_[l]) := by
    conv_lhs => rw [PadicInt.unitCoeff_spec hx]
    rw [map_mul, map_pow, map_natCast, mul_comm]
  set y := muOf ε ^ j * algebraMap ℤ_[l] (Ainf l) (u : ℤ_[l])
  rcases le_or_gt n v with hnv | hnv
  · have := Nat.mul_le_mul_left (l - 1) hnv
    omega
  obtain ⟨n', rfl⟩ := Nat.exists_eq_add_of_le hnv.le
  have h2 : (l : Per.Acris l) ^ n' ∣ algebraMap (Ainf l) (Per.Acris l) y := by
    obtain ⟨w, hw⟩ := h
    refine ⟨w, ?_⟩
    have h3 : ((l ^ v : ℕ) : Per.Acris l) *
        (algebraMap (Ainf l) (Per.Acris l) y - (l : Per.Acris l) ^ n' * w) = 0 := by
      rw [hxu, mul_left_comm, map_mul, map_pow, map_natCast] at hw
      push_cast
      rw [mul_sub, hw]
      ring
    exact sub_eq_zero.1 (acris_nat_cancel (pow_ne_zero _ hl.out.ne_zero) h3)
  have h4 := pow_dvd_cc hl2' hϖ h2
  have h5 : WittVector.constantCoeff y = (ε - 1) ^ j * WittVector.constantCoeff (algebraMap ℤ_[l] (Ainf l) (u : ℤ_[l])) := by
    simp only [y, muOf, map_mul, map_pow, map_sub, map_one, cc_teich]
  have hu : IsUnit (WittVector.constantCoeff (algebraMap ℤ_[l] (Ainf l) (u : ℤ_[l]))) :=
    (u.isUnit.map _).map _
  rw [h5, hu.dvd_mul_right] at h4
  have h6 := tilt_bound hl2 hε hϖ h4
  have h7 : l ≤ 2 * (l - 1) := by omega
  have h8 : (l - 1) * ((l - 1) * n') ≤ (l - 1) * (2 * j) := by
    calc (l - 1) * ((l - 1) * n') ≤ l * j := h6
      _ ≤ 2 * (l - 1) * j := Nat.mul_le_mul_right j h7
      _ = (l - 1) * (2 * j) := by ring
  have h9 := Nat.le_of_mul_le_mul_left h8 (by omega)
  rw [mul_add]
  omega
