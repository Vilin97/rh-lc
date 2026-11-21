module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationBoundOfPrimePowDvdMuPowAcris
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.CrystallinePeriods.CrisLoc
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.AcrisMonBound

variable {l : ℕ} [hl : Fact l.Prime]

theorem exists_pow_bound {ϖ : OCb l} (hϖ : ϖ.untilt = (l : Per.OC l)) {c : OCb l} (hc : c ≠ 0) :
    ∃ K : ℕ, ∀ k : ℕ, ϖ ^ k ∣ c → k < K := by
  set a := ‖((c.untilt : Per.OC l) : ℂ_[l])‖
  set b := ‖((l : ℕ) : ℂ_[l])‖
  have ha : 0 < a := by
    refine norm_pos_iff.2 fun h => hc (GlobalTheory.TiltAbs.eq_zero_of_untilt c ?_)
    exact Subtype.ext (by simpa using h)
  have hb1 : b < 1 := GlobalTheory.RingBasics.norm_p_lt
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one ha hb1
  refine ⟨K, fun k hk => ?_⟩
  by_contra hkK
  obtain ⟨d, hd⟩ := map_dvd (PreTilt.untilt (O := Per.OC l) (p := l)) hk
  rw [map_pow, hϖ] at hd
  have h1 := congrArg (fun z : Per.OC l => ‖(z : ℂ_[l])‖) hd
  push_cast at h1
  rw [norm_mul, norm_pow] at h1
  have h2 : a ≤ b ^ k := by
    change ‖((c.untilt : Per.OC l) : ℂ_[l])‖ ≤ _
    rw [h1]
    exact mul_le_of_le_one_right (pow_nonneg (norm_nonneg _) _) (GlobalTheory.TiltAbs.norm_le_one d)
  have h3 : b ^ k ≤ b ^ K := pow_le_pow_of_le_one (norm_nonneg _) hb1.le (not_lt.1 hkK)
  linarith

end GlobalTheory.AcrisMonBound

namespace GlobalTheory.AcrisMonBound

open GlobalTheory.AcrisMuBound in
theorem main : ∀ (l : ℕ) [Fact l.Prime] (y : Ainf l), WittVector.constantCoeff y ≠ 0 →
    ∃ C : ℕ, ∀ (z : ℤ_[l]) (N : ℕ), z ≠ 0 →
      (l : Per.Acris l) ^ N ∣ algebraMap (Ainf l) (Per.Acris l) y *
        algebraMap ℤ_[l] (Per.Acris l) z → N ≤ z.valuation + C := by
  intro l hl y hy
  have hl2 : 2 ≤ l := hl.out.two_le
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.MemLoc.FundOnto.untilt_surjective l (l : Per.OC l)
  obtain ⟨K, hK⟩ := exists_pow_bound hϖ hy
  refine ⟨K, fun z N hz h => ?_⟩
  set u := PadicInt.unitCoeff hz
  set v := z.valuation
  rcases le_or_gt N v with hNv | hNv
  · omega
  obtain ⟨n', rfl⟩ := Nat.exists_eq_add_of_le hNv.le
  set y' := y * algebraMap ℤ_[l] (Ainf l) (u : ℤ_[l])
  have hza : algebraMap ℤ_[l] (Per.Acris l) z =
      (l : Per.Acris l) ^ v * algebraMap ℤ_[l] (Per.Acris l) (u : ℤ_[l]) := by
    conv_lhs => rw [PadicInt.unitCoeff_spec hz]
    rw [map_mul, map_pow, map_natCast, mul_comm]
  have hy' : algebraMap (Ainf l) (Per.Acris l) y' =
      algebraMap (Ainf l) (Per.Acris l) y * algebraMap ℤ_[l] (Per.Acris l) (u : ℤ_[l]) := by
    simp only [y', map_mul]
    congr 1
  have h2 : (l : Per.Acris l) ^ n' ∣ algebraMap (Ainf l) (Per.Acris l) y' := by
    obtain ⟨w, hw⟩ := h
    refine ⟨w, ?_⟩
    have h3 : ((l ^ v : ℕ) : Per.Acris l) *
        (algebraMap (Ainf l) (Per.Acris l) y' - (l : Per.Acris l) ^ n' * w) = 0 := by
      rw [hza] at hw
      rw [hy']
      push_cast
      rw [mul_sub]
      linear_combination hw
    exact sub_eq_zero.1 (acris_nat_cancel (pow_ne_zero _ hl.out.ne_zero) h3)
  have h4 : ϖ ^ ((l - 1) * n') ∣ WittVector.constantCoeff y' := by
    have exists_divisor : ∃ b ∈ Per.Acris0 l,
        (l : Per.AinfP l) ^ n' * b = algebraMap (Per.Ainf l) (Per.AinfP l) y' := by
      obtain ⟨w, hw⟩ := h2
      obtain ⟨e, he⟩ := GlobalTheory.AdicMaps.exists_acris_completion l
      let I : Ideal (Per.Acris0 l) := Ideal.span {(l : Per.Acris0 l)}
      let f := (AdicCompletion.evalₐ I n').toRingHom.comp e.toRingHom
      have hp : f (l : Per.Acris l) ^ n' = 0 := by
        rw [map_natCast, ← map_natCast (Ideal.Quotient.mk (I ^ n')), ← map_pow,
          Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) _
      have hm := congrArg f hw
      simp only [map_mul f, map_pow f, hp, zero_mul] at hm
      have hmem : algebraMap (Per.Ainf l) (Per.Acris0 l) y' ∈ I ^ n' := by
        rw [GlobalTheory.RingIface.tower l y'] at hm
        change AdicCompletion.evalₐ I n' (e (algebraMap (Per.Acris0 l) (Per.Acris l)
          (algebraMap (Per.Ainf l) (Per.Acris0 l) y'))) = 0 at hm
        rw [he, AlgHom.commutes] at hm
        exact Ideal.Quotient.eq_zero_iff_mem.1 hm
      change _ ∈ Ideal.span {(l : Per.Acris0 l)} ^ n' at hmem
      rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmem
      obtain ⟨b, hb⟩ := hmem
      exact ⟨b, b.2, by simpa using (congrArg Subtype.val hb).symm⟩
    obtain ⟨b, hb, hby⟩ := exists_divisor
    obtain ⟨m, a, ha, hba⟩ := acris0_le hl2 hϖ hb
    have hinj : Function.Injective (algebraMap (Per.Ainf l) (Per.AinfP l)) :=
      IsLocalization.injective (Per.AinfP l)
        (powers_le_nonZeroDivisors_of_noZeroDivisors l_ne_zero_ainf)
    have heq : (l : Ainf l) ^ m * y' = (l : Ainf l) ^ n' * a := by
      apply hinj
      simp only [map_mul, map_pow, map_natCast]
      rw [← hby, ← hba]
      ring
    have hy_mem : y' ∈ Iw ϖ ^ n' := by
      refine mem_of_l_pow_mul (ne_zero_of_untilt hϖ) m n' ?_
      rw [heq, pow_add]
      exact Ideal.mul_mem_mul (Ideal.pow_mem_pow (l_mem_Iw ϖ) n') ha
    have himage := Ideal.mem_map_of_mem (WittVector.constantCoeff (p := l) (R := OCb l)) hy_mem
    have hspan : Ideal.map (WittVector.constantCoeff (p := l) (R := OCb l)) (Iw ϖ) ≤
        Ideal.span {ϖ ^ (l - 1)} := by
      rw [Ideal.map_sup, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton,
        cc_natCast_l, map_pow, cc_teich, Ideal.span_singleton_eq_bot.2 rfl, bot_sup_eq]
    rw [Ideal.map_pow] at himage
    have hpow := Ideal.pow_right_mono hspan n' himage
    rwa [Ideal.span_singleton_pow, Ideal.mem_span_singleton, ← pow_mul] at hpow
  have hu : IsUnit (WittVector.constantCoeff (algebraMap ℤ_[l] (Ainf l) (u : ℤ_[l]))) :=
    (u.isUnit.map _).map _
  rw [show y' = y * algebraMap ℤ_[l] (Ainf l) (u : ℤ_[l]) from rfl, map_mul, hu.dvd_mul_right] at h4
  have h5 := hK _ h4
  have h6 : n' ≤ (l - 1) * n' := Nat.le_mul_of_pos_left n' (by omega)
  omega

end GlobalTheory.AcrisMonBound
