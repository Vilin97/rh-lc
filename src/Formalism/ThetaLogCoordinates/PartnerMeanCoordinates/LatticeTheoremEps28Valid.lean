module

public import Formalism.PolynomialDimension.ChainOrderLetters
public import Formalism.ThetaLogCoordinates.PartnerMeanCoordinates.TheoremMXB
public import Formalism.MahlerMeasure.CoarseLevelSlackInequalities
public import Formalism.MahlerMeasure.FinalD
public import Formalism.MahlerMeasure.MahlerMeasureProofs.BadCrit
public import Formalism.MahlerMeasure.MahlerMeasureProofs.GamDeg
public import Formalism.MahlerMeasure.MahlerMeasureProofs.GamLead
public import Formalism.PolynomialDimension.MultinomialDepth.MonoCount
public import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.GramBoundPosOfProjSat
import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.GramBoundUnconditionalOfSat
public import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.HighestVectorProjectionPos
public import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.RestrictedSaturationHolds
public import Formalism.ThetaLogCoordinates.PartnerMeanCoordinates.PartnerMeanProofs.GamIntC
public import Formalism.ThetaLogCoordinates.PartnerMeanCoordinates.PartnerMeanProofs.GammaZeroIntegral
public import Formalism.ThetaLogCoordinates.PartnerMeanCoordinates.PartnerMeanProofs.NatLogLeOfLe
public import Formalism.ThetaLogCoordinates.PartnerMeanCoordinates.TheoremMCB
public import Formalism.MahlerMeasure.MahlerMeasureProofs.TheoremM
public import Formalism.PolynomialDimension.MultinomialDepth.PartnerM
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Formalism.MahlerMeasure.MahlerMeasureProofs.WeightSpaceDimensionMonotone
import Formalism.PolynomialDimension.MultinomialDepth.TieOps
public import Formalism.ThetaLogCoordinates.PartnerMeanCoordinates.PartnerMeanProofs.TheoremMXBOfPoint
import Formalism.ThetaLogCoordinates.TraceIsometryWeights.DischargeHeightBound
import Formalism.ThetaLogCoordinates.TraceIsometryWeights.FinalP
import Mathlib.Algebra.Order.Star.Real
public import Formalism.MahlerMeasure.MahlerMeasureProofs.WeightSpaceDimensionMonotone

-- Source module: Formalism.ThetaLogCoordinates.PartnerMeanCoordinates.PartnerMeanProofs.PartnerConditionHolds

section

@[expose] public section

namespace Formalism.InvariantFactorPaths.MC

open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.DimensionMonotonicity Formalism.CountingSumsFrames Formalism.CountingSumsFrames.TO MvPolynomial Finset

theorem partner_condition_holds : YPartnerC := by
  intro p _ N r _ _ LL q J M ρ e1 hr hHP z hz hprim
  obtain ⟨hP1, hP2⟩ := hHP
  let Tj : Fin (N + 1) → Set (Fin r → ℤ) := fun j =>
    {la | ∀ k, min (J k) N = (j : ℕ) → ((la 0 : ℤ) : WithTop ℤ) ≤ M k}
  have hex : ∀ j : Fin (N + 1), ∃ P, IsTypeProj p LL j univ (Tj j) P ∧ (∀ F G, fock p (P F) G = fock p F (P G)) ∧
      ∀ F ∈ PolZ p r LL, ((p : ℚ_[p]) ^ e1) • P F ∈ IntPol p (Fin N × Fin r) :=
    fun j => hP1 j (Nat.lt_succ_iff.mp j.isLt) univ (Or.inl rfl) (Tj j)
      (fun la la' h => by rw [show la = la' from funext fun c => h c (mem_univ c)])
  choose P hPt hPsa hPint using hex
  have hPP : ∀ j x, P j (P j x) = P j x := fun j x => LinearMap.congr_fun (hPt j).1 x
  have hcomm : ∀ j j' x, P j (P j' x) = P j' (P j x) := by
    intro j j' x
    rcases le_total (j : ℕ) (j' : ℕ) with h | h
    · exact LinearMap.congr_fun (hP2 j j' univ univ (Tj j) (Tj j') (P j) (P j') h subset_rfl (Or.inl rfl)
        (Or.inl rfl) (hPt j) (hPt j')) x
    · exact (LinearMap.congr_fun (hP2 j' j univ univ (Tj j') (Tj j) (P j') (P j) h subset_rfl (Or.inl rfl)
        (Or.inl rfl) (hPt j') (hPt j)) x).symm
  have hPpol : ∀ j, ∀ x ∈ Pol p r LL, P j x ∈ Pol p r LL := fun j => typeProj_pol LL j (Tj j) (P j) (hPt j)

  have hfixY : ∀ j : Fin (N + 1), ∀ x ∈ Y p (r := r) LL J M, P j x = x := by
    intro j
    set S : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
      Pol p r LL ⊓ ⨅ (k : Fin q) (_ : min (J k) N = (j : ℕ)), YCond p (r := r) LL j (M k) with hSdef
    have hmemS : ∀ x, x ∈ S ↔ x ∈ Pol p r LL ∧ ∀ k, min (J k) N = (j : ℕ) → x ∈ YCond p (r := r) LL j (M k) := by
      intro x; simp only [hSdef, Submodule.mem_inf, Submodule.mem_iInf]
    have hfix := proj_fix LL j (Tj j) (P j) (hPt j) S inf_le_left
      (fun c d x hx => by
        rw [hmemS] at hx ⊢
        exact ⟨glAct_pol LL j c d x hx.1, fun k hk => ycond_glStable LL j (M k) c d x (hx.2 k hk)⟩)
      (fun x hx => by
        rw [hmemS] at hx ⊢
        exact ⟨hPpol j x hx.1, fun k hk => typeProj_ycond LL j (Tj j) (P j) (hPt j) (M k) x (hx.2 k hk)⟩)
      (fun h hh hh0 μ hμ => by
        rw [hmemS] at hh
        intro k hk
        have h1 := ycond_le_supp LL j (M k) (hh.2 k hk)
        obtain ⟨m, hm⟩ : ∃ m, m ∈ h.support := by
          by_contra hc; push Not at hc
          exact hh0 (MvPolynomial.support_eq_empty.mp (Finset.eq_empty_of_forall_notMem hc))
        rw [mem_restrictSupport_iff] at h1
        have h2 := h1 (Finset.mem_coe.mpr hm)
        have h3 := (Submodule.mem_inf.mp hμ).1
        rw [WtSpC, mem_restrictSupport_iff] at h3
        have h4 := h3 (Finset.mem_coe.mpr hm) 0 (Finset.mem_univ _)
        simp only [Set.mem_ofPred_eq] at h2
        rw [h4] at h2
        exact h2)
    intro x hx
    apply hfix
    rw [hmemS]
    refine ⟨(Submodule.mem_inf.mp hx).1, fun k hk => ?_⟩
    have := (Submodule.mem_iInf _).mp (Submodule.mem_inf.mp hx).2 k
    rw [ycond_min, hk] at this
    exact this

  have hranY : ∀ j : Fin (N + 1), ∀ u, P j u = u → ∀ k, min (J k) N = (j : ℕ) →
      u ∈ YCond p (r := r) LL (J k) (M k) := by
    intro j u hu k hk
    rw [ycond_min, hk]
    have h1 : u ∈ LinearMap.range (P j) := ⟨u, hu⟩
    rw [(hPt j).2.1] at h1
    exact (iSup₂_le fun la hla => isoC_le_ycond LL j la (M k) (hla k hk)) h1

  obtain ⟨m0, hm0⟩ := prim_unit_coeff LL J M z hz hprim
  have hzY : z ∈ Y p (r := r) LL J M := (Submodule.mem_inf.mp hz).1
  have hzP : z ∈ Pol p r LL := (Submodule.mem_inf.mp (Submodule.mem_inf.mp hz).2).1
  have hm0mem : m0 ∈ z.support := by
    rw [mem_support_iff]; intro h; rw [h, norm_zero] at hm0; exact zero_ne_one hm0
  have hmd : MultiDeg LL m0 := by
    rw [Pol, mem_restrictSupport_iff] at hzP; exact hzP (Finset.mem_coe.mpr hm0mem)
  have hmonZ : (monomial m0 (1 : ℚ_[p])) ∈ PolZ p r LL := by
    classical
    refine Submodule.mem_inf.mpr ⟨?_, mem_intPol_of_norm _ fun m => ?_⟩
    · show monomial m0 (1 : ℚ_[p]) ∈ Pol p r LL
      rw [Pol, mem_restrictSupport_iff]
      intro m hm
      rw [Finset.mem_coe] at hm
      rw [Finset.mem_singleton.mp (support_monomial_subset hm)]
      exact hmd
    · rw [coeff_monomial]; split_ifs <;> simp
  set u := lcomp P (List.finRange (N + 1)) (monomial m0 (1 : ℚ_[p])) with hu
  have hufix : ∀ j, P j u = u := fun j => lcomp_fix P hPP hcomm _ j (List.mem_finRange j) _
  have hint := lcomp_int LL e1 P hPpol hPint (List.finRange (N + 1)) _ hmonZ
  rw [List.length_finRange] at hint
  refine ⟨((p : ℚ_[p]) ^ (e1 * (N + 1))) • u, ?_, ?_⟩
  · refine Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨(Submodule.mem_inf.mp hint).1, ?_⟩, hint⟩
    rw [Submodule.mem_iInf]
    intro k
    refine Submodule.smul_mem _ _ ?_
    exact hranY ⟨min (J k) N, by omega⟩ u (hufix _) k rfl
  ·
    rw [fockN_smul_right', norm_mul, norm_pow, Padic.norm_p]
    have hf : fockN p LL z u = fockN p LL z (monomial m0 1) := by
      unfold fockN
      rw [hu, lcomp_fock P hPsa z (fun j => hfixY j z hzY)]
    rw [hf]
    have hge := fockN_monomial_ge LL z m0 hmd hm0
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
    calc (p : ℝ) ^ (-((e1 * (N + 1) : ℕ) : ℤ)) = (p : ℝ)⁻¹ ^ (e1 * (N + 1)) * 1 := by
          rw [zpow_neg, zpow_natCast, inv_pow, mul_one]
      _ ≤ (p : ℝ)⁻¹ ^ (e1 * (N + 1)) * ‖fockN p LL z (monomial m0 1)‖ :=
          mul_le_mul_of_nonneg_left hge (by positivity)

end Formalism.InvariantFactorPaths.MC
end
end

-- Source module: Formalism.ThetaLogCoordinates.PartnerMeanCoordinates.PartnerMeanProofs.GramHypothesisOfLogBound

section

@[expose] public section

namespace Formalism.InvariantFactorPaths.MC

open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.CountingSumsFrames Formalism.InvariantFactorPaths.PW Formalism.InvariantFactorPaths.L4 MvPolynomial Finset

theorem meanGamX : MeanGamX :=
  Formalism.InvariantFactorPaths.MC.meanGamX_of
    Formalism.GM.gamma_degree_bound Formalism.GM.gamma_leading_term
    gamma_integral_holds Formalism.GM.Top.windowFullAP

theorem theoremMXB : TheoremMXB :=
  Formalism.InvariantFactorPaths.MC.theoremMXB_of_point meanGamX
    Formalism.GM.DimensionMonotonicity.highest_weight_dim_monotone
    Formalism.CountingSumsFrames.monomial_count Formalism.GM.Top.smithZp
    Formalism.GM.TM.existsAdaptedBasis
    (pointMX_of_partner Formalism.GM.bad_criterion_holds
      (partnerMX_of_parts tieOpsX_main partner_condition_holds))

theorem natLog_le_lgSeg (p : ℕ) [Fact p.Prime] (a : ℝ) (r x : ℕ) (ha : 0 ≤ a) (hr : 1 ≤ r)
    (hx : (x : ℝ) ≤ p * (8 * a + r)) : (Nat.log p x : ℝ) ≤ lgSeg p a r := by
  unfold lgSeg
  have hp : 1 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hy : (1 : ℝ) ≤ 8 * a + r := by linarith
  have hl : 0 ≤ Real.logb p (8 * a + r) := Real.logb_nonneg hp hy
  rcases Nat.eq_zero_or_pos x with hx0 | hx0
  · subst hx0
    simp only [Nat.log_zero_right, Nat.cast_zero]
    linarith
  · have h1 : ((p ^ Nat.log p x : ℕ) : ℝ) ≤ (x : ℝ) := by
      exact_mod_cast Nat.pow_log_le_self p hx0.ne'
    push_cast at h1
    have hpy : (0 : ℝ) < p * (8 * a + r) := mul_pos (by linarith) (by linarith)
    have h2 : (Nat.log p x : ℝ) ≤ Real.logb p (p * (8 * a + r)) := by
      rw [Real.le_logb_iff_rpow_le hp hpy, Real.rpow_natCast]
      linarith
    rw [Real.logb_mul (by positivity) (by linarith), Real.logb_self_eq_one hp] at h2
    linarith

theorem one_le_lgSeg (p : ℕ) [Fact p.Prime] (a : ℝ) (r : ℕ) (ha : 0 ≤ a) (hr : 1 ≤ r) : 1 ≤ lgSeg p a r := by
  unfold lgSeg
  have hp : 1 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hl : 0 ≤ Real.logb p (8 * a + r) := Real.logb_nonneg hp (by linarith)
  linarith

theorem natLog_floor_lgSeg (p : ℕ) [Fact p.Prime] (a : ℝ) (r : ℕ) (ha : 0 ≤ a) (hr : 1 ≤ r) :
    (Nat.log p ⌊8 * a + r⌋₊ : ℝ) + 1 ≤ lgSeg p a r := by
  unfold lgSeg
  have hp : 1 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hy : (1 : ℝ) ≤ 8 * a + r := by linarith
  have hfl : 1 ≤ ⌊8 * a + (r : ℝ)⌋₊ := Nat.le_floor (by rw [Nat.cast_one]; exact hy)
  have h3 : ((p ^ Nat.log p ⌊8 * a + (r : ℝ)⌋₊ : ℕ) : ℝ) ≤ (⌊8 * a + (r : ℝ)⌋₊ : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self p (by omega)
  have h4 := Nat.floor_le (by linarith : (0 : ℝ) ≤ 8 * a + r)
  push_cast at h3
  have h2 : (Nat.log p ⌊8 * a + (r : ℝ)⌋₊ : ℝ) ≤ Real.logb p (8 * a + r) := by
    rw [Real.le_logb_iff_rpow_le hp (by linarith), Real.rpow_natCast]
    linarith
  linarith

theorem choose_two_le (r : ℕ) : ((r.choose 2 : ℕ) : ℝ) ≤ (r : ℝ) ^ 2 / 2 := by
  have h : 2 * r.choose 2 ≤ r ^ 2 := by
    rw [Nat.choose_two_right]
    have h1 := Nat.div_mul_le_self (r * (r - 1)) 2
    have h2 : r * (r - 1) ≤ r ^ 2 := by
      rw [sq]; exact Nat.mul_le_mul_left r (Nat.sub_le r 1)
    calc 2 * (r * (r - 1) / 2) = r * (r - 1) / 2 * 2 := mul_comm _ _
      _ ≤ r * (r - 1) := h1
      _ ≤ r ^ 2 := h2
  have h' : (2 : ℝ) * (r.choose 2 : ℝ) ≤ (r : ℝ) ^ 2 := by exact_mod_cast h
  linarith

theorem gram_hypothesis_of_log_bound (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LLw : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (lgv κ4 : ℝ) (hr : 2 ≤ r) (hρ : (ρ : ℕ) = r - 1)
    (hv : LLw.vec (Fin.last K) = true) (h1 : (Nat.log p (LLw.total + r - 1) : ℝ) ≤ lgv)
    (h2 : (Nat.log p (4 * LLw.total + r - 1) : ℝ) ≤ lgv)
    (hκ : ((K : ℝ) + 7) * ((r : ℝ) ^ 2 / 2 * lgv) ≤ κ4) : GramDeterminantGradedHypothesis p LLw J M ρ κ4 := by
  have hc := choose_two_le r
  have hl1 : (0 : ℝ) ≤ (Nat.log p (LLw.total + r - 1) : ℝ) := Nat.cast_nonneg _
  have hl2 : (0 : ℝ) ≤ (Nat.log p (4 * LLw.total + r - 1) : ℝ) := Nat.cast_nonneg _
  have hlg : 0 ≤ lgv := hl1.trans h1
  have hQ : 0 ≤ (r : ℝ) ^ 2 / 2 * lgv := by positivity
  have g1 : ((kapC p r LLw.total : ℕ) : ℝ) ≤ (r : ℝ) ^ 2 / 2 * lgv := by
    unfold kapC
    rw [Nat.cast_mul]
    exact mul_le_mul hc h1 hl1 (by positivity)
  have g2 : ((r.choose 2 * Nat.log p (4 * LLw.total + r - 1) : ℕ) : ℝ) ≤ (r : ℝ) ^ 2 / 2 * lgv := by
    rw [Nat.cast_mul]
    exact mul_le_mul hc h2 hl2 (by positivity)
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · refine graded_bound_saturation_holds p 0 r LLw J M ρ (kapC p r LLw.total) 0 κ4 hr hρ hv (hypPE_setLast LLw ρ)
      (fun e _ => restricted_saturation_zero p r _ J _ ρ hr hρ hv) ?_
    rw [Nat.mul_zero, Nat.add_zero, Nat.cast_mul]
    push_cast at hκ ⊢
    nlinarith
  · refine graded_bound_pos_of_proj highest_vector_projection_holds p K r LLw J M ρ (kapC p r LLw.total)
      (2 * (r.choose 2 * Nat.log p (4 * LLw.total + r - 1))) κ4 hK hr hρ hv (hypPE_setLast LLw ρ) ?_ (le_trans ?_ hκ)
    · intro e _
      have ht' := setLast_total_le LLw (LLw.deg (Fin.last K) - e) (Nat.sub_le _ _)
      exact resSatL_mono _ J _ ρ
        (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.log_mono_right (by omega))))
        (restricted_saturation_holds p K r (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ hr hρ hv)
    · have h3 : ((K : ℝ) + 3) * ((kapC p r LLw.total : ℕ) : ℝ) ≤ ((K : ℝ) + 3) * ((r : ℝ) ^ 2 / 2 * lgv) :=
        mul_le_mul_of_nonneg_left g1 (by positivity)
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul (2 : ℕ), Nat.cast_mul (2 : ℕ)]
      push_cast at g2 h3 ⊢
      nlinarith

theorem deg_le_total' {N : ℕ} (LL : Letters N) (x : Fin N) : LL.deg x ≤ LL.total := by
  unfold Letters.total
  exact Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ x)

theorem theoremMV7Of : TheoremMV7Of := by
  unfold TheoremMV7Of
  intro p _ s r _ LL T a E Yl n₀ dd ρ hp2 hr hρ hadm hch hcond ha hE hY hS hsize hH
  have : NeZero (2 * s + 1) := ⟨by omega⟩
  have hr1 : 1 ≤ r := by omega
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hlg1 : 1 ≤ lgSeg p a r := one_le_lgSeg p a r (by linarith) hr1
  have hfl := natLog_floor_lgSeg p a r (by linarith) hr1
  have hpos : 0 ≤ (r : ℝ) ^ 2 * lgSeg p a r := mul_nonneg (sq_nonneg _) (by linarith)
  have hsR : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have hspos : 0 ≤ (s : ℝ) * ((r : ℝ) ^ 2 * lgSeg p a r) := mul_nonneg hsR hpos
  have hflo : ∀ m : ℕ, (m : ℝ) ≤ 8 * a + r → m ≤ ⌊8 * a + (r : ℝ)⌋₊ := fun m hm => Nat.le_floor hm
  obtain ⟨htot, hsz⟩ := hsize
  unfold epsSeg
  refine theoremMXB p (2 * s + 1) r LL T ⌊8 * a + (r : ℝ)⌋₊ E (kapSeg p a r s)
    (((s : ℝ) + 4) * ((r : ℝ) ^ 2 * lgSeg p a r)) (lgSeg p a r) ⌊(r : ℝ) ^ 2 * lgSeg p a r⌋₊
    Yl n₀ dd ρ hp2 hr hρ hadm hE hY hS ?_ ?_ ?_ hfl ?_ ?_ ?_ hH
  · intro x
    apply hflo
    have h1 := deg_le_total' (LL.setTies T fun i => n₀ i + dd i * (Yl i - 1)) x
    have h2 : ((LL.setTies T fun i => n₀ i + dd i * (Yl i - 1)).deg x : ℝ) ≤
        ((LL.setTies T fun i => n₀ i + dd i * (Yl i - 1)).total : ℝ) := by exact_mod_cast h1
    linarith
  · intro i
    obtain ⟨h1, h2, h3⟩ := hsz i
    refine ⟨?_, hflo _ h2, ?_⟩
    · apply hflo
      push_cast at h3 ⊢
      linarith
    · intro h
      apply hflo
      have hdA : degreeAtPosition (LL.setTies T fun i => n₀ i + dd i * (Yl i - 1)) (T.pos i) =
          (LL.setTies T fun i => n₀ i + dd i * (Yl i - 1)).deg ⟨T.pos i, h⟩ := by
        unfold degreeAtPosition
        rw [dite_eq_left h]
      rw [hdA] at h1
      push_cast at h1 ⊢
      have h4 := (Nat.cast_nonneg (degreeAtPosition (LL.setTies T fun i => n₀ i + dd i * (Yl i - 1)) (T.pos i + 1)) : (0 : ℝ) ≤ _)
      linarith
  · exact hflo r (by linarith)
  · unfold kapSeg
    push_cast
    linarith
  · unfold kapSeg
    push_cast
    have h1 : ((⌊(r : ℝ) ^ 2 * lgSeg p a r⌋₊ : ℕ) : ℝ) ≤ (r : ℝ) ^ 2 * lgSeg p a r := Nat.floor_le hpos
    have h2 := mul_le_mul_of_nonneg_right h1 (by linarith : (0 : ℝ) ≤ 2 * (s : ℝ) + 1 + 2)
    linarith
  · unfold kapSeg
    have hr4 : (4 : ℝ) ≤ (r : ℝ) ^ 2 := by nlinarith
    have h1 := mul_le_mul_of_nonneg_right hr4 (by linarith : (0 : ℝ) ≤ lgSeg p a r)
    nlinarith

theorem setTies_total_le {N : ℕ} (LL : Letters N) (T : TieData) (n n' : Fin T.t → ℕ) (h : ∀ i, n i ≤ n' i) :
    (LL.setTies T n).total ≤ (LL.setTies T n').total := by
  unfold Letters.total
  apply Finset.sum_le_sum
  intro i _
  unfold Letters.setTies
  dsimp only
  split_ifs with hh
  · exact h _
  · exact le_rfl

theorem theoremMV7 : TheoremMV7 := by
  intro p _ s r _ LL T a E Yl n₀ dd ρ hp hr hρ hadm hch hco ha hE hY hS hsz
  refine theoremMV7Of p s r LL T a E Yl n₀ dd ρ hp hr hρ hadm hch hco ha hE hY hS hsz ?_
  obtain ⟨htot, hsz⟩ := hsz
  have ha0 : 0 ≤ a := by linarith
  have hlg1 := one_le_lgSeg p a r ha0 (by omega)
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hp3 : (3 : ℝ) ≤ p := by
    have h2 := (Fact.out : p.Prime).two_le
    have : 3 ≤ p := by omega
    exact_mod_cast this
  have hy : (0 : ℝ) ≤ 8 * a + r := by linarith
  have hQ : 0 ≤ (r : ℝ) ^ 2 / 2 * lgSeg p a r := by positivity
  intro n hn
  have hle := grid_le T Yl n₀ dd n hn
  have hk : kapC p r (LL.setTies T n).total ≤ ⌊(r : ℝ) ^ 2 * lgSeg p a r⌋₊ := by
    apply Nat.le_floor
    have ht : ((LL.setTies T n).total : ℝ) ≤ 8 * a + r :=
      le_trans (by exact_mod_cast setTies_total_le LL T n _ hle) htot
    have hx : (((LL.setTies T n).total + r - 1 : ℕ) : ℝ) ≤ p * (8 * a + r) := by
      have h1 : (((LL.setTies T n).total + r - 1 : ℕ) : ℝ) ≤ ((LL.setTies T n).total : ℝ) + r := by
        have : (LL.setTies T n).total + r - 1 ≤ (LL.setTies T n).total + r := Nat.sub_le _ _
        exact_mod_cast this
      nlinarith
    have hl := natLog_le_lgSeg p a r _ ha0 (by omega) hx
    unfold kapC
    rw [Nat.cast_mul]
    calc ((r.choose 2 : ℕ) : ℝ) * (Nat.log p ((LL.setTies T n).total + r - 1) : ℝ)
        ≤ (r : ℝ) ^ 2 / 2 * lgSeg p a r := mul_le_mul (choose_two_le r) hl (Nat.cast_nonneg _) (by positivity)
      _ ≤ (r : ℝ) ^ 2 * lgSeg p a r := by nlinarith
  refine ⟨Formalism.InvariantFactorPaths.PW.Top.dischargeP p _ r _ ρ _ hk, Formalism.InvariantFactorPaths.PW.Top.dischargeW p _ r _ _ hk, fun i => ?_⟩
  obtain ⟨hlt, _, _⟩ := hadm.2.1 i
  obtain ⟨-, -, h2S⟩ := hsz i
  have hSle : ((LL.setTies T n).takeD (T.pos i + 1)).total ≤
      T.S (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))) i := by
    rw [takeD_total_eq (LL.setTies T n) T i hlt]; exact S_mono LL T n _ hle i
  have hSr : 2 * (((LL.setTies T n).takeD (T.pos i + 1)).total : ℝ) + 1 ≤ 8 * a + r := by
    have : (((LL.setTies T n).takeD (T.pos i + 1)).total : ℝ) ≤
        (T.S (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))) i : ℝ) := by exact_mod_cast hSle
    push_cast at h2S
    linarith
  have hS0 : (0 : ℝ) ≤ (((LL.setTies T n).takeD (T.pos i + 1)).total : ℝ) := Nat.cast_nonneg _
  refine gram_hypothesis_of_log_bound p (T.pos i) r _ T.J (T.thrUpTo i) ρ (lgSeg p a r) _ hr hρ (takeD_vec_last LL T hadm n i) ?_ ?_ ?_
  · apply natLog_le_lgSeg p a r _ ha0 (by omega)
    have h1 : ((((LL.setTies T n).takeD (T.pos i + 1)).total + r - 1 : ℕ) : ℝ) ≤
        (((LL.setTies T n).takeD (T.pos i + 1)).total : ℝ) + r := by
      have : ((LL.setTies T n).takeD (T.pos i + 1)).total + r - 1 ≤ ((LL.setTies T n).takeD (T.pos i + 1)).total + r :=
        Nat.sub_le _ _
      exact_mod_cast this
    nlinarith
  · apply natLog_le_lgSeg p a r _ ha0 (by omega)
    have h1 : ((4 * ((LL.setTies T n).takeD (T.pos i + 1)).total + r - 1 : ℕ) : ℝ) ≤
        4 * (((LL.setTies T n).takeD (T.pos i + 1)).total : ℝ) + r := by
      have : 4 * ((LL.setTies T n).takeD (T.pos i + 1)).total + r - 1 ≤
          4 * ((LL.setTies T n).takeD (T.pos i + 1)).total + r := Nat.sub_le _ _
      exact_mod_cast this
    nlinarith
  · have hK : ((T.pos i : ℕ) : ℝ) + 7 ≤ 2 * ((s : ℝ) + 4) := by
      have : T.pos i + 7 ≤ 2 * (s + 4) := by omega
      exact_mod_cast this
    calc (((T.pos i : ℕ) : ℝ) + 7) * ((r : ℝ) ^ 2 / 2 * lgSeg p a r)
        ≤ (2 * ((s : ℝ) + 4)) * ((r : ℝ) ^ 2 / 2 * lgSeg p a r) := mul_le_mul_of_nonneg_right hK hQ
      _ = ((s : ℝ) + 4) * ((r : ℝ) ^ 2 * lgSeg p a r) := by ring

end Formalism.InvariantFactorPaths.MC
end
end

-- Source module: Formalism.ThetaLogCoordinates.PartnerMeanCoordinates.LatticeTheoremEps28Valid

section

@[expose] public section

namespace Formalism.InvariantFactorPaths.MC.Top

theorem theoremMV7 : Formalism.CountingSumsFrames.TheoremMV7 := Formalism.InvariantFactorPaths.MC.theoremMV7

end Formalism.InvariantFactorPaths.MC.Top
end
end
