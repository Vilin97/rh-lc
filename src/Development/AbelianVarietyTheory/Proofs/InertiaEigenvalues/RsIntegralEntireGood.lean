module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsIntegralEntireTheta
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WordAppendSingle
public import GroundTheory.AutomorphicForms.ReductionMeasure
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormSmoothSpanNormLeShortRationalVector
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodSmoothDecayModerateGrowthRightTranslate
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
import Development.AbelianVarietyTheory.Definitions.Foundations.MeasurePreservingRmulQuotMeas
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DifferentiableIntegralMulCpow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFundamentalDomainIUnion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFiniteMeasureQuotMeasure
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecaysOfMemSmoothSpan
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InverseTransposeMemCuspFormRapidKernelSpanContra
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KernelOperatorIntegrableContinuousSmooth
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegrableOnMinAbsDetInvFundamentalDomain

section

@[expose] public section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
open scoped ENNReal

noncomputable section

open GlobalTheory.UnitaryBC

namespace GlobalTheory.FinVolGL

theorem exists_tsum_min_le {T : ℝ} (hT : 1 < T) : ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ u : ℝ, 0 < u →
    ∑' n : ℤ, ENNReal.ofReal (min (T ^ n * u) (T ^ n * u)⁻¹) ≤ B := by
  have hT0 : 0 < T := one_pos.trans hT
  have hq0 : 0 ≤ T⁻¹ := inv_nonneg.2 hT0.le
  have hq : T⁻¹ < 1 := inv_lt_one_of_one_lt₀ hT
  have hsum : Summable fun k : ℤ => T * T⁻¹ ^ k.natAbs :=
    (Summable.of_nat_of_neg (by simpa using summable_geometric_of_lt_one hq0 hq)
      (by simpa using summable_geometric_of_lt_one hq0 hq)).mul_left T
  refine ⟨∑' k : ℤ, ENNReal.ofReal (T * T⁻¹ ^ k.natAbs), hsum.tsum_ofReal_ne_top, fun u hu => ?_⟩
  obtain ⟨m, h1, h2⟩ := exists_mem_Ico_zpow hu hT
  rw [← (Equiv.subRight m).tsum_eq]
  refine ENNReal.tsum_le_tsum fun k => ENNReal.ofReal_le_ofReal ?_
  rw [Equiv.subRight_apply]
  have hp : 0 < T ^ (k - m) := zpow_pos hT0 _
  have e1 : T ^ (k - m) * T ^ m = T ^ k := by rw [← zpow_add₀ hT0.ne', sub_add_cancel]
  have e2 : T ^ (k - m) * T ^ (m + 1) = T ^ (k + 1) := by
    rw [← zpow_add₀ hT0.ne']; congr 1; ring
  have hv1 : T ^ k ≤ T ^ (k - m) * u := e1 ▸ mul_le_mul_of_nonneg_left h1 hp.le
  have hv2 : T ^ (k - m) * u < T ^ (k + 1) := e2 ▸ mul_lt_mul_of_pos_left h2 hp
  obtain ⟨j, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · refine (min_le_right _ _).trans ?_
    have h3 := inv_anti₀ (zpow_pos hT0 _) hv1
    rw [zpow_natCast, ← inv_pow] at h3
    rw [Int.natAbs_natCast]
    exact h3.trans (le_mul_of_one_le_left (pow_nonneg hq0 _) hT.le)
  · refine (min_le_left _ _).trans (hv2.le.trans (le_of_eq ?_))
    rw [zpow_add_one₀ hT0.ne', _root_.zpow_neg, zpow_natCast, Int.natAbs_neg, Int.natAbs_natCast, inv_pow, mul_comm]

theorem integrableOn_min_absDet : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ), 0 < m →
    ∀ (μ : Measure (GA E m)) [μ.IsHaarMeasure] (𝓕 : Set (GA E m)),
      IsFundamentalDomain (ratGL E m).range 𝓕 μ →
      IntegrableOn (fun h : GA E m => min (GroundTheory.Global.IdeleGroup.ideleModule E (GeneralLinearGroup.det h) : ℝ)
        (GroundTheory.Global.IdeleGroup.ideleModule E (GeneralLinearGroup.det h) : ℝ)⁻¹) 𝓕 μ := by
  intro E _ _ _ a ha μ _ 𝓕 h𝓕
  set δ : GA E a → ℝ := fun g => (GroundTheory.Global.IdeleGroup.ideleModule E (GeneralLinearGroup.det g) : ℝ) with hδ
  have hδc : Continuous δ := GlobalTheory.RSTheta.continuous_absDet
  have hδ0 : ∀ g, 0 < δ g := fun g => (GroundTheory.Global.IdeleGroup.ideleModule E _).2
  have hδr : ∀ γ g, δ (ratGL E a γ * g) = δ g := fun γ g => by
    simp only [hδ, map_mul, GlobalTheory.ShortVecDecay.ideleModule_det_rat, one_mul]
  set T : ℝ := Real.exp 1 ^ (a * Module.finrank ℚ E) with hT
  have hT1 : 1 < T := one_lt_pow₀ (Real.one_lt_exp_iff.2 one_pos) (Nat.mul_pos ha Module.finrank_pos).ne'
  have hδz : ∀ (n : ℤ) g, δ (@GlobalTheory.UnitaryBC.splitCentre E _ _ _ a 1 ^ n * g) = T ^ n * δ g := GlobalTheory.RSTheta.absDet_zpow_mul
  have hc : Continuous fun g => min (δ g) (δ g)⁻¹ := hδc.min (hδc.inv₀ fun g => (hδ0 g).ne')
  refine ⟨hc.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
    (.of_forall fun g => le_min (hδ0 g).le (inv_nonneg.2 (hδ0 g).le))).2 ?_⟩
  let φ : (ratGL E a).range × ℤ → latticeGL E a := fun p =>
    ⟨p.1 * @GlobalTheory.UnitaryBC.splitCentre E _ _ _ a 1 ^ p.2, mul_mem (Subgroup.mem_sup_left p.1.2) (zpow_mem_latticeGL _)⟩
  have hφ : Function.Bijective φ := by
    constructor
    · rintro ⟨⟨_, γ, rfl⟩, n⟩ ⟨⟨_, γ', rfl⟩, n'⟩ h
      have h1 : ratGL E a γ * @GlobalTheory.UnitaryBC.splitCentre E _ _ _ a 1 ^ n = ratGL E a γ' * @GlobalTheory.UnitaryBC.splitCentre E _ _ _ a 1 ^ n' := congrArg Subtype.val h
      have h2 := congrArg (fun x => δ (x * 1)) h1
      simp only [mul_assoc, hδr, hδz] at h2
      obtain rfl : n = n' := zpow_right_injective₀ (one_pos.trans hT1) hT1.ne' (mul_right_cancel₀ (hδ0 1).ne' h2)
      exact Prod.ext (Subtype.ext (mul_right_cancel h1)) rfl
    · rintro ⟨g, hg⟩
      obtain ⟨γ, n, rfl⟩ := mem_latticeGL_iff.1 hg
      exact ⟨⟨⟨_, γ, rfl⟩, n⟩, rfl⟩
  haveI : Countable (latticeGL E a) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hd := GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom (latticeGL E a) μ
  haveI := GlobalTheory.CovolGL.isFiniteMeasure_quotMeasure E a μ
  have h1 : μ (GlobalTheory.AutomorphicL2Unitary.stdDom (latticeGL E a)) ≠ ⊤ := by
    rw [← GlobalTheory.AutomorphicL2Unitary.quotMeasure_univ hd]; exact measure_ne_top _ _
  rw [← GlobalTheory.ThetaUnfold.lintegral_unfold μ (latticeGL E a) (ratGL E a).range (fun n : ℤ => @GlobalTheory.UnitaryBC.splitCentre E _ _ _ a 1 ^ n)
    (Equiv.ofBijective φ hφ) (fun _ => rfl) hd h𝓕 (fun g => ENNReal.ofReal (min (δ g) (δ g)⁻¹))
    (by rintro _ ⟨γ, rfl⟩ g; simp only [hδr])
    hc.measurable.ennreal_ofReal.aemeasurable]
  obtain ⟨B, hB, h⟩ := exists_tsum_min_le hT1
  refine (lintegral_mono (g := fun _ => B) fun g => ?_).trans_lt ?_
  · refine le_of_eq_of_le (tsum_congr fun n => ?_) (h _ (hδ0 g))
    simp only [hδz]
  · rw [setLIntegral_const]
    exact ENNReal.mul_lt_top hB.lt_top h1.lt_top

end GlobalTheory.FinVolGL
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegrableOnMinAbsDetInvFundamentalDomainStatement

section

@[expose] public section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

theorem _root_.GlobalTheory.T.integrableOn_min_absDet_inv_fundamentalDomain : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ), 0 < m →
    ∀ (μ : Measure (GA E m)) [μ.IsHaarMeasure] (𝓕 : Set (GA E m)),
      IsFundamentalDomain (ratGL E m).range 𝓕 μ →
      IntegrableOn (fun h : GA E m => min (GroundTheory.Global.IdeleGroup.ideleModule E (GeneralLinearGroup.det h) : ℝ)
        (GroundTheory.Global.IdeleGroup.ideleModule E (GeneralLinearGroup.det h) : ℝ)⁻¹) 𝓕 μ := by
  first | exact @GlobalTheory.FinVolGL.integrableOn_min_absDet | exact GlobalTheory.FinVolGL.integrableOn_min_absDet | (intros; apply GlobalTheory.FinVolGL.integrableOn_min_absDet <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MellinTypeIntegralEntireOfRapidDecay

section

@[expose] public section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory.MellinEntire

lemma min_inv_pos {t : ℝ} (ht : 0 < t) : 0 < min t t⁻¹ := lt_min ht (inv_pos.mpr ht)

lemma min_inv_le_one {t : ℝ} (ht : 0 < t) : min t t⁻¹ ≤ 1 := by
  rcases le_total t 1 with h | h
  · exact (min_le_left _ _).trans h
  · exact (min_le_right _ _).trans (inv_le_one_of_one_le₀ h)

lemma le_inv_of_le_one' {t : ℝ} (ht : 0 < t) (h : t ≤ 1) : t ≤ t⁻¹ :=
  h.trans ((one_le_inv₀ ht).mpr h)

lemma inv_le_of_one_le' {t : ℝ} (h : 1 ≤ t) : t⁻¹ ≤ t :=
  (inv_le_one_of_one_le₀ h).trans h

lemma rpow_mul_min_pow_le {t σ : ℝ} {K : ℕ} (ht : 0 < t) (hσ : |σ| ≤ K) :
    t ^ σ * (min t t⁻¹) ^ K ≤ 1 := by
  rcases le_total t 1 with h | h
  · rw [min_eq_left (le_inv_of_le_one' ht h)]
    have h1 : t ^ σ ≤ t ^ (-(K:ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge ht h (by linarith [neg_abs_le σ])
    calc t ^ σ * t ^ K ≤ t ^ (-(K:ℝ)) * t ^ K := by gcongr
      _ = 1 := by
        rw [Real.rpow_neg ht.le, Real.rpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ ht.ne')]
  · rw [min_eq_right (inv_le_of_one_le' h)]
    have h1 : t ^ σ ≤ t ^ (K:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le h (le_trans (le_abs_self σ) hσ)
    calc t ^ σ * t⁻¹ ^ K ≤ t ^ (K:ℝ) * t⁻¹ ^ K := by gcongr
      _ = 1 := by rw [Real.rpow_natCast, ← mul_pow, mul_inv_cancel₀ ht.ne', one_pow]

lemma min_mul_abs_log_le {t : ℝ} (ht : 0 < t) : min t t⁻¹ * |Real.log t| ≤ 1 := by
  rcases le_total t 1 with h | h
  · rw [min_eq_left (le_inv_of_le_one' ht h)]
    have := Real.abs_log_mul_self_lt t ht h
    rw [abs_mul, abs_of_pos ht] at this
    linarith
  · rw [min_eq_right (inv_le_of_one_le' h)]
    have := Real.abs_log_mul_self_lt t⁻¹ (inv_pos.mpr ht) (inv_le_one_of_one_le₀ h)
    rw [Real.log_inv, abs_mul, abs_neg, abs_of_pos (inv_pos.mpr ht)] at this
    linarith

theorem integrable_and_differentiable {X : Type} [MeasurableSpace X] (ν : Measure X)
    (A : X → ℂ) (T : X → ℝ)
    (hA : AEStronglyMeasurable A ν) (hT : Measurable T) (hTpos : ∀ x, 0 < T x)
    (hw : Integrable (fun x => min (T x) (T x)⁻¹) ν)
    (hdec : ∀ N : ℕ, ∃ C : ℝ, ∀ x, ‖A x‖ ≤ C * (min (T x) (T x)⁻¹) ^ N) :
    (∀ s : ℂ, Integrable (fun x => A x * ((T x : ℝ) : ℂ) ^ s) ν) ∧
      Differentiable ℂ (fun s : ℂ => ∫ x, A x * ((T x : ℝ) : ℂ) ^ s ∂ν) := by
  have wpos : ∀ x, 0 < min (T x) (T x)⁻¹ := fun x => min_inv_pos (hTpos x)
  have wle : ∀ x, min (T x) (T x)⁻¹ ≤ 1 := fun x => min_inv_le_one (hTpos x)
  have hTc : Measurable fun x => ((T x : ℝ) : ℂ) := Complex.measurable_ofReal.comp hT
  have meas : ∀ s : ℂ, AEStronglyMeasurable (fun x => A x * ((T x : ℝ) : ℂ) ^ s) ν :=
    fun s => hA.mul (hTc.pow_const s).aestronglyMeasurable
  have bnd : ∀ K : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x (s : ℂ), |s.re| ≤ K →
      ‖A x * ((T x : ℝ) : ℂ) ^ s‖ ≤ C * (min (T x) (T x)⁻¹) ^ 2 := by
    intro K
    obtain ⟨C, hC⟩ := hdec (K + 2)
    refine ⟨|C|, abs_nonneg _, fun x s hs => ?_⟩
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hTpos x)]
    have hA' : ‖A x‖ ≤ |C| * (min (T x) (T x)⁻¹) ^ (K + 2) :=
      (hC x).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg (wpos x).le _))
    have h2 := rpow_mul_min_pow_le (hTpos x) hs
    have h0 : 0 ≤ T x ^ s.re := Real.rpow_nonneg (hTpos x).le _
    calc ‖A x‖ * T x ^ s.re ≤ |C| * (min (T x) (T x)⁻¹) ^ (K + 2) * T x ^ s.re :=
          mul_le_mul_of_nonneg_right hA' h0
      _ = |C| * (min (T x) (T x)⁻¹) ^ 2 * (T x ^ s.re * (min (T x) (T x)⁻¹) ^ K) := by ring
      _ ≤ |C| * (min (T x) (T x)⁻¹) ^ 2 * 1 := by
          gcongr
      _ = |C| * (min (T x) (T x)⁻¹) ^ 2 := mul_one _
  have sq_le : ∀ x, (min (T x) (T x)⁻¹) ^ 2 ≤ min (T x) (T x)⁻¹ := fun x => by
    nlinarith [wpos x, wle x]
  refine ⟨fun s => ?_, fun s₀ => ?_⟩
  · obtain ⟨C, hC0, hC⟩ := bnd ⌈|s.re|⌉₊
    refine Integrable.mono' (hw.const_mul C) (meas s) (ae_of_all _ fun x => ?_)
    exact (hC x s (Nat.le_ceil _)).trans (mul_le_mul_of_nonneg_left (sq_le x) hC0)
  · obtain ⟨C, hC0, hC⟩ := bnd (⌈|s₀.re|⌉₊ + 1)
    have hre : ∀ s ∈ Metric.ball s₀ 1, |s.re| ≤ ((⌈|s₀.re|⌉₊ + 1 : ℕ) : ℝ) := by
      intro s hs
      rw [Metric.mem_ball, dist_eq_norm] at hs
      have h1 : |s.re - s₀.re| ≤ ‖s - s₀‖ := by
        rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _
      have h2 : |s.re| ≤ |s₀.re| + |s.re - s₀.re| := by
        have := abs_add_le s₀.re (s.re - s₀.re); simpa using this
      have h3 := Nat.le_ceil |s₀.re|
      push_cast
      linarith
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν)
      (F := fun s x => A x * ((T x : ℝ) : ℂ) ^ s)
      (F' := fun s x => A x * (((T x : ℝ) : ℂ) ^ s * Complex.log ((T x : ℝ) : ℂ)))
      (x₀ := s₀) (bound := fun x => C * min (T x) (T x)⁻¹) (s := Metric.ball s₀ 1) (Metric.ball_mem_nhds s₀ one_pos)
      (Filter.Eventually.of_forall fun s => meas s) ((fun s => ?_ : ∀ s : ℂ,
        Integrable (fun x => A x * ((T x : ℝ) : ℂ) ^ s) ν) s₀)
      (hA.mul ((hTc.pow_const s₀).mul (Complex.measurable_log.comp hTc)).aestronglyMeasurable)
      (ae_of_all _ fun x s hs => ?_) (hw.const_mul C)
      (ae_of_all _ fun x s _ => ?_)
    · exact key.2.differentiableAt
    · obtain ⟨C', hC0', hC'⟩ := bnd ⌈|s.re|⌉₊
      refine Integrable.mono' (hw.const_mul C') (meas s) (ae_of_all _ fun x => ?_)
      exact (hC' x s (Nat.le_ceil _)).trans (mul_le_mul_of_nonneg_left (sq_le x) hC0')
    · show ‖A x * (((T x : ℝ) : ℂ) ^ s * Complex.log ((T x : ℝ) : ℂ))‖ ≤ C * min (T x) (T x)⁻¹
      rw [← mul_assoc, norm_mul, ← Complex.ofReal_log (hTpos x).le, Complex.norm_real,
        Real.norm_eq_abs]
      have h1 := hC x s (hre s hs)
      have h2 := min_mul_abs_log_le (hTpos x)
      calc ‖A x * ((T x : ℝ) : ℂ) ^ s‖ * |Real.log (T x)|
          ≤ C * (min (T x) (T x)⁻¹) ^ 2 * |Real.log (T x)| :=
            mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
        _ = C * min (T x) (T x)⁻¹ * (min (T x) (T x)⁻¹ * |Real.log (T x)|) := by ring
        _ ≤ C * min (T x) (T x)⁻¹ * 1 := by
            gcongr
            exact mul_nonneg hC0 (wpos x).le
        _ = C * min (T x) (T x)⁻¹ := mul_one _
    · have hne : ((T x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hTpos x).ne'
      exact (Complex.hasStrictDerivAt_const_cpow (Or.inl hne)).hasDerivAt.const_mul (A x)

end GlobalTheory.MellinEntire
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MellinTypeIntegralEntireOfRapidDecayStatement

section

@[expose] public section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

theorem _root_.GlobalTheory.T.mellinType_integral_entire_of_rapid_decay : ∀ {X : Type} [MeasurableSpace X] (ν : Measure X) (A : X → ℂ) (T : X → ℝ),
    AEStronglyMeasurable A ν → Measurable T → (∀ x, 0 < T x) → Integrable (fun x => min (T x) (T x)⁻¹) ν →
    (∀ N : ℕ, ∃ C : ℝ, ∀ x, ‖A x‖ ≤ C * (min (T x) (T x)⁻¹) ^ N) →
    (∀ s : ℂ, Integrable (fun x => A x * ((T x : ℝ) : ℂ) ^ s) ν) ∧
      Differentiable ℂ (fun s : ℂ => ∫ x, A x * ((T x : ℝ) : ℂ) ^ s ∂ν) := by
  first | exact @GlobalTheory.MellinEntire.integrable_and_differentiable | exact GlobalTheory.MellinEntire.integrable_and_differentiable | (intros; apply GlobalTheory.MellinEntire.integrable_and_differentiable <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsIntegralEntireGood

section

@[expose] public section

noncomputable section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.RSnmGood

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


variable (E a) in
def contGood : Submodule ℂ (GA E a → ℂ) where
  carrier := {F | Continuous F ∧ GlobalTheory.MSpanDecay.Good F}
  zero_mem' := ⟨continuous_const, (GlobalTheory.MSpanDecay.goodSub E a).zero_mem⟩
  add_mem' := fun h h' => ⟨h.1.add h'.1, (GlobalTheory.MSpanDecay.goodSub E a).add_mem h.2 h'.2⟩
  smul_mem' := fun z _ h => ⟨h.1.const_smul z, (GlobalTheory.MSpanDecay.goodSub E a).smul_mem z h.2⟩

theorem mspanR_le_contGood (ha : 0 < a) {π : CuspSub E a} (hπ : π.IsUnitary) :
    GlobalTheory.JSW.mspanR π ≤ contGood E a := by
  refine sInf_le ⟨fun φ hφ => ?_, fun F hF h => ?_, fun F hF X _ ν hν k γ hk => ?_⟩
  · exact ⟨(GlobalTheory.RSnm.mem_goodFns ha hπ (Submodule.mem_sup_left ⟨φ, hφ, rfl⟩)).1, GlobalTheory.MSpanDecay.good_of_mem hπ hφ⟩
  · exact ⟨hF.1.comp (continuous_id.mul continuous_const), GlobalTheory.RtGood.good_mul_right E a F h hF.2⟩
  · haveI := hν
    refine ⟨?_, GlobalTheory.MSpanDecay.Good.kernel hF.2 hk⟩
    exact (GlobalTheory.JSW.kerOp_integrable_continuous E a X ν k γ hk ⟨F, hF.2.1⟩ hF.1
      (GlobalTheory.RSnm.bounded_of_decays ha hF.2.decays)).2

theorem mspanR_le_goodFns (ha : 0 < a) {π : CuspSub E a} (hπ : π.IsUnitary) :
    GlobalTheory.JSW.mspanR π ≤ GlobalTheory.RSnm.goodFns a := fun F hF =>
  ⟨(mspanR_le_contGood ha hπ hF).1, (mspanR_le_contGood ha hπ hF).2.decays,
    (GlobalTheory.MSpanDecay.mspanR_le_goodSub hπ.contra (GlobalTheory.JSW.invT_mem_mspanR_contra E a π F hF)).decays⟩


open GroundTheory.Automorphic in
theorem rsIntegral_entire_good {m n : ℕ} (hm0 : 0 < m) (hmn : m < n) {φ : GA E n → ℂ} (g1 : φ ∈ GlobalTheory.RSnm.goodFns n)
    {φ' : GA E m → ℂ} (g2 : φ' ∈ GlobalTheory.RSnm.goodFns m) {F : (Fin m → Ad E) → ℂ}
    (hF : F ∈ GJMatrix.schwartzBruhatPi (K := E) (ι := Fin m)) (μ : Measure (GA E m)) [μ.IsHaarMeasure] {𝓕 : Set (GA E m)}
    (h𝓕 : IsFundamentalDomain (ratGL E m).range 𝓕 μ) :
    (∀ s : ℂ, IntegrableOn (GlobalTheory.RSnm.rsIntegrand m hmn.le F φ φ' s) 𝓕 μ) ∧
      ∀ s : ℂ, AnalyticAt ℂ (fun s => ∫ h in 𝓕, GlobalTheory.RSnm.rsIntegrand m hmn.le F φ φ' s h ∂μ) s := by
  obtain ⟨C₁, hC₁⟩ := GlobalTheory.RSnm.bounded_of_decays (hm0.trans hmn) g1.2.1
  obtain ⟨C₂, hC₂⟩ := GlobalTheory.RSnm.bounded_of_decays hm0 g2.2.1
  set A : GA E m → ℂ := fun h => FourierWhittaker.partialCoeff (GlobalTheory.RSnm.colSmooth m F φ) (m + 1)
    (FourierWhittaker.blockGL hmn.le h) * (starRingEnd ℂ) (φ' h)
  have hAc : Continuous A :=
    ((FourierWhittaker.continuous_partialCoeff (GlobalTheory.RSnm.continuous_colSmooth hF g1.1 hC₁) (m + 1)).comp
      (GlobalTheory.RSnm.continuous_blockGL hmn.le)).mul (Complex.continuous_conj.comp g2.1)
  have hbd : ∀ N : ℕ, ∃ C : ℝ, ∀ h, ‖A h‖ ≤ C * (min (GlobalTheory.RSnm.detAbs h) (GlobalTheory.RSnm.detAbs h)⁻¹) ^ N := by
    intro N
    obtain ⟨C, hC⟩ := GlobalTheory.RSnm.colSmooth_bound hmn g1 hF N
    refine ⟨C * C₂, fun h => ?_⟩
    have hP := GlobalTheory.RSnm.partialCoeff_bound hmn (b := fun t => C * (min t t⁻¹) ^ N) hC (n - (m + 1)) (m + 1) (by omega)
      le_rfl _ (GlobalTheory.RSnm.inS_blockGL hmn h)
    simp only [GlobalTheory.RSnm.detAbs_blockGL] at hP
    rw [norm_mul, Complex.norm_conj]
    calc _ ≤ C * (min (GlobalTheory.RSnm.detAbs h) (GlobalTheory.RSnm.detAbs h)⁻¹) ^ N * C₂ :=
          mul_le_mul hP (hC₂ h) (norm_nonneg _) ((norm_nonneg _).trans hP)
      _ = _ := by ring
  obtain ⟨hI, hD⟩ := GlobalTheory.T.mellinType_integral_entire_of_rapid_decay (μ.restrict 𝓕) A GlobalTheory.RSnm.detAbs hAc.aestronglyMeasurable
    GlobalTheory.RSnm.continuous_detAbs.measurable GlobalTheory.RSnm.detAbs_pos (GlobalTheory.T.integrableOn_min_absDet_inv_fundamentalDomain E m hm0 μ 𝓕 h𝓕) hbd
  have e : ∀ s, GlobalTheory.RSnm.rsIntegrand m hmn.le F φ φ' s =
      fun h => A h * ((GlobalTheory.RSnm.detAbs h : ℝ) : ℂ) ^ (s - ((n : ℂ) - m) / 2) := fun s => rfl
  refine ⟨fun s => by rw [e]; exact hI _, fun s => ?_⟩
  simp only [e]
  exact (hD.analyticAt _).comp (analyticAt_id.sub analyticAt_const)

end GlobalTheory.RSnmGood
end
end
end
