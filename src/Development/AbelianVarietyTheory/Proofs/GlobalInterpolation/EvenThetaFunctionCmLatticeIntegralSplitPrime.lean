module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CmBaseFieldIntegersAndCurveIdealFactsStatement
public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CmEvenThetaSeriesChartCoeffIntegral
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpSeriesCoeffBoundedTaylorEllipticOfPoles
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpSeriesCoeffNormBoundedRingLaws
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpTransportedTaylorSeriesInChartRingHomLaws
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MulPowTwoLeTripleProdOfGe
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpTransportedTaylorSeriesMultiplicativeChart
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsMeasureOfBoundedMoments
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TwistedMeasureMomentsEqShiftedSeriesJets
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeJetsAreBoundedMomentsOfSpanImagQuadraticStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeJetsAreBoundedMomentsPullbackStatement
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdChar
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.QuasiPeriodConstUniqueOf
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.QuasiPeriodConstUnique
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.Th0CharMulOpUTh0HalfPeriodEq

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CpSeriesBoundedThetaLevelValueOne

section

@[expose] public section

noncomputable section
open GlobalTheory.MomOne GlobalTheory.MomN PowerSeries
open scoped ComplexConjugate Topology

namespace GlobalTheory.MomN.ThetaQuot

variable {q : ℕ} [Fact q.Prime]

theorem bdd_hat_quot (M : Mdl q) (ℓ : ℂ_[q]⟦X⟧) (hC : M.Chart ℓ) (F H : ℂ → ℂ)
    (hF : Differentiable ℂ F) (hH : Differentiable ℂ H) (h0 : H 0 ≠ 0)
    (hper : ∀ l ∈ M.L.lattice, ∀ z, F (z + l) / H (z + l) = F z / H z)
    (hz : ∀ p, H p = 0 → ¬ M.Small p) :
    Bdd (hat M.ι ℓ fun z => F z / H z) := by
  refine EllBdd.bdd_hat_of_ell q M ℓ _ hC ⟨fun z => ?_, hper⟩ ((hF.analyticAt 0).div (hH.analyticAt 0) h0)
    fun p hp => hz p ?_
  · exact (hF.analyticAt z).meromorphicAt.div (hH.analyticAt z).meromorphicAt
  · by_contra hne
    exact absurd hp (not_lt.2 ((hF.analyticAt p).div (hH.analyticAt p) hne).meromorphicOrderAt_nonneg)

theorem not_inOK_half {d : ℕ} (hd : 0 < d) : ¬ InOK d (1 / 2) := by
  rintro ⟨u, v, h⟩
  have hs : Real.sqrt d ≠ 0 := by positivity
  have h2 := congrArg Complex.im h
  have h1' := congrArg Complex.re h
  simp [wK, hs] at h1' h2
  subst h2
  have : (1 : ℝ) = 2 * u := by linarith
  have : (1 : ℤ) = 2 * u := by exact_mod_cast this
  omega

theorem bd_one_hat_of_theta_level : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]) (θ G : ℂ → ℂ) (a : ℕ), d.Prime → d % 16 = 7 → Split d q → q ≠ 2 → IsOK d M.L → M.MChart ω → IsTh d θ → Differentiable ℂ G → G 0 = 1 → (∀ x, InOK d x → ∀ z, G (z + x) * (Complex.exp ((Real.pi : ℂ) * Complex.I * ((Complex.normSq x : ℝ) : ℂ)) * Complex.exp (-(Real.pi : ℂ) * h1 d z x - (Real.pi : ℂ) / 2 * h1 d x x)) ^ a = G z) → (∀ z, G z = 0 → PrimeTo d q z) → Bd 1 (hat M.ι (C ω * logS) G) := by
  intro d q _ M ω θ G a hd hd16 hsp hq2 hOK hMC hθ hG hG0 hGW hGz
  have hθB := theta_series_integral d q M ω θ hd hd16 hsp hOK hMC hθ
  have hC : M.Chart (C ω * logS) := hMC
  set ℓ := C ω * logS with hℓ
  have hOk := hC.1
  have hℓ0 : constantCoeff ℓ = 0 := hC.2.1
  obtain ⟨hθd, hθ0, -, hθW, hθz⟩ := hθ
  set E : ℂ → ℂ → ℂ := fun z x => Complex.exp ((Real.pi : ℂ) * Complex.I * ((Complex.normSq x : ℝ) : ℂ)) *
    Complex.exp (-(Real.pi : ℂ) * h1 d z x - (Real.pi : ℂ) / 2 * h1 d x x) with hE
  have hE0 : ∀ z x, E z x ≠ 0 := fun z x => mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)
  have hθE : ∀ x, InOK d x → ∀ z, θ (z + x) * E z x = θ z := by
    intro x hx z
    have := congrFun (hθW x hx) z
    simp only [W1, U1] at this
    rw [← this]; simp only [hE]; ring
  have hGE : ∀ x, InOK d x → ∀ z, G (z + x) * E z x ^ a = G z := hGW
  have hlat : ∀ l, l ∈ M.L.lattice ↔ InOK d l := hOK
  have hper1 : ∀ l ∈ M.L.lattice, ∀ z, G (z + l) / θ (z + l) ^ a = G z / θ z ^ a := by
    intro l hl z
    rw [hlat] at hl
    rw [← hGE l hl z, ← hθE l hl z, mul_pow (θ (z + l)) (E z l) a, mul_div_mul_right _ _ (pow_ne_zero _ (hE0 z l))]
  have hper2 : ∀ l ∈ M.L.lattice, ∀ z, θ (z + l) ^ a / G (z + l) = θ z ^ a / G z := by
    intro l hl z
    rw [hlat] at hl
    rw [← hGE l hl z, ← hθE l hl z, mul_pow (θ (z + l)) (E z l) a, mul_div_mul_right _ _ (pow_ne_zero _ (hE0 z l))]
  have hnsθ : ∀ p, θ p = 0 → ¬ M.Small p := by
    intro p hp
    have hm : p - 1 / 2 ∈ M.L.lattice := (hlat _).2 (hθz p hp)
    have h1m : (1 : ℂ) ∈ M.L.lattice := (hlat _).2 ⟨1, 0, by simp⟩
    have h2 : ((2 : ℕ) : ℂ) * p ∈ M.L.lattice := by
      have : ((2 : ℕ) : ℂ) * p = (p - 1 / 2) + (p - 1 / 2) + 1 := by push_cast; ring
      rw [this]; exact add_mem (add_mem hm hm) h1m
    have hnot : p ∉ M.L.lattice := fun h => not_inOK_half hd.pos ((hlat _).1 (by
      have : (1 / 2 : ℂ) = p - (p - 1 / 2) := by ring
      rw [this]; exact sub_mem h hm))
    have hcop : Nat.Coprime 2 q := (Nat.coprime_primes Nat.prime_two Fact.out).2 (Ne.symm hq2)
    have hx := (TorsionReduction.torsion_integral_and_distinct q M 2 hOk hcop).1 p h2 hnot
    rintro (h | h)
    · exact hnot h
    · linarith
  have hnsG : ∀ p, G p = 0 → ¬ M.Small p := by
    intro p hp
    obtain ⟨s, -, hsq, hsp'⟩ := hGz p hp
    have hm : (s : ℂ) * p ∈ M.L.lattice := (hlat _).2 hsp'
    have hnot : p ∉ M.L.lattice := fun h => by
      have := hGE p ((hlat _).1 h) 0
      rw [zero_add, hp, zero_mul, hG0] at this
      exact zero_ne_one this
    have hx := (TorsionReduction.torsion_integral_and_distinct q M s hOk hsq).1 p hm hnot
    rintro (h | h)
    · exact hnot h
    · linarith
  have hθa : Differentiable ℂ (fun z => θ z ^ a) := hθd.pow a
  have hθa0 : θ 0 ^ a ≠ 0 := by rw [hθ0, one_pow]; exact one_ne_zero
  have hG0' : G 0 ≠ 0 := by rw [hG0]; exact one_ne_zero
  have hφ := bdd_hat_quot M ℓ hC G (fun z => θ z ^ a) hG hθa hθa0 hper1
    (fun p hp => by
      rcases eq_or_ne a 0 with rfl | ha
      · simp at hp
      · exact hnsθ p ((pow_eq_zero_iff ha).1 hp))
  have hψ := bdd_hat_quot M ℓ hC (fun z => θ z ^ a) G hθa hG hG0' hper2 hnsG
  obtain ⟨hL1, hL2, -, hL4, -, -, -⟩ := TaylorRead.hat_laws q M.ι ℓ hℓ0
  obtain ⟨gl1, -, -, -, gl5, -⟩ := sup_norm_laws q
  have haφ : AnalyticAt ℂ (fun z => G z / θ z ^ a) 0 := (hG.analyticAt 0).div (hθa.analyticAt 0) hθa0
  have haψ : AnalyticAt ℂ (fun z => θ z ^ a / G z) 0 := (hθa.analyticAt 0).div (hG.analyticAt 0) hG0'
  have hθne : ∀ᶠ z in 𝓝 0, θ z ≠ 0 := hθd.continuous.continuousAt.eventually_ne (by rw [hθ0]; exact one_ne_zero)
  have hGne : ∀ᶠ z in 𝓝 0, G z ≠ 0 := hG.continuous.continuousAt.eventually_ne hG0'
  have hprod : hat M.ι ℓ (fun z => G z / θ z ^ a) * hat M.ι ℓ (fun z => θ z ^ a / G z) = 1 := by
    have e1 := (hL1 (fun z => G z / θ z ^ a * (θ z ^ a / G z)) (fun _ => 1) (haφ.mul haψ) analyticAt_const).2.2.1
      (eventually_nhdsWithin_of_eventually_nhds (by
        filter_upwards [hθne, hGne] with z h1 h2
        rw [div_mul_div_comm, mul_comm (G z), div_self (mul_ne_zero (pow_ne_zero _ h1) h2)]))
    rw [← (hL1 _ _ haφ haψ).2.1, e1, hL2]; simp
  have hcc : constantCoeff (hat M.ι ℓ (fun z => G z / θ z ^ a)) = 1 := by
    rw [hL4]; simp [hG0, hθ0]
  have hφ1 : Bd 1 (hat M.ι ℓ (fun z => G z / θ z ^ a)) := (gl5 _ _ hφ hψ hprod hcc).1
  have eG : hat M.ι ℓ G = hat M.ι ℓ (fun z => G z / θ z ^ a) * hat M.ι ℓ (fun z => θ z ^ a) := by
    rw [← (hL1 _ _ haφ (hθa.analyticAt 0)).2.1]
    exact (hL1 G _ (hG.analyticAt 0) (haφ.mul (hθa.analyticAt 0))).2.2.1
      (eventually_nhdsWithin_of_eventually_nhds (by
        filter_upwards [hθne] with z h1
        exact (div_mul_cancel₀ _ (pow_ne_zero _ h1)).symm))
  have hpow : ∀ n : ℕ, hat M.ι ℓ (fun z => θ z ^ n) = hat M.ι ℓ θ ^ n ∧ Bd 1 (hat M.ι ℓ θ ^ n) := by
    intro n
    induction n with
    | zero =>
      refine ⟨by simpa using hL2 1, fun k => ?_⟩
      rw [pow_zero, coeff_one]; split_ifs <;> simp
    | succ n ih =>
      have e : (fun z => θ z ^ (n + 1)) = fun z => θ z ^ n * θ z := funext fun z => pow_succ _ _
      rw [e, (hL1 (fun z => θ z ^ n) θ ((hθd.pow n).analyticAt 0) (hθd.analyticAt 0)).2.1, ih.1, pow_succ]
      refine ⟨rfl, ?_⟩
      simpa using (gl1 _ _ 1 1 ih.2 hθB).2
  rw [eG, (hpow a).1]
  simpa using (gl1 _ _ 1 1 hφ1 (hpow a).2).2

end GlobalTheory.MomN.ThetaQuot
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CpSeriesBoundedThetaLevelValueOneStatement

section

@[expose] public section

open GlobalTheory.MomOne GlobalTheory.MomN PowerSeries
open scoped ComplexConjugate

theorem _root_.GlobalTheory.T.cpSeries_bounded_theta_level_value_one : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]) (θ G : ℂ → ℂ) (a : ℕ), d.Prime → d % 16 = 7 → Split d q → q ≠ 2 → IsOK d M.L → M.MChart ω → IsTh d θ → Differentiable ℂ G → G 0 = 1 → (∀ x, InOK d x → ∀ z, G (z + x) * (Complex.exp ((Real.pi : ℂ) * Complex.I * ((Complex.normSq x : ℝ) : ℂ)) * Complex.exp (-(Real.pi : ℂ) * h1 d z x - (Real.pi : ℂ) / 2 * h1 d x x)) ^ a = G z) → (∀ z, G z = 0 → PrimeTo d q z) → Bd 1 (hat M.ι (C ω * logS) G) := by
  first | exact @GlobalTheory.MomN.ThetaQuot.bd_one_hat_of_theta_level | exact GlobalTheory.MomN.ThetaQuot.bd_one_hat_of_theta_level | (intros; apply GlobalTheory.MomN.ThetaQuot.bd_one_hat_of_theta_level <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.JetsAreBoundedMeasureMomentsOfChartCoeffBound

section

@[expose] public section

open GlobalTheory.MomOne GlobalTheory.MomN PowerSeries
open scoped ComplexConjugate

namespace GlobalTheory.MomOneAmice

theorem momInt_of_bd_hat (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (ω : ℂ_[q]) (G : ℂ → ℂ)
    (hG : Differentiable ℂ G) (hB : Bd 1 (hat ι (C ω * logS) G)) :
    MomInt ι (fun _ : Unit => ι.symm ω) G := by
  set H := hat ι (C ω * logS) G with hH
  obtain ⟨μ₁, hμ₁, hsum⟩ := GlobalTheory.MultiMahler.exists_measure_of_bounded_moments q 1
    (fun n => coeff (n 0) H) ⟨1, fun n => hB (n 0)⟩
  have hn1 : ‖μ₁‖ ≤ 1 := (hμ₁ 1 zero_le_one).2 fun n => hB (n 0)

  let e : C(Fin 1 → ℤ_[q], Unit → ℤ_[q]) := ⟨fun a _ => a 0, by fun_prop⟩
  let R₀ : C(Unit → ℤ_[q], ℂ_[q]) →ₗ[ℂ_[q]] C(Fin 1 → ℤ_[q], ℂ_[q]) :=
    { toFun := fun F => F.comp e
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hR : ∀ F, ‖R₀ F‖ ≤ 1 * ‖F‖ := fun F => by
    rw [one_mul, ContinuousMap.norm_le _ (norm_nonneg _)]
    intro a
    exact F.norm_coe_le_norm _
  let R := R₀.mkContinuous 1 hR
  have hRn : ‖R‖ ≤ 1 := LinearMap.mkContinuous_norm_le _ zero_le_one _
  refine ⟨μ₁.comp R, ?_, fun k j f hf => ?_⟩
  · calc ‖μ₁.comp R‖ ≤ ‖μ₁‖ * ‖R‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := mul_le_mul hn1 hRn (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · obtain ⟨f₁, hf₁, hs₁⟩ := GlobalTheory.MomOne.TwistMom.twisted_moments q H 1 0 k ⟨1, hB⟩ (by simp)
    have hF : ∀ a : Fin 1 → ℤ_[q], (R f) a = ∏ i, (fun _ : Fin 1 => f₁) i (a i) := fun a => by
      change f (e a) = _
      rw [hf, Fin.prod_univ_one, hf₁]
      simp [e]
    have h2 := hsum (fun _ => f₁) (R f) hF
    have h3 : HasSum (fun m : ℕ => coeff m H * (fwdDiff (1 : ℤ_[q]))^[m] f₁ 0) (μ₁ (R f)) := by
      have := (Equiv.hasSum_iff (Equiv.funUnique (Fin 1) ℕ).symm).2 h2
      simpa [Function.comp_def] using this
    have h4 := h3.unique hs₁
    rw [GlobalTheory.MomOne.Basic.shiftS_one, (GlobalTheory.MomOne.hat_multiplicative_chart q ι ω G (hG.analyticAt 0)).2.1 k] at h4
    rw [ContinuousLinearMap.comp_apply, h4, iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, smul_eq_mul,
      map_mul, map_prod]
    simp

end GlobalTheory.MomOneAmice
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.JetsAreBoundedMeasureMomentsOfChartCoeffBoundStatement

section

@[expose] public section

open GlobalTheory.MomOne GlobalTheory.MomN PowerSeries
open scoped ComplexConjugate

theorem _root_.GlobalTheory.T.jetsAreBoundedMeasureMoments_of_chart_coeff_bound : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (ω : ℂ_[q]) (G : ℂ → ℂ), Differentiable ℂ G → Bd 1 (hat ι (C ω * logS) G) → MomInt ι (fun _ : Unit => ι.symm ω) G := by
  first | exact @GlobalTheory.MomOneAmice.momInt_of_bd_hat | exact GlobalTheory.MomOneAmice.momInt_of_bd_hat | (intros; apply GlobalTheory.MomOneAmice.momInt_of_bd_hat <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EvenThetaFunctionCmLatticeIntegralSplitPrime

section

@[expose] public section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

noncomputable section

namespace GlobalTheory.MomN

open GlobalTheory.MomOne
open scoped ComplexConjugate

theorem latInt_th0_of_split_prime : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → jacobiSym (-(D.host.d : ℤ)) q = 1 → Nat.Coprime (Ideal.absNorm cc) q → ∀ (ι : ℂ ≃+* ℂ_[q]) (δ₀ : ℂ) (θ : ℂ → ℂ) (Ω : ℂ_[q]), Per D.host.d ι δ₀ θ Ω → LatInt ι (Ω / ι δ₀) (lamOf D cc δ) B.th0 := by
  intro D cc δ B hcc _ q _ hq2 hjac hcop ι δ₀ θ Ω hPer
  obtain ⟨hdp, hd16, hOK, -, hlat⟩ := GlobalTheory.T.cmBaseField_integers_and_curveIdeal_facts D
  obtain ⟨hTh, -, -, -, -, -, M, hMι, hMOK, hMch⟩ := hPer
  have hcc0 : cc ≠ ⊥ := hcc.1
  obtain ⟨hA, hmem⟩ := hlat cc δ hcc0
  have hmem1 := (hlat ⊤ 1 top_ne_bot).2
  have hqp : q.Prime := Fact.out
  have hN0 : Ideal.absNorm cc ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hcc0
  have hNc : ((Ideal.absNorm cc : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hN0
  have hsd : 0 < Real.sqrt D.host.d := Real.sqrt_pos.2 (by exact_mod_cast hdp.pos)
  have hAF : Formalism.L2.Th1.F.area B.L = Complex.normSq δ * (Ideal.absNorm cc : ℝ) * Real.sqrt D.host.d / 2 := by
    rw [← hA]; exact B.areaOK.symm
  have hApos : 0 < Formalism.L2.Th1.F.area B.L := Formalism.L2.Th1.F.PeriodAreaSignLemmas.area_pos B.L
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    rw [hAF] at hApos
    simp at hApos
  have hmemL : ∀ x, x ∈ B.L.lattice ↔ x ∈ lamOf D cc δ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.mem_iff B
  obtain ⟨hGd0, hG00, -, hzero, hlaw⟩ :=
    Formalism.L2.Th1.F.th0Basic B.L B.ω₀ B.omega_mem (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.half B)
  set N : ℕ := Ideal.absNorm cc with hN
  set G : ℂ → ℂ := fun z => B.th0 (δ * N * z) with hG
  have hGd : Differentiable ℂ G := by
    have : Differentiable ℂ fun z : ℂ => δ * N * z := by fun_prop
    exact hGd0.comp this
  have hG0 : G 0 = 1 := by simp only [hG, mul_zero]; exact hG00
  have hsplit : Split D.host.d q := Or.inr ⟨hq2, hjac⟩

  have hzer : ∀ z, G z = 0 → PrimeTo D.host.d q z := by
    intro z hz
    have h1 : δ * N * z + B.ω₀ / 2 ∈ B.L.lattice := (hzero _).1 hz
    have h2 : δ * ((2 * N : ℕ) * z) ∈ B.L.lattice := by
      have e : δ * ((2 * N : ℕ) * z) = (δ * N * z + B.ω₀ / 2) + (δ * N * z + B.ω₀ / 2) - B.ω₀ := by
        push_cast; ring
      rw [e]
      exact B.L.lattice.sub_mem (B.L.lattice.add_mem h1 h1) B.omega_mem
    obtain ⟨y, -, hy⟩ := (hmem _).1 ((hmemL _).1 h2)
    refine ⟨2 * N, Nat.mul_pos two_pos (Nat.pos_of_ne_zero hN0), Nat.Coprime.mul_left ?_ hcop, ?_⟩
    · exact (Nat.coprime_primes Nat.prime_two hqp).2 (Ne.symm hq2)
    · exact (hOK _).2 ⟨y, mul_left_cancel₀ hδ0 hy⟩

  have hkey : ∀ z w : ℂ, Formalism.L2.Th1.F.herm B.L (δ * N * z) (δ * N * w) = N * h1 D.host.d z w := by
    intro z w
    have hc : δ * conj δ = (Complex.normSq δ : ℂ) := Complex.mul_conj δ
    have hδn : (Complex.normSq δ : ℂ) ≠ 0 := by exact_mod_cast (Complex.normSq_pos.2 hδ0).ne'
    have hsc : ((Real.sqrt D.host.d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsd.ne'
    have hA0 : ((Complex.normSq δ * (N : ℝ) * Real.sqrt D.host.d / 2 : ℝ) : ℂ) ≠ 0 := by
      have : 0 < Complex.normSq δ * (N : ℝ) * Real.sqrt D.host.d / 2 := by
        have := Complex.normSq_pos.2 hδ0
        have : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN0
        positivity
      exact_mod_cast this.ne'
    have hs2 : (2 / ((Real.sqrt D.host.d : ℝ) : ℂ)) * ((Real.sqrt D.host.d : ℝ) : ℂ) = 2 := by
      field_simp
    rw [Formalism.L2.Th1.F.herm, hAF, h1, div_eq_iff hA0]
    simp only [map_mul, Complex.conj_natCast]
    push_cast
    linear_combination ((N : ℂ) ^ 2 * z * conj w) * hc - ((N : ℂ) ^ 2 * z * conj w * (Complex.normSq δ : ℂ) / 2) * hs2
  have hlaw' : ∀ x, InOK D.host.d x → ∀ z, G (z + x) * (Complex.exp ((Real.pi : ℂ) * Complex.I * ((Complex.normSq x : ℝ) : ℂ)) * Complex.exp (-(Real.pi : ℂ) * h1 D.host.d z x - (Real.pi : ℂ) / 2 * h1 D.host.d x x)) ^ N = G z := by
    intro x hx z
    obtain ⟨o, ho⟩ := (hOK x).1 hx
    have hω : δ * N * x ∈ B.L.lattice := by
      refine (hmemL _).2 ((hmem _).2 ⟨(N : 𝓞 D.host.K) * o, cc.mul_mem_right _ (Ideal.absNorm_mem cc), ?_⟩)
      rw [ho]; push_cast; rw [map_mul, map_natCast]; ring
    have hl := hlaw _ hω (δ * N * z)
    rw [← Formalism.L2.Th1.F.thetaZeroCharacter] at hl
    rw [← Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.char_eq (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.hst B) B.omega_mem (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.hθ B)
      (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.hθ' B) (by omega) _ hω, hkey, hkey] at hl
    have ha : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.aa B.L D.host.d (δ * N * x) = 1 ∨
        Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.aa B.L D.host.d (δ * N * x) = -1 := by
      rw [Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.char_eq
        (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.hst B) B.omega_mem
        (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.hθ B)
        (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.hθ' B) (by omega) _ hω]
      exact Formalism.L2.Th1.H.th0Char_pm B.L B.ω₀ _ B.omega_mem hω
    have hq1 : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.q1 B.L D.host.d (δ * N * x) = N * Complex.normSq x := by
      rw [Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.q1, hkey, h1, Complex.mul_conj]
      have : ((N : ℂ) * (((2 / Real.sqrt D.host.d : ℝ) : ℂ) * ((Complex.normSq x : ℝ) : ℂ))).re
          = N * (2 / Real.sqrt D.host.d) * Complex.normSq x := by
        rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_re]; ring
      rw [this]; field_simp
    have hapow : Complex.exp ((Real.pi : ℂ) * Complex.I * ((Complex.normSq x : ℝ) : ℂ)) ^ N
        = Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.aa B.L D.host.d (δ * N * x) := by
      rw [Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.aa, hq1, ← Complex.exp_nat_mul]
      congr 1; push_cast; ring
    have e1 : G (z + x) = B.th0 (δ * N * z + δ * N * x) := by
      simp only [hG]; congr 1; ring
    have e2 : G z = B.th0 (δ * N * z) := rfl
    rw [e1, e2, Base.th0, hl, mul_pow, hapow, ← Complex.exp_nat_mul]
    set a := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.aa B.L D.host.d (δ * N * x)
    have haa : a * a = 1 := by rcases ha with h | h <;> rw [h] <;> norm_num
    have hE : Complex.exp ((Real.pi : ℂ) * (N * h1 D.host.d z x) + (Real.pi : ℂ) * (N * h1 D.host.d x x) / 2)
        * Complex.exp (N * (-(Real.pi : ℂ) * h1 D.host.d z x - (Real.pi : ℂ) / 2 * h1 D.host.d x x)) = 1 := by
      rw [← Complex.exp_add, ← Complex.exp_zero]; congr 1; ring
    linear_combination (Complex.exp ((Real.pi : ℂ) * (N * h1 D.host.d z x) + (Real.pi : ℂ) * (N * h1 D.host.d x x) / 2)
        * Complex.exp (N * (-(Real.pi : ℂ) * h1 D.host.d z x - (Real.pi : ℂ) / 2 * h1 D.host.d x x))
        * Formalism.L2.Th1.F.th0 B.L (B.ω₀ / 2) (δ * N * z)) * haa
      + (Formalism.L2.Th1.F.th0 B.L (B.ω₀ / 2) (δ * N * z)) * hE

  have hbd : Bd 1 (hat ι (PowerSeries.C (Ω / ι δ₀) * logS) G) := by
    have := GlobalTheory.T.cpSeries_bounded_theta_level_value_one D.host.d q M (Ω / ι δ₀) θ G N hdp hd16 hsplit hq2 hMOK hMch hTh hGd hG0 hlaw' hzer
    rwa [hMι] at this
  have hmom := GlobalTheory.T.jetsAreBoundedMeasureMoments_of_chart_coeff_bound q ι (Ω / ι δ₀) G hGd hbd
  have hspan : LatInt ι (Ω / ι δ₀) (lamOf D ⊤ 1) G := by
    refine GlobalTheory.T.latticeJetsAreBoundedMoments_of_span_imagQuadratic q ι ℂ D.host.d (Ω / ι δ₀) (lamOf D ⊤ 1) Unit (fun _ => (1 : ℂ)) G hdp hd16 hsplit ?_ ?_
    · intro x hx
      obtain ⟨y, -, hy⟩ := (hmem1 x).1 hx
      refine ⟨1, Nat.coprime_one_left _, fun _ => x, fun _ => (hOK x).2 ⟨y, by rw [hy, one_mul]⟩, ?_⟩
      simp
    · convert hmom using 2
      simp
  have hδN : δ * (N : ℂ) ≠ 0 := mul_ne_zero hδ0 hNc
  have hpull := GlobalTheory.T.latticeJetsAreBoundedMoments_pullback q ι ℂ ℂ (Ω / ι δ₀) (lamOf D ⊤ 1) (lamOf D cc δ)
    ((δ * N)⁻¹ • ContinuousLinearMap.id ℂ ℂ) G hGd.contDiff ?_ hspan
  · convert hpull using 1
    funext z
    simp only [hG, smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    congr 1
    field_simp
  · intro x hx
    obtain ⟨y, -, hy⟩ := (hmem x).1 hx
    refine ⟨N, hcop, (hmem1 _).2 ⟨y, trivial, ?_⟩⟩
    simp only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, nsmul_eq_mul, hy]
    field_simp

end GlobalTheory.MomN
end
end
end
