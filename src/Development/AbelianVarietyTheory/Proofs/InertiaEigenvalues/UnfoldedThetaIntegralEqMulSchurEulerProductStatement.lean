module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurDir
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormRapidKernelSmoothSpanSmoothCuspidalBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
public import GroundTheory.AutomorphicForms.ReductionMeasure
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqColGenMulBlkU
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsUnitaryOfCharIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralRankinSelbergThetaEqWhittakerUnfolding
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNormRsHatLeConst
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaIntegralUpperMspan
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergThetaIntegralSmoothSpanEqToRealLintStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedWhittakerIntegralEqEulerProductSchurSumsStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsFundamentalDomainRationalUpperUnitriangu

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped ENNReal nonZeroDivisors

namespace GlobalTheory.CellDec

theorem exists_isFundamentalDomain_NE : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (μ : Measure (GA E a)),
    ∃ 𝓕₀ : Set (GA E a), IsFundamentalDomain (GlobalTheory.CellDec.NE E a) 𝓕₀ μ := by
  intro E _ _ a μ
  haveI : DiscreteTopology (GlobalTheory.CellDec.NE E a) :=
    GlobalTheory.MirTower.discrete_of_le_range (Subgroup.map_le_range _ _)
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  haveI : SecondCountableTopology (Matrix (Fin a) (Fin a) (Ad E)) :=
    inferInstanceAs (SecondCountableTopology (Fin a → Fin a → Ad E))
  haveI : SecondCountableTopology (Matrix (Fin a) (Fin a) (Ad E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  haveI : SecondCountableTopology (GA E a) :=
    Units.isEmbedding_embedProduct.secondCountableTopology
  exact GlobalTheory.FundDomDiscrete.exists_isFundamentalDomain _ μ

end GlobalTheory.CellDec
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsFundamentalDomainRationalUpperUnitrianguStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped ENNReal nonZeroDivisors

theorem _root_.GlobalTheory.T.exists_isFundamentalDomain_rationalUpperUnitriangular : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (μ : Measure (GA E a)),
    ∃ 𝓕₀ : Set (GA E a), IsFundamentalDomain (GlobalTheory.CellDec.NE E a) 𝓕₀ μ := by
  first | exact @GlobalTheory.CellDec.exists_isFundamentalDomain_NE | exact GlobalTheory.CellDec.exists_isFundamentalDomain_NE | (intros; apply GlobalTheory.CellDec.exists_isFundamentalDomain_NE <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralRankinSelbergThetaEqWhittakerUnfoldingStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped ENNReal nonZeroDivisors

theorem _root_.GlobalTheory.T.lintegral_rankinSelbergTheta_eq_whittakerUnfolding : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ℓ : Fin a), (ℓ : ℕ) + 1 = a →
    ∀ (π : CuspSub E a), π.IsUnitary → ∀ (F : GA E a → ℂ), F ∈ GlobalTheory.JSW.mspanR π →
    ∀ (Φ : (Fin a → Cinf E) → ℂ), Continuous Φ → HasCompactSupport Φ → tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E ℓ →
    ∀ (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 𝓕₀ : Set (GA E a)),
    IsFundamentalDomain (ratGL E a).range 𝓕 μ → IsFundamentalDomain (GlobalTheory.CellDec.NE E a) 𝓕₀ μ → ∀ x : ℝ,
    ∫⁻ g in 𝓕, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖GlobalTheory.RSTheta.rsPsi ℓ F F Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)‖ₑ) * ENNReal.ofReal ((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x) ∂μ =
    ∫⁻ g in 𝓕₀, ‖GlobalTheory.RSTheta.rsPsi ℓ (GlobalTheory.JSW.whit F) (GlobalTheory.JSW.whit F) Φ J η g (g.val ℓ)‖ₑ * ENNReal.ofReal ((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x) ∂μ := by
  first | (exact @GlobalTheory.RSUnfold.lintegral_theta_eq_whit) | (exact GlobalTheory.RSUnfold.lintegral_theta_eq_whit) | (intros; apply GlobalTheory.RSUnfold.lintegral_theta_eq_whit  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralThetaSelfCuspRapidSpanNeTop

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped ENNReal nonZeroDivisors ComplexConjugate
open GlobalTheory.ThetaPoisson GlobalTheory.RSTheta

namespace GlobalTheory.RSThetaSelf

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem rsPsi_self_eq_norm (ℓ : Fin a) (F : GA E a → ℂ) {Φ : (Fin a → Cinf E) → ℂ}
    (hΦ : ∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (g : GA E a)
    (y : Fin a → Ad E) : rsPsi ℓ F F Φ J η g y = ((‖rsPsi ℓ F F Φ J η g y‖ : ℝ) : ℂ) := by
  have key : ∀ z w t : ℂ, 0 ≤ w.re → w.im = 0 → (t = 0 ∨ t = 1) →
      z * conj z * w * t = ((‖z * conj z * w * t‖ : ℝ) : ℂ) := by
    intro z w t h1 h2 ht
    have hw : w = ((w.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [h2])
    rcases ht with rfl | rfl
    · simp
    · rw [mul_one, Complex.mul_conj, hw, ← Complex.ofReal_mul, Complex.norm_real,
        Real.norm_of_nonneg (mul_nonneg (Complex.normSq_nonneg z) h1)]
  simp only [rsPsi, thetaFn, rsInf]
  refine key _ _ _ (hΦ _).1 (hΦ _).2 ?_
  by_cases h : (fun i => pFin E (y i)) - η ∈ latt a J <;> simp [h]

theorem lintegral_ne_top : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ℓ : Fin a) (π : CuspSub E a) (ω : HChar E),
    ω.IsUnitary → π.HasCentChar ω → ∀ F : GA E a → ℂ, F ∈ GlobalTheory.JSW.mspanR π →
    ∀ (Φ : (Fin a → Cinf E) → ℂ), ContDiff ℝ (⊤ : ℕ∞) Φ → HasCompactSupport Φ → tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E ℓ →
    (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) →
    ∀ (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 : Set (GA E a)),
    IsFundamentalDomain (ratGL E a).range 𝓕 μ → ∀ x : ℝ, 1 < x →
    ∫⁻ g in 𝓕, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖GlobalTheory.RSTheta.rsPsi ℓ F F Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)‖ₑ) * ENNReal.ofReal ((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x) ∂μ ≠ ⊤ := by
  intro E _ _ _ a ℓ π ω hω hc F hF Φ hΦ hcs hs hpos J η μ _ 𝓕 h𝓕 x hx
  have hπ : π.IsUnitary := ⟨ω, hω, CuspSub.hasCentral_iff.2 hc⟩
  obtain ⟨φ, rfl, hw⟩ := GlobalTheory.JSW.mspanR_words GlobalTheory.CuspOrth.cuspFormsBounded hπ F hF
  have hcont : Continuous φ.1 := by simpa [GlobalTheory.JSW.word_nil] using (hw []).2.cont
  have hrsm : φ ∈ GlobalTheory.RSThetaLowM.rsm π := hF
  obtain ⟨hsum, hup, -⟩ := GlobalTheory.RSThetaM.theta_integral_upper_mspan E a ℓ π π hπ hπ φ φ (Or.inr hF) (Or.inr hF) Φ
    hΦ.continuous hcs hs J η μ 𝓕 h𝓕
  have hlow := (GlobalTheory.RSThetaLowM.integral_low_eq J η hπ hπ hrsm hrsm hcont hcont ⟨hΦ, hcs, hs⟩ h𝓕 (s := (x : ℂ))
    (by simpa using hx)).1
  have hpt : ∀ g : GA E a, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0},
      ‖rsPsi ℓ φ.1 φ.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)‖ₑ) *
        ENNReal.ofReal ((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x) =
      ENNReal.ofReal ((∑' ξ : {ξ : Fin a → E // ξ ≠ 0},
        ‖rsPsi ℓ φ.1 φ.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)‖) *
          (ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x) := by
    intro g
    rw [ENNReal.ofReal_mul (tsum_nonneg fun _ => norm_nonneg _),
      ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (hsum g)]
    simp only [ofReal_norm_eq_enorm]
  have hlow' : IntegrableOn (fun g : GA E a => (∑' ξ : {ξ : Fin a → E // ξ ≠ 0},
      ‖rsPsi ℓ φ.1 φ.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)‖) *
        (ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x) (𝓕 ∩ GlobalTheory.RSThetaLow.lowSet E a) μ := by
    refine hlow.norm.congr (.of_forall fun g => ?_)
    have e : ∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, rsPsi ℓ φ.1 φ.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val) =
        (((∑' ξ : {ξ : Fin a → E // ξ ≠ 0},
          ‖rsPsi ℓ φ.1 φ.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)‖ : ℝ)) : ℂ) := by
      rw [Complex.ofReal_tsum]
      exact tsum_congr fun ξ => rsPsi_self_eq_norm ℓ φ.1 hpos J η g _
    simp only
    rw [← GlobalTheory.RSThetaLow.tsum_rsPsi_eq_tsum_ne_zero J η _ _ hs g, norm_mul, e, Complex.norm_real,
      Real.norm_of_nonneg (tsum_nonneg fun _ => norm_nonneg _),
      Complex.norm_cpow_eq_rpow_re_of_pos (ideleModule E _).2, Complex.ofReal_re]
  have h1 := (hup x).lintegral_lt_top
  have h2 := hlow'.lintegral_lt_top
  have hsub : 𝓕 ⊆ (𝓕 ∩ {g | 1 ≤ (ideleModule E (GeneralLinearGroup.det g) : ℝ)}) ∪ (𝓕 ∩ GlobalTheory.RSThetaLow.lowSet E a) := by
    intro g hg
    rcases le_total 1 (ideleModule E (GeneralLinearGroup.det g) : ℝ) with h | h
    · exact Or.inl ⟨hg, h⟩
    · exact Or.inr ⟨hg, h⟩
  rw [lintegral_congr hpt]
  exact ne_of_lt ((lintegral_mono_set hsub).trans_lt ((lintegral_union_le _ _ _).trans_lt (ENNReal.add_lt_top.2 ⟨h1, h2⟩)))

end GlobalTheory.RSThetaSelf

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralThetaSelfCuspRapidSpanNeTopStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped ENNReal nonZeroDivisors

theorem _root_.GlobalTheory.T.lintegral_theta_self_cusp_rapid_span_ne_top : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ℓ : Fin a) (π : CuspSub E a) (ω : HChar E),
    ω.IsUnitary → π.HasCentChar ω → ∀ F : GA E a → ℂ, F ∈ GlobalTheory.JSW.mspanR π →
    ∀ (Φ : (Fin a → Cinf E) → ℂ), ContDiff ℝ (⊤ : ℕ∞) Φ → HasCompactSupport Φ → tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E ℓ →
    (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) →
    ∀ (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 : Set (GA E a)),
    IsFundamentalDomain (ratGL E a).range 𝓕 μ → ∀ x : ℝ, 1 < x →
    ∫⁻ g in 𝓕, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖GlobalTheory.RSTheta.rsPsi ℓ F F Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)‖ₑ) * ENNReal.ofReal ((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x) ∂μ ≠ ⊤ := by
  first | exact @GlobalTheory.RSThetaSelf.lintegral_ne_top | exact GlobalTheory.RSThetaSelf.lintegral_ne_top | (intros; apply GlobalTheory.RSThetaSelf.lintegral_ne_top <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedThetaIntegralEqMulSchurEulerProduct

section

@[expose] public section

open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped ENNReal nonZeroDivisors

namespace GlobalTheory.RSEulerId

theorem thetaZ_eq_mul_eulD : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CG E a), 1 ≤ a → π.IsUnitary →
    ∀ T : Finset (HeightOneSpectrum (𝓞 E)), UnrOutside T π →
    ∃ (α : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin a → ℂˣ) (ℓ : Fin a) (Φ : (Fin a → Cinf E) → ℂ)
      (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (π₀ : CuspSub E a) (ω : HChar E) (φ : Sm E a),
      (∀ w, Finset.univ.val.map (α w) = sat π w) ∧ CG.mk π₀ = π ∧ ω.IsUnitary ∧ π₀.HasCentChar ω ∧
      (φ ∈ π₀.V ∨ φ.1 ∈ GlobalTheory.JSW.mspanR π₀) ∧ φ ≠ 0 ∧
      ContDiff ℝ (⊤ : ℕ∞) Φ ∧ HasCompactSupport Φ ∧ tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E ℓ ∧
      (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) ∧ Φ ≠ 0 ∧
      ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 : Set (GA E a)), IsFundamentalDomain (ratGL E a).range 𝓕 μ →
        ∃ H : ℝ → ℝ, ContinuousWithinAt H (Set.Ioi 1) 1 ∧ 0 < H 1 ∧ ∀ x : ℝ, 1 < x → 0 < H x ∧
          GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal)
                       (fun w i => ((α w i : ℂˣ) : ℂ)) x ≠ ⊤ ∧
          GlobalTheory.RSPole.thetaZ μ 𝓕 ℓ φ.1 φ.1 Φ J η x =
            ((H x * (GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal)
              (fun w i => ((α w i : ℂˣ) : ℂ)) x).toReal : ℝ) : ℂ) := by
  intro E _ _ _ a π ha hu T hT
  obtain ⟨α, ℓ, Φ, J, η, π₀, ω, φ, hℓ, hα, hπ₀, hω, hc, hφ, hφ0, hΦs, hΦc, hΦr, hΦp, hΦ0, hcore⟩ :=
    GlobalTheory.T.unfoldedWhittakerIntegral_eq_eulerProduct_schurSums E a π ha hu T hT
  have hF : φ.1 ∈ GlobalTheory.JSW.mspanR π₀ := hφ.elim (fun h => Submodule.mem_sInf.2 fun _ hS => hS.1 φ h) id
  have hπu : π₀.IsUnitary := ⟨ω, hω, CuspSub.hasCentral_iff.2 hc⟩
  have hFc : Continuous φ.1 := by
    obtain ⟨ψ, hψ, hw⟩ := GlobalTheory.JSW.mspanR_words GlobalTheory.CuspOrth.cuspFormsBounded hπu φ.1 hF
    have h0 := (hw []).2
    rw [GlobalTheory.JSW.word_nil, hψ] at h0
    exact h0.cont
  refine ⟨α, ℓ, Φ, J, η, π₀, ω, φ, hα, hπ₀, hω, hc, hφ, hφ0, hΦs, hΦc, hΦr, hΦp, hΦ0, fun μ _ 𝓕 h𝓕 => ?_⟩
  obtain ⟨𝓕₀, h𝓕₀⟩ := GlobalTheory.T.exists_isFundamentalDomain_rationalUpperUnitriangular E a μ
  obtain ⟨H, hHc, hH1, hH⟩ := hcore μ 𝓕₀ h𝓕₀
  refine ⟨H, hHc, hH1, fun x hx => ?_⟩
  obtain ⟨hHx, heq⟩ := hH x hx
  have hU := GlobalTheory.T.lintegral_rankinSelbergTheta_eq_whittakerUnfolding E a ℓ hℓ π₀ hπu φ.1 hF Φ hΦs.continuous hΦc hΦr J η μ 𝓕 𝓕₀ h𝓕 h𝓕₀ x
  have hfin := GlobalTheory.T.lintegral_theta_self_cusp_rapid_span_ne_top E a ℓ π₀ ω hω hc φ.1 hF Φ hΦs hΦc hΦr hΦp J η μ 𝓕 h𝓕 x hx
  have hZ := GlobalTheory.T.rankinSelbergThetaIntegral_smoothSpan_eq_toReal_lintegral E a ℓ π₀ φ.1 hF hFc Φ hΦs.continuous hΦr hΦp J η μ 𝓕 h𝓕 x hfin
  rw [hU, heq] at hfin hZ
  refine ⟨hHx, fun h => hfin (by rw [h, ENNReal.mul_top (ENNReal.ofReal_pos.2 hHx).ne']), ?_⟩
  rw [hZ, ENNReal.toReal_mul, ENNReal.toReal_ofReal hHx.le]

end GlobalTheory.RSEulerId
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedThetaIntegralEqMulSchurEulerProductStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped ENNReal nonZeroDivisors

theorem _root_.GlobalTheory.T.unfolded_theta_integral_eq_mul_schur_euler_product : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CG E a), 1 ≤ a → π.IsUnitary →
    ∀ T : Finset (HeightOneSpectrum (𝓞 E)), UnrOutside T π →
    ∃ (α : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin a → ℂˣ) (ℓ : Fin a) (Φ : (Fin a → Cinf E) → ℂ)
      (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (π₀ : CuspSub E a) (ω : HChar E) (φ : Sm E a),
      (∀ w, Finset.univ.val.map (α w) = sat π w) ∧ CG.mk π₀ = π ∧ ω.IsUnitary ∧ π₀.HasCentChar ω ∧
      (φ ∈ π₀.V ∨ φ.1 ∈ GlobalTheory.JSW.mspanR π₀) ∧ φ ≠ 0 ∧
      ContDiff ℝ (⊤ : ℕ∞) Φ ∧ HasCompactSupport Φ ∧ tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E ℓ ∧
      (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) ∧ Φ ≠ 0 ∧
      ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 : Set (GA E a)), IsFundamentalDomain (ratGL E a).range 𝓕 μ →
        ∃ H : ℝ → ℝ, ContinuousWithinAt H (Set.Ioi 1) 1 ∧ 0 < H 1 ∧ ∀ x : ℝ, 1 < x → 0 < H x ∧
          GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal)
                       (fun w i => ((α w i : ℂˣ) : ℂ)) x ≠ ⊤ ∧
          GlobalTheory.RSPole.thetaZ μ 𝓕 ℓ φ.1 φ.1 Φ J η x =
            ((H x * (GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal)
              (fun w i => ((α w i : ℂˣ) : ℂ)) x).toReal : ℝ) : ℂ) := by
  first | (exact @GlobalTheory.RSEulerId.thetaZ_eq_mul_eulD) | (exact GlobalTheory.RSEulerId.thetaZ_eq_mul_eulD) | (intros; apply GlobalTheory.RSEulerId.thetaZ_eq_mul_eulD  <;> assumption)
end
end
