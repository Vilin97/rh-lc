module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CountableDoubledHermitianLagrangiansStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LagrangiansTransverseEqGraphsRationalUnitaryStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SiegelWeilLagrangianTermStronglyMeasurableStatement
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaPairingInvariant
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Tactic.Linter.Style
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Prod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaPairingInvariantStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

theorem _root_.GlobalTheory.T.theta_pairing_invariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), IsWeilDatumO ψ V W χV χW om → IsCovolOne (ratL W V) μ 𝓕 → ∀ (p : GA D V × GA D W) (a b : WO V W → ℂ), IsThetaFunO ψ V W a → IsThetaFunO ψ V W b → thetaIP μ 𝓕 (om p a) (om p b) = thetaIP μ 𝓕 a b := by
  first | exact @GlobalTheory.WeilPairing.thetaInner_weilRep | exact GlobalTheory.WeilPairing.thetaInner_weilRep | (intros; apply GlobalTheory.WeilPairing.thetaInner_weilRep <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldTsumIntegralFundamentalDomain

section

@[expose] public section

open MeasureTheory

namespace GlobalTheory

section
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] {ν : Measure G} [ν.IsHaarMeasure]
    {Γ : Subgroup G} [Countable Γ] {𝓖 : Set G}

theorem fundamentalDomain_lintegral_unfold_left (h𝓖 : IsFundamentalDomain Γ 𝓖 ν) {a b P : G → ℂ}
    (hb : ∀ γ ∈ Γ, ∀ g, b (γ * g) = b g) (hbm : Measurable b) (hPm : Measurable P) (x : G) :
    ∫⁻ y in 𝓖, ∑' γ : Γ, ‖P (x⁻¹ * (γ : G)⁻¹ * y)‖ₑ * ‖a x‖ₑ * ‖b y‖ₑ ∂ν
      = ∫⁻ g, ‖P g‖ₑ * ‖a x‖ₑ * ‖b (x * g)‖ₑ ∂ν := by
  rw [lintegral_tsum (fun γ => by fun_prop)]
  set F : G → ENNReal := fun g => ‖P (x⁻¹ * g)‖ₑ * ‖a x‖ₑ * ‖b g‖ₑ with hF
  have key : ∀ γ : Γ, ∀ y, ‖P (x⁻¹ * (γ : G)⁻¹ * y)‖ₑ * ‖a x‖ₑ * ‖b y‖ₑ = F (γ⁻¹ • y) := by
    intro γ y
    have h1 : γ⁻¹ • y = (γ : G)⁻¹ * y := by simp [Subgroup.smul_def]
    rw [hF, h1]
    show _ = ‖P (x⁻¹ * ((γ : G)⁻¹ * y))‖ₑ * ‖a x‖ₑ * ‖b ((γ : G)⁻¹ * y)‖ₑ
    rw [hb _ (Γ.inv_mem γ.2)]; simp only [mul_assoc]
  simp_rw [key]
  rw [← h𝓖.lintegral_eq_tsum' F, ← lintegral_mul_left_eq_self _ x]
  simp [hF]

theorem fundamentalDomain_integral_unfold_left (h𝓖 : IsFundamentalDomain Γ 𝓖 ν) {a b P : G → ℂ}
    (hb : ∀ γ ∈ Γ, ∀ g, b (γ * g) = b g) (hbm : Measurable b) (hPm : Measurable P) (x : G)
    (hfin : ∫⁻ g, ‖P g‖ₑ * ‖a x‖ₑ * ‖b (x * g)‖ₑ ∂ν ≠ ⊤) :
    ∑' γ : Γ, ∫ y in 𝓖, star (a x) * b y * P (x⁻¹ * (γ : G)⁻¹ * y) ∂ν
      = ∫ g, star (a x) * b (x * g) * P g ∂ν := by
  set F : G → ℂ := fun g => star (a x) * b g * P (x⁻¹ * g) with hF
  have hFi : Integrable F ν := by
    refine ⟨by fun_prop, ?_⟩
    unfold HasFiniteIntegral
    rw [← lintegral_mul_left_eq_self _ x]
    refine lt_of_le_of_lt (le_of_eq ?_) hfin.lt_top
    refine lintegral_congr (fun g => ?_)
    have hs : ‖star (a x)‖ₑ = ‖a x‖ₑ := by rw [enorm_eq_nnnorm, enorm_eq_nnnorm, nnnorm_star]
    simp only [hF, enorm_mul, hs, inv_mul_cancel_left]
    ring
  have key : ∀ γ : Γ, ∀ y, star (a x) * b y * P (x⁻¹ * (γ : G)⁻¹ * y) = F (γ⁻¹ • y) := by
    intro γ y
    have h1 : γ⁻¹ • y = (γ : G)⁻¹ * y := by simp [Subgroup.smul_def]
    rw [hF, h1]
    show _ = star (a x) * b ((γ : G)⁻¹ * y) * P (x⁻¹ * ((γ : G)⁻¹ * y))
    rw [hb _ (Γ.inv_mem γ.2)]; simp only [mul_assoc]
  simp_rw [key]
  rw [← h𝓖.integral_eq_tsum' F hFi, ← integral_mul_left_eq_self F x]
  simp [hF]

theorem unfold_tsum_fundamentalDomain (ν : Measure G) [ν.IsHaarMeasure]
    (Γ : Subgroup G) [Countable Γ] (𝓖 : Set G) (h𝓖 : IsFundamentalDomain Γ 𝓖 ν) (a b P : G → ℂ)
    (ha : Continuous a) (hbc : Continuous b) (hb : ∀ γ ∈ Γ, ∀ g, b (γ * g) = b g)
    (hP : StronglyMeasurable P)
    (hfin : ∫⁻ g₁ in 𝓖, ∫⁻ g₂ in 𝓖, ∑' γ : Γ, ‖P (g₁⁻¹ * (γ : G)⁻¹ * g₂)‖ₑ * ‖a g₁‖ₑ * ‖b g₂‖ₑ ∂ν ∂ν ≠ ⊤) :
    Integrable (fun g => P g * ∫ x in 𝓖, star (a x) * b (x * g) ∂ν) ν ∧
    ∑' γ : Γ, ∫ p in 𝓖 ×ˢ 𝓖, star (a p.1) * b p.2 * P (p.1⁻¹ * (γ : G)⁻¹ * p.2) ∂(ν.prod ν) =
      ∫ g, P g * (∫ x in 𝓖, star (a x) * b (x * g) ∂ν) ∂ν := by
  have ham : Measurable a := ha.measurable
  have hbm : Measurable b := hbc.measurable
  have hPm : Measurable P := hP.measurable
  have hs : ∀ z : ℂ, ‖star z‖ₑ = ‖z‖ₑ := fun z => by rw [enorm_eq_nnnorm, enorm_eq_nnnorm, nnnorm_star]
  set μ := ν.restrict 𝓖 with hμ

  have hT : ∫⁻ x, ∫⁻ g, ‖P g‖ₑ * ‖a x‖ₑ * ‖b (x * g)‖ₑ ∂ν ∂μ ≠ ⊤ := by
    rw [← lintegral_congr (fun x => fundamentalDomain_lintegral_unfold_left h𝓖 hb hbm hPm (a := a) x)]
    exact hfin
  set k : G → G → ℂ := fun x g => star (a x) * b (x * g) * P g with hk
  have hkm : Measurable (Function.uncurry k) := by
    simp only [hk, Function.uncurry_def]; fun_prop
  have hki : Integrable (Function.uncurry k) (μ.prod ν) := by
    refine ⟨hkm.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    rw [lintegral_prod _ (by fun_prop)]
    refine lt_of_le_of_lt (le_of_eq ?_) hT.lt_top
    refine lintegral_congr (fun x => lintegral_congr (fun g => ?_))
    simp only [hk, Function.uncurry_apply_pair, enorm_mul, hs]
    ring
  refine ⟨?_, ?_⟩
  · have h1 := hki.swap.integral_prod_left
    refine h1.congr (Filter.Eventually.of_forall (fun g => ?_))
    simp only [hk, Function.comp_apply, Prod.swap_prod_mk, Function.uncurry_apply_pair]
    rw [integral_mul_const, mul_comm]

  · set f : Γ → G × G → ℂ := fun γ z => star (a z.1) * b z.2 * P (z.1⁻¹ * (γ : G)⁻¹ * z.2) with hf
    have hfm : ∀ γ, Measurable (f γ) := fun γ => by simp only [hf]; fun_prop
    have hfe : ∀ γ x y, ‖f γ (x, y)‖ₑ = ‖P (x⁻¹ * (γ : G)⁻¹ * y)‖ₑ * ‖a x‖ₑ * ‖b y‖ₑ := by
      intro γ x y; simp only [hf, enorm_mul, hs]; ring
    have hsum : ∑' γ : Γ, ∫⁻ x, ∫⁻ y, ‖f γ (x, y)‖ₑ ∂μ ∂μ ≠ ⊤ := by
      rw [← lintegral_tsum (fun γ => ((hfm γ).enorm.lintegral_prod_right').aemeasurable)]
      have hx : ∀ x, ∑' γ : Γ, ∫⁻ y, ‖f γ (x, y)‖ₑ ∂μ
          = ∫⁻ y, ∑' γ : Γ, ‖P (x⁻¹ * (γ : G)⁻¹ * y)‖ₑ * ‖a x‖ₑ * ‖b y‖ₑ ∂μ := fun x => by
        rw [← lintegral_tsum (f := fun γ y => ‖f γ (x, y)‖ₑ)
          (fun γ => ((hfm γ).comp measurable_prodMk_left).enorm.aemeasurable)]
        simp only [hfe]
      rw [lintegral_congr hx]
      exact hfin
    have hfi : ∀ γ, Integrable (f γ) (μ.prod μ) := fun γ =>
      ⟨(hfm γ).aestronglyMeasurable, by
        unfold HasFiniteIntegral
        rw [lintegral_prod _ (hfm γ).enorm.aemeasurable]
        exact lt_of_le_of_lt (ENNReal.le_tsum (f := fun γ : Γ => ∫⁻ x, ∫⁻ y, ‖f γ (x, y)‖ₑ ∂μ ∂μ) γ)
          hsum.lt_top⟩
    have lhs : ∀ γ : Γ, ∫ p in 𝓖 ×ˢ 𝓖, star (a p.1) * b p.2 * P (p.1⁻¹ * (γ : G)⁻¹ * p.2) ∂(ν.prod ν)
        = ∫ x, ∫ y, f γ (x, y) ∂μ ∂μ := by
      intro γ; rw [← Measure.prod_restrict, ← integral_prod _ (hfi γ)]
    rw [tsum_congr lhs, ← integral_tsum (fun γ => (hfi γ).integral_prod_left.aestronglyMeasurable)
      (ne_top_of_le_ne_top hsum (ENNReal.tsum_le_tsum fun γ =>
        lintegral_mono fun x => enorm_integral_le_lintegral_enorm _))]
    have hae : ∀ᵐ x ∂μ, ∫⁻ g, ‖P g‖ₑ * ‖a x‖ₑ * ‖b (x * g)‖ₑ ∂ν < ⊤ :=
      ae_lt_top (show Measurable (fun z : G × G => ‖P z.2‖ₑ * ‖a z.1‖ₑ * ‖b (z.1 * z.2)‖ₑ) by
        fun_prop).lintegral_prod_right' hT
    have step : (∫ x, ∑' γ : Γ, ∫ y, f γ (x, y) ∂μ ∂μ) = ∫ x, ∫ g, k x g ∂ν ∂μ :=
      integral_congr_ae (hae.mono fun x hx => fundamentalDomain_integral_unfold_left h𝓖 hb hbm hPm x hx.ne)
    rw [step, integral_integral_swap hki]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [hk]
    rw [integral_mul_const, mul_comm]
end
end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldTsumIntegralFundamentalDomainStatement

section

@[expose] public section

open MeasureTheory

theorem _root_.GlobalTheory.T.unfold_tsum_integral_fundamentalDomain : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsHaarMeasure]
    (Γ : Subgroup G) [Countable Γ] (𝓖 : Set G), IsFundamentalDomain Γ 𝓖 ν → ∀ (a b P : G → ℂ), Continuous a → Continuous b →
    (∀ γ ∈ Γ, ∀ g, b (γ * g) = b g) → StronglyMeasurable P →
    ∫⁻ g₁ in 𝓖, ∫⁻ g₂ in 𝓖, ∑' γ : Γ, ‖P (g₁⁻¹ * (γ : G)⁻¹ * g₂)‖ₑ * ‖a g₁‖ₑ * ‖b g₂‖ₑ ∂ν ∂ν ≠ ⊤ →
    Integrable (fun g => P g * ∫ x in 𝓖, star (a x) * b (x * g) ∂ν) ν ∧
    ∑' γ : Γ, ∫ p in 𝓖 ×ˢ 𝓖, star (a p.1) * b p.2 * P (p.1⁻¹ * (γ : G)⁻¹ * p.2) ∂(ν.prod ν) =
      ∫ g, P g * (∫ x in 𝓖, star (a x) * b (x * g) ∂ν) ∂ν := by
  first | exact @GlobalTheory.unfold_tsum_fundamentalDomain | exact GlobalTheory.unfold_tsum_fundamentalDomain | (intros; apply GlobalTheory.unfold_tsum_fundamentalDomain <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LagrangianGraphsSumEqMatrixCoeffIntegral

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

namespace GlobalTheory.RawLift

theorem graph_term_of_termMove {D : D7} (hTM : TermMove D) {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D}
    {χV χW : (AE D)ˣ →* Circle} {om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {νV : Measure (GA D V)}
    {𝓗 : Set (GA D V)} {νW : Measure (GA D W)} {𝓖 : Set (GA D W)} {μ : Measure (WO V W)} {𝓕 : Set (WO V W)}
    {fr : Lag W → Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E}
    (hS : SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr) {f₁ f₂ : WO V W → ℂ} (h₁ : IsThetaFunO ψ V W f₁)
    (h₂ : IsThetaFunO ψ V W f₂) {γ : GA D W} (hγ : γ ∈ GQ W) {c : Matrix (Fin W.rank) (Fin W.rank) D.host.E}
    (hc : mt W γ = c.map (incA D)) {Y : Lag W} (hY : IsLagFrame W Y (1, c)) (g₁ g₂ : GA D W) :
    lagTerm μ 𝓕 (fr Y) (om (1, g₁) f₁) (om (1, g₂) f₂) = thetaIP μ 𝓕 (om (1, g₁⁻¹ * γ⁻¹ * g₂) f₂) f₁ := by
  have hmul : ∀ p q (f : WO V W → ℂ), om p (om q f) = om (p * q) f := fun p q f => by rw [map_mul]; rfl
  have p₁ := hS.weil.om_pres (1, g₁) f₁ h₁
  have p₂ := hS.weil.om_pres (1, g₂) f₂ h₂
  obtain ⟨hfr, hg⟩ := hTM ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS _ _ p₁ p₂
  have e1 : om (1, g₁⁻¹) (om (1, γ⁻¹) (om (1, g₂) f₂)) = om (1, g₁⁻¹ * γ⁻¹ * g₂) f₂ := by
    rw [hmul, hmul, Prod.mk_mul_mk, Prod.mk_mul_mk, one_mul, one_mul, mul_assoc]
  have e2 : om (1, g₁⁻¹) (om (1, g₁) f₁) = f₁ := by
    rw [hmul, Prod.mk_mul_mk, one_mul, inv_mul_cancel, ← Prod.one_eq_mk, map_one, Module.End.one_apply]
  rw [← hfr Y (1, c) hY, (hg γ hγ c hc).2,
    ← GlobalTheory.T.theta_pairing_invariant D ψ V W χV χW om μ 𝓕 hS.weil hS.covol (1, g₁⁻¹) _ _ (hS.weil.om_pres (1, γ⁻¹) _ p₂) p₁, e1, e2]


open scoped GlobalTheory.GaugeEx in
theorem rallis_graphs : ∀ D : D7, EisAbs D → TermMove D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (νV : Measure (GA D V)) (𝓗 : Set (GA D V)) (νW : Measure (GA D W)) (𝓖 : Set (GA D W)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)) (fr : Lag W → Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E), SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ (θ : InfFam D), IsInfFam θ → ∀ (f₁ f₂ : WO V W → ℂ) (φ₁ φ₂ : GA D W → ℂ), IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → IsAutFunSm θ W φ₁ → IsCuspFun W φ₁ → IsAutFunSm θ W φ₂ → IsCuspFun W φ₂ → Integrable (fun g => thetaIP μ 𝓕 (om (1, g) f₂) f₁ * ∫ x in 𝓖, star (φ₁ x) * φ₂ (x * g) ∂νW) νW ∧ ∑' Y : {Y : Lag W // Y.1.comap (LinearMap.inl D.host.E _ _) = ⊥}, ∫ p in 𝓖 ×ˢ 𝓖, star (φ₁ p.1) * φ₂ p.2 * lagTerm μ 𝓕 (fr Y.1) (om (1, p.1) f₁) (om (1, p.2) f₂) ∂(νW.prod νW) = ∫ g, thetaIP μ 𝓕 (om (1, g) f₂) f₁ * (∫ x in 𝓖, star (φ₁ x) * φ₂ (x * g) ∂νW) ∂νW := by
  intro D hEA hTM ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS θ hθ f₁ f₂ φ₁ φ₂ hf₁ hf₂ ha₁ hc₁ ha₂ hc₂
  haveI := hS.haarW
  obtain ⟨e, he⟩ := GlobalTheory.T.lagrangians_transverse_eq_graphs_rational_unitary D W
  haveI : Countable (Lag W) := GlobalTheory.T.countable_doubled_hermitian_lagrangians D W
  haveI : Countable (GQ W) := e.injective.countable
  choose c hc hcf using he
  let P : GA D W → ℂ := fun g => thetaIP μ 𝓕 (om (1, g) f₂) f₁
  have hT : ∀ (γ : GQ W) (p : GA D W × GA D W),
      lagTerm μ 𝓕 (fr (e γ).1) (om (1, p.1) f₁) (om (1, p.2) f₂) = P (p.1⁻¹ * (γ : GA D W)⁻¹ * p.2) :=
    fun γ p => graph_term_of_termMove hTM hS hf₁ hf₂ γ.2 (hc γ) (hcf γ) p.1 p.2
  have hPm : StronglyMeasurable P := by
    have h := GlobalTheory.T.siegelWeil_lagrangian_term_stronglyMeasurable D ψ V W χV χW om μ 𝓕 hS.weil hS.covol f₁ f₂ hf₁ hf₂ (1, 1)
    have hcont : Continuous fun g : GA D W => ((1 : GA D W), g) := continuous_const.prodMk continuous_id
    convert h.comp_measurable hcont.measurable using 1
    funext g
    simp only [Function.comp_apply]
    rw [lagTerm_one_one, ← Prod.one_eq_mk, map_one, Module.End.one_apply]
  have hfin : ∫⁻ g₁ in 𝓖, ∫⁻ g₂ in 𝓖, ∑' γ : GQ W, ‖P (g₁⁻¹ * (γ : GA D W)⁻¹ * g₂)‖ₑ * ‖φ₁ g₁‖ₑ * ‖φ₂ g₂‖ₑ ∂νW ∂νW ≠ ⊤ := by
    refine ne_top_of_le_ne_top (hEA ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS θ hθ f₁ f₂ hf₁ hf₂ φ₁ φ₂ ha₁ hc₁ ha₂ hc₂) ?_
    refine lintegral_mono fun g₁ => lintegral_mono fun g₂ => ?_
    have hinj : Function.Injective fun γ : GQ W => (e γ).1 := Subtype.val_injective.comp e.injective
    refine le_trans (le_of_eq ?_) (ENNReal.tsum_comp_le_tsum_of_injective hinj
      (fun Y => ‖lagTerm μ 𝓕 (fr Y) (om (1, g₁) f₁) (om (1, g₂) f₂)‖ₑ * ‖φ₁ g₁‖ₑ * ‖φ₂ g₂‖ₑ))
    refine tsum_congr fun γ => ?_
    rw [← hT γ (g₁, g₂)]
  obtain ⟨hI, hE⟩ := GlobalTheory.T.unfold_tsum_integral_fundamentalDomain νW (GQ W) 𝓖 hS.fdW φ₁ φ₂ P ha₁.cont ha₂.cont ha₂.left hPm hfin
  refine ⟨hI, ?_⟩
  refine ((e.tsum_eq (fun Y : {Y : Lag W // Y.1.comap (LinearMap.inl D.host.E _ _) = ⊥} =>
    ∫ p in 𝓖 ×ˢ 𝓖, star (φ₁ p.1) * φ₂ p.2 * lagTerm μ 𝓕 (fr Y.1) (om (1, p.1) f₁) (om (1, p.2) f₂) ∂(νW.prod νW))).symm.trans ?_).trans hE
  refine tsum_congr fun γ => ?_
  congr 1
  funext p
  rw [hT γ p]

end GlobalTheory.RawLift
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LagrangianGraphsSumEqMatrixCoeffIntegralStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

theorem _root_.GlobalTheory.T.lagrangianGraphs_sum_eq_matrixCoeff_integral : ∀ D : D7, EisAbs D → TermMove D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (νV : Measure (GA D V)) (𝓗 : Set (GA D V)) (νW : Measure (GA D W)) (𝓖 : Set (GA D W)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)) (fr : Lag W → Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E), SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ (θ : InfFam D), IsInfFam θ → ∀ (f₁ f₂ : WO V W → ℂ) (φ₁ φ₂ : GA D W → ℂ), IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → IsAutFunSm θ W φ₁ → IsCuspFun W φ₁ → IsAutFunSm θ W φ₂ → IsCuspFun W φ₂ → Integrable (fun g => thetaIP μ 𝓕 (om (1, g) f₂) f₁ * ∫ x in 𝓖, star (φ₁ x) * φ₂ (x * g) ∂νW) νW ∧ ∑' Y : {Y : Lag W // Y.1.comap (LinearMap.inl D.host.E _ _) = ⊥}, ∫ p in 𝓖 ×ˢ 𝓖, star (φ₁ p.1) * φ₂ p.2 * lagTerm μ 𝓕 (fr Y.1) (om (1, p.1) f₁) (om (1, p.2) f₂) ∂(νW.prod νW) = ∫ g, thetaIP μ 𝓕 (om (1, g) f₂) f₁ * (∫ x in 𝓖, star (φ₁ x) * φ₂ (x * g) ∂νW) ∂νW := by
  first | exact @GlobalTheory.RawLift.rallis_graphs | exact GlobalTheory.RawLift.rallis_graphs | (intros; apply GlobalTheory.RawLift.rallis_graphs <;> assumption)
end
end
