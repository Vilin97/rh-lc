module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapIntertwinesCoreHeisenbergOperators
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousIntegrand
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiKernelEqWeilRepresentationApply
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteVolumeAdelicUnitaryQuotient
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryQuotientHeightComparableWittDecompositionStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryQuotientHeightOrthogonalSumComparableStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilKernelFunctionalSuperpositionIsTameStatement
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
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
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumHermitianPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiActionsMatchThroughLinkMap
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaTensorRuleOrthogonalSumSource
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepConjSourceLineEqTargetLine
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LinkedLineVectorsInvertibleOnThetaFunctionsStatement
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameFunctionalVacuumIrreducibilityStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VanishingDescendsBesselToFourierJacobiStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiPeriodAllDataIsTameThetaFunctional

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.PerAllTame

variable {D : D7}

theorem tame_congr {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {ℓ ℓ' : (WO S T → ℂ) → ℂ}
    (h : Tame ψ S T ℓ) (e : ∀ f, IsThetaFunO ψ S T f → ℓ' f = ℓ f) : Tame ψ S T ℓ' := by
  have hθ : ∀ w f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (heisO ψ S T w f) :=
    fun w f hf => GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf w
  refine ⟨fun f f' hf hf' => ?_, fun c f hf => ?_, fun f hf => ?_, fun f hf => ?_, fun f hf m _ α hα hs => ?_⟩
  · rw [e _ (GlobalTheory.OrientedHeis.theta_add hf hf'), e _ hf, e _ hf', h.add f f' hf hf']
  · rw [e _ (GlobalTheory.OrientedHeis.theta_smul c hf), e _ hf, h.smul c f hf]
  · have hfun : (fun w => ℓ' (heisO ψ S T w f)) = fun w => ℓ (heisO ψ S T w f) :=
      funext fun w => e _ (hθ w f hf)
    rw [hfun]
    exact h.cont f hf
  · obtain ⟨C, hC⟩ := h.bdd f hf
    exact ⟨C, fun w => (e _ (hθ w f hf)).symm ▸ hC w⟩
  · have hfun : (fun w => α w * ℓ' (heisO ψ S T w f)) = fun w => α w * ℓ (heisO ψ S T w f) :=
      funext fun w => by rw [e _ (hθ w f hf)]
    rw [hfun, e _ hs]
    exact h.sup f hf m α hα hs

theorem decay_of_le {V : HSp D} {F : GA D V → ℂ} (hF : RapidDec V F) (C : ℝ) (a k : ℕ) :
    ∃ C' : ℝ, ∀ (g : GA D V) (t : ℝ), 0 ≤ t → t ≤ C * quotHeight V g ^ a → ‖F g‖ * t ^ k ≤ C' := by
  obtain ⟨-, -, hd⟩ := hF
  obtain ⟨C₀, hC₀⟩ := hd (a * k)
  refine ⟨|C| ^ k * max C₀ 0, fun g t ht0 htle => ?_⟩
  have hq : (0 : ℝ) ≤ quotHeight V g ^ a := pow_nonneg (le_trans zero_le_one (one_le_quotHeight V g)) a
  have ht : t ≤ |C| * quotHeight V g ^ a := htle.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hq)
  calc ‖F g‖ * t ^ k ≤ ‖F g‖ * (|C| * quotHeight V g ^ a) ^ k :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht0 ht k) (norm_nonneg _)
    _ = |C| ^ k * (‖F g‖ * quotHeight V g ^ (a * k)) := by rw [mul_pow, ← pow_mul]; ring
    _ ≤ |C| ^ k * max C₀ 0 :=
        mul_le_mul_of_nonneg_left ((hC₀ g).trans (le_max_left _ _)) (pow_nonneg (abs_nonneg _) _)

theorem perAll_tame : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ σ : ℕ) (B : BesL D σ) (J : JacL D ρ) (χ χ' : (AE D)ˣ →* Circle) (om₀ : Om B.V₀ J.W₀), IsWeilDatumO ψ B.V₀ J.W₀ χ χ' om₀ → ∀ (φ : GA D B.A → ℂ) (G : GA D J.W → ℂ), RapidDec B.A φ → RapidDec J.W G → Tame ψ B.V₀ J.W₀ (J.perAll ψ B om₀ φ G) := by
  intro D ψ ρ σ B J χ χ' om₀ hW φ G hφ hG
  have hψ : IsStdChar D ψ (-1) := hW.std
  have hψc : Continuous ψ := hψ.1.1
  have hψn : ∀ x, ‖ψ x‖ = 1 := hψ.1.2.1
  have hGc : Continuous G := hG.2.1
  have hφc : Continuous φ := hφ.2.1
  haveI : SecondCountableTopology (flagN J.d) := TopologicalSpace.Subtype.secondCountableTopology _
  have hF : J.v0.μ J.v0.𝓕 < ⊤ :=
    GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol J.W₀ J.v0.μ J.v0.𝓕 J.v0.haar J.v0.fund
  have hFA : B.vA.μ B.vA.𝓕 < ⊤ :=
    GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol B.A B.vA.μ B.vA.𝓕 B.vA.haar B.vA.fund
  have hN : J.vN.ν J.vN.𝓝 = 1 := J.vN.unit.2.2
  haveI : IsFiniteMeasure (J.v0.μ.restrict J.v0.𝓕) := isFiniteMeasure_restrict.mpr hF.ne
  haveI : IsFiniteMeasure (B.vA.μ.restrict B.vA.𝓕) := isFiniteMeasure_restrict.mpr hFA.ne
  haveI : IsFiniteMeasure (J.vN.ν.restrict J.vN.𝓝) :=
    isFiniteMeasure_restrict.mpr (by rw [hN]; exact ENNReal.one_ne_top)
  have hpf : Continuous (psiFlag ψ J.d) := GlobalTheory.Unf.EvalCont.continuous_psiFlag hψc J.d
  have hcen : Continuous (cenT J.d B.L (yZero B.L ρ B.ζ)) := GlobalTheory.Unf.EvalCont.continuous_cenT J.d B.L _
  have hpt : Continuous (ptT J.d B.L (yZero B.L ρ B.ζ)) := GlobalTheory.Unf.EvalCont.continuous_ptT J.d B.L _
  have hn : Continuous fun y : (GA D J.W₀ × flagN J.d) × GA D B.A => (y.1.2 : GA D J.W) :=
    continuous_subtype_val.comp (continuous_snd.comp continuous_fst)
  have hh1 : Continuous fun y : (GA D J.W₀ × flagN J.d) × GA D B.A => y.1.1 :=
    continuous_fst.comp continuous_fst
  have hx : Continuous fun y : (GA D J.W₀ × flagN J.d) × GA D B.A => (y.1.2 : GA D J.W) * J.d.emb0 y.1.1 :=
    hn.mul (J.d.continuous_embed.comp hh1)
  have hgg : Continuous fun y : (GA D J.W₀ × flagN J.d) × GA D B.A => B.o.emb (y.2, 1) :=
    B.o.continuous_emb.comp (continuous_snd.prodMk continuous_const)
  have hww : Continuous fun y : (GA D J.W₀ × flagN J.d) × GA D B.A =>
      (B.o.resS J.W₀).symm (0, ptT J.d B.L (yZero B.L ρ B.ζ) (y.1.2 : GA D J.W)) :=
    (B.o.continuous_resS_symm J.W₀).comp (continuous_const.prodMk (hpt.comp hn))
  have hcc : Continuous fun y : (GA D J.W₀ × flagN J.d) × GA D B.A =>
      G ((y.1.2 : GA D J.W) * J.d.emb0 y.1.1) * star (psiFlag ψ J.d (y.1.2 : GA D J.W)) * φ y.2 *
        ψ (cenT J.d B.L (yZero B.L ρ B.ζ) (y.1.2 : GA D J.W)) :=
    (((hGc.comp hx).mul (hpf.comp hn).star).mul (hφc.comp continuous_snd)).mul (hψc.comp (hcen.comp hn))
  obtain ⟨C₁, a₁, hC₁⟩ := GlobalTheory.T.unitaryQuotientHeight_orthogonalSum_comparable D B.V₀ B.A B.L B.o
  obtain ⟨C₂, a₂, hC₂⟩ := GlobalTheory.T.unitaryQuotientHeight_comparable_wittDecomposition D J.W J.W₀ ρ J.d
  have key : ∀ k : ℕ, Integrable (fun y : (GA D J.W₀ × flagN J.d) × GA D B.A =>
      ‖G ((y.1.2 : GA D J.W) * J.d.emb0 y.1.1) * star (psiFlag ψ J.d (y.1.2 : GA D J.W)) * φ y.2 *
        ψ (cenT J.d B.L (yZero B.L ρ B.ζ) (y.1.2 : GA D J.W))‖ *
        (quotHeight B.V₀ (B.o.emb (y.2, 1)) * quotHeight J.W₀ y.1.1) ^ k)
      (((J.v0.μ.restrict J.v0.𝓕).prod (J.vN.ν.restrict J.vN.𝓝)).prod (B.vA.μ.restrict B.vA.𝓕)) := by
    intro k
    obtain ⟨K₁, hK₁⟩ := decay_of_le hφ C₁ a₁ k
    obtain ⟨K₂, hK₂⟩ := decay_of_le hG C₂ a₂ k
    have hq : Continuous fun y : (GA D J.W₀ × flagN J.d) × GA D B.A =>
        (quotHeight B.V₀ (B.o.emb (y.2, 1)) * quotHeight J.W₀ y.1.1) ^ k :=
      (((continuous_quotHeight B.V₀).comp hgg).mul ((continuous_quotHeight J.W₀).comp hh1)).pow k
    refine Integrable.mono' (integrable_const (K₁ * K₂)) (hcc.norm.mul hq).aestronglyMeasurable
      (ae_of_all _ fun y => ?_)
    have q1 : 0 ≤ quotHeight B.V₀ (B.o.emb (y.2, 1)) := zero_le_one.trans (one_le_quotHeight _ _)
    have q2 : 0 ≤ quotHeight J.W₀ y.1.1 := zero_le_one.trans (one_le_quotHeight _ _)
    have b1 := hK₁ y.2 _ q1 (hC₁ y.2).2
    have b2 := hK₂ _ _ q2 (hC₂ y.1.2 y.1.2.2 y.1.1).1
    have n1 : ‖star (psiFlag ψ J.d (y.1.2 : GA D J.W))‖ = 1 := by
      rw [norm_star]; unfold psiFlag psiE; exact hψn _
    have p1 : 0 ≤ ‖φ y.2‖ * quotHeight B.V₀ (B.o.emb (y.2, 1)) ^ k := by positivity
    have p2 : 0 ≤ ‖G ((y.1.2 : GA D J.W) * J.d.emb0 y.1.1)‖ * quotHeight J.W₀ y.1.1 ^ k := by positivity
    rw [Real.norm_of_nonneg (by positivity), norm_mul, norm_mul, norm_mul, n1, hψn, mul_pow]
    calc ‖G ((y.1.2 : GA D J.W) * J.d.emb0 y.1.1)‖ * 1 * ‖φ y.2‖ * 1 *
          (quotHeight B.V₀ (B.o.emb (y.2, 1)) ^ k * quotHeight J.W₀ y.1.1 ^ k)
        = (‖φ y.2‖ * quotHeight B.V₀ (B.o.emb (y.2, 1)) ^ k) *
          (‖G ((y.1.2 : GA D J.W) * J.d.emb0 y.1.1)‖ * quotHeight J.W₀ y.1.1 ^ k) := by ring
      _ ≤ K₁ * K₂ := mul_le_mul b1 b2 p2 (p1.trans b1)
  obtain ⟨hint, htame⟩ := GlobalTheory.T.weilKernelFunctional_superposition_isTame D ψ B.V₀ J.W₀ χ χ' om₀ hW ((GA D J.W₀ × flagN J.d) × GA D B.A)
    (((J.v0.μ.restrict J.v0.𝓕).prod (J.vN.ν.restrict J.vN.𝓝)).prod (B.vA.μ.restrict B.vA.𝓕))
    (fun y => G ((y.1.2 : GA D J.W) * J.d.emb0 y.1.1) * star (psiFlag ψ J.d (y.1.2 : GA D J.W)) * φ y.2 *
        ψ (cenT J.d B.L (yZero B.L ρ B.ζ) (y.1.2 : GA D J.W)))
    (fun y => B.o.emb (y.2, 1)) (fun y => y.1.1)
    (fun y => (B.o.resS J.W₀).symm (0, ptT J.d B.L (yZero B.L ρ B.ζ) (y.1.2 : GA D J.W)))
    hcc.measurable hgg hh1 hww key
  refine tame_congr hψ htame fun Ξ hΞ => ?_
  have hI := hint Ξ hΞ
  rw [MeasureTheory.integral_prod _ hI, MeasureTheory.integral_prod _ hI.integral_prod_left]
  simp only [JacL.perAll, fjAll, fjAllFun,
    GlobalTheory.Unf.fjKer_eq_om_apply D ψ J.W J.W₀ B.V₀ B.A B.L ρ J.d B.o B.ζ χ χ' om₀ hW Ξ hΞ,
    ← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae (ae_of_all _ fun h => ?_)
  refine MeasureTheory.integral_congr_ae (ae_of_all _ fun n => ?_)
  refine MeasureTheory.integral_congr_ae (ae_of_all _ fun h₀ => ?_)
  dsimp only
  ring

end GlobalTheory.PerAllTame

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiPeriodAllDataIsTameThetaFunctionalStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

theorem _root_.GlobalTheory.T.fourierJacobiPeriod_all_data_isTameThetaFunctional : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ σ : ℕ) (B : BesL D σ) (J : JacL D ρ) (χ χ' : (AE D)ˣ →* Circle) (om₀ : Om B.V₀ J.W₀), IsWeilDatumO ψ B.V₀ J.W₀ χ χ' om₀ → ∀ (φ : GA D B.A → ℂ) (G : GA D J.W → ℂ), RapidDec B.A φ → RapidDec J.W G → Tame ψ B.V₀ J.W₀ (J.perAll ψ B om₀ φ G) := by
  first | exact @GlobalTheory.PerAllTame.perAll_tame | exact GlobalTheory.PerAllTame.perAll_tame | (intros; apply GlobalTheory.PerAllTame.perAll_tame <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodAllDataProductsEqFourierJacobiPeriod

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.LinkProd

variable {D : D7}

theorem star_psi {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (a : AF D.host.F) : star (ψ a) = ψ (-a) := by
  have h1 : ‖ψ a‖ = 1 := hψ.1.2.1 a
  have h2 : ψ a * star (ψ a) = 1 := by
    rw [Complex.star_def, Complex.mul_conj', h1]; simp
  have h3 : ψ a * ψ (-a) = 1 := by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have h0 : ψ a ≠ 0 := by intro h; rw [h, zero_mul] at h3; exact zero_ne_one h3
  exact mul_left_cancel₀ h0 (h2.trans h3.symm)

theorem heisO_at_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) (f : WO S T → ℂ) :
    heisO ψ S T w f 0 = f w := by
  simp [heisO, symplOH_zero_left]

theorem lnk_point {L L' : HSp D} {ζ : Fin L.rank → D.host.E} {ζ' : Fin L'.rank → D.host.E} (l : Lnk L ζ L' ζ')
    {W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) (n : GA D W) :
    l.κ W₀ (ptS d L' (zEll L' ρ ζ') n) = ptT d L (yZero L ρ ζ) n ∧
      cenT d L (yZero L ρ ζ) n = -cenS d L' (zEll L' ρ ζ') n := by
  constructor
  · have h : (rat l.τ : Mx D L.rank L'.rank) ⬝ zEll L' ρ ζ' = yZero L ρ ζ := by
      have h0 : ratV (-ζ) = -ratV ζ := funext fun i => map_neg (incA D) _
      rw [yZero, zEll, zEll, Matrix.mul_vecMulVec, ← ratV_mulVec, l.map, h0, Matrix.neg_vecMulVec]
    rw [GlobalTheory.Unf.LinkPoint.ptT_eq, Lnk.κ, ptS, d.extX_apply, ← h]
    simp only [Matrix.mul_assoc]
  · have hN : D.host.xi0 * star D.host.xi0 ≠ 0 :=
      mul_ne_zero (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D) (star_ne_zero.2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D))
    rw [GlobalTheory.Unf.LinkPoint.cenT_eq, GlobalTheory.Unf.LinkPoint.neg_cenS_eq, yZero, adj_neg, Matrix.mul_neg, Matrix.neg_mul,
      Matrix.mul_neg, neg_neg, GlobalTheory.Unf.LinkPoint.gram_zEll, GlobalTheory.Unf.LinkPoint.gram_zEll,
      smul_smul, ← map_mul, l.norm, inv_mul_cancel_left₀ hN]

theorem perAll_box_eq_per : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesL D ρ) (J : JacL D ρ) (s : StBF ψ B J), ∀ (L' : HSp D) (ζ' : Fin L'.rank → D.host.E), IsLineVec L' ζ' → ∀ (l : Lnk B.L B.ζ L' ζ') (χA χz χ' : (AE D)ˣ →* Circle) (oma : Om B.A J.W₀) (omz : Om J.W₀ L'), s.χV = χA * χz → IsWeilDatumO ψ B.A J.W₀ χA s.χW oma → IsWeilDatumO ψ J.W₀ L' χ' χz omz → ∀ (φ : GA D B.A → ℂ) (G : GA D J.W → ℂ) Ξ₁ Ξ₂, IsThetaFunO ψ B.A J.W₀ Ξ₁ → IsThetaFunO ψ B.L J.W₀ Ξ₂ → J.perAll ψ B s.om₀ φ G (B.o.boxS J.W₀ Ξ₁ Ξ₂) = J.per ψ ζ' omz (liftT oma B.vA.μ B.vA.𝓕 φ Ξ₁) G (fun w => star (Ξ₂ (l.κ J.W₀ w))) := by
  intro D ψ ρ B J s L' ζ' hL' l χA χz χ' oma omz hχ hoa hoz φ G Ξ₁ Ξ₂ hΞ₁ hΞ₂
  have hψ := hoa.std
  have hrk : B.L.rank = L'.rank := B.line.1.trans hL'.1.symm
  have hres : ResEta D χz B.L.rank := by rw [hrk]; exact hoz.resT
  obtain ⟨omL, hoL⟩ := GlobalTheory.WeilDatumExistence.weilDatumExists D B.L J.W₀ ψ χz s.χW hψ hoz.hecT hoa.hecT hres hoa.resT
  obtain ⟨hg, -⟩ := GlobalTheory.T.linkedLineVectors_invertible_on_theta_functions D ψ hψ B.L L' J.W₀ B.ζ ζ' B.line hL' l
  have hg' : l.τᴴ ⬝ (B.L.gram ⬝ l.τ) = (((1 : ℤ) : D.host.E) * (D.host.xi0 * star D.host.xi0)) • L'.gram := by
    rw [Int.cast_one, one_mul]; exact hg
  have hcl := (GlobalTheory.ConjLine.conj_line D ψ B.L L' J.W₀ l.τ hrk hg' χz s.χW χ' omL omz hoL hoz Ξ₂ hΞ₂).2
  have hTS := GlobalTheory.TensorSrc.tensorSource D ψ hψ B.V₀ B.A B.L B.o J.W₀
  have hw0 : IsWeilDatumO ψ B.V₀ J.W₀ (χA * χz) s.χW s.om₀ := hχ ▸ s.weil₀
  have hbt : IsThetaFunO ψ B.V₀ J.W₀ (B.o.boxS J.W₀ Ξ₁ Ξ₂) := hTS.box_theta Ξ₁ Ξ₂ hΞ₁ hΞ₂
  have key : ∀ n ∈ flagN J.d, ∀ h, ∫ h₀ in B.vA.𝓕, φ h₀ * fjKer ψ J.d B.o B.ζ s.om₀ (B.o.boxS J.W₀ Ξ₁ Ξ₂) h₀ n h ∂B.vA.μ =
      liftT oma B.vA.μ B.vA.𝓕 φ Ξ₁ h * star (thetaJS ψ J.d ζ' omz (fun w => star (Ξ₂ (l.κ J.W₀ w))) n h) := by
    intro n _ h
    obtain ⟨hp, hc⟩ := lnk_point l J.d n
    have e1 : ∀ h₀, φ h₀ * fjKer ψ J.d B.o B.ζ s.om₀ (B.o.boxS J.W₀ Ξ₁ Ξ₂) h₀ n h =
        oma (h₀, h) Ξ₁ 0 * φ h₀ * (ψ (cenT J.d B.L (yZero B.L ρ B.ζ) n) * omL (1, h) Ξ₂ (ptT J.d B.L (yZero B.L ρ B.ζ) n)) := by
      intro h₀
      rw [GlobalTheory.Unf.fjKer_eq_om_apply D ψ J.W J.W₀ B.V₀ B.A B.L ρ J.d B.o B.ζ _ _ s.om₀ s.weil₀ _ hbt,
        hTS.om_box χA χz s.χW s.om₀ oma omL hw0 hoa hoL h₀ 1 h Ξ₁ Ξ₂ hΞ₁ hΞ₂]
      simp only [OrthDec.boxS, AddEquiv.apply_symm_apply]
      ring
    simp_rw [e1]
    rw [integral_mul_const, liftT_apply]
    congr 1
    have hcl' : omz (h, 1) (fun w => star (Ξ₂ (l.κ J.W₀ w))) = fun w => star (omL (1, h) Ξ₂ (l.κ J.W₀ w)) := hcl h
    rw [thetaJS, jacS, hcl', Pi.smul_apply, smul_eq_mul, heisO_at_zero, star_mul', star_star, star_psi hψ, hp, hc]
  unfold JacL.perAll JacL.per fjAll fjSrc
  congr 1
  funext h
  congr 1
  funext n
  rw [fjAllFun, fjSrcFun, key n.1 n.2 h]
  ring

end GlobalTheory.LinkProd

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodAllDataProductsEqFourierJacobiPeriodStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

theorem _root_.GlobalTheory.T.periodAllData_products_eq_fourierJacobiPeriod : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesL D ρ) (J : JacL D ρ) (s : StBF ψ B J), ∀ (L' : HSp D) (ζ' : Fin L'.rank → D.host.E), IsLineVec L' ζ' → ∀ (l : Lnk B.L B.ζ L' ζ') (χA χz χ' : (AE D)ˣ →* Circle) (oma : Om B.A J.W₀) (omz : Om J.W₀ L'), s.χV = χA * χz → IsWeilDatumO ψ B.A J.W₀ χA s.χW oma → IsWeilDatumO ψ J.W₀ L' χ' χz omz → ∀ (φ : GA D B.A → ℂ) (G : GA D J.W → ℂ) Ξ₁ Ξ₂, IsThetaFunO ψ B.A J.W₀ Ξ₁ → IsThetaFunO ψ B.L J.W₀ Ξ₂ → J.perAll ψ B s.om₀ φ G (B.o.boxS J.W₀ Ξ₁ Ξ₂) = J.per ψ ζ' omz (liftT oma B.vA.μ B.vA.𝓕 φ Ξ₁) G (fun w => star (Ξ₂ (l.κ J.W₀ w))) := by
  first | exact @GlobalTheory.LinkProd.perAll_box_eq_per | exact GlobalTheory.LinkProd.perAll_box_eq_per | (intros; apply GlobalTheory.LinkProd.perAll_box_eq_per <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiPeriodGivesBesselPeriodOfLift

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.UpBessel

theorem upBF : ∀ D : D7, UpBF D := by
  intro D ψ ρ B J s 𝒮 Γ₀ K hL L' ζ' hζ' l χA χz χ' oma omz hχ hWa hWz φ G hφ hG hK Ξ₁ Ξ₂ hΞ₁ hΞ₂ hbox hJ
  by_contra hnone
  push_neg at hnone

  have hstd : IsStdChar D ψ (-1) := s.weil.std
  have hℓ : Tame ψ B.V₀ J.W₀ (J.perAll ψ B s.om₀ φ G) :=
    GlobalTheory.T.fourierJacobiPeriod_all_data_isTameThetaFunctional D ψ ρ ρ B J s.χV s.χW s.om₀ s.weil₀ φ G hφ hG

  have hkill : ∀ Φ ∈ 𝒮, J.perAll ψ B s.om₀ φ G (flBF s Φ) = 0 :=
    GlobalTheory.T.vanishing_descends_bessel_to_fourierJacobi D ψ ρ B J s 𝒮 Γ₀ K hL φ G hφ hG hK hnone
  obtain ⟨Φ₁, hΦ₁, hΦ₁ne⟩ := hL.ne

  have hall : ∀ f, VacG ψ B.V₀ J.W₀ Γ₀ f → J.perAll ψ B s.om₀ φ G f = 0 := by
    refine GlobalTheory.T.tame_functional_vacuum_irreducibility D ψ hstd B.V₀ J.W₀ Γ₀ _ hℓ (flBF s Φ₁) (hL.vac Φ₁ hΦ₁) hΦ₁ne ?_
    intro w hw
    have hcomm := (GlobalTheory.FlatHeis.flatAt_heisO D ψ hstd B.V B.V₀ J.W J.W₀ ρ ρ B.d J.d s.vS s.vT s.vU
      (xZero J.d) (yZero B.V₀ ρ (vecB B.o B.ζ)) Φ₁ (hL.theta Φ₁ hΦ₁)).2.1 w
    have hflat : flBF s (heisO ψ B.V J.W (B.d.ext0 J.W (J.d.inc0 B.V₀ w)) Φ₁) =
        heisO ψ B.V₀ J.W₀ w (flBF s Φ₁) := hcomm
    rw [← hflat]
    exact hkill _ (hL.core Φ₁ hΦ₁ w hw)

  have h0 := hall _ hbox
  rw [GlobalTheory.T.periodAllData_products_eq_fourierJacobiPeriod D ψ ρ B J s L' ζ' hζ' l χA χz χ' oma omz hχ hWa hWz φ G Ξ₁ Ξ₂ hΞ₁ hΞ₂] at h0
  exact hJ h0

end GlobalTheory.UpBessel
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiPeriodGivesBesselPeriodOfLiftStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

theorem _root_.GlobalTheory.T.fourierJacobi_period_gives_bessel_period_of_lift : ∀ D : D7, UpBF D := by
  first | exact @GlobalTheory.UpBessel.upBF | exact GlobalTheory.UpBessel.upBF | (intros; apply GlobalTheory.UpBessel.upBF <;> assumption)
end
end
