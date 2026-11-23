module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapIntertwinesCoreHeisenbergOperators
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingLevelsAndStepsHaarMeasuresExist
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaTensorRuleTargetOrthogonalSum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumPreservesThetaFundamentalDomainPairing
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
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUniqueIsProdMeasureFinAway
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumThetaJointlyContinuous
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteVolumeAdelicUnitaryQuotient
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentBesselCharacterLaws
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryQuotientHeightComparableWittDecompositionStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilKernelFunctionalSuperpositionIsTameStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepresentationThetaFunctionSupLeQuotientHeig
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameFunctionalVacuumIrreducibilityStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VanishingDescendsFourierJacobiToBesselStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselHandedFunctionProductEqCoreLiftMulPairing

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.HandProd

theorem handP_boxT : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (s : StFB ψ J B), ∀ (vL : VolM D B.L.rank J.W₀.rank) (χA χz : (AE D)ˣ →* Circle) (omb : Om J.W₀ B.A) (omz : Om J.W₀ B.L), s.χW = χA * χz → IsWeilDatumO ψ J.W₀ B.A s.χV χA omb → IsWeilDatumO ψ J.W₀ B.L s.χV χz omz → ∀ (φ : GA D J.W₀ → ℂ) Ξ₁ Φ' Φ₀, IsThetaFunO ψ J.W₀ B.A Ξ₁ → IsThetaFunO ψ J.W₀ B.L Φ' → IsThetaFunO ψ J.W₀ B.L Φ₀ → handP s vL omz φ Φ₀ (B.o.boxT J.W₀ Ξ₁ Φ') = thPair vL.μ vL.𝓕 Φ' Φ₀ • liftT omb J.v0.μ J.v0.𝓕 φ Ξ₁ := by
  intro D ψ σ J B s vL χA χz omb omz hχ hb hz φ Ξ₁ Φ' Φ₀ h1 h' h0
  have hW₀ : IsWeilDatumO ψ J.W₀ B.V₀ s.χV (χA * χz) s.om₀ := hχ ▸ s.weil₀
  have tt := GlobalTheory.TensorTargetRule.tensorTarget D ψ hb.std B.V₀ B.A B.L B.o J.W₀
  funext h₁
  have hpt : ∀ h₀, contractT B.o J.W₀ vL.μ vL.𝓕 (s.om₀ (h₀, B.o.emb (h₁, 1)) (B.o.boxT J.W₀ Ξ₁ Φ')) (omz (h₀, 1) Φ₀) 0 =
      omb (h₀, h₁) Ξ₁ 0 * thPair vL.μ vL.𝓕 Φ' Φ₀ := by
    intro h₀
    rw [tt.om_box s.χV χA χz s.om₀ omb omz hW₀ hb hz h₀ h₁ 1 Ξ₁ Φ' h1 h',
      ← GlobalTheory.WeilPairing.thPair_om_eq D ψ J.W₀ B.L s.χV χz omz hz vL (h₀, 1) Φ' Φ₀ h' h0]
    have e : (fun v => B.o.boxT J.W₀ (omb (h₀, h₁) Ξ₁) (omz (h₀, 1) Φ') ((B.o.resT J.W₀).symm (0, v))) =
        fun v => omb (h₀, h₁) Ξ₁ 0 * omz (h₀, 1) Φ' v := by
      funext v
      simp only [OrthDec.boxT, AddEquiv.apply_symm_apply]
    simp only [contractT, e, thPair]
    rw [← integral_const_mul]
    congr 1; funext w
    have ew := congrFun e w
    rw [ew]; ring
  simp only [handP, hpt, Pi.smul_apply, smul_eq_mul, liftT_apply]
  rw [← integral_const_mul]
  congr 1; funext h₀; ring

end GlobalTheory.HandProd

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselHandedFunctionProductEqCoreLiftMulPairingStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

theorem _root_.GlobalTheory.T.besselHandedFunction_product_eq_coreLift_mul_pairing : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (s : StFB ψ J B), ∀ (vL : VolM D B.L.rank J.W₀.rank) (χA χz : (AE D)ˣ →* Circle) (omb : Om J.W₀ B.A) (omz : Om J.W₀ B.L), s.χW = χA * χz → IsWeilDatumO ψ J.W₀ B.A s.χV χA omb → IsWeilDatumO ψ J.W₀ B.L s.χV χz omz → ∀ (φ : GA D J.W₀ → ℂ) Ξ₁ Φ' Φ₀, IsThetaFunO ψ J.W₀ B.A Ξ₁ → IsThetaFunO ψ J.W₀ B.L Φ' → IsThetaFunO ψ J.W₀ B.L Φ₀ → handP s vL omz φ Φ₀ (B.o.boxT J.W₀ Ξ₁ Φ') = thPair vL.μ vL.𝓕 Φ' Φ₀ • liftT omb J.v0.μ J.v0.𝓕 φ Ξ₁ := by
  first | exact @GlobalTheory.HandProd.handP_boxT | exact GlobalTheory.HandProd.handP_boxT | (intros; apply GlobalTheory.HandProd.handP_boxT <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodHandedDownIsTameThetaFunctional

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.HandTame

theorem integral_prod_four {α β γ δ : Type} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
    (μ₁ : Measure α) (μ₂ : Measure β) (μ₃ : Measure γ) (μ₄ : Measure δ) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    [IsFiniteMeasure μ₃] [IsFiniteMeasure μ₄]
    (F : α × β × γ × δ → ℂ) (hF : Integrable F (μ₁.prod (μ₂.prod (μ₃.prod μ₄)))) :
    ∫ y, F y ∂(μ₁.prod (μ₂.prod (μ₃.prod μ₄))) = ∫ a, ∫ b, ∫ c, ∫ d, F (a, b, c, d) ∂μ₄ ∂μ₃ ∂μ₂ ∂μ₁ := by
  rw [integral_prod _ hF]
  refine integral_congr_ae (hF.prod_right_ae.mono fun a ha => ?_)
  simp only
  rw [integral_prod _ ha]
  refine integral_congr_ae (ha.prod_right_ae.mono fun b hb => ?_)
  simp only
  rw [integral_prod _ hb]

theorem sfinite_of_finite {α : Type} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ] : SFinite μ := inferInstance

variable {D : D7}

theorem tame_congr {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {ℓ ℓ' : (WO S T → ℂ) → ℂ}
    (h : Tame ψ S T ℓ) (e : ∀ f, IsThetaFunO ψ S T f → ℓ' f = ℓ f) : Tame ψ S T ℓ' := by
  have hh : ∀ f, IsThetaFunO ψ S T f → ∀ w, ℓ' (heisO ψ S T w f) = ℓ (heisO ψ S T w f) := fun f hf w =>
    e _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf w)
  refine ⟨fun f f' hf hf' => ?_, fun c f hf => ?_, fun f hf => ?_, fun f hf => ?_, fun f hf m _ α hα hI => ?_⟩
  · rw [e _ (GlobalTheory.WeilVacMove.isTheta_add hf hf'), e _ hf, e _ hf', h.add f f' hf hf']
  · rw [e _ (GlobalTheory.WeilVacMove.isTheta_smul c hf), e _ hf, h.smul c f hf]
  · simp only [hh f hf]; exact h.cont f hf
  · simp only [hh f hf]; exact h.bdd f hf
  · simp only [hh f hf]; rw [e _ hI]; exact h.sup f hf m α hα hI

theorem rapid_core {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {G : GA D S → ℂ} (hG : RapidDec S G) (k : ℕ) :
    ∃ C : ℝ, ∀ n ∈ flagN d, ∀ h, ‖G (n * d.emb0 h)‖ * quotHeight S₀ h ^ k ≤ C := by
  obtain ⟨C, a, hC⟩ := GlobalTheory.T.unitaryQuotientHeight_comparable_wittDecomposition D S S₀ ρ d
  obtain ⟨C', hC'⟩ := hG.decay (a * k)
  refine ⟨|C| ^ k * C', fun n hn h => ?_⟩
  have h1 : quotHeight S₀ h ≤ |C| * quotHeight S (n * d.emb0 h) ^ a :=
    (hC n hn h).1.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (pow_pos (quotHeight_pos S _) a).le)
  calc ‖G (n * d.emb0 h)‖ * quotHeight S₀ h ^ k
      ≤ ‖G (n * d.emb0 h)‖ * (|C| * quotHeight S (n * d.emb0 h) ^ a) ^ k :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (quotHeight_pos S₀ h).le h1 k) (norm_nonneg _)
    _ = |C| ^ k * (‖G (n * d.emb0 h)‖ * quotHeight S (n * d.emb0 h) ^ (a * k)) := by rw [mul_pow, ← pow_mul]; ring
    _ ≤ |C| ^ k * C' := mul_le_mul_of_nonneg_left (hC' _) (by positivity)

theorem rapid_theta {ψ : AddChar (AF D.host.F) ℂ} {S L : HSp D} {χ χz : (AE D)ˣ →* Circle} {om : Om S L}
    (hom : IsWeilDatumO ψ S L χ χz om) {φ : GA D S → ℂ} (hφ : RapidDec S φ) {Φ₀ : WO S L → ℂ} (hΦ : IsThetaFunO ψ S L Φ₀)
    (k : ℕ) : ∃ C : ℝ, ∀ h v, ‖φ h‖ * ‖om (h, 1) Φ₀ v‖ * quotHeight S h ^ k ≤ C := by
  obtain ⟨C, a, hC⟩ := GlobalTheory.SupThetaGrowth.om_sup_quotHeight D ψ S L χ χz om hom Φ₀ hΦ
  obtain ⟨C', hC'⟩ := hφ.decay (a + k)
  refine ⟨|C| * C', fun h v => ?_⟩
  have h1 : ‖om (h, 1) Φ₀ v‖ ≤ |C| * quotHeight S h ^ a := by
    have := hC h 1 v
    rw [quotHeight_of_mem L (one_mem _), mul_one] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (pow_pos (quotHeight_pos S _) a).le)
  calc ‖φ h‖ * ‖om (h, 1) Φ₀ v‖ * quotHeight S h ^ k
      ≤ ‖φ h‖ * (|C| * quotHeight S h ^ a) * quotHeight S h ^ k :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)) (pow_pos (quotHeight_pos S _) k).le
    _ = |C| * (‖φ h‖ * quotHeight S h ^ (a + k)) := by ring
    _ ≤ |C| * C' := mul_le_mul_of_nonneg_left (hC' _) (abs_nonneg _)

theorem handP₂ : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (s : StFB ψ J B),
    ∀ (vL : VolM D B.L.rank J.W₀.rank) (χ χz : (AE D)ˣ →* Circle) (omz : Om J.W₀ B.L), IsWeilDatumO ψ J.W₀ B.L χ χz omz →
    ∀ (φ : GA D J.W₀ → ℂ) (G : GA D B.V → ℂ) (Φ₀ : WO J.W₀ B.L → ℂ), RapidDec J.W₀ φ → RapidDec B.V G →
    IsThetaFunO ψ J.W₀ B.L Φ₀ → Tame ψ J.W₀ B.V₀ fun Ξ => B.per ψ (handP s vL omz φ Φ₀ Ξ) G := by
  intro D ψ σ J B s vL χ χz omz homz φ G Φ₀ hφ hG hΦ
  have hψ := homz.std
  haveI : ∀ V : HSp D, SecondCountableTopology (GA D V) := fun V => (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V).2.1
  haveI : ∀ V : HSp D, BorelSpace (GA D V) := fun V => ⟨rfl⟩
  obtain ⟨-, -, i3, -, -, -⟩ := GlobalTheory.MixModel.lattice_Mx D B.L.rank J.W₀.rank
  haveI : SecondCountableTopology (WO J.W₀ B.L) := i3
  haveI : BorelSpace (WO J.W₀ B.L) := ⟨rfl⟩
  haveI : IsFiniteMeasure (B.vA.μ.restrict B.vA.𝓕) := isFiniteMeasure_restrict.2
    (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol B.A _ _ B.vA.haar B.vA.fund).ne
  haveI : IsFiniteMeasure (J.v0.μ.restrict J.v0.𝓕) := isFiniteMeasure_restrict.2
    (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol J.W₀ _ _ J.v0.haar J.v0.fund).ne
  haveI : IsFiniteMeasure (B.vN.ν.restrict B.vN.𝓝) := isFiniteMeasure_restrict.2 (by rw [B.vN.unit.2.2]; exact ENNReal.one_ne_top)
  haveI : IsFiniteMeasure (vL.μ.restrict vL.𝓕) := isFiniteMeasure_restrict.2 (by rw [vL.covol.2.2]; exact ENNReal.one_ne_top)
  let Y : Type := GA D B.A × flagN B.d × GA D J.W₀ × WO J.W₀ B.L
  let m : Measure Y := (B.vA.μ.restrict B.vA.𝓕).prod ((B.vN.ν.restrict B.vN.𝓝).prod
    ((J.v0.μ.restrict J.v0.𝓕).prod (vL.μ.restrict vL.𝓕)))
  haveI : IsFiniteMeasure m := by dsimp only [m]; infer_instance
  haveI : SFinite m := sfinite_of_finite m
  let c : Y → ℂ := fun y => G (y.2.1.1 * embA B.d B.o y.1) * star (psiBes ψ B.d 1 (vecB B.o B.ζ) y.2.1.1) *
    (φ y.2.2.1 * star (omz (y.2.2.1, 1) Φ₀ y.2.2.2))
  have hn : Continuous fun y : Y => (y.2.1.1 : GA D B.V) := continuous_subtype_val.comp (continuous_fst.comp continuous_snd)
  have h0 : Continuous fun y : Y => y.2.2.1 := continuous_fst.comp (continuous_snd.comp continuous_snd)
  have hv : Continuous fun y : Y => y.2.2.2 := continuous_snd.comp (continuous_snd.comp continuous_snd)
  have he : Continuous fun y : Y => B.o.emb (y.1, 1) := B.o.continuous_emb.comp (continuous_fst.prodMk continuous_const)
  have hw : Continuous fun y : Y => (B.o.resT J.W₀).symm (0, y.2.2.2) :=
    (B.o.continuous_resT_symm J.W₀).comp (continuous_const.prodMk hv)
  haveI := (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B.V).2.2.2.2.1
  have hJ : Continuous fun p : (GA D J.W₀ × GA D B.L) × WO J.W₀ B.L => omz p.1 Φ₀ p.2 :=
    (@GlobalTheory.Unf.jointCont_all D) ψ _ _ χ χz omz homz Φ₀ hΦ
  have hc : Continuous c :=
    ((hG.continuous.comp (hn.mul (B.d.continuous_embed.comp he))).mul
      (continuous_star.comp ((GlobalTheory.CharLaws.continuous_psiBes ψ B.d hψ.1.1 1 _).comp hn))).mul
      ((hφ.continuous.comp h0).mul (continuous_star.comp (hJ.comp ((h0.prodMk continuous_const).prodMk hv))))
  have hint : ∀ k : ℕ, Integrable
      (fun y : Y => ‖c y‖ * (quotHeight J.W₀ y.2.2.1 * quotHeight B.V₀ (B.o.emb (y.1, 1))) ^ k) m := by
    intro k
    obtain ⟨C₁, h₁⟩ := rapid_core B.d hG k
    obtain ⟨C₂, h₂⟩ := rapid_theta homz hφ hΦ k
    have hcc : Continuous fun y : Y => ‖c y‖ * (quotHeight J.W₀ y.2.2.1 * quotHeight B.V₀ (B.o.emb (y.1, 1))) ^ k :=
      hc.norm.mul ((((continuous_quotHeight _).comp h0).mul ((continuous_quotHeight _).comp he)).pow k)
    refine Integrable.of_bound hcc.measurable.aestronglyMeasurable (C₁ * C₂) (.of_forall fun y => ?_)
    have p1 := quotHeight_pos J.W₀ y.2.2.1
    have p2 := quotHeight_pos B.V₀ (B.o.emb (y.1, 1))
    have n1 : ‖psiBes ψ B.d 1 (vecB B.o B.ζ) y.2.1.1‖ = 1 := hψ.1.2.1 _
    rw [Real.norm_of_nonneg (by positivity)]
    have a1 := h₁ _ y.2.1.2 (B.o.emb (y.1, 1))
    have a2 := h₂ y.2.2.1 y.2.2.2
    calc ‖c y‖ * (quotHeight J.W₀ y.2.2.1 * quotHeight B.V₀ (B.o.emb (y.1, 1))) ^ k
        = (‖G (y.2.1.1 * B.d.emb0 (B.o.emb (y.1, 1)))‖ * quotHeight B.V₀ (B.o.emb (y.1, 1)) ^ k) *
          (‖φ y.2.2.1‖ * ‖omz (y.2.2.1, 1) Φ₀ y.2.2.2‖ * quotHeight J.W₀ y.2.2.1 ^ k) := by
          simp only [c, norm_mul, norm_star, n1, embA_apply, mul_pow]; ring
      _ ≤ C₁ * C₂ := mul_le_mul a1 a2 (by positivity) (le_trans (by positivity) a1)
  obtain ⟨hI, hT⟩ := GlobalTheory.T.weilKernelFunctional_superposition_isTame D ψ J.W₀ B.V₀ s.χV s.χW s.om₀ s.weil₀ Y m c (fun y => y.2.2.1) (fun y => B.o.emb (y.1, 1))
    (fun y => (B.o.resT J.W₀).symm (0, y.2.2.2)) hc.measurable h0 he hw hint
  refine tame_congr hψ hT fun f hf => ?_
  refine Eq.trans ?_ (integral_prod_four _ _ _ _ _ (hI f hf)).symm
  simp only [BesL.per, besPer, GlobalTheory.MixPer.besFun, handP, contractT, thPair]
  refine integral_congr_ae (.of_forall fun a => ?_)
  refine integral_congr_ae (.of_forall fun b => ?_)
  simp only
  rw [mul_assoc, ← integral_mul_const]
  refine integral_congr_ae (.of_forall fun x => ?_)
  simp only
  rw [← integral_const_mul, ← integral_mul_const]
  refine integral_congr_ae (.of_forall fun v => ?_)
  simp only [c]
  ring

end GlobalTheory.HandTame

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodHandedDownIsTameThetaFunctionalStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

theorem _root_.GlobalTheory.T.besselPeriod_handedDown_isTameThetaFunctional : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (s : StFB ψ J B), ∀ (vL : VolM D B.L.rank J.W₀.rank) (χ χz : (AE D)ˣ →* Circle) (omz : Om J.W₀ B.L), IsWeilDatumO ψ J.W₀ B.L χ χz omz → ∀ (φ : GA D J.W₀ → ℂ) (G : GA D B.V → ℂ) (Φ₀ : WO J.W₀ B.L → ℂ), RapidDec J.W₀ φ → RapidDec B.V G → IsThetaFunO ψ J.W₀ B.L Φ₀ → Tame ψ J.W₀ B.V₀ fun Ξ => B.per ψ (handP s vL omz φ Φ₀ Ξ) G := by
  first | exact @GlobalTheory.HandTame.handP₂ | exact GlobalTheory.HandTame.handP₂ | (intros; apply GlobalTheory.HandTame.handP₂ <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodGivesFourierJacobiPeriodOfLift

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.UpFromBessel

variable {D : D7}

theorem pair_self_ne_zero {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    (v : VolM D T.rank S.rank) {f₀ : WO S T → ℂ} (hf : IsThetaFunO ψ S T f₀) (hne : f₀ ≠ 0) :
    thPair v.μ v.𝓕 f₀ f₀ ≠ 0 := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.MixModel.lattice_Mx D T.rank S.rank
  haveI : BorelSpace (Mx D T.rank S.rank) := ⟨rfl⟩
  haveI : DiscreteTopology (ratMx D T.rank S.rank) := i5
  haveI : Countable (ratMx D T.rank S.rank) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  obtain ⟨hμ, hF, h1⟩ := v.covol
  haveI := hμ
  haveI : IsFiniteMeasure (v.μ.restrict v.𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
  obtain ⟨C, hC⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ hf
  have e : ∀ w, f₀ w * star (f₀ w) = ((‖f₀ w‖ ^ 2 : ℝ) : ℂ) := fun w => by
    rw [Complex.star_def, Complex.mul_conj']; push_cast; rfl
  have hint : Integrable (fun w => ‖f₀ w‖ ^ 2) (v.μ.restrict v.𝓕) :=
    Integrable.of_bound (hf.cont.norm.pow 2).measurable.aestronglyMeasurable (C ^ 2)
      (Filter.Eventually.of_forall fun w => by
        rw [Real.norm_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hC w) 2)
  intro h0
  have h2 : (∫ w in v.𝓕, ‖f₀ w‖ ^ 2 ∂v.μ) = 0 := by
    have : thPair v.μ v.𝓕 f₀ f₀ = ((∫ w in v.𝓕, ‖f₀ w‖ ^ 2 ∂v.μ : ℝ) : ℂ) := by
      unfold thPair
      simp_rw [e]
      exact integral_ofReal
    rw [this] at h0
    exact_mod_cast h0
  have h3 : ∫⁻ w in v.𝓕, ‖f₀ w‖ₑ ^ 2 ∂v.μ = 0 := by
    have en : ∀ z : ℂ, ‖z‖ₑ ^ 2 = ENNReal.ofReal (‖z‖ ^ 2) := fun z => by
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
    simp_rw [en]
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun w => by positivity), h2,
      ENNReal.ofReal_zero]
  exact hne (GlobalTheory.OrientedHeis.eq_zero_of_lintegral_eq_zero (ratMx D T.rank S.rank) v.μ v.𝓕 hF f₀ hf.cont
    (fun γ hγ w => GlobalTheory.OrientedHeis.theta_norm_periodic hψ hf γ hγ w) h3)

theorem per_smul {ρ : ℕ} (B : BesL D ρ) (ψ : AddChar (AF D.host.F) ℂ) (c : ℂ) (φ : GA D B.A → ℂ) (f : GA D B.V → ℂ) :
    B.per ψ (c • φ) f = c * B.per ψ φ f := by
  simp only [BesL.per, besPer, besFun, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]

theorem upFB : ∀ D : D7, UpFB D := by
  intro D ψ σ J B s 𝒮 Γ₀ K hL χA χz omb omz hχ hb hz φ G hφ hG hK Ξ₁ Φ₀ hΞ hΦ hne hvac hper
  by_contra hcon
  push_neg at hcon
  have hψ := s.weil.std
  obtain ⟨vL⟩ := (GlobalTheory.Unf.VolExist.measures_exist D).2.2.1 B.L.rank J.W₀.rank
  have hvan := GlobalTheory.T.vanishing_descends_fourierJacobi_to_bessel D ψ σ J B s 𝒮 Γ₀ K hL vL _ _ omz hz φ G Φ₀ hφ hG hΦ hK hcon
  have htame := GlobalTheory.T.besselPeriod_handedDown_isTameThetaFunctional D ψ σ J B s vL _ _ omz hz φ G Φ₀ hφ hG hΦ
  obtain ⟨Φ, hΦS, hfl⟩ := hL.ne
  have hall := GlobalTheory.T.tame_functional_vacuum_irreducibility D ψ hψ J.W₀ B.V₀ Γ₀ _ htame _ (hL.vac Φ hΦS) hfl (fun w hw => by
    have h1 := (GlobalTheory.FlatHeis.flatAt_heisO D ψ hψ J.W J.W₀ B.V B.V₀ (σ + 1) σ J.d B.d s.vS s.vT s.vU
      (xLast B.d (vecB B.o B.ζ)) 0 Φ (hL.theta Φ hΦS)).2.1 w
    have h2 := hvan _ (hL.core Φ hΦS w hw)
    simp only [flFB, flatS] at h2 ⊢
    rw [h1] at h2
    exact h2) _ hvac
  have hlink := GlobalTheory.T.besselHandedFunction_product_eq_coreLift_mul_pairing D ψ σ J B s vL χA χz omb omz hχ hb hz φ Ξ₁ Φ₀ Φ₀ hΞ hΦ hΦ
  simp only [hlink, per_smul] at hall
  exact hper ((mul_eq_zero.1 hall).resolve_left (pair_self_ne_zero hψ vL hΦ hne))

end GlobalTheory.UpFromBessel
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodGivesFourierJacobiPeriodOfLiftStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

theorem _root_.GlobalTheory.T.bessel_period_gives_fourierJacobi_period_of_lift : ∀ D : D7, UpFB D := by
  first | exact @GlobalTheory.UpFromBessel.upFB | exact GlobalTheory.UpFromBessel.upFB | (intros; apply GlobalTheory.UpFromBessel.upFB <;> assumption)
end
end
