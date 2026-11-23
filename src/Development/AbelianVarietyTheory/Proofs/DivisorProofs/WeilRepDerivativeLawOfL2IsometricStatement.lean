module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleJoinZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicL2EqZeroImpEqZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrArchPairAdeleJoin
import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzHaarWeilStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchDerivativeKeepsSumsFixedFiniteParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrArchPairAdeleJoin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzSeminormSmulLeftLinearPhaseLe
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicL2LimitZero

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section
open MeasureTheory Filter Topology

namespace GlobalTheory.WeilL2Words

theorem l2A_eq_zero_of_tendsto (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (μ : @MeasureTheory.Measure (κ → FiniteAdeleRing (𝓞 F) F) (borel _))
    (D : (κ → AdeleRing (𝓞 F) F) → ℂ) (G : ℕ → (κ → AdeleRing (𝓞 F) F) → ℂ) (hG : ∀ n, G n ∈ GlobalTheory.WeilM.schA F κ)
    (hD : ∀ a, Filter.Tendsto (fun n => G n a) Filter.atTop (nhds (D a)))
    (h0 : Filter.Tendsto (fun n => GlobalTheory.WeilL2Words.l2A F μ (G n)) Filter.atTop (nhds 0)) : GlobalTheory.WeilL2Words.l2A F μ D = 0 := by
  letI : MeasurableSpace (κ → FiniteAdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (κ → FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
  haveI : OpensMeasurableSpace (κ → mixedEmbedding.mixedSpace F) := Pi.opensMeasurableSpace
  have hc : Continuous fun z : ℂ => ‖z‖ₑ ^ 2 := (ENNReal.continuous_pow 2).comp continuous_enorm
  have hin : ∀ y, (∫⁻ x, ‖D (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2) ≤
      liminf (fun n => ∫⁻ x, ‖G n (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2) atTop := by
    intro y
    have hm : ∀ n, AEMeasurable (fun x => ‖G n (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2) volume := by
      intro n
      obtain ⟨s, hs⟩ := GlobalTheory.WeilCont.exists_slice F (hG n) y
      have e : (fun x => ‖G n (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2) = fun x => ‖s x‖ₑ ^ 2 := by
        funext x; rw [hs]
      rw [e]
      exact (hc.comp s.continuous).measurable.aemeasurable
    calc (∫⁻ x, ‖D (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2)
        = ∫⁻ x, liminf (fun n => ‖G n (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2) atTop := by
          refine lintegral_congr fun x => ?_
          exact (((hc.tendsto _).comp (hD _)).liminf_eq).symm
      _ ≤ _ := lintegral_liminf_le' hm
  have hmeas : ∀ n, AEMeasurable (fun y => ∫⁻ x, ‖G n (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2) μ := by
    intro n
    obtain ⟨m, f, g, hg, he⟩ := schA_exists_sum F (hG n)
    have hlc : IsLocallyConstant (fun y => ∫⁻ x, ‖G n (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2) := by
      rw [IsLocallyConstant.iff_eventually_eq]
      intro y
      have hev : ∀ᶠ z in 𝓝 y, ∀ i, g i z = g i y :=
        Filter.eventually_all.2 fun i => (hg i).1.eventually_eq y
      filter_upwards [hev] with z hz
      refine lintegral_congr fun x => ?_
      simp only [he, Finset.sum_apply, GlobalTheory.WeilCont.pureA_adeleJoin, hz]
    exact hlc.continuous.measurable.aemeasurable
  refine le_antisymm ?_ (bot_le)
  calc l2A F μ D = ∫⁻ y, (∫⁻ x, ‖D (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2) ∂μ := rfl
    _ ≤ ∫⁻ y, liminf (fun n => ∫⁻ x, ‖G n (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2) atTop ∂μ := lintegral_mono hin
    _ ≤ liminf (fun n => ∫⁻ y, (∫⁻ x, ‖G n (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2) ∂μ) atTop := lintegral_liminf_le' hmeas
    _ = 0 := h0.liminf_eq

end GlobalTheory.WeilL2Words

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicL2LimitZeroStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical


theorem _root_.GlobalTheory.T.adelic_l2_limit_zero : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (μ : @MeasureTheory.Measure (κ → FiniteAdeleRing (𝓞 F) F) (borel _))
    (D : (κ → AdeleRing (𝓞 F) F) → ℂ) (G : ℕ → (κ → AdeleRing (𝓞 F) F) → ℂ), (∀ n, G n ∈ GlobalTheory.WeilM.schA F κ) →
    (∀ a, Filter.Tendsto (fun n => G n a) Filter.atTop (nhds (D a))) →
    Filter.Tendsto (fun n => GlobalTheory.WeilL2Words.l2A F μ (G n)) Filter.atTop (nhds 0) → GlobalTheory.WeilL2Words.l2A F μ D = 0 := by
  first | exact @GlobalTheory.WeilL2Words.l2A_eq_zero_of_tendsto | exact GlobalTheory.WeilL2Words.l2A_eq_zero_of_tendsto | (intros; apply GlobalTheory.WeilL2Words.l2A_eq_zero_of_tendsto <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerOperatorArchimedeanMemAdelicSchwartz

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

namespace GlobalTheory.WeilL2Words

theorem schr_archPair_mem_schA : ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ), GlobalTheory.WeilL2Words.IsStdInf F ψ →
    ∀ (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)), ∀ φ ∈ GlobalTheory.WeilM.schA F κ,
      GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilL2Words.archPair F h) φ ∈ GlobalTheory.WeilM.schA F κ := by
  intro F _ _ _ κ _ ψ hψ h φ hφ
  obtain ⟨ℓ, -, hℓ⟩ := hψ
  obtain ⟨n, f, g, hg, rfl⟩ := schA_exists_sum F hφ
  let M : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] mixedEmbedding.mixedSpace F :=
    ∑ k, (LinearMap.mulRight ℝ (h.2 k)).comp (LinearMap.proj k)
  let L : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (ℓ.comp M)
  have hL : ∀ X, L X = ℓ (∑ k, X k * h.2 k) := by
    intro X
    simp [L, M]
  set c : ℝ := ℓ (∑ k, h.1 k * h.2 k) / 2 with hc
  have hgr := GlobalTheory.LinPhaseSeminorm.hasTemperateGrowth_phase L (-c) (-1)
  rw [← GlobalTheory.LinPhaseSeminorm.phase_eq] at hgr
  rw [schr_sum']
  refine Submodule.sum_mem _ fun i _ => Submodule.subset_span
    ⟨SchwartzMap.smulLeftCLM ℂ
      (fun x => Complex.exp (-(2 * Real.pi * Complex.I) * ((-1 * L x + (-1) ^ 2 * -c : ℝ) : ℂ)))
      (SchwartzMap.compSubConstCLM ℂ (-h.1) (f i)), g i, hg i, ?_⟩
  funext a
  rw [← adeleJoin_archPart F a, schr_archPair_adeleJoin F ψ ℓ hℓ, GlobalTheory.WeilCont.pureA_adeleJoin,
    GlobalTheory.WeilCont.pureA_adeleJoin, SchwartzMap.smulLeftCLM_apply_apply hgr, SchwartzMap.compSubConstCLM_apply,
    sub_neg_eq_add, smul_eq_mul, hL, ← mul_assoc]
  congr 2
  rw [hc]
  push_cast
  ring_nf

end GlobalTheory.WeilL2Words

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerOperatorArchimedeanMemAdelicSchwartzStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical


theorem _root_.GlobalTheory.T.schroedingerOperator_archimedean_mem_adelicSchwartz : ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ), GlobalTheory.WeilL2Words.IsStdInf F ψ →
    ∀ (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)), ∀ φ ∈ GlobalTheory.WeilM.schA F κ,
      GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilL2Words.archPair F h) φ ∈ GlobalTheory.WeilM.schA F κ := by
  first | exact @GlobalTheory.WeilL2Words.schr_archPair_mem_schA | exact GlobalTheory.WeilL2Words.schr_archPair_mem_schA | (intros; apply GlobalTheory.WeilL2Words.schr_archPair_mem_schA <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepDerivativeLawOfL2Isometric

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section
open MeasureTheory

namespace GlobalTheory.WeilL2Words

theorem dS_om_eq : ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ), GlobalTheory.WeilL2Words.IsStdInf F ψ →
    ∀ {G : Type} [Group G] (om : G →* Module.End ℂ ((κ → AdeleRing (𝓞 F) F) → ℂ)),
      (∀ p, ∀ φ ∈ GlobalTheory.WeilM.schA F κ, om p φ ∈ GlobalTheory.WeilM.schA F κ) →
      ∀ (M : G → ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) →ₗ[ℝ] ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))),
      (∀ p h, ∀ φ ∈ GlobalTheory.WeilM.schA F κ,
        om p (GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilL2Words.archPair F (M p h)) φ) = GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilL2Words.archPair F h) (om p φ)) →
      ∀ (μ : @MeasureTheory.Measure (κ → FiniteAdeleRing (𝓞 F) F) (borel _)), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      (∀ p, ∀ φ ∈ GlobalTheory.WeilM.schA F κ, GlobalTheory.WeilL2Words.l2A F μ (om p φ) = GlobalTheory.WeilL2Words.l2A F μ φ) →
      ∀ p h, ∀ φ ∈ GlobalTheory.WeilM.schA F κ, GlobalTheory.WeilL2Words.dS F ψ h (om p φ) = om p (GlobalTheory.WeilL2Words.dS F ψ (M p h) φ) := by
  intro F _ _ _ κ _ ψ hψ G _ om hpres M himpl μ hμ hiso p h φ hφ
  set h' := M p h with hh'
  have hOm : om p φ ∈ GlobalTheory.WeilM.schA F κ := hpres p φ hφ
  have hD1 : GlobalTheory.WeilL2Words.dS F ψ h' φ ∈ GlobalTheory.WeilM.schA F κ := GlobalTheory.WeilL2Words.dS_mem_schA F hψ h' hφ

  set Qr : ℕ → (κ → AdeleRing (𝓞 F) F) → ℂ := fun n => ((n : ℂ) + 1) •
      (GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilL2Words.archPair F (((n : ℝ) + 1)⁻¹ • h')) φ - φ) - GlobalTheory.WeilL2Words.dS F ψ h' φ with hQr
  have hQr_mem : ∀ n, Qr n ∈ GlobalTheory.WeilM.schA F κ := fun n =>
    Submodule.sub_mem _ (Submodule.smul_mem _ _ (Submodule.sub_mem _ (GlobalTheory.T.schroedingerOperator_archimedean_mem_adelicSchwartz F κ ψ hψ _ φ hφ) hφ)) hD1
  set Gn : ℕ → (κ → AdeleRing (𝓞 F) F) → ℂ := fun n a => ((n : ℂ) + 1) *
      (GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilL2Words.archPair F (((n : ℝ) + 1)⁻¹ • h)) (om p φ) a - om p φ a) -
        om p (GlobalTheory.WeilL2Words.dS F ψ h' φ) a with hGn
  have hGQ : ∀ n, Gn n = om p (Qr n) := by
    intro n
    have e := himpl p (((n : ℝ) + 1)⁻¹ • h) φ hφ
    rw [map_smul] at e
    rw [hQr, map_sub, map_smul, map_sub, e]
    funext a
    simp [hGn, smul_eq_mul]
  have hGmem : ∀ n, Gn n ∈ GlobalTheory.WeilM.schA F κ := fun n => by rw [hGQ]; exact hpres p _ (hQr_mem n)
  have hGl2 : Filter.Tendsto (fun n => GlobalTheory.WeilL2Words.l2A F μ (Gn n)) Filter.atTop (nhds 0) := by
    have e : (fun n => GlobalTheory.WeilL2Words.l2A F μ (Gn n)) = fun n => GlobalTheory.WeilL2Words.l2A F μ (Qr n) := by
      funext n; rw [hGQ, hiso p _ (hQr_mem n)]
    rw [e]
    have := GlobalTheory.T.adelic_schwartz_haar_weil F κ ψ hψ μ hμ h' φ hφ
    refine this.congr fun n => ?_
    congr 1
  set D : (κ → AdeleRing (𝓞 F) F) → ℂ := GlobalTheory.WeilL2Words.dS F ψ h (om p φ) - om p (GlobalTheory.WeilL2Words.dS F ψ h' φ) with hD
  have hDmem : D ∈ GlobalTheory.WeilM.schA F κ :=
    Submodule.sub_mem _ (GlobalTheory.WeilL2Words.dS_mem_schA F hψ h hOm) (hpres p _ hD1)
  have hpt : ∀ a, Filter.Tendsto (fun n => Gn n a) Filter.atTop (nhds (D a)) := by
    intro a
    have hd := (GlobalTheory.WeilL2Words.differentiableAt_schr F hψ h hOm a).hasDerivAt
    rw [hasDerivAt_iff_tendsto_slope_zero] at hd
    have ht : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) Filter.atTop (nhdsWithin 0 {0}ᶜ) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Filter.Eventually.of_forall fun n => ?_⟩
      · have h1 : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        simpa only [one_div] using h1
      · simp only [Set.mem_compl_iff, Set.mem_singleton_iff, inv_eq_zero]; positivity
    have h0 : ∀ Ψ : (κ → AdeleRing (𝓞 F) F) → ℂ, GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilL2Words.archPair F ((0 : ℝ) • h)) Ψ a = Ψ a := by
      intro Ψ
      have : GlobalTheory.WeilL2Words.archPair F ((0 : ℝ) • h) = (0, 0) := by
        rw [zero_smul]
        refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> exact GlobalTheory.WeilL2Words.adeleOfMixedSpaceComponent_zero F
      rw [this]
      simp [GlobalTheory.WeilM.schr]
    have := (hd.comp ht).sub_const (om p (GlobalTheory.WeilL2Words.dS F ψ h' φ) a)
    refine this.congr fun n => ?_
    simp only [Function.comp, zero_add, h0, hGn, inv_inv, Complex.real_smul]
    push_cast
    ring
  have hl := GlobalTheory.T.adelic_l2_limit_zero F κ μ D Gn hGmem hpt hGl2
  have hz := GlobalTheory.T.adelic_l2_eq_zero_imp_eq_zero F κ μ hμ D hDmem hl
  exact sub_eq_zero.mp hz

end GlobalTheory.WeilL2Words
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepDerivativeLawOfL2IsometricStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical


theorem _root_.GlobalTheory.T.weilRep_derivative_law_of_L2Isometric : ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ), GlobalTheory.WeilL2Words.IsStdInf F ψ →
    ∀ {G : Type} [Group G] (om : G →* Module.End ℂ ((κ → AdeleRing (𝓞 F) F) → ℂ)),
      (∀ p, ∀ φ ∈ GlobalTheory.WeilM.schA F κ, om p φ ∈ GlobalTheory.WeilM.schA F κ) →
      ∀ (M : G → ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) →ₗ[ℝ] ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))),
      (∀ p h, ∀ φ ∈ GlobalTheory.WeilM.schA F κ,
        om p (GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilL2Words.archPair F (M p h)) φ) = GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilL2Words.archPair F h) (om p φ)) →
      ∀ (μ : @MeasureTheory.Measure (κ → FiniteAdeleRing (𝓞 F) F) (borel _)), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      (∀ p, ∀ φ ∈ GlobalTheory.WeilM.schA F κ, GlobalTheory.WeilL2Words.l2A F μ (om p φ) = GlobalTheory.WeilL2Words.l2A F μ φ) →
      ∀ p h, ∀ φ ∈ GlobalTheory.WeilM.schA F κ, GlobalTheory.WeilL2Words.dS F ψ h (om p φ) = om p (GlobalTheory.WeilL2Words.dS F ψ (M p h) φ) := by
  first | exact @GlobalTheory.WeilL2Words.dS_om_eq | exact GlobalTheory.WeilL2Words.dS_om_eq | (intros; apply GlobalTheory.WeilL2Words.dS_om_eq <;> assumption)
end
end
