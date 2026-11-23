module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousTranslatesKernelRouteSmallVertex
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallRouteKernelLeftInvariantRationalUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslatedKernelLeThetaFunctionRouteBigVertexStatement
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicHeightBlockDiagonalEmbeddingLeMul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteVolumeAdelicUnitaryQuotient
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousTranslatesKernelRouteSmallVertexStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.continuous_translates_kernel_route_small_vertex : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G)
    (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j))
    (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j))) (z : GA D (G.V (.grid i j)) →₀ ℂ),
    Continuous (fun p : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid i j)) =>
      translates z (kerSmall W Θ' p.1 g₁) p.2) := by
  first | exact @GlobalTheory.SmallRoute.continuous_translates_kerSmall | exact GlobalTheory.SmallRoute.continuous_translates_kerSmall | (intros; apply GlobalTheory.SmallRoute.continuous_translates_kerSmall <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallRouteKernelLeftInvariantRationalUnitaryStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.smallRouteKernel_left_invariant_rationalUnitary : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G)
    (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j))
    (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j))),
    ∀ γ ∈ GQ (G.V (.grid i (j + 1))), ∀ g u, kerSmall W Θ' (γ * g) g₁ u = kerSmall W Θ' g g₁ u := by
  first | exact @GlobalTheory.ZConvLeft.kerSmall_rat_left | exact GlobalTheory.ZConvLeft.kerSmall_rat_left | (intros; apply GlobalTheory.ZConvLeft.kerSmall_rat_left <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicHeightBlockDiagonalEmbeddingLeMulStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.unitaryAdelicHeight_blockDiagonalEmbedding_le_mul : ∀ {D : D7} (A B : HSp D) {d : ℕ} (e : Fin A.rank ⊕ Fin B.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram A B e) (g : GA D A) (g₁ : GA D B),
    (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ht (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU A B e hJ (g, g₁)) : ℝ) ≤ GlobalTheory.Grow.height A g * GlobalTheory.Grow.height B g₁ := by
  first | exact @GlobalTheory.BlockHeight.ht_blkU_le | exact GlobalTheory.BlockHeight.ht_blkU_le | (intros; apply GlobalTheory.BlockHeight.ht_blkU_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslationCombIntegrableThetaKernel

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.ZConv

theorem zconv : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree) (hP : GlobalTheory.Published.CuspDecayBound) {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (hT : SquareTriple W t i j)
    (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ')
    (F : Fn G (.grid i (j + 1))) (hF : IsAutFunSm W.θ _ F) (hFc : IsCuspFun _ F) (hFl : G.IsListed W.θ _ F) (hB : TotConv W M _ Θ' F) (g₁ : GA D (G.V (.grid (i + 1) j))),
    ∃ z : GA D (G.V (.grid i j)) →₀ ℂ, zdeg z ≠ 0 ∧
    (∀ g, IntegrableOn (translates z (kerSmall W Θ' g g₁)) (M.fd (.grid i j)) (M.ν (.grid i j))) ∧
    Integrable (fun p : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid i j)) => F p.1 * translates z (kerSmall W Θ' p.1 g₁) p.2)
      (((M.ν (.grid i (j + 1))).restrict (M.fd (.grid i (j + 1)))).prod ((M.ν (.grid i j)).restrict (M.fd (.grid i j)))) := by
  intro D T L sc G hK hP μ₀ hL W B ρ t i j hT M hM Θ Θ' hΘ F hF hFc hFl hB g₁
  obtain ⟨e, Bs, Γ, X, om, om', h, hTr, hv⟩ := hT M hM
  obtain ⟨z, Φ, a, C₀, hz, hΦ, hid⟩ := GlobalTheory.T.translatedKernel_le_thetaFunction_routeBigVertex hL W B ρ t i j M hM Θ Θ' hΘ g₁ e Bs Γ X om om' h hTr hv
  have dec := (hK.1 D.host.F D.host.E D.sp.cm.sig Bs _ _ Γ X om om' hTr).1
  obtain ⟨C, k, hC⟩ := (dec.2 Φ hΦ).1 0
  have hbd : ∀ g u, ‖translates z (kerSmall W Θ' g g₁) u‖ ≤
      |C₀| * |C| * (2 * GlobalTheory.Grow.quotHeight _ g * GlobalTheory.Grow.height _ g₁) ^ k := by
    intro g u
    obtain ⟨γ, hγ, hle⟩ := GlobalTheory.Grow.exists_height_le_two_mul_quotHeight _ g
    have e1 : translates z (kerSmall W Θ' g g₁) u = translates z (kerSmall W Θ' (γ * g) g₁) u := by
      simp only [translates, GlobalTheory.T.smallRouteKernel_left_invariant_rationalUnitary hL W B ρ t i j Θ Θ' hΘ g₁ γ hγ]
    rw [e1]
    have h1 := hC (a u) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (γ * g, g₁))
    rw [pow_zero, mul_one] at h1
    have h2 := GlobalTheory.T.unitaryAdelicHeight_blockDiagonalEmbedding_le_mul _ _ e h.JWW (γ * g) g₁
    have h3 : (0 : ℝ) ≤ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ht (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (γ * g, g₁)) : ℝ) := NNReal.coe_nonneg _
    have h4 : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ht (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (γ * g, g₁)) : ℝ) ≤
        2 * GlobalTheory.Grow.quotHeight _ g * GlobalTheory.Grow.height _ g₁ :=
      h2.trans (mul_le_mul_of_nonneg_right hle (GlobalTheory.Grow.height_pos _ _).le)
    calc _ ≤ C₀ * ‖GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om' Φ (a u) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (γ * g, g₁))‖ := hid _ _
      _ ≤ |C₀| * ‖GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om' Φ (a u) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (γ * g, g₁))‖ :=
          mul_le_mul_of_nonneg_right (le_abs_self C₀) (norm_nonneg _)
      _ ≤ |C₀| * (|C| * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ht (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (γ * g, g₁)) : ℝ) ^ k) :=
          mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg h3 k)))
            (abs_nonneg C₀)
      _ ≤ _ := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h3 h4 k) (mul_nonneg (abs_nonneg C₀) (abs_nonneg C))

  have hWl := (hM.vtx (.grid i j) ⟨i.2.le, j.2.le⟩).haar_fund
  have hVl := (hM.vtx (.grid i (j + 1)) ⟨i.2.le, j.2⟩).haar_fund
  haveI : IsFiniteMeasure ((M.ν (.grid i j)).restrict (M.fd (.grid i j))) :=
    isFiniteMeasure_restrict.2 (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol _ _ _ hWl.1 hWl.2).ne
  haveI : IsFiniteMeasure ((M.ν (.grid i (j + 1))).restrict (M.fd (.grid i (j + 1)))) :=
    isFiniteMeasure_restrict.2 (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol _ _ _ hVl.1 hVl.2).ne
  have hcont := GlobalTheory.T.continuous_translates_kernel_route_small_vertex hL W B ρ t i j Θ Θ' hΘ g₁ z
  have hRD := GlobalTheory.Grow.rapidDec_of_cuspForm (GlobalTheory.Grow.cuspRapidDecay_of_bound hP) W.θ_is hF hFc
  obtain ⟨Bd, hBd⟩ := hRD.decay k
  refine ⟨z, hz, fun g => ?_, ?_⟩
  · exact Integrable.of_bound ((hcont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable) _
      (.of_forall fun u => hbd g u)
  · have h0 : (0 : ℝ) ≤ |C₀| * |C| * (2 * GlobalTheory.Grow.height _ g₁) ^ k :=
      mul_nonneg (mul_nonneg (abs_nonneg C₀) (abs_nonneg C)) (pow_nonneg (by have := GlobalTheory.Grow.height_pos _ g₁; positivity) k)
    refine Integrable.of_bound ((hRD.continuous.comp continuous_fst).mul hcont).aestronglyMeasurable
      (|C₀| * |C| * (2 * GlobalTheory.Grow.height _ g₁) ^ k * Bd) (.of_forall fun p => ?_)
    rw [norm_mul]
    calc ‖F p.1‖ * ‖translates z (kerSmall W Θ' p.1 g₁) p.2‖ ≤
          ‖F p.1‖ * (|C₀| * |C| * (2 * GlobalTheory.Grow.quotHeight _ p.1 * GlobalTheory.Grow.height _ g₁) ^ k) :=
          mul_le_mul_of_nonneg_left (hbd _ _) (norm_nonneg _)
      _ = |C₀| * |C| * (2 * GlobalTheory.Grow.height _ g₁) ^ k * (‖F p.1‖ * GlobalTheory.Grow.quotHeight _ p.1 ^ k) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hBd _) h0
end GlobalTheory.ZConv

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslationCombIntegrableThetaKernelStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.exists_translation_comb_integrable_thetaKernel : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree) (hP : GlobalTheory.Published.CuspDecayBound) {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (hT : SquareTriple W t i j)
    (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ')
    (F : Fn G (.grid i (j + 1))) (hF : IsAutFunSm W.θ _ F) (hFc : IsCuspFun _ F) (hFl : G.IsListed W.θ _ F) (hB : TotConv W M _ Θ' F) (g₁ : GA D (G.V (.grid (i + 1) j))),
    ∃ z : GA D (G.V (.grid i j)) →₀ ℂ, zdeg z ≠ 0 ∧
    (∀ g, IntegrableOn (translates z (kerSmall W Θ' g g₁)) (M.fd (.grid i j)) (M.ν (.grid i j))) ∧
    Integrable (fun p : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid i j)) => F p.1 * translates z (kerSmall W Θ' p.1 g₁) p.2)
      (((M.ν (.grid i (j + 1))).restrict (M.fd (.grid i (j + 1)))).prod ((M.ν (.grid i j)).restrict (M.fd (.grid i j)))) := by
  first | exact @GlobalTheory.ZConv.zconv | exact GlobalTheory.ZConv.zconv | (intros; apply GlobalTheory.ZConv.zconv <;> assumption)
end
end
