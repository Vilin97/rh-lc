module

public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PhaseApply
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqOfLeviPhaseCharacterIntegralsEqStatement
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsotropicDualFrameOfSplitEmbedding
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralLeviPhaseChangeOfVariablesStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelParsevalThetaInnerProductStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictIsotropicQuotientWittTowerPropertie
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymplecticHalfIsotropicPartsAddSelfEqTraceStatement
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorIdeleAbsDetUnitaryAdelicEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFunctionPeriodicNormFiniteSqIntegral
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionIsotropicPartHomOfFrameMulStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaFunctionScalarProductPreservedIsometry
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsConstSqNormTwoHaarFundamentalDomains

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Twist.NormRed

theorem sq_norm_two_haar : ∀ (D : D7) (V' W : HSp D) (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)), μ'.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V') 𝓕' μ' → ∀ (μ'' : Measure (WO V' W)) (𝓕'' : Set (WO V' W)), IsCovolOne (ratL W V') μ'' 𝓕'' → ∃ c : ENNReal, ∀ g : WO V' W → ℂ, Continuous g → (∀ γ ∈ ratL W V', ∀ w, ‖g (γ + w)‖ = ‖g w‖) → ∫⁻ x in 𝓕', ‖g x‖ₑ ^ 2 ∂μ' = c * ∫⁻ x in 𝓕'', ‖g x‖ₑ ^ 2 ∂μ'' := by
  intro D V' W μ' 𝓕' hμ' hF' μ'' 𝓕'' h''
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank V'.rank
  haveI : BorelSpace (WO V' W) := ⟨rfl⟩
  haveI : IsTopologicalAddGroup (WO V' W) := i1
  haveI : LocallyCompactSpace (WO V' W) := i2
  haveI : SecondCountableTopology (WO V' W) := i3
  haveI : T2Space (WO V' W) := i4
  haveI : DiscreteTopology (ratL W V') := i5
  haveI : TopologicalSpace.SeparableSpace (ratL W V') := inferInstance
  haveI : Countable (ratL W V') := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI : MeasurableConstVAdd (ratL W V') (WO V' W) :=
    ⟨fun c => (continuous_const.add continuous_id).measurable⟩
  obtain ⟨hμ'', hF'', -⟩ := h''
  haveI : VAddInvariantMeasure (ratL W V') (WO V' W) μ'' :=
    ⟨fun c s _ => measure_preimage_add μ'' (c : WO V' W) s⟩
  have e := Measure.isAddLeftInvariant_eq_smul μ' μ''
  set c := Measure.addHaarScalarFactor μ' μ''
  have hc : c ≠ 0 := (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ' μ'').ne'
  have hac : μ'' ≪ μ' := by
    rw [e]; exact Measure.absolutelyContinuous_smul (by exact_mod_cast hc)
  have hF2 : IsAddFundamentalDomain (ratL W V') 𝓕' μ'' := hF'.mono hac
  refine ⟨(c : ENNReal), fun g hg hper => ?_⟩
  have hp : ∀ (γ : ratL W V') (x : WO V' W), ‖g (γ +ᵥ x)‖ₑ ^ 2 = ‖g x‖ₑ ^ 2 := by
    intro γ x
    rw [AddSubgroup.vadd_def, vadd_eq_add]
    have h1 : ‖g ((γ : WO V' W) + x)‖₊ = ‖g x‖₊ := NNReal.eq (hper γ γ.2 x)
    simp only [enorm_eq_nnnorm, h1]
  rw [e, Measure.restrict_smul, lintegral_smul_measure, hF2.setLIntegral_eq hF'' _ hp]
  rfl

end GlobalTheory.Twist.NormRed
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsConstSqNormTwoHaarFundamentalDomainsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_const_sqNorm_two_haar_fundamentalDomains : ∀ (D : D7) (V' W : HSp D) (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)), μ'.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V') 𝓕' μ' → ∀ (μ'' : Measure (WO V' W)) (𝓕'' : Set (WO V' W)), IsCovolOne (ratL W V') μ'' 𝓕'' → ∃ c : ENNReal, ∀ g : WO V' W → ℂ, Continuous g → (∀ γ ∈ ratL W V', ∀ w, ‖g (γ + w)‖ = ‖g w‖) → ∫⁻ x in 𝓕', ‖g x‖ₑ ^ 2 ∂μ' = c * ∫⁻ x in 𝓕'', ‖g x‖ₑ ^ 2 ∂μ'' := by
  first | exact @GlobalTheory.Twist.NormRed.sq_norm_two_haar | exact GlobalTheory.Twist.NormRed.sq_norm_two_haar | (intros; apply GlobalTheory.Twist.NormRed.sq_norm_two_haar <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedNormSqFourierEqIsotropicMatrixCoeff

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ResNormFourier

theorem resNorm_fourier : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B → ∀ C' : Matrix (Fin V.rank) (Fin r) D.host.E, GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D C * V.gram * C' = 1 → GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D C' * V.gram * C' = 0 → GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D C' * V.gram * B = 0 → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨 → ∀ (μ₀ : Measure (WO V W)) (𝓕₀ : Set (WO V W)), IsCovolOne (ratL W V) μ₀ 𝓕₀ → ∀ (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)), IsCovolOne (ratL W V') μ' 𝓕' → ∀ f, IsThetaFunO ψ V W f → ∀ y : Mx D W.rank r, ∫ w in 𝓕₀, heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y) f w * starRingEnd ℂ (f w) ∂μ₀ = ∫ u, ψ (symplOH V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y) + symplOH V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y)) * GlobalTheory.LeviNorm.resNorm ψ V V' W C C' B μ 𝓨 μ' 𝓕' f u ∂μ := by
  intro D V V' W r C B hs C' h1 h2 h3 ψ hψ μ 𝓨 hY μ₀ 𝓕₀ h0 μ' 𝓕' h' f hf y
  have L := GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ V W
  have hR := GlobalTheory.TowerRestrict.res_theta D V V' W r C B hs ψ hψ μ 𝓨 hY
  obtain ⟨-, -, hP⟩ := GlobalTheory.T.mixedModel_parseval_thetaInnerProduct D V V' W r C B hs C' h1 h2 h3 ψ hψ μ 𝓨 hY μ₀ 𝓕₀ h0 μ' 𝓕' h' _ f
    (L.1 _ f hf) hf
  rw [hP]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  have hsm : ∀ (c : ℂ) (g : WO V W → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (c • g) =
      c • GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 g := by
    intro c g; funext x
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res, Pi.smul_apply, smul_eq_mul, integral_const_mul]
  have key : ∀ a b : WO V W, heisO ψ V W a (heisO ψ V W b f) =
      ψ (symplOH V W a b + symplOH V W a b) • heisO ψ V W b (heisO ψ V W a f) := by
    intro a b
    rw [L.2.1 a b f, L.2.1 b a f, smul_smul, add_comm b a, GlobalTheory.MixModel.symplOH_skew V W b a,
      ← AddChar.map_add_eq_mul]
    congr 2
    abel
  simp only
  rw [key, hsm, (hR.1 _ (L.1 _ f hf)).2.2.2 y]
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
  rw [integral_const_mul]
  rfl

end GlobalTheory.ResNormFourier
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedNormSqFourierEqIsotropicMatrixCoeffStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.restrictedNormSq_fourier_eq_isotropicMatrixCoeff : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B → ∀ C' : Matrix (Fin V.rank) (Fin r) D.host.E, GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D C * V.gram * C' = 1 → GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D C' * V.gram * C' = 0 → GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D C' * V.gram * B = 0 → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨 → ∀ (μ₀ : Measure (WO V W)) (𝓕₀ : Set (WO V W)), IsCovolOne (ratL W V) μ₀ 𝓕₀ → ∀ (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)), IsCovolOne (ratL W V') μ' 𝓕' → ∀ f, IsThetaFunO ψ V W f → ∀ y : Mx D W.rank r, ∫ w in 𝓕₀, heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y) f w * starRingEnd ℂ (f w) ∂μ₀ = ∫ u, ψ (symplOH V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y) + symplOH V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y)) * GlobalTheory.LeviNorm.resNorm ψ V V' W C C' B μ 𝓨 μ' 𝓕' f u ∂μ := by
  first | exact @GlobalTheory.ResNormFourier.resNorm_fourier | exact GlobalTheory.ResNormFourier.resNorm_fourier | (intros; apply GlobalTheory.ResNormFourier.resNorm_fourier <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorIdeleAbsDetUnitaryAdelicEqOneStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.tensorIdeleAbs_det_unitaryAdelic_eq_one : ∀ (D : D7) (W : HSp D) (h : GA D W), GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det (matHom W h)) = 1 := by
  first | exact @GlobalTheory.UnitaryDetAbs.absE_det_matHom | exact GlobalTheory.UnitaryDetAbs.absE_det_matHom | (intros; apply GlobalTheory.UnitaryDetAbs.absE_det_matHom <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFunctionPeriodicNormFiniteSqIntegralStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaFunction_periodicNorm_finite_sqIntegral : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ F : WO S T → ℂ, IsThetaFunO ψ S T F → (∀ γ ∈ ratL T S, ∀ w, ‖F (γ + w)‖ = ‖F w‖) ∧ ∫⁻ x in 𝓕, ‖F x‖ₑ ^ 2 ∂μ ≠ ⊤ ∧ ∫ x in 𝓕, F x * starRingEnd ℂ (F x) ∂μ = (((∫⁻ x in 𝓕, ‖F x‖ₑ ^ 2 ∂μ).toReal : ℝ) : ℂ) := by
  first | exact @GlobalTheory.ThetaSqInt.thetaO_norm_fin | exact GlobalTheory.ThetaSqInt.thetaO_norm_fin | (intros; apply GlobalTheory.ThetaSqInt.thetaO_norm_fin <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumTransportsHeisenbergMatrixCoeffs

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilCoeff

theorem heis_coeff_eq : ∀ (D : D7) (V W : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (g : GA D V) (h : GA D W) (f : WO V W → ℂ), IsThetaFunO ψ V W f → ∀ (μ₀ : Measure (WO V W)) (𝓕₀ : Set (WO V W)), μ₀.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕₀ μ₀ → ∀ w₀ : WO V W, ∫ w in 𝓕₀, heisO ψ V W (actO V W g h w₀) (ω (g, h) f) w * starRingEnd ℂ (ω (g, h) f w) ∂μ₀ = ∫ w in 𝓕₀, heisO ψ V W w₀ f w * starRingEnd ℂ (f w) ∂μ₀ := by
  intro D V W ψ χS χT ω hω g h f hf μ₀ 𝓕₀ hμ h𝓕 w₀
  have hf1 := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hω.std V W).1 w₀ f hf
  rw [← hω.om_heis g h w₀ f hf]
  exact GlobalTheory.Mem.LiftPolar.scalar_eq D ψ hω.std V W μ₀ 𝓕₀ hμ h𝓕 (ω (g, h))
    (fun f hf => hω.om_pres (g, h) f hf) (fun f hf => hω.om_unit μ₀ 𝓕₀ hμ h𝓕 (g, h) f hf) _ f hf1 hf

end GlobalTheory.WeilCoeff
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumTransportsHeisenbergMatrixCoeffsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.weilDatum_transports_heisenbergMatrixCoeffs : ∀ (D : D7) (V W : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (g : GA D V) (h : GA D W) (f : WO V W → ℂ), IsThetaFunO ψ V W f → ∀ (μ₀ : Measure (WO V W)) (𝓕₀ : Set (WO V W)), μ₀.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕₀ μ₀ → ∀ w₀ : WO V W, ∫ w in 𝓕₀, heisO ψ V W (actO V W g h w₀) (ω (g, h) f) w * starRingEnd ℂ (ω (g, h) f w) ∂μ₀ = ∫ w in 𝓕₀, heisO ψ V W w₀ f w * starRingEnd ℂ (f w) ∂μ₀ := by
  first | exact @GlobalTheory.WeilCoeff.heis_coeff_eq | exact GlobalTheory.WeilCoeff.heis_coeff_eq | (intros; apply GlobalTheory.WeilCoeff.heis_coeff_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviElementScalesRestrictionNormSqAbsDet

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LeviNorm

variable {D : D7}

theorem heisO_isoPart_zero (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) {r : ℕ}
    (C' : Matrix (Fin V.rank) (Fin r) D.host.E) (F : WO V W → ℂ) :
    heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' 0) F = F := by
  have h0 : GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' 0 = 0 := Matrix.zero_mul _
  funext w
  rw [h0]
  simp only [heisO, GlobalTheory.MixModel.symplOH_zero_right, AddChar.map_zero_eq_one, one_mul, add_zero]



theorem norm_levi : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨 → ∀ (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)), μ'.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V') 𝓕' μ' → ∀ (a : GL (Fin r) (AE D)) (g' : GA D V') (m : GA D V), HMul.hMul (Formalism.L2.Theta.mt V m) (C.map (incA D)) = HMul.hMul (C.map (incA D)) a.val → HMul.hMul (Formalism.L2.Theta.mt V m) (B.map (incA D)) = HMul.hMul (B.map (incA D)) (Formalism.L2.Theta.mt V' g') → ∀ (h : GA D W) (f : WO V W → ℂ), IsThetaFunO ψ V W f → ∫⁻ x in 𝓕', ‖GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (ω (m, h) f) x‖ₑ ^ 2 ∂μ' = (GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det a) : ENNReal) ^ W.rank * ∫⁻ x in 𝓕', ‖GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 f x‖ₑ ^ 2 ∂μ' := by
  intro D V V' W r C B hs ψ χS χT ω hω μ 𝓨 hμ μ' 𝓕' hμ' h𝓕' a g' m hC _hB h f hf
  have hstd : IsStdChar D ψ (-1) := hω.std
  obtain ⟨C', h1, h2, h3⟩ := GlobalTheory.TwistDual.exists_isotropic_dual D V V' r C B hs
  obtain ⟨μ₀, 𝓕₀, h0⟩ := GlobalTheory.MixModel.exists_isCovolOne D W.rank V.rank
  obtain ⟨μ'', 𝓕'', h''⟩ := GlobalTheory.MixModel.exists_isCovolOne D W.rank V'.rank
  have hres := GlobalTheory.TowerRestrict.res_theta D V V' W r C B hs ψ hstd μ 𝓨 hμ
  have hΩf : IsThetaFunO ψ V W (ω (m, h) f) := hω.om_pres _ f hf
  have pΩ := GlobalTheory.T.mixedModel_parseval_thetaInnerProduct D V V' W r C B hs C' h1 h2 h3 ψ hstd μ 𝓨 hμ μ₀ 𝓕₀ h0 μ'' 𝓕'' h'' _ _ hΩf hΩf
  have pf := GlobalTheory.T.mixedModel_parseval_thetaInnerProduct D V V' W r C B hs C' h1 h2 h3 ψ hstd μ 𝓨 hμ μ₀ 𝓕₀ h0 μ'' 𝓕'' h'' f f hf hf
  obtain ⟨N₁, hN₁⟩ : ∃ N : Mx D W.rank r → ℂ, N = resNorm ψ V V' W C C' B μ 𝓨 μ'' 𝓕'' (ω (m, h) f) := ⟨_, rfl⟩
  obtain ⟨N₀, hN₀⟩ : ∃ N : Mx D W.rank r → ℂ, N = resNorm ψ V V' W C C' B μ 𝓨 μ'' 𝓕'' f := ⟨_, rfl⟩
  have hN₁c : Continuous N₁ := by rw [hN₁]; exact pΩ.1
  have hN₁i : Integrable N₁ μ := by rw [hN₁]; exact pΩ.2.1
  have hN₀c : Continuous N₀ := by rw [hN₀]; exact pf.1
  have hN₀i : Integrable N₀ μ := by rw [hN₀]; exact pf.2.1
  obtain ⟨k, hk⟩ : ∃ k : ℂ, k = ((GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det a) : ℝ) : ℂ) ^ W.rank :=
    ⟨_, rfl⟩
  have hcov := GlobalTheory.T.integral_levi_phase_change_of_variables D ψ hstd W r μ hμ.1 h (GlobalTheory.T.tensorIdeleAbs_det_unitaryAdelic_eq_one D W h) a N₀ hN₀c hN₀i
  have hph : ∀ y u : Mx D W.rank r, ψ (symplOH V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y) +
      symplOH V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y)) = phase ψ W y u :=
    fun y u => by rw [phase_apply, GlobalTheory.T.symplecticHalf_isotropicParts_add_self_eq_trace D V W r C C' h1 u y]
  rw [← hk] at hcov
  have hφ : Continuous fun u : Mx D W.rank r => (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) u) a.val : Mx D W.rank r) :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  obtain ⟨N₂, hN₂⟩ : ∃ N₂ : Mx D W.rank r → ℂ,
      N₂ = fun u : Mx D W.rank r => k * N₀ (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) u) a.val) := ⟨_, rfl⟩
  have hN₂c : Continuous N₂ := by rw [hN₂]; exact continuous_const.mul (hN₀c.comp hφ)
  have hN₂i : Integrable N₂ μ := by rw [hN₂]; exact hcov.1.const_mul k
  have key : N₁ = N₂ := GlobalTheory.T.eq_of_leviPhaseCharacter_integrals_eq D ψ hstd W r μ hμ.1 N₁ N₂ hN₁c hN₂c hN₁i hN₂i (fun y => by
    have s1 := GlobalTheory.T.restrictedNormSq_fourier_eq_isotropicMatrixCoeff D V V' W r C B hs C' h1 h2 h3 ψ hstd μ 𝓨 hμ μ₀ 𝓕₀ h0 μ'' 𝓕'' h'' _ hΩf y
    have hz : HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h) (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) y)
        (GlobalTheory.MixModel.adj (a⁻¹).val))) (GlobalTheory.MixModel.adj a.val) = y := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, GlobalTheory.MixModel.mt_mul_inv, Matrix.one_mul, Matrix.mul_assoc,
        ← GlobalTheory.MixModel.adj_mul, Units.mul_inv, GlobalTheory.MixModel.adj_one, Matrix.mul_one]
    have s2 := GlobalTheory.T.weilDatum_transports_heisenbergMatrixCoeffs D V W ψ χS χT ω hω m h f hf μ₀ 𝓕₀ h0.1 h0.2.1 (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C
      (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) y) (GlobalTheory.MixModel.adj (a⁻¹).val)))
    rw [GlobalTheory.T.weilAction_isotropicPartHom_of_frameMul D V W r C a m hC h, hz] at s2
    have s3 := GlobalTheory.T.restrictedNormSq_fourier_eq_isotropicMatrixCoeff D V V' W r C B hs C' h1 h2 h3 ψ hstd μ 𝓨 hμ μ₀ 𝓕₀ h0 μ'' 𝓕'' h'' f hf
      (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) y) (GlobalTheory.MixModel.adj (a⁻¹).val))
    simp only [hph] at s1 s3
    rw [← hN₁] at s1
    rw [← hN₀] at s3
    rw [← s1, s2, s3, hcov.2 y, hN₂, ← integral_const_mul]
    congr 1
    funext u
    ring)
  have e0 := congrFun key 0
  rw [hN₁, hN₂, hN₀] at e0
  simp only [resNorm, Matrix.mul_zero, Matrix.zero_mul, heisO_isoPart_zero] at e0
  obtain ⟨p1, fin1, eq1⟩ := GlobalTheory.T.thetaFunction_periodicNorm_finite_sqIntegral D ψ hstd V' W μ'' 𝓕'' h'' _ (hres.1 _ hΩf).2.1
  obtain ⟨p2, fin2, eq2⟩ := GlobalTheory.T.thetaFunction_periodicNorm_finite_sqIntegral D ψ hstd V' W μ'' 𝓕'' h'' _ (hres.1 f hf).2.1
  rw [eq1, eq2, hk] at e0
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_const_sqNorm_two_haar_fundamentalDomains D V' W μ' 𝓕' hμ' h𝓕' μ'' 𝓕'' h''
  rw [hc _ (hres.1 _ hΩf).2.1.cont p1, hc _ (hres.1 f hf).2.1.cont p2]
  have eR : (∫⁻ x in 𝓕'', ‖GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (ω (m, h) f) x‖ₑ ^ 2 ∂μ'').toReal =
      ((GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det a) : ℝ)) ^ W.rank *
        (∫⁻ x in 𝓕'', ‖GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 f x‖ₑ ^ 2 ∂μ'').toReal := by
    exact_mod_cast e0
  have eE : ∫⁻ x in 𝓕'', ‖GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (ω (m, h) f) x‖ₑ ^ 2 ∂μ'' =
      (GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det a) : ENNReal) ^ W.rank *
        ∫⁻ x in 𝓕'', ‖GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 f x‖ₑ ^ 2 ∂μ'' := by
    rw [← ENNReal.toReal_eq_toReal_iff' fin1 (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top) fin2),
      ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal]
    exact eR
  rw [eE, mul_left_comm]

end GlobalTheory.LeviNorm

end
end
end
