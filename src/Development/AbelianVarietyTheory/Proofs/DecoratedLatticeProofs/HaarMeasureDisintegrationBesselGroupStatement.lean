module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HaarFiniteAdeleDisintegrationStabilizerCompactStatement
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CastGAMemGFset
import Development.AbelianVarietyTheory.Definitions.Foundations.MeasurePreservingRmulQuotMeas
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselGroupQuotientFundamentalDomainCocompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentAnisotropicProjectionEqOne
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HaarOn
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.WuDecayPf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.UnfoldAbs
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
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HaarOn
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.RightInvOfLattice
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SCompact
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.ConjugationInvariantMeasure
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FiniteDimensionalMram
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.IndefiniteReal.AutomorphicEvaluation
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.IUnfold

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LintegralBesselGroupHaarEqConstMulProd

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Core.Mi.BesHaar

open scoped NNReal ENNReal

noncomputable def prodEquiv {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    {u : D.what₂.Word} {ψ : AddChar (AF D.host.F) ℂ} {A : HSp D} (B : SBes X h u ψ A) :
    (Formalism.L2.SG.Pf.SinfSub X.B.I X.eR (X.zR u) × Formalism.L2.SG.Pf.SfinSub X.B.I X.eR (X.zR u)) ≃ₜ*
      besGrp B.d B.o where
  toFun p := ⟨(iotaX X h).symm ((p.1 : X.B.I.Ginf), (p.2 : X.B.I.Gf)), by
    rw [((GlobalTheory.Core.Mi.besGrp_eq_sGroup D X h u ψ A B).1 _), ContinuousMulEquiv.apply_symm_apply]
    exact ⟨p.1.2, p.2.2⟩⟩
  invFun s := (⟨(iotaX X h s.1).1, (((GlobalTheory.Core.Mi.besGrp_eq_sGroup D X h u ψ A B).1 _).1 s.2).1⟩,
    ⟨(iotaX X h s.1).2, (((GlobalTheory.Core.Mi.besGrp_eq_sGroup D X h u ψ A B).1 _).1 s.2).2⟩)
  left_inv p := by
    ext <;> simp
  right_inv s := by
    ext
    simp
  map_mul' p q := by
    ext
    simp only [Subgroup.coe_mul, Prod.fst_mul, Prod.snd_mul]
    rw [← map_mul]
    rfl
  continuous_toFun := by
    refine Continuous.subtype_mk ((iotaX X h).symm.continuous.comp ?_) _
    exact (continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)
  continuous_invFun := by
    have hc : Continuous (fun s : besGrp B.d B.o => iotaX X h s.1) :=
      (iotaX X h).continuous.comp continuous_subtype_val
    exact ((continuous_fst.comp hc).subtype_mk _).prodMk ((continuous_snd.comp hc).subtype_mk _)

theorem iota_prodEquiv {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    {u : D.what₂.Word} {ψ : AddChar (AF D.host.F) ℂ} {A : HSp D} (B : SBes X h u ψ A)
    (p : Formalism.L2.SG.Pf.SinfSub X.B.I X.eR (X.zR u) × Formalism.L2.SG.Pf.SfinSub X.B.I X.eR (X.zR u)) :
    iotaX X h (prodEquiv X h B p).1 = ((p.1 : X.B.I.Ginf), (p.2 : X.B.I.Gf)) := by
  show iotaX X h ((iotaX X h).symm _) = _
  simp

theorem lintegral_besGrp_eq : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A) (μSf : Measure (Formalism.L2.SG.Pf.SfinSub X.B.I X.eR (X.zR u))), μSf.IsHaarMeasure → SigmaFinite μSf → IsHaarOnSet X.B.I (X.SinfU u) (((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2)) → ∃ c : ℝ, 0 < c ∧ ∀ Φ : X.B.I.GA → ENNReal, Measurable Φ → ∫⁻ s, Φ (iotaX X h s.1) ∂B.lev.μR = ENNReal.ofReal c * ∫⁻ a, ∫⁻ t, Φ (a, t.1) ∂μSf ∂(((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2)) := by
  intro D X h u ψ A B μSf hSf hσf hS
  haveI := hSf
  haveI := hσf
  have hR := Formalism.L2.SG.Pf.foldReady_holds X.B.I
  haveI : BorelSpace X.B.I.GA := hR.2.2.2.1
  haveI : SecondCountableTopology X.B.I.GA := hR.2.1
  haveI : LocallyCompactSpace X.B.I.GA := hR.1
  haveI : SecondCountableTopology X.B.I.Gf := Formalism.L2.SG.Pf.gf_secondCountable X.B.I
  haveI : SecondCountableTopology (GA D (D.sp.Y 0)) := (iotaX X h).toHomeomorph.secondCountableTopology
  haveI : LocallyCompactSpace (GA D (D.sp.Y 0)) := (iotaX X h).toHomeomorph.isClosedEmbedding.locallyCompactSpace
  have hcl : IsClosed (besGrp B.d B.o : Set (GA D (D.sp.Y 0))) := GlobalTheory.BesClosed.besGrp_isClosed _ _ _ _ _ _ B.d B.o
  haveI : LocallyCompactSpace (besGrp B.d B.o) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : B.lev.μR.IsHaarMeasure := (GlobalTheory.BesselQuot.besGrp_quotient D D.R.rS B.lev).1
  have hSi : IsClosed ((Formalism.L2.SG.Pf.SinfSub X.B.I X.eR (X.zR u) : Subgroup X.B.I.Ginf) : Set X.B.I.Ginf) := Formalism.L2.SG.WuDecayPf.isClosed_sinfU X u
  haveI : LocallyCompactSpace (Formalism.L2.SG.Pf.SinfSub X.B.I X.eR (X.zR u)) := hSi.isClosedEmbedding_subtypeVal.locallyCompactSpace
  obtain ⟨hHaar', -, -⟩ := Formalism.L2.SG.Pf.haarOnSet_isHaar_inst X.B.I (Formalism.L2.SG.Pf.SinfSub X.B.I X.eR (X.zR u)) hSi _ hS
  haveI := hHaar'
  have hmap := Formalism.L2.SG.Pf.map_comap_subgroup (Formalism.L2.SG.Pf.SinfSub X.B.I X.eR (X.zR u)) hSi _ hS.2.2.1
  set μS' := (((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2)).comap ((↑) : (Formalism.L2.SG.Pf.SinfSub X.B.I X.eR (X.zR u)) → X.B.I.Ginf) with hμS'
  haveI : SigmaFinite μS' := inferInstance
  let e := GlobalTheory.Core.Mi.BesHaar.prodEquiv X h B
  haveI : LocallyCompactSpace ((Formalism.L2.SG.Pf.SinfSub X.B.I X.eR (X.zR u)) × (Formalism.L2.SG.Pf.SfinSub X.B.I X.eR (X.zR u))) := e.toHomeomorph.isClosedEmbedding.locallyCompactSpace
  haveI : (B.lev.μR.map e.symm).IsHaarMeasure := e.symm.isHaarMeasure_map B.lev.μR
  haveI : (μS'.prod μSf).IsHaarMeasure := Measure.prod.instIsHaarMeasure μS' μSf
  have hcpos := Measure.haarScalarFactor_pos_of_isHaarMeasure (B.lev.μR.map e.symm) (μS'.prod μSf)
  set c : ℝ≥0 := (B.lev.μR.map e.symm).haarScalarFactor (μS'.prod μSf) with hc
  have hme : Measurable (e : (Formalism.L2.SG.Pf.SinfSub X.B.I X.eR (X.zR u)) × (Formalism.L2.SG.Pf.SfinSub X.B.I X.eR (X.zR u)) → besGrp B.d B.o) := e.continuous.measurable
  have hEq : B.lev.μR = (c • μS'.prod μSf).map e := by
    rw [hc, ← Measure.isMulLeftInvariant_eq_smul, Measure.map_map hme (show Measurable (e.symm : besGrp B.d B.o → (Formalism.L2.SG.Pf.SinfSub X.B.I X.eR (X.zR u)) × (Formalism.L2.SG.Pf.SfinSub X.B.I X.eR (X.zR u))) from e.symm.continuous.measurable)]
    simp
  refine ⟨(c : ℝ), hcpos, fun Φ hΦ => ?_⟩
  have hv : Measurable (fun p : (Formalism.L2.SG.Pf.SinfSub X.B.I X.eR (X.zR u)) × (Formalism.L2.SG.Pf.SfinSub X.B.I X.eR (X.zR u)) => ((p.1 : X.B.I.Ginf), (p.2 : X.B.I.Gf))) :=
    (measurable_subtype_coe.comp measurable_fst).prodMk (measurable_subtype_coe.comp measurable_snd)
  have hΦ' : Measurable (fun p : (Formalism.L2.SG.Pf.SinfSub X.B.I X.eR (X.zR u)) × (Formalism.L2.SG.Pf.SfinSub X.B.I X.eR (X.zR u)) => Φ ((p.1 : X.B.I.Ginf), (p.2 : X.B.I.Gf))) := hΦ.comp hv
  have hin : Measurable (fun a : X.B.I.Ginf => ∫⁻ t, Φ (a, (t : X.B.I.Gf)) ∂μSf) := by
    have : Measurable (Function.uncurry fun (a : X.B.I.Ginf) (t : Formalism.L2.SG.Pf.SfinSub X.B.I X.eR (X.zR u)) => Φ (a, (t : X.B.I.Gf))) :=
      hΦ.comp (measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd))
    exact this.lintegral_prod_right'
  have hΦι : Measurable (fun s : besGrp B.d B.o => Φ (iotaX X h s.1)) :=
    hΦ.comp ((iotaX X h).continuous.measurable.comp measurable_subtype_coe)
  rw [hEq, lintegral_map hΦι hme]
  have hιe : ∀ p : (Formalism.L2.SG.Pf.SinfSub X.B.I X.eR (X.zR u)) × (Formalism.L2.SG.Pf.SfinSub X.B.I X.eR (X.zR u)), iotaX X h (e p).1 = ((p.1 : X.B.I.Ginf), (p.2 : X.B.I.Gf)) :=
    GlobalTheory.Core.Mi.BesHaar.iota_prodEquiv X h B
  simp_rw [hιe]
  rw [lintegral_smul_measure, lintegral_prod _ hΦ'.aemeasurable, ← hmap,
    lintegral_map hin measurable_subtype_coe, ENNReal.ofReal_coe_nnreal, ENNReal.smul_def, smul_eq_mul]

end GlobalTheory.Core.Mi.BesHaar
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LintegralBesselGroupHaarEqConstMulProdStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.lintegral_besselGroup_haar_eq_const_mul_prod : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A) (μSf : Measure (Formalism.L2.SG.Pf.SfinSub X.B.I X.eR (X.zR u))), μSf.IsHaarMeasure → SigmaFinite μSf → IsHaarOnSet X.B.I (X.SinfU u) (((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2)) → ∃ c : ℝ, 0 < c ∧ ∀ Φ : X.B.I.GA → ENNReal, Measurable Φ → ∫⁻ s, Φ (iotaX X h s.1) ∂B.lev.μR = ENNReal.ofReal c * ∫⁻ a, ∫⁻ t, Φ (a, t.1) ∂μSf ∂(((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2)) := by
  first | exact @GlobalTheory.Core.Mi.BesHaar.lintegral_besGrp_eq | exact GlobalTheory.Core.Mi.BesHaar.lintegral_besGrp_eq | (intros; apply GlobalTheory.Core.Mi.BesHaar.lintegral_besGrp_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealStabilizerProductMeasureIsHaarOnSet

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MuSHaar

open scoped Pointwise

open Formalism.L2.SG.Pf Formalism.L2.SG.Pf.Sinf Formalism.L2.SG.PoincareInHH.PoincareSetting

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word)

theorem muN_conj (h : X.B.I.Ginf) (hh : h ∈ Hinf X u) :
    (X.muN u).map (fun x => h * x * h⁻¹) = X.muN u := by
  have hNc : IsClosed (X.NinfU u) := isClosed_ninfU X u
  have hHc : IsCompact ((Hinf X u : Subgroup X.B.I.Ginf) : Set X.B.I.Ginf) := hinf_compact X u
  obtain ⟨-, hfin, hpos⟩ := haarOnSet_isHaar_inst X.B.I (NinfSub X.eR (X.zR u)) (isClosed_ninfU X u)
    (X.muN u) (X.muN_haar u)
  have hgN : QPK.IsGrp (X.NinfU u) :=
    ⟨(NinfSub X.eR (X.zR u)).one_mem, fun a ha b hb => (NinfSub X.eR (X.zR u)).mul_mem ha hb,
      fun a ha => (NinfSub X.eR (X.zR u)).inv_mem ha⟩
  have hgH : QPK.IsGrp ((Hinf X u : Subgroup X.B.I.Ginf) : Set X.B.I.Ginf) :=
    ⟨(Hinf X u).one_mem, fun a ha b hb => (Hinf X u).mul_mem ha hb, fun a ha => (Hinf X u).inv_mem ha⟩
  exact QPK.conjugation_invariant_measure X.B.I.Ginf (X.NinfU u) _ hNc hHc hgN hgH
    (fun h hh m hm => conj_ninf X u hh hm) (X.muN u) (X.muN_haar u) ⟨fun K hK => hfin K hK⟩
    (fun U hU hne => (hpos U hU hne).ne') h hh

theorem muS_compact {K : Set X.B.I.Ginf} (hK : IsCompact K) :
    ((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2) K < ⊤ := by
  haveI := (X.muN_haar u).1
  haveI := (X.muH_haar u).1
  have hmul : Measurable (fun p : X.B.I.Ginf × X.B.I.Ginf => p.1 * p.2) := measurable_fst.mul measurable_snd
  set L : Set X.B.I.Ginf := (K * ((Hinf X u : Subgroup X.B.I.Ginf) : Set X.B.I.Ginf)⁻¹) ∩ X.NinfU u with hL
  have hLc : IsCompact L := (hK.mul (hinf_compact X u).inv).inter_right (isClosed_ninfU X u)
  rw [Measure.map_apply hmul hK.isClosed.measurableSet]
  calc ((X.muN u).prod (X.muH u)) ((fun p : X.B.I.Ginf × X.B.I.Ginf => p.1 * p.2) ⁻¹' K)
      ≤ ((X.muN u).prod (X.muH u)) (L ×ˢ Set.univ) := by
        refine measure_mono_ae ?_
        filter_upwards [ae_NH X u] with p hp hpK
        refine ⟨⟨?_, hp.1⟩, Set.mem_univ _⟩
        have e : p.1 = (p.1 * p.2) * p.2⁻¹ := by group
        rw [e]
        exact Set.mul_mem_mul hpK (Set.inv_mem_inv.2 hp.2)
    _ = X.muN u L * X.muH u Set.univ := Measure.prod_prod _ _
    _ < ⊤ := ENNReal.mul_lt_top (muN_compact X u hLc) (hFinite_holds X u)

theorem muS_isHaarOnSet : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word),
    IsHaarOnSet X.B.I (X.SinfU u) (((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2)) := by
  intro D X u
  obtain ⟨hNσ, hN0, -, hNinv⟩ := X.muN_haar u
  obtain ⟨hHσ, hH0, -, hHinv⟩ := X.muH_haar u
  haveI := hNσ
  haveI := hHσ
  have hmul : Measurable (fun p : X.B.I.Ginf × X.B.I.Ginf => p.1 * p.2) := measurable_fst.mul measurable_snd
  refine ⟨?_, ?_, ?_, ?_⟩
  · haveI : IsFiniteMeasureOnCompacts (((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2)) :=
      ⟨fun K hK => muS_compact X u hK⟩
    infer_instance
  · intro h0
    have h1 := congrArg (fun μ : Measure X.B.I.Ginf => μ Set.univ) h0
    simp only [Measure.map_apply hmul MeasurableSet.univ, Set.preimage_univ, Measure.coe_zero,
      Pi.zero_apply] at h1
    rw [← Set.univ_prod_univ, Measure.prod_prod, mul_eq_zero, Measure.measure_univ_eq_zero,
      Measure.measure_univ_eq_zero] at h1
    exact h1.elim hN0 hH0
  · exact ae_iff.1 (Formalism.L2.SG.WuDecayPf.muSOn X u)
  · intro s hs
    obtain ⟨h0, hh0, n0, hn0, rfl⟩ := levi X u hs
    have hf : (X.muN u).map (fun x => h0 * (n0 * x) * h0⁻¹) = X.muN u := by
      have e : (fun x => h0 * (n0 * x) * h0⁻¹) = (fun x => h0 * x * h0⁻¹) ∘ (fun x => n0 * x) := rfl
      rw [e, ← Measure.map_map (by fun_prop) (by fun_prop), hNinv n0 hn0, muN_conj X u h0 hh0]
    have hg : (X.muH u).map (fun y => h0 * y) = X.muH u := hHinv h0 hh0
    have hfm : Measurable (fun x : X.B.I.Ginf => h0 * (n0 * x) * h0⁻¹) := by fun_prop
    have hgm : Measurable (fun y : X.B.I.Ginf => h0 * y) := by fun_prop
    calc (((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2)).map (fun x => h0 * n0 * x)
        = ((X.muN u).prod (X.muH u)).map ((fun x => h0 * n0 * x) ∘ (fun p => p.1 * p.2)) :=
          Measure.map_map (by fun_prop) hmul
      _ = ((X.muN u).prod (X.muH u)).map ((fun p => p.1 * p.2) ∘
            Prod.map (fun x => h0 * (n0 * x) * h0⁻¹) (fun y => h0 * y)) := by
          congr 1; funext p; simp only [Function.comp, Prod.map]; group
      _ = (((X.muN u).prod (X.muH u)).map
            (Prod.map (fun x => h0 * (n0 * x) * h0⁻¹) (fun y => h0 * y))).map (fun p => p.1 * p.2) :=
          (Measure.map_map hmul (hfm.prodMap hgm)).symm
      _ = (((X.muN u).map (fun x => h0 * (n0 * x) * h0⁻¹)).prod ((X.muH u).map (fun y => h0 * y))).map
            (fun p => p.1 * p.2) := by rw [Measure.map_prod_map _ _ hfm hgm]
      _ = ((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2) := by rw [hf, hg]

end GlobalTheory.MuSHaar
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealStabilizerProductMeasureIsHaarOnSetStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.real_stabilizer_product_measure_isHaarOnSet : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word), IsHaarOnSet X.B.I (X.SinfU u) (((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2)) := by
  first | exact @GlobalTheory.MuSHaar.muS_isHaarOnSet | exact GlobalTheory.MuSHaar.muS_isHaarOnSet | (intros; apply GlobalTheory.MuSHaar.muS_isHaarOnSet <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HaarMeasureDisintegrationBesselGroup

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi.Disint

theorem disint : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A), ∃ c : ℝ, 0 < c ∧ ∀ G : X.B.I.GA → ENNReal, Measurable G → (∀ x, G x ≠ 0 → ∃ s ∈ SfinU X u, ∃ k ∈ X.K2, x.2 = s * X.xu u * k) → ∫⁻ x, G x ∂(X.B.I.muA X.B.μf) = ENNReal.ofReal c * ∫⁻ y, ∫⁻ s, ∫⁻ k in X.K2, G (iotaX X h s.1 * (y, X.xu u) * (1, k)) ∂X.B.μf ∂B.lev.μR ∂(X.nuQ u) := by
  intro D X h u ψ A B
  obtain ⟨μSf, hHaar, hσ, c₁, hc₁, hfin⟩ := GlobalTheory.T.haar_finite_adele_disintegration_stabilizer_compact D X u
  obtain ⟨c₃, hc₃, hR⟩ := GlobalTheory.T.lintegral_besselGroup_haar_eq_const_mul_prod D X h u ψ A B μSf hHaar hσ (GlobalTheory.T.real_stabilizer_product_measure_isHaarOnSet D X u)
  refine ⟨c₁ / c₃, div_pos hc₁ hc₃, ?_⟩
  intro G hGm hsupp
  haveI : SecondCountableTopology X.B.I.Gf := Formalism.L2.SG.Pf.gf_secondCountable X.B.I
  haveI := hσ
  set μS := ((X.muN u).prod (X.muH u)).map (fun p : X.B.I.Ginf × X.B.I.Ginf => p.1 * p.2) with hμS

  set g : X.B.I.Ginf → ENNReal := fun x => ∫⁻ t, ∫⁻ k in X.K2, G (x, t.1 * X.xu u * k) ∂X.B.μf ∂μSf with hgdef
  have hg : Measurable g := by
    have hΨ : Measurable (fun p : (X.B.I.Ginf × Formalism.L2.SG.Pf.SfinSub X.B.I X.eR (X.zR u)) × X.B.I.Gf =>
        G (p.1.1, p.1.2.1 * X.xu u * p.2)) :=
      hGm.comp (measurable_fst.fst.prodMk
        (((measurable_subtype_coe.comp measurable_fst.snd).mul_const _).mul measurable_snd))
    exact (hΨ.lintegral_prod_right' (ν := X.B.μf.restrict X.K2)).lintegral_prod_right' (ν := μSf)
  have hL : ∫⁻ x, G x ∂(X.B.I.muA X.B.μf) = ENNReal.ofReal c₁ * ∫⁻ y, ∫⁻ a, g (a * y) ∂μS ∂(X.nuQ u) := by
    have e0 : X.B.I.muA X.B.μf = (Formalism.L2.SG.ProjRows.muInf X.B.I).prod X.B.μf := rfl
    rw [e0, lintegral_prod _ hGm.aemeasurable]
    have e1 : ∀ x, ∫⁻ z, G (x, z) ∂X.B.μf = ENNReal.ofReal c₁ * g x := fun x =>
      hfin (fun z => G (x, z)) (hGm.comp measurable_prodMk_left) (fun z hz => hsupp (x, z) hz)
    simp_rw [e1]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, X.nuQ_weil u g hg]
  have hRy : ∀ y : X.B.I.Ginf, ∫⁻ s, ∫⁻ k in X.K2, G (iotaX X h s.1 * (y, X.xu u) * (1, k)) ∂X.B.μf ∂B.lev.μR =
      ENNReal.ofReal c₃ * ∫⁻ a, g (a * y) ∂μS := by
    intro y
    set Φ : X.B.I.GA → ENNReal := fun p => ∫⁻ k in X.K2, G (p.1 * y, p.2 * X.xu u * k) ∂X.B.μf with hΦ
    have hΦm : Measurable Φ := by
      have : Measurable (fun q : X.B.I.GA × X.B.I.Gf => G (q.1.1 * y, q.1.2 * X.xu u * q.2)) :=
        hGm.comp ((measurable_fst.fst.mul_const y).prodMk ((measurable_fst.snd.mul_const _).mul measurable_snd))
      exact this.lintegral_prod_right' (ν := X.B.μf.restrict X.K2)
    have e : ∀ s : besGrp B.d B.o, ∫⁻ k in X.K2, G (iotaX X h s.1 * (y, X.xu u) * (1, k)) ∂X.B.μf = Φ (iotaX X h s.1) := by
      intro s
      refine lintegral_congr fun k => ?_
      congr 1
      ext <;> simp
    simp_rw [e]
    rw [hR Φ hΦm]
  calc ∫⁻ x, G x ∂(X.B.I.muA X.B.μf) = ENNReal.ofReal c₁ * ∫⁻ y, ∫⁻ a, g (a * y) ∂μS ∂(X.nuQ u) := hL
    _ = ENNReal.ofReal (c₁ / c₃) * (ENNReal.ofReal c₃ * ∫⁻ y, ∫⁻ a, g (a * y) ∂μS ∂(X.nuQ u)) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (div_pos hc₁ hc₃).le, div_mul_cancel₀ _ hc₃.ne']
    _ = _ := by
        congr 1
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact (lintegral_congr fun y => hRy y).symm

end GlobalTheory.Core.Mi.Disint
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HaarMeasureDisintegrationBesselGroupStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.haarMeasure_disintegration_besselGroup : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A), ∃ c : ℝ, 0 < c ∧ ∀ G : X.B.I.GA → ENNReal, Measurable G → (∀ x, G x ≠ 0 → ∃ s ∈ SfinU X u, ∃ k ∈ X.K2, x.2 = s * X.xu u * k) → ∫⁻ x, G x ∂(X.B.I.muA X.B.μf) = ENNReal.ofReal c * ∫⁻ y, ∫⁻ s, ∫⁻ k in X.K2, G (iotaX X h s.1 * (y, X.xu u) * (1, k)) ∂X.B.μf ∂B.lev.μR ∂(X.nuQ u) := by
  first | exact @GlobalTheory.Core.Mi.Disint.disint | exact GlobalTheory.Core.Mi.Disint.disint | (intros; apply GlobalTheory.Core.Mi.Disint.disint <;> assumption)
end
end
