module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OneMeasureSizes
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspFormsRapidDecay
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
public import Development.AbelianVarietyTheory.Counterexamples.TwistSurvey.ConjModelCast
public import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.ParabolicAtStandardWeylElement
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasAtOf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcFiniteAndSchurMult
public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.VolPairExAndFinVol
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocallyCompactSecondCountableT2
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JEvExists
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Mathlib.Tactic.Basify

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspFormsRapidDecayStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta MeasureTheory NumberField Matrix GlobalTheory.CuspGeo
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.cusp_forms_rapid_decay : GlobalTheory.Published.CuspRapidDecay := by
  first | exact @GlobalTheory.RapidDecay.cuspRapidDecay | exact GlobalTheory.RapidDecay.cuspRapidDecay | (intros; apply GlobalTheory.RapidDecay.cuspRapidDecay <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdLowestKTypeDimsIndepComplexEmbedding

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.DimProdLab

theorem lab_spec {D : D7} (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau) :
    labE σ (lab σ ρ) = tauE D ρ ∨ labE σ (lab σ ρ) = (starRingEnd ℂ).comp (tauE D ρ) := by
  unfold lab; rw [dite_eq_left (GlobalTheory.ConjReading.lab_exists σ ρ)]; exact (GlobalTheory.ConjReading.lab_exists σ ρ).choose_spec

theorem lab_injective {D : D7} (σ : D.what₂.LL →+* ℂ) : Function.Injective (lab σ : D.what₂.Tau → D.what₂.Tau) := by
  intro ρ ρ' h
  have cc : ∀ f : D.host.E →+* ℂ, (starRingEnd ℂ).comp ((starRingEnd ℂ).comp f) = f := GlobalTheory.ConjReading.conj_conj
  rcases lab_spec σ ρ with h1 | h1 <;> rcases lab_spec σ ρ' with h2 | h2 <;> rw [h] at h1
  · exact Formalism.IndefR.Fock.KV.tauE_injective (h1.symm.trans h2)
  · exact absurd (h1.symm.trans h2) (Formalism.IndefR.Fock.KV.tauE_ne_conj _ _)
  · exact absurd (h2.symm.trans h1) (Formalism.IndefR.Fock.KV.tauE_ne_conj _ _)
  · have e := congrArg (fun f => (starRingEnd ℂ).comp f) (h1.symm.trans h2)
    simp only [cc] at e
    exact Formalism.IndefR.Fock.KV.tauE_injective e

theorem dimK_congr {R : Ranks} (hc : HCParam R) {a b : ℕ × ℕ} (e : a = b) :
    dimK a.1 a.2 (Formalism.L2.NTheta.kapW hc a.1 a.2) = dimK b.1 b.2 (Formalism.L2.NTheta.kapW hc b.1 b.2) := by
  subst e; rfl

theorem prod_dims (D : D7) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) :
    (∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℂ)) = ((∏ τ, GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ : ℝ) : ℂ) := by
  set s := D.R.sigW ((i : ℕ) + 1)
  let hd : D.what₂.Tau → ℚ := fun τ => dimK s.1 s.2 (Formalism.L2.NTheta.kapW (D.hc τ) s.1 s.2)
  have h1 : ∀ ρ, dimK _ _ (kapAt (Wc D i) σ ρ) = hd (lab σ ρ) := fun ρ =>
    dimK_congr (D.hc (lab σ ρ)) (Formalism.IndefR.Fock.KV.sig_Wc i ρ)
  have h2 : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ = ((hd τ : ℚ) : ℝ) := fun τ =>
    congrArg (fun q : ℚ => (q : ℝ)) (dimK_congr (D.hc τ) (Formalism.IndefR.Fock.KV.sig_Wc i τ))
  have hb : Function.Bijective (lab σ : D.what₂.Tau → D.what₂.Tau) := (lab_injective σ).bijective_of_finite
  simp only [h1, h2]
  refine (Equiv.prod_comp (Equiv.ofBijective _ hb) (fun τ => ((hd τ : ℚ) : ℂ))).trans ?_
  push_cast
  rfl

end GlobalTheory.DimProdLab
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdLowestKTypeDimsIndepComplexEmbeddingStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.prod_lowestKTypeDims_indep_complexEmbedding : ∀ (D : D7) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℂ)) = ((∏ τ, GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ : ℝ) : ℂ) := by
  first | exact @GlobalTheory.DimProdLab.prod_dims | exact GlobalTheory.DimProdLab.prod_dims | (intros; apply GlobalTheory.DimProdLab.prod_dims <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExactRatioOfFundamentalDomain

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ExactRatioProof

open scoped InnerProductSpace ComplexConjugate

theorem L1 : ∀ (D : D7) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℂ)) = ((∏ τ, GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ : ℝ) : ℂ) := GlobalTheory.T.prod_lowestKTypeDims_indep_complexEmbedding

theorem K2aux (D : D7) (T : CoreJ D) (h : LawsJ T) (i : Fin D.R.m) (s : T.Q.c.F →+* ℂ) (hs : GoodEmb T.Q.c s)
    (f : FDSec (T.U ((i : ℕ) + 1) s).X) (W : HSp D) (hV : T.V ((i : ℕ) + 1) s = W) :
    eLpNorm' (fun q : AutQ W => ‖(hV ▸ ((lieFacZ (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW D i) : ℂ) •
      adel (T.V ((i : ℕ) + 1) s) (T.dict ((i : ℕ) + 1) s)
        (muPin (T.V ((i : ℕ) + 1) s) (T.dict ((i : ℕ) + 1) s) (T.mu ((i : ℕ) + 1) s) (T.cE ((i : ℕ) + 1) s)) f) :
          GA D W → ℂ) q.out‖) 2 (muQ1 W) =
      ENNReal.ofReal (lieFacZ (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW D i)) *
        petE (T.V ((i : ℕ) + 1) s) (T.dict ((i : ℕ) + 1) s) (muQ1 (T.V ((i : ℕ) + 1) s))
          (modelWt (T.U ((i : ℕ) + 1) s) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW D i)) f := by
  subst hV
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hmu := h.muUnit _ hj s hs
  have hcu := h.cUnit _ hj s hs
  set c := lieFacZ (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW D i) with hcdef
  have hc0 : 0 < c := lieFacZ_pos _ _
  unfold petE
  rw [← Real.enorm_eq_ofReal hc0.le, ← eLpNorm'_const_smul c (by norm_num)]
  refine eLpNorm'_congr_norm_ae (Filter.Eventually.of_forall fun q => ?_)
  simp only [Pi.smul_apply, smul_eq_mul, norm_norm, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hc0, adel_muPin]
  rw [hcu, hmu.2.1]
  simp only [abs_one, one_mul, abs_norm, abs_of_nonneg (ptN_nonneg _ _ _)]
  unfold ptN
  rw [pnorm_eq_of_unit _ _ _ _ (hmu.2.2.2 _)]

theorem K2 : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ (i : Fin D.R.m) (s : T.Q.c.F →+* ℂ), GoodEmb T.Q.c s → ∀ (hV : T.V ((i : ℕ) + 1) s = Wc D i) (f : FDSec (T.U ((i : ℕ) + 1) s).X), eLpNorm' (fun q : AutQ (Wc D i) => ‖GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.adFun T i hV f q.out‖) 2 (muQ1 (Wc D i)) = ENNReal.ofReal (lieFacZ (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW D i)) * petE (T.V ((i : ℕ) + 1) s) (T.dict ((i : ℕ) + 1) s) (muQ1 (T.V ((i : ℕ) + 1) s)) (modelWt (T.U ((i : ℕ) + 1) s) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW D i)) f :=
  fun D T h i s hs hV f => K2aux D T h i s hs f (Wc D i) hV

theorem K3 : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ (i : Fin D.R.m) (s : T.Q.c.F →+* ℂ), GoodEmb T.Q.c s → ∀ f ∈ GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.scalarForms T i s, petE (T.V ((i : ℕ) + 1) s) (T.dict ((i : ℕ) + 1) s) (muQ1 (T.V ((i : ℕ) + 1) s)) (modelWt (T.U ((i : ℕ) + 1) s) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW D i)) f ≠ ⊤ := by
  intro D T h i s hs f hf
  obtain ⟨th, hr, -, hdu⟩ := h.dictU _ ⟨Nat.le_add_left _ _, i.2⟩ s hs
  exact petE_ne_top _ _ _ prob_le_one hdu.2.2.2.1 hf

end GlobalTheory.ExactRatioProof
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.QuotMeasureEqSmul

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ReadingNorm

theorem sq_eq_inner {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (x : H) :
    ((‖x‖ ^ 2 : ℝ) : ℂ) = inner ℂ x x := by
  rw [Complex.ofReal_pow, inner_self_eq_norm_sq_to_K]
  rfl

variable {D : D7}

theorem quotMeasure_eq_smul (V : HSp D) (hs : V.SigOK) {ν : Measure (GA D V)} {𝓕 : Set (GA D V)} (hν : ν.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 ν) : GlobalTheory.AutomorphicL2Unitary.autMeasure V ν = ν 𝓕 • muQ1 V := by
  obtain ⟨hP, hV⟩ := GlobalTheory.FinalJoin2.volPairEx_and_finVol D V hs
  have hp := GlobalTheory.AutomorphicL2Unitary.isVolPair_volPair hP
  have := hp.1.1
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D V
  have e := Measure.isMulLeftInvariant_eq_smul ν (volPair V).1
  set c := Measure.haarScalarFactor ν (volPair V).1
  have e1 : GlobalTheory.AutomorphicL2Unitary.autMeasure V ν = (c : ENNReal) • muQ V := by
    rw [GlobalTheory.AutomorphicL2Unitary.muQ_eq hP, ← GlobalTheory.AutomorphicL2Unitary.quotMeasure_smul]
    exact congrArg _ e
  have e2 : ν 𝓕 = c * muQ V Set.univ := by
    rw [← GlobalTheory.AutomorphicL2Unitary.quotMeasure_univ h𝓕]
    exact congrArg (fun m : Measure (AutQ V) => m Set.univ) e1
  rw [e1, e2, muQ1, if_pos (show _ ∧ _ from hV), smul_smul, mul_assoc, ENNReal.mul_inv_cancel hV.1 hV.2, mul_one]

theorem integral_star_mul (V : HSp D) (hs : V.SigOK) {ν : Measure (GA D V)} {𝓕 : Set (GA D V)} (hν : ν.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 ν) (φ : GA D V → ℂ) (hφ : ∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g)
    (ψ : AutQ V → ℂ) (hψ : MemLp ψ 2 (muQ1 V)) (c : ℝ) (h : ∀ q, ‖φ q.out‖ = c * ‖ψ q‖) :
    ∫ g in 𝓕, star (φ g) * φ g ∂ν = (((ν 𝓕).toReal * (c * ‖hψ.toLp ψ‖) ^ 2 : ℝ) : ℂ) := by
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D V
  have hL : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) φ := hφ
  have e1 := GlobalTheory.AutomorphicL2Unitary.integral_quotMeasure h𝓕
    (fun q => star (GlobalTheory.AutomorphicL2Unitary.descend (GQ V) φ q) * GlobalTheory.AutomorphicL2Unitary.descend (GQ V) φ q)
  simp only [hL.descend_mk] at e1
  have e2 : ((‖hψ.toLp ψ‖ ^ 2 : ℝ) : ℂ) = ∫ q, ((‖ψ q‖ ^ 2 : ℝ) : ℂ) ∂muQ1 V := by
    rw [sq_eq_inner, MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hψ.coeFn_toLp] with q hq
    rw [hq, sq_eq_inner]
  rw [← e1, show GlobalTheory.AutomorphicL2Unitary.quotMeasure (GQ V) ν = _ from quotMeasure_eq_smul V hs hν h𝓕, integral_smul_measure, mul_pow,
    Complex.ofReal_mul, Complex.ofReal_mul, e2, ← integral_const_mul, Complex.real_smul]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  show star (φ q.out) * φ q.out = ((c ^ 2 : ℝ) : ℂ) * ((‖ψ q‖ ^ 2 : ℝ) : ℂ)
  rw [← Complex.ofReal_mul, ← mul_pow, ← h, Complex.ofReal_pow]
  exact Complex.conj_mul' _

end GlobalTheory.ReadingNorm
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CovolumeRatioEqIndex

section

@[expose] public section

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.ExactRatioProof
open scoped InnerProductSpace ComplexConjugate
theorem exact_covolume_ratio : ∀ (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) (D : D7) (Tu : Type) (C : LevCh D Tu) (t0 : Tu) (hC : C.Is t0) (i : Fin D.R.m) (P : LevelP C.Pg D.R.r ℂ) (μ : MeasureTheory.Measure (GA D (Wc D i))) (𝓕 : Set (GA D (Wc D i))) (hF : IsMeasFD (Wc D i) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW C i P) μ 𝓕), GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.ExactRatio C i P μ 𝓕 := by
  intro hP D Tu C t0 hC i P μ 𝓕 hF T _ hT ha θ hθ σ M hV F hFm f hf hc
  have hμ : μ.IsHaarMeasure := hF.1.1
  have hS : ∃ c, IsMultIP M μ 𝓕 F F c :=
    GlobalTheory.MultFinite.schurMult GlobalTheory.T.cusp_forms_rapid_decay μ 𝓕 hθ hμ hF.2 F hFm F hFm
  refine ⟨hS, ?_⟩
  obtain ⟨v, hv1, hnorm⟩ : ∃ v : M.Vec, (∀ τ, ‖(v τ : M.H τ)‖ = 1) ∧
      ∀ g, ‖F v g‖ = ‖GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.adFun T i hV f g‖ := by
    rcases hc with ⟨-, v, hv, e⟩ | ⟨-, v, hv, e⟩
    · exact ⟨v, fun τ => (hv τ).1, fun g => by rw [e]⟩
    · exact ⟨v, hv, fun g => by rw [e, RCLike.norm_conj]⟩
  have hFM := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 hFm
  have haut := hFM.aut v
  have h1 := (ipM_spec M μ 𝓕 F F hS v v).2
  have hprod : ∏ τ, ⟪(v τ : M.H τ), (v τ : M.H τ)⟫_ℂ = 1 :=
    Finset.prod_eq_one fun τ _ => by rw [inner_self_eq_norm_sq_to_K, hv1 τ]; simp
  rw [hprod, mul_one] at h1
  have hs : GoodEmb T.Q.c (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.gd T σ) := goodEmb_goodOf _ _
  set c := lieFacZ (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW D i) with hcdef
  have hc0 : 0 < c := lieFacZ_pos _ _
  set ψ : AutQ (Wc D i) → ℂ := fun q => ((‖F v q.out‖ / c : ℝ) : ℂ) with hψdef
  have hK2 := K2 D T hT i _ hs hV f
  have hK3 := K3 D T hT i _ hs f hf
  have hψm : AEStronglyMeasurable ψ (muQ1 (Wc D i)) := by
    haveI : BorelSpace (GA D (Wc D i)) := ⟨rfl⟩
    have hm : Measurable fun q : AutQ (Wc D i) => F v q.out := by
      rw [measurable_from_quotient]
      have e : ((fun q : AutQ (Wc D i) => F v q.out) ∘ Quotient.mk'') = F v := funext fun g => by
        have h2 : g * (Quotient.mk (QuotientGroup.rightRel (GQ (Wc D i))) g).out⁻¹ ∈ GQ (Wc D i) :=
          QuotientGroup.rightRel_apply.1 (Quotient.mk_out g)
        have h3 := haut.left _ h2 (Quotient.mk (QuotientGroup.rightRel (GQ (Wc D i))) g).out
        rw [inv_mul_cancel_right] at h3
        exact h3.symm
      rw [e]
      exact haut.cont.measurable
    refine Measurable.aestronglyMeasurable ?_
    exact Complex.measurable_ofReal.comp ((hm.norm).div_const c)
  have hE : eLpNorm ψ 2 (muQ1 (Wc D i)) = petE (T.V ((i : ℕ) + 1) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.gd T σ))
      (T.dict ((i : ℕ) + 1) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.gd T σ)) (muQ1 (T.V ((i : ℕ) + 1) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.gd T σ)))
      (modelWt (T.U ((i : ℕ) + 1) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.gd T σ)) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW D i)) f := by
    have e1 : eLpNorm ψ 2 (muQ1 (Wc D i)) =
        eLpNorm (c⁻¹ • fun q : AutQ (Wc D i) => ‖GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.adFun T i hV f q.out‖) 2 (muQ1 (Wc D i)) := by
      have heq : ∀ q : AutQ (Wc D i), ‖ψ q‖ =
          (c⁻¹ • fun q : AutQ (Wc D i) => ‖GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.adFun T i hV f q.out‖) q := by
        intro q
        simp only [hψdef, Pi.smul_apply, smul_eq_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_norm,
          abs_of_pos hc0, hnorm]
        ring
      have hm : AEStronglyMeasurable (c⁻¹ • fun q : AutQ (Wc D i) => ‖GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.adFun T i hV f q.out‖) (muQ1 (Wc D i)) :=
        hψm.norm.congr (Filter.Eventually.of_forall heq)
      refine eLpNorm_congr_norm_ae hψm hm (Filter.Eventually.of_forall fun q => ?_)
      rw [← heq q, Real.norm_eq_abs, abs_norm]
    have hadm : AEStronglyMeasurable (fun q : AutQ (Wc D i) =>
        ‖GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.adFun T i hV f q.out‖)
        (muQ1 (Wc D i)) := by
      have heq : (fun q : AutQ (Wc D i) =>
          ‖GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.adFun T i hV f q.out‖) =
          c • (fun q => ‖ψ q‖) := by
        funext q
        simp only [hψdef, Pi.smul_apply, smul_eq_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_div, abs_norm, abs_of_pos hc0, hnorm]
        field_simp
      rw [heq]
      exact hψm.norm.const_smul c
    rw [e1, eLpNorm_const_smul]
    conv_lhs =>
      rw [eLpNorm_eq_eLpNorm' (by norm_num) (by simp) hadm]
    have ht : (2 : ENNReal).toReal = 2 := by norm_num
    rw [ht, hK2]
    rw [← mul_assoc, Real.enorm_eq_ofReal (inv_nonneg.2 hc0.le),
      ← ENNReal.ofReal_mul (inv_nonneg.2 hc0.le), inv_mul_cancel₀ hc0.ne', ENNReal.ofReal_one, one_mul]
  have hψ : MemLp ψ 2 (muQ1 (Wc D i)) := by rw [memLp_iff, hE]; exact lt_top_iff_ne_top.2 hK3
  have hI := GlobalTheory.ReadingNorm.integral_star_mul (Wc D i) (D.sp.W_sig _) hμ hF.2 (F v) haut.left ψ hψ c
    (fun q => by
      simp only [hψdef, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_norm, abs_of_pos hc0]
      field_simp)
  have hL : ‖hψ.toLp ψ‖ = (petE (T.V ((i : ℕ) + 1) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.gd T σ))
      (T.dict ((i : ℕ) + 1) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.gd T σ)) (muQ1 (T.V ((i : ℕ) + 1) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.gd T σ)))
      (modelWt (T.U ((i : ℕ) + 1) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.gd T σ)) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW D i)) f).toReal := by
    rw [Lp.norm_toLp, hE]
  rw [Formalism.IndefR.Links.ipAt, ← h1, hI, L1 D i σ, hL]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.ratio GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.probSq
  push_cast
  ring
end GlobalTheory.ExactRatioProof
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta

theorem _root_.GlobalTheory.T.covolume_ratio_eq_index : ∀ (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) (D : D7) (Tu : Type) (C : LevCh D Tu) (t0 : Tu) (hC : C.Is t0) (i : Fin D.R.m) (P : LevelP C.Pg D.R.r ℂ) (μ : MeasureTheory.Measure (GA D (Wc D i))) (𝓕 : Set (GA D (Wc D i))) (hF : IsMeasFD (Wc D i) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW C i P) μ 𝓕), GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.ExactRatio C i P μ 𝓕 := by
  first | exact @_root_.GlobalTheory.ExactRatioProof.exact_covolume_ratio | exact _root_.GlobalTheory.ExactRatioProof.exact_covolume_ratio | (intros; apply _root_.GlobalTheory.ExactRatioProof.exact_covolume_ratio <;> assumption)
end
end
end
