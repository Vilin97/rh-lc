module

public import Formalism.LocalToGlobal.InertKernelTheory.DefsRepDict
public import Formalism.LocalToGlobal.InertKernelTheory.GenusOneModelExistsLattice
public import Formalism.LocalToGlobal.InertKernelTheory.StatementAlgT
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsEntC
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ColNorm
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Formalism.LocalToGlobal.InertKernelTheory.StatementInt
public import Formalism.LocalToGlobal.KernelLattices.AdaptedEnt
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.KernelRationalReferenceTuple
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdmissibleKernelSeriesInertPrimeNonConjugateFrobStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConditionsAtStandardKernelComparisonTrueColumnsStatement
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsConstantCoeffOne
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrobeniusConjugationConditionsAdaptedKernelDatum
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
public import Formalism.LocalRingCardinality.HostCls
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.GlobalOrthonormalBasisFour
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntWAPlaces
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.JetsOrth
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.BiextensionRelation
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelClassSumsCarryChainComplexFormsStatement
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaZJetsThree
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelDatumEntriesIntegralAwayFromD
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AtLinAdaptedCoefEqStandardSeries
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CombOfTied
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsStandardBasesLatticeAtPlaceOfAdaptedBasesStatement
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormPadicEmbeddingLeOneOfMemInverseHalfDifferent
import Development.AutomorphicArithmetic.CyclotomicBounds.SmallFacts
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ShapeNormalisedThetaCombinationsDualBasesAtDStatement
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StdBases
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FormsPin
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelEntriesHypOfColumnSideProperties
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelPairScalarsIsUnitTrueColumnsStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalisedThetaCMCurveTheoremsOfAlgebraicTranslaStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrbitBoundStandardSeriesInertPlacesStatement
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepZeroTrivialStabilisersTrueColumns
import Formalism.PeriodIntegrals.OrbJetBase

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrobeniusConjugationConditionsAdaptedKernelDatumStatement

section

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

theorem _root_.GlobalTheory.T.frobeniusConjugation_conditions_adaptedKernelDatum : Formalism.L2.KerInert.AlgTAll → (∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), 5 ≤ p → (IsResidueClassZero D p ∨ IsSg D p) → HostAt B χ p lam) → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : Formalism.L2.Ker.KerEntTied ex), t.Hyp → t.Adapted → 3 ≤ D.host.splitBound → ∀ ep be sg, OrbitPlaces.EvenConditionsAtC (OrbitPlaces.ofKer (nuRowOK D) t.ent ep be sg) Y := by
  first | exact @GlobalTheory.Ggeo.frobeniusConjugation_conditions_adaptedKernelDatum_alt | exact GlobalTheory.Ggeo.frobeniusConjugation_conditions_adaptedKernelDatum_alt | (intros; apply GlobalTheory.Ggeo.frobeniusConjugation_conditions_adaptedKernelDatum_alt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.JacobiOfClass

section

@[expose] public section

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.KerStd.HostInert


open Formalism.InvariantFactorPaths.G7 (lgF at1) in
open Formalism.L2.G.Pend (k0ToC wittFractionAlgebraCp) in
theorem inParamK_eq {l : ℕ} [Fact l.Prime] {ι : Type} (f : MvPowerSeries ι ℂ_[l]) :
    @Formalism.MainNotions.FormalGroupSystem.inParamK l _ ι ℂ_[l] _ (wittFractionAlgebraCp l) f = MvPowerSeries.subst (fun i => at1 i (lgF ℂ_[l] l)) f := by
  unfold Formalism.MainNotions.FormalGroupSystem.inParamK
  have hlog : PowerSeries.map (k0ToC l) (Formalism.MainNotions.FormalGroupSystem.logF l) = lgF ℂ_[l] l := by
    ext n
    rw [PowerSeries.coeff_map]

    simp only [Formalism.MainNotions.FormalGroupSystem.logF, lgF, PowerSeries.coeff_mk, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_mul]
    split_ifs <;> simp
  congr 1
  funext i
  rw [show @algebraMap (Formalism.MainNotions.FormalGroupSystem.K0 l) ℂ_[l] _ _ (wittFractionAlgebraCp l) = k0ToC l from rfl, hlog]
  rfl

theorem jacobi_of_class (D : D7) (p : ℕ) [Fact p.Prime] (h : IsResidueClassZero D p ∨ IsSg D p) :
    jacobiSym (-(D.host.d : ℤ)) p = -1 := by
  have hp : p.Prime := Fact.out
  have hd : D.host.d.Prime := D.host.hyp.2.1
  have key : p ≠ D.host.d ∧ jacobiSym (-(D.host.d : ℤ)) p ≠ 1 := by
    have h' : D.host.cls p = PrimeClass.inertClass ∨
        D.host.cls p = PrimeClass.signal := h
    rcases h' with h' | h'
    · obtain ⟨-, -, h3, h4, -⟩ := (primeClass_eq_inert_iff _).1 h'
      exact ⟨h3, h4⟩
    · obtain ⟨-, -, h3, h4, -⟩ := (primeClass_eq_signal_iff _).1 h'
      exact ⟨h3, h4⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rcases jacobiSym.trichotomy (-(D.host.d : ℤ)) p with h0 | h1 | h1
  · exfalso
    rw [jacobiSym.eq_zero_iff_not_coprime] at h0
    apply h0
    have : Nat.Coprime D.host.d p := (Nat.coprime_primes hd hp).2 key.1.symm
    simpa [Int.gcd_neg, Int.gcd_natCast_natCast] using this
  · exact absurd h1 key.2
  · exact h1

theorem hostAt_inert : Formalism.L2.KerInert.GenusOneModelExistsLattice → Formalism.L2.KerInert.Rep.CurveDict → Formalism.L2.KerInert.IntInert → ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), 5 ≤ p → (IsResidueClassZero D p ∨ IsSg D p) → HostAt B χ p lam := by
  intro h1 h2 h3 D cc δ B χ hc hδ hχ p _ lam h5 hcl
  have hin := jacobi_of_class D p hcl
  obtain ⟨cc', δ', g, -, -, hL, hlam, hAt, hM, hLT⟩ := h1 D cc δ hc hδ p h5 hin lam
  obtain ⟨g2, g3, ε, s2, -, -, -, -, hn, ⟨a1, a2, a3, a4, a5, -, F, hF, -⟩, hD⟩ := h2 D cc' δ' p g hLT hAt h5 hin hM
  obtain ⟨σ, hσ, -⟩ := Formalism.L2.Th1.D.fieldDataCM p h5
  refine ⟨_, g2, g3, s2, ε, σ, F, hn, ⟨h5, a1, a2, a3, a4, hσ, hF, a5 σ hσ⟩, ?_⟩
  intro N N' L L' hA
  obtain ⟨r, b, hb, ho⟩ := Formalism.L2.KerInert.orthBasisExists_of Formalism.L2.KerInert.global_orthonormal_basis_four
    Formalism.L2.KerInert.weakApprox_of_approx_and_separation D p h5 hin N N' L L' hA
  refine ⟨r, b, hb, ho, fun G hG => ?_⟩
  obtain ⟨C, wq, hC, hw, hd⟩ := hD D
  have hΛ : g.abelian₂ = B.tor.abelian₂ := hAt.2.2.2.1.trans hL
  subst hlam
  rw [hΛ] at hC hw hd
  have := hd N N' r b G (h3 D cc δ B hc hδ χ hχ p h5 hin g.lam N N' L L' hA G hG C wq r b hC hw hb ho)
  rw [HostLog.iff_phSum]
  rw [inParamK_eq] at this
  exact this

end GlobalTheory.KerStd.HostInert
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelDatumEntriesIntegralAwayFromDStatement

section

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Classical

theorem _root_.GlobalTheory.T.jetIntegralityBis_ofKer_of_hyp : GlobalTheory.ThLoc.Inputs → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), t.Hyp → 3 ≤ D.host.splitBound → ∀ ep be sg, OrbitPlaces.JetIntegralityBis (OrbitPlaces.ofKer (nuRowOK D) t.ent ep be sg) Y := by
  first | exact @GlobalTheory.Ggeo.AdmEntInt.kernelDatum_entries_integral_away_from_d | exact GlobalTheory.Ggeo.AdmEntInt.kernelDatum_entries_integral_away_from_d | (intros; apply GlobalTheory.Ggeo.AdmEntInt.kernelDatum_entries_integral_away_from_d <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormDgenEqOne

section

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Classical

namespace GlobalTheory.EigenGenerator

theorem norm_dgen_eq_one : ∀ (D : D7) (cD : D.what₂.Tau → ℂ), Formalism.L2.Ker.IsDgen D cD → ∀ (p : ℕ) [Fact p.Prime] (lm : Qbar →+* ℂ_[p]), p = D.host.d → ∀ τ, ‖lamC lm (cD τ)‖ = 1 := by
  intro D cD hD p _ lm hp τ
  obtain ⟨M, hMnf, hM, hs⟩ := hD
  obtain ⟨s, hsc, hsp⟩ := hs τ
  have hh := D.host.hyp
  unfold Formalism.FrobeniusOrbits.HostHyp at hh
  have h2 : p ∉ D.host.small := hp ▸ UpperTheory.Small.d_not_mem D.host
  have hq : p ≠ D.host.q := by omega
  rw [← hsc]
  exact norm_generator_eq_one D p lm h2 hq M hM τ s hsp

end GlobalTheory.EigenGenerator
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelDatumThetaSeriesShapeAtDAdaptedBases

section

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Classical

namespace GlobalTheory.Ggeo.KerShapeD

theorem thetaKernelShapeAtD_ofKer_of_hyp_adapted : GlobalTheory.ThLoc.Inputs → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D)
    (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), t.Hyp → t.Adapted →
    ∀ ep be sg, OrbitPlaces.ThetaKernelShapeAtD (OrbitPlaces.ofKer (nuRowOK D) t.ent ep be sg) Y := by
  intro hIn D L hT Gi Gl K Y cX ex t hH hA ep be sg
  intro u μ w hlev hcls i hi c c'
  have hpd : D.what₂.places.resChar w = D.host.d := by
    have h := hcls
    simp only [Host.cls, primeClass] at h
    split_ifs at h with h1 h2 h3 <;> first | exact h3 | cases h
  have hAd : AdPl D w := Or.inr (Or.inr hcls)
  have hlev' : LevFree Y u μ w := hlev
  obtain ⟨Pm, hBas, -, hConj, hTh⟩ := hA w hAd u μ hlev'
  have hStd : ∀ j, j ≤ D.R.m → ∀ cl, GlobalTheory.KerStd.StdBases D (t.ent.lam w) ((t.O u μ).lat j cl).1 (Pm j cl) :=
    fun j hj cl => GlobalTheory.T.isStandardBasesLatticeAtPlace_of_adapted_bases D _ (t.ent.lam w) _ _ _ ((t.O u μ).lat j cl).2.1 (fun τ => hBas j hj cl τ)
      (fun τ τ' h => hConj j hj cl τ τ' h)
  have hcomb := GlobalTheory.Ggeo.KerComb.comb_of_tied hIn.algT D L hT Gi Gl K Y cX ex t hH u μ w hlev' i hi c c'
  have hdg : IsDgen D t.cD := by
    rw [← t.O_dgen u μ]
    exact (t.O u μ).dgen_gen
  have hnorm : ∀ τ, ‖(fun _ => (1 : ℂ_[D.what₂.places.resChar w])) τ‖ ≤ ‖TaylorLogMetric.lamC (t.ent.lam w) (t.cD τ)‖ := by
    intro τ
    rw [GlobalTheory.EigenGenerator.norm_dgen_eq_one D t.cD hdg _ (t.ent.lam w) hpd τ]
    simp
  show OrbitPlaces.ShapeD D _ (t.ent.Th u μ w i c c')
  rw [hTh i hi c c', GlobalTheory.atLin_adCoef_eq_stdSer]
  exact GlobalTheory.T.shape_normalisedThetaCombinations_dualBases_at_d hIn D t.cc t.δ t.cc_ok t.δ_ok t.B t.χ t.χ_ok t.X t.seam t.seam_ok _ _ _ _ hcomb.1 _ (t.ent.lam w) hpd
    t.cD hdg (Pm i c) (Pm (i + 1) c') _ (hStd i hi.le c) (hStd (i + 1) hi c') hnorm _ hcomb.2

end GlobalTheory.Ggeo.KerShapeD
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelDatumThetaSeriesShapeAtDAdaptedBasesStatement

section

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Classical

theorem _root_.GlobalTheory.T.kernelDatum_thetaSeries_shape_at_d_adaptedBases : GlobalTheory.ThLoc.Inputs → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), t.Hyp → t.Adapted → ∀ ep be sg, OrbitPlaces.ThetaKernelShapeAtD (OrbitPlaces.ofKer (nuRowOK D) t.ent ep be sg) Y := by
  first | exact @GlobalTheory.Ggeo.KerShapeD.thetaKernelShapeAtD_ofKer_of_hyp_adapted | exact GlobalTheory.Ggeo.KerShapeD.thetaKernelShapeAtD_ofKer_of_hyp_adapted | (intros; apply GlobalTheory.Ggeo.KerShapeD.thetaKernelShapeAtD_ofKer_of_hyp_adapted <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelEntriesHypOfColumnSidePropertiesStatement

section

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker

theorem _root_.GlobalTheory.T.kernelEntries_hyp_of_columnSideProperties : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), GlobalTheory.KerJ.ColSide t → t.TopPinned → t.Hyp := by
  first | exact @GlobalTheory.colSide_hyp | exact GlobalTheory.colSide_hyp | (intros; apply GlobalTheory.colSide_hyp <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepZeroTrivialStabilisersTrueColumnsStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.stab0_rec7_of_levelData : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), LevelData (I.rec7 l Z) → OrbitPlaces.Stab0 (I.rec7 l Z) := by
  first | exact @GlobalTheory.Pdv.stepZero_trivial_stabilisers_trueColumns | exact GlobalTheory.Pdv.stepZero_trivial_stabilisers_trueColumns | (intros; apply GlobalTheory.Pdv.stepZero_trivial_stabilisers_trueColumns <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.AtOfTrueColumns

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PdvClose

theorem at_of_true_columns : Formalism.L2.KerInert.AlgTAll → Formalism.L2.KerInert.GenusOneModelExistsLattice → Formalism.L2.KerInert.Rep.CurveDict → Formalism.L2.KerInert.IntInert → ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), GlobalTheory.Pdv.ColNorm I → ColIn.JetsIn I → ex.tw = I.tw l l0 Z → I.StdKer l Z t → GlobalTheory.Pdv.IsEntC t → t.Adapted → t.TopPinned → 3 ≤ B.host.splitBound → 5 ≤ K.dl1 → 4 ≤ K.dl2 → (∀ Ee : OrbitPlaces.Ent (I.rec7 l Z), OrbitPlaces.Shape (I.rec7 l Z) L Gi Ee ∧ ∀ u, ∀ j < B.R.m, ∀ s ∈ B.host.TT, Ee.row u j (false, s) 0 - Ee.row u j (false, s) 1 ≤ 2 * L.sc.a) → GlobalTheory.Pdv.At ex t.ent := by
  intro hAlg hG1 hCD hII B X I hOk hPins l Z l0 L hT Gi Gl K Y cX ex t hNorm hJets htw hStd hEntC hAd hTop hsplit hdl1 hdl2 hSh
  have hDuty : GlobalTheory.Pdv.Duty t := GlobalTheory.T.conditions_at_standardKernelComparison_trueColumns I hOk hPins l Z l0 L hT Gi Gl K Y cX ex t hNorm hJets htw hStd hEntC
  have hHyp : t.Hyp := GlobalTheory.T.kernelEntries_hyp_of_columnSideProperties _ L hT Gi Gl K Y cX ex t hDuty.col hTop
  have hInp : GlobalTheory.ThLoc.Inputs := GlobalTheory.T.normalisedThetaCMCurveTheorems_of_algebraicTranslates hAlg
  have hHost := GlobalTheory.KerStd.HostInert.hostAt_inert hG1 hCD hII
  obtain ⟨P, Bf, hK, he⟩ := hEntC
  obtain ⟨t', hc', hf'⟩ := hDuty.forms
  obtain ⟨ep, be, hBe, h0⟩ := GlobalTheory.T.admissibleKernelSeries_inertPrime_nonConjugateFrobenius hAlg hHost _ L hT Gi Gl K Y cX ex t hHyp hAd hsplit
  refine ⟨⟨GlobalTheory.T.kernelPairScalars_isUnit_trueColumns I hOk hPins l Z L hT Gi Gl K Y cX ex t hStd,
    GlobalTheory.PdvKm.kmapRat_kerEntC' t P Bf hK he hDuty.rk,
    GlobalTheory.T.kernelClassSums_carry_chainComplexForms _ L hT Gi Gl K Y cX ex t' hc' hf',
    GlobalTheory.T.stab0_rec7_of_levelData I hOk hPins l Z ex.lev⟩, ep, be, (fun _ _ => -1), h0,
    GlobalTheory.T.frobeniusConjugation_conditions_adaptedKernelDatum hAlg hHost _ L hT Gi Gl K Y cX ex t hHyp hAd hsplit ep be _, ?_,
    GlobalTheory.T.jetIntegralityBis_ofKer_of_hyp hInp _ L hT Gi Gl K Y cX ex t hHyp hsplit ep be _,
    GlobalTheory.T.kernelDatum_thetaSeries_shape_at_d_adaptedBases hInp _ L hT Gi Gl K Y cX ex t hHyp hAd ep be _,
    (hSh _).1⟩
  exact GlobalTheory.T.orbitBound_standardSeries_inertPlaces _ L Gi K _ (hSh _).1 (hSh _).2 hdl1 hdl2 hBe rfl

end GlobalTheory.PdvClose
end
end
