module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IteratedLiftChains
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SatakeParameterOfSpherical
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmDataIsCMExtAndGramIsHermND
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HilbertSchurOfAdjointClosed
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormSatakeLeOfUnitarySphericalGLStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PowDvdOfHermMatEq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SatakeParameterGLStarEqInvOfUnitarisable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeActsByScalarCommutative
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenIsCompactUnitaryIntegralPoints
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSplitPrimeAvoiding
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.CondSq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPrimePlacesSplit
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPrimeAdditiveCharacterUnramified
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharacterInfiniteOrderAtSplit
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CharacterEquivalenceLocalData

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Links
open GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains GlobalTheory.PRep GlobalTheory.LFun
open Formalism.UG (IsCommensurated Hecke)
open Formalism.MainNotions.SchurIrreducible (IsSplit)

noncomputable section

namespace GlobalTheory.NoExcl

open Formalism.MainNotions.StandardLattice Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.IndefR.Lift GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem isHermND_gram (V : HSp D) : IsHermND D.sp.cm.sig V.gram :=
  (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm).2 V

theorem chart (V : HSp D) {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}
    (h : w.under (𝓞 D.host.F) = v) (hv : IsSplit (E := D.host.E) v) :
    (∃ e, IsSplitChart D.sp.cm.sig V.gram (frameLat V) h e) ∧ Ideal.absNorm w.asIdeal = Formalism.UG.qV D.host.F v := by
  obtain ⟨⟨e, he, -⟩, w', -, -, h1, -⟩ := SplitChart.split_chart_and_places (isCMExt_host D) (isHermND_gram V)
    (frameLat_fg V) (SelfDual.isLattice_frameLat V).span_eq_top h hv (SelfDual.isSelfDualAt_frameLat D V v)
  exact ⟨⟨e, he⟩, h1⟩

section Param

variable {V : HSp D} {ν : Measure (GA D V)} [ν.IsHaarMeasure] [ν.IsMulRightInvariant] {W : Submodule ℂ (DividedPowerChartLift V ν)}

end Param

section Chars

open Formalism.L2.Host

variable {T : Type} {L : LevCh D T} {t₀ : T}

end Chars

section Zero

variable {V : HSp D} {ν : Measure (GA D V)} [ν.IsHaarMeasure] [ν.IsMulRightInvariant]
  {σ π : Submodule ℂ (DividedPowerChartLift V ν)}

end Zero

end GlobalTheory.NoExcl

end
