module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameBoundSpaces.FrameBound
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactLevelExistsStatement
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SetupEig
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelExistsBis
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
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.IsPairLevel
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MuCharacterExists
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.SymIdx
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitPlaceExistsStatement
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CongruenceSubgroupIndicatorWeight
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceTwistedConstantTermMatches
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.FullThetaHolds
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.LWeightEx
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameEx0Of
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.HyperbolicEntryBounds.ArchFinal
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.HyperbolicEntryBounds.ChainFinal
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.HyperbolicEntryBounds.WExFinal
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.QuadraticCharacterNorms.BadEx2Of
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.QuadraticCharacterNorms.QuadCharNorm
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfFiniteInputs

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelExistsBisStatement

section

@[expose] public section

open PositivityTheory.Rg.BcB.F.Eig

theorem _root_.GlobalTheory.T.level_exists_bis : LevelEx := by
  first | exact @GlobalTheory.CompanionTheory.LevelU.levelEx | exact GlobalTheory.CompanionTheory.LevelU.levelEx | (intros; apply GlobalTheory.CompanionTheory.LevelU.levelEx <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MuCharacterExistsStatement

section

@[expose] public section

open NumberField GlobalTheory.BCT Formalism.L2.Host PositivityTheory.Rg.BcB.F.Ex0 PositivityTheory.Rg.Bc.ArchbcB.B

theorem _root_.GlobalTheory.T.mu_character_exists : (∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∃ (μ : HChar E) (e : InfinitePlace E → ℤ), IsMu μ e) → MuEx := by
  first | exact @GlobalTheory.CompanionTheory.MuOpen.muEx_of_exists | exact GlobalTheory.CompanionTheory.MuOpen.muEx_of_exists | (intros; apply GlobalTheory.CompanionTheory.MuOpen.muEx_of_exists <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionExistsAlt

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.Ex0 PositivityTheory.Rg.Bc.ArchbcB.B
open scoped Classical

namespace GlobalTheory.CompanionTheory.SecThrough

theorem secEx : SecEx := by
  intro E _ _ _ S₀ hS₀
  let f : Pl E → HeightOneSpectrum (𝓞 (maximalRealSubfield E)) := fun w => w.under (𝓞 (maximalRealSubfield E))
  have hex : ∀ y : Set.range f, ∃ u : Pl E, f u = y.1 ∧ ∀ w ∈ S₀, f w = y.1 → u = w := by
    rintro ⟨_, w₀, rfl⟩
    by_cases h : ∃ w ∈ S₀, f w = f w₀
    · obtain ⟨w, hw, hfw⟩ := h
      exact ⟨w, hfw, fun w' hw' _ => Finset.card_le_one.1 hS₀ w hw w' hw'⟩
    · exact ⟨w₀, rfl, fun w hw hfw => absurd ⟨w, hw, hfw⟩ h⟩
  let g : Set.range f → Pl E := fun y => (hex y).choose
  have hg : ∀ y, f (g y) = y.1 := fun y => (hex y).choose_spec.1
  have hg₀ : ∀ y, ∀ w ∈ S₀, f w = y.1 → g y = w := fun y => (hex y).choose_spec.2
  refine ⟨Set.range g, fun w => ⟨g ⟨f w, w, rfl⟩, ⟨⟨_, rfl⟩, hg _⟩, ?_⟩, ?_, ?_⟩
  · rintro _ ⟨⟨y, rfl⟩, hy⟩
    exact congrArg g (Subtype.ext ((hg y).symm.trans hy))
  · intro w hw
    exact ⟨⟨f w, w, rfl⟩, hg₀ _ w hw rfl⟩
  · intro w hw
    refine ⟨⟨f w, w, rfl⟩, ?_⟩
    by_contra hne
    exact hw ⟨_, hne, hg _⟩

end GlobalTheory.CompanionTheory.SecThrough

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionExistsStatement

section

@[expose] public section

open NumberField GlobalTheory.BCT Formalism.L2.Host PositivityTheory.Rg.BcB.F.Ex0 PositivityTheory.Rg.Bc.ArchbcB.B

theorem _root_.GlobalTheory.T.sec_ex : SecEx := by
  first | exact @GlobalTheory.CompanionTheory.SecThrough.secEx | exact GlobalTheory.CompanionTheory.SecThrough.secEx | (intros; apply GlobalTheory.CompanionTheory.SecThrough.secEx <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformizerExists

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.BCT Formalism.L2.Host PositivityTheory.Rg.BcB.F.Ex0 PositivityTheory.Rg.Bc.ArchbcB.B

namespace GlobalTheory.CompanionTheory.UnifFix

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem conj_real (x : maximalRealSubfield E) :
    IsCMField.complexConj E (algebraMap (maximalRealSubfield E) E x) = algebraMap (maximalRealSubfield E) E x := by
  exact (IsCMField.complexConj E).commutes x

theorem cj_real (w : Pl E) (x : maximalRealSubfield E) :
    GlobalTheory.BCT.cj w (algebraMap E (w.adicCompletion E) (algebraMap (maximalRealSubfield E) E x)) =
      algebraMap E (w.adicCompletion E) (algebraMap (maximalRealSubfield E) E x) := by
  unfold GlobalTheory.BCT.cj
  split_ifs with h
  · rw [h.choose_spec.2, conj_real]
  · rfl

theorem valuation_up (hU : GlobalTheory.BCT.Unr E) (w : Pl E) (x : maximalRealSubfield E) :
    w.valuation E (algebraMap (maximalRealSubfield E) E x) =
      (w.under (𝓞 (maximalRealSubfield E))).valuation (maximalRealSubfield E) x := by
  have := hU w
  have h1 := HeightOneSpectrum.valuation_liesOver E (w.under (𝓞 (maximalRealSubfield E))) w x
  have he : w.asIdeal.ramificationIdx (𝓞 (maximalRealSubfield E)) = 1 := by
    exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
  rw [← h1, he, pow_one]

theorem neg_toAdd_unzero (a : WithZero (Multiplicative ℤ)) (h : a ≠ 0) (ha : a = WithZero.exp (-1 : ℤ)) :
    -Multiplicative.toAdd (WithZero.unzero h) = 1 := by
  subst ha
  rfl

theorem unifEx : UnifEx := by
  intro E _ _ _ hU w
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer (maximalRealSubfield E)
    (w.under (𝓞 (maximalRealSubfield E)))
  have hy : w.valuation E (algebraMap (maximalRealSubfield E) E π) = WithZero.exp (-1) := by
    rw [valuation_up hU w π, hπ]
  have hy0 : algebraMap (maximalRealSubfield E) E π ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hy
    exact WithZero.zero_ne_coe hy
  have hne : algebraMap E (w.adicCompletion E) (algebraMap (maximalRealSubfield E) E π) ≠ 0 :=
    (map_ne_zero _).2 hy0
  have hv : Valued.v (algebraMap E (w.adicCompletion E) (algebraMap (maximalRealSubfield E) E π)) =
      WithZero.exp (-1) := by
    rw [HeightOneSpectrum.algebraMap_adicCompletion (𝓞 E) E w, Function.comp_apply, Algebra.algebraMap_self,
      RingHom.id_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hy]
  have hv0 : Valued.v (algebraMap E (w.adicCompletion E) (algebraMap (maximalRealSubfield E) E π)) ≠ 0 := by
    rw [hv]
    exact WithZero.coe_ne_zero
  refine ⟨Units.mk0 _ hne, ⟨?_, ?_⟩, ?_⟩
  · show Formalism.UG.ordL (algebraMap E (w.adicCompletion E) (algebraMap (maximalRealSubfield E) E π)) = 1
    unfold Formalism.UG.ordL
    rw [dite_eq_right hv0]
    exact neg_toAdd_unzero _ hv0 hv
  · exact cj_real w π
  · exact hv

end GlobalTheory.CompanionTheory.UnifFix
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformizerExistsStatement

section

@[expose] public section

open NumberField GlobalTheory.BCT Formalism.L2.Host PositivityTheory.Rg.BcB.F.Ex0 PositivityTheory.Rg.Bc.ArchbcB.B

theorem _root_.GlobalTheory.T.uniformizer_exists : UnifEx := by
  first | exact @GlobalTheory.CompanionTheory.UnifFix.unifEx | exact GlobalTheory.CompanionTheory.UnifFix.unifEx | (intros; apply GlobalTheory.CompanionTheory.UnifFix.unifEx <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.HodgeTatePoints.CongruenceInertMatching

section

@[expose] public section

theorem PositivityTheory.HtPt.Bc.CongruenceInertMatching.matchCongInert : type_of% @GlobalTheory.CongMatch.match_principal_congruence_inert := @GlobalTheory.CongMatch.match_principal_congruence_inert
end
end

-- Source module: Development.WeilBound.CoreStatements.HodgeTatePoints.SplitMuMatching

section

@[expose] public section

theorem PositivityTheory.HtPt.Bc.SplitMuMatching.matchCtMuSplit : type_of% @GlobalTheory.BCT.SplitCtMatch.match_ctMu_of_isSplitAt := @GlobalTheory.BCT.SplitCtMatch.match_ctMu_of_isSplitAt
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameEx0Plug

section

@[expose] public section

namespace PositivityTheory.Rg.BcB.F.Ex0

open PositivityTheory.Rg.BcB.F

theorem frameEx0_plug (h2 : PositivityTheory.Rg.Bc.ArchbcB.B.M2) (h3 : PositivityTheory.Rg.Bc.ArchbcB.B.M3) : FrameEx0 :=
  frameEx0_of Rig.weightEx Rig.unrAE_holds (GlobalTheory.T.mu_character_exists Fok.Mu3.muExists) GlobalTheory.T.sec_ex GlobalTheory.T.uniformizer_exists GlobalTheory.T.level_exists_bis
    GlobalTheory.T.split_place_exists (badEx2_of h2 h3) GlobalTheory.T.compact_level_exists PositivityTheory.Rg.BcB.G8.translation_existence_holds F0.chainEx_holds F0.archEx_holds F0.wEx_holds

theorem frameEx0 : FrameEx0 := frameEx0_plug PositivityTheory.HtPt.Bc.CongruenceInertMatching.matchCongInert PositivityTheory.HtPt.Bc.SplitMuMatching.matchCtMuSplit

end PositivityTheory.Rg.BcB.F.Ex0
end
end
