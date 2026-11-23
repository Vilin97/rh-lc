module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.JumpDictionary
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightInfinitesimalCharacterParamOfLevelCompatibStatement
public import Formalism.LocalToGlobal.GaloisLevelStructure.TiedLevel
public import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ResidualIrreducibilityFormsEquivalent
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.InfinityTypeEtaTildeAtCmTypeEmbeddingsEqHalf

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.NPin GlobalTheory.NFacts

namespace GlobalTheory.EtaInfType

theorem main : ∀ (D : D7) (cf : CharFrame D) (C : NChoice D) (tp : TupTied D cf C), NCharTied D cf C tp → ∀ t, D.naut.infG D.naut.etaT (Formalism.L2.embT D t) = {(1 / 2 : ℂ)} := by
  intro D cf C tp N t
  have hI : (N.e1 D.naut.etaT).1.HasInfQ (embPsi D.host) (fun _ => (1 / 2 : ℚ)) := by
    rw [N.etaT]
    exact ⟨fun _ => 1, fun _ => by norm_num, cf.isEta.inf⟩
  have h1 := (N.infG _ _ hI (D.eTau t)).1
  have e0 : Formalism.L2.embT D t = embPsi D.host (D.eTau t) := rfl
  rw [e0, h1]
  push_cast
  rfl

end GlobalTheory.EtaInfType
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.InfinityTypeEtaTildeAtCmTypeEmbeddingsEqHalfStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.NPin GlobalTheory.NFacts

theorem _root_.GlobalTheory.T.infinityType_etaTilde_at_cmTypeEmbeddings_eq_half : ∀ (D : D7) (cf : CharFrame D) (C : NChoice D) (tp : TupTied D cf C), NCharTied D cf C tp → ∀ t, D.naut.infG D.naut.etaT (Formalism.L2.embT D t) = {(1 / 2 : ℂ)} := by
  first | exact @GlobalTheory.EtaInfType.main | exact GlobalTheory.EtaInfType.main | (intros; apply GlobalTheory.EtaInfType.main <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.InfWtEqInfOf

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.NPin GlobalTheory.NFacts
namespace GlobalTheory.LocInfWt
theorem infWt_eq_infOf_alt : ∀ (D : D7) (M : MtFam D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E), _root_.GlobalTheory.HeightCounting.HeckeOpenStatements D M tup → ∀ (i : D.nd.Loc) (a : Formalism.L2.NG.AlgWt D.host.E D.R.nV) (τ : D.host.E →+* ℂ) (lam : Fin D.R.nV → ℤ), (M.loc i).wt.IsDual a → a.HWAt τ lam → D.naut.infWt i τ = Formalism.L2.NG.infOf lam := by
  intro D M tup hH i a τ lam hd hw
  obtain ⟨P, -⟩ := D.naut.pt_surj i (Classical.arbitrary (D.nd.X i))
  rw [D.nbc.embAV_inf i P, hH.emb i P,
    hH.au.wt (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2 (hH.av.rep i P) a hd]
  exact hH.au.infW (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2 a τ lam hw
end GlobalTheory.LocInfWt
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.InfWtEqInfOfStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.NPin GlobalTheory.NFacts

theorem _root_.GlobalTheory.T.infWt_eq_infOf_of_isDual : ∀ (D : D7) (M : MtFam D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E), _root_.GlobalTheory.HeightCounting.HeckeOpenStatements D M tup → ∀ (i : D.nd.Loc) (a : Formalism.L2.NG.AlgWt D.host.E D.R.nV) (τ : D.host.E →+* ℂ) (lam : Fin D.R.nV → ℤ), (M.loc i).wt.IsDual a → a.HWAt τ lam → D.naut.infWt i τ = Formalism.L2.NG.infOf lam := by
  first | exact @_root_.GlobalTheory.LocInfWt.infWt_eq_infOf_alt | exact _root_.GlobalTheory.LocInfWt.infWt_eq_infOf_alt | (intros; apply _root_.GlobalTheory.LocInfWt.infWt_eq_infOf_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightParamOfPin

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.NPin GlobalTheory.NFacts
namespace GlobalTheory
theorem weightParam_of_pin_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.WeightParam D := by
  intro hL D P
  exact GlobalTheory.T.weightInfinitesimalCharacterParam_of_levelCompatible D P.M P.tp.tup P.H.level (GlobalTheory.T.infinityType_etaTilde_at_cmTypeEmbeddings_eq_half D P.cf P.C P.tp P.chr) (_root_.GlobalTheory.T.infWt_eq_infOf_of_isDual D P.M P.tp.tup P.H)
end GlobalTheory
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightParamOfPinStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.NPin GlobalTheory.NFacts

theorem _root_.GlobalTheory.T.weight_param_of_character_choice : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.WeightParam D := by
  first | exact @_root_.GlobalTheory.weightParam_of_pin_alt | exact _root_.GlobalTheory.weightParam_of_pin_alt | (intros; apply _root_.GlobalTheory.weightParam_of_pin_alt <;> assumption)
end
end
end
