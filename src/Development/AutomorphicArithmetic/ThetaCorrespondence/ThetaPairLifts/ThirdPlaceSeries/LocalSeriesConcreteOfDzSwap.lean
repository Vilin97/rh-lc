module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OPin
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaLocalInputs
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SplitLoc
import Mathlib.Tactic.NormNum.Parity
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalGlobalCompatibilityCMDatum
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalBesselMultiplicityOne
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CompatibleSystemLocalPropertyExplicit
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FirstTermConditionAllStages
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DepthZeroTypeGlobalOfRegularLocal
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DepthZeroTypeGlobalOfSeriesLocal
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsRepresentationComponent
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GlobalArtinReciprocityTrivial
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GoodFTAllStA
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LabelTameCharacter
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SglobDzBigDef
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MClassMapD
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TameUniformizerPower

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NonGaloisTwistType

section

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host GlobalTheory.Mem.Top.Bl GlobalTheory.HeightCounting GlobalTheory.CoefDuty GlobalTheory.TypeRec
attribute [local instance] GlobalTheory.TypeRec.factG

abbrev _root_.GlobalTheory.T.NonGaloisTwistType' : Prop :=  GlobalTheory.GLq.Green → GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (cf : CharFrame D) (nch : NChoice D) (tp : TupTied D cf nch) (a : _root_.GlobalTheory.Mem.Top.Bl.NAtData hL D cf nch tp), _root_.GlobalTheory.CoefDuty.OPinAlt a → (∀ (I : Ident a.nt.D) cp, IsComp I a.nt.rep cp → ∀ σ, ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (ρ : Representation ℂ (G0g a.nt.D.nd) V) (W : Submodule ℂ V) (x : V), (∀ k v, GlobalTheory.GoodTypes.ConjIn ρ W (GlobalTheory.GoodTypes.facHom a.nt.D k v) (cp σ k v).ρ) ∧ x ≠ 0 ∧ (∀ b, ρ.asAlgebraHom b x ∈ W) ∧ ρ.asAlgebraHom a.nt.D.ntypes.e0 x = x) → GoodFTAll D
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CompatibleSystemLocalProperty

section

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG

abbrev _root_.GlobalTheory.T.CompatibleSystemLocalPropertyThirdPlace : Prop :=  _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → Green → GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (L : ∀ k, LabelDatum (D.host.g k)), LabTie D L → (∀ k v, ∃ κ : IsLocalRing.ResidueField (D.nd.plOm.1 (D.naut.plGw k v)) ≃+* Formalism.CyclotomicNorms.Fbar (D.host.g k), TameCoupled (D.nd.plOm.1 (D.naut.plGw k v)) κ (D.ntypes.tg k v) (L k).gen) → GlobalTheory.HeightCounting.Up.CenLoc D P.M → GlobalTheory.TypeLeaf.SerLoc D
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ConjSelfDualGaloisRepCMDatum

section

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

abbrev _root_.GlobalTheory.T.ConjSelfDualGaloisRepCMDatumThirdPlace : Prop :=  ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (Γ : GrpSide D) (k : Fin 2) (v : D.nd.PlG k) (μ : ((D.naut.plGw k v).adicCompletion D.host.E)ˣ →* ℂˣ) (hμ : GlobalTheory.SmGL.IsSmoothChar μ), GlobalTheory.SplitWeil.IsTame μ → ∀ (u : 𝓞 D.host.E) (hu : (u : D.host.E) ≠ 0), (∃ (ϖ : 𝓞 D.host.E) (π : D.nd.Om), ϖ ∈ (D.naut.plGw k v).asIdeal ∧ ϖ ∉ (D.naut.plGw k v).asIdeal ^ 2 ∧ π ^ (normV (D.naut.plGw k v) - 1) = algebraMap D.host.E D.nd.Om (ϖ : D.host.E) ∧ (D.nd.plOm.1 (D.naut.plGw k v)).valuation (D.ntypes.tg k v π / π - algebraMap D.host.E D.nd.Om (u : D.host.E)) < 1) → ∀ c : ZMod (D.host.g k), D.ntypes.teichC k (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) c) = ((μ (Units.map (algebraMap D.host.E ((D.naut.plGw k v).adicCompletion D.host.E)).toMonoidHom (Units.mk0 (u : D.host.E) hu)) : ℂˣ) : ℂ) → _root_.GlobalTheory.PendOf.localLabelPolynomial hL D k v (Irr.ofDet 1 μ hμ) = X - C c
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BlockTypeSplitProp

section

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

abbrev _root_.GlobalTheory.T.BlockTypeSplitThirdPlace : Prop :=  _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (Γ : GrpSide D), GreenLab Γ → _root_.GlobalTheory.PendOf.RegularLocalCondition hL D
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowTruthOfLabelTie

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
namespace DiscreteGroups.sglob.DzType.Rt
open GlobalTheory.TypeRec GlobalTheory.LabPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem rowTruth_of_labelTie_alt : Green → GlobalTheory.Published.ZelevinskyPolynomialRing → _root_.DiscreteGroups.sglob.DzType.DepthZeroInertiaBigAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (Rw : GlobalTheory.HeightCounting.RowSide D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (L : ∀ k, LabelDatum (D.host.g k)), GlobalTheory.HeightCounting.LabTrue D T → _root_.GlobalTheory.HeightCounting.RepresentationParametersHold hL D rep (fun σ w => T.e w (Rw.locR σ w)) Rw.satR → GlobalTheory.HeightCounting.RowDepth D rep → GlobalTheory.SerSys.LabTie D L → (∀ k v, ∃ κ : IsLocalRing.ResidueField (D.nd.plOm.1 (D.naut.plGw k v)) ≃+* Formalism.CyclotomicNorms.Fbar (D.host.g k), TameCoupled (D.nd.plOm.1 (D.naut.plGw k v)) κ (D.ntypes.tg k v) (L k).gen) → GlobalTheory.LabPin.TypeLab D rep :=
  _root_.DiscreteGroups.sglob.DzType.Rt.typeLab_of_local_m_alt
end DiscreteGroups.sglob.DzType.Rt
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalSeriesConcreteOfDzSwap

section

@[expose] public section



section
section
namespace UpperTheory.Lit.Dz
theorem dz_swap_compatible_alt : _root_.GlobalTheory.T.ConjSelfDualGaloisRepCMDatumThirdPlace :=
  fun hL => _root_.DiscreteGroups.sglob.DzType.Rt.tame_uniformizer_power_alt (_root_.UpperTheory.Lit.Dz.global_artin_reciprocity_trivial hL) hL
theorem localGlobalCompatibility_cmDatum_alt : _root_.GlobalTheory.T.LocalGlobalCompatibilityCMDatum' :=
  fun hL => _root_.DiscreteGroups.sglob.DzType.Rt.labAt_ofDet_tame_eq_X_sub_C (_root_.UpperTheory.Lit.Dz.global_artin_reciprocity_trivial hL) hL
theorem blockTypeSplitProp : _root_.GlobalTheory.T.BlockTypeSplitThirdPlace :=
  fun a hL => _root_.DiscreteGroups.sglob.DzType.Rt.regLoc_of_depth_zero_inertia_big_greenLab a (_root_.UpperTheory.Lit.Dz.global_artin_reciprocity_trivial hL) hL
theorem nonGaloisTwistType : _root_.GlobalTheory.T.NonGaloisTwistType' :=
  fun a b hL => _root_.DiscreteGroups.sglob.DzType.Rt.exists_representation_component_alt a b (_root_.UpperTheory.Lit.Dz.global_artin_reciprocity_trivial hL) hL
theorem firstTermCondition_all_stages : _root_.GlobalTheory.GoodFirst.FirstTermConditionAllStagesAlt :=
  fun a b hL => _root_.DiscreteGroups.sglob.DzType.Rt.goodFTAll_stA_alt a b (_root_.UpperTheory.Lit.Dz.global_artin_reciprocity_trivial hL) hL
theorem compatibleSystemLocalProperty : _root_.GlobalTheory.T.CompatibleSystemLocalPropertyThirdPlace :=
  fun a b c hL => _root_.DiscreteGroups.sglob.DzType.Rt.serLoc_of_tame_coupled_and_cenLoc a b c (_root_.UpperTheory.Lit.Dz.global_artin_reciprocity_trivial hL) hL
theorem compatibleSystemLocalProperty_explicit : _root_.GlobalTheory.SerSys.Assembly.CompatibleSystemLocalPropertyExplicitAlt :=
  fun a b c hL => _root_.DiscreteGroups.sglob.DzType.Rt.depthZeroType_series_local_explicit_alt a b c (_root_.UpperTheory.Lit.Dz.global_artin_reciprocity_trivial hL) hL
theorem localBesselMultiplicityOne : _root_.GlobalTheory.T.LocalBesselMultiplicityOne' :=
  fun a b hL => _root_.DiscreteGroups.sglob.DzType.Rt.rowTruth_of_labelTie_alt a b (_root_.UpperTheory.Lit.Dz.global_artin_reciprocity_trivial hL) hL
end UpperTheory.Lit.Dz
end
end
end
end
