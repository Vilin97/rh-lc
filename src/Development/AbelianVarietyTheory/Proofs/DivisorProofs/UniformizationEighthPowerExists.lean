module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Laws3
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationCompleteLocalDomainPrime
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubicalStructureE8PowerStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8MumfordBundlePowerSectionNonvanishingClosedFibStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8LB
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ToATotal
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8PowerBundleHypothesis
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
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericEighthPowerUniformisedIsPolarisedStatement
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitExtDatumOfSplitTorusExtension
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsIsPowGrpSplitTorus
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsMonHomOfComm
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsPowGrpBaseChange
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.PowExt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SmoothIsMultiplicative
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAbelianSchemeThick
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EgaHolds
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.NonemptyTorusExtensionOfIsPowGrp
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SurjectiveCubeBaseChange
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisationCompleteDvrOfLawsStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHoldStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8PowerBundleHypothesisStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.hypW_e8LB_powObj : ∀ (S : Scheme.{0}) (G₀ : Over S) [GrpObj G₀] [IsCommMonObj G₀] (P : GlobalTheory.UU.CP G₀) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → GlobalTheory.LN.HypW (powObj G₀ 8) (GlobalTheory.PowE8.e8LB G₀ P.L.L W) := by
  first | exact @GlobalTheory.PowE8.hypW_e8LB | exact GlobalTheory.PowE8.hypW_e8LB | (intros; apply GlobalTheory.PowE8.hypW_e8LB <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitExtensionModuloIdealEighthPower

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SplitPow

theorem splitExtensionModuloIdeal_eighth_power : ∀ (R : Type) [CommRing R] (G₀ : Over (Sp R)) [GrpObj G₀] [IsCommMonObj G₀] (I : Ideal R),
    GlobalTheory.LN.SplitOver G₀ I → GlobalTheory.LN.SplitOver (powObj G₀ 8) I := by
  intro R _ G₀ _ _ I ⟨E, ⟨D⟩⟩
  letI := E.grpB
  haveI := E.free
  haveI := E.finite
  obtain ⟨p, -⟩ := GlobalTheory.isPowGrp_baseChange _ _ (spMap (Ideal.Quotient.mk I)) (powObj G₀ 8) G₀ 8 (powIsPowGrp G₀ 8)
  obtain ⟨pT, -⟩ := GlobalTheory.exists_isPowGrp_splitTorus (Sp (R ⧸ I)) E.X (Fin 8 → E.X) 8 (AddEquiv.refl _)
  obtain ⟨q', hq, hq1, hq2, hq3, hq4, -⟩ :=
    GlobalTheory.PowMap.main _ _ _ (powObj E.B 8) E.B 8 p (powIsPowGrp E.B 8) D.q
  obtain ⟨i', hi, hi1, -⟩ := GlobalTheory.PowMap.main _ _ _ _ _ 8 pT p D.i
  have hB : IsAbelianScheme (powObj E.B 8) := (GlobalTheory.PowGrp.powers _ _ _ 8 (powIsPowGrp E.B 8)).2.2.2.1 E.isAbelian
  have hk := GlobalTheory.PowKernel.main _ _ _ _ _ _ _ 8 pT p (powIsPowGrp E.B 8) D.i D.q i' q' hi hq D.isKernel
  haveI : IsCommMonObj ((Over.pullback (spMap (Ideal.Quotient.mk I))).obj G₀) := inferInstance
  haveI : IsCommMonObj ((Over.pullback (spMap (Ideal.Quotient.mk I))).obj (powObj G₀ 8)) := inferInstance
  have hqc : QuasiCompact D.q.left := by
    have := D.q_affine
    infer_instance
  obtain ⟨O, h₁, h₂, h₃, h⟩ := GlobalTheory.exists_gtDatum_of_splitTorus_extension _ (Fin 8 → E.X) _ (powObj E.B 8) hB q' i'
    (hq1 D.q_hom) (hi1 D.i_hom) (hq2 D.q_flat) (hq3 D.q_surjective) (hq4 hqc) hk
  obtain ⟨d, -, -⟩ := h hB
  exact ⟨_, ⟨d⟩⟩

end GlobalTheory.SplitPow
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitExtensionModuloIdealEighthPowerStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.splitOver_powObj_eight : ∀ (R : Type) [CommRing R] (G₀ : Over (Sp R)) [GrpObj G₀] [IsCommMonObj G₀] (I : Ideal R), GlobalTheory.LN.SplitOver G₀ I → GlobalTheory.LN.SplitOver (powObj G₀ 8) I := by
  first | exact @GlobalTheory.SplitPow.splitExtensionModuloIdeal_eighth_power | exact GlobalTheory.SplitPow.splitExtensionModuloIdeal_eighth_power | (intros; apply GlobalTheory.SplitPow.splitExtensionModuloIdeal_eighth_power <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedSemiAbelianSplitModMaximalIdeal

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SplitRed

theorem splitOver_of_unif : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))), Unif (maximalIdeal V₁) D₀ A₀ G₀ → IsSemiAbelian G₀ → GlobalTheory.LN.SplitOver G₀ (maximalIdeal V₁) := by
  intro V₁ _ _ _ _ D₀ G₀ _ _ A₀ U _
  obtain ⟨E, -, -, -, -, hE⟩ := GlobalTheory.gtCoord_isGt V₁ (IsLocalRing.maximalIdeal V₁) D₀.toPre 0 G₀ ⟨U.gt 0⟩
  have key : ∀ J : Ideal V₁, J = IsLocalRing.maximalIdeal V₁ →
      ∀ S : SplitExt (Spec (CommRingCat.of (V₁ ⧸ J))),
        S.IsGt ((Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).obj G₀) →
        GlobalTheory.LN.SplitOver G₀ (IsLocalRing.maximalIdeal V₁) := by
    rintro J rfl S hS
    exact ⟨S, hS⟩
  exact key _ (pow_one _) E hE

end GlobalTheory.SplitRed
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedSemiAbelianSplitModMaximalIdealStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.uniformised_semiAbelian_split_mod_maximalIdeal : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))), Unif (maximalIdeal V₁) D₀ A₀ G₀ → IsSemiAbelian G₀ → GlobalTheory.LN.SplitOver G₀ (maximalIdeal V₁) := by
  first | exact @GlobalTheory.SplitRed.splitOver_of_unif | exact GlobalTheory.SplitRed.splitOver_of_unif | (intros; apply GlobalTheory.SplitRed.splitOver_of_unif <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTotalClosed

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

namespace GlobalTheory

theorem uniformisation_total_closed : USt :=
  GlobalTheory.T.uniformisation_complete_dvr_of_laws GlobalTheory.T.all_six_abelian_scheme_laws_hold.1 GlobalTheory.T.all_six_abelian_scheme_laws_hold.2.1 GlobalTheory.T.all_six_abelian_scheme_laws_hold.2.2.1 GlobalTheory.T.all_six_abelian_scheme_laws_hold.2.2.2.1
    GlobalTheory.T.all_six_abelian_scheme_laws_hold.2.2.2.2.1

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformizationEighthPowerExists

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.PowE8

theorem isAdmissibleBase_of_completeNormalLocalCharZero (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (h : IsCN V₁) :
    GlobalTheory.LN.admitted V₁ (maximalIdeal V₁) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  letI : Field (V₁ ⧸ maximalIdeal V₁) := Ideal.Quotient.field _
  exact ⟨⟨h1, inferInstance, h2, h3⟩, h3, h4, inferInstance, inferInstance⟩

theorem exists_unif_pow8 : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (y : Sp (FractionRing V₁) ⟶ F.X) (α : A₀.A.left ⟶ F.univ.A.left) (α₂ : (G2 A₀.A).left ⟶ (G2 F.univ.A).left), IsSemiAbelian G₀ → IsGrpPullback A₀.A F.univ.A y α → IsSquare α α₂ → LBIso (abelian₂ A₀.A A₀.L) (F.univ.P.pull α₂) → ∀ P : PolAV (Sp (FractionRing V₁)), SharpOver F W P y → ∃ D : DegData V₁ (maximalIdeal V₁), Nonempty (Unif (maximalIdeal V₁) D P (powObj G₀ 8)) := by
  intro g n o _ ζ F W hW V₁ _ _ _ hCN D₀ G₀ _ _ A₀ U₀ y α α₂ hS hpb hsq hlb P hP
  have hL := GlobalTheory.abelianSchemeLaws_all
  let P₀ := GlobalTheory.ValueForm.modelCP U₀.toUnifPre hL.1.globalFns
  obtain ⟨Pc, hPc⟩ := GlobalTheory.T.cubical_structure_e8_power _ G₀ P₀ W
  obtain ⟨gen, hgen, hA⟩ := GlobalTheory.T.generic_eighth_power_uniformised_is_polarised g n o ζ F W V₁ D₀ G₀ A₀ U₀ y α α₂ hpb hsq hlb P hP
  have hW8 : GlobalTheory.LN.HypW (powObj G₀ 8) Pc.L.L := hPc ▸ GlobalTheory.T.hypW_e8LB_powObj _ G₀ P₀ W hW
  have hT : GlobalTheory.LN.ThetaNZ (powObj G₀ 8) Pc.L.L :=
    hPc ▸ GlobalTheory.T.thetaNZ_e8LB_powObj hL.1 hL.2 GlobalTheory.LN.ega_holds V₁ hCN D₀ G₀ A₀ U₀ hS W hW
  have hA' : LBIso (P.L.pull gen.hom.left) (Pc.L.L.pull (pullback.fst (powObj G₀ 8).hom (jK V₁))) := hPc ▸ hA
  letI : Field (V₁ ⧸ maximalIdeal V₁) := Ideal.Quotient.field _
  obtain ⟨D, U, -, -⟩ := GlobalTheory.PrimeUnif.exists_unif hL.1 hL.2 GlobalTheory.laws3 GlobalTheory.LN.ega_holds GlobalTheory.uniformisation_total_closed V₁
    (maximalIdeal V₁) (isAdmissibleBase_of_completeNormalLocalCharZero V₁ hCN) inferInstance (powObj G₀ 8) Pc
    (GlobalTheory.PowGrp.isSemiAbelian_pow _ _ _ 8 (powIsPowGrp G₀ 8) hS) hW8
    (GlobalTheory.T.splitOver_powObj_eight V₁ G₀ _ (GlobalTheory.T.uniformised_semiAbelian_split_mod_maximalIdeal V₁ hCN D₀ G₀ A₀ U₀ hS)) hT P gen hgen hA'
  exact ⟨D, ⟨U⟩⟩

end GlobalTheory.PowE8
end
end
end
