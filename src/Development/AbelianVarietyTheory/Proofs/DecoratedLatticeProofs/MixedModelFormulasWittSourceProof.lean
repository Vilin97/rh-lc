module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumTransportSourceRationalIsometryStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittDecompositionMixedCoordsRankZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittSourceMixedCoordHeisenbergRestrictionStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilCompatibleOfSameSplittingCharacterStatement
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorsWittParabolicOriginToPointStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepresentationValueAtOriginLeviFactor
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittMixedModelUnipotentFormulasStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittSourceMixedCoordHeisenbergRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinateOriginWeilRepTargetEquivariant

section

namespace I195MixedCoordinates_d909b66b3061dc587285daac

open Formalism.BasicNotions Formalism.BasicNotions.TH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

public noncomputable abbrev source
    {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D T.rank ρ))
    (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) : WO S₀ T → ℂ :=
  fun w₀ => ∫ a in 𝓕, heisO ψ S T (a * d.pY)
    (heisO ψ S T (x * d.pX) (heisO ψ S T (w₀ * d.p0) f)) 0 ∂μ

end I195MixedCoordinates_d909b66b3061dc587285daac

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.ValueAtOrigin

theorem mixS_zero_target : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (χS χT : (AE D)ˣ →* Circle) (om : Om S T) (om₀ : Om S₀ T), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S₀ T χS χT om₀ → ∀ (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), IsCovolOne (ratMx D T.rank ρ) μ 𝓕 → ∀ h f, IsThetaFunO ψ S T f → (_root_.I195MixedCoordinates_d909b66b3061dc587285daac.source d) T ψ μ 𝓕 (om (1, h) f) 0 = om₀ (1, h) ((_root_.I195MixedCoordinates_d909b66b3061dc587285daac.source d) T ψ μ 𝓕 (f) 0) := by
  intro D ψ S S₀ T ρ d χS χT om om₀ hS hS₀ μ 𝓕 hμ h f hf
  rcases Nat.eq_zero_or_pos ρ with rfl | hρ
  · have hz := (GlobalTheory.T.wittDecomposition_mixedCoords_rank_zero D ψ).1 S S₀ T d μ 𝓕 hμ
    have hi := (GlobalTheory.T.weil_datum_transport_source_rational_isometry D ψ S S₀ T d hS.std).2.2.2 χS χT om om₀ hS hS₀ 1 h f hf
    change I195MixedCoordinates_00549d7c7323d43c39912169.source d T ψ μ 𝓕 (om (1, h) f) 0 = om₀ (1, h) (I195MixedCoordinates_00549d7c7323d43c39912169.source d T ψ μ 𝓕 f 0)
    rw [hz, hz, hi, map_one]
  · obtain ⟨hsp, hrat, -, -, -, hmix, -⟩ := GlobalTheory.T.wittSourceMixedCoord_heisenbergRestriction D ψ S S₀ T ρ d
    have hc := GlobalTheory.T.weilCompatible_of_sameSplittingCharacter D S S₀ T ρ d.e d.i₀ (hsp hρ) ψ χS χT χT om om₀ hS hS₀ μ 𝓕 (hrat ▸ hμ) h f hf
    have h0 : ∀ g : WO S T → ℂ, heisO ψ S T (d.extX T 0) g = g := by
      intro g; funext w
      simp [heisO, symplOH_zero_right]
    change I195MixedCoordinates_61fbc522a99e851221ffe16d.source d T ψ μ 𝓕 (om (1, h) f) 0 = om₀ (1, h) (I195MixedCoordinates_61fbc522a99e851221ffe16d.source d T ψ μ 𝓕 f 0)
    rw [hmix, hmix, h0, h0, hc]

end GlobalTheory.ValueAtOrigin
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinateOriginWeilRepTargetEquivariantStatement

section

namespace I195MixedCoordinates_6a77e1566d048881366221d8

open Formalism.BasicNotions Formalism.BasicNotions.TH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

public noncomputable abbrev source
    {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D T.rank ρ))
    (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) : WO S₀ T → ℂ :=
  fun w₀ => ∫ a in 𝓕, heisO ψ S T (a * d.pY)
    (heisO ψ S T (x * d.pX) (heisO ψ S T (w₀ * d.p0) f)) 0 ∂μ

end I195MixedCoordinates_6a77e1566d048881366221d8

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.mixedCoordinate_origin_weilRep_target_equivariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (χS χT : (AE D)ˣ →* Circle) (om : Om S T) (om₀ : Om S₀ T), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S₀ T χS χT om₀ → ∀ (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), IsCovolOne (ratMx D T.rank ρ) μ 𝓕 → ∀ h f, IsThetaFunO ψ S T f → (_root_.I195MixedCoordinates_6a77e1566d048881366221d8.source d) T ψ μ 𝓕 (om (1, h) f) 0 = om₀ (1, h) ((_root_.I195MixedCoordinates_6a77e1566d048881366221d8.source d) T ψ μ 𝓕 (f) 0) := by
  first | exact @GlobalTheory.ValueAtOrigin.mixS_zero_target | exact GlobalTheory.ValueAtOrigin.mixS_zero_target | (intros; apply GlobalTheory.ValueAtOrigin.mixS_zero_target <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepresentationValueAtOriginLeviFactorStatement

section

namespace I195MixedCoordinates_34c45ee3f9864caed77cce75

open Formalism.BasicNotions Formalism.BasicNotions.TH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

public noncomputable abbrev source
    {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D T.rank ρ))
    (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) : WO S₀ T → ℂ :=
  fun w₀ => ∫ a in 𝓕, heisO ψ S T (a * d.pY)
    (heisO ψ S T (x * d.pX) (heisO ψ S T (w₀ * d.p0) f)) 0 ∂μ

end I195MixedCoordinates_34c45ee3f9864caed77cce75

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.weilRepresentation_value_at_origin_leviFactor : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (χS χT : (AE D)ˣ →* Circle) (om : Om S T) (om₀ : Om S₀ T), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S₀ T χS χT om₀ → ∀ (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), IsCovolOne (ratMx D T.rank ρ) μ 𝓕 → ∀ f, IsThetaFunO ψ S T f → (∀ g, (_root_.I195MixedCoordinates_34c45ee3f9864caed77cce75.source d) T ψ μ 𝓕 (om (d.emb0 g, 1) f) 0 = om₀ (g, 1) ((_root_.I195MixedCoordinates_34c45ee3f9864caed77cce75.source d) T ψ μ 𝓕 (f) 0)) ∧ (∀ a : GL (Fin ρ) (AE D), Matrix.GeneralLinearGroup.det a = 1 → (_root_.I195MixedCoordinates_34c45ee3f9864caed77cce75.source d) T ψ μ 𝓕 (om (d.levi a, 1) f) 0 = (_root_.I195MixedCoordinates_34c45ee3f9864caed77cce75.source d) T ψ μ 𝓕 (f) 0) ∧ ∀ a : GL (Fin ρ) (AE D), (_root_.I195MixedCoordinates_34c45ee3f9864caed77cce75.source d) T ψ μ 𝓕 (om (d.levi a, 1) f) 0 = ((((χT (Matrix.GeneralLinearGroup.det a))⁻¹ : Circle) : ℂ) * (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod T.rank a : ℂ)) • (_root_.I195MixedCoordinates_34c45ee3f9864caed77cce75.source d) T ψ μ 𝓕 (f) 0 := by
  first | exact @GlobalTheory.LeviOrigin.value_at_origin | exact GlobalTheory.LeviOrigin.value_at_origin | (intros; apply GlobalTheory.LeviOrigin.value_at_origin <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedModelFormulasWittSourceProof

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.MixSourceFormulas

theorem mixed_source : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.MixedSource D := by
  intro D ψ S S₀ T ρ d χS χT om om₀ ho ho₀ μ 𝓕 hμ f hf
  have hth : ∀ w f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (heisO ψ S T w f) :=
    (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ ho.std S T).1
  have hbr : ∀ (f : WO S T → ℂ) x, d.mixS T ψ μ 𝓕 f x = d.mixS T ψ μ 𝓕 (heisO ψ S T (d.extX T x) f) 0 :=
    fun f x => (GlobalTheory.T.wittSourceMixedCoord_heisenbergRestriction D ψ S S₀ T ρ d).2.2.2.2.2.2.1 μ 𝓕 f x
  have hmv := GlobalTheory.T.weil_operators_witt_parabolic_origin_to_point D ψ S S₀ T ρ d χS χT om ho μ 𝓕 hμ f hf
  have hun := GlobalTheory.T.wittMixedModel_unipotent_formulas D ψ S S₀ T ρ d χS χT om ho μ 𝓕 hμ f hf
  have hlv := fun w => GlobalTheory.T.weilRepresentation_value_at_origin_leviFactor D ψ S S₀ T ρ d χS χT om om₀ ho ho₀ μ 𝓕 hμ (heisO ψ S T w f) (hth w f hf)
  unfold I195MixedCoordinates_3601ff04f10fcda6f28caf89.source at hmv
  unfold I195MixedCoordinates_34c45ee3f9864caed77cce75.source at hlv
  unfold HypDec.mixS HypDec.extX HypDec.extY HypDec.ext0 at hbr
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h x
    have hor := GlobalTheory.T.mixedCoordinate_origin_weilRep_target_equivariant D ψ S S₀ T ρ d χS χT om om₀ ho ho₀ μ 𝓕 hμ h (heisO ψ S T (d.extX T (mt T h⁻¹ ⬝ x)) f) (hth _ f hf)
    unfold I195MixedCoordinates_6a77e1566d048881366221d8.source at hor
    unfold I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.source
    rw [(hmv x).1 h, hor]
    exact congrArg (om₀ (1, h)) (hbr f (mt T h⁻¹ ⬝ x)).symm
  · intro g x
    have e := (hmv x).2.1 1 g
    rw [map_one, one_mul, Units.val_one, Matrix.mul_one] at e
    unfold I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.source
    rw [e, (hlv _).1 g]
    exact congrArg (om₀ (g, 1)) (hbr f x).symm
  · intro a x
    have e := (hmv x).2.1 a 1
    rw [map_one, mul_one] at e
    unfold I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.source
    rw [e, (hlv _).2.2 a]
    exact congrArg (fun (z : WO S₀ T → ℂ) => (((χT (Matrix.GeneralLinearGroup.det a) : Circle) : ℂ)⁻¹ * (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod T.rank a : ℂ)) • z) (hbr f (x ⬝ a.1)).symm
  · intro b x
    exact (hun x).1 b
  · intro c x
    exact (hun x).2 c

end GlobalTheory.MixSourceFormulas
end
end
