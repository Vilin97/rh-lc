module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InhabitBis
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagFurtherTermIndependentStatementStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagModelJoinLeftStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagModelJoinRightStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagPlainValueIndependentStatement
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartBundleBaseExtension
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartBundleBaseExtensionUnique
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
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
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsTerSide
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PConeTrdegFnField
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinJoinTwoModels
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsTerTail
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinJoinVertDiv
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsBisExtra
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ExSub
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ExSubAlt
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsBisLast
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyBridgeFull
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagPairValueIndep

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ImportsAlt

section

@[expose] public section

namespace GlobalTheory.CompanionTheory.CommAlg.JoinPullbackAlt

open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
  (mseg joinCoord IsPull SameGeneric)

theorem main :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
      [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (x : (Σ k, ι k) → Ω) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
      (z : (Σ k, ι' k) → Ω) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V]
      (E E' : ChartBundle O (mseg x) N V), SameGeneric O x E E' →
      ∃ EB E'B : ChartBundle O (mseg (joinCoord x z)) N V,
        IsPull O x z E EB ∧ IsPull O x z E' E'B ∧ SameGeneric O (joinCoord x z) EB E'B := by
  classical
  intro O _ _ _ Ω _ _ K _ ι _ x K' _ ι' _ z N V _ _ E E' hE
  obtain ⟨EB, hEB⟩ := (GlobalTheory.CompanionTheory.Ar.Num.PullExists.main O Ω K ι x N V E).1 K' ι' z
  obtain ⟨E'B, hE'B⟩ := (GlobalTheory.CompanionTheory.Ar.Num.PullExists.main O Ω K ι x N V E').1 K' ι' z
  exact ⟨EB, E'B, hEB, hE'B,
    (GlobalTheory.CompanionTheory.Ar.Num.PullPreserve.pull_preserve O Ω K ι x N V E E' K' ι' z EB E'B hEB hE'B).2.1 hE⟩

end GlobalTheory.CompanionTheory.CommAlg.JoinPullbackAlt
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.JoinTwoModels

section

@[expose] public section

namespace GlobalTheory.CompanionTheory.CommAlg

theorem joinTwoModels : GroundTheory.Heights₂.Heights.NumbersDVR.JoinTwoModels.Statement :=
  GroundTheory.Heights₂.Heights.NumbersDVR.JoinTwoModels.proof
    GroundTheory.Heights₂.Heights.NumbersDVR.ConeTrdegFnField.proof

end GlobalTheory.CompanionTheory.CommAlg
end
end

-- Source module: Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XSJoinvertdiv

section

@[expose] public section

theorem PositivityTheory.Xgn.t_s_joinvertdiv : GroundTheory.Heights₂.Heights.NumbersDVR.JoinVerticalDivisor.Statement :=
  GroundTheory.Heights₂.Heights.NumbersDVR.JoinVerticalDivisor.proof
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.JoinVerticalDivisorStatement

section

@[expose] public section

namespace GlobalTheory.CompanionTheory.Heights

theorem join_vertical_divisor_statement : GroundTheory.Heights₂.Heights.NumbersDVR.JoinVerticalDivisor.Statement :=
  PositivityTheory.Xgn.t_s_joinvertdiv

end GlobalTheory.CompanionTheory.Heights
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsTerRest

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg joinCoord IsPull SameGeneric)

def JoinPullbackAlt.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (z : (Σ k, ι' k) → Ω) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V]
    (E E' : ChartBundle O (mseg x) N V), SameGeneric O x E E' →
    ∃ EB E'B : ChartBundle O (mseg (joinCoord x z)) N V,
      IsPull O x z E EB ∧ IsPull O x z E' E'B ∧ SameGeneric O (joinCoord x z) EB E'B

end GroundTheory.Heights₂.Heights.NumbersDVR
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagModelCommonModel

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (joinCoord)

theorem FlagModelCommonModel.proof (hModel : JoinTwoModels.Statement)
    (hPull : JoinPullbackAlt.Statement) (hVert : JoinVerticalDivisor.Statement)
    (hLeft : FlagModelJoinLeftAlt.Statement) (hRight : FlagModelJoinRightAlt.Statement) :
    FlagModelCommonModel.Statement := by
  intro O _ _ _ Ω _ _ K _ ι _ x d N V _ _ E E' hW hE F₁ F₂
  obtain ⟨hZ, hfn⟩ := hModel O Ω K ι x d hW F₁.K' F₁.ι' F₁.z F₂.K' F₂.ι' F₂.z F₁.model F₁.birat
    F₂.model F₂.birat
  obtain ⟨EB, E'B, hp, hp', hsame⟩ :=
    hPull O Ω K ι x (F₁.K' ⊕ F₂.K') (Sum.elim F₁.ι' F₂.ι') (joinCoord F₁.z F₂.z) N V E E' hE
  obtain ⟨φ₁, h₁⟩ := hLeft O Ω K ι x d N V E E' hW hE F₁ F₂.K' F₂.ι' F₂.z hZ hfn EB E'B hp hp'
  obtain ⟨φ₂, h₂⟩ := hRight O Ω K ι x d N V E E' hW hE F₂ F₁.K' F₁.ι' F₁.z hZ hfn EB E'B hp hp'
  refine ⟨F₁.K' ⊕ F₂.K', inferInstance, Sum.elim F₁.ι' F₂.ι', inferInstance, joinCoord F₁.z F₂.z, EB, E'B,
    φ₁, φ₂, hZ, hfn, hp, hp', hsame, fun b f g hv => hVert O Ω K ι x _ _ _ b f g hv, ?_⟩
  intro I I₁ I₂ hI hI₁ hI₂ G r y y' f g hv c Q hc hG hQ
  exact ⟨h₁ I I₁ hI hI₁ G r y y' f g hv c Q hc hG hQ, h₂ I I₂ hI hI₂ G r y y' f g hv c Q hc hG hQ⟩

end GroundTheory.Heights₂.Heights.NumbersDVR
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagModelValueIndep

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IFamily IsFieldIntersection)

namespace FlagModelValueIndependence

theorem fieldNum_isFieldIntersection (F : Type) [Field F] {K : Type} [Fintype K] (κ : K → Type)
    [∀ k, Fintype (κ k)] : IsFieldIntersection (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fieldNum F κ) := by
  classical
  exact Classical.epsilon_spec (p := fun I : IFamily F κ => IsFieldIntersection I)
    ⟨_, IntNumIsFieldIntersection.full F K κ⟩

theorem pullDeg_sub {K K' : Type} (a b : K → ℤ) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := K') (a - b) =
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := K') a - IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := K') b := by
  funext k
  cases k <;> simp [IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg]

theorem proof (hOne : FlagPairValueIndependence.Statement) (hCommon : FlagModelCommonModel.Statement) :
    FlagModelValueIndependence.Statement := by
  intro O _ _ _ Ω _ _ K _ ι _ x d N V _ _ E E' hW hE F₁ F₂ I₁ I₂ hI₁ hI₂ G hG r y y' f g hv c Q hc hGc hQ
  obtain ⟨K'', _, ι'', _, z, EB, E'B, φ₁, φ₂, hZ, -, -, -, hS, hpull, hval⟩ :=
    hCommon O Ω K ι x d N V E E' hW hE F₁ F₂
  have hI := fieldNum_isFieldIntersection (IsLocalRing.ResidueField O) (Sum.elim ι ι'')
  obtain ⟨h₁, h₂⟩ := hval _ I₁ I₂ hI hI₁ hI₂ G r y y' f g hv c Q hc hGc hQ
  rw [h₁, h₂]
  refine hOne O Ω (K ⊕ K'') (Sum.elim ι ι'') (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord x z) d N V EB E'B hZ hS
    φ₁ φ₂ _ hI G hG r (fun l => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (y l))
    (fun l => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (y' l))
    (fun l => rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ι'') (f l))
    (fun l => rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ι'') (g l)) (fun l => ?_) c Q hc hGc hQ
  rw [← pullDeg_sub]
  exact hpull _ _ _ (hv l)

end FlagModelValueIndependence

end GroundTheory.Heights₂.Heights.NumbersDVR
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagModelValueIndependent

section

@[expose] public section

namespace GlobalTheory.CompanionTheory.CommAlg.FlagModelValue


open GroundTheory.Heights₂.Heights.NumbersDVR in
theorem main : FlagModelValueIndependence.Statement :=
  FlagModelValueIndependence.proof
    (FlagPairValueIndependence.proof GlobalTheory.T.flag_plain_value_independent GlobalTheory.T.flag_further_term_independent_statement)
    (_root_.GroundTheory.Heights₂.Heights.NumbersDVR.FlagModelCommonModel.proof
      GlobalTheory.CompanionTheory.CommAlg.joinTwoModels
      GlobalTheory.CompanionTheory.CommAlg.JoinPullbackAlt.main
      GlobalTheory.CompanionTheory.Heights.join_vertical_divisor_statement
      GlobalTheory.T.flag_model_join_left GlobalTheory.T.flag_model_join_right)

end GlobalTheory.CompanionTheory.CommAlg.FlagModelValue
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagModelValueIndependentStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.flag_model_value_independent : GroundTheory.Heights₂.Heights.NumbersDVR.FlagModelValueIndependence.Statement := by
  first | exact @GlobalTheory.CompanionTheory.CommAlg.FlagModelValue.main | exact GlobalTheory.CompanionTheory.CommAlg.FlagModelValue.main | (intros; apply GlobalTheory.CompanionTheory.CommAlg.FlagModelValue.main <;> assumption)
end
end
