module

public import Development.WeilBound.ThetaLifts.TowerModels.PlaneHerm
public import Development.WeilBound.ThetaLifts.CartanFactorisation.Unimod
public import Development.WeilBound.ThetaLifts.TowerModels.DetHerm
public import Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.EventuallySelfDualLatticeIndicatorIsVacuum
public import Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.ExistsFinitePlaceVacuumAnyDarbouxCoordinates
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.ExistsRationalDarbouxHermitianTensorAdeles
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

-- Source module: Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.ExistsRationalDarbouxCoordinatesTensorHermitian

section

@[expose] public section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem Tw.RatDarboux.exists_rational_darboux_of_isGood : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : Base F E), B.IsGood σ → ∀ {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (r s r' s' : ℕ),
    X.IsHerm σ B r s → Y.IsSkew σ B r' s' → ∃ co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J)) (Fin n × Fin d), ∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F, co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F x) = (fun k => algebraMap F (AF F) (y k), fun k => algebraMap F (AF F) (z k)) :=
  fun B hB _ _ X Y r s r' s' hX hY => Tw.RatDarboux.exists_rational_darboux _ B X Y r s r' s' hB hX hY
end
end

-- Source module: Development.WeilBound.ThetaLifts.TowerModels.ModelEx

section

@[expose] public section

noncomputable section

namespace PositivityTheory.ThKG.Tow

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

theorem modelEx : ModelEx := by
  intro F E _ _ _ _ _ σ B hB n d X W r s r' s' hX hW
  classical
  obtain ⟨co, hco⟩ := Tw.RatDarboux.exists_rational_darboux_of_isGood B hB X W r s r' s' hX hW
  obtain ⟨-, ⟨μ, 𝓕, hμ, h𝓕⟩, -⟩ := PositivityTheory.ThKF.unimodularity_holds F E σ hB.cm n X.J 1 (by simpa using hX.herm) (det_herm hX)
  have hS := Tw.VacIndic.eventually_isVac_indicator B hB X W r s r' s' hX hW co hco
  have hA := Tw.VacAny.exists_isVac_any_darboux B hB X W r s r' s' hX hW co
  let M₀ : Model σ X W := ⟨co, fun _ => 0, 0, ∅⟩
  let ind : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ := fun v =>
    Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1
  let vac : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ := fun v =>
    if M₀.IsVac B.ψ v (ind v) then ind v else (hA v).choose
  refine ⟨⟨co, vac, μ, 𝓕⟩, ⟨hco, fun v => ?_, ?_, hμ, h𝓕⟩⟩
  · show M₀.IsVac B.ψ v (vac v)
    by_cases h : M₀.IsVac B.ψ v (ind v)
    · simp only [vac, if_pos h]; exact h
    · simp only [vac, if_neg h]; exact (hA v).choose_spec
  · filter_upwards [hS] with v hv
    show vac v = ind v
    exact if_pos hv

end PositivityTheory.ThKG.Tow

end
end
end
