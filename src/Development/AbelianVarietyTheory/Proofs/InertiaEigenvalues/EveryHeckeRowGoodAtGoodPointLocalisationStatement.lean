module

public import Formalism.LocalRingCardinality.DataTies
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.HeckeStdTwOfStd
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.HeckeSplitOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlOfNotIsConjPl
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RowsExhaust
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverAlg
import ReciprocityTheory.Automorphisms.PlaceA
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftHasPointAtLocalisationSamePlaceStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AtMOfParamRec

section

@[expose] public section

noncomputable section

namespace GlobalTheory.LiftLeaf

open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem atMOfParam_rec {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
    (i : N.Loc) : AtMOfParam N A i := by
  intro x _ Sig hX σ hW
  obtain ⟨P, hP, hB⟩ := hX
  refine ⟨Sig, hW, x, fun w hw => ⟨heckePol N i x w, ?_, rfl⟩⟩
  rw [hB.2.2.2.1 w hw.1]
  exact A.pt_loc i P x hP w hw

theorem atMOfParam (D : D7) (i : D.nd.Loc) : AtMOfParam D.nd D.naut i :=
  atMOfParam_rec D.nd D.naut i

end GlobalTheory.LiftLeaf
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LabCompat

section

@[expose] public section

open GlobalTheory.LiftLeaf GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.LabelCompat

theorem labCompat : ∀ (D : D7) (i : D.nd.Loc), LabCompat D.nd D.naut i := by
  intro D i σ Sig hσ
  have key : ∀ k, D.nd.lab k σ = fun v =>
      D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v)) := by
    intro k
    funext v
    rw [D.naut.lab_loc i k σ v, hσ.2.2 _ (GlobalTheory.FixedPlaceSplit.isSplitPl_plGw D k v)]
  unfold NData.goodRow goodSig
  refine forall_congr' fun k => ?_
  rw [key k]

end GlobalTheory.LabelCompat
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftGoodRowPointGood

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory.GoodLiftPoint

theorem good_of_lift : ∀ (D : D7), SumRepresentations.Conclusion42 D → ∀ (i : D.nd.Loc) (σ : D.what₂.FT) (P : D.naut.AV i) (x : D.nd.X i), D.nd.goodRow σ → thetaOf D.nd D.naut i σ P → D.naut.ptV i P = some x → x ∈ ZgoodN D.nd D.naut i ∧ AtM D.nd D.naut i σ := by
  intro D h42 i σ P x hg hth hpt
  have hne : D.what₂.isot (D.nd.j i) σ ≠ ⊥ := by
    intro h
    apply hth.1
    rw [h, Submodule.map_bot]
  obtain ⟨Sig, hW, hBC⟩ := (h42 i σ hne).2.1
  have hX : HasParamX D.nd D.naut i x Sig := ⟨P, hpt, hBC P hth⟩
  have hZ : x ∈ ZN D.nd D.naut i := by
    refine ⟨P, hpt, _, hBC P hth, ?_⟩
    unfold twistIso
    exact List.mem_map.2 ⟨muPart D.nd D.naut i, by simp, rfl⟩
  have hgood : x ∈ ZgoodN D.nd D.naut i :=
    ⟨hZ, Sig, hX, (GlobalTheory.LabelCompat.labCompat D i σ Sig hW).1 hg⟩
  exact ⟨hgood, GlobalTheory.LiftLeaf.atMOfParam D i x hgood Sig hX σ hW⟩

end GlobalTheory.GoodLiftPoint
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftGoodRowPointGoodStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

theorem _root_.GlobalTheory.T.thetaLift_goodRow_point_good : ∀ (D : D7), SumRepresentations.Conclusion42 D → ∀ (i : D.nd.Loc) (σ : D.what₂.FT) (P : D.naut.AV i) (x : D.nd.X i), D.nd.goodRow σ → thetaOf D.nd D.naut i σ P → D.naut.ptV i P = some x → x ∈ ZgoodN D.nd D.naut i ∧ AtM D.nd D.naut i σ := by
  first | exact @GlobalTheory.GoodLiftPoint.good_of_lift | exact GlobalTheory.GoodLiftPoint.good_of_lift | (intros; apply GlobalTheory.GoodLiftPoint.good_of_lift <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EveryHeckeRowGoodAtGoodPointLocalisation

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory.ExhaustRows

theorem main : ∀ (D : D7) (M : MtFam D), HeckeTied D M → AVTied D M → ∀ Tn : NormalizedLocalCompatibility D M, HeckeStdTw Tn.B → SumRepresentations.Conclusion42 D → GoodFTAll D → ∀ (i : D.nd.Loc) (σ : D.what₂.FT), D.what₂.isot (D.nd.j i) σ ≠ ⊥ → D.nd.goodRow σ ∧ ∃ i' ∈ D.nd.locs (D.nd.j i) (D.nd.w i), HG D.nd D.naut i' ∧ AtM D.nd D.naut i' σ := by
  intro D M hT hA Tn hS h42 hG i σ hne
  have hg : D.nd.goodRow σ := hG σ
  obtain ⟨P, hP⟩ := ((h42 i) σ hne).1.2
  obtain ⟨i', hi', P', x', hth, hx⟩ := GlobalTheory.T.theta_lift_has_point_at_localisation_same_place D M hT hA Tn hS i σ P hP
  obtain ⟨hxg, hat⟩ := GlobalTheory.T.thetaLift_goodRow_point_good D h42 i' σ P' x' hg hth hx
  exact ⟨hg, i', hi', ⟨x', hxg⟩, hat⟩

end GlobalTheory.ExhaustRows
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EveryHeckeRowGoodAtGoodPointLocalisationStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

theorem _root_.GlobalTheory.T.every_heckeRow_good_at_goodPointLocalisation : ∀ (D : D7) (M : MtFam D), HeckeTied D M → AVTied D M → ∀ Tn : NormalizedLocalCompatibility D M, HeckeStdTw Tn.B → SumRepresentations.Conclusion42 D → GoodFTAll D → ∀ (i : D.nd.Loc) (σ : D.what₂.FT), D.what₂.isot (D.nd.j i) σ ≠ ⊥ → D.nd.goodRow σ ∧ ∃ i' ∈ D.nd.locs (D.nd.j i) (D.nd.w i), HG D.nd D.naut i' ∧ AtM D.nd D.naut i' σ := by
  first | exact @GlobalTheory.ExhaustRows.main | exact GlobalTheory.ExhaustRows.main | (intros; apply GlobalTheory.ExhaustRows.main <;> assumption)
end
end
