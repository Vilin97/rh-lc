module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTrans
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartCharacterTrivialOnStandardPairStabilizer
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
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelComponentFixesStandardPairStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPointsLieOverDistinctPlacesStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitFrameGLFiniteMatrixOffPlaceEqOneStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceComponentKeepsLevelFunctionalStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceComponentMemBaseLatticeLevelOfFixesPaiStatement
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Mathlib.Tactic.Linter.Style
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.ValuedAlgebraMapEqOne
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardDatumSplitPlacesOverLevelPrime
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryClassRepresentativesBijective
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicPointEqProdSplitComponentsMulOff

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartCharacterTrivialOnStandardPairStabilizerStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.chartCharacter_trivial_on_standardPairStabilizer : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    GlobalTheory.AdForm.StdT I l Z u p β Q L → ∀ j, j ≤ B.R.m → ∀ b, ∀ i (g : GL (Fin ((I.rec7 l Z).sp.X j).rank) k), g • Q j i = Q j i → ∀ h : (β j i).gl g ∈ A.U j b, A.chi j b ⟨_, h⟩ = 1 := by
  first | exact @GlobalTheory.AdForm.chi_std_trivial | exact GlobalTheory.AdForm.chi_std_trivial | (intros; apply GlobalTheory.AdForm.chi_std_trivial <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceFrameGLMemCompactRealTrivial

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdForm

noncomputable section

namespace GlobalTheory.FrameGfC

theorem gl_mem_GfC : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S : HSp D) (n : Type) [Fintype n] [DecidableEq n] (β : Frame p S n) (g : GL n k), β.gl g ∈ GfC S := by
  intro D k _ _ _ _ p S n _ _ β g
  have hg := β.gl_supp g
  have he := p.split
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h : infPart D ((mt S (β.gl g) - 1) i j) = 0 := by
    rw [← hg i j, RingHom.map_mul, RingHom.map_add (f := _), GlobalTheory.SplitScalar.infPart_splitIdem he,
      GlobalTheory.SplitScalar.infPart_splitIdem (GlobalTheory.SplitScalar.isSplitIdem_conj he), add_zero, zero_mul]
  rw [Matrix.sub_apply, RingHom.map_sub, sub_eq_zero] at h
  show infPart D (mt S (β.gl g) i j) = (1 : Matrix _ _ _) i j
  rw [h, Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · rw [RingHom.map_one]
  · rw [RingHom.map_zero]

end GlobalTheory.FrameGfC
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceFrameGLMemCompactRealTrivialStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdForm


theorem _root_.GlobalTheory.T.splitPlaceFrameGL_mem_compactRealTrivial : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S : HSp D) (n : Type) [Fintype n] [DecidableEq n] (β : Frame p S n) (g : GL n k), β.gl g ∈ GfC S := by
  first | exact @GlobalTheory.FrameGfC.gl_mem_GfC | exact GlobalTheory.FrameGfC.gl_mem_GfC | (intros; apply GlobalTheory.FrameGfC.gl_mem_GfC <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardDatumSplitPlacesOverLevelPrimeStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdForm


theorem _root_.GlobalTheory.T.standardDatum_splitPlaces_over_levelPrime : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    GlobalTheory.AdForm.StdT I l Z u p β Q L → ∀ i, ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ (p i).v.asIdeal := by
  first | exact @GlobalTheory.AdForm.stdT_levelPrime_mem_v | exact GlobalTheory.AdForm.stdT_levelPrime_mem_v | (intros; apply GlobalTheory.AdForm.stdT_levelPrime_mem_v <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardPairStabiliserMemChartLevel

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.StabLev

theorem stab_mem_level : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    GlobalTheory.AdForm.StdT I l Z u p β Q L → ∀ j, j ≤ B.R.m → ∀ b, ∀ i (g : GL (Fin ((I.rec7 l Z).sp.X j).rank) k), g • Q j i = Q j i → (β j i).gl g ∈ A.U j b := by
  intro B X I hOk hPins l Z u a Ch A hA k _ _ _ _ ι p β Q L hStd j hj b i g hg
  rw [hA.U j hj b]
  refine ⟨GlobalTheory.T.splitPlaceFrameGL_mem_compactRealTrivial _ _ _ _ _ _ _, ?_⟩
  obtain ⟨x, hx⟩ := GlobalTheory.AdForm.RdVal.finM_mem ((I.rec7 l Z).sp.X j) (rankN (I.rec7 l Z) j hj) (gramN (I.rec7 l Z) j hj) rfl ((β j i).gl g)
  have hmem : x.1 ∈ (A.K j hj b).lev.U := by
    rw [(A.K j hj b).lev.U_eq]
    refine ⟨x.2, fun v => ?_⟩
    by_cases hv : v = (p i).v
    · subst hv
      have hT := GlobalTheory.T.standardDatum_splitPlaces_over_levelPrime I hOk hPins l Z u k ι p β Q L hStd i
      exact GlobalTheory.T.splitPlace_component_keeps_level_functional I hOk hPins l Z u a Ch A hA k ι p β Q L hStd j hj b i g hg x hx hT
        (GlobalTheory.T.splitPlace_component_mem_baseLattice_level_of_fixes_pair I hOk hPins l Z u a Ch A hA k ι p β Q L hStd j hj b i g hg x hx)
    · rw [GlobalTheory.T.splitFrameGL_finiteMatrix_offPlace_eq_one _ _ _ _ _ _ g _ (rankN (I.rec7 l Z) j hj) x.1 hx v hv]
      exact Subgroup.one_mem _
  exact ⟨⟨x.1, hmem⟩, hx⟩

end GlobalTheory.AdForm.StabLev

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardPairStabiliserMemChartLevelStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.standardPair_stabiliser_mem_chartLevel : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    GlobalTheory.AdForm.StdT I l Z u p β Q L → ∀ j, j ≤ B.R.m → ∀ b, ∀ i (g : GL (Fin ((I.rec7 l Z).sp.X j).rank) k), g • Q j i = Q j i → (β j i).gl g ∈ A.U j b := by
  first | exact @GlobalTheory.AdForm.StabLev.stab_mem_level | exact GlobalTheory.AdForm.StabLev.stab_mem_level | (intros; apply GlobalTheory.AdForm.StabLev.stab_mem_level <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicPointEqProdSplitComponentsMulOffStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.unitaryAdelicPoint_eq_prod_splitComponents_mul_off : ∀ (D : D7) (S : HSp D) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (β : ∀ i, Frame (p i) S n), Function.Injective (fun i => (p i).v) → ∀ J : List ι, J.Nodup → (∀ i, i ∈ J) → ∀ κ : GA D S, ∃ g : ι → GL n k, (∀ i, κ * ((β i).gl (g i))⁻¹ ∈ grpOff S (· = (p i).v)) ∧ ∃ κ' ∈ grpOff S (fun x => ∃ i, x = (p i).v), κ = (J.map fun i => (β i).gl (g i)).prod * κ' := by
  first | exact @GlobalTheory.FinPl.LocProd.eq_prod_gl_mul_off | exact GlobalTheory.FinPl.LocProd.eq_prod_gl_mul_off | (intros; apply GlobalTheory.FinPl.LocProd.eq_prod_gl_mul_off <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistLevelStabiliserAtLevelPrimeProof

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.AdForm.twLev_prime : GlobalTheory.AdForm.TwLev' := by
  intro B X I hOk hPins l Z u a Ch A hA k _ _ _ _ ι p β Q L hS J hJ hJall j hj b
  refine ⟨fun i g hg => ⟨GlobalTheory.T.standardPair_stabiliser_mem_chartLevel I hOk hPins l Z u a Ch A hA k ι p β Q L hS j hj b i g hg,
    GlobalTheory.T.chartCharacter_trivial_on_standardPairStabilizer I hOk hPins l Z u a Ch A hA k ι p β Q L hS j hj b i g hg _⟩, fun κ hκ => ?_⟩
  obtain ⟨g, hg1, κ', hκ', heq⟩ := GlobalTheory.T.unitaryAdelicPoint_eq_prod_splitComponents_mul_off (I.rec7 l Z) ((I.rec7 l Z).sp.X j) k ι p _ (β j)
    (GlobalTheory.T.splitPoints_lie_over_distinct_places I hOk hPins l Z u p β Q L hS) J hJ hJall κ
  exact ⟨g, fun i => GlobalTheory.T.chartLevel_component_fixes_standardPair I hOk hPins l Z u a Ch A hA k ι p β Q L hS j hj b κ hκ i (g i) (hg1 i), κ', hκ', heq⟩
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistLevelStabiliserAtLevelPrimeProofStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.twistLevelStabiliserAtLevelPrime_proof : GlobalTheory.AdForm.TwLev' := by
  first | exact @GlobalTheory.AdForm.twLev_prime | exact GlobalTheory.AdForm.twLev_prime | (intros; apply GlobalTheory.AdForm.twLev_prime <;> assumption)
end
end
