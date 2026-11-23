module

public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StLemmaETailMass
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StListMono
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StListTailLog
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StRegSection
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StTailShift
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.OfListTailLog
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StRegSectionParts
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
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PBdComparison
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PBdDivides
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PBdMetric
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PBdPartition
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PBdTransition
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PBdWeight
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PBddOnInner
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PChartCont
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PCoordDivDivisible
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PHyperplaneDivisible
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PIndicatorSmooth
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PLemmaETailLog
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StListMonoRaise
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StListMonoDens
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StLocDensContOnOpen
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StMIntegrableOfDensLe
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StMIntMonoOfDensLe
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PListMonoDens
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PListMonoRaise
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PLocDensContOnOpen
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PLogNormHolo
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PMIntMonoOfDensLe
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PMIntegrableOfDensLe
import Mathlib.Analysis.InnerProductSpace.Calculus
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PRegRCont
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PRegSection
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PRegYoDense
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PTailLogOfMass
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PTailShift

-- Source module: GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PBdCocycle

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

theorem BdCocycle.proof (hDense : RegYoDense.Statement) (hHolo : BdEqHolo.Statement) :
    BdCocycle.Statement := by
  intro X _ D A R g hg hEq j k l
  have hOopen : IsOpen (bdDom R j ∩ bdDom R k ∩ bdDom R l) :=
    ((isOpen_bdDom R j).inter (isOpen_bdDom R k)).inter (isOpen_bdDom R l)
  have hOjl : bdDom R j ∩ bdDom R k ∩ bdDom R l ⊆ bdDom R j ∩ bdDom R l := fun _ hy => ⟨hy.1.1, hy.2⟩
  have hOjk : bdDom R j ∩ bdDom R k ∩ bdDom R l ⊆ bdDom R j ∩ bdDom R k := fun _ hy => hy.1
  have hOkl : bdDom R j ∩ bdDom R k ∩ bdDom R l ⊆ bdDom R k ∩ bdDom R l := fun _ hy => ⟨hy.1.2, hy.2⟩
  have hYo : Set.EqOn (g j l) (fun y => g j k y * g k l y)
      ((bdDom R j ∩ bdDom R k ∩ bdDom R l) ∩ R.Yo) := by
    rintro y ⟨hyO, hyY⟩
    have hne : bdEq R l y ≠ 0 := fun h0 => ((hHolo D A R l).2 y hyO.2).1 h0 hyY
    have h1 := hEq j l y (hOjl hyO)
    have h2 := hEq j k y (hOjk hyO)
    have h3 := hEq k l y (hOkl hyO)
    apply mul_right_cancel₀ hne
    show g j l y * bdEq R l y = g j k y * g k l y * bdEq R l y
    rw [← h1, h2, h3, mul_assoc]
  have hall := hYo.of_subset_closure ((hg j l).mono hOjl)
    (((hg j k).mono hOjk).mul ((hg k l).mono hOkl)) Set.inter_subset_left
    ((hDense D A R).open_subset_closure_inter hOopen)
  intro y hy
  exact hall hy

end GroundTheory.Heights₂.Heights.AnalyticLimit
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PBdEqHolo

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.A (coordDiv)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData)

theorem BdEqHolo.proof : BdEqHolo.Statement := by
  intro X _ D A R j
  refine ⟨fun m v hv => ?_, fun y hy => ?_⟩
  · have h : AnalyticAt ℂ (R.ψ j ∘ (A.chart m).symm) v := (R.compat j m).1 v ⟨hv.1, hv.2.1⟩
    have hi : ∀ i, AnalyticAt ℂ (fun w => (R.ψ j ∘ (A.chart m).symm) w i) v :=
      (analyticAt_pi_iff (f := fun i w => (R.ψ j ∘ (A.chart m).symm) w i)).1 h
    show AnalyticAt ℂ (fun w => ∏ i ∈ R.S j, (R.ψ j ∘ (A.chart m).symm) w i) v
    exact Finset.analyticAt_fun_prod _ fun i _ => hi i
  · have hmem := R.mem_Yo_iff j (R.ψ j y) hy.2
    rw [(R.ψ j).left_inv hy.1] at hmem
    rw [hmem, not_not]
    simp only [bdEq, Finset.prod_eq_zero_iff, coordDiv, Set.mem_ofPred_eq]

end GroundTheory.Heights₂.Heights.AnalyticLimit
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PBdNormCont

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Filter Topology
open ReciprocityTheory.AnForm.M (FinHolAtlas)

theorem BdNormCont.proof (hCC : ChartCont.Statement) (hEq : BdEqHolo.Statement) :
    BdNormCont.Statement := by
  intro X _ D A R φ hφ c
  refine continuous_iff_continuousAt.2 fun y₀ => ?_
  set j := bdIdx R y₀
  have hU : IsOpen (bdDom R j) := isOpen_bdDom R j
  have hy₀ : y₀ ∈ bdDom R j := mem_bdDom_bdIdx R y₀
  have hEqc : ContinuousOn (bdEq R j) (bdDom R j) := (hCC D A _ hU).2 _ (hEq D A R j).1
  have hφc : ContinuousOn (φ j) (bdDom R j) := (hCC D A _ hU).1 _ (hφ.1 j)
  have hg : ContinuousOn (fun y => ‖bdEq R j y‖ * Real.exp (-(φ j y + c))) (bdDom R j) :=
    hEqc.norm.mul ((hφc.add continuousOn_const).neg.rexp)
  have hgy : ContinuousAt (fun y => ‖bdEq R j y‖ * Real.exp (-(φ j y + c))) y₀ :=
    hg.continuousAt (hU.mem_nhds hy₀)
  refine hgy.congr ?_
  filter_upwards [hU.mem_nhds hy₀] with y hy
  have hk : y ∈ bdDom R (bdIdx R y) ∩ bdDom R j := ⟨mem_bdDom_bdIdx R y, hy⟩
  have h3 := hφ.2.2 (bdIdx R y) j y hk
  show ‖bdEq R j y‖ * Real.exp (-(φ j y + c)) = ‖bdSec R y y‖ * Real.exp (-(bdPot R φ c).φ y y)
  simp only [bdSec, bdPot]
  simp only [neg_add, Real.exp_add, ← mul_assoc, h3]

end GroundTheory.Heights₂.Heights.AnalyticLimit
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PBdSectionProps

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsSection)

theorem BdSectionProps.proof (hB : BdEqHolo.Statement) : BdSectionProps.Statement := by
  intro X _ D A R φ hφ c
  obtain ⟨h1, h2, h3⟩ := hφ
  refine ⟨⟨fun x j => ?_, fun x x' y hy => ?_⟩, ⟨fun x => (hB D A R _).1, fun x x' y hy => ?_⟩, ?_⟩
  · exact (h1 (bdIdx R x) j).add contDiffOn_const
  · obtain ⟨W, hW, hyW, G, hG, hGe⟩ := h2 (bdIdx R x) (bdIdx R x') y hy
    refine ⟨W, hW, hyW, G, hG, fun z hz => ?_⟩
    have h := hGe z ⟨hz.1.1, hz.1.2, hz.2⟩
    show (φ (bdIdx R x) z + c) - (φ (bdIdx R x') z + c) = (G z).re
    linarith
  · show ‖bdEq R (bdIdx R x) y‖ * Real.exp (-(φ (bdIdx R x) y + c)) =
      ‖bdEq R (bdIdx R x') y‖ * Real.exp (-(φ (bdIdx R x') y + c))
    simp only [neg_add, Real.exp_add, ← mul_assoc]
    rw [h3 _ _ y hy]
  · ext y
    have h := (hB D A R (bdIdx R y)).2 y (mem_bdDom_bdIdx R y)
    show bdEq R (bdIdx R y) y ≠ 0 ↔ y ∈ R.Yo
    rw [Ne, h, not_not]

end GroundTheory.Heights₂.Heights.AnalyticLimit
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PListMono

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

theorem ListMono.proof (hRaise : ListMonoRaise.Statement) (hDens : ListMonoDens.Statement)
    (hCont : LocDensContOnOpen.Statement) (hInt : MIntegrableOfDensLe.Statement)
    (hMono : MIntMonoOfDensLe.Statement) : ListMono.Statement := by
  intro X _ _ _ D A Yo r Om C₁ th u hYo hT
  have hdens := hDens A Yo th Om.pot u hYo (fun i => (hT i).th_pot) Om.isPot
    (fun i => (hT i).u_smooth) (fun i => (hT i).th_le) (fun i => (hT i).nonneg)
  refine ⟨fun i => hRaise A Yo (th i) Om.pot (u i) hYo (hT i).th_pot Om.isPot (hT i).u_smooth
    (hT i).th_le (hT i).nonneg, fun j y hy hY => (hdens j y hy hY).1, fun g hg0 hgV hgA => ?_⟩
  have hcT := hCont A Yo th u hYo (fun i => (hT i).th_pot) (fun i => (hT i).u_smooth)
  have hcA := hCont A Yo (fun _ => Om.pot) u hYo (fun _ => Om.isPot) (fun i => (hT i).u_smooth)
  exact ⟨hInt A Yo _ _ hYo hcT hcA hdens g hgV hgA, hMono A Yo _ _ hdens g hg0 hgV hgA⟩

end GroundTheory.Heights₂.Heights.AnalyticLimit
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PNormSqSmooth

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open scoped ContDiff

theorem NormSqSmooth.proof : NormSqSmooth.Statement := by
  intro X _ D A U g hg j
  have h1 : ContDiffOn ℝ ∞ (g ∘ (A.chart j).symm)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U) :=
    ((hg j).contDiffOn_of_completeSpace (n := ∞)).restrict_scalars ℝ
  have h2 : ContDiff ℝ ∞ (fun w : ℂ => ‖w‖ ^ 2) := contDiff_norm_sq ℝ
  exact h2.comp_contDiffOn h1

end GroundTheory.Heights₂.Heights.AnalyticLimit
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.TailBound

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ForSecondHalf

open GroundTheory.Heights₂.Heights.AnalyticLimit

theorem ListMono.full : ListMono.Statement :=
  ListMono.proof ListMonoRaise.proof ListMonoDens.proof LocDensContOnOpen.proof
    MIntegrableOfDensLe.proof MIntMonoOfDensLe.proof

theorem RegSection.full : RegSection.Statement :=
  RegSection.proof RegYoDense.proof RegRCont.proof
    (BdMetric.proof ChartCont.proof
      (BdTransition.proof RegYoDense.proof BdEqHolo.proof
        (BdDivides.proof (CoordDivDivisible.proof HyperplaneDivisible.proof)))
      (BdCocycle.proof RegYoDense.proof BdEqHolo.proof)
      (LogNormHolo.proof ChartCont.proof)
      (BdWeight.proof BdPartition.proof IndicatorSmooth.proof NormSqSmooth.proof))
    (BdSectionProps.proof BdEqHolo.proof)
    (BdNormCont.proof ChartCont.proof BdEqHolo.proof)
    (BdComparison.proof ChartCont.proof BddOnInner.proof)

theorem TailShift.full : TailShift.Statement := TailShift.proof

theorem LemmaETailLog.of_lemmaETailMass (h : LemmaETailMass.Statement) : LemmaETailLog.Statement :=
  LemmaETailLog.proof h TailLogOfMass.proof

theorem ListTailLog.of_lemmaETailMass (h : LemmaETailMass.Statement) : ListTailLog.Statement :=
  ListTailLog.of_lemmaE (LemmaETailLog.of_lemmaETailMass h) ListMono.full RegSection.full
    TailShift.full

end GroundTheory.Heights₂.Heights.ForSecondHalf
end
end
