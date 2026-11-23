module

public import Formalism.GradedWeylDivisibility.StatementA
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.BideterminantDominance
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.BideterminantMem
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DomPow
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylIntRat
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylMap
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LBidetLemmas
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylNonDom
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylPoint
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylRowGraded
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylRowStable
import Formalism.GradedWeylDivisibility.StatementA
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LSatLemmas
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockDiagBound
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ProdFactorialSupportSubSingle
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LFockbLemmas
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockRowAdj
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockSubAdj
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.HWRaise
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.HWRowWeight
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.RowDivStable
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.SumIcoTsubTelescope
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.WeylRowDivStable

-- Source module: Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylMul

section

@[expose] public section

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem dualWeylModuleMul : DualWeylMul := fun _ _ _ _ _ _ _ _ =>
  ⟨fun hf hg => dualWeyl_mul hf hg, one_mem_dualWeyl⟩

end Formalism.GradedWeylDivisibility
end
end
end

-- Source module: Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylSat

section

section

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem dualWeylModuleSaturated : DualWeylSat := by
  intro R _ _ r n ν c f hc hcf
  rw [lsat_mem_dualWeyl] at hcf ⊢
  obtain ⟨hwh, hcol⟩ := hcf
  refine ⟨fun {d} hd => hwh ?_, fun l j hlj => ?_⟩
  · rw [AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul]
    exact mul_ne_zero hc hd
  · have h := hcol l j hlj
    rw [smul_eq_C_mul, map_mul, map_mul, algHom_C, algHom_C] at h
    exact mul_left_cancel₀ (by simpa using hc) h

end Formalism.GradedWeylDivisibility
end
end
end

-- Source module: Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockHerm

section

section

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem fischerInnerConjSymm_holds : FockHerm := by
  intro σ f g
  exact Formalism.REAL.fischerInner_eq_star g f

end Formalism.GradedWeylDivisibility
end
end
end

-- Source module: Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockPos

section

section

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem fischerInnerPos : FockPos := by
  intro σ f hf
  rw [LFockb_fockF_self]
  refine ⟨?_, Complex.ofReal_im _⟩
  rw [Complex.ofReal_re]
  apply Finset.sum_pos
  · intro m hm
    apply mul_pos
    · exact Complex.normSq_pos.mpr (mem_support_iff.mp hm)
    · exact Nat.cast_pos.mpr (Finset.prod_pos fun k _ => Nat.factorial_pos _)
  · exact Finset.nonempty_of_ne_empty fun h => hf (support_eq_empty.mp h)

end Formalism.GradedWeylDivisibility
end
end
end

-- Source module: Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockWeightOrth

section

section

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem fischerInnerWeightOrthogonal_holds : FockWeightOrth := by
  intro σ M _ w μ μ' f g hne hf hg
  unfold Formalism.REAL.fockF
  refine Finset.sum_eq_zero fun m hm => ?_
  have hgm : g.coeff m = 0 := by
    by_contra h
    exact hne ((hf (mem_support_iff.mp hm)).symm.trans (hg h))
  rw [hgm, star_zero, mul_zero, zero_mul]

end Formalism.GradedWeylDivisibility
end
end
end

-- Source module: Formalism.GradedWeylDivisibility.FockSpaceTableaux.HighestWeightVectorNeZero

section

section

namespace Formalism.GradedWeylDivisibility

open MvPolynomial

theorem highestWeightVectorNeZero : HWNe := by
  intro R _ _ r n hn ν h
  have key : ∀ (s : ℕ) (hr : s ≤ r) (hs : s ≤ n),
      eval (fun v : Fin r × Fin n => if v.1.val = v.2.val then (1 : R) else 0)
        (lpMinor R s hr hs) = 1 := by
    intro s hr hs
    unfold lpMinor
    rw [RingHom.map_det]
    convert Matrix.det_one (R := R) (n := Fin s)
    ext p q
    simp [RingHom.mapMatrix_apply, Matrix.one_apply, Fin.ext_iff]
  have h2 := congrArg (eval (fun v : Fin r × Fin n => if v.1.val = v.2.val then (1 : R) else 0)) h
  simp [hw, map_prod, map_pow, key] at h2

end Formalism.GradedWeylDivisibility
end
end

-- Source module: Formalism.GradedWeylDivisibility.FockSpaceTableaux.RowNuSum

section

@[expose] public section

namespace Formalism.GradedWeylDivisibility

open MvPolynomial

theorem rowPartSum : RowNuSum := by
  classical
  intro r n ν hn k
  let g : ℕ → ℕ := fun i => if i < k then (if h : i < n then ν ⟨i, h⟩ else 0) else 0
  have hL : ∑ a : Fin r with a.val < k, rowNu (r := r) ν a = ∑ i ∈ Finset.range r, g i := by
    rw [Finset.sum_filter, ← Fin.sum_univ_eq_sum_range g r]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [g, rowNu]
  have hR : ∑ t : Fin n with t.val < k, ν t = ∑ i ∈ Finset.range n, g i := by
    rw [Finset.sum_filter, ← Fin.sum_univ_eq_sum_range g n]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [g, dif_pos t.isLt]
  rw [hL, hR]
  refine (Finset.sum_subset (fun i hi => ?_) (fun i hi hni => ?_)).symm
  · simp only [Finset.mem_range] at hi ⊢; omega
  · simp only [Finset.mem_range] at hi hni
    simp only [g, dif_neg hni, ite_self]

end Formalism.GradedWeylDivisibility
end
end

-- Source module: Formalism.GradedWeylDivisibility.DualWeylDominanceOf

section

@[expose] public section

namespace Formalism.GradedWeylDivisibility

theorem bidetMem : BideterminantMem := bideterminantMem
theorem hwMem : HWMem := highestWeightVectorMem
theorem hwNe : HWNe := highestWeightVectorNeZero
theorem hwRowWeight : HWRowWeight := highestWeightVectorRowWeight
theorem dualWeylSat : DualWeylSat := dualWeylModuleSaturated
theorem dualWeylPoint : DualWeylPoint := dualWeylModuleMemIff
theorem dualWeylRowStable : DualWeylRowStable := dualWeylModuleRowActionStable
theorem rowDivStable : RowDivStable := dualWeylModuleRowDividedPowerStable
theorem dualWeylRowGraded : DualWeylRowGraded := dualWeylModuleRowGraded
theorem dualWeylMap : DualWeylMap := dualWeylModuleMap
theorem dualWeylIntRat : DualWeylIntRat := dualWeylModuleIntRat
theorem weylLeDual : WeylLeDual := by
  intro R _ r n hn ν hν
  unfold weyl
  rw [Submodule.span_le]
  rintro _ ⟨w, rfl⟩
  induction w with
  | nil => exact hwMem R r n hn ν hν
  | cons x w ih => exact rowDivStable R r n ν x.1 x.2.1 x.2.2 _ ih
theorem dualWeylNonDom : DualWeylNonDom := dualWeylModuleNonDominant
theorem bidetDominance : BideterminantDominance := bideterminantDominance
theorem dualWeylMul : DualWeylMul := dualWeylModuleMul
theorem hwRaise : HWRaise := highestWeightVectorRaising
theorem weylRowDivStable : WeylRowDivStable := weylModuleRowDividedPowerStable
theorem rowNuSum : RowNuSum := rowPartSum
theorem fockHerm : FockHerm := fischerInnerConjSymm_holds
theorem fockPos : FockPos := fischerInnerPos
theorem fockWeightOrth : FockWeightOrth := fischerInnerWeightOrthogonal_holds
theorem fockSubAdj : FockSubAdj := fischerInnerSubstitutionAdjoint
theorem fockRowAdj : FockRowAdj := fischerInnerRowActionAdjoint
theorem domPow : DomPow := dominancePowerProduct_holds
theorem fockDiagBound : FockDiagBound := fockDiagBound_of domPow

end Formalism.GradedWeylDivisibility
end
end
