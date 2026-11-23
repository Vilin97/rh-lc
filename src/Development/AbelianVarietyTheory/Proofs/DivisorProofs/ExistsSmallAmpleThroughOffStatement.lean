module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDivOfGlobalSectionPowNumEquivMultiple
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsQuasicoherentOfForallExistsAffine
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilQDivisorAvoidsPointCartierIffNotMemSuppStatement
import Mathlib.Algebra.Order.Star.Rat

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDivOfGlobalSectionPowNumEquivMultipleStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

theorem _root_.GlobalTheory.T.cartierDivOfGlobalSection_pow_numEquiv_multiple : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ (N : LB X) (hN : N.IsLB) (l m : ℕ) (s : (lbPow N l).Sec) (hs : genericPoint X ∈ nonzeroLocus s), 0 < m → (divOfSec (isLB_lbPow hN l) s hs).Eff ∧ QNum p N ((l : ℚ) / m) (qWeil (divOfSec (isLB_lbPow hN l) s hs) m) := by
  first | exact @GlobalTheory.PairStep.qNum_divOfSec | exact GlobalTheory.PairStep.qNum_divOfSec | (intros; apply GlobalTheory.PairStep.qNum_divOfSec <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleSectionNonvanishingAtNotSpecializing

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem exists_sec_mem_not_mem_of_not_specializes :
    ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (N : LB X) (x z : X), IsAmpleLB N → ¬ z ⤳ x →
      ∃ (l : ℕ) (s : (lbPow N l).Sec), 0 < l ∧ x ∈ nonzeroLocus s ∧ z ∉ nonzeroLocus s := by
  intro X _ _ N x z hN hzx
  let U : X.Opens := ⟨(closure ({z} : Set X))ᶜ, isClosed_closure.isOpen_compl⟩
  have hx : x ∈ U := fun h => hzx (specializes_iff_mem_closure.2 h)
  obtain ⟨n, hn, s, hs, hle, -⟩ := hN.exists_affine_le hx
  exact ⟨n, s, hn, hs, fun h => hle h (subset_closure rfl)⟩

end GlobalTheory.PairStep
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleSectionNonvanishingAtNotSpecializingStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

theorem _root_.GlobalTheory.T.exists_ampleSection_nonvanishing_at_not_specializing : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (N : LB X) (x z : X), IsAmpleLB N → ¬ z ⤳ x → ∃ (l : ℕ) (s : (lbPow N l).Sec), 0 < l ∧ x ∈ nonzeroLocus s ∧ z ∉ nonzeroLocus s := by
  first | exact @GlobalTheory.PairStep.exists_sec_mem_not_mem_of_not_specializes | exact GlobalTheory.PairStep.exists_sec_mem_not_mem_of_not_specializes | (intros; apply GlobalTheory.PairStep.exists_sec_mem_not_mem_of_not_specializes <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmallAmpleThroughOff

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

theorem GlobalTheory.PairStep.exists_small_ample_through_off : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ (N : LB X) (x z : X) (ε : ℚ), IsAmpleLB N → ¬ z ⤳ x → 0 < ε → ∃ (b : ℚ) (A : X → ℚ), 0 ≤ b ∧ b ≤ ε ∧ QNum p N b A ∧ Off A x ∧ ¬ Off A z := by
  intro X _ _ p hp N x z ε hN hzx hε
  obtain ⟨l, s, hl, hx, hz⟩ := GlobalTheory.T.exists_ampleSection_nonvanishing_at_not_specializing X N x z hN hzx
  have hs : genericPoint X ∈ nonzeroLocus s :=
    (genericPoint_specializes x).mem_open (nonzeroLocus s).isOpen hx
  obtain ⟨m, hm⟩ := exists_nat_ge ((l : ℚ) / ε)
  have hm0 : 0 < m := by
    have : (0 : ℚ) < (l : ℚ) / ε := div_pos (by exact_mod_cast hl) hε
    exact_mod_cast this.trans_le hm
  obtain ⟨hE, hQ⟩ := GlobalTheory.T.cartierDivOfGlobalSection_pow_numEquiv_multiple X p hp N hN.isLB l m s hs hm0
  refine ⟨(l : ℚ) / m, _, by positivity, ?_, hQ, ?_, ?_⟩
  · have hm' : (0 : ℚ) < m := by exact_mod_cast hm0
    rw [div_le_iff₀ hm']
    rw [div_le_iff₀ hε] at hm
    linarith [mul_comm (m : ℚ) ε]
  · exact (GlobalTheory.T.weilQDivisorAvoidsPoint_cartier_iff_notMem_supp X _ m x hE hm0).2 (notMem_supp_divOfSec.2 hx)
  · rw [GlobalTheory.T.weilQDivisorAvoidsPoint_cartier_iff_notMem_supp X _ m z hE hm0, notMem_supp_divOfSec]
    exact hz
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmallAmpleThroughOffStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

theorem _root_.GlobalTheory.T.exists_small_ample_through_off' : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ (N : LB X) (x z : X) (ε : ℚ), IsAmpleLB N → ¬ z ⤳ x → 0 < ε → ∃ (b : ℚ) (A : X → ℚ), 0 ≤ b ∧ b ≤ ε ∧ QNum p N b A ∧ Off A x ∧ ¬ Off A z := by
  first | exact @GlobalTheory.PairStep.exists_small_ample_through_off | exact GlobalTheory.PairStep.exists_small_ample_through_off | (intros; apply GlobalTheory.PairStep.exists_small_ample_through_off <;> assumption)
end
end
