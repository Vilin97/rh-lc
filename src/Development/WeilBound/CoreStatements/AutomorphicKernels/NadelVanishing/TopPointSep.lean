module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PointSeparationPair
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsQuasicoherentOfForallExistsAffine
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeparateTwoPointsNefBigStatement
import Mathlib.Algebra.Order.Star.Rat
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.NadelVanishingPairsOfPrincipalisation
public import Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.NefLineBundleNumericalTheoremsProof
public import Development.WeilBound.CoreStatements.ResolutionCharZero.PrincipalisationClosed

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalBudgetsTwoPointInduction

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem exists_rat_budget_term (r : ℕ) (hr : 0 < r) (e : ℕ) (he : e ≠ 0) (c : ℝ) (hc : 0 < c) :
    ∃ q : ℚ, 0 < q ∧ (q : ℝ) < (2 : ℝ) ^ (1 / (e : ℝ)) * e / (r * c) ∧
      ∀ t : ℤ, c ^ e < (t : ℝ) / (r : ℝ) ^ e → 2 * (e : ℚ) ^ e < q ^ e * t := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have heR : (0 : ℝ) < e := by exact_mod_cast Nat.pos_of_ne_zero he
  have hapos : 0 < ((r : ℝ) * c) ^ e := by positivity
  obtain ⟨T, hT⟩ : ∃ T : ℤ, T = ⌊((r : ℝ) * c) ^ e⌋ + 1 := ⟨_, rfl⟩
  have hTa : ((r : ℝ) * c) ^ e < (T : ℝ) := by
    rw [hT]; push_cast; exact Int.lt_floor_add_one _
  have hTpos : (0 : ℝ) < T := hapos.trans hTa
  have hupos : 0 < (2 : ℝ) ^ (1 / (e : ℝ)) * e / (r * c) := by positivity
  have hue : ((2 : ℝ) ^ (1 / (e : ℝ)) * e / (r * c)) ^ e = 2 * (e : ℝ) ^ e / ((r : ℝ) * c) ^ e := by
    rw [div_pow, mul_pow, one_div, Real.rpow_inv_natCast_pow (by norm_num) he]
  have hv0 : 0 ≤ (2 * (e : ℝ) ^ e / T) ^ ((e : ℝ)⁻¹) := by positivity
  have hve : ((2 * (e : ℝ) ^ e / T) ^ ((e : ℝ)⁻¹)) ^ e = 2 * (e : ℝ) ^ e / T :=
    Real.rpow_inv_natCast_pow (by positivity) he
  have hvu : (2 * (e : ℝ) ^ e / T) ^ ((e : ℝ)⁻¹) < (2 : ℝ) ^ (1 / (e : ℝ)) * e / (r * c) := by
    rw [← pow_lt_pow_iff_left₀ hv0 hupos.le he, hve, hue]
    exact div_lt_div_of_pos_left (by positivity) hapos hTa
  obtain ⟨q, hvq, hqu⟩ := exists_rat_btwn hvu
  have hq0 : (0 : ℝ) < q := lt_of_le_of_lt hv0 hvq
  refine ⟨q, by exact_mod_cast hq0, hqu, ?_⟩
  intro t ht
  have hct : c ^ e * (r : ℝ) ^ e < t := (lt_div_iff₀ (by positivity)).1 ht
  have hat : ((r : ℝ) * c) ^ e < t := by
    calc ((r : ℝ) * c) ^ e = c ^ e * (r : ℝ) ^ e := by rw [mul_pow, mul_comm]
      _ < t := hct
  have hTt : (T : ℝ) ≤ t := by
    have h1 := Int.floor_lt.2 hat
    have : T ≤ t := by omega
    exact_mod_cast this
  have key : 2 * (e : ℝ) ^ e < (q : ℝ) ^ e * t := by
    have h1 := pow_lt_pow_left₀ hvq hv0 he
    rw [hve, div_lt_iff₀ hTpos] at h1
    calc 2 * (e : ℝ) ^ e < (q : ℝ) ^ e * T := h1
      _ ≤ (q : ℝ) ^ e * t := mul_le_mul_of_nonneg_left hTt (by positivity)
  exact_mod_cast key

theorem exists_rat_budgets : ∀ (n r : ℕ) (c : ℕ → ℝ), 0 < r → (∀ e ∈ Finset.Icc 1 n, 0 < c e) →
    ∑ e ∈ Finset.Icc 1 n, (2 : ℝ) ^ (1 / (e : ℝ)) * e / c e ≤ 1 →
    ∃ (h : ℕ → ℚ), (∀ e, 0 < h e) ∧ ∑ e ∈ Finset.Icc 1 n, h e < 1 / (r : ℚ) ∧
      ∀ e ∈ Finset.Icc 1 n, ∀ t : ℤ, c e ^ e < (t : ℝ) / (r : ℝ) ^ e →
        2 * (e : ℚ) ^ e < h e ^ e * t := by
  intro n r c hr hc hsum
  have hex : ∀ e, ∃ q : ℚ, 0 < q ∧ (e ∈ Finset.Icc 1 n →
      (q : ℝ) < (2 : ℝ) ^ (1 / (e : ℝ)) * e / (r * c e) ∧
      ∀ t : ℤ, c e ^ e < (t : ℝ) / (r : ℝ) ^ e → 2 * (e : ℚ) ^ e < q ^ e * t) := by
    intro e
    by_cases he : e ∈ Finset.Icc 1 n
    · have he0 : e ≠ 0 := by
        have := (Finset.mem_Icc.1 he).1
        omega
      obtain ⟨q, hq0, hqu, hqt⟩ := exists_rat_budget_term r hr e he0 (c e) (hc e he)
      exact ⟨q, hq0, fun _ => ⟨hqu, hqt⟩⟩
    · exact ⟨1, one_pos, fun h => absurd h he⟩
  choose h hpos hprop using hex
  refine ⟨h, hpos, ?_, fun e he => (hprop e he).2⟩
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hR : ∑ e ∈ Finset.Icc 1 n, (h e : ℝ) < 1 / (r : ℝ) := by
    rcases (Finset.Icc 1 n).eq_empty_or_nonempty with hE | hE
    · rw [hE, Finset.sum_empty]; positivity
    · calc ∑ e ∈ Finset.Icc 1 n, (h e : ℝ)
          < ∑ e ∈ Finset.Icc 1 n, (2 : ℝ) ^ (1 / (e : ℝ)) * e / (r * c e) :=
            Finset.sum_lt_sum_of_nonempty hE (fun e he => (hprop e he).1)
        _ = 1 / (r : ℝ) * ∑ e ∈ Finset.Icc 1 n, (2 : ℝ) ^ (1 / (e : ℝ)) * e / c e := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun e _ => by ring
        _ ≤ 1 / (r : ℝ) * 1 := mul_le_mul_of_nonneg_left hsum (by positivity)
        _ = 1 / (r : ℝ) := mul_one _
  have hR' : ((∑ e ∈ Finset.Icc 1 n, h e : ℚ) : ℝ) < ((1 / (r : ℚ) : ℚ) : ℝ) := by
    push_cast; exact hR
  exact Rat.cast_lt.mp hR'

end GlobalTheory.PairStep
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalBudgetsTwoPointInductionStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

theorem _root_.GlobalTheory.T.exists_rational_budgets_twoPointInduction : ∀ (n r : ℕ) (c : ℕ → ℝ), 0 < r → (∀ e ∈ Finset.Icc 1 n, 0 < c e) → ∑ e ∈ Finset.Icc 1 n, (2 : ℝ) ^ (1 / (e : ℝ)) * e / c e ≤ 1 → ∃ (h : ℕ → ℚ), (∀ e, 0 < h e) ∧ ∑ e ∈ Finset.Icc 1 n, h e < 1 / (r : ℚ) ∧ ∀ e ∈ Finset.Icc 1 n, ∀ t : ℤ, c e ^ e < (t : ℝ) / (r : ℝ) ^ e → 2 * (e : ℚ) ^ e < h e ^ e * t := by
  first | exact @GlobalTheory.PairStep.exists_rat_budgets | exact GlobalTheory.PairStep.exists_rat_budgets | (intros; apply GlobalTheory.PairStep.exists_rat_budgets <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KollarTwoPointSeparationOfNadelVanishing

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory

theorem pointSeparationPair_of_vanishing :
    GlobalTheory.Published.Principalisation → GlobalTheory.Published.NadelVanishingPair → GlobalTheory.Published.NefNumerics →
      GlobalTheory.Published.PointSeparationPair := by
  intro hP hV hN X _ _ _ p n hproj hdim M Δ m G r N₀ x₁ x₂ c hM hΔ hklt hm hG hr hnef hbig hC
    h₁ h₂ hx hc hZ hs
  letI := algebraΓOfHom p
  obtain ⟨h, hpos, hsum, hh⟩ := GlobalTheory.T.exists_rational_budgets_twoPointInduction n r c hr hc hs
  have hr' : (0 : ℚ) < (r : ℚ) := by exact_mod_cast hr
  refine GlobalTheory.T.separate_two_points_nef_big hP hV hN X p n hproj hdim M Δ m G N₀ (1 / (r : ℚ)) h x₁ x₂ hM hΔ hklt hm hG
    hnef hbig ?_ h₁ h₂ hx hpos ?_ hsum (by positivity)
  · intro C hCc
    rw [hC C hCc]
    ring
  · intro z e hz he hze
    have hle : e ≤ n := by
      have h1 := topologicalKrullDim_subspace_le X (closure ({z} : Set X))
      rw [hze, hdim] at h1
      exact_mod_cast h1
    have hmem : x₁ ∈ Closeds.closure ({z} : Set X) ∨ x₂ ∈ Closeds.closure ({z} : Set X) := by
      rcases hz with hz | hz
      · exact Or.inl (specializes_iff_mem_closure.1 hz)
      · exact Or.inr (specializes_iff_mem_closure.1 hz)
    have hZ' := hZ (Closeds.closure ({z} : Set X)) e isIrreducible_singleton.closure hmem he hze
    exact hh e (Finset.mem_Icc.2 ⟨he, hle⟩) _ hZ'

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KollarTwoPointSeparationOfNadelVanishingStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

theorem _root_.GlobalTheory.T.kollarTwoPointSeparation_of_nadelVanishing : GlobalTheory.Published.Principalisation → GlobalTheory.Published.NadelVanishingPair → GlobalTheory.Published.NefNumerics → GlobalTheory.Published.PointSeparationPair := by
  first | exact @GlobalTheory.pointSeparationPair_of_vanishing | exact GlobalTheory.pointSeparationPair_of_vanishing | (intros; apply GlobalTheory.pointSeparationPair_of_vanishing <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NadelVanishingPairsOfPrincipalisationStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

theorem _root_.GlobalTheory.T.nadel_vanishing_pairs_of_principalisation : GlobalTheory.Published.Principalisation → GlobalTheory.Published.NadelVanishingPair := by
  first | exact @GlobalTheory.Discrepancy.nadelVanishingPair_of_principalisation | exact GlobalTheory.Discrepancy.nadelVanishingPair_of_principalisation | (intros; apply GlobalTheory.Discrepancy.nadelVanishingPair_of_principalisation <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefLineBundleNumericalTheoremsProofStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.nefLineBundleNumericalTheorems_proof : GlobalTheory.Published.NefNumerics := by
  first | exact @GlobalTheory.nefNumerics_outright | exact GlobalTheory.nefNumerics_outright | (intros; apply GlobalTheory.nefNumerics_outright <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointSeparationPairOfPrincipalisation

section

@[expose] public section

theorem GlobalTheory.pointSeparationPair_of_principalisation :
    GlobalTheory.Published.Principalisation → GlobalTheory.Published.PointSeparationPair := fun hP =>
  GlobalTheory.T.kollarTwoPointSeparation_of_nadelVanishing hP (GlobalTheory.T.nadel_vanishing_pairs_of_principalisation hP) GlobalTheory.T.nefLineBundleNumericalTheorems_proof
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.NadelVanishing.TopPointSep

section

@[expose] public section

namespace NadelVanishingSeparation.NSI

theorem pointSeparationPair : GlobalTheory.Published.PointSeparationPair :=
  GlobalTheory.pointSeparationPair_of_principalisation PositivityTheory.ResPlug.WeightsCompactStabilizer.principalisation_closed

end NadelVanishingSeparation.NSI
end
end
