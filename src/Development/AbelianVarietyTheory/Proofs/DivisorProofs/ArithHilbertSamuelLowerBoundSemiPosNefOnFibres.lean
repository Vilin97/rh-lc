module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairSectionsMulMemNormMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsBaseBundlesAndTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionsTwistedPowerEncardEqBall
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodHermPairAdaptedTwistStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSmallSecHermitianLineBundleArithVarietyStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLBLeBySmallSectionTensorIsometricTransShiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermPairWithSectionsRepresentsTensor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsBaseBundlesAndTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsHermitianLineBundleDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsHermitianLineBundlePow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermPairWithSectionsRepresentsTensor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedModelDominantCurveRestriction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleTensorOfNefFibresAmpleStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCountRadiusOneLowerBoundAmpleSemiPosStatement
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.SpecificLimits.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemipositiveNonnegCombination
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Tactic.Polynomial.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionCountLogTwistContinuityAbove
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoSelfIntersectionPowTensorDivPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionsTwistedPowerEncardEqBall

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EncardSmallSectionsLeOfHermLBLeBySmallSection

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef.LeCard

theorem encard_smallSec_le : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k),
    ∀ A B : HermLB p, Le B A → B.smallSec.encard ≤ A.smallSec.encard := by
  intro k _ X _ p A B hBA
  obtain ⟨P, rfl, rfl, h1⟩ := hBA
  have hrep := Pair.rep_base k X p P
  have eL : P.L.smallSec.encard = (P.Bl 1 0 1).encard :=
    SmallBall.encard_eq_Bl P hrep.1 P.L.smallSec 1 zero_le_one fun u => by
      simp only [HermLB.smallSec, Set.mem_setOf_eq, one_pow]
  have eA : P.A.smallSec.encard = (P.Bl 0 1 1).encard :=
    SmallBall.encard_eq_Bl P hrep.2.1 P.A.smallSec 1 zero_le_one fun u => by
      simp only [HermLB.smallSec, Set.mem_setOf_eq, one_pow]
  rw [eL, eA]
  refine Set.encard_le_encard fun f hf => ?_
  have e := NuMul.mul_mem_H_and_nu_mul k X p P 1 (-1) 0 1 1 f h1.1 hf.1
  rw [one_mul, add_zero, neg_add_cancel] at e
  refine ⟨e.1, fun σ y => ?_⟩
  rw [e.2 σ y]
  calc P.nu 1 (-1) σ y 1 * P.nu 0 1 σ y f ≤ 1 * 1 :=
        mul_le_mul (h1.2 σ y) (hf.2 σ y) (SmallBall.nu_nonneg P 0 1 σ y f) zero_le_one
    _ = 1 := one_mul 1

end GlobalTheory.HSNef.LeCard
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EncardSmallSectionsLeOfHermLBLeBySmallSectionStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.encard_smallSections_le_of_hermLBLeBySmallSection : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ A B : HermLB p, Le B A → B.smallSec.encard ≤ A.smallSec.encard := by
  first | exact @GlobalTheory.HSNef.LeCard.encard_smallSec_le | exact GlobalTheory.HSNef.LeCard.encard_smallSec_le | (intros; apply GlobalTheory.HSNef.LeCard.encard_smallSec_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerBoundAlongResidues

section

@[expose] public section

open Filter Topology

namespace GlobalTheory

theorem lowerBound_along_residues : ∀ (d n : ℕ) (u : ℕ → ℝ) (γ : ℝ), 0 < n → (∀ r < n, ∀ ε : ℝ, 0 < ε → ∀ᶠ q : ℕ in atTop, (γ - ε) * (q : ℝ) ^ d ≤ u (n * q + r)) → ∀ ε : ℝ, 0 < ε → ∀ᶠ M : ℕ in atTop, (γ / (n : ℝ) ^ d - ε) * (M : ℝ) ^ d ≤ u M := by
  intro d n u γ hn h ε hε
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hnd : (0:ℝ) < (n:ℝ)^d := pow_pos hnR d
  set ε' := ε * (n:ℝ)^d / 2 with hε'
  have hε'pos : 0 < ε' := by positivity
  have h1 : ∀ᶠ q : ℕ in atTop, ∀ r ∈ Set.Iio n, (γ - ε') * (q:ℝ)^d ≤ u (n*q + r) :=
    (Filter.eventually_all_finite (Set.finite_Iio n)).2 (fun r hr => h r hr ε' hε'pos)
  have h2 : ∀ᶠ M : ℕ in atTop, ∀ r ∈ Set.Iio n, (γ - ε') * ((M / n : ℕ):ℝ)^d ≤ u (n*(M/n) + r) :=
    (Nat.tendsto_div_const_atTop hn.ne').eventually h1
  have hf : Tendsto (fun M : ℕ => ((M / n : ℕ):ℝ) / M) atTop (𝓝 (1 / n)) := by
    have hlow : Tendsto (fun M : ℕ => 1 / (n:ℝ) - 1 / (M:ℝ)) atTop (𝓝 (1 / n)) := by
      simpa using (tendsto_const_nhds (x := 1/(n:ℝ))).sub tendsto_one_div_atTop_nhds_zero_nat
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with M hM
      have hMR : (0:ℝ) < M := Nat.cast_pos.mpr hM
      have key : (n:ℝ) * ((M/n : ℕ):ℝ) + ((M % n : ℕ):ℝ) = M := by exact_mod_cast Nat.div_add_mod M n
      have hmod : ((M % n : ℕ):ℝ) < n := by exact_mod_cast Nat.mod_lt M hn
      have hq : (M:ℝ) - n ≤ n * ((M/n : ℕ):ℝ) := by linarith
      rw [div_sub_div _ _ hnR.ne' hMR.ne', div_le_div_iff₀ (by positivity) hMR]
      nlinarith [mul_le_mul_of_nonneg_right hq hMR.le]
    · filter_upwards [eventually_gt_atTop 0] with M hM
      have hMR : (0:ℝ) < M := Nat.cast_pos.mpr hM
      rw [div_le_div_iff₀ hMR hnR]
      have h0 : ((M / n : ℕ):ℝ) ≤ (M:ℝ) / n := Nat.cast_div_le
      rw [le_div_iff₀ hnR] at h0
      linarith
  have hg : Tendsto (fun M : ℕ => (γ - ε') * (((M / n : ℕ):ℝ) / M)^d) atTop (𝓝 ((γ - ε') * (1/(n:ℝ))^d)) :=
    (hf.pow d).const_mul _
  have hlim : (γ - ε') * (1/(n:ℝ))^d = γ / (n:ℝ)^d - ε/2 := by
    rw [one_div_pow, hε']; field_simp
  have h3 : ∀ᶠ M : ℕ in atTop, γ / (n:ℝ)^d - ε < (γ - ε') * (((M / n : ℕ):ℝ) / M)^d := by
    rw [hlim] at hg
    exact hg.eventually (lt_mem_nhds (by linarith))
  filter_upwards [h2, h3, eventually_gt_atTop 0] with M hM2 hM3 hM
  have hMR : (0:ℝ) < M := Nat.cast_pos.mpr hM
  have hMd : (0:ℝ) < (M:ℝ)^d := pow_pos hMR d
  have e1 := hM2 (M % n) (Nat.mod_lt M hn)
  rw [Nat.div_add_mod] at e1
  rw [div_pow, ← mul_div_assoc, lt_div_iff₀ hMd] at hM3
  linarith

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHilbertSamuelLowerBoundNefPlusAmple

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem lowerBound_along_div : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (c n : ℕ) (α : ℝ), 0 < n → NefFib P.L → P.L.SemiPos D → IsAmpleLB P.A.B → P.A.SemiPos D → ((P.L.pow n).tens P.A).IsSelfInter α → ∀ ε : ℝ, 0 < ε → ∀ᶠ M : ℕ in atTop, (α / (D + 1).factorial / (n : ℝ) ^ (D + 1) - ε) * (M : ℝ) ^ (D + 1) ≤ P.lc M ((M / n : ℕ) - c) 1 := by
  intro _ hHS k _ X _ p D hX P c n α hn hL hLs hA hAs hα ε hε
  have : Module.Finite ℤ k := hX.finite
  have hp : IsProjOver p := hX.isProjOver
  have hLn : NefFib (P.L.pow n) := fun Z i _ _ κ _ _ _ hd => by
    rw [NefHodgeTateAt.topSelf_pow hp P.L n Z i κ hd]
    exact mul_nonneg (Nat.cast_nonneg _) (hL Z i κ hd)
  have hAmp : IsAmpleLB ((P.L.pow n).tens P.A).B := GlobalTheory.T.isAmple_tensor_of_nef_fibres_ample k X p D hX _ _ hLn hA
  have hSP : ((P.L.pow n).tens P.A).SemiPos D := (hLs.pow n).tens hAs
  have hRep : P.Rep (n : ℤ) 1 ((P.L.pow n).tens P.A) := by
    have h1 := Pair.rep_pow k X p P 1 0 P.L n (Pair.rep_base k X p P).1
    have h2 := Pair.rep_tens k X p P _ _ 0 1 _ _ h1 (Pair.rep_base k X p P).2.1
    simpa using h2
  refine lowerBound_along_residues (D + 1) n (fun M => P.lc M ((M / n : ℕ) - c) 1) (α / (D + 1).factorial) hn
    (fun r hr ε' hε' => ?_) ε hε
  filter_upwards [GlobalTheory.T.log_count_radius_one_lower_bound_ample_semiPos hHS k X p D hX P n 1 r (-(c : ℤ)) _ α hRep hAmp hSP hα ε' hε'] with q hq
  have e : (n * q + r) / n = q := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt hr, zero_add]
  simp only [e]
  convert hq using 2 <;> push_cast <;> ring

end GlobalTheory.HSNef
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionCountLogTwistContinuityAboveStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.smallSectionCount_log_twist_continuity_above : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (b : ℕ) (s t : X.functionField), P.Good D b s t → ∀ c : ℕ, GenAt P c → Regime P D → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ᶠ M : ℕ in atTop, P.lc M ((M / n : ℕ) - c) 1 ≤ P.lc M (-c) 1 + ε * (M : ℝ) ^ (D + 1) := by
  first | exact @GlobalTheory.HSNef.lc_add_div_sub_le | exact GlobalTheory.HSNef.lc_add_div_sub_le | (intros; apply GlobalTheory.HSNef.lc_add_div_sub_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionsLowerBoundAmpleMinusTwist

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSLowerTwist

theorem main : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (b : ℕ) (s t : X.functionField), P.Good D b s t → ∀ c : ℕ, GenAt P c → Regime P D → NefFib P.L → P.L.SemiPos D → ∀ a : ℝ, P.L.IsSelfInter a → ∀ ε : ℝ, 0 < ε → ∀ᶠ M : ℕ in atTop, (a / (D + 1).factorial - ε) * (M : ℝ) ^ (D + 1) ≤ P.lc M (-c) 1 := by
  intro hC hHS k _ X _ p D hX P b s t hG c hgen hreg hnef hsemi a ha ε hε
  obtain ⟨α, hα, hlim⟩ := GlobalTheory.SelfInterGrowth.main hC k X p D hX P.L P.A a ha
  have hε3 : 0 < ε / 3 := by positivity
  have h1 := GlobalTheory.T.smallSectionCount_log_twist_continuity_above k X p D hX P b s t hG c hgen hreg (ε / 3) hε3
  have h2 : ∀ᶠ n : ℕ in atTop, a / ((D + 1).factorial : ℝ) - ε / 3 <
      α n / (n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ) :=
    (hlim.div_const ((D + 1).factorial : ℝ)).eventually (lt_mem_nhds (by linarith))
  obtain ⟨n, ⟨hn1, hn2⟩, hn0⟩ := ((h1.and h2).and (eventually_gt_atTop 0)).exists
  have h3 := GlobalTheory.HSNef.lowerBound_along_div hC hHS k X p D hX P c n (α n) hn0 hnef hsemi hG.ample hG.nef.semiPos (hα n) (ε / 3) hε3
  filter_upwards [hn1, h3] with M hM1 hM3
  have hM : (0 : ℝ) ≤ (M : ℝ) ^ (D + 1) := by positivity
  rw [div_right_comm] at hM3
  have h4 := mul_le_mul_of_nonneg_right hn2.le hM
  nlinarith

end GlobalTheory.HSLowerTwist
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionsLowerBoundAmpleMinusTwistStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.smallSections_lowerBound_ample_minus_twist : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (b : ℕ) (s t : X.functionField), P.Good D b s t → ∀ c : ℕ, GenAt P c → Regime P D → NefFib P.L → P.L.SemiPos D → ∀ a : ℝ, P.L.IsSelfInter a → ∀ ε : ℝ, 0 < ε → ∀ᶠ M : ℕ in atTop, (a / (D + 1).factorial - ε) * (M : ℝ) ^ (D + 1) ≤ P.lc M (-c) 1 := by
  first | exact @GlobalTheory.HSLowerTwist.main | exact GlobalTheory.HSLowerTwist.main | (intros; apply GlobalTheory.HSLowerTwist.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHilbertSamuelLowerBoundSemiPosNefOnFibres

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef.LowerNef

theorem main : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L N : HermLB p) (a : ℝ), NefFib L → L.SemiPos D → L.IsSelfInter a → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, (a / (D + 1).factorial - ε) * (m : ℝ) ^ (D + 1) ≤ Real.log (((L.pow m).tens N).smallSec.ncard : ℝ) := by
  intro hAr hHS k _ X _ p D hX L N a hNef hSP hSI ε hε
  obtain ⟨P, b, s, t, c, hPL, hG, hGen, hReg, hLe⟩ := GlobalTheory.T.exists_goodHermPair_adapted_twist hAr hHS k X p D hX L N
  subst hPL
  have hlow := GlobalTheory.T.smallSections_lowerBound_ample_minus_twist hAr hHS k X p D hX P b s t hG c hGen hReg hNef hSP a hSI ε hε
  filter_upwards [hlow] with m hm
  obtain ⟨h1, h2, -⟩ := Pair.rep_base k X p P
  have hRep : P.Rep (m : ℤ) (-(c : ℤ)) ((P.L.pow m).tens ((P.A.pow c).dual)) := by
    have := Pair.rep_tens k X p P _ _ _ _ _ _ (Pair.rep_pow k X p P _ _ _ m h1)
      (Pair.rep_dual k X p P _ _ _ (Pair.rep_pow k X p P _ _ _ c h2))
    simpa using this
  have hE := SmallBall.encard_eq_Bl P hRep ((P.L.pow m).tens ((P.A.pow c).dual)).smallSec 1 zero_le_one fun u => by
    simp only [HermLB.smallSec, Set.mem_setOf_eq, one_pow]
  have hle := GlobalTheory.T.encard_smallSections_le_of_hermLBLeBySmallSection k X p _ _ ((GlobalTheory.T.hermLBLeBySmallSection_tensor_isometric_trans_shift k X p _ _ (P.L.pow m)).1 hLe)
  have hfin := GlobalTheory.T.finite_smallSec_hermitian_line_bundle_arith_variety k X p D hX ((P.L.pow m).tens N)
  have hBle : (P.Bl m (-c) 1).encard ≤ ((P.L.pow m).tens N).smallSec.encard := hE ▸ hle
  have hBfin : (P.Bl m (-c) 1).Finite :=
    Set.finite_of_encard_le_coe (hBle.trans_eq hfin.cast_ncard_eq.symm)
  have hone : (1 : ℕ∞) ≤ (P.Bl m (-c) 1).encard :=
    hE ▸ Set.one_le_encard_iff_nonempty.2 ⟨_, ((P.L.pow m).tens ((P.A.pow c).dual)).zero_mem_smallSec⟩
  have hc1 : 1 ≤ (P.Bl m (-c) 1).ncard := by
    have := hBfin.cast_ncard_eq ▸ hone
    exact_mod_cast this
  have hc2 : (P.Bl m (-c) 1).ncard ≤ ((P.L.pow m).tens N).smallSec.ncard := by
    have := hBfin.cast_ncard_eq ▸ hfin.cast_ncard_eq ▸ hBle
    exact_mod_cast this
  refine hm.trans ?_
  unfold Pair.lc
  exact Real.log_le_log (by exact_mod_cast hc1) (by exact_mod_cast hc2)

end GlobalTheory.HSNef.LowerNef
end
end
end
