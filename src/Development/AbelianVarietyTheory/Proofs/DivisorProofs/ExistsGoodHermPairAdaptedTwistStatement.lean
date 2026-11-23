module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermPairPowSectionMemAndNormPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentedBundleSectionsRationalFunctionsDict
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsBaseBundlesAndTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsHermitianLineBundlePow
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.Tactic.Polynomial.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodHermitianLineBundlePair
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleArithHilbertSamuelLargeRadiusPairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsBaseBundlesAndTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShiftSecondBundleNormPairNormBallGenerationStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmallSectionAddMultipleAmpleAfterShiftStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLineBundleIsNefShiftOfNonneg
import Mathlib.Algebra.Order.Star.Real
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShiftSecondBundleNormPairNormBallGenerationStatement
import Mathlib.Algebra.Order.Star.Int

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalGenerationAmplePairMultiples

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef.AmpleGen

theorem exists_genAt_mul : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ P : Pair p, IsAmpleLB P.A.B → ∃ c₀ : ℕ, 0 < c₀ ∧ ∀ j : ℕ, GenAt P (c₀ * j) := by
  intro k _ X _ p D _ P hA
  obtain ⟨c, hc, N, s, hs⟩ := hA.exists_isGenerated_pow
  have hrep : P.Rep 0 (c : ℤ) (P.A.pow c) := by
    have := Pair.rep_pow k X p P 0 1 P.A c (Pair.rep_base k X p P).2.1
    simpa using this
  obtain ⟨e, -, hrange, hnu, -⟩ := RepDict.rep_dict k X p P 0 c (P.A.pow c) hrep
  have hmem : ∀ i, e (s i) ∈ P.H 0 c := fun i => by
    have : e (s i) ∈ Set.range e := ⟨s i, rfl⟩
    rw [hrange] at this
    exact this
  have hne : ∀ (σ : k →+* ℂ) (y : CxPts p σ), ∃ i, P.nu 0 c σ y (e (s i)) ≠ 0 := by
    intro σ y
    obtain ⟨i, hi⟩ := exists_mem_ptsIn hs y
    refine ⟨i, fun h0 => ?_⟩
    have h2 := hnu (s i) σ y
    have hpick := mem_pick ((P.A.pow c).φ σ).isLB y
    have hv := (secVal_ne_zero_iff (s i) hpick).2 hi
    have hpos : ((P.A.pow c).φ σ).nsq (secVal p σ (s i)) y ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (norm_ne_zero_iff.2 hv)) (Real.exp_pos _).ne'
    rw [h0] at h2
    exact hpos (by rw [← h2]; ring)
  refine ⟨c, hc, fun j => ⟨N, fun i => e (s i) ^ j, fun i => ?_, fun σ y => ?_⟩⟩
  · obtain ⟨h1, -⟩ := NuPow.pow_mem_H_and_nu_pow k X p P 0 c (e (s i)) (hmem i) j
    have e1 : (j : ℤ) * 0 = 0 := by ring
    have e2 : (j : ℤ) * c = ((c * j : ℕ) : ℤ) := by push_cast; ring
    rw [e1, e2] at h1
    exact h1
  · obtain ⟨i, hi⟩ := hne σ y
    obtain ⟨-, h2⟩ := NuPow.pow_mem_H_and_nu_pow k X p P 0 c (e (s i)) (hmem i) j
    have e1 : (j : ℤ) * 0 = 0 := by ring
    have e2 : (j : ℤ) * c = ((c * j : ℕ) : ℤ) := by push_cast; ring
    have h3 := h2 σ y
    rw [e1, e2] at h3
    exact ⟨i, by rw [h3]; exact pow_ne_zero _ hi⟩

end GlobalTheory.HSNef.AmpleGen
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalGenerationAmplePairMultiplesStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.exists_globalGeneration_ample_pair_multiples : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ P : Pair p, IsAmpleLB P.A.B → ∃ c₀ : ℕ, 0 < c₀ ∧ ∀ j : ℕ, GenAt P (c₀ * j) := by
  first | exact @GlobalTheory.HSNef.AmpleGen.exists_genAt_mul | exact GlobalTheory.HSNef.AmpleGen.exists_genAt_mul | (intros; apply GlobalTheory.HSNef.AmpleGen.exists_genAt_mul <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsShiftSmallSectionCountRegimeFromRadiusOne

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem regime_shiftA : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ P : Pair p, IsAmpleLB P.A.B → P.A.SemiPos D → ∃ u₀ : ℝ, ∀ u, u₀ ≤ u → Regime (shiftA P u) D := by
  intro hA hHS k _ X _ p D hX P hamp hsemi
  obtain ⟨Φ, hΦ⟩ := ((hA.arExists k X p D hX).2 PUnit fun _ => P.A).1
  have hα := ((hA.arIso k X p D hX).2 PUnit _ Φ hΦ).1 PUnit.unit
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.T.ampleArithHilbertSamuel_largeRadius_pair hHS k X p D hX P 0 1 0 0 P.A _ (Pair.rep_base k X p P).2.1 hamp hsemi hα
  refine ⟨t₀, fun u hu => ⟨Φ (MvPolynomial.X PUnit.unit ^ (D + 1)) / (D + 1).factorial + ((D : ℝ) + 1) * gdeg P.A D / (D + 1).factorial * u, ((D : ℝ) + 1) * gdeg P.A D / (D + 1).factorial, fun t ht => ?_⟩⟩
  have h := ht₀ (t + u) (by linarith)
  have e : ∀ m : ℕ, (shiftA P u).lc 0 m (Real.exp (t * m)) =
      P.lc ((m : ℤ) * 0 + 0) ((m : ℤ) * 1 + 0) (Real.exp ((t + u) * m)) := by
    intro m
    simp only [Pair.lc, (GlobalTheory.T.shiftSecondBundleNormPair_norm_ball_generation k X p P u).2.1, mul_zero, add_zero, mul_one, ← Real.exp_add]
    congr 4
    push_cast
    ring_nf
  have hfun : (fun m : ℕ => (shiftA P u).lc 0 m (Real.exp (t * m)) / (m : ℝ) ^ (D + 1)) =
      fun m : ℕ => P.lc ((m : ℤ) * 0 + 0) ((m : ℤ) * 1 + 0) (Real.exp ((t + u) * m)) / (m : ℝ) ^ (D + 1) :=
    funext fun m => by rw [e]
  rw [hfun]
  convert h using 2
  ring

end GlobalTheory.HSNef
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsShiftSmallSectionCountRegimeFromRadiusOneStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.exists_shift_smallSectionCount_regime_from_radius_one : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ P : Pair p, IsAmpleLB P.A.B → P.A.SemiPos D → ∃ u₀ : ℝ, ∀ u, u₀ ≤ u → Regime (shiftA P u) D := by
  first | exact @GlobalTheory.HSNef.regime_shiftA | exact GlobalTheory.HSNef.regime_shiftA | (intros; apply GlobalTheory.HSNef.regime_shiftA <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermPairSectionsGoodShiftSecondBundleNormPair

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem nu_shiftA {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} (P : Pair p) (u : ℝ)
    (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField) :
    (shiftA P u).nu a b σ y f = P.nu a b σ y f * Real.exp (-(b * u)) := by
  change ‖ratVal (P.loc a b f (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y)) y‖ *
      Real.exp (-(a * (P.L.φ σ).φ (pick (P.L.φ σ).isLB y) y +
        b * ((P.A.φ σ).φ (pick (P.A.φ σ).isLB y) y + 2 * u)) / 2) = _
  rw [Pair.nu, mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem Bl_subset_shiftA {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} (P : Pair p) {u : ℝ}
    (hu : 0 ≤ u) (a b : ℤ) (hb : 0 ≤ b) {R : ℝ} {f : X.functionField} (hf : f ∈ P.Bl a b R) :
    f ∈ (shiftA P u).Bl a b R := by
  refine ⟨hf.1, fun σ y => ?_⟩
  rw [nu_shiftA]
  have h1 : Real.exp (-(b * u)) ≤ 1 := Real.exp_le_one_iff.2 (by
    have : (0 : ℝ) ≤ b := by exact_mod_cast hb
    nlinarith)
  have h0 : 0 ≤ P.nu a b σ y f := by unfold Pair.nu; positivity
  have h2 : R ≥ P.nu a b σ y f := hf.2 σ y
  nlinarith [Real.exp_pos (-(b * u))]

theorem good_shiftA : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
    ∀ (P : Pair p) (b : ℕ) (s t : X.functionField) (u : ℝ), 0 ≤ u → P.Good D b s t → (shiftA P u).Good D b s t := by
  intro k _ X _ p D hX P b s t u hu h
  exact
    { ample := h.ample
      nef := GlobalTheory.NefShift.isNef_shift_nonneg k X p D hX P.A u hu h.nef
      pos := h.pos
      s_mem := Bl_subset_shiftA P hu 0 1 zero_le_one h.s_mem
      s_ne := h.s_ne
      t_mem := Bl_subset_shiftA P hu (-1) b (Int.natCast_nonneg b) h.t_mem
      t_ne := h.t_ne
      reg := h.reg }

end GlobalTheory.HSNef
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermPairSectionsGoodShiftSecondBundleNormPairStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.hermPairSections_good_shiftSecondBundleNormPair : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (b : ℕ) (s t : X.functionField) (u : ℝ), 0 ≤ u → P.Good D b s t → (shiftA P u).Good D b s t := by
  first | exact @GlobalTheory.HSNef.good_shiftA | exact GlobalTheory.HSNef.good_shiftA | (intros; apply GlobalTheory.HSNef.good_shiftA <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodHermPairAdaptedTwist

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem exists_good_pair_twist : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ L N : HermLB p, ∃ (P : Pair p) (b : ℕ) (s t : X.functionField) (c : ℕ),
    P.L = L ∧ P.Good D b s t ∧ GenAt P c ∧ Regime P D ∧ Le ((P.A.pow c).dual) N := by
  intro hAC hHS k _ X _ p D hX L N
  obtain ⟨P₀, b, s, t, hL, hG⟩ := GlobalTheory.VolBr.exists_good_pair hAC k X p D hX L
  obtain ⟨c₀, hc₀, hgen⟩ := GlobalTheory.T.exists_globalGeneration_ample_pair_multiples k X p D hX P₀ hG.ample
  obtain ⟨c₁, hc₁⟩ := GlobalTheory.T.exists_small_section_add_multiple_ample_after_shift k X p D hX P₀ N s hG.ample hG.s_mem.1 hG.s_ne
  have hc : c₁ ≤ c₀ * (c₁ + 1) := by nlinarith
  have hcpos : 0 < c₀ * (c₁ + 1) := Nat.mul_pos hc₀ (Nat.succ_pos _)
  obtain ⟨u₁, hu₁⟩ := hc₁ (c₀ * (c₁ + 1)) hc hcpos
  obtain ⟨u₂, hu₂⟩ := GlobalTheory.T.exists_shift_smallSectionCount_regime_from_radius_one hAC hHS k X p D hX P₀ hG.ample hG.nef.semiPos
  refine ⟨shiftA P₀ (max 0 (max u₁ u₂)), b, s, t, c₀ * (c₁ + 1), hL, ?_, ?_, ?_, ?_⟩
  · exact GlobalTheory.T.hermPairSections_good_shiftSecondBundleNormPair k X p D hX P₀ b s t _ (le_max_left _ _) hG
  · exact (GlobalTheory.T.shiftSecondBundleNormPair_norm_ball_generation k X p P₀ _).2.2 _ (hgen (c₁ + 1))
  · exact hu₂ _ (le_trans (le_max_right _ _) (le_max_right _ _))
  · exact hu₁ _ (le_trans (le_max_left _ _) (le_max_right _ _))

end GlobalTheory.HSNef
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodHermPairAdaptedTwistStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.exists_goodHermPair_adapted_twist : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ L N : HermLB p, ∃ (P : Pair p) (b : ℕ) (s t : X.functionField) (c : ℕ), P.L = L ∧ P.Good D b s t ∧ GenAt P c ∧ Regime P D ∧ Le ((P.A.pow c).dual) N := by
  first | exact @GlobalTheory.HSNef.exists_good_pair_twist | exact GlobalTheory.HSNef.exists_good_pair_twist | (intros; apply GlobalTheory.HSNef.exists_good_pair_twist <;> assumption)
end
end
