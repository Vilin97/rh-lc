module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithGlobalMaximumPrincipleOffDivisorStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianRepresentativeIntegerCombinationStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentedBundleSectionsRationalFunctionsDict
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
import Mathlib.Tactic.Basify
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairSectionsMulMemNormMulStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermPairPowSectionMemAndNormPowStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratingPairSectionsNormBounds

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HSNef.GenLow

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem exists_pos_bounds {Y : Type} [TopologicalSpace Y] [CompactSpace Y] (G : Y → ℝ) (hG : Continuous G)
    (hpos : ∀ y, 0 < G y) : ∃ m U : ℝ, 0 < m ∧ 0 < U ∧ ∀ y, m ≤ G y ∧ G y ≤ U := by
  rcases isEmpty_or_nonempty Y with h | h
  · exact ⟨1, 1, one_pos, one_pos, fun y => (h.false y).elim⟩
  · obtain ⟨a, -, ha⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hG.continuousOn
    obtain ⟨b, -, hb⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hG.continuousOn
    exact ⟨G a, G b, hpos a, hpos b, fun y => ⟨ha (Set.mem_univ y), hb (Set.mem_univ y)⟩⟩

theorem nu_nonneg (P : Pair p) (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField) :
    0 ≤ P.nu a b σ y f :=
  mul_nonneg (norm_nonneg _) (Real.exp_pos _).le

theorem continuous_nu (P : Pair p) (a b : ℤ) (M : HermLB p) (hM : P.Rep a b M) (σ : k →+* ℂ)
    (f : X.functionField) (hf : f ∈ P.H a b) : Continuous fun y : CxPts p σ => P.nu a b σ y f := by
  obtain ⟨e, -, hr, hn, -⟩ := GlobalTheory.VolBr.RepDict.rep_dict k X p P a b M hM
  obtain ⟨u, rfl⟩ : f ∈ Set.range e := hr ▸ hf
  have h : (fun y : CxPts p σ => P.nu a b σ y (e u)) = fun y => Real.sqrt ((M.φ σ).nsq (secVal p σ u) y) := by
    funext y
    rw [← hn u σ y, Real.sqrt_sq (nu_nonneg P a b σ y _)]
  rw [h]
  exact ((M.cInf σ).continuous_nsq u).sqrt

theorem gen_low : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
    ∀ (P : Pair p) (c : ℕ), GenAt P c → ∃ (n : ℕ) (v : Fin n → X.functionField) (ρ : ℝ), 0 < ρ ∧
      (∀ i, v i ∈ P.Bl 0 c ρ⁻¹) ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ), ∃ i, ρ ≤ P.nu 0 c σ y (v i) := by
  intro k _ X _ p D hX P c ⟨n, v, hvH, hnz⟩
  classical
  haveI : Finite (k →+* ℂ) := hX.finite_emb
  obtain ⟨M, hM⟩ := GlobalTheory.T.exists_hermitianRepresentative_integerCombination k X p P 0 c
  have hb : ∀ σ : k →+* ℂ, ∃ m U : ℝ, 0 < m ∧ 0 < U ∧ ∀ y : CxPts p σ,
      m ≤ ∑ i, P.nu 0 c σ y (v i) ∧ ∑ i, P.nu 0 c σ y (v i) ≤ U := by
    intro σ
    haveI : CompactSpace (CxPts p σ) := hX.compactSpace σ
    refine exists_pos_bounds _ (continuous_finsetSum _ fun i _ => continuous_nu P 0 c M hM σ (v i) (hvH i))
      fun y => ?_
    obtain ⟨i, hi⟩ := hnz σ y
    exact lt_of_lt_of_le ((nu_nonneg P 0 c σ y _).lt_of_ne' hi)
      (Finset.single_le_sum (fun j _ => nu_nonneg P 0 c σ y (v j)) (Finset.mem_univ i))
  choose m U hm hU hmU using hb
  have hlow : ∃ m₀ : ℝ, 0 < m₀ ∧ ∀ σ, m₀ ≤ m σ := by
    rcases isEmpty_or_nonempty (k →+* ℂ) with h | h
    · exact ⟨1, one_pos, fun σ => (h.false σ).elim⟩
    · obtain ⟨σ, hσ⟩ := Finite.exists_min m
      exact ⟨m σ, hm σ, hσ⟩
  have hup : ∃ U₀ : ℝ, 0 < U₀ ∧ ∀ σ, U σ ≤ U₀ := by
    rcases isEmpty_or_nonempty (k →+* ℂ) with h | h
    · exact ⟨1, one_pos, fun σ => (h.false σ).elim⟩
    · obtain ⟨σ, hσ⟩ := Finite.exists_max U
      exact ⟨U σ, hU σ, hσ⟩
  obtain ⟨m₀, hm₀, hm₀le⟩ := hlow
  obtain ⟨U₀, hU₀, hU₀le⟩ := hup
  have hn1 : (0 : ℝ) < ((max n 1 : ℕ) : ℝ) := by exact_mod_cast lt_max_of_lt_right one_pos
  refine ⟨n, v, min (m₀ / (max n 1 : ℕ)) U₀⁻¹, lt_min (div_pos hm₀ hn1) (inv_pos.2 hU₀), fun i => ⟨hvH i, fun σ y => ?_⟩,
    fun σ y => ?_⟩
  · calc P.nu 0 c σ y (v i) ≤ ∑ j, P.nu 0 c σ y (v j) :=
          Finset.single_le_sum (fun j _ => nu_nonneg P 0 c σ y (v j)) (Finset.mem_univ i)
      _ ≤ U σ := (hmU σ y).2
      _ ≤ U₀ := hU₀le σ
      _ = U₀⁻¹⁻¹ := (inv_inv U₀).symm
      _ ≤ (min (m₀ / (max n 1 : ℕ)) U₀⁻¹)⁻¹ :=
          inv_anti₀ (lt_min (div_pos hm₀ hn1) (inv_pos.2 hU₀)) (min_le_right _ _)
  · obtain ⟨i₀, -⟩ := hnz σ y
    have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.2 fun h => by subst h; exact i₀.elim0
    have hmax : (max n 1 : ℕ) = n := max_eq_left hn
    have hsum : ∑ _j : Fin n, m₀ / (max n 1 : ℕ) ≤ ∑ j, P.nu 0 c σ y (v j) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hmax, mul_div_cancel₀ _
        (by exact_mod_cast (show n ≠ 0 by omega))]
      exact (hm₀le σ).trans (hmU σ y).1
    obtain ⟨i, -, hi⟩ := Finset.exists_le_of_sum_le ⟨i₀, Finset.mem_univ _⟩ hsum
    exact ⟨i, (min_le_left _ _).trans hi⟩

end GlobalTheory.HSNef.GenLow
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratingPairSectionsNormBoundsStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.generatingPairSections_norm_bounds : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (c : ℕ), GenAt P c → ∃ (n : ℕ) (v : Fin n → X.functionField) (ρ : ℝ), 0 < ρ ∧ (∀ i, v i ∈ P.Bl 0 c ρ⁻¹) ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ), ∃ i, ρ ≤ P.nu 0 c σ y (v i) := by
  first | exact @GlobalTheory.HSNef.GenLow.gen_low | exact GlobalTheory.HSNef.GenLow.gen_low | (intros; apply GlobalTheory.HSNef.GenLow.gen_low <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSectionBallOfMulSmallSectionPowTwist

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef.MpDivTwist

theorem mem_Bl_of_mul_pow_twist : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (c : ℕ), GenAt P c → ∀ s : X.functionField, s ∈ P.H 0 1 → s ≠ 0 → ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧ ∀ (N m : ℕ) (f : X.functionField), f ∈ P.H N (-c) → f * s ^ m ∈ P.Bl N (m - c) 2 → f ∈ P.Bl N (-c) (Real.exp (δ * N + C * m + C)) := by
  intro k _ X _ p D hX P c hc s hs hs0 δ hδ

  obtain ⟨n, v, ρ₁, hρ₁, hv, hcov⟩ := GlobalTheory.T.generatingPairSections_norm_bounds k X p D hX P c hc

  obtain ⟨ρ₂, hρ₂, hmax⟩ := GlobalTheory.T.arith_global_maximum_principle_off_divisor k X p D hX P s hs hs0 δ hδ
  have hnu0 : ∀ (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (g : X.functionField), 0 ≤ P.nu a b σ y g := by
    intro a b σ y g
    unfold Pair.nu
    positivity
  obtain ⟨A, hA⟩ : ∃ A : ℝ, Real.exp A = ρ₂⁻¹ := ⟨_, Real.exp_log (inv_pos.2 hρ₂)⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, Real.exp B = 2 * ρ₁⁻¹ * ρ₁⁻¹ := ⟨_, Real.exp_log (by positivity)⟩
  refine ⟨|A| + |B|, by positivity, ?_⟩
  intro N m f hf hfs
  obtain ⟨hsm, hsmnu⟩ := GlobalTheory.T.hermPair_pow_section_mem_and_norm_pow k X p P 0 1 s hs m
  obtain ⟨-, hfsnu⟩ := GlobalTheory.T.hermLineBundlePair_sections_mul_mem_norm_mul k X p P (N : ℤ) (-(c : ℤ)) ((m : ℤ) * 0) ((m : ℤ) * 1) f (s ^ m) hf hsm

  have key : ∀ (σ : k →+* ℂ) (y : CxPts p σ), ρ₂ ≤ P.nu 0 1 σ y s → P.nu N (-c) σ y f ≤ 2 * ρ₂⁻¹ ^ m := by
    intro σ y hy
    have h1 := hfsnu σ y
    rw [hsmnu σ y] at h1
    have h2 : P.nu ((N : ℤ) + (m : ℤ) * 0) (-(c : ℤ) + (m : ℤ) * 1) σ y (f * s ^ m) ≤ 2 := by
      have e1 : ((N : ℤ) + (m : ℤ) * 0) = N := by ring
      have e2 : (-(c : ℤ) + (m : ℤ) * 1) = (m : ℤ) - c := by ring
      rw [e1, e2]
      exact hfs.2 σ y
    rw [h1] at h2
    have h3 : P.nu N (-c) σ y f * ρ₂ ^ m ≤ 2 := by
      calc P.nu N (-c) σ y f * ρ₂ ^ m ≤ P.nu N (-c) σ y f * P.nu 0 1 σ y s ^ m := by
            gcongr
            exact hnu0 _ _ _ _ _
        _ ≤ 2 := h2
    calc P.nu N (-c) σ y f = P.nu N (-c) σ y f * ρ₂ ^ m * ρ₂⁻¹ ^ m := by
          rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ hρ₂.ne', one_pow, mul_one]
      _ ≤ 2 * ρ₂⁻¹ ^ m := by gcongr

  have hprod : ∀ i, ∀ (σ : k →+* ℂ) (y : CxPts p σ),
      P.nu N (-c) σ y f * P.nu 0 c σ y (v i) ≤ Real.exp (δ * N) * (2 * ρ₂⁻¹ ^ m * ρ₁⁻¹) := by
    intro i
    obtain ⟨hfv, hfvnu⟩ := GlobalTheory.T.hermLineBundlePair_sections_mul_mem_norm_mul k X p P (N : ℤ) (-(c : ℤ)) 0 (c : ℤ) f (v i) hf (hv i).1
    have e1 : ((N : ℤ) + 0) = N := by ring
    have e2 : (-(c : ℤ) + c) = 0 := by ring
    rw [e1, e2] at hfv hfvnu
    have hb := hmax N (f * v i) (2 * ρ₂⁻¹ ^ m * ρ₁⁻¹) hfv (fun σ y hy => by
      rw [hfvnu σ y]
      exact mul_le_mul (key σ y hy) ((hv i).2 σ y) (hnu0 _ _ _ _ _) (by positivity))
    intro σ y
    rw [← hfvnu σ y]
    exact hb.2 σ y
  refine ⟨hf, fun σ y => ?_⟩
  obtain ⟨i, hi⟩ := hcov σ y
  have h4 : P.nu N (-c) σ y f * ρ₁ ≤ Real.exp (δ * N) * (2 * ρ₂⁻¹ ^ m * ρ₁⁻¹) :=
    calc P.nu N (-c) σ y f * ρ₁ ≤ P.nu N (-c) σ y f * P.nu 0 c σ y (v i) := by
          gcongr
          exact hnu0 _ _ _ _ _
      _ ≤ _ := hprod i σ y
  have hAC : A ≤ |A| + |B| := by
    have := le_abs_self A
    have := abs_nonneg B
    linarith
  have hBC : B ≤ |A| + |B| := by
    have := le_abs_self B
    have := abs_nonneg A
    linarith
  calc P.nu N (-c) σ y f = P.nu N (-c) σ y f * ρ₁ * ρ₁⁻¹ := by
        rw [mul_assoc, mul_inv_cancel₀ hρ₁.ne', mul_one]
    _ ≤ Real.exp (δ * N) * (2 * ρ₂⁻¹ ^ m * ρ₁⁻¹) * ρ₁⁻¹ := by gcongr
    _ = Real.exp (δ * N) * ρ₂⁻¹ ^ m * (2 * ρ₁⁻¹ * ρ₁⁻¹) := by ring
    _ = Real.exp (δ * N) * Real.exp (m * A) * Real.exp B := by rw [Real.exp_nat_mul, hA, hB]
    _ ≤ Real.exp (δ * N) * Real.exp (m * (|A| + |B|)) * Real.exp (|A| + |B|) := by
        gcongr
    _ = Real.exp (δ * N + (|A| + |B|) * m + (|A| + |B|)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring

end GlobalTheory.HSNef.MpDivTwist
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSectionBallOfMulSmallSectionPowTwistStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.mem_sectionBall_of_mul_smallSection_pow_twist : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (c : ℕ), GenAt P c → ∀ s : X.functionField, s ∈ P.H 0 1 → s ≠ 0 → ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧ ∀ (N m : ℕ) (f : X.functionField), f ∈ P.H N (-c) → f * s ^ m ∈ P.Bl N (m - c) 2 → f ∈ P.Bl N (-c) (Real.exp (δ * N + C * m + C)) := by
  first | exact @GlobalTheory.HSNef.MpDivTwist.mem_Bl_of_mul_pow_twist | exact GlobalTheory.HSNef.MpDivTwist.mem_Bl_of_mul_pow_twist | (intros; apply GlobalTheory.HSNef.MpDivTwist.mem_Bl_of_mul_pow_twist <;> assumption)
end
end
