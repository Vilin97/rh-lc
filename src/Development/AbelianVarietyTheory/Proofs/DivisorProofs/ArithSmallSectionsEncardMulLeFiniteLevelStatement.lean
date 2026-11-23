module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivMemOfMulPowDivMemOfRegularPair
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
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EncardMulLeOfQuotEmbed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairSectionsMulMemNormMulStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermPairPowSectionMemAndNormPowStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSeminormBallFamilySectionBallsStatement
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivPowMemSectionsOfMulPowMem

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory.VolBr

theorem Pair.div_pow_mem_H_of_mul_pow : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (P : Pair p), ∀ (b : ℕ) (s t : X.functionField), P.Good D b s t → ∀ (N m : ℕ)
    (u : X.functionField), u ∈ P.H N m → u * t ^ N / s ^ m ∈ P.H 0 (b * N) → u / s ^ m ∈ P.H N 0 := by
  intro k _ X _ p D _ P b s t hG N m u hu hut x i j hi hj
  let O : Subring X.functionField := (algebraMap (X.presheaf.stalk x) X.functionField).range
  have hO : ∀ f, RegAt x f ↔ f ∈ O := fun f => Iff.rfl
  have hri : (P.r i : X.functionField) ≠ 0 := (P.r i).ne_zero
  have hrj : (P.r' j : X.functionField) ≠ 0 := (P.r' j).ne_zero
  have hs : P.loc 0 1 s i j ∈ O := (hO _).1 (hG.s_mem.1 x i j hi hj)
  have ht : P.loc (-1) b t i j ∈ O := (hO _).1 (hG.t_mem.1 x i j hi hj)
  have hs0 : P.loc 0 1 s i j ≠ 0 := by
    simp only [loc, zpow_zero, zpow_one, mul_one]
    exact mul_ne_zero hG.s_ne hrj
  have hreg : ∀ g ∈ O, g * P.loc (-1) b t i j / P.loc 0 1 s i j ∈ O → g / P.loc 0 1 s i j ∈ O :=
    fun g hg h => (hO _).1 (hG.reg x i j hi hj g ((hO _).2 hg) ((hO _).2 h))
  have hg : P.loc N m u i j ∈ O := (hO _).1 (hu x i j hi hj)
  have e1 : P.loc N m u i j * P.loc (-1) b t i j ^ N / P.loc 0 1 s i j ^ m =
      P.loc 0 ((b * N : ℕ) : ℤ) (u * t ^ N / s ^ m) i j := by
    simp only [loc, zpow_zero, zpow_one, mul_one, zpow_natCast, zpow_neg, mul_pow, inv_pow]
    push_cast
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast]
    simp only [zpow_natCast]
    field_simp
    ring
  have e2 : P.loc N m u i j / P.loc 0 1 s i j ^ m = P.loc N 0 (u / s ^ m) i j := by
    simp only [loc, zpow_zero, zpow_one, mul_one, zpow_natCast, mul_pow]
    field_simp
  have hgN : P.loc N m u i j * P.loc (-1) b t i j ^ N / P.loc 0 1 s i j ^ m ∈ O := by
    rw [e1]
    have := hut x i j hi hj
    push_cast at this ⊢
    exact (hO _).1 this
  have := regularPair_pow X.functionField O _ _ hs ht hs0 hreg m N _ hg hgN
  rw [e2] at this
  exact (hO _).2 (by exact_mod_cast this)

end GlobalTheory.VolBr
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivPowMemSectionsOfMulPowMemStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

theorem _root_.GlobalTheory.T.div_pow_mem_sections_of_mul_pow_mem : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (b : ℕ) (s t : X.functionField), P.Good D b s t → ∀ (N m : ℕ) (u : X.functionField), u ∈ P.H N m → u * t ^ N / s ^ m ∈ P.H 0 (b * N) → u / s ^ m ∈ P.H N 0 := by
  first | exact @GlobalTheory.VolBr.Pair.div_pow_mem_H_of_mul_pow | exact GlobalTheory.VolBr.Pair.div_pow_mem_H_of_mul_pow | (intros; apply GlobalTheory.VolBr.Pair.div_pow_mem_H_of_mul_pow <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithSmallSectionsEncardMulLeFiniteLevel

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false

namespace GlobalTheory.VolBr

theorem encard_mul_le_at_level : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (P : Pair p), ∀ (b : ℕ) (s t : X.functionField), P.Good D b s t → ∀ (N m : ℕ),
    (P.Bl N m 1).Finite → (P.Bl N m 1).encard * (P.Bl 0 (b * N) 1).encard ≤
      {f | f ∈ P.H N 0 ∧ f * s ^ m ∈ P.Bl N m 2}.encard * (P.Bl 0 (b * N + m) 2).encard := by
  intro k _ X _ p D hX P b s t hg N m hfin

  have hnu : ∀ (a c : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField), 0 ≤ P.nu a c σ y f := by
    intro a c σ y f
    unfold Pair.nu
    positivity
  have hs0 : s ^ m ≠ 0 := pow_ne_zero _ hg.s_ne

  obtain ⟨hsH, hsnu⟩ := GlobalTheory.T.hermPair_pow_section_mem_and_norm_pow k X p P 0 1 s hg.s_mem.1 m
  obtain ⟨htH, htnu⟩ := GlobalTheory.T.hermPair_pow_section_mem_and_norm_pow k X p P (-1) b t hg.t_mem.1 N
  have hsle : ∀ (σ : k →+* ℂ) (y : CxPts p σ), P.nu (↑m * 0) (↑m * 1) σ y (s ^ m) ≤ 1 := by
    intro σ y
    rw [hsnu]
    exact pow_le_one₀ (hnu _ _ _ _ _) (hg.s_mem.2 σ y)
  have htle : ∀ (σ : k →+* ℂ) (y : CxPts p σ), P.nu (↑N * (-1)) (↑N * ↑b) σ y (t ^ N) ≤ 1 := by
    intro σ y
    rw [htnu]
    exact pow_le_one₀ (hnu _ _ _ _ _) (hg.t_mem.2 σ y)

  let Λ₀ : AddSubgroup X.functionField := (P.H N 0).comap (AddMonoidHom.mulRight (s ^ m)⁻¹)
  let Λ₀' : AddSubgroup X.functionField := (P.H 0 (b * N)).comap (AddMonoidHom.mulRight (s ^ m)⁻¹)
  have key := GlobalTheory.VolBr.encard_mul_le_of_quot_embed X.functionField (P.H N m) (P.H 0 (b * N + m)) Λ₀ Λ₀'
    (P.Bl N m) (P.Bl 0 (b * N + m)) (AddMonoidHom.mulRight (t ^ N))
    (GlobalTheory.T.isSeminormBallFamily_sectionBalls k X p P N m) (GlobalTheory.T.isSeminormBallFamily_sectionBalls k X p P 0 (b * N + m)) ?_ ?_ hfin
  rotate_left
  ·
    intro u hu
    obtain ⟨hH, hn⟩ := GlobalTheory.T.hermLineBundlePair_sections_mul_mem_norm_mul k X p P N m (↑N * (-1)) (↑N * ↑b) u (t ^ N) hu.1 htH
    have e1 : (N : ℤ) + ↑N * (-1) = 0 := by ring
    have e2 : (m : ℤ) + ↑N * ↑b = ↑b * ↑N + ↑m := by ring
    rw [e1, e2] at hH hn
    refine ⟨hH, fun σ y => ?_⟩
    simp only [AddMonoidHom.coe_mulRight]
    rw [hn]
    exact mul_le_one₀ (hu.2 σ y) (hnu _ _ _ _ _) (htle σ y)
  ·
    intro u hu hT
    simp only [Λ₀, Λ₀', AddSubgroup.mem_comap, AddMonoidHom.coe_mulRight] at hT ⊢
    rw [← div_eq_mul_inv] at hT ⊢
    exact GlobalTheory.T.div_pow_mem_sections_of_mul_pow_mem k X p D hX P b s t hg N m u hu hT

  have hE : (P.Bl 0 (b * N) 1).encard ≤ (P.Bl 0 (b * N + m) 1 ∩ (Λ₀' : Set X.functionField)).encard := by
    rw [← (mul_left_injective₀ hs0).injOn.encard_image]
    apply Set.encard_le_encard
    rintro _ ⟨g, hg', rfl⟩
    obtain ⟨hH, hn⟩ := GlobalTheory.T.hermLineBundlePair_sections_mul_mem_norm_mul k X p P 0 (↑b * ↑N) (↑m * 0) (↑m * 1) g (s ^ m) hg'.1 hsH
    have e1 : (0 : ℤ) + ↑m * 0 = 0 := by ring
    have e2 : (↑b * ↑N : ℤ) + ↑m * 1 = ↑b * ↑N + ↑m := by ring
    rw [e1, e2] at hH hn
    refine ⟨⟨hH, fun σ y => ?_⟩, ?_⟩
    · rw [hn]
      exact mul_le_one₀ (hg'.2 σ y) (hnu _ _ _ _ _) (hsle σ y)
    · show g * s ^ m * (s ^ m)⁻¹ ∈ P.H 0 (↑b * ↑N)
      rw [mul_inv_cancel_right₀ hs0]
      exact hg'.1

  have hB : (P.Bl N m 2 ∩ (Λ₀ : Set X.functionField)) =
      (fun f => f * s ^ m) '' {f | f ∈ P.H N 0 ∧ f * s ^ m ∈ P.Bl N m 2} := by
    ext u
    constructor
    · rintro ⟨hu, hu0⟩
      refine ⟨u * (s ^ m)⁻¹, ⟨hu0, ?_⟩, ?_⟩
      · rw [inv_mul_cancel_right₀ hs0]
        exact hu
      · exact inv_mul_cancel_right₀ hs0 u
    · rintro ⟨f, ⟨hf, hfs⟩, rfl⟩
      refine ⟨hfs, ?_⟩
      show f * s ^ m * (s ^ m)⁻¹ ∈ P.H N 0
      rw [mul_inv_cancel_right₀ hs0]
      exact hf
  rw [hB, (mul_left_injective₀ hs0).injOn.encard_image] at key
  refine le_trans ?_ key
  gcongr

end GlobalTheory.VolBr
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithSmallSectionsEncardMulLeFiniteLevelStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

theorem _root_.GlobalTheory.T.arith_small_sections_encard_mul_le_finite_level : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (b : ℕ) (s t : X.functionField), P.Good D b s t → ∀ (N m : ℕ), (P.Bl N m 1).Finite → (P.Bl N m 1).encard * (P.Bl 0 (b * N) 1).encard ≤ {f | f ∈ P.H N 0 ∧ f * s ^ m ∈ P.Bl N m 2}.encard * (P.Bl 0 (b * N + m) 2).encard := by
  first | exact @GlobalTheory.VolBr.encard_mul_le_at_level | exact GlobalTheory.VolBr.encard_mul_le_at_level | (intros; apply GlobalTheory.VolBr.encard_mul_le_at_level <;> assumption)
end
end
