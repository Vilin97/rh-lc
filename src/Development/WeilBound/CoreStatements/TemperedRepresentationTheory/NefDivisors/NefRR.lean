module

public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.NefRR
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartLatticeDimensionUpperStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartLatticeLeSpanNormStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartLatticeSpanTwistShiftStatement
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsKodairaGeneric
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalChartLattice
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
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinrankLeAddOfMem
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.Topology.Order.Basic
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsKleimanScheme
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSuppAA
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.PCoordCurveAlgebraic
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionsDimZero
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSaturatedFirstCoordinateLine
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel
import Mathlib.Tactic.Linter.Style
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalChartLatticeStatement

section

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel Filter Topology

theorem _root_.GlobalTheory.T.finiteDimensional_chart_lattice : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (b : K → ℤ), IsArithVar (mCoordIdeal y) (D + 1) → FiniteDimensional ℚ (chartLatQ y b 1) := by
  first | exact @GlobalTheory.CompanionTheory.GenericFibre.finiteDimensional_chartLatQ | exact GlobalTheory.CompanionTheory.GenericFibre.finiteDimensional_chartLatQ | (intros; apply GlobalTheory.CompanionTheory.GenericFibre.finiteDimensional_chartLatQ <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TendstoOfAsymptoticBounds

section

@[expose] public section

open Filter Topology

namespace GlobalTheory.CompanionTheory.Analysis

theorem tendsto_factorial_mul_div_pow_of_eps_bounds (f : ℕ → ℝ) (G : ℝ) (D : ℕ)
    (hl : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, (G - ε) * (n : ℝ) ^ D / (D.factorial : ℝ) ≤ f n)
    (hu : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, f n ≤ (G + ε) * (n : ℝ) ^ D / (D.factorial : ℝ)) :
    Tendsto (fun n : ℕ => (D.factorial : ℝ) * f n / (n : ℝ) ^ D) atTop (𝓝 G) := by
  have hfac : (0 : ℝ) < (D.factorial : ℝ) := by exact_mod_cast D.factorial_pos
  have hev : ∀ᶠ n : ℕ in atTop, (0 : ℝ) < (n : ℝ) ^ D := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    positivity
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · filter_upwards [hl ((G - a) / 2) (by linarith), hev] with n hn hp
    rw [div_le_iff₀ hfac] at hn
    have key : G - (G - a) / 2 ≤ (D.factorial : ℝ) * f n / (n : ℝ) ^ D := by
      rw [le_div_iff₀ hp]
      linarith
    linarith
  · filter_upwards [hu ((b - G) / 2) (by linarith), hev] with n hn hp
    rw [le_div_iff₀ hfac] at hn
    have key : (D.factorial : ℝ) * f n / (n : ℝ) ^ D ≤ G + (b - G) / 2 := by
      rw [div_le_iff₀ hp]
      linarith
    linarith

end GlobalTheory.CompanionTheory.Analysis
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TendstoOfAsymptoticBoundsStatement

section

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel Filter Topology

theorem _root_.GlobalTheory.T.tendsto_of_asymptotic_bounds : ∀ (f : ℕ → ℝ) (G : ℝ) (D : ℕ), (∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, (G - ε) * (n : ℝ) ^ D / (D.factorial : ℝ) ≤ f n) → (∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, f n ≤ (G + ε) * (n : ℝ) ^ D / (D.factorial : ℝ)) → Tendsto (fun n : ℕ => (D.factorial : ℝ) * f n / (n : ℝ) ^ D) atTop (𝓝 G) := by
  first | exact @GlobalTheory.CompanionTheory.Analysis.tendsto_factorial_mul_div_pow_of_eps_bounds | exact GlobalTheory.CompanionTheory.Analysis.tendsto_factorial_mul_div_pow_of_eps_bounds | (intros; apply GlobalTheory.CompanionTheory.Analysis.tendsto_factorial_mul_div_pow_of_eps_bounds <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.ProjLineLimit

section

@[expose] public section

namespace GlobalTheory.CompanionTheory.Ar.Pub.NefRRModel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel Filter Topology
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet



section DimZero

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]

theorem chart_finite {y : (Σ k, ι k) → Ω} (hP : IsArithVar (mCoordIdeal y) 1) (c : ∀ k, ι k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) : Module.Finite ℚ (chartRingQ y c) :=
  Algebra.finite_adjoin_of_finite_of_isIntegral (Set.finite_range _) (by
    rintro _ ⟨p, rfl⟩
    exact (CoordCurveDegree.isAlgebraic_ratio hP c hc p).isIntegral)

theorem chart_eq_top {y : (Σ k, ι k) → Ω} (hP : IsArithVar (mCoordIdeal y) 1) (hb : Birational y)
    (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) : chartRingQ y c = ⊤ := by
  have hfin := chart_finite hP c hc
  rw [eq_top_iff]
  intro s _
  obtain ⟨d, g, h, hg, hh, hh0, he⟩ := hb s
  obtain ⟨t₁, ht₁, e₁⟩ := SectionsDimZero.valueSpan_le y c hc d (Submodule.subset_span ⟨g, hg, rfl⟩)
  obtain ⟨t₂, ht₂, e₂⟩ := SectionsDimZero.valueSpan_le y c hc d (Submodule.subset_span ⟨h, hh, rfl⟩)
  rw [LinearMap.mulRight_apply] at e₁ e₂
  have hw : (∏ k, y ⟨k, c k⟩ ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)
  have ht0 : t₂ ≠ 0 := by
    rintro rfl
    exact hh0 (by rw [← e₂, zero_mul])
  have hs : s = t₁ * t₂⁻¹ := by
    rw [← e₁, ← e₂, ← mul_assoc] at he
    have := mul_right_cancel₀ hw he
    rw [this]; field_simp
  rw [hs]
  refine mul_mem ht₁ ?_
  have halg : IsAlgebraic ℚ (⟨t₂, ht₂⟩ : chartRingQ y c) := IsAlgebraic.of_finite ℚ _
  exact Subalgebra.inv_mem_of_algebraic (A := chartRingQ y c) (x := ⟨t₂, ht₂⟩)
    (halg.algHom (chartRingQ y c).val)

theorem span_eq_top {y : (Σ k, ι k) → Ω} [Module.Finite ℚ Ω] (a : K → ℤ) (τ : ℕ) :
    Submodule.span ℚ (chartLatNm y a τ : Set Ω) = ⊤ := by
  classical
  rw [eq_top_iff]
  intro s _
  have halg : ∀ x : Ω, IsAlgebraic ℤ x := fun x =>
    (IsFractionRing.isAlgebraic_iff ℤ ℚ Ω).2 (IsAlgebraic.of_finite ℚ x)
  have hex : ∀ c : ∀ k, ι k, ∃ n : ℤ, n ≠ 0 ∧
      IsIntegral ℤ (n • (s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k)))) := fun c =>
    (halg _).exists_integral_multiple
  choose n hn0 hn using hex
  have hN : (∏ c, n c) ≠ 0 := Finset.prod_ne_zero_iff.2 fun c _ => hn0 c
  have hmem : (∏ c, n c) • s ∈ chartLatNm y a τ := by
    intro c _
    have e : ((∏ c, n c) • s) * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k)) =
        (∏ c' ∈ Finset.univ.erase c, n c') • (n c • (s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k)))) := by
      rw [smul_smul, Finset.prod_erase_mul _ _ (Finset.mem_univ c), smul_mul_assoc]
    rw [e]
    exact ((hn c).zsmul _).tower_top
  have h1 : (∏ c, n c) • s ∈ Submodule.span ℚ (chartLatNm y a τ : Set Ω) := Submodule.subset_span hmem
  have h2 := Submodule.smul_mem _ (((∏ c, n c : ℤ) : ℚ)⁻¹) h1
  rwa [← Int.cast_smul_eq_zsmul ℚ, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hN), one_smul] at h2

theorem nefRR_dimZero (y : (Σ k, ι k) → Ω) (a : K → ℤ) (hP : IsArithVar (mCoordIdeal y) (0 + 1))
    (hb : Birational y) :
    (∀ τ, FiniteDimensional ℚ (Submodule.span ℚ (chartLatNm y a τ : Set Ω))) ∧
      Tendsto (fun τ : ℕ => ((0 : ℕ).factorial : ℝ) *
        (Module.finrank ℚ (Submodule.span ℚ (chartLatNm y a τ : Set Ω)) : ℝ) /
        (τ : ℝ) ^ 0) atTop (𝓝 (genDeg (mCoordIdeal y) 0 a : ℝ)) := by
  classical
  choose c hcX using hP.2.1.2.2
  have hc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k h0 => hcX k (CoordCurveDegree.X_mem_of_eq_zero h0)
  have hfin := chart_finite hP c hc
  rw [chart_eq_top hP hb c hc] at hfin
  have hΩ : Module.Finite ℚ Ω := Module.Finite.equiv (Subalgebra.topEquiv (R := ℚ) (A := Ω)).toLinearEquiv
  refine ⟨fun τ => inferInstance, ?_⟩
  have hQ : chartLatQ y a 0 = ⊤ := by
    rw [eq_top_iff]
    intro s _ c' hc'
    rw [chart_eq_top hP hb c' hc']
    trivial
  have hd := SectionsDimZero.proof K ι Ω y a 0 hP
  rw [hQ] at hd
  have hs : ∀ τ : ℕ, Module.finrank ℚ (Submodule.span ℚ (chartLatNm y a τ : Set Ω)) =
      Module.finrank ℚ (⊤ : Submodule ℚ Ω) := fun τ => by rw [span_eq_top]
  simp only [hs, Nat.factorial_zero, Nat.cast_one, one_mul, pow_zero, div_one, ← hd, Int.cast_natCast]
  exact tendsto_const_nhds

end DimZero

end GlobalTheory.CompanionTheory.Ar.Pub.NefRRModel
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNefSectionsAsymptotic

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter
open GroundTheory.Heights₂.Heights.CoordinateConeArithVar

noncomputable section

set_option linter.unusedSectionVars false

section Coordinates

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]

theorem chartLatQ_eq_smul_one (y : (Σ k, ι k) → Ω) (a : K → ℤ) (τ : ℕ) :
    chartLatQ y a τ = chartLatQ y ((τ : ℤ) • a) 1 := by
  ext s
  show (∀ c : ∀ k, ι k, _ → _) ↔ (∀ c : ∀ k, ι k, _ → _)
  simp only [Pi.smul_apply, smul_eq_mul, Nat.cast_one, one_mul]

end Coordinates

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
end

-- Source module: Development.WeilBound.CoreStatements.TemperedRepresentationTheory.NefDivisors.NefRR

section

@[expose] public section

namespace PositivityTheory.Tls2.Nef

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel Filter Topology

theorem nefRR : GlobalTheory.CompanionTheory.Ar.Pub.NefRR := by
  intro K _ ι _ Ω _ _ y D a hV hB hN
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · exact GlobalTheory.CompanionTheory.Ar.Pub.NefRRModel.nefRR_dimZero y a hV hB
  obtain ⟨e, c, hc, hmem⟩ := GlobalTheory.T.chart_lattice_span_twist_shift K ι Ω y D hV hB
  have hinj : Function.Injective (LinearMap.mulLeft ℚ c) := mul_right_injective₀ hc
  have hle : ∀ τ : ℕ, (Submodule.span ℚ (chartLatNm y a τ : Set Ω)).map (LinearMap.mulLeft ℚ c) ≤
      chartLatQ y ((τ : ℤ) • a + fun k => (e k : ℤ)) 1 := by
    intro τ
    rintro _ ⟨s, hs, rfl⟩
    exact hmem a τ s hs
  have hfd : ∀ τ : ℕ, FiniteDimensional ℚ (Submodule.span ℚ (chartLatNm y a τ : Set Ω)) := by
    intro τ
    haveI := GlobalTheory.T.finiteDimensional_chart_lattice K ι Ω y D ((τ : ℤ) • a + fun k => (e k : ℤ)) hV
    haveI : FiniteDimensional ℚ ((Submodule.span ℚ (chartLatNm y a τ : Set Ω)).map (LinearMap.mulLeft ℚ c)) :=
      Submodule.finiteDimensional_of_le (hle τ)
    exact LinearEquiv.finiteDimensional (Submodule.equivMapOfInjective _ hinj _).symm
  have hup : ∀ τ : ℕ, Module.finrank ℚ (Submodule.span ℚ (chartLatNm y a τ : Set Ω)) ≤
      Module.finrank ℚ (chartLatQ y ((τ : ℤ) • a + fun k => (e k : ℤ)) 1) := by
    intro τ
    haveI := GlobalTheory.T.finiteDimensional_chart_lattice K ι Ω y D ((τ : ℤ) • a + fun k => (e k : ℤ)) hV
    rw [(Submodule.equivMapOfInjective _ hinj (Submodule.span ℚ (chartLatNm y a τ : Set Ω))).finrank_eq]
    exact Submodule.finrank_mono (hle τ)
  have hlow : ∀ τ : ℕ, Module.finrank ℚ (chartLatQ y ((τ : ℤ) • a + 0) 1) ≤
      Module.finrank ℚ (Submodule.span ℚ (chartLatNm y a τ : Set Ω)) := by
    intro τ
    haveI := hfd τ
    have hsub : chartLatQ y ((τ : ℤ) • a + 0) 1 ≤ Submodule.span ℚ (chartLatNm y a τ : Set Ω) := by
      rw [add_zero, ← chartLatQ_eq_smul_one]
      exact GlobalTheory.T.chart_lattice_le_span_norm K ι Ω y a τ
    exact Submodule.finrank_mono hsub
  refine ⟨hfd, ?_⟩
  apply GlobalTheory.T.tendsto_of_asymptotic_bounds (fun τ => (Module.finrank ℚ (Submodule.span ℚ (chartLatNm y a τ : Set Ω)) : ℝ)) _ D
  · intro ε hε
    filter_upwards [GlobalTheory.CompanionTheory.NefLower.nef_sections_lower K ι Ω y D a 0 hD hV hB hN ε hε] with n hn
    exact hn.trans (by exact_mod_cast hlow n)
  · intro ε hε
    filter_upwards [GlobalTheory.T.chart_lattice_dimension_upper K ι Ω y D a (fun k => (e k : ℤ)) hD hV hB hN ε hε] with n hn
    exact le_trans (by exact_mod_cast hup n) hn

end PositivityTheory.Tls2.Nef
end
end
