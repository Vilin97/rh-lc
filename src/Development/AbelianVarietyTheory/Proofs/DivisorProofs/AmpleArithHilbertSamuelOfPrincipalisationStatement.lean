module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArCalcOfPrincipalisation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHilbertSamuelSmallSectionsChangeOfMetricStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasepointFreeSectionTupleAmpleArithStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFubiniStudyWeightsBoundedDifferenceStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairNormIndependentOfFrames
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularNonvanishingLocusSectionPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionLocalFunctionContinuousOnHolomorphicChartStatement
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
import ReciprocityTheory.L2DbarEstimates.LeviForms.LogNormSq
import ReciprocityTheory.L2DbarEstimates.LeviForms.OfRealNormSqSumMul
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundleGeometricDegreeRaiseWeightStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGoodSectionGroupFamilyAmpleMultiplesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormBasepointFreeSectionsLeOneFubiniStudyStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionCountGrowthMetricNearGeneratorMaxStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProjectiveSpaceMorphismOfGeneratingSectionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFunctionFieldQuotientSubfieldEqDegreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricDegreeProjectionFormulaSelfInterPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveSpaceOrderArithVarietyFubiniStudyDegreStatement
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Tactic.Basify

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudyWeightIncrementSemiPositiveCurvature

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false


namespace GlobalTheory.HSAmp

open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y

theorem semiPos_up_of_isCan : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (P : Pair p), ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x →
    ∀ (n : ℕ) (u : SmFn p), 1 ≤ n → IsCan P e n x u → (up P.L u).SemiPos D := by
  intro k _ X _ p D _ P e x hx n u hn hu σ i c y hy ξ
  set j := pick (P.A.φ σ).isLB y
  have hj : y ∈ ptsIn p σ (P.A.B.U j) := mem_pick (P.A.φ σ).isLB y
  set O := ptsIn p σ (P.L.B.U i) ∩ ptsIn p σ (P.A.B.U j) with hOdef
  have hO : IsOpen O := (isOpen_ptsIn _).inter (isOpen_ptsIn _)
  have he : (0 : ℝ) < e := by exact_mod_cast hx.pos
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hen : (0 : ℝ) < (e : ℝ) * n := mul_pos he hn'

  have key : ∀ z ∈ O, 0 < ∑ l, Complex.normSq (ratVal (P.loc e 0 (x l) i j) z ^ n) ∧
      (P.L.φ σ).φ i z + u.u σ z =
        ((e : ℝ) * n)⁻¹ * Real.log (∑ l, Complex.normSq (ratVal (P.loc e 0 (x l) i j) z ^ n)) := by
    intro z hz
    have hnu : ∀ l, P.nu e 0 σ z (x l) ^ (2 * n) =
        Complex.normSq (ratVal (P.loc e 0 (x l) i j) z ^ n) * Real.exp (-((e : ℝ) * n) * (P.L.φ σ).φ i z) := by
      intro l
      rw [GlobalTheory.VolBr.nu_eq k X p P e 0 (x l) (hx.mem l) σ z i j hz.1 hz.2, Complex.normSq_eq_norm_sq, norm_pow,
        mul_pow, ← pow_mul, ← Real.exp_nat_mul]
      congr 2
      · ring_nf
      · push_cast; ring
    have hsum : ∑ l, P.nu e 0 σ z (x l) ^ (2 * n) =
        (∑ l, Complex.normSq (ratVal (P.loc e 0 (x l) i j) z ^ n)) * Real.exp (-((e : ℝ) * n) * (P.L.φ σ).φ i z) := by
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun l _ => hnu l
    have hpos : 0 < ∑ l, P.nu e 0 σ z (x l) ^ (2 * n) := by
      obtain ⟨l, hl⟩ := hx.cover (under z)
      have h1 := ((GlobalTheory.T.regularNonvanishingLocusSection_properties k X p P e 0 (x l) (hx.mem l)).2.2.2.2 (x l) (hx.mem l) σ z hl).2
      exact Finset.sum_pos' (fun l' _ => pow_nonneg (by unfold Pair.nu; positivity) _)
        ⟨l, Finset.mem_univ _, pow_pos h1 _⟩
    have hS : 0 < ∑ l, Complex.normSq (ratVal (P.loc e 0 (x l) i j) z ^ n) := by
      rw [hsum] at hpos
      exact pos_of_mul_pos_left hpos (Real.exp_pos _).le
    refine ⟨hS, ?_⟩
    rw [hu σ z, hsum, Real.log_mul hS.ne' (Real.exp_pos _).ne', Real.log_exp]
    field_simp
    ring
  have hyO : y ∈ O := ⟨hy.2, hj⟩
  have hW : IsOpen (c.e.target ∩ c.e.symm ⁻¹' O) := GlobalTheory.ChartGlue.isOpen_over c.e hO
  have hyW : c.e y ∈ c.e.target ∩ c.e.symm ⁻¹' O := GlobalTheory.ChartGlue.mem_over c.e hy.1 hyO
  have hG : ∀ l, ContDiffAt ℂ 2 (fun v => ratVal (P.loc e 0 (x l) i j) (c.e.symm v) ^ n) (c.e y) := fun l =>
    contDiffAt_two_of_holo hW (((GlobalTheory.T.sectionLocalFunction_continuousOn_holomorphicChart k X p P e 0 σ (x l) (hx.mem l) i j).2 D c).pow n) hyW
  have hS : 0 < ∑ l, Complex.normSq (ratVal (P.loc e 0 (x l) i j) (c.e.symm (c.e y)) ^ n) :=
    (key _ hyW.2).1
  have hf : ContDiffAt ℝ 2 (fun v => Real.log (∑ l, Complex.normSq (ratVal (P.loc e 0 (x l) i j) (c.e.symm v) ^ n)))
      (c.e y) :=
    (ContDiffAt.sum fun l _ => contDiffAt_normSq_comp (hG l)).log hS.ne'
  have heq : (fun v => ((((P.L.φ σ).addFn (u.u σ)).φ i (c.e.symm v) : ℝ) : ℂ)) =ᶠ[𝓝 (c.e y)]
      fun v => ((((e : ℝ) * n)⁻¹ *
        Real.log (∑ l, Complex.normSq (ratVal (P.loc e 0 (x l) i j) (c.e.symm v) ^ n)) + 0 : ℝ) : ℂ) :=
    eventually_of_mem (hW.mem_nhds hyW) fun v hv => by
      dsimp only
      rw [add_zero, ← (key _ hv.2).2]
      rfl
  change 0 ≤ (leviV D (fun v => ((((P.L.φ σ).addFn (u.u σ)).φ i (c.e.symm v) : ℝ) : ℂ)) (c.e y) ξ).re
  rw [leviV_congr heq, leviV_const_mul hf _ 0, Complex.re_ofReal_mul]
  exact mul_nonneg (inv_nonneg.2 hen.le) (leviV_log_sum_nonneg (fun l => contDiffAt_normSq_comp (hG l))
    (fun l => logPshAt_normSq (hG l)) hS ξ)

end GlobalTheory.HSAmp
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudyWeightIncrementSemiPositiveCurvatureStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

theorem _root_.GlobalTheory.T.fubiniStudyWeightIncrement_semiPositive_curvature : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → ∀ (n : ℕ) (u : SmFn p), 1 ≤ n → IsCan P e n x u → (up P.L u).SemiPos D := by
  first | exact @GlobalTheory.HSAmp.semiPos_up_of_isCan | exact GlobalTheory.HSAmp.semiPos_up_of_isCan | (intros; apply GlobalTheory.HSAmp.semiPos_up_of_isCan <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfIntersectionCanonicalWeightsTendstoZero

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

theorem selfInter_canWeight_le : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k)
    (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField),
    Gens P D e x → ∃ C : ℝ, ∀ (n : ℕ) (u : SmFn p) (a : ℝ), 1 ≤ n → IsCan P e n x u →
      (up P.L u).IsSelfInter a → |a| ≤ C / n := by
  intro hC k _ X _ p D hX P hA e x hG
  haveI := hX.isDomain
  haveI := hX.finite
  haveI := hX.charZero_base
  have hf : 0 < Module.finrank ℤ k := Module.finrank_pos
  have he : 0 < e := hG.pos
  obtain ⟨hPI, -, -, -, -, -, -⟩ := GlobalTheory.T.exists_projectiveSpace_morphism_of_generating_sections k X p D hX P hA e x hG
  obtain ⟨hPV, -, -⟩ := GlobalTheory.T.projectiveSpace_order_arithVariety_fubiniStudyDegree k D

  obtain ⟨Φ₀, hΦ₀⟩ := ((hC.arExists k (PSpace k D) (PSpace.str k D) D hPV).2 Unit
    fun _ => ProjSpace.hermitianTwistingSheaf k D).1
  have hH := ((hC.arIso k (PSpace k D) (PSpace.str k D) D hPV).2 Unit _ Φ₀ hΦ₀).1 ()
  set H := Φ₀ (MvPolynomial.X () ^ (D + 1)) with hHdef
  set g := gdeg P.L D
  refine ⟨|g * H| / ((Module.finrank ℤ k : ℝ) * e), fun n u a hn hu ha => ?_⟩
  obtain ⟨-, -, -, hG', hu'⟩ := GlobalTheory.T.norm_basepointFree_sections_le_one_fubiniStudy k X p D hX P e x hG n u hn hu
  obtain ⟨hPI', π, hπ, hgen, hd, hdf, hiso⟩ := GlobalTheory.T.exists_projectiveSpace_morphism_of_generating_sections k X p D hX P hA (e * n) _ hG'
  have hdeg := GlobalTheory.T.finrank_functionField_quotientSubfield_eq_degree hC k X p D hX P hA (e * n) _ hG'
  have hpow := (GlobalTheory.T.geometricDegree_projectionFormula_selfInter_pow hC k X p D hX).2 (up P.L u) (e * n) a ha
  have hpull := ((hC.arProj k (PSpace k D) X (PSpace.str k D) p D hPV hX π hπ hgen hd).1 _ H hH)

  obtain ⟨Φ, hΦ⟩ := ((hC.arExists k X p D hX).2 Unit fun _ => (up P.L u).pow (e * n)).1
  have hI := hC.arIso k X p D hX
  have h₁ := (hI.2 Unit _ Φ hΦ).1 ()
  have hΦ' := (hI.2 Unit _ Φ hΦ).2.1 (fun _ => (ProjSpace.hermitianTwistingSheaf k D).pull π hπ) fun _ => hiso u hu'
  have h₂ := (hI.2 Unit _ Φ hΦ').1 ()
  have e₁ := HermLB.IsSelfInter.unique hX hpow h₁
  have e₂ := HermLB.IsSelfInter.unique hX hpull h₂

  set d : ℝ := ((π.residueDegree (genericPoint X) : ℕ) : ℝ)
  set f : ℝ := ((Module.finrank ℤ k : ℕ) : ℝ)
  set E : ℝ := ((e * n : ℕ) : ℝ)
  have hE : 0 < E := by positivity
  have hfpos : (0 : ℝ) < f := Nat.cast_pos.mpr hf
  have key1 : E ^ (D + 1) * a = d * H := e₁.trans e₂.symm
  have key2 : d * f = E ^ D * g := by
    have := congrArg (fun m : ℕ => (m : ℝ)) hdf
    simp only [Nat.cast_mul] at this
    rw [← hdeg]; exact this
  have ha' : a = g * H / (f * E) := by
    field_simp
    have : E ^ (D + 1) * a * f = E ^ D * g * H := by rw [key1, ← key2]; ring
    have hED : E ^ D ≠ 0 := pow_ne_zero _ hE.ne'
    apply mul_left_cancel₀ hED
    linear_combination this
  rw [ha', abs_div, abs_of_pos (by positivity : (0:ℝ) < f * E)]
  have : f * E = (f * e) * n := by simp [E, f]; ring
  rw [this, div_div]

end GlobalTheory.HSAmp
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfIntersectionCanonicalWeightsTendstoZeroStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

theorem _root_.GlobalTheory.T.selfIntersection_canonicalWeights_tendsto_zero : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → ∃ C : ℝ, ∀ (n : ℕ) (u : SmFn p) (a : ℝ), 1 ≤ n → IsCan P e n x u → (up P.L u).IsSelfInter a → |a| ≤ C / n := by
  first | exact @GlobalTheory.HSAmp.selfInter_canWeight_le | exact GlobalTheory.HSAmp.selfInter_canWeight_le | (intros; apply GlobalTheory.HSAmp.selfInter_canWeight_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleArithHilbertSamuelOfPrincipalisation

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem ampleHS_of_principalisation : GlobalTheory.Published.Principalisation → AmpleHS := by
  intro hPr k _ X _ p D hX P a hA hS ha
  have hC := GlobalTheory.MixHt.arCalc_of_principalisation hPr
  obtain ⟨e, x, hx⟩ := GlobalTheory.T.exists_basepointFreeSectionTuple_ample_arith k X p D hX P hA
  obtain ⟨B, hB0, hB⟩ := GlobalTheory.T.exists_fubiniStudyWeights_bounded_difference k X p D hX P e x hx
  have hG := GlobalTheory.T.isGoodSectionGroupFamily_ampleMultiples hC k X p D hX P hA
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.T.arithHilbertSamuel_smallSections_change_of_metric hPr k X p D hX P a hS ha hG
  obtain ⟨C, hCb⟩ := GlobalTheory.T.selfIntersection_canonicalWeights_tendsto_zero hC k X p D hX P hA e x hx
  refine ⟨max (t₀ + B) 1, fun t ht => ?_⟩
  have ht1 : t₀ + B ≤ t := le_trans (le_max_left _ _) ht
  have ht2 : 0 < t := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) ht)
  have hball : ∀ (u : SmFn p) (m : ℕ) (R : ℝ), ballIn (upperParabolic P u) (P.H m 1) m 1 R = (upperParabolic P u).Bl m 1 R :=
    fun _ _ _ => rfl
  have hball' : ∀ (m : ℕ) (R : ℝ), ballIn P (P.H m 1) m 1 R = P.Bl m 1 R := fun _ _ => rfl
  have hF : (0 : ℝ) < D.factorial := by exact_mod_cast Nat.factorial_pos D
  have hF1 : (0 : ℝ) < (D + 1).factorial := by exact_mod_cast Nat.factorial_pos _
  have he : (0 : ℝ) < e := by exact_mod_cast hx.pos
  have hLg : 0 ≤ Real.log ((D : ℝ) + 1) := Real.log_nonneg (by linarith [(Nat.cast_nonneg D : (0 : ℝ) ≤ D)])
  set g := gdeg P.L D with hg
  have hc : (a + ((D : ℝ) + 1) * t * g) / ((D + 1).factorial : ℝ) = g / D.factorial * t + a / (D + 1).factorial := by
    rw [Nat.factorial_succ]; push_cast; field_simp; ring
  have key : ∀ n : ℕ, 1 ≤ n → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop,
      |P.lc m 1 (Real.exp (t * m)) / (m : ℝ) ^ (D + 1) - (g / D.factorial * t + a / (D + 1).factorial)|
        ≤ |g| / D.factorial * (Real.log ((D : ℝ) + 1) / (2 * n) / e) + |C| / n / (D + 1).factorial + 2 * ε := by
    intro n hn ε hε
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    obtain ⟨u, hu, huB⟩ := hB n hn
    have hsemi := GlobalTheory.T.fubiniStudyWeightIncrement_semiPositive_curvature k X p D hX P e x hx n u hn hu
    obtain ⟨h, hh⟩ := (hC.arExists k X p D hX).1 (up P.L u)
    have hsi : (up P.L u).IsSelfInter (h (genericPoint X)) := ⟨h, hh, rfl⟩
    have han := hCb n u _ hn hu hsi
    have hdiff := ht₀ u B _ hB0 huB hsemi hsi t ht1
    obtain ⟨hnu1, hnu2, hgu, -, -⟩ := GlobalTheory.T.norm_basepointFree_sections_le_one_fubiniStudy k X p D hX P e x hx n u hn hu
    have hκ1 : Real.exp (-(Real.log ((D : ℝ) + 1) / (2 * n))) ≤ 1 :=
      Real.exp_le_one_iff.2 (neg_nonpos.2 (div_nonneg hLg (by positivity)))
    have hcnt := GlobalTheory.T.sectionCount_growth_metric_near_generatorMax hC k X p D hX (upperParabolic P u) hA e x hgu _ t (Real.exp_pos _) hκ1 ht2 hnu1 hnu2 ε hε
    rw [show (upperParabolic P u).L = up P.L u from rfl, GlobalTheory.T.hermLineBundleGeometricDegree_raiseWeight hC k X p D hX P.L u, Real.log_exp, ← hg] at hcnt
    simp only [hball, hball'] at hdiff
    have hd := hdiff.eventually (Metric.ball_mem_nhds _ hε)
    set an := h (genericPoint X)
    set T := Real.log ((D : ℝ) + 1) / (2 * n) / e with hT
    have hT0 : 0 ≤ T := by positivity
    have hup : g / D.factorial * (t - -(Real.log ((D : ℝ) + 1) / (2 * n)) / e) ≤ g / D.factorial * t + |g| / D.factorial * T := by
      rw [show t - -(Real.log ((D : ℝ) + 1) / (2 * n)) / e = t + T by rw [hT]; ring, mul_add]
      gcongr
      exact le_abs_self g
    have han1 : an / (D + 1).factorial ≤ |C| / n / (D + 1).factorial :=
      div_le_div_of_nonneg_right ((le_abs_self an).trans (han.trans (div_le_div_of_nonneg_right (le_abs_self C) hn0.le))) hF1.le
    have hgT : 0 ≤ |g| / D.factorial * T := by positivity
    have han2 : -(an / (D + 1).factorial) ≤ |C| / n / (D + 1).factorial := by
      rw [← neg_div]; exact div_le_div_of_nonneg_right ((neg_le_abs an).trans (han.trans (div_le_div_of_nonneg_right (le_abs_self C) hn0.le))) hF1.le
    filter_upwards [hd, hcnt] with m hm1 hm2
    rw [Real.dist_eq, abs_sub_lt_iff] at hm1
    have hsplit : P.lc m 1 (Real.exp (t * m)) / (m : ℝ) ^ (D + 1) =
        (upperParabolic P u).lc m 1 (Real.exp (t * m)) / (m : ℝ) ^ (D + 1) -
          (Real.log ((upperParabolic P u).Bl m 1 (Real.exp (t * m))).ncard - Real.log (P.Bl m 1 (Real.exp (t * m))).ncard) /
            (m : ℝ) ^ (D + 1) := by
      simp only [Pair.lc]; ring
    have hq : (an - a) / ((D + 1).factorial : ℝ) = an / (D + 1).factorial - a / (D + 1).factorial := sub_div _ _ _
    rw [hsplit, abs_le]
    constructor <;> linarith [hm2.1, hm2.2]
  rw [hc]
  refine Metric.tendsto_nhds.2 fun δ hδ => ?_
  set K := |g| / D.factorial * (Real.log ((D : ℝ) + 1) / 2 / e) + |C| / (D + 1).factorial with hK
  have hK0 : 0 ≤ K := by positivity
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * K / δ)
  have hn1 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hKn : |g| / D.factorial * (Real.log ((D : ℝ) + 1) / (2 * ((n + 1 : ℕ) : ℝ)) / e) +
      |C| / ((n + 1 : ℕ) : ℝ) / (D + 1).factorial = K / ((n + 1 : ℕ) : ℝ) := by
    rw [hK]; field_simp
  have hKlt : K / ((n + 1 : ℕ) : ℝ) < δ / 2 := by
    have h1 : 2 * K / δ < ((n + 1 : ℕ) : ℝ) := hn.trans (by exact_mod_cast Nat.lt_succ_self n)
    rw [div_lt_iff₀ hδ] at h1
    rw [div_lt_iff₀ hn1]
    linarith
  filter_upwards [key (n + 1) (Nat.le_add_left 1 n) (δ / 8) (by positivity)] with m hm
  rw [hKn] at hm
  rw [Real.dist_eq]
  linarith

end GlobalTheory.HSNef
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleArithHilbertSamuelOfPrincipalisationStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.ampleArithHilbertSamuel_of_principalisation : GlobalTheory.Published.Principalisation → GlobalTheory.HSNef.AmpleHS := by
  first | exact @GlobalTheory.HSNef.ampleHS_of_principalisation | exact GlobalTheory.HSNef.ampleHS_of_principalisation | (intros; apply GlobalTheory.HSNef.ampleHS_of_principalisation <;> assumption)
end
end
