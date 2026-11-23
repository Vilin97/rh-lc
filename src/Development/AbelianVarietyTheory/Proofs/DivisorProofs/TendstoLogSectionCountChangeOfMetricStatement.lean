module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
public import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists
import Development.AbelianVarietyTheory.Definitions.Divisors.LeTwoMulOfForallScale
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Topology.PartitionOfUnity
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaiseFirstWeightSectionsLociValuesNormsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupNormBallCountAsymptoticGramDeterminantStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoLogDetGramChangeSemiPositiveMetricStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PositiveDensityExists

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.Cartier
open scoped ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CurveDens

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

theorem transDet_trans_chart (c c' c'' : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ c.e.source)
    (hy' : y ∈ c'.e.source) (hy'' : y ∈ c''.e.source) :
    ChartGlue.transDet c.e c''.e y =
      ChartGlue.transDet c.e c'.e y * ChartGlue.transDet c'.e c''.e y := by
  have ho := ChartGlue.isOpen_over c.e (c'.e.open_source.inter c''.e.open_source)
  have hm : c.e y ∈ c.e.target ∩ c.e.symm ⁻¹' (c'.e.source ∩ c''.e.source) :=
    ChartGlue.mem_over c.e hy ⟨hy', hy''⟩
  have e : c''.e ∘ c.e.symm =ᶠ[𝓝 (c.e y)] (c''.e ∘ c'.e.symm) ∘ (c'.e ∘ c.e.symm) :=
    eventually_of_mem (ho.mem_nhds hm) fun w hw => by
      simp only [Function.comp_apply, c'.e.left_inv hw.2.1]
  have hf : DifferentiableAt ℂ (c'.e ∘ c.e.symm) (c.e y) :=
    (c.holo_trans c').differentiableAt
      ((ChartGlue.isOpen_over c.e c'.e.open_source).mem_nhds (ChartGlue.mem_over c.e hy hy'))
  have hfy : (c'.e ∘ c.e.symm) (c.e y) = c'.e y := by simp [c.e.left_inv hy]
  have hg : DifferentiableAt ℂ (c''.e ∘ c'.e.symm) ((c'.e ∘ c.e.symm) (c.e y)) := by
    rw [hfy]
    exact (c'.holo_trans c'').differentiableAt
      ((ChartGlue.isOpen_over c'.e c''.e.open_source).mem_nhds (ChartGlue.mem_over c'.e hy' hy''))
  rw [ChartGlue.transDet, e.fderiv_eq, fderiv_comp _ hg hf, hfy, ChartGlue.transDet,
    ChartGlue.transDet]
  simp only [ContinuousLinearMap.det]
  exact (LinearMap.det_comp _ _).trans (mul_comm _ _)

theorem transDet_chart_ne_zero (c c' : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ c.e.source)
    (hy' : y ∈ c'.e.source) : ChartGlue.transDet c.e c'.e y ≠ 0 := by
  intro h
  have := transDet_trans_chart c c' c hy hy' hy
  rw [c.transDet_self hy, h, zero_mul] at this
  exact one_ne_zero this

theorem continuousAt_transDet_chart (c c' : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ c.e.source)
    (hy' : y ∈ c'.e.source) : ContinuousAt (ChartGlue.transDet c.e c'.e) y := by
  have hW : y ∈ ptsIn p σ (c.U ⊓ c'.U) :=
    mem_ptsIn_inf.2 ⟨c.source_subset hy, c'.source_subset hy'⟩
  have h1 : ContinuousAt (ev p σ _ (c.isFrame.ratio c'.isFrame).val) y :=
    (continuousOn_ev _).continuousAt ((isOpen_ptsIn _).mem_nhds hW)
  refine h1.congr ?_
  filter_upwards [(c.e.open_source.inter c'.e.open_source).mem_nhds ⟨hy, hy'⟩] with z hz
  exact c.ev_ratio c' hz.1 hz.2

end GlobalTheory.CurveDens
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothVolumeDensityChartProjArith

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmp

theorem exists_volDens : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → GenSmooth p D → ∀ σ : k →+* ℂ, Nonempty (VolDens p σ D) := by
  intro k _ X _ p D hX hS σ
  haveI := hX.compactSpace σ
  haveI := CxPts.t2Space_cxPts_of_isProjOver σ hX.isProjOver
  obtain ⟨R⟩ := hS σ
  obtain ⟨s, hs⟩ := R.exists_finite
  obtain ⟨f, hf⟩ := PartitionOfUnity.exists_isSubordinate (X := CxPts p σ) (ι := s) isClosed_univ
    (fun i => (R.chart i.1).e.source) (fun i => (R.chart i.1).e.open_source)
    (fun y _ => by
      obtain ⟨i, hi, hy⟩ := hs y
      exact Set.mem_iUnion.2 ⟨⟨i, hi⟩, hy⟩)
  have hsrc : ∀ (i : s) (y : CxPts p σ), f i y ≠ 0 → y ∈ (R.chart i.1).e.source := fun i y h =>
    hf i (subset_tsupport _ h)
  refine ⟨{ dens := fun c y => ∑ i : s, f i y * ‖ChartGlue.transDet c.e (R.chart i.1).e y‖ ^ 2
            cont := fun c => ?_
            pos := fun c y hy => ?_
            trans := fun c c' y hy hy' => ?_ }⟩
  · refine continuousOn_finsetSum _ fun i _ => fun y hy => ContinuousAt.continuousWithinAt ?_
    by_cases h : y ∈ tsupport (f i)
    · exact (f i).continuous.continuousAt.mul
        ((CurveDens.continuousAt_transDet_chart c _ hy (hf i h)).norm.pow 2)
    · refine (continuousAt_const (y := (0 : ℝ))).congr ?_
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 h] with z hz
      rw [hz, Pi.zero_apply, zero_mul]
  · obtain ⟨i, hi⟩ := f.exists_pos (Set.mem_univ y)
    refine Finset.sum_pos' (fun j _ => mul_nonneg (f.nonneg j y) (sq_nonneg _))
      ⟨i, Finset.mem_univ _, mul_pos hi (pow_pos (norm_pos_iff.2 ?_) 2)⟩
    exact CurveDens.transDet_chart_ne_zero c _ hy (hsrc i y hi.ne')
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : f i y = 0
    · simp [h]
    · rw [CurveDens.transDet_trans_chart c c' _ hy hy' (hsrc i y h), norm_mul, mul_pow]
      ring

end GlobalTheory.HSAmp
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothVolumeDensityChartProjArithStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

theorem _root_.GlobalTheory.T.exists_smoothVolumeDensityChart_projArith : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → GenSmooth p D → ∀ σ : k →+* ℂ, Nonempty (VolDens p σ D) := by
  first | exact @GlobalTheory.HSAmp.exists_volDens | exact GlobalTheory.HSAmp.exists_volDens | (intros; apply GlobalTheory.HSAmp.exists_volDens <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoLogSectionCountChangeOfMetric

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

theorem exists_intBasis {K : Type} [Field K] [CharZero K] (Λ : AddSubgroup K) (hΛ : Λ.FG) :
    ∃ f : Fin (Module.finrank ℤ Λ) → K, LinearIndependent ℤ f ∧ AddSubgroup.closure (Set.range f) = Λ ∧
      ∀ i, f i ∈ Λ := by
  haveI : Module.Finite ℤ Λ := Module.Finite.iff_addGroup_fg.2 ((AddGroup.fg_iff_addSubgroup_fg Λ).2 hΛ)
  haveI : Module.Free ℤ Λ := Module.free_of_finite_type_torsion_free'
  let b := Module.finBasis ℤ Λ
  refine ⟨fun i => (b i : K), ?_, le_antisymm ?_ ?_, fun i => (b i).2⟩
  · exact b.linearIndependent.map' Λ.subtype.toIntLinearMap (LinearMap.ker_eq_bot.2 Subtype.val_injective)
  · exact (AddSubgroup.closure_le _).2 (Set.range_subset_iff.2 fun i => (b i).2)
  · intro x hx
    have h := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
    change _ = x at h
    rw [← h, AddSubmonoidClass.coe_finsetSum]
    refine AddSubgroup.sum_mem _ fun i _ => ?_
    rw [AddSubgroupClass.coe_zsmul]
    exact AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self (f := fun i => (b i : K)) i)) _

theorem tendsto_logCount_sub_up : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → GenSmooth p D → ∀ (P : Pair p) (a : ℝ), P.L.SemiPos D → P.L.IsSelfInter a → ∀ Λ : ℕ → AddSubgroup X.functionField, GoodFam P D (gdeg P.L D / D.factorial) Λ → ∃ t₀ : ℝ, ∀ (u : SmFn p) (B a' : ℝ), 0 ≤ B → (∀ σ y, |u.u σ y| ≤ B) → (up P.L u).SemiPos D → (up P.L u).IsSelfInter a' → ∀ t : ℝ, t₀ + B ≤ t → Tendsto (fun m : ℕ => (Real.log ((ballIn (upperParabolic P u) (Λ m) m 1 (Real.exp (t * m))).ncard : ℝ) - Real.log ((ballIn P (Λ m) m 1 (Real.exp (t * m))).ncard : ℝ)) / (m : ℝ) ^ (D + 1)) atTop (𝓝 ((a' - a) / (D + 1).factorial)) := by
  intro HA k _ X _ p D hX hS P a hP ha Λ hΛ
  obtain ⟨C, hC1, hCs⟩ := hΛ.small
  refine ⟨Real.log C + 1, ?_⟩
  intro u B a' hB hu hup ha' t ht
  have := hX.charZero
  haveI : CharZero X.functionField :=
    charZero_of_injective_ringHom (germ_injective_of_isIntegral X (U := ⊤) _ trivial)
  choose f hli hcl hmemΛ using fun m => exists_intBasis (Λ m) (hΛ.fg m)
  let ω : ∀ σ, VolDens p σ D := fun σ => Classical.choice (GlobalTheory.T.exists_smoothVolumeDensityChart_projArith k X p D hX hS σ)
  have hmem : ∀ (m : ℕ) i, f m i ∈ P.H m 1 := fun m i => hΛ.le m (hmemΛ m i)
  have hmem' : ∀ (m : ℕ) i, f m i ∈ (upperParabolic P u).H m 1 := fun m i => by
    rw [(GlobalTheory.T.raiseFirstWeight_sections_loci_values_norms k X p P u m 1).1]; exact hmem m i
  have hC1' : 1 ≤ C * Real.exp B := one_le_mul_of_one_le_of_one_le hC1 (Real.one_le_exp hB)
  have hlog : Real.log (C * Real.exp B) = Real.log C + B := by
    rw [Real.log_mul (by positivity) (Real.exp_pos B).ne', Real.log_exp]
  have hs : ∀ m : ℕ, 1 ≤ m → AddSubgroup.closure (Set.range (f m)) ≤
      AddSubgroup.closure (ballIn P (AddSubgroup.closure (Set.range (f m))) m 1 (C ^ m)) := by
    intro m hm; rw [hcl m]; exact hCs m hm
  have hs' : ∀ m : ℕ, 1 ≤ m → AddSubgroup.closure (Set.range (f m)) ≤
      AddSubgroup.closure (ballIn (upperParabolic P u) (AddSubgroup.closure (Set.range (f m))) m 1 ((C * Real.exp B) ^ m)) := by
    intro m hm
    rw [hcl m]
    refine (hCs m hm).trans (AddSubgroup.closure_mono ?_)
    rintro x ⟨hx, hb⟩
    refine ⟨hx, fun σ y => ?_⟩
    rw [((GlobalTheory.T.raiseFirstWeight_sections_loci_values_norms k X p P u m 1).2.2 σ y x).2]
    have h0 : 0 ≤ P.nu m 1 σ y x := by rw [← norm_val]; exact norm_nonneg _
    rw [mul_pow, ← Real.exp_nat_mul]
    refine mul_le_mul (hb σ y) (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le (by positivity)
    have hu' := (abs_le.1 (hu σ y)).1
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left (neg_le.1 hu') hm0, mul_nonneg hm0 hB]
  have h1 := GlobalTheory.T.supNormBall_count_asymptotic_gramDeterminant k X p D hX hS P hP ω _ f hmem hli _ hΛ.rank C hC1 hs t (by linarith)
  have h2 := GlobalTheory.T.supNormBall_count_asymptotic_gramDeterminant k X p D hX hS (upperParabolic P u) hup ω _ f hmem' hli _ hΛ.rank (C * Real.exp B) hC1' hs' t
    (by rw [hlog]; linarith)
  have h3 := GlobalTheory.T.tendsto_logDet_gram_change_semiPositive_metric HA k X p D hX hS P hP ω _ f hmem hli hΛ.rank u a a' hup ha ha'
  simp only [hcl] at h1 h2
  have key := (h2.sub h1).add (h3.div_const 2)
  convert key using 1
  · funext m; ring
  · congr 1; ring

end GlobalTheory.HSAmp
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoLogSectionCountChangeOfMetricStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

theorem _root_.GlobalTheory.T.tendsto_logSectionCount_change_of_metric : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → GenSmooth p D → ∀ (P : Pair p) (a : ℝ), P.L.SemiPos D → P.L.IsSelfInter a → ∀ Λ : ℕ → AddSubgroup X.functionField, GoodFam P D (gdeg P.L D / D.factorial) Λ → ∃ t₀ : ℝ, ∀ (u : SmFn p) (B a' : ℝ), 0 ≤ B → (∀ σ y, |u.u σ y| ≤ B) → (up P.L u).SemiPos D → (up P.L u).IsSelfInter a' → ∀ t : ℝ, t₀ + B ≤ t → Tendsto (fun m : ℕ => (Real.log ((ballIn (upperParabolic P u) (Λ m) m 1 (Real.exp (t * m))).ncard : ℝ) - Real.log ((ballIn P (Λ m) m 1 (Real.exp (t * m))).ncard : ℝ)) / (m : ℝ) ^ (D + 1)) atTop (𝓝 ((a' - a) / (D + 1).factorial)) := by
  first | exact @GlobalTheory.HSAmp.tendsto_logCount_sub_up | exact GlobalTheory.HSAmp.tendsto_logCount_sub_up | (intros; apply GlobalTheory.HSAmp.tendsto_logCount_sub_up <;> assumption)
end
end
