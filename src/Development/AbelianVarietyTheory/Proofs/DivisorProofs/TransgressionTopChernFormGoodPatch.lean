module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffAtHolomorphicComplexChartOfSmoothAtStatement
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceComplexPointsOfProjVariety
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousMulTopChernFormIsTopDegreeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableOnHolomorphicChartTransEtaleChartStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodPatchChartImagePropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramMatrixSmoothIsUnitInHolomorphicChartStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnCutoffTopChernFormPoincareGrowth
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopChernDensityHolomorphicChartEtaleStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopFormIntegralOfSupportInHolomorphicChartStatement
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodMetricLocalTransgressionFormula
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodPatchChartImagePropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramMatrixSmoothIsUnitInHolomorphicChartStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnCutoffTopChernFormSmoothGram
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransgressionTermDensityGoodPatchStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnCutoffTopChernFormPoincareGrowthStatement

section

@[expose] public section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

theorem _root_.GlobalTheory.T.integrableOn_cutoff_topChernForm_poincareGrowth : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (S : Finset (Fin n)) (U K : Set (V n)) (G₀ G₁ : V n → Matrix r r ℂ) (ρ : V n → ℝ) (c : ℝ), IsOpen U → IsCompact K → K ⊆ U → (∀ v ∈ U, ∀ a ∈ S, ‖v a‖ ≤ 1 / 2) → (∀ v ∈ U, MContDiffAt ∞ G₀ v ∧ IsUnit (G₀ v).det) → (∀ v ∈ offHyp S U, MContDiffAt ∞ G₁ v ∧ IsUnit (G₁ v).det) → (∀ v ∈ offHyp S U, ∀ a i j, ‖conn G₁ v (coordVec a) i j‖ * poinWt S v a ≤ c) → (∀ v ∈ offHyp S U, ∀ a b i j, ‖curv G₁ v (coordVec a) (coordVec b) i j‖ * (poinWt S v a * poinWt S v b) ≤ c) → ContDiffOn ℝ ∞ ρ U → (∀ v ∈ U, v ∉ K → ρ v = 0) → IntegrableOn (fun v => (ρ v : ℂ) * mixTop fun _ => curvAt G₁ v) (offHyp S U) := by
  first | exact @GlobalTheory.GoodTop.integrableOn_cut_mixTop_curvAt | exact GlobalTheory.GoodTop.integrableOn_cut_mixTop_curvAt | (intros; apply GlobalTheory.GoodTop.integrableOn_cut_mixTop_curvAt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodMetricCutTopChernDensityPatch

section

@[expose] public section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option autoImplicit false
noncomputable section

theorem GlobalTheory.GoodTop.hasInt_mul_topDens_goodPatch : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H H₀ : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), IsMetricOn E O H → IsMetricOn E ⊤ H₀ → ∀ {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)} {S : Finset (Fin X.dim)} {A : Mat (fun _ : Unit => m) X.Fn} {W : Set (CxPts X.str σ)} {c : ℝ}, GoodPatch E O H e S A W c → ∀ {ρ : CxPts X.str σ → ℝ}, (∀ y, CInfAt ρ y) → tsupport ρ ⊆ W → HasInt (fun c : AlgChart X.str σ X.dim => c.e) (fun c y => ρ y * topDens E H c y) (ptsIn X.str σ O) ((Real.pi ^ X.dim)⁻¹ * (∫ v in offHyp S (e '' W), (ρ (e.symm v) : ℂ) * mixTop fun _ => curvAt (fun v => H A (e.symm v) ()) v).re) := by
  intro F _ σ X m E O H H₀ hH hH₀ e S A W c hP ρ hρ hρW
  obtain ⟨hU, himg, hcpt⟩ := GlobalTheory.T.goodPatch_chart_image_properties E O H hP
  have hS : MeasurableSet (ptsIn X.str σ O) := (isOpen_ptsIn O).measurableSet
  have hd : ∀ i j : AlgChart X.str σ X.dim,
      DifferentiableOn ℂ (j.e ∘ i.e.symm) (i.e.target ∩ i.e.symm ⁻¹' j.e.source) := fun i j => i.holo_trans j
  have hcov : ∀ y, ∃ i : AlgChart X.str σ X.dim, y ∈ i.e.source := fun y => AlgChart.exists_mem_source y
  have hρc : Continuous ρ := continuous_iff_continuousAt.2 fun y => (hρ y).continuousAt
  have hρ0 : ∀ y, y ∉ W → ρ y = 0 := fun y hy => image_eq_zero_of_notMem_tsupport (fun h => hy (hρW h))
  set f : V X.dim → ℂ := fun v => (ρ (e.symm v) : ℂ) * mixTop fun _ => curvAt (fun v => H A (e.symm v) ()) v with hf
  have hint : IntegrableOn f (offHyp S (e '' W)) := by
    refine GlobalTheory.T.integrableOn_cutoff_topChernForm_poincareGrowth S (e '' W) (e '' tsupport ρ) (fun v => H₀ A (e.symm v) ()) (fun v => H A (e.symm v) ())
      (fun v => ρ (e.symm v)) c hU (hcpt _ (isClosed_tsupport ρ) hρW) (Set.image_mono hρW) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rintro _ ⟨z, hz, rfl⟩ a ha
      exact hP.small z hz a ha
    · rintro _ ⟨z, hz, rfl⟩
      exact GlobalTheory.T.gramMatrix_smooth_isUnit_in_holomorphicChart E ⊤ H₀ hH₀ hP.holo mem_ptsIn_top (hP.sub hz) (hP.frame z hz)
    · intro v hv
      rw [← himg] at hv
      obtain ⟨z, ⟨hzO, hz⟩, rfl⟩ := hv
      exact GlobalTheory.T.gramMatrix_smooth_isUnit_in_holomorphicChart E O H hH hP.holo hzO (hP.sub hz) (hP.frame z hz)
    · intro v hv
      rw [← himg] at hv
      obtain ⟨z, ⟨hzO, hz⟩, rfl⟩ := hv
      exact hP.form z hz hzO
    · intro v hv
      rw [← himg] at hv
      obtain ⟨z, ⟨hzO, hz⟩, rfl⟩ := hv
      exact hP.dbar z hz hzO
    · rintro _ ⟨z, hz, rfl⟩
      exact (GlobalTheory.T.contDiffAt_holomorphicComplexChart_of_smoothAt hP.holo (hP.sub hz) (hρ z)).contDiffWithinAt
    · rintro _ ⟨z, hz, rfl⟩ hK
      have hzK : z ∉ tsupport ρ := fun h => hK ⟨z, h, rfl⟩
      show ρ (e.symm (e z)) = 0
      rw [e.left_inv (hP.sub hz)]
      exact image_eq_zero_of_notMem_tsupport hzK
  have hre : IntegrableOn (fun v => (Real.pi ^ X.dim)⁻¹ * (f v).re) (offHyp S (e '' W)) :=
    (Integrable.re hint).const_mul _
  have key := GlobalTheory.T.topFormIntegral_of_support_in_holomorphicChart (fun c : AlgChart X.str σ X.dim => c.e) hd hcov hS
    (d := fun c y => ρ y * topDens E H c y) e W (fun v => (Real.pi ^ X.dim)⁻¹ * (f v).re) hP.isOpen hP.sub
    (fun j => GlobalTheory.T.differentiableOn_holomorphicChart_trans_etaleChart hP.holo j) (GlobalTheory.T.continuous_mul_top_chern_form_isTopDegree E O H hH hρc) ?_ ?_ (by rw [himg]; exact hre)
  · rw [himg, integral_const_mul] at key
    have h2 : ∫ v in offHyp S (e '' W), (f v).re = (∫ v in offHyp S (e '' W), f v).re := integral_re hint
    rw [h2] at key
    exact key
  · intro i y _ hy _
    simp [hρ0 y hy]
  · intro j y hyO hy hj
    have h1 := GlobalTheory.T.top_chern_density_holomorphic_chart_etale E O H hH hP.holo j hyO (hP.sub hy) hj (hP.frame y hy)
    simp only [hf, e.left_inv (hP.sub hy), Complex.re_ofReal_mul]
    rw [mul_left_comm, h1]
    ring
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodMetricCutTopChernDensityPatchStatement

section

@[expose] public section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

theorem _root_.GlobalTheory.T.goodMetric_cut_topChern_density_patch : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H H₀ : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), IsMetricOn E O H → IsMetricOn E ⊤ H₀ → ∀ {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)} {S : Finset (Fin X.dim)} {A : Mat (fun _ : Unit => m) X.Fn} {W : Set (CxPts X.str σ)} {c : ℝ}, GoodPatch E O H e S A W c → ∀ {ρ : CxPts X.str σ → ℝ}, (∀ y, CInfAt ρ y) → tsupport ρ ⊆ W → HasInt (fun c : AlgChart X.str σ X.dim => c.e) (fun c y => ρ y * topDens E H c y) (ptsIn X.str σ O) ((Real.pi ^ X.dim)⁻¹ * (∫ v in offHyp S (e '' W), (ρ (e.symm v) : ℂ) * mixTop fun _ => curvAt (fun v => H A (e.symm v) ()) v).re) := by
  first | exact @GlobalTheory.GoodTop.hasInt_mul_topDens_goodPatch | exact GlobalTheory.GoodTop.hasInt_mul_topDens_goodPatch | (intros; apply GlobalTheory.GoodTop.hasInt_mul_topDens_goodPatch <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodMetricLocalTransgressionFormulaStatement

section

@[expose] public section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

theorem _root_.GlobalTheory.T.goodMetric_local_transgression_formula : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (S : Finset (Fin n)) (U K : Set (V n)) (G₀ G₁ : V n → Matrix r r ℂ) (ρ : V n → ℝ) (c : ℝ), IsOpen U → IsCompact K → K ⊆ U → (∀ v ∈ U, ∀ a ∈ S, ‖v a‖ ≤ 1 / 2) → (∀ v ∈ U, MContDiffAt ∞ G₀ v ∧ IsUnit (G₀ v).det) → (∀ v ∈ offHyp S U, MContDiffAt ∞ G₁ v ∧ IsUnit (G₁ v).det) → (∀ v ∈ offHyp S U, ∀ a i j, ‖conn G₁ v (coordVec a) i j‖ * poinWt S v a ≤ c) → (∀ v ∈ offHyp S U, ∀ a b i j, ‖curv G₁ v (coordVec a) (coordVec b) i j‖ * (poinWt S v a * poinWt S v b) ≤ c) → ContDiffOn ℝ ∞ ρ U → (∀ v ∈ U, v ∉ K → ρ v = 0) → (∫ v in offHyp S U, (ρ v : ℂ) * mixTop fun _ => curvAt G₁ v) - (∫ v in U, (ρ v : ℂ) * mixTop fun _ => curvAt G₀ v) = ∫ v in offHyp S U, corrC ρ G₀ G₁ v := by
  first | exact @GlobalTheory.GoodTop.integral_cutTop_sub | exact GlobalTheory.GoodTop.integral_cutTop_sub | (intros; apply GlobalTheory.GoodTop.integral_cutTop_sub <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnCutoffTopChernFormSmoothGramStatement

section

@[expose] public section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

theorem _root_.GlobalTheory.T.integrableOn_cutoff_topChernForm_smoothGram : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (U K : Set (V n)) (G₀ : V n → Matrix r r ℂ) (ρ : V n → ℝ), IsOpen U → IsCompact K → K ⊆ U → (∀ v ∈ U, MContDiffAt ∞ G₀ v ∧ IsUnit (G₀ v).det) → ContDiffOn ℝ ∞ ρ U → (∀ v ∈ U, v ∉ K → ρ v = 0) → IntegrableOn (fun v => (ρ v : ℂ) * mixTop fun _ => curvAt G₀ v) U := by
  first | exact @GlobalTheory.GoodTop.integrableOn_cut_mixTop_smooth | exact GlobalTheory.GoodTop.integrableOn_cut_mixTop_smooth | (intros; apply GlobalTheory.GoodTop.integrableOn_cut_mixTop_smooth <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothMetricCutTopChernDensityPatch

section

@[expose] public section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option autoImplicit false

namespace GlobalTheory.GoodTop

theorem hasInt_cut_topDens_patch : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H H₀ : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), IsMetricOn E O H → IsMetricOn E ⊤ H₀ → ∀ {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)} {S : Finset (Fin X.dim)} {A : Mat (fun _ : Unit => m) X.Fn} {W : Set (CxPts X.str σ)} {c : ℝ}, GoodPatch E O H e S A W c → ∀ {ρ : CxPts X.str σ → ℝ}, (∀ y, CInfAt ρ y) → tsupport ρ ⊆ W → HasInt (fun c : AlgChart X.str σ X.dim => c.e) (fun c y => ρ y * topDens E H₀ c y) (ptsIn X.str σ ⊤) ((Real.pi ^ X.dim)⁻¹ * (∫ v in e '' W, (ρ (e.symm v) : ℂ) * mixTop fun _ => curvAt (fun v => H₀ A (e.symm v) ()) v).re) := by
  intro F _ σ X m E O H H₀ hH hH₀ e S A W c hp ρ hρ hsupp
  haveI := CxPts.secondCountableTopology_of_isProjOver σ X.isProjOver
  have hcont : Continuous ρ := continuous_iff_continuousAt.2 fun y => (hρ y).continuousAt
  have htop : ptsIn X.str σ ⊤ = Set.univ := Set.eq_univ_of_forall fun _ => mem_ptsIn_top
  set f : V X.dim → ℂ := fun v => (ρ (e.symm v) : ℂ) * mixTop fun _ => curvAt (fun v => H₀ A (e.symm v) ()) v with hf
  set g : V X.dim → ℝ := fun v => (Real.pi ^ X.dim)⁻¹ * (f v).re with hg
  obtain ⟨hUo, -, hK⟩ := GlobalTheory.T.goodPatch_chart_image_properties E O H hp

  have hfi : IntegrableOn f (e '' W) := by
    refine GlobalTheory.T.integrableOn_cutoff_topChernForm_smoothGram (e '' W) (e '' tsupport ρ) (fun v => H₀ A (e.symm v) ()) (fun v => ρ (e.symm v)) hUo
      (hK _ (isClosed_tsupport ρ) hsupp) (Set.image_mono hsupp) ?_ ?_ ?_
    · rintro _ ⟨z, hz, rfl⟩
      exact GlobalTheory.T.gramMatrix_smooth_isUnit_in_holomorphicChart E ⊤ H₀ hH₀ hp.holo mem_ptsIn_top (hp.sub hz) (hp.frame z hz)
    · rintro _ ⟨z, hz, rfl⟩
      exact (GlobalTheory.T.contDiffAt_holomorphicComplexChart_of_smoothAt hp.holo (hp.sub hz) (hρ z)).contDiffWithinAt
    · rintro _ ⟨z, hz, rfl⟩ hK'
      rw [e.left_inv (hp.sub hz)]
      by_contra h0
      exact hK' ⟨z, subset_tsupport ρ h0, rfl⟩
  have hgi : IntegrableOn g (e '' W) := hfi.re.const_mul _
  have key := GlobalTheory.T.topFormIntegral_of_support_in_holomorphicChart (fun c : AlgChart X.str σ X.dim => c.e)
    (fun i j => GlobalTheory.T.differentiableOn_holomorphicChart_trans_etaleChart i.holo j) (fun y => AlgChart.exists_mem_source y)
    (S := ptsIn X.str σ ⊤) (isOpen_ptsIn _).measurableSet (d := fun c y => ρ y * topDens E H₀ c y) e W g
    hp.isOpen hp.sub (fun j => GlobalTheory.T.differentiableOn_holomorphicChart_trans_etaleChart hp.holo j) (GlobalTheory.T.continuous_mul_top_chern_form_isTopDegree E ⊤ H₀ hH₀ hcont) ?_ ?_
    (by rw [htop, Set.univ_inter]; exact hgi)
  · rw [htop, Set.univ_inter] at key
    convert key using 1
    rw [hg, integral_const_mul]
    congr 1
    exact (integral_re hfi).symm
  · intro i y _ hyW _
    have : ρ y = 0 := by
      by_contra h0
      exact hyW (hsupp (subset_tsupport ρ h0))
    simp [this]
  · intro j y _ hyW hyj
    have ht := GlobalTheory.T.top_chern_density_holomorphic_chart_etale E ⊤ H₀ hH₀ hp.holo j mem_ptsIn_top (hp.sub hyW) hyj (hp.frame y hyW)
    simp only [hg, hf, e.left_inv (hp.sub hyW), Complex.re_ofReal_mul]
    rw [← mul_assoc, mul_comm _ (ρ y), mul_assoc, ht]
    ring

end GlobalTheory.GoodTop
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothMetricCutTopChernDensityPatchStatement

section

@[expose] public section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

theorem _root_.GlobalTheory.T.smoothMetric_cut_topChern_density_patch : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H H₀ : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), IsMetricOn E O H → IsMetricOn E ⊤ H₀ → ∀ {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)} {S : Finset (Fin X.dim)} {A : Mat (fun _ : Unit => m) X.Fn} {W : Set (CxPts X.str σ)} {c : ℝ}, GoodPatch E O H e S A W c → ∀ {ρ : CxPts X.str σ → ℝ}, (∀ y, CInfAt ρ y) → tsupport ρ ⊆ W → HasInt (fun c : AlgChart X.str σ X.dim => c.e) (fun c y => ρ y * topDens E H₀ c y) (ptsIn X.str σ ⊤) ((Real.pi ^ X.dim)⁻¹ * (∫ v in e '' W, (ρ (e.symm v) : ℂ) * mixTop fun _ => curvAt (fun v => H₀ A (e.symm v) ()) v).re) := by
  first | exact @GlobalTheory.GoodTop.hasInt_cut_topDens_patch | exact GlobalTheory.GoodTop.hasInt_cut_topDens_patch | (intros; apply GlobalTheory.GoodTop.hasInt_cut_topDens_patch <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransgressionTopChernFormGoodPatch

section

@[expose] public section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem hasInt_patch_transgression : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H H₀ : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), IsMetricOn E O H → IsMetricOn E ⊤ H₀ → ∀ {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)} {S : Finset (Fin X.dim)} {A : Mat (fun _ : Unit => m) X.Fn} {W : Set (CxPts X.str σ)} {c : ℝ}, GoodPatch E O H e S A W c → ∀ {ρ : CxPts X.str σ → ℝ}, (∀ y, CInfAt ρ y) → tsupport ρ ⊆ W → ∃ a b : ℝ, HasInt (fun c : AlgChart X.str σ X.dim => c.e) (fun c y => ρ y * topDens E H c y) (ptsIn X.str σ O) a ∧ HasInt (fun c : AlgChart X.str σ X.dim => c.e) (fun c y => ρ y * topDens E H₀ c y) (ptsIn X.str σ ⊤) b ∧ HasInt (fun c : AlgChart X.str σ X.dim => c.e) (corrDens E H₀ H ρ) (ptsIn X.str σ O) (a - b) := by
  intro F _ σ X m E O H H₀ hH hH₀ e S A W c hP ρ hρ hsupp
  obtain ⟨hUo, hUoff, hcpt⟩ := GlobalTheory.T.goodPatch_chart_image_properties E O H hP
  have h1 := GlobalTheory.T.goodMetric_cut_topChern_density_patch E O H H₀ hH hH₀ hP hρ hsupp
  have h0 := GlobalTheory.T.smoothMetric_cut_topChern_density_patch E O H H₀ hH hH₀ hP hρ hsupp
  have hc := GlobalTheory.T.transgression_term_density_good_patch E O H H₀ hH hH₀ hP hρ hsupp
  refine ⟨_, _, h1, h0, ?_⟩
  have hloc := GlobalTheory.T.goodMetric_local_transgression_formula S (e '' W) (e '' tsupport ρ) (fun v => H₀ A (e.symm v) ()) (fun v => H A (e.symm v) ())
    (fun v => ρ (e.symm v)) c hUo (hcpt _ (isClosed_tsupport ρ) hsupp) (Set.image_mono hsupp)
    (by
      rintro v ⟨z, hz, rfl⟩ a ha
      exact hP.small z hz a ha)
    (by
      rintro v ⟨z, hz, rfl⟩
      exact GlobalTheory.T.gramMatrix_smooth_isUnit_in_holomorphicChart E ⊤ H₀ hH₀ hP.holo mem_ptsIn_top (hP.sub hz) (hP.frame z hz))
    (by
      intro v hv
      rw [← hUoff] at hv
      obtain ⟨z, ⟨hzO, hz⟩, rfl⟩ := hv
      exact GlobalTheory.T.gramMatrix_smooth_isUnit_in_holomorphicChart E O H hH hP.holo hzO (hP.sub hz) (hP.frame z hz))
    (by
      intro v hv a i j
      rw [← hUoff] at hv
      obtain ⟨z, ⟨hzO, hz⟩, rfl⟩ := hv
      exact hP.form z hz hzO a i j)
    (by
      intro v hv a b i j
      rw [← hUoff] at hv
      obtain ⟨z, ⟨hzO, hz⟩, rfl⟩ := hv
      exact hP.dbar z hz hzO a b i j)
    (by
      rintro v ⟨z, hz, rfl⟩
      exact (GlobalTheory.T.contDiffAt_holomorphicComplexChart_of_smoothAt hP.holo (hP.sub hz) (hρ z)).contDiffWithinAt)
    (by
      rintro v ⟨z, hz, rfl⟩ hv
      rw [e.left_inv (hP.sub hz)]
      by_contra h
      exact hv ⟨z, subset_tsupport _ h, rfl⟩)
  convert hc using 1
  rw [← mul_sub, ← Complex.sub_re, hloc]

end GlobalTheory.GoodTop
end
end
