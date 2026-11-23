module

public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPtsBddConv
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Weights
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.ModelProjObjects
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ChartIntegralPotentialLocallyFinite
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
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FiniteFibresOfAnalyticLocalDiffeoStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LocDensDivJacN
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.Topology.Separation.CompletelyRegular
import ReciprocityTheory.AnalyticForms.PotentialTheory.Partition
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MeasurableFibreCountOfLocalDiffeoStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDensityNonnegOffNullSet
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothLocalPotentialLiftStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.VolumeModelCritChartEqZeroStatement
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFib

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.ChartIntegralPotentialLocallyFiniteStatement

section

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

theorem _root_.GlobalTheory.T.chart_integral_potential_locally_finite : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ) (M : CxModel P n) (Q : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (Y Z : Set M.Xc) (N : Set ((Σ k, ι k) → ℂ)) (c : Fin n → ℝ) (B : Fin n → HermLine ι) (Φ : Fin n → LocPot M.Xc) (g : ((Σ k, ι k) → ℂ) → ℝ) (G₀ : M.Xc → ℝ), IsArithVar P (n + 1) → IsGoodProj P Q → IsOpen Y → (∀ j, volume ((M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' (Yᶜ ∪ Z)) = 0) → IsPtsNull P n N → (∀ i x, M.atlas.SmoothOn ((Φ i).U x ∩ Y) ((Φ i).φ x)) → (∀ i, ∀ x, ∀ y₀ ∈ (Φ i).U x ∩ Y, ∃ U : Set M.Xc, IsOpen U ∧ y₀ ∈ U ∧ U ⊆ (Φ i).U x ∩ Y ∧ ∃ s : M.Xc → (Σ k, ι k) → ℂ, (∀ y' ∈ U, s y' ∈ mcPts (P) ∧ M.proj (s y') = y') ∧ (∀ p, M.atlas.HoloOn U fun y' => s y' p) ∧ ∃ G : M.Xc → ℂ, M.atlas.HoloOn U G ∧ ∀ y' ∈ U, (Φ i).φ x y' - (fun z => c i * Real.log ((B i).h z)) (s y') = (G y').re) → (∀ z ∈ mcPts P, z ∉ N → M.proj z ∈ Y → M.proj z ∉ Z → g z = G₀ (M.proj z)) → ∀ᵐ y, ∃ W : M.Xc → (((k : K) → ι k) → ℂ), Set.InjOn W (modelQ M Q ⁻¹' {y} \ modelBad M Q (Yᶜ ∪ Z)) ∧ fibre P Q y = W '' (modelQ M Q ⁻¹' {y} \ modelBad M Q (Yᶜ ∪ Z)) ∧ ∀ x ∈ modelQ M Q ⁻¹' {y} \ modelBad M Q (Yᶜ ∪ Z), sheetDensity P Q (fun i z => c i * Real.log ((B i).h z)) g y (W x) = G₀ x * pushDens M.atlas Φ (modelQ M Q) x := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.Push.fibre_term_ae | exact GlobalTheory.CompanionTheory.Ar.Giv.Push.fibre_term_ae | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.Push.fibre_term_ae <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.IntegralFibreSumChangeOfVariables

section

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.Giv.Push

theorem integrable_mInt_fibreSum {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) (q : X → Fin e → ℂ) (S : Set X) (G : X → ℝ)
    (hS : ∀ j, volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' S) = 0)
    (hq : ∀ x ∉ S, ∀ j, x ∈ (A.chart j).source →
      AnalyticAt ℂ (q ∘ (A.chart j).symm) (A.chart j x) ∧
        LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) (A.chart j x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0)
    (hfin : ∀ y, (q ⁻¹' {y} \ S).Finite)
    (hsm : ∀ x ∉ S, ∀ i k, x ∈ (A.chart k).source →
      ContDiffAt ℝ 2 ((Φ i).φ x ∘ (A.chart k).symm) (A.chart k x))
    (hG : MIntegrable A Φ G) :
    Integrable (fun y => ∑ᶠ x ∈ q ⁻¹' {y} \ S, G x * pushDens A Φ q x) ∧
      mInt A Φ G = ∫ y, ∑ᶠ x ∈ q ⁻¹' {y} \ S, G x * pushDens A Φ q x := by
  classical
  have hne : Nonempty (ChartPartition A) := existsPartition A
  have hm : mInt A Φ G = integralWith A hne.some Φ G := by unfold mInt; rw [dite_eq_left hne]
  set Pt := hne.some with hPt
  set hj : Fin A.n → (Fin e → ℂ) → ℝ := fun j u =>
    Pt.χ j ((A.chart j).symm u) * G ((A.chart j).symm u) * locDens A Φ j u with hhj
  have hN : ∀ j, volume ((q ∘ (A.chart j).symm) '' (goodT A q j ∩ (A.chart j).symm ⁻¹' S)) = 0 := by
    intro j
    refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_ ?_
    · intro u hu
      exact (hu.1.2.1.differentiableAt.restrictScalars ℝ).differentiableWithinAt
    · exact measure_mono_null (Set.inter_subset_inter_left _ fun u (hu : u ∈ goodT A q j) => hu.1)
        (hS j)
  have hfinj : ∀ j, ∀ᵐ y, (goodT A q j ∩ (q ∘ (A.chart j).symm) ⁻¹' {y}).Finite := by
    intro j
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp (hN j)] with y hy
    rw [goodT_fibre_eq A q S hq j hy]
    exact ((hfin y).subset Set.inter_subset_right).image _
  have harea : ∀ j, Integrable (fibSum (goodT A q j) (q ∘ (A.chart j).symm) (hj j)) ∧
      ∫ u in goodT A q j, hj j u = ∫ y, fibSum (goodT A q j) (q ∘ (A.chart j).symm) (hj j) y :=
    fun j => area_open (isOpen_goodT A q j) (fun u hu => hu.2)
      ((integrableOn_chart A Pt Φ G hG j).mono_set fun u hu => hu.1) (hfinj j)
  have hset : ∀ j, ∫ u in (A.chart j).target, hj j u = ∫ u in goodT A q j, hj j u := by
    intro j
    refine setIntegral_congr_set (ae_eq_set.mpr ⟨?_, ?_⟩)
    · exact measure_mono_null (target_diff_goodT_subset A q S hq j) (hS j)
    · rw [Set.sdiff_eq_empty.mpr fun u (hu : u ∈ goodT A q j) => hu.1]; exact measure_empty
  have hterm : ∀ j x, x ∈ (A.chart j).source → x ∉ S →
      hj j (A.chart j x) / jacN (q ∘ (A.chart j).symm) (A.chart j x) =
        Pt.χ j x * (G x * pushDens A Φ q x) := by
    intro j x hx hxS
    simp only [hhj, (A.chart j).left_inv hx]
    rw [mul_div_assoc, locDens_div_jacN A Φ q S hq hsm j hx hxS, mul_assoc]
  have hae := sum_fibSum_ae A q S hN hq hfin Pt hj (fun x => G x * pushDens A Φ q x) hterm
  refine ⟨(integrable_finsetSum Finset.univ fun j _ => (harea j).1).congr hae, ?_⟩
  rw [hm]
  unfold integralWith
  have hsum : ∑ j, ∫ u in (A.chart j).target, hj j u =
      ∫ y, ∑ j, fibSum (goodT A q j) (q ∘ (A.chart j).symm) (hj j) y := by
    rw [integral_finsetSum _ fun j _ => (harea j).1]
    exact Finset.sum_congr rfl fun j _ => (hset j).trans (harea j).2
  exact hsum.trans (integral_congr_ae hae)

end GlobalTheory.CompanionTheory.Ar.Giv.Push
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.IntegralFibreSumChangeOfVariablesStatement

section

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

theorem _root_.GlobalTheory.T.integral_fibre_sum_change_of_variables : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) (q : X → Fin e → ℂ) (S : Set X) (G : X → ℝ), (∀ j, volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' S) = 0) → (∀ x ∉ S, ∀ j, x ∈ (A.chart j).source → AnalyticAt ℂ (q ∘ (A.chart j).symm) (A.chart j x) ∧ LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) (A.chart j x) : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0) → (∀ y, (q ⁻¹' {y} \ S).Finite) → (∀ x ∉ S, ∀ i k, x ∈ (A.chart k).source → ContDiffAt ℝ 2 ((Φ i).φ x ∘ (A.chart k).symm) (A.chart k x)) → MIntegrable A Φ G → Integrable (fun y => ∑ᶠ x ∈ q ⁻¹' {y} \ S, G x * pushDens A Φ q x) ∧ mInt A Φ G = ∫ y, ∑ᶠ x ∈ q ⁻¹' {y} \ S, G x * pushDens A Φ q x := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.Push.integrable_mInt_fibreSum | exact GlobalTheory.CompanionTheory.Ar.Giv.Push.integrable_mInt_fibreSum | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.Push.integrable_mInt_fibreSum <;> assumption)
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsModelFibreFinite

section

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

def ModelFibreFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (M : CxModel P e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsArithVar P (e + 1) → IsGoodProj P Ψ → ∀ y, (modelQ M Ψ ⁻¹' {y} \ modelCrit M Ψ).Finite

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PModelFibreFinite

section

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

theorem ModelFibreFinite.proof : ModelFibreFinite.Statement := by
  intro K _ ι _ P e M Ψ hP hΨ y
  classical
  obtain ⟨k0⟩ := hP.1
  have hH : IsMultiHomogIdeal P := hP.2.1.2.1
  let f : M.Xc → (((k : K) → ι k) → ℂ) := fun x =>
    (Ψ (segre (modelLift M x x)) 0)⁻¹ • segre (modelLift M x x)
  refine Set.Finite.of_finite_image (f := f) ((fibreFinite K ι P e Ψ hP hΨ y).subset ?_) ?_
  · rintro _ ⟨x, ⟨hxy, hx0⟩, rfl⟩
    have hq : modelQ M Ψ x = y := hxy
    have hl := (modelLift_spec M x).1 x (mem_modelU M x)
    have hlam : Ψ (segre (modelLift M x x)) 0 ≠ 0 := fun h => hx0 (Or.inl h)
    refine ⟨fun p => Function.update (1 : K → ℂ) k0 (Ψ (segre (modelLift M x x)) 0)⁻¹ p.1 *
      modelLift M x x p, mcPts_smul hH _ ?_ hl.1, ?_, ?_⟩
    · intro k
      by_cases hk : k = k0
      · subst hk
        simp [hlam]
      · simp [Function.update_of_ne hk]
    · rw [segre_smul, Finset.prod_update_of_mem (Finset.mem_univ _)]
      simp [f]
    · show Ψ ((Ψ (segre (modelLift M x x)) 0)⁻¹ • segre (modelLift M x x)) = Fin.cons 1 y
      rw [map_smul]
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [hlam]
      · rw [← hq]
        simp [modelQ, div_eq_inv_mul]
  · rintro x1 ⟨_, h1⟩ x2 ⟨_, h2⟩ heq
    have l1 := (modelLift_spec M x1).1 x1 (mem_modelU M x1)
    have l2 := (modelLift_spec M x2).1 x2 (mem_modelU M x2)
    have hlam1 : Ψ (segre (modelLift M x1 x1)) 0 ≠ 0 := fun h => h1 (Or.inl h)
    have hlam2 : Ψ (segre (modelLift M x2 x2)) 0 ≠ 0 := fun h => h2 (Or.inl h)
    have hseg : segre (modelLift M x1 x1) =
        (Ψ (segre (modelLift M x1 x1)) 0 / Ψ (segre (modelLift M x2 x2)) 0) •
          segre (modelLift M x2 x2) := by
      have := congrArg (fun w => Ψ (segre (modelLift M x1 x1)) 0 • w) heq
      simp only [f, smul_smul, mul_inv_cancel₀ hlam1, one_smul] at this
      rw [div_eq_mul_inv]
      exact this
    obtain ⟨c, hc, hcz⟩ := sameOrbit_of_segre l2.1.1 _ (div_ne_zero hlam1 hlam2) hseg
    rw [← l1.2, ← l2.2]
    exact ((M.fibre _ l2.1 _ l1.1).2 ⟨c, hc, hcz⟩).symm

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedIntegralModelFormula

section

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem push_chart_integrals : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ) (M : CxModel P n) (Q : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (Y Z : Set M.Xc) (N : Set ((Σ k, ι k) → ℂ)) (c : Fin n → ℝ) (B : Fin n → HermLine ι) (Φ : Fin n → LocPot M.Xc) (g : ((Σ k, ι k) → ℂ) → ℝ) (G₀ : M.Xc → ℝ), IsArithVar P (n + 1) → IsGoodProj P Q → IsOpen Y → (∀ j, volume ((M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' (Yᶜ ∪ Z)) = 0) → IsPtsNull P n N → (∀ i x, M.atlas.SmoothOn ((Φ i).U x ∩ Y) ((Φ i).φ x)) → (∀ i, ∀ x, ∀ y₀ ∈ (Φ i).U x ∩ Y, ∃ U : Set M.Xc, IsOpen U ∧ y₀ ∈ U ∧ U ⊆ (Φ i).U x ∩ Y ∧ ∃ s : M.Xc → (Σ k, ι k) → ℂ, (∀ y' ∈ U, s y' ∈ mcPts (P) ∧ M.proj (s y') = y') ∧ (∀ p, M.atlas.HoloOn U fun y' => s y' p) ∧ ∃ G : M.Xc → ℂ, M.atlas.HoloOn U G ∧ ∀ y' ∈ U, (Φ i).φ x y' - (fun z => c i * Real.log ((B i).h z)) (s y') = (G y').re) → (∀ z ∈ mcPts P, z ∉ N → M.proj z ∈ Y → M.proj z ∉ Z → g z = G₀ (M.proj z)) → (∀ j, AEStronglyMeasurable (G₀ ∘ (M.atlas.chart j).symm) (volume.restrict (M.atlas.chart j).target)) → AEStronglyMeasurable (fun y => ∑ᶠ w ∈ fibre P Q y, sheetDensity P Q (fun i z => c i * Real.log ((B i).h z)) g y w) volume ∧ (∀ Pt : ChartPartition M.atlas, ∫⁻ y, ENNReal.ofReal (∑ᶠ w ∈ fibre P Q y, |sheetDensity P Q (fun i z => c i * Real.log ((B i).h z)) g y w|) = ∑ j, ∫⁻ u in (M.atlas.chart j).target, ENNReal.ofReal |Pt.χ j ((M.atlas.chart j).symm u) * G₀ ((M.atlas.chart j).symm u) * locDens M.atlas (Φ) j u|) ∧ (MIntegrable M.atlas Φ G₀ → Integrable (fun y => ∑ᶠ w ∈ fibre P Q y, sheetDensity P Q (fun i z => c i * Real.log ((B i).h z)) g y w) ∧ ptsIntegralAt P Q (fun i z => c i * Real.log ((B i).h z)) g = mInt M.atlas Φ G₀) := by
  intro K _ ι _ P n M Q Y Z N c B Φ g G₀ hP hQ hY hnull hN hΦs hΦt hg hG
  have hS : ∀ j, volume ((M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' modelBad M Q (Yᶜ ∪ Z)) = 0 := by
    intro j
    rw [modelBad, Set.preimage_union, Set.inter_union_distrib_left]
    exact measure_union_null (hnull j) (GlobalTheory.T.volume_modelCrit_chart_eq_zero K ι P n M Q j hP hQ)
  have hq := modelQ_good_of_notMem M Q (Yᶜ ∪ Z)
  have hfin : ∀ y, (modelQ M Q ⁻¹' {y} \ modelBad M Q (Yᶜ ∪ Z)).Finite := fun y =>
    (ModelFibreFinite.proof K ι P n M Q hP hQ y).subset (Set.sdiff_subset_sdiff_right Set.subset_union_right)
  have hYof : ∀ x ∉ modelBad M Q (Yᶜ ∪ Z), x ∈ Y := fun x hx => by
    by_contra h
    exact hx (Or.inl (Or.inl h))
  have hsm : ∀ x ∉ modelBad M Q (Yᶜ ∪ Z), ∀ i k, x ∈ (M.atlas.chart k).source →
      ContDiffAt ℝ 2 ((Φ i).φ x ∘ (M.atlas.chart k).symm) (M.atlas.chart k x) := by
    intro x hx i k hk
    have hxk : (M.atlas.chart k).symm (M.atlas.chart k x) = x := (M.atlas.chart k).left_inv hk
    have hmem : M.atlas.chart k x ∈ (M.atlas.chart k).target ∩ (M.atlas.chart k).symm ⁻¹' ((Φ i).U x ∩ Y) :=
      ⟨(M.atlas.chart k).map_source hk, by
        rw [Set.mem_preimage, hxk]; exact ⟨(Φ i).mem_U x, hYof x hx⟩⟩
    have hop := (M.atlas.chart k).isOpen_inter_preimage_symm (((Φ i).isOpen_U x).inter hY)
    exact ((hΦs i x k).contDiffAt (hop.mem_nhds hmem)).of_le (WithTop.coe_le_coe.2 le_top)
  have hYnull : ∀ j, volume ((M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' Yᶜ) = 0 := fun j =>
    measure_mono_null (Set.inter_subset_inter_right _ (Set.preimage_mono Set.subset_union_left)) (hnull j)
  have hm : ∀ j, AEStronglyMeasurable (fun u => G₀ ((M.atlas.chart j).symm u) * locDens M.atlas Φ j u)
      (volume.restrict (M.atlas.chart j).target) := by
    intro j
    let _ : MeasurableSpace M.Xc := borel M.Xc
    have : BorelSpace M.Xc := ⟨rfl⟩
    refine AEStronglyMeasurable.mul (hG j) ?_
    rw [MeasOff.restrict_target_eq M.atlas hYnull j]
    exact ((GlobalTheory.T.smooth_local_potential_lift K ι P n M Y c B Φ j hY hΦs hΦt).aestronglyMeasurable
      (MeasOff.isOpen_ov M.atlas hY j).measurableSet)
  have hae := GlobalTheory.T.chart_integral_potential_locally_finite K ι P n M Q Y Z N c B Φ g G₀ hP hQ hY hnull hN hΦs hΦt hg
  have e1 : ∀ᵐ y, ∑ᶠ w ∈ fibre P Q y, sheetDensity P Q (fun i z => c i * Real.log ((B i).h z)) g y w =
      ∑ᶠ x ∈ modelQ M Q ⁻¹' {y} \ modelBad M Q (Yᶜ ∪ Z), G₀ x * pushDens M.atlas Φ (modelQ M Q) x := by
    filter_upwards [hae] with y ⟨W, hW, hf, ht⟩
    rw [hf, finsum_mem_image hW]
    exact finsum_mem_congr rfl ht
  have e2 : ∀ᵐ y, ∑ᶠ w ∈ fibre P Q y, |sheetDensity P Q (fun i z => c i * Real.log ((B i).h z)) g y w| =
      ∑ᶠ x ∈ modelQ M Q ⁻¹' {y} \ modelBad M Q (Yᶜ ∪ Z), |G₀ x * pushDens M.atlas Φ (modelQ M Q) x| := by
    filter_upwards [hae] with y ⟨W, hW, hf, ht⟩
    rw [hf, finsum_mem_image hW]
    exact finsum_mem_congr rfl fun x hx => by rw [ht x hx]
  refine ⟨(GlobalTheory.T.measurable_fibre_count_of_local_diffeo M.atlas Φ (modelQ M Q) _ G₀ hS hq hfin hsm hm).congr (e1.mono fun y hy => hy.symm),
    fun Pt => ?_, fun hI => ?_⟩
  · rw [lintegral_congr_ae (e2.mono fun y hy => congrArg ENNReal.ofReal hy)]
    exact GlobalTheory.T.finite_fibres_of_analytic_local_diffeo M.atlas Φ (modelQ M Q) _ G₀ hS hq hfin hsm hm Pt
  · obtain ⟨h1, h2⟩ := GlobalTheory.T.integral_fibre_sum_change_of_variables M.atlas Φ (modelQ M Q) _ G₀ hS hq hfin hsm hI
    refine ⟨h1.congr (e1.mono fun y hy => hy.symm), ?_⟩
    rw [h2]
    exact integral_congr_ae (e1.mono fun y hy => hy)

end GlobalTheory.CompanionTheory.Ar.Giv
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedIntegralModelFormulaStatement

section

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

theorem _root_.GlobalTheory.T.mixed_integral_model_formula : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ) (M : CxModel P n) (Q : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (Y Z : Set M.Xc) (N : Set ((Σ k, ι k) → ℂ)) (c : Fin n → ℝ) (B : Fin n → HermLine ι) (Φ : Fin n → LocPot M.Xc) (g : ((Σ k, ι k) → ℂ) → ℝ) (G₀ : M.Xc → ℝ), IsArithVar P (n + 1) → IsGoodProj P Q → IsOpen Y → (∀ j, volume ((M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' (Yᶜ ∪ Z)) = 0) → IsPtsNull P n N → (∀ i x, M.atlas.SmoothOn ((Φ i).U x ∩ Y) ((Φ i).φ x)) → (∀ i, ∀ x, ∀ y₀ ∈ (Φ i).U x ∩ Y, ∃ U : Set M.Xc, IsOpen U ∧ y₀ ∈ U ∧ U ⊆ (Φ i).U x ∩ Y ∧ ∃ s : M.Xc → (Σ k, ι k) → ℂ, (∀ y' ∈ U, s y' ∈ mcPts (P) ∧ M.proj (s y') = y') ∧ (∀ p, M.atlas.HoloOn U fun y' => s y' p) ∧ ∃ G : M.Xc → ℂ, M.atlas.HoloOn U G ∧ ∀ y' ∈ U, (Φ i).φ x y' - (fun z => c i * Real.log ((B i).h z)) (s y') = (G y').re) → (∀ z ∈ mcPts P, z ∉ N → M.proj z ∈ Y → M.proj z ∉ Z → g z = G₀ (M.proj z)) → (∀ j, AEStronglyMeasurable (G₀ ∘ (M.atlas.chart j).symm) (volume.restrict (M.atlas.chart j).target)) → AEStronglyMeasurable (fun y => ∑ᶠ w ∈ fibre P Q y, sheetDensity P Q (fun i z => c i * Real.log ((B i).h z)) g y w) volume ∧ (∀ Pt : ChartPartition M.atlas, ∫⁻ y, ENNReal.ofReal (∑ᶠ w ∈ fibre P Q y, |sheetDensity P Q (fun i z => c i * Real.log ((B i).h z)) g y w|) = ∑ j, ∫⁻ u in (M.atlas.chart j).target, ENNReal.ofReal |Pt.χ j ((M.atlas.chart j).symm u) * G₀ ((M.atlas.chart j).symm u) * locDens M.atlas (Φ) j u|) ∧ (MIntegrable M.atlas Φ G₀ → Integrable (fun y => ∑ᶠ w ∈ fibre P Q y, sheetDensity P Q (fun i z => c i * Real.log ((B i).h z)) g y w) ∧ ptsIntegralAt P Q (fun i z => c i * Real.log ((B i).h z)) g = mInt M.atlas Φ G₀) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.push_chart_integrals | exact GlobalTheory.CompanionTheory.Ar.Giv.push_chart_integrals | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.push_chart_integrals <;> assumption)
end
end
