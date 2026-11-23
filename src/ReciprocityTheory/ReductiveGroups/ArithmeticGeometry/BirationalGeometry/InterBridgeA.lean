module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeJ
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeO
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeD
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeE
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeF
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.Topology.Separation.CompletelyRegular
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Partition
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeH
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.MeasureTheory.Function.Jacobian
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeG
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AnResBridgeNull
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Tactic.Linter.Style
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.NullZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeL
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeN
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeQ
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterPCProof
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeI

section

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm.M

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem pushForward_null' [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (q : X → Fin e → ℂ) (S : Set X)
    (hS : ∀ j, volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' S) = 0)
    (hq : ∀ x ∉ S, ∀ j, x ∈ (A.chart j).source →
      AnalyticAt ℂ (q ∘ (A.chart j).symm) (A.chart j x) ∧
        LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) (A.chart j x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0)
    (hfin : ∀ y, (q ⁻¹' {y} \ S).Finite) (g : X → ℝ) (hg : MIntegrable A Φ g) :
    mInt A Φ g = ∫ y, ∑ᶠ x ∈ q ⁻¹' {y} \ S, g x * pushDens A Φ q x := by
  classical
  have hne : Nonempty (ChartPartition A) := existsPartition A
  rw [mInt, dite_eq_left hne, integralWith]
  generalize hne.some = Pt
  have hnull : ∀ j, volume ((q ∘ (A.chart j).symm) '' (goodT A q j ∩ (A.chart j).symm ⁻¹' S)) = 0 := by
    intro j
    refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero (μ := volume) ?_ ?_
    · intro u hu
      exact (hu.1.2.1.differentiableAt.restrictScalars ℝ).differentiableWithinAt
    · exact measure_mono_null
        (show goodT A q j ∩ (A.chart j).symm ⁻¹' S ⊆ (A.chart j).target ∩ (A.chart j).symm ⁻¹' S from
          fun u hu => ⟨hu.1.1, hu.2⟩) (hS j)
  have hfinj : ∀ j, ∀ᵐ y ∂(volume : Measure (Fin e → ℂ)),
      (goodT A q j ∩ (q ∘ (A.chart j).symm) ⁻¹' {y}).Finite := by
    intro j
    filter_upwards [compl_mem_ae_iff.2 (hnull j)] with y hy
    rw [goodT_fibre_eq A q S hq j hy]
    exact ((hfin y).subset inter_subset_right).image _
  have harea : ∀ j, Integrable (fibSum (goodT A q j) (q ∘ (A.chart j).symm) (fun u => Pt.χ j ((A.chart j).symm u) * g ((A.chart j).symm u) * locDens A Φ j u)) ∧
      ∫ u in goodT A q j, Pt.χ j ((A.chart j).symm u) * g ((A.chart j).symm u) * locDens A Φ j u = ∫ y, fibSum (goodT A q j) (q ∘ (A.chart j).symm) (fun u => Pt.χ j ((A.chart j).symm u) * g ((A.chart j).symm u) * locDens A Φ j u) y := fun j =>
    area_open (isOpen_goodT A q j) (fun u hu => hu.2)
      ((integrableOn_chart A Pt Φ g hg j).mono_set (fun u hu => hu.1)) (hfinj j)
  have htarget : ∀ j, ∫ u in (A.chart j).target, Pt.χ j ((A.chart j).symm u) * g ((A.chart j).symm u) * locDens A Φ j u = ∫ u in goodT A q j, Pt.χ j ((A.chart j).symm u) * g ((A.chart j).symm u) * locDens A Φ j u := by
    intro j
    apply setIntegral_congr_set
    rw [ae_eq_set]
    refine ⟨measure_mono_null (target_diff_goodT_subset A q S hq j) (hS j), ?_⟩
    rw [diff_eq_empty.2 (show goodT A q j ⊆ (A.chart j).target from fun u hu => hu.1)]
    exact measure_empty
  have hj : ∀ j y, y ∉ (q ∘ (A.chart j).symm) '' (goodT A q j ∩ (A.chart j).symm ⁻¹' S) →
      fibSum (goodT A q j) (q ∘ (A.chart j).symm) (fun u => Pt.χ j ((A.chart j).symm u) * g ((A.chart j).symm u) * locDens A Φ j u) y =
        ∑ᶠ x ∈ q ⁻¹' {y} \ S, Pt.χ j x * (g x * pushDens A Φ q x) := by
    intro j y hy
    unfold fibSum
    rw [goodT_fibre_eq A q S hq j hy, finsum_mem_image ((A.chart j).injOn.mono inter_subset_left)]
    calc _ = ∑ᶠ x ∈ (A.chart j).source ∩ (q ⁻¹' {y} \ S), Pt.χ j x * (g x * pushDens A Φ q x) :=
          finsum_mem_congr rfl (fun x hx => fib_term A Φ hΦ q S hq Pt g j hx.1 hx.2.2)
      _ = _ := by
          apply finsum_mem_inter_support_eq
          ext x
          simp only [mem_inter_iff, Function.mem_support]
          constructor
          · rintro ⟨⟨_, h2⟩, h3⟩
            exact ⟨h2, h3⟩
          · rintro ⟨h2, h3⟩
            exact ⟨⟨Pt.tsupport_subset j (subset_tsupport _ (left_ne_zero_of_mul h3)), h2⟩, h3⟩
  have hae : ∀ᵐ y ∂(volume : Measure (Fin e → ℂ)),
      ∀ j, y ∉ (q ∘ (A.chart j).symm) '' (goodT A q j ∩ (A.chart j).symm ⁻¹' S) := by
    rw [ae_all_iff]
    intro j
    exact compl_mem_ae_iff.2 (hnull j)
  calc ∑ j, ∫ u in (A.chart j).target, Pt.χ j ((A.chart j).symm u) * g ((A.chart j).symm u) * locDens A Φ j u
      = ∑ j, ∫ y, fibSum (goodT A q j) (q ∘ (A.chart j).symm) (fun u => Pt.χ j ((A.chart j).symm u) * g ((A.chart j).symm u) * locDens A Φ j u) y :=
        Finset.sum_congr rfl (fun j _ => (htarget j).trans (harea j).2)
    _ = ∫ y, ∑ j, fibSum (goodT A q j) (q ∘ (A.chart j).symm) (fun u => Pt.χ j ((A.chart j).symm u) * g ((A.chart j).symm u) * locDens A Φ j u) y :=
        (MeasureTheory.integral_finsetSum _ (fun j _ => (harea j).1)).symm
    _ = ∫ y, ∑ᶠ x ∈ q ⁻¹' {y} \ S, g x * pushDens A Φ q x := by
        apply integral_congr_ae
        filter_upwards [hae] with y hy
        have hF := hfin y
        calc ∑ j, fibSum (goodT A q j) (q ∘ (A.chart j).symm) (fun u => Pt.χ j ((A.chart j).symm u) * g ((A.chart j).symm u) * locDens A Φ j u) y
            = ∑ j, ∑ᶠ x ∈ q ⁻¹' {y} \ S, Pt.χ j x * (g x * pushDens A Φ q x) :=
              Finset.sum_congr rfl (fun j _ => hj j y (hy j))
          _ = ∑ j, ∑ x ∈ hF.toFinset, Pt.χ j x * (g x * pushDens A Φ q x) :=
              Finset.sum_congr rfl (fun j _ => finsum_mem_eq_finite_toFinset_sum _ hF)
          _ = ∑ x ∈ hF.toFinset, g x * pushDens A Φ q x := by
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl (fun x _ => ?_)
              rw [← Finset.sum_mul, Pt.sum_eq_one, one_mul]
          _ = ∑ᶠ x ∈ q ⁻¹' {y} \ S, g x * pushDens A Φ q x :=
              (finsum_mem_eq_finite_toFinset_sum _ hF).symm

end ReciprocityTheory.ChartRestriction.G.Geo
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeM

section

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M Topology Filter Set

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P J : Ideal (MRing ι)} {e : ℕ} (R : AnLogRes P J e)

theorem ram_null' (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (j : Fin R.A.n) :
    volume ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' {x | Ψ (segre (R.lift x x)) 0 ≠ 0 ∧
      ∃ k, x ∈ (R.A.chart k).source ∧
        LinearMap.det (fderiv ℂ (brQ R Ψ ∘ (R.A.chart k).symm) (R.A.chart k x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = 0}) = 0 := by
  exact GroundTheory.Heights₂.Heights.HilbertSamuel.AnResBridge.ram_null' R.toAnRes Ψ hP hΨ j

theorem volume_projection_zeroSet_null (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (j : Fin R.A.n) :
    volume ((R.A.chart j).target ∩
      (R.A.chart j).symm ⁻¹' {x | Ψ (segre (R.lift x x)) 0 = 0}) = 0 := by
  exact GroundTheory.Heights₂.Heights.HilbertSamuel.AnResBridge.volume_projection_zeroSet_null R.toAnRes Ψ hP hΨ j

end ReciprocityTheory.ChartRestriction.G.Geo
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeA

section

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M

section PushForward

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem pushForward_null [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (q : X → Fin e → ℂ) (S : Set X)
    (hS : ∀ j, volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' S) = 0)
    (hq : ∀ x ∉ S, ∀ j, x ∈ (A.chart j).source →
      AnalyticAt ℂ (q ∘ (A.chart j).symm) (A.chart j x) ∧
        LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) (A.chart j x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0)
    (hfin : ∀ y, (q ⁻¹' {y} \ S).Finite) (g : X → ℝ) (hg : MIntegrable A Φ g) :
    mInt A Φ g = ∫ y, ∑ᶠ x ∈ q ⁻¹' {y} \ S, g x * pushDens A Φ q x :=
  pushForward_null' A Φ hΦ q S hS hq hfin g hg

end PushForward

section Res

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P J : Ideal (MRing ι)} {e : ℕ}

theorem psi0_null (R : AnLogRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (j : Fin R.A.n) :
    volume ((R.A.chart j).target ∩
      (R.A.chart j).symm ⁻¹' {x | Ψ (segre (R.lift x x)) 0 = 0}) = 0 :=
  volume_projection_zeroSet_null R Ψ hP hΨ j

theorem ram_null (R : AnLogRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (j : Fin R.A.n) :
    volume ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' {x | Ψ (segre (R.lift x x)) 0 ≠ 0 ∧
      ∃ k, x ∈ (R.A.chart k).source ∧
        LinearMap.det (fderiv ℂ (brQ R Ψ ∘ (R.A.chart k).symm) (R.A.chart k x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = 0}) = 0 :=
  ram_null' R Ψ hP hΨ j

theorem brBad_null (R : AnLogRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (j : Fin R.A.n) :
    volume ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' brBad R Ψ) = 0 := by
  have h3 : brBad R Ψ ⊆ {x | R.lift x x ∈ mcPts J} ∪ {x | Ψ (segre (R.lift x x)) 0 = 0} ∪
      {x | Ψ (segre (R.lift x x)) 0 ≠ 0 ∧ ∃ k, x ∈ (R.A.chart k).source ∧
        LinearMap.det (fderiv ℂ (brQ R Ψ ∘ (R.A.chart k).symm) (R.A.chart k x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = 0} := by
    rintro x ((h | h) | ⟨k, hk, hn⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · by_cases h0 : Ψ (segre (R.lift x x)) 0 = 0
      · exact Or.inl (Or.inr h0)
      · refine Or.inr ⟨h0, k, hk, ?_⟩
        by_contra hd
        exact hn ⟨analyticAt_brQ R Ψ x k hk h0, hd⟩
  refine measure_mono_null (Set.inter_subset_inter_right _ (Set.preimage_mono h3)) ?_
  simp only [Set.preimage_union, Set.inter_union_distrib_left]
  exact measure_union_null (measure_union_null (R.null j) (psi0_null R Ψ hP hΨ j))
    (ram_null R Ψ hP hΨ j)

theorem potOf_isPotential (R : AnLogRes P J e) (L : HermLine ι) (hL : IsSmoothHerm L) :
    IsPotential R.A (potOf R L) :=
  isPotential_potOf R hL

theorem logAbsLocInt : LogAbsLocIntStatement := logAbsLocInt'

theorem brIntegrable (R : AnLogRes P J e) (L : Fin e → HermLine ι) (A : HermLine ι) (s : MRing ι)
    (hP : IsArithVar P (e + 1)) (hL : ∀ j, IsSmoothHerm (L j)) (hA : IsSmoothHerm A)
    (hs : IsSectionOn P A s) :
    MIntegrable R.A (fun j => potOf R (L j)) (fun x => logNorm A s (R.lift x x)) :=
  brIntegrable_of logAbsLocInt R L A s hL hA hs

theorem normPoly : NormPolyStatement := normPoly_of pcMinContract

theorem projB_null (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (hJ : IsMultiHomogIdeal J) (hJP : ¬ J ≤ P) :
    volume {y : Fin e → ℂ | ∃ z ∈ mcPts P, z ∈ mcPts J ∧ Ψ (segre z) = Fin.cons 1 y} = 0 :=
  projB_null_of normPoly Ψ hP hΨ hJ hJP

theorem brQ_image_null (R : AnLogRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) :
    volume (brQ R Ψ '' (brBad R Ψ ∩ {x | Ψ (segre (R.lift x x)) 0 ≠ 0})) = 0 :=
  brQ_image_null_of R Ψ (brBad_null R Ψ hP hΨ)

theorem brFibreSum_ae (R : AnLogRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (L : Fin e → HermLine ι) (A : HermLine ι) (s : MRing ι)
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (hL : ∀ j, IsSmoothHerm (L j))
    (hA : IsSmoothHerm A) (hs : IsSectionOn P A s) :
    ∀ᵐ y, ∑ᶠ w ∈ fibre P Ψ y, sheetDensity P Ψ (pot L) (logNorm A s) y w =
      ∑ᶠ x ∈ brQ R Ψ ⁻¹' {y} \ brBad R Ψ,
        logNorm A s (R.lift x x) * pushDens R.A (fun j => potOf R (L j)) (brQ R Ψ) x := by
  have hN : volume ({y : Fin e → ℂ | ∃ z ∈ mcPts P, z ∈ mcPts J ∧ Ψ (segre z) = Fin.cons 1 y} ∪
      brQ R Ψ '' (brBad R Ψ ∩ {x | Ψ (segre (R.lift x x)) 0 ≠ 0})) = 0 :=
    measure_union_null (projB_null Ψ hP hΨ R.homog R.nondeg) (brQ_image_null R Ψ hP hΨ)
  have hNae : ∀ᵐ y, y ∉ ({y : Fin e → ℂ | ∃ z ∈ mcPts P, z ∈ mcPts J ∧ Ψ (segre z) = Fin.cons 1 y} ∪
      brQ R Ψ '' (brBad R Ψ ∩ {x | Ψ (segre (R.lift x x)) 0 ≠ 0})) :=
    ae_iff.mpr (by simpa only [not_not, Set.ofPred_mem_eq] using hN)
  filter_upwards [hNae, sheetIndep K ι P e Ψ L A s hP hΨ hL hA hs] with y hyN hind
  have hy1 : ¬ ∃ z ∈ mcPts P, z ∈ mcPts J ∧ Ψ (segre z) = Fin.cons 1 y := fun h => hyN (Or.inl h)
  have hfib : fibre P Ψ y = brW R Ψ '' (brQ R Ψ ⁻¹' {y} \ brBad R Ψ) := by
    ext w
    constructor
    · intro hw
      obtain ⟨x, -, hx0, hxq, rfl⟩ := exists_of_mem_fibre R Ψ hw hy1
      exact ⟨x, ⟨hxq, fun hbad => hyN (Or.inr ⟨x, ⟨hbad, hx0⟩, hxq⟩)⟩, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      have := brW_mem_fibre R Ψ hP.1 hP.2.1.2.1 (projection_zero_ne_of_notMem_bridgeBadSet R Ψ hx.2)
      rwa [show brQ R Ψ x = y from hx.1] at this
  rw [hfib, finsum_mem_image ((brW_injOn R Ψ).mono (by exact fun x hx => show _ ∧ _ from
    ⟨notMemB_of_notMem_brBad R Ψ hx.2, projection_zero_ne_of_notMem_bridgeBadSet R Ψ hx.2⟩))]
  refine finsum_mem_congr rfl fun x hx => ?_
  obtain ⟨γ, hγ, hval⟩ := exists_sheet_brW R Ψ L A s hP hL hs x hx.2
  rw [show brQ R Ψ x = y from hx.1] at hγ hval
  unfold sheetDensity
  rw [dite_eq_left ⟨γ, hγ⟩]
  exact (hind _ _ _ (Exists.choose_spec (⟨γ, hγ⟩ : ∃ γ, IsSheet P Ψ y (brW R Ψ x) γ)) hγ).trans hval

end Res

end ReciprocityTheory.ChartRestriction.G.Geo
end
end
end
