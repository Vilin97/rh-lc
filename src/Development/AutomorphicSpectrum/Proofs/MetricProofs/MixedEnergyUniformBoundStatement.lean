module

public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Statements
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LemmaETailMass
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Assembly
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PListTailLogSmooth
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.IsOpenKappaOpenNeighbourhood
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.ContinuousTmaxShift
import Mathlib.Algebra.Order.Star.Real
public import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.TailBound
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv

-- Source module: GroundTheory.HeightsAndTheta.Heights.Regularisation.ToPotentialChartsChartFun

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular

open MeasureTheory Metric Set
open scoped ContDiff
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.AnForm.A (Mollifier molli regMax tmax kθ le_tmax tmax_le kθ_integral abs_le_of_kθ_ne)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPosPot IsCompatChart)
open GroundTheory.Heights₂.Heights.Regular (PotentialCharts)

noncomputable section

theorem closure_image_subset {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [TopologicalSpace Y]
    [T2Space Y] (e : OpenPartialHomeomorph X Y) {s : Set X} (hs : closure s ⊆ e.source) :
    IsCompact (e '' closure s) ∧ closure (e.target ∩ e.symm ⁻¹' s) ⊆ e '' closure s := by
  have hK : IsCompact (e '' closure s) :=
    isClosed_closure.isCompact.image_of_continuousOn (e.continuousOn.mono hs)
  refine ⟨hK, closure_minimal ?_ hK.isClosed⟩
  rintro y ⟨hy, hys⟩
  exact ⟨e.symm y, subset_closure hys, e.right_inv hy⟩

variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X}

namespace RegCharts

def ofPotentialCharts [CompactSpace X] (P : PotentialCharts A) (om : LocPot X)
    (om_pot : IsPotential A om) (om_pos : IsPosPot A om) : RegCharts A where
  n := P.N
  ψ := P.chart
  compat := P.compat
  W j := (P.chart j).target
  W' j := (P.chart j).target ∩ (P.chart j).symm ⁻¹' P.mid j
  W'' j := (P.chart j).target ∩ (P.chart j).symm ⁻¹' P.inner j
  isOpen_kappaOpenNeighbourhood j := (P.chart j).open_target
  isOpen_alt j := (P.chart j).isOpen_inter_preimage_symm (P.isOpen_mid j)
  isOpen_alt_alt j := (P.chart j).isOpen_inter_preimage_symm (P.isOpen_inner j)
  W_subset _ := subset_rfl
  isCompact_closure_middle j :=
    (closure_image_subset (P.chart j) (P.closure_mid j)).1.of_isClosed_subset isClosed_closure
      (closure_image_subset (P.chart j) (P.closure_mid j)).2
  closure_W'_subset j := (closure_image_subset (P.chart j) (P.closure_mid j)).2.trans
    (image_subset_iff.2 fun _ hx => (P.chart j).map_source (P.closure_mid j hx))
  closure_W''_subset j := by
    have hs := (P.closure_inner j).trans (P.mid_subset_source j)
    refine (closure_image_subset (P.chart j) hs).2.trans ?_
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨(P.chart j).map_source (hs hx), ?_⟩
    show (P.chart j).symm (P.chart j x) ∈ P.mid j
    rw [(P.chart j).left_inv (hs hx)]
    exact P.closure_inner j hx
  cover x := by
    obtain ⟨j, hj⟩ := P.cover x
    have hs : x ∈ (P.chart j).source := P.mid_subset_source j (P.inner_subset_mid j hj)
    refine ⟨j, hs, (P.chart j).map_source hs, ?_⟩
    show (P.chart j).symm (P.chart j x) ∈ P.inner j
    rw [(P.chart j).left_inv hs]
    exact hj
  θ := P.th
  θ_pot := P.th_pot
  om := om
  om_pot := om_pot
  om_pos := om_pos
  q := P.q
  q_smooth := P.q_smooth
  q_θ j y hy _ := by
    obtain ⟨V, hV, hyV, G, hG, hq⟩ := P.q_th j y y ⟨P.th.mem_U y, hy⟩
    refine ⟨V, hV, hyV, fun x => -G x, fun k => (hG k).neg, fun x hx _ => ?_⟩
    have := hq x hx
    simp only [Complex.neg_re]
    linarith

variable [CompactSpace X] (P : PotentialCharts A) (om : LocPot X) (om_pot : IsPotential A om)
  (om_pos : IsPosPot A om)

end RegCharts

namespace RegCharts

variable (R : RegCharts A)

variable [T2Space X] (hW : ∀ j, R.W j ⊆ ball 0 1)

end RegCharts

section RoundTrip

variable [CompactSpace X] [T2Space X]

end RoundTrip

namespace PotentialCharts

variable (P : PotentialCharts A)


end PotentialCharts

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.Regularisation.ProjLineChartsNotSubsetBall

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular

open MeasureTheory Metric Set
open scoped ContDiff
open ReciprocityTheory.AnForm.A (Mollifier molli regMax coordDiv limsupExt)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPosPot)
open GroundTheory.Heights₂.Heights.Regular (PotentialCharts BoundedPshData pointReg pointCharts pointAtlas)

local notation "RegChartDataA" => GroundTheory.Heights₂.Heights.Regular.RegChartData

noncomputable section

theorem isClosed_coordDiv {D : ℕ} (S : Finset (Fin D)) : IsClosed (coordDiv S) := by
  have h : coordDiv S = ⋃ i ∈ S, (fun z : Fin D → ℂ => z i) ⁻¹' {0} := by
    ext z
    simp [coordDiv]
  rw [h]
  exact isClosed_biUnion_finset fun i _ => isClosed_singleton.preimage (continuous_apply i)

variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X}

theorem isOpen_Yo_regular (R : RegChartDataA A) : IsOpen R.Yo := by
  refine isOpen_iff_forall_mem_open.2 fun x hx => ?_
  obtain ⟨j, hj⟩ := R.cover x
  have hs : x ∈ (R.chart j).source := R.mid_subset_source j (R.inner_subset_mid j hj)
  exact ⟨(R.chart j).source ∩ R.chart j ⁻¹' (coordDiv (R.S j))ᶜ,
    fun y hy => (R.mem_Yo j y hy.1).2 hy.2,
    (R.chart j).isOpen_inter_preimage (isClosed_coordDiv _).isOpen_compl, hs,
    (R.mem_Yo j x hs).1 hx⟩

namespace RegChartData

def ofRegular [CompactSpace X] (R : RegChartDataA A) (om : LocPot X) (om_pot : IsPotential A om)
    (om_pos : IsPosPot A om) : RegChartData A where
  toRegCharts := RegCharts.ofPotentialCharts R.toPotentialCharts om om_pot om_pos
  Yo := R.Yo
  isOpen_Yo := isOpen_Yo_regular R
  S := R.S
  mem_Yo_iff j z hz := by
    have h := R.mem_Yo j _ ((R.chart j).map_target hz)
    rwa [(R.chart j).right_inv hz] at h
  r := R.r
  f := R.f
  f_cont j := (R.f_smooth j).continuousOn
  f_bdd j := ⟨R.f_bdd.choose, R.f_bdd.choose_spec j⟩
  r_chart j z hz := by
    refine (R.r_chart j z hz).trans ?_
    simp only [Real.log_inv, Finset.sum_neg_distrib]
    ring
  one_le_r := R.one_le_r
  φ := R.ph
  φ_smooth := R.ph_smooth
  psh := R.u_psh
  C := |R.Clog| + |R.Cph| + |R.Cgrad|
  φ_le x hx := (R.ph_le x hx).trans
    (by linarith [le_abs_self R.Cph, abs_nonneg R.Clog, abs_nonneg R.Cgrad])
  le_φ x hx := by
    have h1 := R.ph_ge x hx
    have h2 : 0 ≤ Real.log (R.r x) := Real.log_nonneg (R.one_le_r x hx)
    have h3 : R.Clog ≤ |R.Clog| + |R.Cph| + |R.Cgrad| := by
      linarith [le_abs_self R.Clog, abs_nonneg R.Cph, abs_nonneg R.Cgrad]
    nlinarith
  grad j z hz := by
    have hYo : (R.chart j).symm z ∈ R.Yo :=
      (R.mem_Yo j _ ((R.chart j).map_target hz.1)).2 (by rw [(R.chart j).right_inv hz.1]; exact hz.2)
    have hr : 1 ≤ R.r ((R.chart j).symm z) := R.one_le_r _ hYo
    have hC0 : 0 ≤ |R.Clog| + |R.Cph| + |R.Cgrad| := by positivity
    have hCg : |R.Cgrad| ≤ |R.Clog| + |R.Cph| + |R.Cgrad| := by
      linarith [abs_nonneg R.Clog, abs_nonneg R.Cph]
    have hpos : 0 ≤ R.r ((R.chart j).symm z) ^ R.Cgrad := Real.rpow_nonneg (by linarith) _
    have h1 : R.Cgrad * R.r ((R.chart j).symm z) ^ R.Cgrad ≤
        (|R.Clog| + |R.Cph| + |R.Cgrad|) * R.r ((R.chart j).symm z) ^ (|R.Clog| + |R.Cph| + |R.Cgrad|) :=
      calc R.Cgrad * R.r ((R.chart j).symm z) ^ R.Cgrad
          ≤ (|R.Clog| + |R.Cph| + |R.Cgrad|) * R.r ((R.chart j).symm z) ^ R.Cgrad :=
            mul_le_mul_of_nonneg_right ((le_abs_self _).trans hCg) hpos
        _ ≤ _ := mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hr ((le_abs_self _).trans hCg)) hC0
    exact (R.grad_le j z hz).trans (mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le)

end RegChartData

namespace BoundedThPsh

end BoundedThPsh

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedEnergyUniformBound

section

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.Giv

open GroundTheory.Heights₂.Heights.AnalyticLimit

theorem tailLogBound_of_φ_eq {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Yo : Set X) (r : X → ℝ) {Φ Ψ : Fin e → LocPot X} (h : ∀ i, (Φ i).φ = (Ψ i).φ) (CE : ℝ)
    (H : TailLogBound A Yo r Φ CE) : TailLogBound A Yo r Ψ CE := by
  have hd : ∀ j y, ReciprocityTheory.AnForm.M.locDens A Φ j y = ReciprocityTheory.AnForm.M.locDens A Ψ j y := by
    intro j y
    simp only [ReciprocityTheory.AnForm.M.locDens, h]
  have hM : ∀ g, ReciprocityTheory.AnForm.M.MIntegrable A Φ g ↔ ReciprocityTheory.AnForm.M.MIntegrable A Ψ g := by
    intro g
    simp only [ReciprocityTheory.AnForm.M.MIntegrable, hd]
  have hI : ∀ g, ReciprocityTheory.AnForm.M.mInt A Φ g = ReciprocityTheory.AnForm.M.mInt A Ψ g := by
    intro g
    simp only [ReciprocityTheory.AnForm.M.mInt, ReciprocityTheory.AnForm.M.integralWith, hd]
  intro R₀ hR
  rw [← hM, ← hI]
  exact H R₀ hR

theorem tailLogProducts : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (R : GroundTheory.Heights₂.Heights.Regular.RegChartData A) (Θ : LocPot X), IsPotential A Θ → IsPosPot A Θ → ∀ (P : Fin e → LocPot X) (C : ℝ), (∀ i, IsPotential A (P i)) → ∃ CE : ℝ, ∀ f : Fin e → X → ℝ, (∀ i, A.Smooth (f i)) → (∀ i, IsPsh A (P i + LocPot.ofFun (f i))) → (∀ i, ∀ x ∈ R.Yo, |f i x| ≤ C + C * Real.log (R.r x)) → (∀ i, ∀ x ∈ R.Yo, f i x ≤ C) → GroundTheory.Heights₂.Heights.AnalyticLimit.TailLogBound A R.Yo R.r (fun i => P i + LocPot.ofFun (f i)) CE := by
  intro e X _ _ _ A R Θ hΘ hΘp P C hP
  have hSmooth : ListTailLogSmooth.Statement :=
    ListTailLogSmooth.proof
      (GroundTheory.Heights₂.Heights.ForSecondHalf.ListTailLog.of_lemmaETailMass lemmaETailMass)
  let R₁ := GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular.RegChartData.ofRegular R Θ hΘ hΘp
  let R' := regChartShift R₁
  have hconst : A.Smooth (fun _ : X => C) := fun j => contDiffOn_const
  let th : Fin e → LocPot X := fun i => P i + LocPot.ofFun (fun _ => C)
  have hth : ∀ i, IsPotential A (th i) := fun i =>
    isPotentialAdd A _ _ (hP i) (isPotential_ofFun A _ hconst)
  obtain ⟨Om, hOm⟩ := BoundingKaehler.full e A ⟨Θ, hΘ, hΘp⟩ e th hth
  obtain ⟨CE, hCE⟩ := hSmooth A R' Om (3 * |C|)
  refine ⟨CE, fun f hf hpsh habs hle => ?_⟩
  let u : Fin e → X → ℝ := fun i x => f i x - C
  have hu : ∀ i, A.Smooth (u i) := fun i j => (hf i j).sub contDiffOn_const
  have hφ : ∀ i, (potForm (th i) (u i)).φ = (P i + LocPot.ofFun (f i)).φ := by
    intro i
    funext x y
    show (P i).φ x y + C + (f i y - C) = (P i).φ x y + f i y
    ring
  have hnn : ∀ i, FormNonneg A R.Yo (P i + LocPot.ofFun (f i)) := fun i x k y hy w =>
    hpsh i x k y ⟨hy.1, hy.2.2⟩ w
  have hform : ∀ i, IsSmoothPotForm A R'.Yo R'.r Om (3 * |C|) (th i) (u i) := by
    intro i
    refine ⟨⟨hth i, (hOm i).1, (hOm i).2, ?_, ?_, ?_, ?_, Or.inl (hu i)⟩, hu i⟩
    · exact fun j => (hu i j).mono fun y hy => ⟨hy.1, trivial⟩
    · intro x hx
      have := hle i x hx
      show f i x - C ≤ 0
      linarith
    · intro x hx
      have hx' : x ∈ R.Yo := hx
      have h1 : 1 ≤ R.r x := R.one_le_r x hx'
      have he : (2 : ℝ) ≤ Real.exp 1 := by
        have := Real.add_one_le_exp (1 : ℝ)
        linarith
      have hL : Real.log (R.r x) ≤ Real.log (R.r x + (Real.exp 1 - 1)) :=
        Real.log_le_log (by linarith) (by linarith)
      have hL1 : 1 ≤ Real.log (R.r x + (Real.exp 1 - 1)) := by
        have h2 : Real.log (Real.exp 1) ≤ Real.log (R.r x + (Real.exp 1 - 1)) :=
          Real.log_le_log (Real.exp_pos 1) (by linarith)
        rwa [Real.log_exp] at h2
      have hL0 := Real.log_nonneg h1
      have hf' : -(C + C * Real.log (R.r x)) ≤ f i x := by
        have := (neg_abs_le (f i x))
        linarith [habs i x hx']
      have hc1 : C * Real.log (R.r x) ≤ |C| * Real.log (R.r x + (Real.exp 1 - 1)) :=
        mul_le_mul (le_abs_self C) hL hL0 (abs_nonneg C)
      have hc2 : |C| ≤ |C| * Real.log (R.r x + (Real.exp 1 - 1)) :=
        le_mul_of_one_le_right (abs_nonneg _) hL1
      have hc3 := le_abs_self C
      show -(3 * |C| * Real.log (R.r x + (Real.exp 1 - 1))) ≤ f i x - C
      linarith
    · intro x k y hy w
      have := hnn i x k y ⟨hy.1, hy.2.1, hy.2.2.1⟩ w
      rw [hφ i]
      exact this
  have hB := hCE th u hform
  have hpot : ∀ i, IsPotential A (P i + LocPot.ofFun (f i)) := fun i =>
    isPotentialAdd A _ _ (hP i) (isPotential_ofFun A _ (hf i))
  have hB' : TailLogBound A R.Yo R'.r (fun i => P i + LocPot.ofFun (f i)) CE :=
    tailLogBound_of_φ_eq A _ _ hφ CE hB
  exact tailLogBound_of_le (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular.isOpen_Yo_regular R)
    (regChartData_continuousOn_r R₁) (r' := R'.r)
    (fun x _ => by
      show R.r x ≤ R.r x + (Real.exp 1 - 1)
      linarith [Real.add_one_le_exp (1 : ℝ)])
    hpot hnn hB'

end GlobalTheory.CompanionTheory.Ar.Giv
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedEnergyUniformBoundStatement

section

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

theorem _root_.GlobalTheory.T.mixed_energy_uniform_bound : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (R : GroundTheory.Heights₂.Heights.Regular.RegChartData A) (Θ : LocPot X), IsPotential A Θ → IsPosPot A Θ → ∀ (P : Fin e → LocPot X) (C : ℝ), (∀ i, IsPotential A (P i)) → ∃ CE : ℝ, ∀ f : Fin e → X → ℝ, (∀ i, A.Smooth (f i)) → (∀ i, IsPsh A (P i + LocPot.ofFun (f i))) → (∀ i, ∀ x ∈ R.Yo, |f i x| ≤ C + C * Real.log (R.r x)) → (∀ i, ∀ x ∈ R.Yo, f i x ≤ C) → GroundTheory.Heights₂.Heights.AnalyticLimit.TailLogBound A R.Yo R.r (fun i => P i + LocPot.ofFun (f i)) CE := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.tailLogProducts | exact GlobalTheory.CompanionTheory.Ar.Giv.tailLogProducts | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.tailLogProducts <;> assumption)
end
end
