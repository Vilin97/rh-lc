module

public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices
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
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsMuSheetLeviNonneg
public import Mathlib.Analysis.Matrix.PosDef
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ComplexHessianTransposeIsHermitian
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PMuSheetLeviNonneg
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsRefAlongSheet
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.TypeStar
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PSheetChartHolo
import Mathlib.Algebra.Order.Star.Real
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MeasureLimitStatementHolds

-- Source module: GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsMuHomDensityNonneg

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def MuHomDensityNonneg.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt) (Q : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (D.n + 1) → ℂ)),
    IsGoodProj (mCoordIdeal D.y) Q →
      ∀ᵐ y : Fin D.n → ℂ, ∀ w,
        0 ≤ sheetDensity (mCoordIdeal D.y) Q (fun (_ : Fin D.n) => phMu X.H) (fun _ => 1) y w

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PMuHomDensityNonneg

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

theorem maDensity_const_nonneg {D : ℕ} {φ : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ} (hφ : ContDiffAt ℝ 2 φ y)
    (hL : ∀ v, 0 ≤ leviForm φ y v) : 0 ≤ maDensity (fun _ : Fin D => φ) y := by
  unfold maDensity
  rw [ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.mixedDiscriminant_constant]
  have hS : IsSymmSndFDerivAt ℝ φ y := hφ.isSymmSndFDerivAt (by simp)
  have hP := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.complexHessian_posSemidef hS (zero_le_one' ℝ) hL
  have hd := hP.det_nonneg
  rw [Complex.ofReal_one, one_smul, Matrix.det_transpose] at hd
  have hre : 0 ≤ (cxHessian φ y).det.re := (Complex.nonneg_iff.1 hd).1
  have h1 : (0 : ℝ) ≤ (D.factorial : ℝ) * (2 / Real.pi) ^ D := by positivity
  exact mul_nonneg h1 hre

theorem MuHomDensityNonneg.proof (h : MuSheetLeviNonneg.Statement) : MuHomDensityNonneg.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X Q hQ
  filter_upwards [h II Ψ K ι Ω E D O Lt X Q hQ] with y hy w
  unfold sheetDensity
  split_ifs with hγ
  · obtain ⟨h2, hL⟩ := hy w _ hγ.choose_spec
    rw [one_mul]
    exact maDensity_const_nonneg h2 hL
  · exact le_rfl

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PRefAlongSheet

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open ReciprocityTheory.AnForm.M (FinHolAtlas)

theorem analyticAt_holoOn_comp_chartSymm {e m : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas e X}
    {ψ : OpenPartialHomeomorph X (Fin e → ℂ)} (hψ : ReciprocityTheory.AnForm.M.IsCompatChart A ψ) {V : Set X}
    {F : X → ℂ} (hF : A.HoloOn V F) {g : (Fin m → ℂ) → Fin e → ℂ} {y : Fin m → ℂ} (hg : AnalyticAt ℂ g y)
    (hgy : g y ∈ ψ.target) (hV : ψ.symm (g y) ∈ V) :
    AnalyticAt ℂ (fun y' => F (ψ.symm (g y'))) y := by
  obtain ⟨i, hi⟩ := A.cover (ψ.symm (g y))
  have hτ : AnalyticAt ℂ (A.chart i ∘ ψ.symm) (g y) := (hψ i).2 (g y) ⟨hgy, hi⟩
  have hFi : AnalyticAt ℂ (F ∘ (A.chart i).symm) ((A.chart i ∘ ψ.symm) (g y)) := by
    refine hF i _ ⟨(A.chart i).map_source hi, ?_⟩
    show (A.chart i).symm (A.chart i (ψ.symm (g y))) ∈ V
    rw [(A.chart i).left_inv hi]
    exact hV
  refine ((hFi.comp hτ).comp hg).congr ?_
  have hc : ContinuousAt (fun y' => ψ.symm (g y')) y := (ψ.continuousAt_symm hgy).comp hg.continuousAt
  filter_upwards [hc.preimage_mem_nhds ((A.chart i).open_source.mem_nhds hi)] with y' hy'
  simp only [Function.comp_apply, (A.chart i).left_inv hy']

theorem RefAlongSheet.proof : RefAlongSheet.Statement := by
  intro K _ ι _ P n M Xo A S γ y j hγ hsrc hev
  classical
  obtain ⟨g, hg'⟩ : ∃ g : (Fin n → ℂ) → Fin n → ℂ, g = fun y'' => S.R.chart j (M.proj (γ y'')) := ⟨_, rfl⟩
  have hg : AnalyticAt ℂ g y := by
    obtain ⟨V, hV, hVo, hyV⟩ := eventually_nhds_iff.1 (hev.mono fun _ h => h.2)
    refine AnalyticAt.pi fun i => ReciprocityTheory.AnForm.Osgood.osgood n V (fun w => g w i) hVo (fun z hz => ?_) y hyV
    rw [hg']
    exact (differentiableAt_pi.mp (hV z hz) i).differentiableWithinAt
  have hγc : ∀ p, AnalyticAt ℂ (fun w => γ w p) y := by
    intro p
    obtain ⟨V, hV, hVo, hyV⟩ := eventually_nhds_iff.1 (hγ.mono fun _ h => h.1)
    exact ReciprocityTheory.AnForm.Osgood.osgood n V (fun w => γ w p) hVo
      (fun z hz => (differentiableAt_pi.mp (hV z hz) p).differentiableWithinAt) y hyV
  have hgy : g y ∈ (S.R.chart j).target := by rw [hg']; exact (S.R.chart j).map_source hsrc
  have hxy : (S.R.chart j).symm (g y) = M.proj (γ y) := by rw [hg']; exact (S.R.chart j).left_inv hsrc
  obtain ⟨U, hUo, hx0U, hUth, s, hs, hsh, G1, hG1, hG1eq⟩ :=
    S.th_ref (M.proj (γ y)) (M.proj (γ y)) (S.R.th.mem_U _)
  obtain ⟨W, hWo, hx0W, G2, hG2, hG2eq⟩ := S.R.q_th j (M.proj (γ y)) (M.proj (γ y)) ⟨S.R.th.mem_U _, hsrc⟩
  obtain ⟨x', hx'⟩ : ∃ x' : (Fin n → ℂ) → M.Xc, x' = fun y' => (S.R.chart j).symm (g y') := ⟨_, rfl⟩
  have hsxy : x' y = M.proj (γ y) := by rw [hx']; exact hxy
  have hx'c : ContinuousAt x' y := by
    rw [hx']; exact ((S.R.chart j).continuousAt_symm hgy).comp hg.continuousAt
  have hsc : ∀ p, AnalyticAt ℂ (fun y' => s (x' y') p) y := fun p => by
    rw [hx']
    exact analyticAt_holoOn_comp_chartSymm (S.R.compat j) (hsh p) hg hgy (by rw [hxy]; exact hx0U)
  have hG1x : AnalyticAt ℂ (fun y' => G1 (x' y')) y := by
    rw [hx']
    exact analyticAt_holoOn_comp_chartSymm (S.R.compat j) hG1 hg hgy (by rw [hxy]; exact hx0U)
  have hG2x : AnalyticAt ℂ (fun y' => G2 (x' y')) y := by
    rw [hx']
    exact analyticAt_holoOn_comp_chartSymm (S.R.compat j) hG2 hg hgy (by rw [hxy]; exact hx0W)
  have hs0 : s (M.proj (γ y)) ∈ mcPts P := (hs _ hx0U).1
  choose i hi using hs0.1
  obtain ⟨cf, hcf⟩ : ∃ cf : K → (Fin n → ℂ) → ℂ,
      cf = fun k y' => γ y' ⟨k, i k⟩ / s (x' y') ⟨k, i k⟩ := ⟨_, rfl⟩
  have hsi : ∀ k, s (x' y) ⟨k, i k⟩ ≠ 0 := fun k => by rw [hsxy]; exact hi k
  have hcfa : ∀ k, AnalyticAt ℂ (cf k) y := fun k => by
    rw [hcf]; exact (hγc _).div (hsc _) (hsi k)
  have hne : ∀ᶠ y' in 𝓝 y, ∀ k, s (x' y') ⟨k, i k⟩ ≠ 0 :=
    Filter.eventually_all.2 fun k => (hsc _).continuousAt.eventually_ne (hsi k)
  have hUWn : U ∩ W ∈ 𝓝 (x' y) := (hUo.inter hWo).mem_nhds (by rw [hsxy]; exact ⟨hx0U, hx0W⟩)
  have hgood : ∀ᶠ y' in 𝓝 y, (x' y' ∈ U ∩ W ∧ M.proj (γ y') ∈ (S.R.chart j).source ∧ γ y' ∈ mcPts P) ∧
      ∀ k, s (x' y') ⟨k, i k⟩ ≠ 0 := by
    filter_upwards [hx'c.preimage_mem_nhds hUWn, hev, hγ, hne] with y' h1 h2 h3 h4
    exact ⟨⟨h1, h2.1, h3.2⟩, h4⟩
  have key : ∀ y', ((x' y' ∈ U ∩ W ∧ M.proj (γ y') ∈ (S.R.chart j).source ∧ γ y' ∈ mcPts P) ∧
      ∀ k, s (x' y') ⟨k, i k⟩ ≠ 0) →
      (∀ k, cf k y' ≠ 0) ∧ Real.log (S.ref.h (γ y')) = ∑ k, (S.ref.a k : ℝ) * Real.log ‖cf k y'‖ +
        (S.R.q j (S.R.chart j (M.proj (γ y'))) - (G2 (x' y')).re - (G1 (x' y')).re) := by
    rintro y' ⟨⟨⟨hU', hW'⟩, hsrc', hγ'⟩, hne'⟩
    have hxp : x' y' = M.proj (γ y') := by rw [hx', hg']; exact (S.R.chart j).left_inv hsrc'
    obtain ⟨hsm, hsp⟩ := hs _ hU'
    obtain ⟨c, hc, hγc'⟩ := (M.fibre _ hsm _ hγ').1 (by rw [hsp, hxp])
    have hck : ∀ k, cf k y' = c k := fun k => by
      have h := congrFun hγc' ⟨k, i k⟩
      rw [hcf]
      show γ y' ⟨k, i k⟩ / s (x' y') ⟨k, i k⟩ = c k
      rw [h]
      exact mul_div_cancel_right₀ (c k) (hne' k)
    have hh : S.ref.h (γ y') = (∏ k, ‖c k‖ ^ S.ref.a k) * S.ref.h (s (x' y')) := by
      rw [hγc']; exact S.ref.smul c _ hc
    have hpos : ∀ k, 0 < ‖c k‖ := fun k => norm_pos_iff.2 (hc k)
    have hlog : Real.log (S.ref.h (γ y')) =
        ∑ k, (S.ref.a k : ℝ) * Real.log ‖c k‖ + Real.log (S.ref.h (s (x' y'))) := by
      rw [hh, Real.log_mul (Finset.prod_pos fun k _ => zpow_pos (hpos k) _).ne' (S.ref.pos _ hsm.1).ne',
        Real.log_prod fun k _ => (zpow_pos (hpos k) _).ne']
      simp only [Real.log_zpow]
    have h1 := hG1eq _ hU'
    have hsrc'' : x' y' ∈ (S.R.chart j).source := by rw [hxp]; exact hsrc'
    have h2 := hG2eq _ ⟨⟨hW', hUth hU'⟩, hsrc''⟩
    refine ⟨fun k => by rw [hck]; exact hc k, ?_⟩
    rw [hlog, ← hxp]
    simp only [hck]
    linarith
  have hcy : ∀ k, cf k y ≠ 0 := (key y hgood.self_of_nhds).1
  refine ⟨fun y' => ∑ k, ((S.ref.a k : ℝ) : ℂ) * (Complex.log (cf k y' / cf k y) + (Real.log ‖cf k y‖ : ℂ)) -
    (G1 (x' y') + G2 (x' y')), ?_, ?_⟩
  · have hterm : ∀ k, AnalyticAt ℂ (fun y' => ((S.ref.a k : ℝ) : ℂ) *
        (Complex.log (cf k y' / cf k y) + (Real.log ‖cf k y‖ : ℂ))) y := fun k => by
      have hl : AnalyticAt ℂ (fun y' => Complex.log (cf k y' / cf k y)) y := by
        refine ((hcfa k).div analyticAt_const (hcy k)).clog ?_
        show cf k y / cf k y ∈ Complex.slitPlane
        rw [div_self (hcy k)]
        exact Complex.one_mem_slitPlane
      exact analyticAt_const.mul (hl.add analyticAt_const)
    have hsum : AnalyticAt ℂ (fun y' => ∑ k, ((S.ref.a k : ℝ) : ℂ) *
        (Complex.log (cf k y' / cf k y) + (Real.log ‖cf k y‖ : ℂ))) y := by
      have h := Finset.analyticAt_sum (𝕜 := ℂ) (f := fun k y' => ((S.ref.a k : ℝ) : ℂ) *
        (Complex.log (cf k y' / cf k y) + (Real.log ‖cf k y‖ : ℂ))) Finset.univ fun k _ => hterm k
      convert h using 1
      ext y'
      simp [Finset.sum_apply]
    have hG12 : AnalyticAt ℂ (fun y' => G1 (x' y') + G2 (x' y')) y := hG1x.add hG2x
    exact hsum.sub hG12
  · filter_upwards [hgood] with y' hy'
    obtain ⟨hnz, heq⟩ := key y' hy'
    rw [heq]
    have hl : ∀ k, Real.log ‖cf k y' / cf k y‖ = Real.log ‖cf k y'‖ - Real.log ‖cf k y‖ := fun k => by
      rw [norm_div, Real.log_div (norm_ne_zero_iff.2 (hnz k)) (norm_ne_zero_iff.2 (hcy k))]
    simp only [Complex.sub_re, Complex.add_re, Complex.re_sum, Complex.re_ofReal_mul, Complex.log_re,
      Complex.ofReal_re, hl, sub_add_cancel]
    ring

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.StokesLimitIffPosOfResK

section

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.StokesCompare

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology MeasureTheory
open GroundTheory.Heights₂.Heights.LowerBoundFree

section Clauses

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
  {D : ComponentData II Ψ K ι Ω E} {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt]

end Clauses

section Mass

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Giv.MuLimit

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)] {D : ComponentData II Ψ K ι Ω E} {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt]

theorem degMu_nonneg (X : ComponentSetting D O Lt) : 0 ≤ degMu X.H := by
  classical
  have hN := MuHomDensityNonneg.proof (MuSheetLeviNonneg.proof SheetChartHolo.proof RefAlongSheet.proof)
  have hdeg : degMu X.H = ptsIntegral (e := D.n) (mCoordIdeal D.y) (fun _ => phMu X.H) (fun _ => 1) := rfl
  rw [hdeg]
  unfold ptsIntegral
  split_ifs with hΨ
  · refine integral_nonneg_of_ae ?_
    filter_upwards [hN II Ψ K ι Ω E D O Lt X _ hΨ.choose_spec] with y hy
    exact finsum_nonneg fun w => finsum_nonneg fun _ => hy w
  · exact le_rfl

end Mass

end GlobalTheory.CompanionTheory.StokesCompare
end
end
end
