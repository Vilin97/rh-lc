module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseVectorPropertiesStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAnalyticProjectionBijectiveStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagPointInMultiprojectivePointsStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsClosedSectionBoundaryStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoPointFibreChartFirst
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.BasePartFlagPt
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsFibreChartIff
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAnalyticOrbitOffBoundaryStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagPotentialBlockDecomposition
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagPotentialBlockDecompositionStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalHolomorphicLiftRealisationStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogNormNonvanishingAnalyticHarmonicStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularFunctionAnalyticOnChartStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.UnipotentValueNeZeroStatement
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.AnalyticAtFlagPt
import Development.WeilBound.CoreStatements.PluriharmonicCharts.ExistsHoloOnOfGerm
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
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.CoreStatements.PluriharmonicCharts.AnalyticAtFlagPt
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.NotMemOfEqTop
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.PullbackPullback

-- Source module: Development.WeilBound.CoreStatements.PluriharmonicCharts.AnalyticAtDetFac

section

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace PositivityTheory.Xgp.c_unif

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ} {M : FlagModel y Ψ N j} {n d : ℕ} {BM : BaseMetric M n}

theorem analyticAt_detFac {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (i : Fin N)
    {H : E → Matrix (Fin N) (Fin N) ℂ} {w : E} (h : ∀ r s, AnalyticAt ℂ (fun u => H u r s) w) :
    AnalyticAt ℂ (fun u => detFac j i (H u)) w := by
  unfold detFac
  refine AnalyticAt.mul ?_ ?_
  · split_ifs
    · exact Fib.analyticAt_minorIJ_of_entries _ w h _ _
    · exact analyticAt_const
  · split_ifs
    · exact Fib.analyticAt_minorIJ_of_entries _ w h _ _
    · exact analyticAt_const

theorem holoOn_mul {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {W : Set X}
    {P Q : X → Matrix (Fin N) (Fin N) ℂ} (hP : ∀ a b, A.HoloOn W fun x => P x a b)
    (hQ : ∀ a b, A.HoloOn W fun x => Q x a b) (a b : Fin N) : A.HoloOn W fun x => (P x * Q x) a b := by
  intro k t ht
  show AnalyticAt ℂ (fun w => (P ((A.chart k).symm w) * Q ((A.chart k).symm w)) a b) t
  simp only [Matrix.mul_apply]
  exact Finset.analyticAt_fun_sum _ fun c _ => (hP a c k t ht).mul (hQ c b k t ht)

theorem period_chart (FA : FlagAn BM d) (hsurj : Function.Surjective FA.Re.π) {l : Fin BM.q} {Vb : Set BM.Rb.X}
    {Pi : Ψ → BM.Rb.X → Matrix (Fin N) (Fin N) ℂ} (hPi : IsPeriodOn BM.Rb.A j Vb Pi (BM.G l)) {W : Set FA.S.X}
    (hW : IsOpen W) {x : FA.S.X} (hx : x ∈ W) (hl : ∀ x' ∈ W, FA.pr x' ∈ BM.O l \ bdry BM.s ∧ FA.pr x' ∈ Vb)
    {H : Ψ → FA.S.X → Matrix (Fin N) (Fin N) ℂ} (hH : ∀ τ a b, FA.S.A.HoloOn W fun x' => H τ x' a b)
    (hHb : ∀ τ, ∀ x' ∈ W, IsBlockDiag j (H τ x') ∧ (H τ x').det ≠ 0)
    (ho : ∀ x' ∈ W, ∀ x₀, FA.Re.π x₀ = x' →
      SameOrbit (FA.Re.R.lift x₀ x₀) (FC.flagPt M (BM.F l) (FC.bvec BM l (FA.pr x')) fun τ => H τ x')) :
    ∃ V, IsPeriodChart (FA.S.comap some).A j (FA.S.comap some).potH x V fun τ x' => Pi τ (FA.pr x') * H τ x' := by
  have hj := M.j_le
  have hg := GlobalTheory.T.base_vector_properties K ι Φ y Ψ N j M n BM l
  have hl1 : ∀ x' ∈ W, FA.pr x' ∈ BM.O l := fun x' h => (hl x' h).1.1
  have hbv := bvec_holo BM FA.pr_holo hW hl1
  have hst := fun (p : Ψ × Fin N) x' (hx' : x' ∈ W) => GlobalTheory.T.flag_potential_block_decomposition N j p.2 (Pi p.1 (FA.pr x'))
    (BM.G l p.1 (FA.pr x')) (H p.1 x') hj (hPi.2.2 p.1 _ (hl x' hx').2) (BM.G_pos l p.1 _ (hl x' hx').1).1
    (BM.G_pos l p.1 _ (hl x' hx').1).2 (hHb p.1 x' hx').1 (hHb p.1 x' hx').2
  obtain ⟨k, hk⟩ := FA.S.A.cover x
  set c := FA.S.A.chart k with hc
  have hO : IsOpen (c.target ∩ c.symm ⁻¹' W) := c.isOpen_inter_preimage_symm hW
  have hxO : c x ∈ c.target ∩ c.symm ⁻¹' W := ⟨c.map_source hk, by simpa [c.left_inv hk] using hx⟩
  have hsx : c.symm (c x) = x := c.left_inv hk
  have key : ∀ p : Ψ × Fin N, ∃ V : Set FA.S.X, IsOpen V ∧ x ∈ V ∧ ∃ G : FA.S.X → ℂ, FA.S.A.HoloOn V G ∧
      ∀ x' ∈ V, ((FA.S.comap some).potH p).φ x x' - stepPot N j p.2 (Pi p.1 (FA.pr x') * H p.1 x') = (G x').re := by
    intro p
    obtain ⟨H1, hH1, he1⟩ := GlobalTheory.T.local_holomorphic_lift_realisation K ι (d + 1) _ FA.S (mCoordIdeal y) FA.Re (some p) (d + 1)
      (c.target ∩ c.symm ⁻¹' W) c.symm
      (fun u => FC.flagPt M (BM.F l) (FC.bvec BM l (FA.pr (c.symm u))) fun τ => H τ (c.symm u)) (c x)
      FA.J_top FA.deg_one FA.br_empty hO hxO
      (fun q u hu => analyticAt_flagPt (BM.F l) (fun q => hbv.1 q k u hu)
        (fun q I => hbv.2 _ (fun b hb => ((hg b hb).2.1.2.1 q I).1) k u hu) (fun τ r s => hH τ r s k u hu) q)
      (fun u hu => GlobalTheory.T.flag_point_in_multiprojective_points K ι Φ y Ψ N j M n BM l _ (hl1 _ hu.2) _ fun τ => hHb τ _ hu.2)
      (fun u hu x₀ h => ho _ hu.2 x₀ h)
    obtain ⟨H2, hH2, he2⟩ := GlobalTheory.T.log_norm_nonvanishing_analytic_harmonic (d + 1) (fun u => detFac j p.2 (H p.1 (c.symm u))) (c x)
      (analyticAt_detFac p.2 fun r s => hH p.1 r s k _ hxO)
      (CPts.detFac_ne_zero hj p.2 (hHb p.1 _ hxO.2).1 (hHb p.1 _ hxO.2).2)
    obtain ⟨H3, hH3, he3⟩ : ∃ H3 : (Fin (d + 1) → ℂ) → ℂ, AnalyticAt ℂ H3 (c x) ∧
        ∀ᶠ u in 𝓝 (c x), Fib.upsLogAt BM l p (FA.pr (c.symm u)) = (H3 u).re := by
      by_cases hp : M.blk p = none
      · simp only [Fib.upsLogAt, if_pos hp]
        refine GlobalTheory.T.log_norm_nonvanishing_analytic_harmonic (d + 1) (fun u => Fib.upsVal BM l p (FA.pr (c.symm u))) (c x) ?_
          (GlobalTheory.T.unipotent_value_ne_zero K ι Φ y Ψ N j M n d BM l p _ (hl1 _ hxO.2) hp)
        exact GlobalTheory.T.regular_function_analytic_on_chart _ _ M.Ω M.x ((BM.F l).υ p) (d + 1) n BM.Rb (c.target ∩ c.symm ⁻¹' W) (FA.pr ∘ c.symm) (c x)
          hO hxO (FA.pr_holo.1.comp_continuousOn (c.continuousOn_symm.mono Set.inter_subset_left))
          (fun m => (FA.pr_holo.2 k m).mono fun t ht => ⟨ht.1.1, ht.2⟩)
          ((BM.good l _ (hl1 _ hxO.2)).2.2 p hp).2.1
      · exact ⟨fun _ => 0, analyticAt_const, Eventually.of_forall fun u => by simp [Fib.upsLogAt, hp]⟩
    refine exists_holoOn_of_germ FA.S.A hk (H := fun u => H1 u - H2 u - H3 u) ((hH1.sub hH2).sub hH3) ?_
    filter_upwards [he1, he2, he3, hO.mem_nhds hxO] with u h1 h2 h3 hu
    obtain ⟨x₀, hx₀⟩ := hsurj (c.symm u)
    have hline := GlobalTheory.T.flag_analytic_orbit_off_boundary K ι Φ y Ψ N j M n d BM FA l x₀ _ (FA.pr (c.symm u)) p (H p.1 (c.symm u))
      (hl _ hu.2).1 (ho _ hu.2 x₀ hx₀) (by rw [FC.basePart_flagPt]; exact (hg _ (hl1 _ hu.2)).2.2.2)
      (FC.exactAt_flagPt M (BM.F l) (hg _ (hl1 _ hu.2)).2.2.1 (fun τ => H τ (c.symm u)) p)
      (hHb _ _ hu.2).1 (hHb _ _ hu.2).2
    have hphi : ((FA.S.comap some).potH p).φ x (c.symm u) =
      (FA.S.th (some p)).φ x (c.symm u) + FA.S.ph (some p) (c.symm u) := rfl
    rw [hsx, FA.ref_some] at h1
    rw [hx₀, Fib.potAt] at hline
    rw [hphi, h1, (hst p _ hu.2).2, Complex.sub_re, Complex.sub_re, ← h2, ← h3]
    linarith
  choose V hVo hxV G hG hGe using key
  refine ⟨W ∩ ⋂ p, V p, hW.inter (isOpen_iInter_of_finite hVo), ⟨hx, Set.mem_iInter.2 hxV⟩, fun τ a b => ?_,
    fun τ x' hx' => ?_, fun p => ⟨G p, holoOn_mono (hG p) fun x' hx' => Set.mem_iInter.1 hx'.2 p, fun x' hx' => ?_⟩⟩
  · refine holoOn_mono (holoOn_mul (W := W) (fun a b => ?_) (hH τ) a b) Set.inter_subset_left
    exact holoOn_mono (holoOn_comp FA.pr_holo (hPi.2.1 τ a b)) fun x' hx' => (hl x' hx').2
  · exact StepBlock.inFlagDomain_mul (hPi.2.2 τ _ (hl x' hx'.1).2).1 (hHb τ x' hx'.1).1 (hHb τ x' hx'.1).2
  · have := hGe p x' (Set.mem_iInter.1 hx'.2 p)
    linarith

end PositivityTheory.Xgp.c_unif
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PluriharmonicCharts.XCUnif

section

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace PositivityTheory.Xgp.c_unif

open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ} {M : FlagModel y Ψ N j} {n d : ℕ} {BM : BaseMetric M n}

theorem chart_over (FA : FlagAn BM d) (x : FA.S.X) {l : Fin BM.q} (hl : FA.pr x ∈ BM.O l \ bdry BM.s)
    {Vb : Set BM.Rb.X} {Pi : Ψ → BM.Rb.X → Matrix (Fin N) (Fin N) ℂ} (hVb : FA.pr x ∈ Vb)
    (hPi : IsPeriodOn BM.Rb.A j Vb Pi (BM.G l)) :
    ∃ V g, IsPeriodChart (FA.S.comap some).A j (FA.S.comap some).potH x V g ∧
      ((∀ k, FA.pr x ∈ (BM.Rb.A.chart k).source → ∀ v : Fin n → ℂ,
        (∀ τ (a b : Fin N), N - j ≤ (a : ℕ) → (b : ℕ) < N - j → ((Pi τ (FA.pr x))⁻¹ * Matrix.of fun a b =>
          fderiv ℂ (fun w => Pi τ ((BM.Rb.A.chart k).symm w) a b) (BM.Rb.A.chart k (FA.pr x)) v) a b = 0) → v = 0) →
        IsFlagImmersionAt (FA.S.comap some).A g x) := by
  have hb := GlobalTheory.T.flag_analytic_projection_bijective K ι Φ y Ψ N j M n d BM FA
  have hd := FA.Re.degree
  rw [FA.deg_one, FA.br_empty] at hd
  obtain ⟨σ, h1, h2, hσ, hinj⟩ := exists_inv FA.S.A FA.Re.R.A FA.Re.π FA.Re.holo hd hb
  have hcl : IsClosed (bdry BM.s) := GlobalTheory.T.isClosed_section_boundary n _ BM.Rb.A BM.L BM.s BM.sec
  have hW : IsOpen (σ ⁻¹' FA.Re.R.U (σ x) ∩ FA.pr ⁻¹' ((BM.O l \ bdry BM.s) ∩ Vb)) :=
    ((FA.Re.R.isOpen_U _).preimage hσ.1).inter ((((BM.O_open l).sdiff hcl).inter hPi.1).preimage FA.pr_holo.1)
  have hcomp : ∀ x', σ x' ∈ FA.Re.R.U (σ x) → SameOrbit (FA.Re.R.lift (σ x) (σ x')) (FA.Re.R.lift (σ x') (σ x')) :=
    fun x' h => FA.Re.R.compat _ _ _ ⟨h, FA.Re.R.mem_U _⟩
  obtain ⟨W, hWo, hxW, hsub, h₀, L, hh₀, hL, hLb, ho⟩ := exists_holo_flags BM FA.pr_holo hW
    (z := fun x' => FA.Re.R.lift (σ x) (σ x'))
    (fun q => holoOn_mono (holoOn_comp hσ (FA.Re.R.holo (σ x) q)) Set.inter_subset_left)
    (fun x' h => FA.Re.R.mem _ _ h.1)
    (fun x' h => orbit_trans (Fib.sameOrbit_basePart M.blk (hcomp x' h.1)) (by
      have := FA.pr_eq (σ x')
      rwa [h1] at this))
    (l := l) (fun x' h => h.2.1.1) (x₀ := x) ⟨FA.Re.R.mem_U _, hl, hVb⟩
  obtain ⟨V, hV⟩ := period_chart FA hb.2 hPi hWo hxW (fun x' h => (hsub h).2) (H := fun τ x' => h₀ τ * L τ x')
    (fun τ => holoOn_mul (fun _ _ _ => analyticOnNhd_const) (hL τ))
    (fun τ x' _ => ⟨(hh₀ τ).1.mul (hLb τ x').1, by
      rw [Matrix.det_mul, (hLb τ x').2.det, mul_one]; exact (hh₀ τ).2⟩)
    (fun x' h x₀ e => by
      have e' : x₀ = σ x' := by rw [← e, h2]
      rw [e']
      exact orbit_trans (orbit_symm (hcomp x' (hsub h).1)) (ho x' h))
  exact ⟨V, _, hV, fun himm => flag_immersion FA hσ hinj hPi hWo hxW hl.1 hVb hh₀ hL hLb ho himm⟩

theorem exists_over (FA : FlagAn BM d) {l : Fin BM.q} {b : BM.Rb.X} (hb : b ∈ BM.O l) : ∃ x, FA.pr x = b := by
  obtain ⟨x₀, hx₀⟩ := FA.Re.R.surj _ (GlobalTheory.T.flag_point_in_multiprojective_points K ι Φ y Ψ N j M n BM l b hb (fun _ => 1)
    fun _ => ⟨isBlockDiag_one, by simp⟩) (not_mem_of_eq_top FA.J_top _)
  refine ⟨FA.Re.π x₀, BM.Rb.inj _ _ (not_mem_of_eq_top rfl _) ?_⟩
  have h := Fib.sameOrbit_basePart M.blk hx₀
  rw [FC.basePart_flagPt] at h
  exact orbit_trans (orbit_symm (FA.pr_eq x₀)) (orbit_trans h (GlobalTheory.T.base_vector_properties K ι Φ y Ψ N j M n BM l b hb).2.2.2)

theorem mem_open_iff (FA : FlagAn BM d) (x : FA.S.X) : x ∈ (FA.S.comap some).open' ↔ FA.pr x ∉ bdry BM.s := by
  show ¬ FA.S.s x x = 0 ↔ _
  rw [FA.s_eq]
  rfl

end PositivityTheory.Xgp.c_unif
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAnalyticDataUniformised

section

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

theorem _root_.GlobalTheory.CompanionTheory.Relay.flag_analytic_data_uniformised : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d), n = Fintype.card Ψ * j * (N - j) → d + 1 = antisymDegree Ψ N → IsUniformised (FA.S.comap some).A (FA.S.comap some).open' j (FA.S.comap some).potH := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA _ _
  refine ⟨?_, ?_⟩
  · intro x hx
    have hb := (PositivityTheory.Xgp.c_unif.mem_open_iff FA x).1 hx
    obtain ⟨l, hl⟩ := BM.O_cover (FA.pr x)
    obtain ⟨V, Pi, hxV, hP⟩ := BM.period l (FA.pr x) ⟨hl, hb⟩
    obtain ⟨V', g, hc, -⟩ := PositivityTheory.Xgp.c_unif.chart_over FA x ⟨hl, hb⟩ hxV hP
    exact ⟨V', g, hc⟩
  · obtain ⟨l, b, ⟨hbO, hbs⟩, V, Pi, hbV, hP, himm⟩ := BM.immersion
    obtain ⟨x, rfl⟩ := PositivityTheory.Xgp.c_unif.exists_over FA hbO
    have hx : x ∈ (FA.S.comap some).open' := (PositivityTheory.Xgp.c_unif.mem_open_iff FA x).2 hbs
    obtain ⟨V', g, hc, hi⟩ := PositivityTheory.Xgp.c_unif.chart_over FA x ⟨hbO, hbs⟩ hbV hP
    exact ⟨x, hx, V', g, hc, hi himm⟩
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAnalyticDataUniformisedStatement

section

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

theorem _root_.GlobalTheory.T.flag_analytic_data_uniformised : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d), n = Fintype.card Ψ * j * (N - j) → d + 1 = antisymDegree Ψ N → IsUniformised (FA.S.comap some).A (FA.S.comap some).open' j (FA.S.comap some).potH := by
  first | exact @GlobalTheory.CompanionTheory.Relay.flag_analytic_data_uniformised | exact GlobalTheory.CompanionTheory.Relay.flag_analytic_data_uniformised | (intros; apply GlobalTheory.CompanionTheory.Relay.flag_analytic_data_uniformised <;> assumption)
end
end
