module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.DivStatementPfLA
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MumfordGoodGrowthBoundBlocksOfBlockDiagonalStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MumfordGoodGrowthBoundCongrGermGramStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MumfordGoodGrowthBoundHolomorphicFrameChangeStatement
import Mathlib.Tactic.Basify
import Mathlib.Algebra.Azumaya.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolomorphicFrameChangeLocalBounds

section

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology

namespace GlobalTheory.HermFrame

theorem holo_contDiffOn {n : ℕ} {U : Set (ReciprocityTheory.L2DbarEstimates.V n)} (hU : IsOpen U)
    {g : ReciprocityTheory.L2DbarEstimates.V n → ℂ} (hg : DifferentiableOn ℂ g U) {m : WithTop ℕ∞} :
    ContDiffOn ℂ m g U := by
  have ha : AnalyticOnNhd ℂ g U := fun z hz =>
    ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA.analyticAt_of_diffOn hU hg hz
  exact ha.contDiffOn hU.uniqueDiffOn

theorem holo_fderiv_apply_on {n : ℕ} {U : Set (ReciprocityTheory.L2DbarEstimates.V n)} (hU : IsOpen U)
    {g : ReciprocityTheory.L2DbarEstimates.V n → ℂ} (hg : DifferentiableOn ℂ g U) (w : ReciprocityTheory.L2DbarEstimates.V n) :
    DifferentiableOn ℂ (fun u => fderiv ℂ g u w) U := by
  have h2 : ContDiffOn ℂ 2 g U := holo_contDiffOn hU hg
  have h1 : ContDiffOn ℂ 1 (fun u => fderiv ℂ g u) U := h2.fderiv_of_isOpen hU (by norm_num)
  exact (h1.clm_apply contDiffOn_const).differentiableOn (by norm_num)

theorem holo_del_eq_on {n : ℕ} {U : Set (ReciprocityTheory.L2DbarEstimates.V n)} (hU : IsOpen U)
    {g : ReciprocityTheory.L2DbarEstimates.V n → ℂ} (hg : DifferentiableOn ℂ g U) {u : ReciprocityTheory.L2DbarEstimates.V n}
    (hu : u ∈ U) (w : ReciprocityTheory.L2DbarEstimates.V n) : GlobalTheory.del g u w = fderiv ℂ g u w := by
  rw [GlobalTheory.del_eq_fderiv (hg.differentiableAt (hU.mem_nhds hu))]

end GlobalTheory.HermFrame

namespace GlobalTheory.HermFrame

theorem holo_mdel_entry {n : ℕ} {K : Type} {P : ReciprocityTheory.L2DbarEstimates.V n → Matrix K K ℂ}
    {U : Set (ReciprocityTheory.L2DbarEstimates.V n)} (hU : IsOpen U) (hP : ∀ i k, DifferentiableOn ℂ (fun u => P u i k) U)
    {u : ReciprocityTheory.L2DbarEstimates.V n} (hu : u ∈ U) (w : ReciprocityTheory.L2DbarEstimates.V n) (i k : K) :
    mdel P u w i k = fderiv ℂ (fun x => P x i k) u w :=
  holo_del_eq_on hU (hP i k) hu w

theorem holo_mdel_mdel_entry {n : ℕ} {K : Type} {P : ReciprocityTheory.L2DbarEstimates.V n → Matrix K K ℂ}
    {U : Set (ReciprocityTheory.L2DbarEstimates.V n)} (hU : IsOpen U) (hP : ∀ i k, DifferentiableOn ℂ (fun u => P u i k) U)
    {u : ReciprocityTheory.L2DbarEstimates.V n} (hu : u ∈ U) (w w' : ReciprocityTheory.L2DbarEstimates.V n) (i k : K) :
    mdel (fun x => mdel P x w') u w i k =
      fderiv ℂ (fun x => fderiv ℂ (fun y => P y i k) x w') u w := by
  change GlobalTheory.del (fun x => GlobalTheory.del (fun y => P y i k) x w') u w = _
  have hev : (fun x => GlobalTheory.del (fun y => P y i k) x w') =ᶠ[𝓝 u]
      (fun x => fderiv ℂ (fun y => P y i k) x w') := by
    filter_upwards [hU.mem_nhds hu] with x hx
    exact holo_del_eq_on hU (hP i k) hx w'
  rw [GlobalTheory.del_congr hev]
  exact holo_del_eq_on hU (holo_fderiv_apply_on hU (hP i k) w') hu w

theorem holoFrame_local_bounds : ∀ (n : ℕ) (K : Type) [Fintype K] [DecidableEq K] (P : ReciprocityTheory.L2DbarEstimates.V n → Matrix K K ℂ) (r : ℝ), 0 < r → (∀ i k, DifferentiableOn ℂ (fun u => P u i k) (Metric.ball 0 r)) → IsUnit (P 0).det → ∃ r' : ℝ, 0 < r' ∧ r' ≤ r ∧ ∃ B : ℝ, ∀ v : ReciprocityTheory.L2DbarEstimates.V n, ‖v‖ < r' → IsUnit (P v).det ∧ (∀ i k, ContDiffAt ℝ 2 (fun u => P u i k) v) ∧ (∀ᶠ u in nhds v, ∀ η, GlobalTheory.HermFrame.mdbar P u η = 0) ∧ (∀ i k, ‖P v i k‖ ≤ B) ∧ (∀ i k, ‖(P v)⁻¹ i k‖ ≤ B) ∧ (∀ a i k, ‖GlobalTheory.HermFrame.mdel P v (GlobalTheory.GoodMetric.coordVec a) i k‖ ≤ B) ∧ (∀ a b i k, ‖GlobalTheory.HermFrame.mdel (fun u => GlobalTheory.HermFrame.mdel P u (GlobalTheory.GoodMetric.coordVec b)) v (GlobalTheory.GoodMetric.coordVec a) i k‖ ≤ B) := by
  intro n K _ _ P r hr hP h0
  set U : Set (ReciprocityTheory.L2DbarEstimates.V n) := Metric.ball 0 r with hUdef
  have hU : IsOpen U := Metric.isOpen_ball
  have hPc : ContinuousOn P U :=
    continuousOn_pi.2 fun i => continuousOn_pi.2 fun k => (hP i k).continuousOn
  have hdetc : ContinuousOn (fun u => (P u).det) U :=
    (continuous_id.matrix_det).comp_continuousOn hPc
  have hadjc : ∀ i k, ContinuousOn (fun u => (P u).adjugate i k) U := fun i k =>
    ((continuous_id.matrix_adjugate).matrix_elem i k).comp_continuousOn hPc
  have h0U : (0 : ReciprocityTheory.L2DbarEstimates.V n) ∈ U := Metric.mem_ball_self hr
  have hev : ∀ᶠ u in 𝓝 (0 : ReciprocityTheory.L2DbarEstimates.V n), (P u).det ≠ 0 :=
    (hdetc.continuousAt (hU.mem_nhds h0U)).eventually_ne h0.ne_zero
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  have hm : 0 < min ε r := lt_min hε hr
  set ρ := min ε r / 2 with hρ
  have hρpos : 0 < ρ := by rw [hρ]; linarith
  have hρε : ρ < ε := by have := min_le_left ε r; rw [hρ]; linarith
  have hρr : ρ < r := by have := min_le_right ε r; rw [hρ]; linarith
  set S := Metric.closedBall (0 : ReciprocityTheory.L2DbarEstimates.V n) ρ with hSdef
  have hSU : S ⊆ U := Metric.closedBall_subset_ball hρr
  have hSdet : ∀ u ∈ S, (P u).det ≠ 0 := fun u hu =>
    hball u (Metric.closedBall_subset_ball hρε hu)
  have hSc : IsCompact S := isCompact_closedBall 0 ρ

  let G1 : ReciprocityTheory.L2DbarEstimates.V n → (K → K → ℂ) := fun u i k => P u i k
  let G2 : ReciprocityTheory.L2DbarEstimates.V n → (K → K → ℂ) := fun u i k => (P u)⁻¹ i k
  let G3 : ReciprocityTheory.L2DbarEstimates.V n → (Fin n → K → K → ℂ) := fun u a i k =>
    mdel P u (GlobalTheory.GoodMetric.coordVec a) i k
  let G4 : ReciprocityTheory.L2DbarEstimates.V n → (Fin n → Fin n → K → K → ℂ) := fun u a b i k =>
    mdel (fun u => mdel P u (GlobalTheory.GoodMetric.coordVec b)) u (GlobalTheory.GoodMetric.coordVec a) i k
  have hG1 : ContinuousOn G1 S :=
    continuousOn_pi.2 fun i => continuousOn_pi.2 fun k => ((hP i k).continuousOn).mono hSU
  have hG2 : ContinuousOn G2 S := by
    refine continuousOn_pi.2 fun i => continuousOn_pi.2 fun k => ?_
    refine (((hdetc.mono hSU).inv₀ hSdet).mul ((hadjc i k).mono hSU)).congr fun u _ => ?_
    simp [G2, Matrix.inv_def, Ring.inverse_eq_inv']
  have hG3 : ContinuousOn G3 S := by
    refine continuousOn_pi.2 fun a => continuousOn_pi.2 fun i => continuousOn_pi.2 fun k => ?_
    refine ((holo_fderiv_apply_on hU (hP i k) (GlobalTheory.GoodMetric.coordVec a)).continuousOn.mono
      hSU).congr fun u hu => ?_
    exact holo_mdel_entry hU hP (hSU hu) _ i k
  have hG4 : ContinuousOn G4 S := by
    refine continuousOn_pi.2 fun a => continuousOn_pi.2 fun b => continuousOn_pi.2 fun i =>
      continuousOn_pi.2 fun k => ?_
    refine ((holo_fderiv_apply_on hU (holo_fderiv_apply_on hU (hP i k)
      (GlobalTheory.GoodMetric.coordVec b)) (GlobalTheory.GoodMetric.coordVec a)).continuousOn.mono hSU).congr
      fun u hu => ?_
    exact holo_mdel_mdel_entry hU hP (hSU hu) _ _ i k
  obtain ⟨C1, hC1⟩ := hSc.exists_bound_of_continuousOn hG1
  obtain ⟨C2, hC2⟩ := hSc.exists_bound_of_continuousOn hG2
  obtain ⟨C3, hC3⟩ := hSc.exists_bound_of_continuousOn hG3
  obtain ⟨C4, hC4⟩ := hSc.exists_bound_of_continuousOn hG4
  refine ⟨ρ, hρpos, hρr.le, max (max C1 C2) (max C3 C4), fun v hv => ?_⟩
  have hvS : v ∈ S := by
    rw [hSdef, Metric.mem_closedBall, dist_zero_right]; exact hv.le
  have hvU : v ∈ U := hSU hvS
  refine ⟨isUnit_iff_ne_zero.2 (hSdet v hvS), fun i k => ?_, ?_, fun i k => ?_, fun i k => ?_,
    fun a i k => ?_, fun a b i k => ?_⟩
  · exact ((holo_contDiffOn hU (hP i k)).contDiffAt (hU.mem_nhds hvU)).restrict_scalars ℝ
  · filter_upwards [hU.mem_nhds hvU] with u hu η
    ext i k
    simp [GlobalTheory.dbar_eq_zero ((hP i k).differentiableAt (hU.mem_nhds hu))]
  · have h := (norm_le_pi_norm (G1 v i) k).trans ((norm_le_pi_norm (G1 v) i).trans (hC1 v hvS))
    exact h.trans ((le_max_left _ _).trans (le_max_left _ _))
  · have h := (norm_le_pi_norm (G2 v i) k).trans ((norm_le_pi_norm (G2 v) i).trans (hC2 v hvS))
    exact h.trans ((le_max_right _ _).trans (le_max_left _ _))
  · have h := (norm_le_pi_norm (G3 v a i) k).trans ((norm_le_pi_norm (G3 v a) i).trans
      ((norm_le_pi_norm (G3 v) a).trans (hC3 v hvS)))
    exact h.trans ((le_max_left _ _).trans (le_max_right _ _))
  · have h := (norm_le_pi_norm (G4 v a b i) k).trans ((norm_le_pi_norm (G4 v a b) i).trans
      ((norm_le_pi_norm (G4 v a) b).trans ((norm_le_pi_norm (G4 v) a).trans (hC4 v hvS))))
    exact h.trans ((le_max_right _ _).trans (le_max_right _ _))

end GlobalTheory.HermFrame
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolomorphicFrameChangeLocalBoundsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology


theorem _root_.GlobalTheory.T.holomorphicFrameChange_local_bounds : ∀ (n : ℕ) (K : Type) [Fintype K] [DecidableEq K] (P : ReciprocityTheory.L2DbarEstimates.V n → Matrix K K ℂ) (r : ℝ), 0 < r → (∀ i k, DifferentiableOn ℂ (fun u => P u i k) (Metric.ball 0 r)) → IsUnit (P 0).det → ∃ r' : ℝ, 0 < r' ∧ r' ≤ r ∧ ∃ B : ℝ, ∀ v : ReciprocityTheory.L2DbarEstimates.V n, ‖v‖ < r' → IsUnit (P v).det ∧ (∀ i k, ContDiffAt ℝ 2 (fun u => P u i k) v) ∧ (∀ᶠ u in nhds v, ∀ η, GlobalTheory.HermFrame.mdbar P u η = 0) ∧ (∀ i k, ‖P v i k‖ ≤ B) ∧ (∀ i k, ‖(P v)⁻¹ i k‖ ≤ B) ∧ (∀ a i k, ‖GlobalTheory.HermFrame.mdel P v (GlobalTheory.GoodMetric.coordVec a) i k‖ ≤ B) ∧ (∀ a b i k, ‖GlobalTheory.HermFrame.mdel (fun u => GlobalTheory.HermFrame.mdel P u (GlobalTheory.GoodMetric.coordVec b)) v (GlobalTheory.GoodMetric.coordVec a) i k‖ ≤ B) := by
  first | exact @GlobalTheory.HermFrame.holoFrame_local_bounds | exact GlobalTheory.HermFrame.holoFrame_local_bounds | (intros; apply GlobalTheory.HermFrame.holoFrame_local_bounds <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MumfordGoodGrowthBoundFrameChangeOrthogonalSumma

section

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.FrameGood
open ReciprocityTheory.L2DbarEstimates (V)

theorem goodBound_submatrix {n : ℕ} {K L : Type} [Fintype K] [DecidableEq K] [Fintype L] [DecidableEq L]
    (e : K ≃ L) {S : Finset (Fin n)} {c : ℝ} {N : ℕ} {G : V n → Matrix L L ℂ} {v : V n}
    (h : GoodBound S c N G v) : GoodBound S c N (fun u => (G u).submatrix e e) v := by
  refine ⟨fun i j => h.entry (e i) (e j), ?_, ?_, ?_, ?_⟩
  · simpa only [det_submatrix_equiv_self] using h.det
  · intro a i j
    simpa only [GlobalTheory.HermFrame.conn_submatrix_equiv, Matrix.submatrix_apply]
      using h.form a (e i) (e j)
  · intro a b i j
    simpa only [GlobalTheory.HermFrame.curv_submatrix_equiv, Matrix.submatrix_apply]
      using h.dbar a b (e i) (e j)
  · intro a b i j
    have h1 : ∀ ξ, (fun u => GlobalTheory.HermFrame.conn (fun x => (G x).submatrix e e) u ξ) =
        fun u => (GlobalTheory.HermFrame.conn G u ξ).submatrix e e :=
      fun ξ => funext fun u => GlobalTheory.HermFrame.conn_submatrix_equiv G e u ξ
    simp only [h1]
    exact h.del a b (e i) (e j)

theorem frame_summands_goodBound : ∀ (n g : ℕ) (S : Finset (Fin n)) (W : Set (ReciprocityTheory.L2DbarEstimates.V n)) (G₀ : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin g) (Fin g) ℂ) (c : ℝ) (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (m : ι → ℕ) (Q : ∀ τ : ι, ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin (m τ)) (Fin g) ℂ) (r : ℝ), IsOpen W → 0 < r → (∀ τ i k, DifferentiableOn ℂ (fun u => Q τ u i k) (Metric.ball 0 r)) → Fintype.card (Σ τ, Fin (m τ)) = g → LinearIndependent ℂ (fun p : Σ τ, Fin (m τ) => Q p.1 0 p.2) → (∀ v ∈ W, (G₀ v).det ≠ 0 ∧ (∀ i k, ContDiffAt ℝ 2 (fun u => G₀ u i k) v) ∧ GlobalTheory.GoodMetric.GoodBound S c N G₀ v) → (∀ v ∈ W, ∀ τ τ', τ ≠ τ' → Q τ v * G₀ v * (Q τ' v)ᴴ = 0) → ∃ r' : ℝ, 0 < r' ∧ ∃ (c' : ℝ) (N' : ℕ), ∀ v ∈ W, ‖v‖ < r' → ∀ τ, GlobalTheory.GoodMetric.GoodBound S c' N' (fun u => Q τ u * G₀ u * (Q τ u)ᴴ) v := by
  intro n g S W G₀ c N ι _ _ m Q r hW hr hQ hcard hind hG₀ horth
  let K := Σ τ, Fin (m τ)
  let e : K ≃ Fin g := Fintype.equivFinOfCardEq hcard
  let P : V n → Matrix K K ℂ := fun u => Matrix.of fun p k => Q p.1 u p.2 (e k)
  let G₁ : V n → Matrix K K ℂ := fun u => (G₀ u).submatrix e e
  have hP : ∀ i k, DifferentiableOn ℂ (fun u => P u i k) (Metric.ball 0 r) := fun i k => hQ i.1 i.2 (e k)
  have hP0 : IsUnit (P 0).det := by
    rw [← isUnit_iff_isUnit_det, ← linearIndependent_row_iff_isUnit]
    have h2 := hind.map' _ (LinearEquiv.ker (LinearEquiv.funCongrLeft ℂ ℂ e))
    have h3 : (P 0).row = ⇑(LinearEquiv.funCongrLeft ℂ ℂ e) ∘ fun p => Q p.1 0 p.2 := by
      funext p k; rfl
    rw [h3]; exact h2
  have hG₁ : ∀ v ∈ W, (G₁ v).det ≠ 0 ∧ (∀ i k, ContDiffAt ℝ 2 (fun u => G₁ u i k) v) ∧
      GoodBound S c N G₁ v := by
    intro v hv
    obtain ⟨h1, h2, h3⟩ := hG₀ v hv
    exact ⟨by simpa [G₁, det_submatrix_equiv_self] using h1, fun i k => h2 (e i) (e k),
      goodBound_submatrix e h3⟩
  obtain ⟨r₁, hr₁, -, B, hB⟩ := GlobalTheory.T.holomorphicFrameChange_local_bounds n K P r hr hP hP0
  obtain ⟨c₁, hc₁⟩ := GlobalTheory.T.mumfordGoodGrowthBound_holomorphic_frameChange n K S c N B
  let Gb : V n → Matrix K K ℂ := fun u => blockDiagonal' fun τ => Q τ u * G₀ u * (Q τ u)ᴴ
  obtain ⟨c', N', h3⟩ := GlobalTheory.T.mumfordGoodGrowthBound_blocks_of_blockDiagonal n S ι m (fun τ u => Q τ u * G₀ u * (Q τ u)ᴴ) c₁ N
  refine ⟨min r₁ (1 / 2), by positivity, c', N', fun v hv hvr τ => ?_⟩
  have hv1 : ‖v‖ < r₁ := hvr.trans_le (min_le_left _ _)
  have hv2 : ‖v‖ < 1 / 2 := hvr.trans_le (min_le_right _ _)
  obtain ⟨hPu, hPc, hPd, hPb, hPib, hPdb, hPddb⟩ := hB v hv1
  obtain ⟨hdet, hC, hgb⟩ := hG₁ v hv
  obtain ⟨d1, c1, g1⟩ := hc₁ G₁ P v (by linarith) hdet hC hPc hPd hPu hPb hPib hPdb hPddb hgb
  have heq : ∀ u ∈ W, P u * G₁ u * (P u)ᴴ = Gb u := by
    intro u hu
    ext ⟨τ, i⟩ ⟨τ', j⟩
    have key : (P u * G₁ u * (P u)ᴴ) ⟨τ, i⟩ ⟨τ', j⟩ = (Q τ u * G₀ u * (Q τ' u)ᴴ) i j := by
      simp only [P, G₁, Matrix.mul_apply, conjTranspose_apply, of_apply, submatrix_apply]
      exact Fintype.sum_equiv e _ _ fun l => by
        congr 1
        exact Fintype.sum_equiv e _ _ fun k => rfl
    by_cases hτ : τ = τ'
    · subst hτ
      rw [key]
      simp only [Gb, blockDiagonal'_apply_eq]
    · rw [key, horth u hu τ τ' hτ]
      simp only [Gb, blockDiagonal'_apply_ne _ _ _ hτ, Matrix.zero_apply]
  have hev : (fun u => P u * G₁ u * (P u)ᴴ) =ᶠ[𝓝 v] Gb :=
    Filter.eventually_of_mem (hW.mem_nhds hv) heq
  refine h3 v (fun a _ => (PiLp.norm_apply_le v a).trans_lt hv2) ?_ ?_ ?_ τ
  · change (Gb v).det ≠ 0
    rw [← heq v hv]; exact d1
  · intro p q
    exact (c1 p q).congr_of_eventuallyEq (hev.mono fun u hu => by
      exact (congrFun (congrFun hu p) q).symm)
  · exact GlobalTheory.T.mumfordGoodGrowthBound_congr_germ_gram n K S c₁ N _ Gb v hev g1

end GlobalTheory.FrameGood
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MumfordGoodGrowthBoundFrameChangeOrthogonalSummaStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology

theorem _root_.GlobalTheory.T.mumfordGoodGrowthBound_frameChange_orthogonalSummands : ∀ (n g : ℕ) (S : Finset (Fin n)) (W : Set (ReciprocityTheory.L2DbarEstimates.V n)) (G₀ : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin g) (Fin g) ℂ) (c : ℝ) (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (m : ι → ℕ) (Q : ∀ τ : ι, ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin (m τ)) (Fin g) ℂ) (r : ℝ), IsOpen W → 0 < r → (∀ τ i k, DifferentiableOn ℂ (fun u => Q τ u i k) (Metric.ball 0 r)) → Fintype.card (Σ τ, Fin (m τ)) = g → LinearIndependent ℂ (fun p : Σ τ, Fin (m τ) => Q p.1 0 p.2) → (∀ v ∈ W, (G₀ v).det ≠ 0 ∧ (∀ i k, ContDiffAt ℝ 2 (fun u => G₀ u i k) v) ∧ GlobalTheory.GoodMetric.GoodBound S c N G₀ v) → (∀ v ∈ W, ∀ τ τ', τ ≠ τ' → Q τ v * G₀ v * (Q τ' v)ᴴ = 0) → ∃ r' : ℝ, 0 < r' ∧ ∃ (c' : ℝ) (N' : ℕ), ∀ v ∈ W, ‖v‖ < r' → ∀ τ, GlobalTheory.GoodMetric.GoodBound S c' N' (fun u => Q τ u * G₀ u * (Q τ u)ᴴ) v := by
  first | exact @GlobalTheory.FrameGood.frame_summands_goodBound | exact GlobalTheory.FrameGood.frame_summands_goodBound | (intros; apply GlobalTheory.FrameGood.frame_summands_goodBound <;> assumption)
end
end
