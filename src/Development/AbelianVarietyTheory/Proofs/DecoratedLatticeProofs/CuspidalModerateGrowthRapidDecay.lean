module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicUnitaryEveryPointHasCuspScale
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratedGainRapidDecayStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MeanValueIneqRightTranslateRealPointNearOne
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormLeOfCuspidalVariationUnipotentRadical
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RderMemAutFormsCuspForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOneP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GelfConstSmul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothAutomorphicFormRightTranslateFiniteAdelic
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsGrowthSobNeTopOfIsAutFunSm
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicUnitaryEveryPointHasCuspScaleStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta MeasureTheory NumberField Matrix GlobalTheory.CuspGeo
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.adelicUnitary_every_point_has_cusp_scale : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ V : HSp D, Near θ V := by
  first | exact @GlobalTheory.CuspGeo.near | exact GlobalTheory.CuspGeo.near | (intros; apply GlobalTheory.CuspGeo.near <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MeanValueIneqRightTranslateRealPointNearOneStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta MeasureTheory NumberField Matrix GlobalTheory.CuspGeo
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.meanValue_ineq_rightTranslate_realPoint_near_one : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ V : HSp D, ∃ (B : Finset (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)) (Ω : Set (GA D V)) (C δ₁ : ℝ), (∀ p ∈ B, p.2 ∈ lieAt V p.1) ∧ IsCompact Ω ∧ 0 < δ₁ ∧ 0 ≤ C ∧ ∀ ψ : GA D V → ℂ, SmoothW θ V ψ → ∀ (g u : GA D V) (δ : ℝ), 0 ≤ δ → δ ≤ δ₁ → CloseR θ V u δ → ∀ c : D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ → ℝ, (∀ p ∈ B, ∀ w ∈ Ω, ‖Rder θ V p.1 p.2 ψ (g * w)‖ ≤ c p) → ‖ψ (g * u) - ψ g‖ ≤ C * δ * ∑ p ∈ B, c p := by
  first | exact @GlobalTheory.CuspGeo.MeanValue.mean_value | exact GlobalTheory.CuspGeo.MeanValue.mean_value | (intros; apply GlobalTheory.CuspGeo.MeanValue.mean_value <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormLeOfCuspidalVariationUnipotentRadicalStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta MeasureTheory NumberField Matrix GlobalTheory.CuspGeo
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.norm_le_of_cuspidal_variation_unipotentRadical : ∀ (D : D7) (V : HSp D) (φ : GA D V → ℂ), IsAutFun V φ → IsCuspFun V φ → ∀ (r : ℕ) (C₀ : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C₀ → ∀ (g : GA D V) (e : ℝ), (∀ m ∈ NI V C₀, ‖φ (m * g) - φ g‖ ≤ e) → ‖φ g‖ ≤ e := by
  first | exact @GlobalTheory.CuspGeo.norm_le_of_unipRad_variation | exact GlobalTheory.CuspGeo.norm_le_of_unipRad_variation | (intros; apply GlobalTheory.CuspGeo.norm_le_of_unipRad_variation <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RightDerivativeSmoothCuspidalSameLevel

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta MeasureTheory NumberField Matrix GlobalTheory.CuspGeo
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Mem.Th GlobalTheory.Cusp GlobalTheory.Mem.AutSpace GlobalTheory.Mem.RealTranslate
open scoped TensorProduct Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspStab

theorem rder_stab : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (U : Subgroup (GA D V)) (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ), X ∈ lieAt V τ → ∀ (A : ℕ) (φ : GA D V → ℂ), IsAutFun V φ → (∀ k ∈ U, k ∈ GfC V → ∀ g, φ (g * k) = φ g) → SmoothW θ V φ → (∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) → GlobalTheory.Grow.ModGrowthExp V A (l.foldr (fun p f => Rder θ V p.1 p.2 f) φ)) → IsCuspFun V φ → IsAutFun V (Rder θ V τ X φ) ∧ (∀ k ∈ U, k ∈ GfC V → ∀ g, Rder θ V τ X φ (g * k) = Rder θ V τ X φ g) ∧ SmoothW θ V (Rder θ V τ X φ) ∧ (∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) → GlobalTheory.Grow.ModGrowthExp V A (l.foldr (fun p f => Rder θ V p.1 p.2 f) (Rder θ V τ X φ))) ∧ IsCuspFun V (Rder θ V τ X φ) := by
  intro D θ hθ V U τ X hX A φ ha hU hs hg hc
  have hs' : φ ∈ SmFun θ V := hs
  have inv : ∀ k, k ∈ GfC V → (∀ g, φ (g * k) = φ g) → ∀ g, Rder θ V τ X φ (g * k) = Rder θ V τ X φ g := by
    intro k hk e g
    have := congrFun (GlobalTheory.Mem.FinTranslate.Rder_rTr (θ := θ) hk τ X φ) g
    rw [show rTr V k φ = φ from funext e] at this
    exact this.symm
  have hcont : Continuous (Rder θ V τ X φ) := by
    refine GlobalTheory.Size.continuous_Rder_of_growth hθ hs' ha.cont hX (A := A) ?_
    simpa using hg [(τ, X), (τ, X)] (by simp [hX])
  have ha' : IsAutFun V (Rder θ V τ X φ) :=
    { left := fun γ hγ => GlobalTheory.Mem.Lift.Rder_left (ha.left γ hγ) τ X
      level := by
        obtain ⟨U₀, hU₀, e⟩ := ha.level
        exact ⟨U₀, hU₀, fun k hk hf => inv k hf (e k hk hf)⟩
      cont := hcont }
  refine ⟨ha', fun k hk hf => inv k hf (hU k hk hf), Rder_mem hs' hX, fun l hl => ?_, ?_⟩
  · have := hg (l ++ [(τ, X)]) (by
      intro p hp
      rcases List.mem_append.1 hp with h | h
      · exact hl p h
      · rw [List.mem_singleton.1 h]; exact hX)
    simpa only [List.foldr_append, List.foldr_cons, List.foldr_nil] using this
  · refine (isCuspFun_iff ha'.left).2 fun W hW => funext fun x => ?_
    have h0 : constTermOn (GQ V) (NA (.single hW)) φ = 0 := (isCuspFun_iff ha.left).1 hc W hW
    have := GlobalTheory.CuspLie.hasDerivAt_constTermOn (cocompact_single hW) ha.left ha.cont ha'.left ha'.cont
      (GlobalTheory.Mem.Lift.continuous_oneP hθ hX)
      (GlobalTheory.Mem.Lift.hasDerivAt_oneP hθ hX (GlobalTheory.Mem.Lift.hasDerivAt_Rder hs' hX)) x
    rw [h0, GlobalTheory.Mem.Lift.oneP_zero hθ, mul_one] at this
    exact this.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))

end GlobalTheory.CuspStab

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RightDerivativeSmoothCuspidalSameLevelStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta MeasureTheory NumberField Matrix GlobalTheory.CuspGeo
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rightDerivative_smoothCuspidal_same_level : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (U : Subgroup (GA D V)) (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ), X ∈ lieAt V τ → ∀ (A : ℕ) (φ : GA D V → ℂ), IsAutFun V φ → (∀ k ∈ U, k ∈ GfC V → ∀ g, φ (g * k) = φ g) → SmoothW θ V φ → (∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) → GlobalTheory.Grow.ModGrowthExp V A (l.foldr (fun p f => Rder θ V p.1 p.2 f) φ)) → IsCuspFun V φ → IsAutFun V (Rder θ V τ X φ) ∧ (∀ k ∈ U, k ∈ GfC V → ∀ g, Rder θ V τ X φ (g * k) = Rder θ V τ X φ g) ∧ SmoothW θ V (Rder θ V τ X φ) ∧ (∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) → GlobalTheory.Grow.ModGrowthExp V A (l.foldr (fun p f => Rder θ V p.1 p.2 f) (Rder θ V τ X φ))) ∧ IsCuspFun V (Rder θ V τ X φ) := by
  first | exact @GlobalTheory.CuspStab.rder_stab | exact GlobalTheory.CuspStab.rder_stab | (intros; apply GlobalTheory.CuspStab.rder_stab <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspidalModerateGrowthRapidDecay

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta MeasureTheory NumberField Matrix GlobalTheory.CuspGeo
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspGeo

theorem closeR_mono {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}
    {u : GA D V} {a a' : ℝ} (h : CloseR θ V u a) (hle : a ≤ a') : CloseR θ V u a' :=
  ⟨h.1, fun τ i j => (h.2 τ i j).trans hle⟩

theorem cuspDecayBound : GlobalTheory.Published.CuspDecayBound := by
  intro D θ hθ V U hU A N
  let Dr : D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ → (GA D V → ℂ) → GA D V → ℂ :=
    fun p f => Rder θ V p.1 p.2 f
  let 𝓒 : Set (GA D V → ℂ) := {φ | IsAutFun V φ ∧ (∀ k ∈ U, k ∈ GfC V → ∀ g, φ (g * k) = φ g) ∧ SmoothW θ V φ ∧
    (∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) →
      GlobalTheory.Grow.ModGrowthExp V A (l.foldr Dr φ)) ∧ IsCuspFun V φ}
  obtain ⟨B, Ω₀, Cm, δ₁, hB, hΩ₀, hδ₁, hCm, hmv⟩ := GlobalTheory.T.meanValue_ineq_rightTranslate_realPoint_near_one D θ hθ V
  obtain ⟨b, Cn, δn, hδn, hnear⟩ := GlobalTheory.T.adelicUnitary_every_point_has_cusp_scale D θ hθ V U hU
  obtain ⟨H, hH⟩ := GlobalTheory.Grow.exists_height_le_of_isCompact V hΩ₀
  have hstab : ∀ ψ ∈ 𝓒, ∀ i ∈ B, Dr i ψ ∈ 𝓒 := by
    rintro ψ ⟨ha, hlev, hs, hg, hc⟩ i hi
    exact GlobalTheory.T.rightDerivative_smoothCuspidal_same_level D θ hθ V U i.1 i.2 (hB i hi) A ψ ha hlev hs hg hc
  have hwords : ∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ i ∈ l, i ∈ B) →
      ∀ ψ ∈ 𝓒, l.foldr Dr ψ ∈ 𝓒 := by
    intro l
    induction l with
    | nil => intro _ ψ hψ; exact hψ
    | cons a l ih =>
      intro hl ψ hψ
      exact hstab _ (ih (fun i hi => hl i (List.mem_cons_of_mem _ hi)) ψ hψ) a (hl a List.mem_cons_self)
  set Cn' := max Cn 0 with hCn'
  have hCn'0 : 0 ≤ Cn' := le_max_right _ _
  set δ₀ := min δn (δ₁ / (Cn' + 1)) with hδ₀
  have hδ₀pos : 0 < δ₀ := lt_min hδn (div_pos hδ₁ (by linarith))
  set K := max (max Cn (Cm * Cn')) (max H 1) with hK
  have hK1 : Cn ≤ K := (le_max_left _ _).trans (le_max_left _ _)
  have hK2 : Cm * Cn' ≤ K := (le_max_right _ _).trans (le_max_left _ _)
  have hK3 : H ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hstep : ∀ g, ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ GlobalTheory.Grow.quotHeight V g * δ ^ b ≤ K ∧ (δ₀ ≤ δ ∨
      ∃ Ω : Set (GA D V), (∀ w ∈ Ω, GlobalTheory.Grow.quotHeight V w ≤ K * GlobalTheory.Grow.quotHeight V g ∧
        GlobalTheory.Grow.quotHeight V g ≤ K * GlobalTheory.Grow.quotHeight V w) ∧
      ∀ ψ ∈ 𝓒, ∀ c : D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ → ℝ,
        (∀ i ∈ B, 0 ≤ c i ∧ ∀ w ∈ Ω, ‖Dr i ψ w‖ ≤ c i) → ‖ψ g‖ ≤ K * δ * ∑ i ∈ B, c i) := by
    intro g
    obtain ⟨δ, hδ0, hδ1, hq, hcase⟩ := hnear g
    refine ⟨δ, hδ0, hδ1, hq.trans hK1, ?_⟩
    by_cases hδ : δ₀ ≤ δ
    · exact Or.inl hδ
    right
    push_neg at hδ
    have hδn' : ¬ δn ≤ δ := fun h => absurd (hδ.trans_le (min_le_left _ _)) (not_lt.2 h)
    obtain ⟨r, C₀, hC₀, hN⟩ := hcase.resolve_left hδn'
    have hsmall : Cn' * δ ≤ δ₁ := by
      have h1 : δ < δ₁ / (Cn' + 1) := hδ.trans_le (min_le_right _ _)
      rw [lt_div_iff₀ (by linarith)] at h1
      nlinarith
    refine ⟨(g * ·) '' Ω₀, ?_, ?_⟩
    · rintro _ ⟨w, hw, rfl⟩
      have hq0 := GlobalTheory.Grow.one_le_quotHeight V g
      have hq1 := GlobalTheory.Grow.one_le_quotHeight V (g * w)
      have hw1 := hH w hw
      constructor
      · calc GlobalTheory.Grow.quotHeight V (g * w) ≤ GlobalTheory.Grow.quotHeight V g * GlobalTheory.Grow.height V w :=
              GlobalTheory.Grow.quotHeight_mul_le V g w
          _ ≤ GlobalTheory.Grow.quotHeight V g * K := mul_le_mul_of_nonneg_left (hw1.trans hK3) (by linarith)
          _ = K * GlobalTheory.Grow.quotHeight V g := mul_comm _ _
      · calc GlobalTheory.Grow.quotHeight V g = GlobalTheory.Grow.quotHeight V (g * w * w⁻¹) := by rw [mul_inv_cancel_right]
          _ ≤ GlobalTheory.Grow.quotHeight V (g * w) * GlobalTheory.Grow.height V w⁻¹ := GlobalTheory.Grow.quotHeight_mul_le V _ _
          _ ≤ GlobalTheory.Grow.quotHeight V (g * w) * K := by
              rw [GlobalTheory.Grow.height_inv]; exact mul_le_mul_of_nonneg_left (hw1.trans hK3) (by linarith)
          _ = K * GlobalTheory.Grow.quotHeight V (g * w) := mul_comm _ _
    · rintro ψ ⟨ha, hlev, hs, hg, hc⟩ c hc'
      have hsum : 0 ≤ ∑ i ∈ B, c i := Finset.sum_nonneg fun i hi => (hc' i hi).1
      have hmain : ‖ψ g‖ ≤ Cm * (Cn' * δ) * ∑ p ∈ B, c p := by
        refine GlobalTheory.T.norm_le_of_cuspidal_variation_unipotentRadical D V ψ ha hc r C₀ hC₀ g _ fun m hm => ?_
        obtain ⟨γ, hγ, u, k, hu, hkU, hkf, hmg⟩ := hN m hm
        have hval : ψ (m * g) = ψ (g * u) := by
          rw [hmg, show γ * g * u * k = γ * (g * u) * k by group, hlev k hkU hkf, ha.left γ hγ]
        rw [hval]
        refine hmv ψ hs g u (Cn' * δ) (mul_nonneg hCn'0 hδ0.le) hsmall
          (closeR_mono hu (mul_le_mul_of_nonneg_right (le_max_left _ _) hδ0.le)) c fun p hp w hw => ?_
        exact (hc' p hp).2 _ ⟨w, hw, rfl⟩
      refine hmain.trans ?_
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK2 hδ0.le) hsum
  obtain ⟨L, C', hLB, hL⟩ := GlobalTheory.T.exists_rapid_decay_of_iterated_gain (GA D V) (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ) B
    (GlobalTheory.Grow.quotHeight V) 𝓒 Dr b K δ₀ hδ₀pos (GlobalTheory.Grow.one_le_quotHeight V) hstab hstep A N
  refine ⟨L, C' * 2 ^ A, fun l hl p hp => hB p (hLB l hl p hp), ?_⟩
  intro φ ha hlev hs hg hc c hcl g
  have hφ : φ ∈ 𝓒 := ⟨ha, hlev, hs, hg, hc⟩
  have h := hL φ hφ (fun l => c l * 2 ^ A) (fun l hl g' =>
    GlobalTheory.Grow.norm_le_quotHeight_pow (hwords l (hLB l hl) φ hφ).1.left (hcl l hl) g') g
  refine h.trans (le_of_eq ?_)
  rw [← Finset.sum_mul]
  ring

end GlobalTheory.CuspGeo
end
end
