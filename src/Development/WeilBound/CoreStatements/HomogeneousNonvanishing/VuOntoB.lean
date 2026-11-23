module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecondCountableTopologyOfIsProjOver
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.OffZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenframeSpecializationUniformBoundStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormFactorInvLePowHolomorphicOrbitPeriodBoundStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsChartLieBasisMatrices
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameBorelGroupoidProperties
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundaryArcLiftNotConvergesSymmetricDomainStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsArcLiftPeriodsTendstoSpanStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFramePointEigenframe
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicFrameOrbitLiftOfArcStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicFrameOrbitUnipotentOrderTwoStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolomorphicFrameOrbitIsotropicVectorShortStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TendstoPowMulExp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrivialMonodromyOrbitConvergesSymmetricDomainStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRiemannExtensionAnalytic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.WeilBound.CoreStatements.ProjectiveValuations.ExistsFrBorOfMatches
public import Development.WeilBound.CoreStatements.ProjectiveValuations.FrequentlyNeZero
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsVanBdOfMemExtVanZ
public import Development.WeilBound.CoreStatements.ProjectiveValuations.ExistsChartFrBor
import Mathlib.Algebra.Azumaya.Basic

-- Source module: Development.WeilBound.CoreStatements.ProjectiveValuations.DifferentiableAtOfLines

section

@[expose] public section

namespace DifferentiableLines

open Metric Filter Topology Set Complex
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.RiemannExtensionAnalytic

open scoped Real

theorem differentiableAt_of_lines {k : ℕ} {U O : Set (Fin k → ℂ)} {g f : (Fin k → ℂ) → ℂ}
    (hU : IsOpen U) (hO : IsOpen O) (hg : DifferentiableOn ℂ g U) (hgO : ∀ t ∈ U, g t ≠ 0 → t ∈ O)
    (hf : DifferentiableOn ℂ f O)
    (hl : ∀ τ ∈ U, τ ∉ O → ∀ v : Fin k → ℂ, (∀ᶠ z : ℂ in 𝓝[≠] 0, τ + z • v ∈ O) →
      Tendsto (fun z : ℂ => f (τ + z • v)) (𝓝[≠] 0) (𝓝 (f τ)))
    {τ₀ : Fin k → ℂ} (hτ₀ : τ₀ ∈ U) (hne : ∀ r > 0, ∃ t ∈ ball τ₀ r, g t ≠ 0) : DifferentiableAt ℂ f τ₀ := by
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU τ₀ hτ₀
  obtain ⟨t₁, ht₁, hgt₁⟩ := hne (r / 2) (by linarith)
  set v : Fin k → ℂ := t₁ - τ₀ with hvdef
  have hv : ‖v‖ < r / 2 := by
    rw [hvdef, ← dist_eq_norm]
    exact ht₁
  have hline : ∀ τ ∈ ball τ₀ (r / 4), ∀ z : ℂ, ‖z‖ < 3 / 2 → τ + z • v ∈ U := by
    intro τ hτ z hz
    apply hrU
    rw [mem_ball, dist_eq_norm] at hτ ⊢
    have h1 : ‖τ + z • v - τ₀‖ ≤ ‖τ - τ₀‖ + ‖z‖ * ‖v‖ := by
      rw [← norm_smul]
      calc ‖τ + z • v - τ₀‖ = ‖(τ - τ₀) + z • v‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    have h2 : ‖z‖ * ‖v‖ ≤ 3 / 2 * (r / 2) := mul_le_mul hz.le hv.le (norm_nonneg _) (by norm_num)
    linarith
  have hlined : ∀ (τ : Fin k → ℂ) (z : ℂ), DifferentiableAt ℂ (fun z : ℂ => τ + z • v) z := by
    intro τ z
    fun_prop
  have hga : ∀ τ ∈ ball τ₀ (r / 4), AnalyticOnNhd ℂ (fun z : ℂ => g (τ + z • v)) (ball 0 (3 / 2)) := by
    intro τ hτ
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) isOpen_ball
    have h1 : DifferentiableAt ℂ g (τ + z • v) :=
      hg.differentiableAt (hU.mem_nhds (hline τ hτ z (mem_ball_zero_iff.mp hz)))
    exact (h1.comp z (hlined τ z)).differentiableWithinAt
  have hiso : ∀ τ ∈ ball τ₀ (r / 4), ∀ z₁ ∈ ball (0 : ℂ) (3 / 2), g (τ + z₁ • v) ≠ 0 →
      ∀ z₀ ∈ ball (0 : ℂ) (3 / 2), ∀ᶠ z in 𝓝[≠] z₀, g (τ + z • v) ≠ 0 := fun τ hτ z₁ hz₁ h z₀ hz₀ =>
    (hga τ hτ z₀ hz₀).eventually_eq_zero_or_eventually_ne_zero.resolve_left fun h' =>
      h ((hga τ hτ).eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball _ _).isPreconnected hz₀ h' hz₁)
  have hτ₀b : τ₀ ∈ ball τ₀ (r / 4) := mem_ball_self (by linarith)
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) (3 / 2) := mem_ball_self (by norm_num)
  have h1 : (1 : ℂ) ∈ ball (0 : ℂ) (3 / 2) := by
    rw [mem_ball_zero_iff]
    norm_num
  obtain ⟨ε, hε, hεφ⟩ : ∃ ε > 0, ∀ z : ℂ, dist z 0 < ε → z ≠ 0 → g (τ₀ + z • v) ≠ 0 :=
    Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp
      (hiso τ₀ hτ₀b 1 h1 (by simpa [hvdef] using hgt₁) 0 h0))
  set ρ : ℝ := min ε 1 / 2 with hρdef
  have hm : 0 < min ε 1 := lt_min hε one_pos
  have hρ : 0 < ρ := by positivity
  have hρε : ρ < ε := by
    have := min_le_left ε 1
    linarith
  have hρ1 : ρ < 3 / 2 := by
    have := min_le_right ε 1
    linarith
  have hO' : IsOpen (U ∩ {t | g t ≠ 0}) := hg.continuousOn.isOpen_inter_preimage hU isOpen_compl_singleton
  have hsph₀ : ∀ z ∈ sphere (0 : ℂ) ρ, τ₀ + z • v ∈ U ∩ {t | g t ≠ 0} := by
    intro z hz
    have hz' : ‖z‖ = ρ := mem_sphere_zero_iff_norm.mp hz
    refine ⟨hline τ₀ hτ₀b z (by linarith), hεφ z (by rw [dist_zero_right]; linarith) ?_⟩
    rintro rfl
    rw [norm_zero] at hz'
    linarith
  have hev : ∀ᶠ τ in 𝓝 τ₀, ∀ z ∈ sphere (0 : ℂ) ρ, τ + z • v ∈ U ∩ {t | g t ≠ 0} := by
    refine (isCompact_sphere (0 : ℂ) ρ).eventually_forall_of_forall_eventually fun z hz => ?_
    have hPc : Continuous fun p : (Fin k → ℂ) × ℂ => p.1 + p.2 • v := by fun_prop
    exact hPc.continuousAt.preimage_mem_nhds (hO'.mem_nhds (hsph₀ z hz))
  obtain ⟨δ₀, hδ₀, hδ₀K⟩ := Metric.eventually_nhds_iff.mp hev
  set δ : ℝ := min (δ₀ / 2) (r / 8) with hδdef
  have hδ : 0 < δ := by positivity
  have hδcl : closedBall τ₀ δ ⊆ ball τ₀ δ₀ := closedBall_subset_ball (by
    have := min_le_left (δ₀ / 2) (r / 8)
    linarith)
  have hδr : ball τ₀ δ ⊆ ball τ₀ (r / 4) := ball_subset_ball (by
    have := min_le_right (δ₀ / 2) (r / 8)
    linarith)
  have hK : ∀ τ ∈ closedBall τ₀ δ, ∀ z ∈ sphere (0 : ℂ) ρ, τ + z • v ∈ U ∩ {t | g t ≠ 0} :=
    fun τ hτ => hδ₀K (hδcl hτ)
  have hdiff := differentiableOn_circleAverage hO hf hρ.le fun τ hτ z hz => hgO _ (hK τ hτ z hz).1 (hK τ hτ z hz).2
  refine (((hdiff.const_mul I).const_mul (2 * π * I : ℂ)⁻¹).differentiableAt (ball_mem_nhds τ₀ hδ)).congr_of_eventuallyEq ?_
  filter_upwards [ball_mem_nhds τ₀ hδ] with τ hτ
  have hτr := hδr hτ
  have hρs : (ρ : ℂ) ∈ sphere (0 : ℂ) ρ := by simp [abs_of_pos hρ]
  have hρb : (ρ : ℂ) ∈ ball (0 : ℂ) (3 / 2) := by simpa [abs_of_pos hρ] using hρ1
  have hin : ∀ z, τ + z • v ∈ O → DifferentiableAt ℂ (fun z : ℂ => f (τ + z • v)) z := fun z hz =>
    (hf.differentiableAt (hO.mem_nhds hz)).comp z (hlined τ z)
  have hH : ∀ z₀ ∈ ball (0 : ℂ) (3 / 2), DifferentiableAt ℂ (fun z : ℂ => f (τ + z • v)) z₀ := by
    intro z₀ hz₀
    by_cases hz : τ + z₀ • v ∈ O
    · exact hin z₀ hz
    have e₁ : ∀ᶠ z in 𝓝[≠] z₀, τ + z • v ∈ O := by
      filter_upwards [hiso τ hτr ρ hρb (hK τ (ball_subset_closedBall hτ) ρ hρs).2 z₀ hz₀,
        mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds hz₀)] with z h h'
      exact hgO _ (hline τ hτr z (mem_ball_zero_iff.mp h')) h
    have t₁ : Tendsto (fun w : ℂ => z₀ + w) (𝓝[≠] 0) (𝓝[≠] z₀) :=
      tendsto_nhdsWithin_iff.2 ⟨by
        simpa using ((show Continuous (fun w : ℂ => z₀ + w) by fun_prop).tendsto 0).mono_left (nhdsWithin_le_nhds (s := {0}ᶜ)),
        eventually_mem_nhdsWithin.mono fun w hw => by simpa using hw⟩
    have t₂ : Tendsto (fun z : ℂ => z - z₀) (𝓝[≠] z₀) (𝓝[≠] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨by
        simpa using ((continuous_sub_right z₀).tendsto z₀).mono_left (nhdsWithin_le_nhds (s := {z₀}ᶜ)),
        eventually_mem_nhdsWithin.mono fun w hw => by simpa [sub_eq_zero] using hw⟩
    have e₂ := hl _ (hline τ hτr z₀ (mem_ball_zero_iff.mp hz₀)) hz v
      ((t₁.eventually e₁).mono fun w hw => by rwa [add_smul, ← add_assoc] at hw)
    have e₃ : Tendsto (fun z : ℂ => f (τ + z • v)) (𝓝[≠] z₀) (𝓝 (f (τ + z₀ • v))) :=
      (e₂.comp t₂).congr fun z => by simp only [Function.comp_apply, add_assoc, ← add_smul, add_sub_cancel]
    exact (analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt (e₁.mono hin)
      (continuousAt_iff_punctured_nhds.2 e₃)).differentiableAt
  have hcl : closedBall (0 : ℂ) ρ ⊆ ball 0 (3 / 2) := closedBall_subset_ball hρ1
  have hC := two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
    (s := ∅) countable_empty (mem_ball_self hρ)
    (fun z hz => (hH z (hcl hz)).continuousAt.continuousWithinAt)
    (fun z hz => hH z (hcl (ball_subset_closedBall hz.1)))
  simp only [sub_zero, zero_smul, add_zero] at hC
  rw [circleIntegral_inv_smul_eq hρ.ne' (fun z => f (τ + z • v)), smul_eq_mul] at hC
  exact hC.symm

end DifferentiableLines
end
end

-- Source module: Development.WeilBound.CoreStatements.HomogeneousNonvanishing.VuOntoB

section

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.OntoDef GlobalTheory.CompHS
open GlobalTheory.CompanionTheory.Ar.HolExt DifferentiableLines

noncomputable section

namespace PositivityTheory.UnitarySelfGeneration.VuOnto

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {r : ℕ} {σ : c.F →+* ℂ}

section ThetaShiftProofs

open Limits GlobalTheory.CxPts Filter Topology GlobalTheory.ShFam GlobalTheory.ShFam.BdArc GlobalTheory.Toroidal MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory



theorem tendsto_arc_readsZ {V : Unf Xo c σ r} (hσ : GoodEmb c σ) (hU : IsUnf V) (T : TorFlag Xo c)
    {ee : Ix D → ℤ} (hee : ee none = 0) {k : V.Comp} {la : ReciprocityTheory.ChartRestriction.G.FD.Wt (V.X k).Ψ r}
    {P : Frame (V.X k).Ψ r → ℂ} (hP : P ∈ (V.X k).SS la)
    {h : (T.X.LL ee).ι → GlobalTheory.CxPts (flagStr T.X) σ → ℂ}
    (hR : Reads V T ee k P h) (hZ : OffZero V T k h) (i : T.X.F.J)
    {W : T.X.YY.Opens} (hW : IsAffineOpen W) [IsDomain Γ(T.X.YY, W)] (hWi : W ≤ T.X.F.U i)
    (s : ℂ → GlobalTheory.CxPts (flagStr T.X) σ) {ρ : ℝ} (hρ : 0 < ρ) (hsW : ∀ u ∈ Metric.ball (0 : ℂ) ρ, s u ∈ ptsIn _ σ W)
    (hsd : ∀ f : Γ(T.X.YY, W), DifferentiableOn ℂ (fun u => ev _ σ W f (s u)) (Metric.ball 0 ρ))
    (h0 : s 0 ∉ ptsIn _ σ (flagOpen T.X)) (h1 : ∀ u ∈ Metric.ball (0 : ℂ) ρ, u ≠ 0 → s u ∈ ptsIn _ σ (flagOpen T.X)) :
    Tendsto (fun u => h i (s u)) (𝓝[≠] 0) (𝓝 0) := by
  classical
  obtain ⟨-, g1, g2, -⟩ := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H D l Xo c (CAt σ)
  let A : Type := Γ(T.X.YY, W)
  let q : Sp A ⟶ T.X.YY := GlobalTheory.FlagMod.tau hW
  let φ : c.F →+* A := (GlobalTheory.FlagMod.ev (q ≫ flagStr T.X) ⊤ le_top).comp (toΓ c.F)
  have hφ : q ≫ flagStr T.X = spMap φ := (GlobalTheory.FlagMod.spMap_ev_top _).symm
  have hz : ⊤ ≤ q ⁻¹ᵁ T.X.F.U i := GlobalTheory.FlagMod.tau_le hW hWi
  have hxc : (q ≫ T.X.π) ≫ T.Y.s = spMap φ ≫ spMap (RingHom.id c.F) :=
    ((Category.assoc _ _ _).trans hφ).trans ((Category.comp_id _).symm.trans (congrArg (_ ≫ ·) (Spec.map_id _).symm))
  let x : Sp A ⟶ gen T.Y := pullback.lift _ _ hxc
  have hx : q ≫ T.X.π = x ≫ genι T.Y := (pullback.lift_fst _ _ _).symm
  have hxs : x ≫ genStr T.Y = spMap φ := pullback.lift_snd _ _ _
  obtain ⟨fr, hfr⟩ := exists_eigFrame_tau T hW hφ i hz hx
  have hb0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) ρ := Metric.mem_ball_self hρ
  let ψ : ℂ → (A →+* ℂ) := fun u => if hu : u ∈ Metric.ball (0 : ℂ) ρ then
    GlobalTheory.FlagMod.ev (s u).1 W (hsW u hu) else GlobalTheory.FlagMod.ev (s 0).1 W (hsW 0 hb0)
  have hψ : ∀ u (hu : u ∈ Metric.ball (0 : ℂ) ρ), ψ u = GlobalTheory.FlagMod.ev (s u).1 W (hsW u hu) := fun u hu => dif_pos hu
  have hψq : ∀ u ∈ Metric.ball (0 : ℂ) ρ, spMap (ψ u) ≫ q = (s u).1 := fun u hu => by
    rw [hψ u hu]
    exact GlobalTheory.FlagMod.spMap_ev (s u).1 hW _
  have hφu : ∀ u ∈ Metric.ball (0 : ℂ) ρ, (ψ u).comp φ = σ := fun u hu => by
    have e₁ : spMap ((ψ u).comp φ) = spMap (ψ u) ≫ spMap φ := Spec.map_comp _ _
    rw [← hφ, ← Category.assoc, hψq u hu, (s u).2] at e₁
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e₁)
  have key : ∀ u ∈ Metric.ball (0 : ℂ) ρ, ∀ p : Sp ℂ,
      (s u).1 p ∈ flagOpen T.X ↔ (spMap (ψ u) ≫ x) p ∉ genBd T.Y := by
    intro u hu p
    have := GlobalTheory.LogKS.isIso_fst T.Y
    have e : (s u).1 p ∈ flagOpen T.X ↔ genι T.Y ((spMap (ψ u) ≫ x) p) ∈ Set.range T.Y.j := by
      rw [← Scheme.Hom.comp_apply, Category.assoc, ← hx, ← Category.assoc, hψq u hu]
      exact Iff.rfl
    rw [e, mem_genBd, not_not]
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨a, (genι T.Y).isOpenEmbedding.injective (by rw [← ha]; rfl)⟩
    · rintro ⟨a, ha⟩
      exact ⟨a, by rw [← ha]; rfl⟩
  have hb : IsBdArc T.Y σ φ x ψ ρ := by
    refine ⟨⟨⟨hρ, fun f => (hsd f).congr fun u hu => ?_⟩, hxs, hφu⟩, fun p => ?_,
      fun u hu hne p => (key u hu p).1 (h1 u hu hne (Set.mem_univ p))⟩
    · rw [hψ u hu]
      exact (ev_eq (hsW u hu) f).symm
    · by_contra hp
      refine h0 (mem_ptsIn.2 ?_)
      rw [Subsingleton.elim (α := PrimeSpectrum ℂ) (IsLocalRing.closedPoint ℂ) p]
      exact (key 0 hb0 p).2 hp
  have hy' : ∀ u : ℂ, u ∈ Metric.ball (0 : ℂ) ρ ∧ u ≠ 0 → ∃ y : FrPt Xo c (CAt σ), Matches fr (ψ u) y :=
    fun u hu => GlobalTheory.ShFam.BdArc.exists_matches E H D l Xo c c.F (RingHom.id c.F) T.Y σ _ φ x fr (ψ u) hxs
      (hφu u hu.1) (hb.2.2 u hu.1 hu.2)
  have hr : ((ρ / 2 : ℝ) : ℂ) ∈ Metric.ball (0 : ℂ) ρ ∧ ((ρ / 2 : ℝ) : ℂ) ≠ 0 := by
    refine ⟨?_, by exact_mod_cast (half_pos hρ).ne'⟩
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg (half_pos hρ).le]
    exact half_lt_self hρ
  have : Nonempty (FrPt Xo c (CAt σ)) := ⟨(hy' _ hr).choose⟩
  choose! y hy using hy'
  have hm : ∀ u ∈ Metric.ball (0 : ℂ) ρ, u ≠ 0 → Matches fr (ψ u) (y u) := fun u hu hne => hy u ⟨hu, hne⟩
  obtain ⟨k', T₀, M₀, γ₀, xx, hT, hO₀, hL⟩ :=
    GlobalTheory.T.exists_holomorphicFrameOrbit_lift_of_arc E H D l Xo c _ _ T.Y σ r V A φ x fr ψ ρ y hσ hU hb.1 hm
  have hne0 : ∀ w, eTwoPi w ≠ 0 := fun w => Complex.exp_ne_zero _
  have hi : ∀ u ∈ Metric.ball (0 : ℂ) ρ, ⊤ ≤ zOf (s u) ⁻¹ᵁ T.X.F.U i := fun u hu => ptsIn_mono hWi (hsW u hu)
  have hfb : ∀ w (hw : T₀ < w.im), ∃ (hd : xx w ∈ (V.X k').dom) (Q : FrPt Xo c (CAt σ)) (t : Ix D → (CAt σ)ˣ),
      T.X.F.ChartFr i (zOf (s (eTwoPi w))) (hi _ (hT w hw)) Q ∧ FrBor t Q (V.un k' ⟨_, hd⟩) ∧ ∀ s, t (some s) = 1 := by
    intro w hw
    obtain ⟨hd, hl⟩ := hL w hw
    exact ⟨hd, exists_frBor_of_matches T q i hz hx fr hfr (ψ _)
      (matches_of_sameLie (hm _ (hT w hw) (hne0 w)) hl) (hψq _ (hT w hw)) _⟩
  have hev : ∀ᶠ w in imTop, T₀ < w.im := (tendsto_comap (f := Complex.im)).eventually (eventually_gt_atTop _)
  refine tendsto_punctured ?_
  by_cases hk : k' = k
  swap
  · refine tendsto_const_nhds.congr' (hev.mono fun w hw => (hZ i _ fun x' hx' e => hk ?_).symm)
    obtain ⟨hd, Q, t, hQ, ht, -⟩ := hfb w hw
    have e' : T.X.ptY (V.un k ⟨x', hx'⟩) = zOf (s (eTwoPi w)) := e
    have hlx : T.X.F.Lies (zOf (s (eTwoPi w))) (V.un k ⟨x', hx'⟩) := e' ▸ T.X.lies_ptY _
    obtain ⟨t', ht'⟩ := hQ.exists_frBor hlx
    obtain ⟨γ, -, β, -, h'⟩ := (hU.2.2.2.1 k' k _ _).1 ⟨_, g1 _ _ _ _ _ (g2 _ _ _ ht) ht'⟩
    exact (Sigma.mk.inj h').1.symm
  subst hk
  obtain ⟨M, γ, hO, hγ⟩ := GlobalTheory.T.exists_holomorphicFrameOrbit_unipotent_order_two E r _ T₀ M₀ γ₀ xx hO₀
  have hne : γ ≠ 1 := by
    rintro rfl
    obtain ⟨x₀, hx₀, x', a1, a2⟩ := GlobalTheory.T.trivial_monodromy_orbit_converges_symmetric_domain E r _ T₀ M xx hO
    exact GlobalTheory.T.boundary_arc_lift_not_converges_symmetric_domain E H D l Xo c _ _ T.Y σ r V A φ x fr ψ ρ y k' T₀ xx hσ hU hb hm hL x₀ hx₀ x' a1 a2
  obtain ⟨ξ, c', hξ, hc', ht⟩ := GlobalTheory.T.holomorphicFrameOrbit_isotropic_vector_short E r _ T₀ M γ xx hO hγ hne
  obtain ⟨m, v, Lp, Lm, hlim⟩ := GlobalTheory.T.exists_arcLift_periods_tendsto_span E H D l Xo c _ _ T.Y σ r V A φ x fr ψ ρ y k' T₀ M γ xx hσ hU hb.1 hm hO hL
  have hper := GlobalTheory.T.eigenframe_specialization_uniform_bound E H D l Xo c _ _ T.Y σ r V A φ x fr ψ ρ y k' T₀ M γ xx hσ hU hb.1 hm hO hL
  obtain ⟨C', B, hn⟩ := GlobalTheory.T.normFactor_inv_le_pow_holomorphicOrbit_periodBound E r _ T₀ M γ xx la m v Lp Lm hO hlim hper
  have hp := tendsto_cusp hP hO.2.2.2.1 hξ hc' ht hn
  refine hp.congr' ?_
  filter_upwards [hev] with w hw
  obtain ⟨hd, Q, t, hQ, ht, ht1⟩ := hfb w hw
  have hu := hT w hw
  have e₁ : P (xx w) = chr ee t * h i (s (eTwoPi w)) :=
    hR (xx w) hd i _ (hi _ hu) Q t (GlobalTheory.FlagMod.FlagCover.eq_ptY (hQ.lies.frBor ht)).symm hQ ht
  rw [chr_of_some ht1, hee, zpow_zero, one_mul] at e₁
  exact e₁

end ThetaShiftProofs

open GlobalTheory.CxPts Filter Topology ReciprocityTheory.ChartRestriction.G.DVR.FlatBC



theorem holoOn_bdZ {V : Unf Xo c σ r} (hσ : GoodEmb c σ) (hU : IsUnf V) (T : TorFlag Xo c)
    {ee : Ix D → ℤ} (hee : ee none = 0) {k : V.Comp} {la : ReciprocityTheory.ChartRestriction.G.FD.Wt (V.X k).Ψ r}
    {P : Frame (V.X k).Ψ r → ℂ} (hP : P ∈ (V.X k).SS la) {d : ℕ} [SmoothOfRelativeDimension d (flagStr T.X)]
    (R : GlobalTheory.AnRead (flagStr T.X) σ d)
    {h : (T.X.LL ee).ι → GlobalTheory.CxPts (flagStr T.X) σ → ℂ}
    (hR : Reads V T ee k P h) (hZ : OffZero V T k h)
    (hh : ∀ i, R.HoloOn (ptsIn _ σ ((T.X.LL ee).U i) ∩ ptsIn _ σ (flagOpen T.X)) (h i))
    (i : T.X.F.J) :
    R.HoloOn (ptsIn _ σ (T.X.F.U i)) (h i) := by
  intro j v hv
  have hs : Smooth (flagStr T.X) := SmoothOfRelativeDimension.smooth d _
  obtain ⟨-, hn, hl⟩ := GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field c.F _ _ hs
  have := GlobalTheory.IsNormalScheme.of_pred hn
  let C := R.chart j
  let L := EuclideanSpace.equiv (Fin d) ℂ
  let y₀ := C.e.symm v
  obtain ⟨W₁, hyW₁, hW₁⟩ := GlobalTheory.ModelChart.exists_open_isDomain T.X.YY (y₀.1 (IsLocalRing.closedPoint ℂ))
  obtain ⟨W, hW, hyW, hWle⟩ := GlobalTheory.Points.exists_isAffineOpen_le y₀.1
    (mem_ptsIn_inf.2 ⟨mem_ptsIn.2 hyW₁, hv.2⟩ : y₀ ∈ ptsIn _ σ (W₁ ⊓ T.X.F.U i))
  have hyW' : y₀ ∈ ptsIn _ σ W := hyW
  have := hW₁ W (mem_ptsIn.1 hyW') (hWle.trans inf_le_left)
  have hWi := hWle.trans inf_le_right
  obtain ⟨p, hpW, hpO⟩ := (dense_flagOpen T.X).inter_open_nonempty W W.isOpen ⟨_, mem_ptsIn.1 hyW'⟩
  obtain ⟨g, hgO, hpg⟩ := hW.exists_basicOpen_le (V := flagOpen T.X) ⟨p, hpO⟩ hpW
  have hg : g ≠ 0 := by
    rintro rfl
    rw [Scheme.basicOpen_zero] at hpg
    exact hpg
  let s : (Fin d → ℂ) → GlobalTheory.CxPts (flagStr T.X) σ := fun b => C.e.symm (L.symm b)
  have ho : ∀ {S}, IsOpen S → IsOpen (L.symm ⁻¹' (C.e.target ∩ C.e.symm ⁻¹' S)) := fun hS =>
    (GlobalTheory.ChartGlue.isOpen_over C.e hS).preimage L.symm.continuous
  have hU' := ho (isOpen_ptsIn W)
  have hd : ∀ f : Γ(T.X.YY, W), DifferentiableOn ℂ (fun b => ev _ σ W f (s b))
      (L.symm ⁻¹' (C.e.target ∩ C.e.symm ⁻¹' ptsIn _ σ W)) := fun f =>
    (C.holo W f).comp L.symm.differentiableOn fun _ hb => hb
  have key : DifferentiableAt ℂ (fun b => h i (s b)) (L v) := by
    refine differentiableAt_of_lines hU' (ho ((isOpen_ptsIn (T.X.F.U i)).inter (isOpen_ptsIn (flagOpen T.X)))) (hd g)
      (fun t ht h0 => ⟨ht.1, ptsIn_mono hWi ht.2, ptsIn_mono hgO ((mem_ptsIn_basicOpen ht.2 g).2 h0)⟩)
      ((hh i j).comp L.symm.differentiableOn fun _ hb => hb) (fun τ hτ hτO w hw => ?_)
      (by simpa using ⟨hv.1, hyW'⟩) fun ρ hρ => ?_
    · have hout : s τ ∉ ptsIn _ σ (flagOpen T.X) := fun h' => hτO ⟨hτ.1, ptsIn_mono hWi hτ.2, h'⟩
      have h0 : h i (s τ) = 0 := hZ i _ fun x hx e => hout (mem_open_of_ptY T _ _ e)
      have hline : Differentiable ℂ fun z : ℂ => τ + z • w := by fun_prop
      have hnb : ∀ᶠ z : ℂ in 𝓝 0, τ + z • w ∈ L.symm ⁻¹' (C.e.target ∩ C.e.symm ⁻¹' ptsIn _ σ W) :=
        hline.continuous.continuousAt.preimage_mem_nhds (hU'.mem_nhds (by simpa using hτ))
      obtain ⟨ρ, hρ, hb⟩ := Metric.eventually_nhds_iff_ball.1 (hnb.and (eventually_nhdsWithin_iff.1 hw))
      show Tendsto (fun z : ℂ => h i (s (τ + z • w))) _ (𝓝 (h i (s τ)))
      rw [h0]
      have b₁ : ∀ u ∈ Metric.ball (0 : ℂ) ρ, s (τ + u • w) ∈ ptsIn _ σ W := fun u hu => (hb u hu).1.2
      have b₂ : ∀ f : Γ(T.X.YY, W), DifferentiableOn ℂ (fun u : ℂ => ev _ σ W f (s (τ + u • w))) (Metric.ball 0 ρ) :=
        fun f => DifferentiableOn.comp (g := fun b => ev _ σ W f (s b)) (f := fun u : ℂ => τ + u • w) (hd f)
          hline.differentiableOn fun u hu => (hb u hu).1
      have b₃ : s (τ + (0 : ℂ) • w) ∉ ptsIn _ σ (flagOpen T.X) := by
        rw [zero_smul, add_zero]
        exact hout
      have b₄ : ∀ u ∈ Metric.ball (0 : ℂ) ρ, u ≠ 0 → s (τ + u • w) ∈ ptsIn _ σ (flagOpen T.X) :=
        fun u hu hu0 => ((hb u hu).2 hu0).2.2
      exact tendsto_arc_readsZ hσ hU T hee hP hR hZ i hW hWi (fun z => s (τ + z • w)) hρ b₁ b₂ b₃ b₄
    · have hsrc : y₀ ∈ C.e.source := C.e.map_target hv.1
      have hc : ContinuousAt (fun y => L (C.e y)) y₀ := L.continuous.continuousAt.comp (C.e.continuousAt hsrc)
      have hN : {y | L (C.e y) ∈ Metric.ball (L v) ρ} ∈ 𝓝 y₀ :=
        hc.preimage_mem_nhds (by rw [C.e.right_inv hv.1]; exact Metric.ball_mem_nhds _ hρ)
      obtain ⟨y', hy', hne⟩ := frequently_ne_zero (flagStr T.X) hW hg hyW'
        (inter_mem hN (C.e.open_source.mem_nhds hsrc))
      refine ⟨_, hy'.1, ?_⟩
      simp only [s, ContinuousLinearEquiv.symm_apply_apply]
      rwa [C.e.left_inv hy'.2]
  refine DifferentiableAt.differentiableWithinAt ?_
  refine (key.comp v L.differentiableAt).congr_of_eventuallyEq (Eventually.of_forall fun w => ?_)
  simp only [s, Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
  rfl

end PositivityTheory.UnitarySelfGeneration.VuOnto
end
end
end
