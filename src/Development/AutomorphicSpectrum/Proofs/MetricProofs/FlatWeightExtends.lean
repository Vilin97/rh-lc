module

public import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.BoundedPshCorrectionLocallySmoothStatement
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
public import Mathlib.Geometry.Manifold.IsManifold.Basic
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
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SectionBoundaryClosedAndCodenseStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SingularPotentialLogGrowthPshStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.PshExtensionAcrossClosedDense

section

@[expose] public section

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.AnForm

theorem isPsh_of_dense_compl : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (B : Set X) (Q Q' : LocPot X), IsClosed B → Dense Bᶜ → (∀ x, Q'.U x = Q.U x) → (∀ x, A.SmoothOn (Q'.U x) (Q'.φ x)) → (∀ x, ∀ y ∈ Q.U x, y ∉ B → Q'.φ x y = Q.φ x y) → IsPshOn A Bᶜ Q → IsPsh A Q' := by
  intro e X _ A B Q Q' hB hD hU hS hE hP x j y hy w
  by_contra hneg
  have hneg' : levi (Q'.φ x ∘ (A.chart j).symm) y w < 0 := not_le.mp hneg
  have hO : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Q'.U x) :=
    (A.chart j).isOpen_inter_preimage_symm (Q'.isOpen_U x)
  have hf : ContDiffOn ℝ 2 (Q'.φ x ∘ (A.chart j).symm)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Q'.U x) :=
    (hS x j).of_le ENat.LEInfty.out
  have hc := continuousOn_levi hO hf
  have hc' : ContinuousOn (fun y' => levi (Q'.φ x ∘ (A.chart j).symm) y' w)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Q'.U x) :=
    hc.comp (f := fun y' => (y', w)) (by fun_prop) (fun y' hy' => ⟨hy', Set.mem_univ _⟩)
  have hV := hc'.isOpen_inter_preimage hO (isOpen_Iio (a := (0 : ℝ)))
  set V := ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Q'.U x) ∩
    (fun y' => levi (Q'.φ x ∘ (A.chart j).symm) y' w) ⁻¹' Set.Iio 0 with hVdef
  have hVt : V ⊆ (A.chart j).target := fun z hz => hz.1.1
  have hVi : IsOpen ((A.chart j).symm '' V) :=
    (A.chart j).symm.isOpen_image_of_subset_source hV hVt
  have hne : ((A.chart j).symm '' V).Nonempty := ⟨_, y, ⟨hy, hneg'⟩, rfl⟩
  obtain ⟨z, ⟨y', hy'V, rfl⟩, hzB⟩ := hD.inter_open_nonempty _ hVi hne
  have hW : IsOpen (V ∩ (A.chart j).symm ⁻¹' Bᶜ) := by
    have h1 := (A.chart j).isOpen_inter_preimage_symm hB.isOpen_compl
    have : V ∩ (A.chart j).symm ⁻¹' Bᶜ =
        V ∩ ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Bᶜ) := by
      ext u
      exact ⟨fun h => ⟨h.1, hVt h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
    rw [this]
    exact hV.inter h1
  have hev : (Q'.φ x ∘ (A.chart j).symm) =ᶠ[𝓝 y'] (Q.φ x ∘ (A.chart j).symm) := by
    filter_upwards [hW.mem_nhds ⟨hy'V, hzB⟩] with u hu
    have huU : (A.chart j).symm u ∈ Q.U x := hU x ▸ hu.1.1.2
    exact hE x _ huU hu.2
  have h0 := hP x j y' ⟨hy'V.1.1, (hU x ▸ hy'V.1.2 : (A.chart j).symm y' ∈ Q.U x), hzB⟩ w
  rw [← levi_congr hev w] at h0
  exact absurd h0 (not_le.mpr hy'V.2)

end GlobalTheory.CompanionTheory.AnForm
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.PshExtensionAcrossClosedDenseStatement

section

@[expose] public section

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff

theorem _root_.GlobalTheory.T.psh_extension_across_closed_dense : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (B : Set X) (Q Q' : LocPot X), IsClosed B → Dense Bᶜ → (∀ x, Q'.U x = Q.U x) → (∀ x, A.SmoothOn (Q'.U x) (Q'.φ x)) → (∀ x, ∀ y ∈ Q.U x, y ∉ B → Q'.φ x y = Q.φ x y) → IsPshOn A Bᶜ Q → IsPsh A Q' := by
  first | exact @GlobalTheory.CompanionTheory.AnForm.isPsh_of_dense_compl | exact GlobalTheory.CompanionTheory.AnForm.isPsh_of_dense_compl | (intros; apply GlobalTheory.CompanionTheory.AnForm.isPsh_of_dense_compl <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothExtensionAcrossClosedDense

section

@[expose] public section

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.SmoothGlue

theorem continuousAt_of_smoothOn {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    {N : Set X} {E : X → ℝ} (hN : IsOpen N) (hS : A.SmoothOn N E) {p : X} (hp : p ∈ N) :
    ContinuousAt E p := by
  obtain ⟨j, hj⟩ := A.cover p
  have hopen : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' N) :=
    (A.chart j).isOpen_inter_preimage_symm hN
  have hz : A.chart j p ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' N := by
    refine ⟨(A.chart j).map_source hj, ?_⟩
    simpa [Set.mem_preimage, (A.chart j).left_inv hj] using hp
  have h1 : ContinuousAt (E ∘ (A.chart j).symm) (A.chart j p) :=
    ((hS j).continuousOn).continuousAt (hopen.mem_nhds hz)
  have h2 : ContinuousAt (A.chart j) p := (A.chart j).continuousAt hj
  have h1' : ContinuousAt (E ∘ (A.chart j).symm) ((A.chart j) p) := h1
  have h3 : ContinuousAt ((E ∘ (A.chart j).symm) ∘ (A.chart j)) p :=
    ContinuousAt.comp h1' h2
  refine h3.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
  simp [Function.comp, (A.chart j).left_inv hy]

theorem eq_of_dense_compl {X : Type} [TopologicalSpace X] {B W : Set X} {f g : X → ℝ}
    (hD : Dense Bᶜ) (hW : IsOpen W) (hf : ∀ p ∈ W, ContinuousAt f p)
    (hg : ∀ p ∈ W, ContinuousAt g p) (hfg : ∀ y ∈ W, y ∉ B → f y = g y) :
    ∀ y ∈ W, f y = g y := by
  intro y hy
  by_contra hne
  have hc : ContinuousAt (fun w => f w - g w) y := (hf y hy).sub (hg y hy)
  have hev : ∀ᶠ w in 𝓝 y, f w - g w ≠ 0 := hc.eventually_ne (sub_ne_zero.mpr hne)
  obtain ⟨w, hwB, hw1, hw2⟩ := hD.inter_nhds_nonempty (hev.and (hW.mem_nhds hy))
  exact hw1 (sub_eq_zero.mpr (hfg w hw2 hwB))

theorem glue : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (B : Set X) (u : X → ℝ), IsClosed B → Dense Bᶜ → (∀ x, ∃ (N : Set X) (E : X → ℝ), IsOpen N ∧ x ∈ N ∧ A.SmoothOn N E ∧ ∀ y ∈ N, y ∉ B → E y = u y) → ∃ u' : X → ℝ, A.Smooth u' ∧ ∀ y ∉ B, u' y = u y := by
  intro e X _ A B u _ hD h
  classical
  choose N E hN hx hS hE using h
  have hagree : ∀ x y, ∀ w ∈ N x ∩ N y, E x w = E y w := by
    intro x y
    refine eq_of_dense_compl hD ((hN x).inter (hN y))
      (fun p hp => continuousAt_of_smoothOn A (hN x) (hS x) hp.1)
      (fun p hp => continuousAt_of_smoothOn A (hN y) (hS y) hp.2) ?_
    intro w hw hwB
    rw [hE x w hw.1 hwB, hE y w hw.2 hwB]
  refine ⟨fun y => if y ∈ B then E y y else u y, ?_, ?_⟩
  · have hu' : ∀ x, ∀ y ∈ N x, (if y ∈ B then E y y else u y) = E x y := by
      intro x y hy
      by_cases hB : y ∈ B
      · rw [if_pos hB]
        exact hagree y x y ⟨hx y, hy⟩
      · rw [if_neg hB]
        exact (hE x y hy hB).symm
    intro j z hz
    have hzt : z ∈ (A.chart j).target := hz.1
    set x := (A.chart j).symm z with hxdef
    have hopen : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' N x) :=
      (A.chart j).isOpen_inter_preimage_symm (hN x)
    have hzm : z ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' N x := ⟨hzt, hx x⟩
    have hc : ContDiffAt ℝ ∞ (E x ∘ (A.chart j).symm) z :=
      (hS x j).contDiffAt (hopen.mem_nhds hzm)
    refine (hc.congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [hopen.mem_nhds hzm] with w hw
    exact hu' x _ hw.2
  · intro y hy
    simp [hy]

end GlobalTheory.CompanionTheory.SmoothGlue
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothExtensionAcrossClosedDenseStatement

section

@[expose] public section

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff

theorem _root_.GlobalTheory.T.smooth_extension_across_closed_dense : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (B : Set X) (u : X → ℝ), IsClosed B → Dense Bᶜ → (∀ x, ∃ (N : Set X) (E : X → ℝ), IsOpen N ∧ x ∈ N ∧ A.SmoothOn N E ∧ ∀ y ∈ N, y ∉ B → E y = u y) → ∃ u' : X → ℝ, A.Smooth u' ∧ ∀ y ∉ B, u' y = u y := by
  first | exact @GlobalTheory.CompanionTheory.SmoothGlue.glue | exact GlobalTheory.CompanionTheory.SmoothGlue.glue | (intros; apply GlobalTheory.CompanionTheory.SmoothGlue.glue <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.FlatWeightExtends

section

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder ContDiff

namespace GlobalTheory.CompanionTheory.Ar.PB.Flat

theorem flat_weight_extends : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set X), IsPotential A L → IsSection A L s → IsSNC A L s m W → (∀ y, logNormSec L s y ≤ 0) → ∀ (th : LocPot X) (u : X → ℝ) (C₁ : ℝ), IsPotential A th → A.SmoothOn (bdry s)ᶜ u → IsPshOn A (bdry s)ᶜ (th + LocPot.ofFun u) → IsPshOn A (bdry s)ᶜ ((th + LocPot.ofFun u).rsmul (-1)) → (∀ y ∉ bdry s, |u y| ≤ C₁ * Real.log (rW L s y)) → ∃ u' : X → ℝ, A.Smooth u' ∧ (∀ y ∉ bdry s, u' y = u y) ∧ IsPsh A (th + LocPot.ofFun u') ∧ IsPsh A ((th + LocPot.ofFun u').rsmul (-1)) := by
  intro e X _ _ _ A L s nb m W hL hs hsnc hn th u C₁ hth hu hp hp' hb
  have hthm : IsPotential A (th.rsmul (-1)) := isPotentialRsmul A (-1) th hth
  have hum : A.SmoothOn (bdry s)ᶜ (fun y => -u y) := fun j => (hu j).neg
  have hpm : IsPshOn A (bdry s)ᶜ (th.rsmul (-1) + LocPot.ofFun (fun y => -u y)) := by
    intro x j y hy w
    have hf : (((th.rsmul (-1) + LocPot.ofFun (fun y => -u y)).φ x) ∘ (A.chart j).symm) =
        (((th + LocPot.ofFun u).rsmul (-1)).φ x) ∘ (A.chart j).symm := by
      funext z
      simp only [Function.comp, LocPot.rsmul]
      show -1 * th.φ x _ + -u _ = -1 * (th.φ x _ + u _)
      ring
    rw [hf]
    exact hp' x j y hy w
  obtain ⟨C5, h5⟩ := GlobalTheory.T.singular_potential_log_growth_psh e X A L s nb m W hL hs hsnc hn th u C₁ hth hu hp hb
  obtain ⟨C6, h6⟩ := GlobalTheory.T.singular_potential_log_growth_psh e X A L s nb m W hL hs hsnc hn (th.rsmul (-1)) (fun y => -u y) C₁ hthm hum hpm
    (fun y hy => by simpa using hb y hy)
  have hM : ∀ y ∉ bdry s, |u y| ≤ max C5 C6 := by
    intro y hy
    have a := (h5.2.2.2 y hy).2
    have b := (h6.2.2.2 y hy).2
    rw [abs_le]
    constructor
    · have := le_max_right C5 C6; linarith
    · exact a.trans (le_max_left _ _)
  obtain ⟨hcl, hde⟩ := GlobalTheory.T.section_boundary_closed_and_codense e X A L s nb m W hs hsnc
  obtain ⟨u', hu', heq⟩ := GlobalTheory.T.smooth_extension_across_closed_dense e X A (bdry s) u hcl hde
    (GlobalTheory.T.bounded_psh_correction_locally_smooth e X A L s nb m W hs hsnc th u _ hth hu hp hp' hM)
  have hsm : ∀ x, A.SmoothOn ((th + LocPot.ofFun u').U x) ((th + LocPot.ofFun u').φ x) := by
    intro x j
    have h1 : ContDiffOn ℝ ∞ (th.φ x ∘ (A.chart j).symm)
        ((A.chart j).target ∩ (A.chart j).symm ⁻¹' ((th + LocPot.ofFun u').U x)) :=
      (hth.1 x j).mono fun y hy => ⟨hy.1, hy.2.1⟩
    have h2 : ContDiffOn ℝ ∞ (u' ∘ (A.chart j).symm)
        ((A.chart j).target ∩ (A.chart j).symm ⁻¹' ((th + LocPot.ofFun u').U x)) :=
      (hu' j).mono fun y hy => ⟨hy.1, trivial⟩
    exact h1.add h2
  refine ⟨u', hu', heq, ?_, ?_⟩
  · refine GlobalTheory.T.psh_extension_across_closed_dense e X A (bdry s) (th + LocPot.ofFun u) (th + LocPot.ofFun u') hcl hde
      (fun _ => rfl) hsm ?_ hp
    intro x y _ hy
    show th.φ x y + u' y = th.φ x y + u y
    rw [heq y hy]
  · refine GlobalTheory.T.psh_extension_across_closed_dense e X A (bdry s) ((th + LocPot.ofFun u).rsmul (-1))
      ((th + LocPot.ofFun u').rsmul (-1)) hcl hde (fun _ => rfl) ?_ ?_ hp'
    · intro x j
      have := (hsm x j).const_smul (-1 : ℝ)
      refine this.congr fun y _ => ?_
      simp [LocPot.rsmul]
    · intro x y _ hy
      show -1 * (th.φ x y + u' y) = -1 * (th.φ x y + u y)
      rw [heq y hy]

end GlobalTheory.CompanionTheory.Ar.PB.Flat
end
end
