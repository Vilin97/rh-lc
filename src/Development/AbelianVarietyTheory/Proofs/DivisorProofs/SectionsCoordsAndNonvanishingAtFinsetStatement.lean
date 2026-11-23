module

public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FamilyLeCoords
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionsApproxFirstJetsPositiveStatement
public import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.FDeriv.Mul
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FlatCalcA
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientJetsFderivDetNeZero

section

@[expose] public section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
namespace GlobalTheory

theorem quot_jets_det_ne_zero : ∀ n : ℕ, ∃ ε : ℝ, 0 < ε ∧ ∀ (p : V n) (w0 : V n → ℂ) (w : Fin n → V n → ℂ), DifferentiableAt ℂ w0 p → (∀ j, DifferentiableAt ℂ (w j) p) → ‖w0 p - 1‖ ≤ ε → ‖fderiv ℂ (fun v => w0 v - 1) p‖ ≤ ε → (∀ j, ‖w j p‖ ≤ ε) → (∀ j, ‖fderiv ℂ (fun v : V n => w j v - (v j - p j)) p‖ ≤ ε) → w0 p ≠ 0 ∧ (fderiv ℂ (fun v : V n => (WithLp.toLp 2 (fun j => w j v / w0 v) : V n)) p).det ≠ 0 := by
  intro n
  refine ⟨1 / (4 * ((n : ℝ) + 1)), by positivity, ?_⟩
  intro p w0 w hw0 hw h0 hL0 hwp hLj
  set ε : ℝ := 1 / (4 * ((n : ℝ) + 1)) with hε
  have hεpos : 0 < ε := by positivity
  have hε4 : ε ≤ 1 / 4 := by
    rw [hε]; apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    have : (0:ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  set a := w0 p with ha_def
  have ha_norm : 3 / 4 ≤ ‖a‖ := by
    have h1 : ‖(1:ℂ)‖ ≤ ‖a‖ + ‖a - 1‖ := by
      have := norm_sub_le a (a - 1)
      simpa using this
    simp at h1
    linarith
  have ha : a ≠ 0 := by
    intro h; rw [h] at ha_norm; simp at ha_norm; linarith
  refine ⟨ha, ?_⟩
  set L0 := fderiv ℂ w0 p with hL0_def
  have hL0' : ‖L0‖ ≤ ε := by
    have := hL0; rwa [fderiv_sub_const] at this
  have hproj : ∀ j : Fin n, HasFDerivAt (fun v : V n => v j - p j) (EuclideanSpace.proj (𝕜 := ℂ) j) p := by
    intro j
    have := (EuclideanSpace.proj (𝕜 := ℂ) (ι := Fin n) j).hasFDerivAt (x := p)
    exact this.sub_const (p j)
  have hLj' : ∀ j : Fin n, ∀ ξ : V n, ‖fderiv ℂ (w j) p ξ - ξ j‖ ≤ ε * ‖ξ‖ := by
    intro j ξ
    have hd : fderiv ℂ (fun v : V n => w j v - (v j - p j)) p
        = fderiv ℂ (w j) p - EuclideanSpace.proj (𝕜 := ℂ) j :=
      ((hw j).hasFDerivAt.sub (hproj j)).fderiv
    have := (fderiv ℂ (fun v : V n => w j v - (v j - p j)) p).le_opNorm ξ
    rw [hd] at this
    have h2 := hLj j
    rw [hd] at h2
    calc ‖fderiv ℂ (w j) p ξ - ξ j‖ = ‖(fderiv ℂ (w j) p - EuclideanSpace.proj (𝕜 := ℂ) j) ξ‖ := by simp
      _ ≤ _ := this
      _ ≤ ε * ‖ξ‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
  set F : V n → V n := fun v => (WithLp.toLp 2 (fun j => w j v / w0 v) : V n) with hF
  have hq : ∀ j : Fin n, HasFDerivAt (fun v => w j v / w0 v)
      (w j p • ((-(a ^ 2)⁻¹) • L0) + a⁻¹ • fderiv ℂ (w j) p) p := by
    intro j
    have hinv : HasFDerivAt (fun v => (w0 v)⁻¹) ((-(a ^ 2)⁻¹) • L0) p :=
      (hasDerivAt_inv ha).comp_hasFDerivAt p hw0.hasFDerivAt
    have := HasFDerivAt.mul (hw j).hasFDerivAt hinv
    have e : (fun v => w j v / w0 v) = (w j * fun v => (w0 v)⁻¹) := by
      funext v; simp [div_eq_mul_inv]
    rw [e]; exact this
  have hFd : DifferentiableAt ℂ F p := by
    rw [differentiableAt_piLp]
    intro j
    simpa [hF] using (hq j).differentiableAt
  set D := fderiv ℂ F p with hD
  have hDj : ∀ j : Fin n, ∀ ξ : V n, (D ξ) j = w j p * ((-(a ^ 2)⁻¹) * L0 ξ) + a⁻¹ * fderiv ℂ (w j) p ξ := by
    intro j ξ
    have h1 : HasFDerivAt (fun v => EuclideanSpace.proj (𝕜 := ℂ) j (F v)) ((EuclideanSpace.proj (𝕜 := ℂ) j).comp D) p :=
      (EuclideanSpace.proj (𝕜 := ℂ) (ι := Fin n) j).hasFDerivAt.comp p hFd.hasFDerivAt
    have h2 : (fun v => EuclideanSpace.proj (𝕜 := ℂ) j (F v)) = fun v => w j v / w0 v := by
      funext v; simp [hF]
    rw [h2] at h1
    have := congrArg (fun T : V n →L[ℂ] ℂ => T ξ) (h1.unique (hq j))
    simpa using this
  have hinj : ∀ ξ : V n, D ξ = 0 → ξ = 0 := by
    intro ξ hξ
    have hcoord : ∀ j : Fin n, ‖ξ j‖ ≤ 2 * ε * ‖ξ‖ := by
      intro j
      have e := hDj j ξ
      rw [hξ] at e
      simp only [PiLp.zero_apply] at e
      have e2 : a * fderiv ℂ (w j) p ξ = w j p * L0 ξ := by
        have : a ^ 2 * (w j p * ((-(a ^ 2)⁻¹) * L0 ξ) + a⁻¹ * fderiv ℂ (w j) p ξ) = 0 := by
          rw [← e]; ring
        field_simp at this
        linear_combination this
      have hL0ξ : ‖L0 ξ‖ ≤ ε * ‖ξ‖ := (L0.le_opNorm ξ).trans (mul_le_mul_of_nonneg_right hL0' (norm_nonneg _))
      have e3 : ‖a‖ * ‖fderiv ℂ (w j) p ξ‖ ≤ ε * (ε * ‖ξ‖) := by
        rw [← norm_mul, e2, norm_mul]
        exact mul_le_mul (hwp j) hL0ξ (norm_nonneg _) hεpos.le
      have e4 : ‖fderiv ℂ (w j) p ξ‖ ≤ ε * ‖ξ‖ := by
        by_contra hc
        push_neg at hc
        have : (3/4) * (ε * ‖ξ‖) < ‖a‖ * ‖fderiv ℂ (w j) p ξ‖ := by
          calc (3/4) * (ε * ‖ξ‖) ≤ ‖a‖ * (ε * ‖ξ‖) := mul_le_mul_of_nonneg_right ha_norm (by positivity)
            _ < ‖a‖ * ‖fderiv ℂ (w j) p ξ‖ := mul_lt_mul_of_pos_left hc (by linarith)
        have : ε * (ε * ‖ξ‖) ≤ (3/4) * (ε * ‖ξ‖) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        linarith
      have e5 := hLj' j ξ
      have : ‖ξ j‖ ≤ ‖fderiv ℂ (w j) p ξ‖ + ‖fderiv ℂ (w j) p ξ - ξ j‖ := by
        have := norm_sub_le (fderiv ℂ (w j) p ξ) (fderiv ℂ (w j) p ξ - ξ j)
        simpa using this
      linarith
    have hsq : ‖ξ‖ ^ 2 ≤ (n : ℝ) * (2 * ε * ‖ξ‖) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      calc ∑ i, ‖ξ.ofLp i‖ ^ 2 ≤ ∑ _i : Fin n, (2 * ε * ‖ξ‖) ^ 2 := by
            apply Finset.sum_le_sum
            intro i _
            exact pow_le_pow_left₀ (norm_nonneg _) (hcoord i) 2
        _ = (n : ℝ) * (2 * ε * ‖ξ‖) ^ 2 := by simp
    have hc : (n : ℝ) * (2 * ε) ^ 2 ≤ 1 / 4 := by
      rw [hε]
      have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
      rw [show (2 * (1 / (4 * ((n:ℝ) + 1)))) ^ 2 = 1 / (4 * ((n:ℝ)+1)^2) by field_simp; ring]
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have : ‖ξ‖ ^ 2 ≤ (1/4) * ‖ξ‖ ^ 2 := by
      calc ‖ξ‖ ^ 2 ≤ (n : ℝ) * (2 * ε * ‖ξ‖) ^ 2 := hsq
        _ = ((n : ℝ) * (2 * ε) ^ 2) * ‖ξ‖ ^ 2 := by ring
        _ ≤ (1/4) * ‖ξ‖ ^ 2 := mul_le_mul_of_nonneg_right hc (by positivity)
    have : ‖ξ‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖ξ‖]
    simpa using this
  intro hdet
  have h := (LinearMap.det_eq_zero_iff_ker_ne_bot (f := (D : V n →ₗ[ℂ] V n))).1 hdet
  apply h
  rw [LinearMap.ker_eq_bot']
  intro m hm
  exact hinj m hm

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientJetsFderivDetNeZeroStatement

section

@[expose] public section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.quotient_jets_fderiv_det_ne_zero : ∀ n : ℕ, ∃ ε : ℝ, 0 < ε ∧ ∀ (p : V n) (w0 : V n → ℂ) (w : Fin n → V n → ℂ), DifferentiableAt ℂ w0 p → (∀ j, DifferentiableAt ℂ (w j) p) → ‖w0 p - 1‖ ≤ ε → ‖fderiv ℂ (fun v => w0 v - 1) p‖ ≤ ε → (∀ j, ‖w j p‖ ≤ ε) → (∀ j, ‖fderiv ℂ (fun v : V n => w j v - (v j - p j)) p‖ ≤ ε) → w0 p ≠ 0 ∧ (fderiv ℂ (fun v : V n => (WithLp.toLp 2 (fun j => w j v / w0 v) : V n)) p).det ≠ 0 := by
  first | exact @GlobalTheory.quot_jets_det_ne_zero | exact GlobalTheory.quot_jets_det_ne_zero | (intros; apply GlobalTheory.quot_jets_det_ne_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsCoordsAndNonvanishingAtFinset

section

@[expose] public section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

theorem sections_coords_and_nonvanishing_at_finset : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (H : La), (∀ i y, y ∈ (A.chart i).source → ∀ ξ : Fin n → ℂ, ξ ≠ 0 → 0 < A.leviAt i (A.ph H i) y ξ) → ∀ (T : Finset Y) (G : La), ∃ k0 : ℕ, ∀ k ≥ k0, ∃ (t0 : ι → Y → ℂ) (t : Fin n → ι → Y → ℂ) (a : ι → Y → ℂ), A.IsSec (A.kap + k • H) t0 ∧ (∀ j, A.IsSec (A.kap + k • H) (t j)) ∧ A.IsSec (A.kap + (G + k • H)) a ∧ ∀ P ∈ T, t0 (A.pick P) P ≠ 0 ∧ A.IsCoordAt t0 t P ∧ a (A.pick P) P ≠ 0 := by
  intro n Y _ _ _ _ _ _ ι La _ A H hH T G
  obtain ⟨q, hq, hk9⟩ := GlobalTheory.T.exists_sections_approx_firstJets_positive n Y ι La A H hH T
  obtain ⟨ε, hε, hk10⟩ := GlobalTheory.T.quotient_jets_fderiv_det_ne_zero n
  obtain ⟨k0, hk0⟩ := hk9 0 (fun _ _ => 1) (fun _ => differentiable_const _) ε hε
  have hpj : ∀ j : Fin n, ∀ P : Y,
      Differentiable ℂ (fun v : V n => v j - (A.chart (A.pick P) P) j) := fun j P =>
    ((EuclideanSpace.proj (𝕜 := ℂ) j).differentiable).sub_const _
  choose kj hkj using fun j : Fin n =>
    hk9 0 (fun P v => v j - (A.chart (A.pick P) P) j) (hpj j) ε hε
  obtain ⟨ka, hka⟩ := hk9 G (fun _ _ => 1) (fun _ => differentiable_const _) (1/2) (by norm_num)
  refine ⟨max k0 (max ka (Finset.univ.sup kj)), fun k hk => ?_⟩
  have hk0' : k ≥ k0 := le_trans (le_max_left _ _) hk
  have hka' : k ≥ ka := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
  have hkj' : ∀ j, k ≥ kj j := fun j =>
    le_trans (le_trans (Finset.le_sup (f := kj) (Finset.mem_univ j))
      (le_trans (le_max_right _ _) (le_max_right _ _))) hk
  obtain ⟨F0, hF0s, hF0⟩ := hk0 k hk0'
  choose Fj hFjs hFj using fun j => hkj j k (hkj' j)
  obtain ⟨Fa, hFas, hFa⟩ := hka k hka'
  rw [zero_add] at hF0s hFjs
  refine ⟨F0, Fj, Fa, hF0s, hFjs, hFas, fun P hP => ?_⟩
  set i := A.pick P with hi
  set p := A.chart i P with hp
  have hPs : P ∈ (A.chart i).source := A.mem_pick P
  have hpt : p ∈ (A.chart i).target := (A.chart i).map_source hPs
  have hsymm : (A.chart i).symm p = P := (A.chart i).left_inv hPs
  have hdiffF : ∀ F : ι → Y → ℂ, ∀ la, A.IsSec la F →
      DifferentiableAt ℂ (fun v => F i ((A.chart i).symm v)) p := by
    intro F la hF
    have h1 := hF.1 i
    have h2 : (A.chart i).target ∩ (A.chart i).symm ⁻¹' Set.univ = (A.chart i).target := by simp
    rw [h2] at h1
    exact h1.differentiableAt ((A.chart i).open_target.mem_nhds hpt)
  have hE : DifferentiableAt ℂ (fun v => Complex.exp (-((k : ℂ) * q P v))) p :=
    ((((hq P hP) p).const_mul (k : ℂ)).neg).cexp
  set w0 : V n → ℂ := fun v => F0 i ((A.chart i).symm v) * Complex.exp (-((k : ℂ) * q P v)) with hw0
  set w : Fin n → V n → ℂ := fun j v => Fj j i ((A.chart i).symm v) * Complex.exp (-((k : ℂ) * q P v)) with hw
  have hd0 : DifferentiableAt ℂ w0 p := (hdiffF F0 _ hF0s).mul hE
  have hdj : ∀ j, DifferentiableAt ℂ (w j) p := fun j => (hdiffF (Fj j) _ (hFjs j)).mul hE
  obtain ⟨h0a, h0b⟩ := hF0 P hP
  have e1 : ‖w0 p - 1‖ ≤ ε := by
    simp only [hw0, hsymm]; exact h0a
  have e2 : ‖fderiv ℂ (fun v => w0 v - 1) p‖ ≤ ε := h0b
  have e3 : ∀ j, ‖w j p‖ ≤ ε := by
    intro j
    have := (hFj j P hP).1
    simp only [sub_self, sub_zero] at this
    simp only [hw, hsymm]; exact this
  have e4 : ∀ j, ‖fderiv ℂ (fun v : V n => w j v - (v j - p j)) p‖ ≤ ε := fun j => (hFj j P hP).2
  obtain ⟨hne, hdet⟩ := hk10 p w0 w hd0 hdj e1 e2 e3 e4
  refine ⟨?_, ?_, ?_⟩
  · intro h0
    apply hne
    simp only [hw0, hsymm, h0, zero_mul]
  · unfold WeightedAtlas.IsCoordAt
    have hfun : A.zLoc F0 Fj i = fun v : V n => (WithLp.toLp 2 (fun j => w j v / w0 v) : V n) := by
      funext v
      simp only [WeightedAtlas.zLoc, hw, hw0]
      congr 1
      funext j
      rw [mul_div_mul_right _ _ (Complex.exp_ne_zero _)]
    rw [← hi, ← hp, hfun]
    exact hdet
  · intro h0
    have := (hFa P hP).1
    rw [h0, zero_mul, zero_sub, norm_neg, norm_one] at this
    norm_num at this

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsCoordsAndNonvanishingAtFinsetStatement

section

@[expose] public section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.exists_sections_coords_nonvanishing_at_finset : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (H : La), (∀ i y, y ∈ (A.chart i).source → ∀ ξ : Fin n → ℂ, ξ ≠ 0 → 0 < A.leviAt i (A.ph H i) y ξ) → ∀ (T : Finset Y) (G : La), ∃ k0 : ℕ, ∀ k ≥ k0, ∃ (t0 : ι → Y → ℂ) (t : Fin n → ι → Y → ℂ) (a : ι → Y → ℂ), A.IsSec (A.kap + k • H) t0 ∧ (∀ j, A.IsSec (A.kap + k • H) (t j)) ∧ A.IsSec (A.kap + (G + k • H)) a ∧ ∀ P ∈ T, t0 (A.pick P) P ≠ 0 ∧ A.IsCoordAt t0 t P ∧ a (A.pick P) P ≠ 0 := by
  first | exact @GlobalTheory.sections_coords_and_nonvanishing_at_finset | exact GlobalTheory.sections_coords_and_nonvanishing_at_finset | (intros; apply GlobalTheory.sections_coords_and_nonvanishing_at_finset <;> assumption)
end
end
