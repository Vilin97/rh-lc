module

public import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.ChartSymmEventuallyEq
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.TsupportDbSubset
public import ReciprocityTheory.L2DbarEstimates.HormanderEstimate.Closed
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Tactic.TypeStar
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import ReciprocityTheory.L2DbarEstimates.MinimalSolutions.MinimalSolutionStatement
public import ReciprocityTheory.L2DbarEstimates.NormFibrations.Hormander
public import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.MeasurableEmbeddingRotAbout
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FlatCalcA

-- Source module: ReciprocityTheory.L2DbarEstimates.LeviForms.FixedA

section

@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology Set
open scoped ENNReal ContDiff

noncomputable section

theorem fx_wint_eq_withDensity {M : Type*} [MeasurableSpace M] (n : ℕ) (z : M → V n)
    (ps : M → ℝ) (hps : Measurable ps) (F : M → ℂ) :
    wint n z F ps = ∫⁻ x, ‖F x‖ₑ ^ 2 ∂(vol n z).withDensity
      (fun x => ENNReal.ofReal (Real.exp (-ps x))) := by
  unfold wint
  have hmeas : Measurable (fun x => ENNReal.ofReal (Real.exp (-ps x))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hps.neg)
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _ hmeas
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine lintegral_congr fun x => ?_
  simp only [Pi.mul_apply, Function.comp]
  rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_mul (Real.exp_pos _).le, mul_comm]

theorem fx_lintegral_enorm_sq_eq {α : Type*} [MeasurableSpace α] (μ : Measure α) (F : α → ℂ) :
    ∫⁻ x, ‖F x‖ₑ ^ 2 ∂μ = eLpNorm' F 2 μ ^ (2 : ℝ) := by
  rw [MeasureTheory.eLpNorm'_eq_lintegral_eNorm, ← ENNReal.rpow_mul]
  norm_num

end

end ReciprocityTheory.L2DbarEstimates.I
end
end

-- Source module: ReciprocityTheory.L2DbarEstimates.LeviForms.FixedC

section

@[expose] public section

universe u

namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology Set
open scoped ENNReal ContDiff

noncomputable section

theorem fx_lp_norm_sq_eq {α : Type*} [MeasurableSpace α] (μ : Measure α) (v : Lp ℂ 2 μ)
    (G : α → ℂ) (h : (v : α → ℂ) =ᵐ[μ] G) :
    eLpNorm G 2 μ ^ (2 : ℝ) = ENNReal.ofReal (‖v‖ ^ 2) := by
  rw [eLpNorm_congr_ae h.symm, Lp.norm_def, ENNReal.ofReal_pow ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top v), ENNReal.rpow_two]

end

end ReciprocityTheory.L2DbarEstimates.I
end
end

-- Source module: ReciprocityTheory.L2DbarEstimates.MinimalSolutions.CvxOfConvex

section

@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates

open Filter Topology

theorem cvx (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :
    CVXStatement H := by
  unfold CVXStatement
  intro K hanti hne hcl hmid hb
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hb
  have hbdd : ∀ n, BddBelow ((fun w : H => ‖w‖) '' K n) :=
    fun n => ⟨0, by rintro _ ⟨w, _, rfl⟩; exact norm_nonneg w⟩
  have hSne : ∀ n, ((fun w : H => ‖w‖) '' K n).Nonempty := fun n => (hne n).image _
  obtain ⟨d, hd⟩ : ∃ d : ℕ → ℝ, d = fun n => sInf ((fun w : H => ‖w‖) '' K n) := ⟨_, rfl⟩
  have hdle : ∀ n, ∀ w ∈ K n, d n ≤ ‖w‖ := by
    intro n w hw; rw [hd]; exact csInf_le (hbdd n) ⟨w, hw, rfl⟩
  have hd0 : ∀ n, 0 ≤ d n := by
    intro n; rw [hd]
    exact le_csInf (hSne n) (by rintro _ ⟨w, _, rfl⟩; exact norm_nonneg w)
  have hdmono : Monotone d := by
    intro n m hnm; rw [hd]
    exact csInf_le_csInf (hbdd n) (hSne m) (Set.image_mono (hanti hnm))
  have hdR : ∀ n, d n ≤ R := by
    intro n
    obtain ⟨w, hw⟩ := hne n
    exact (hdle n w hw).trans (hR w (hanti (Nat.zero_le n) hw))
  have happrox : ∀ n, ∃ w ∈ K n, ‖w‖ < d n + 1 / ((n : ℝ) + 1) := by
    intro n
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hlt : sInf ((fun w : H => ‖w‖) '' K n) < d n + 1 / ((n : ℝ) + 1) := by
      rw [hd]; exact lt_add_of_pos_right _ hpos
    obtain ⟨_, ⟨w, hw, rfl⟩, hw2⟩ := exists_lt_of_csInf_lt (hSne n) hlt
    exact ⟨w, hw, hw2⟩
  choose x hxK hxn using happrox
  have hbddA : BddAbove (Set.range d) := ⟨R, by rintro _ ⟨n, rfl⟩; exact hdR n⟩
  obtain ⟨L, hL⟩ : ∃ L, L = ⨆ n, d n := ⟨_, rfl⟩
  have hdL : ∀ n, d n ≤ L := fun n => by rw [hL]; exact le_ciSup hbddA n
  have hL0 : 0 ≤ L := (hd0 0).trans (hdL 0)
  have hkey : ∀ n m, n ≤ m → ‖x m - x n‖ ^ 2 ≤ 2 * ‖x m‖ ^ 2 + 2 * ‖x n‖ ^ 2 - 4 * d n ^ 2 := by
    intro n m hnm
    have hmK : x m ∈ K n := hanti hnm (hxK m)
    have h1 := hdle n _ (hmid n (x m) hmK (x n) (hxK n))
    have h2 : ‖x m + x n‖ = 2 * ‖(2 : ℂ)⁻¹ • (x m + x n)‖ := by
      first
        | (rw [norm_smul, norm_inv, Complex.norm_two]; ring)
        | (rw [norm_smul]; norm_num)
        | (simp [norm_smul]; ring)
    have h3 : 4 * d n ^ 2 ≤ ‖x m + x n‖ ^ 2 := by
      rw [h2]; nlinarith [h1, hd0 n]
    have hpar := parallelogram_law_with_norm ℂ (x m) (x n)
    nlinarith [hpar, h3]
  have hcauchy : CauchySeq x := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨η, hηdef⟩ : ∃ η, η = min 1 (ε ^ 2 / (16 * (L + 1))) := ⟨_, rfl⟩
    have hη0 : 0 < η := by rw [hηdef]; exact lt_min one_pos (by positivity)
    have hη1 : η ≤ 1 := by rw [hηdef]; exact min_le_left _ _
    have hηε : η ≤ ε ^ 2 / (16 * (L + 1)) := by rw [hηdef]; exact min_le_right _ _
    obtain ⟨N₁, hN₁⟩ := exists_lt_of_lt_ciSup (f := d) (by rw [← hL]; linarith : L - η < ⨆ n, d n)
    obtain ⟨N₂, hN₂⟩ := exists_nat_one_div_lt hη0
    refine ⟨max N₁ N₂, fun m hm => ?_⟩
    have hdN : L - η < d (max N₁ N₂) := hN₁.trans_le (hdmono (le_max_left _ _))
    have heN : 1 / (((max N₁ N₂ : ℕ) : ℝ) + 1) < η := by
      refine lt_of_le_of_lt (one_div_le_one_div_of_le (by positivity) ?_) hN₂
      have : (N₂ : ℝ) ≤ ((max N₁ N₂ : ℕ) : ℝ) := by exact_mod_cast le_max_right N₁ N₂
      linarith
    have hem : 1 / ((m : ℝ) + 1) < η := by
      refine lt_of_le_of_lt (one_div_le_one_div_of_le (by positivity) ?_) hN₂
      have : (N₂ : ℝ) ≤ (m : ℝ) := by exact_mod_cast (le_max_right N₁ N₂).trans hm
      linarith
    have hk := hkey (max N₁ N₂) m hm
    have hxm := hxn m
    have hxN := hxn (max N₁ N₂)
    have hdm := hdL m
    have hdNL := hdL (max N₁ N₂)
    have hd0N := hd0 (max N₁ N₂)
    have a1 : ‖x m‖ < L + η := by linarith
    have a2 : ‖x (max N₁ N₂)‖ < d (max N₁ N₂) + η := by linarith
    have b1 : ‖x m‖ ^ 2 ≤ (L + η) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) a1.le 2
    have b2 : ‖x (max N₁ N₂)‖ ^ 2 ≤ (d (max N₁ N₂) + η) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) a2.le 2
    have c0 : 0 ≤ (d (max N₁ N₂) - L + η) * (d (max N₁ N₂) + L) :=
      mul_nonneg (by linarith) (by linarith)
    have c1 : d (max N₁ N₂) * η ≤ L * η := mul_le_mul_of_nonneg_right hdNL hη0.le
    have c2 : η * η ≤ η * 1 := mul_le_mul_of_nonneg_left hη1 hη0.le
    have c3 : 0 ≤ L * η := mul_nonneg hL0 hη0.le
    have b3 : L ^ 2 - 2 * L * η ≤ d (max N₁ N₂) ^ 2 := by nlinarith
    have b4 : η * (16 * (L + 1)) ≤ ε ^ 2 := (le_div_iff₀ (by positivity)).1 hηε
    have hsq : ‖x m - x (max N₁ N₂)‖ ^ 2 < ε ^ 2 := by nlinarith
    rw [dist_eq_norm]
    nlinarith [norm_nonneg (x m - x (max N₁ N₂))]
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨y, fun n => ?_⟩
  apply (hcl n).mem_of_tendsto hy
  filter_upwards [Filter.eventually_ge_atTop n] with m hm
  exact hanti hm (hxK m)

end ReciprocityTheory.L2DbarEstimates
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoloLimitIncreasingWeights

section

@[expose] public section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

noncomputable section

theorem holo_limit_increasing_weights : ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M], ∀ (X : EtaleStein n M) (F0 : M → ℂ) (om : M → ℝ) (c : ℝ) (p : ℕ → M → ℝ) (q : M → ℝ) (F : ℕ → M → ℂ) (B : ℝ≥0∞), Continuous F0 → Continuous om → 0 < c → (∀ x, c ≤ om x ∧ om x ≤ 1) → (∀ k, SmoothR n X.z (p k)) → (∀ x, Antitone (fun k => p k x)) → (∀ x, Tendsto (fun k => p k x) atTop (𝓝 (q x))) → (∀ k, Holo n X.z (F k)) → B < ⊤ → (∀ k, ∫⁻ x, ENNReal.ofReal (‖F0 x - F k x‖ ^ 2 * (om x * Real.exp (-p k x))) ∂vol n X.z ≤ B) → ∃ G : M → ℂ, Holo n X.z G ∧ ∫⁻ x, ENNReal.ofReal (‖F0 x - G x‖ ^ 2 * (om x * Real.exp (-q x))) ∂vol n X.z ≤ B := by
  intro n M _ _ _ _ _ X F0 om c p q Fk B hF0 hom hc hombd hp hpanti hpq hF hBtop hB
  have hz := X.isLocalHomeomorph
  have hpc : ∀ k, Continuous (p k) := fun k => by
    have := Complex.continuous_re.comp (Smooth.continuous n X.z hz _ (hp k))
    exact this.congr fun x => by simp
  have hcont : ∀ G : M → ℂ, Holo n X.z G → Continuous G := fun G hG =>
    Smooth.continuous n X.z hz _ (Holo.smooth n X.z _ hG)
  have hC : ReciprocityTheory.L2DbarEstimates.I.HoloClosedNeed n M :=
    ReciprocityTheory.L2DbarEstimates.F.holoClosedNeed n M (regMAll n M)
  have hE : ReciprocityTheory.L2DbarEstimates.I.EvalNeed n M := ReciprocityTheory.L2DbarEstimates.F.evalNeed n M C.mv
  set Iw : ℕ → (M → ℂ) → ℝ≥0∞ := fun k G =>
    ∫⁻ x, ENNReal.ofReal (‖F0 x - G x‖ ^ 2 * (om x * Real.exp (-p k x))) ∂vol n X.z with hIw
  set μ : Measure M := (vol n X.z).withDensity (fun x => ENNReal.ofReal (Real.exp (-p 0 x)))
    with hμ
  have hkey : ∀ f : M → ℂ, AEStronglyMeasurable f μ →
      wint n X.z f (p 0) = eLpNorm f 2 μ ^ (2 : ℝ) := fun f hf => by
    rw [ReciprocityTheory.L2DbarEstimates.I.fx_wint_eq_withDensity n X.z (p 0) (hpc 0).measurable f,
      ReciprocityTheory.L2DbarEstimates.I.fx_lintegral_enorm_sq_eq,
      eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num) hf]
    norm_num [hμ]
  have hN : ∀ (v : Lp ℂ 2 μ) (G : M → ℂ), (v : M → ℂ) =ᵐ[μ] G →
      wint n X.z G (p 0) = ENNReal.ofReal (‖v‖ ^ 2) := fun v G h => by
    rw [hkey G ((Lp.stronglyMeasurable v).aestronglyMeasurable.congr h),
      ReciprocityTheory.L2DbarEstimates.I.fx_lp_norm_sq_eq μ v G h]

  have hmono : ∀ G k k', k ≤ k' → Iw k G ≤ Iw k' G := fun G k k' h => by
    refine lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_
    have h1 : Real.exp (-p k x) ≤ Real.exp (-p k' x) :=
      Real.exp_le_exp.mpr (neg_le_neg (hpanti x h))
    have h0 : 0 ≤ om x := hc.le.trans (hombd x).1
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 h0) (by positivity)

  have hmeas : ∀ G : M → ℂ, Continuous G → ∀ (w : M → ℝ), Continuous w →
      Measurable fun x => ENNReal.ofReal (‖F0 x - G x‖ ^ 2 * (om x * Real.exp (-w x))) :=
    fun G hG w hw => (ENNReal.continuous_ofReal.comp (((hF0.sub hG).norm.pow 2).mul
      (hom.mul (Real.continuous_exp.comp hw.neg)))).measurable

  have hbd : ∀ G : M → ℂ, Continuous G → wint n X.z (fun x => G x - Fk 0 x) (p 0) ≤
      ENNReal.ofReal (2 / c) * (Iw 0 G + Iw 0 (Fk 0)) := fun G hG => by
    rw [hIw, ← lintegral_add_left (hmeas G hG _ (hpc 0)),
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun x => ?_
    have ha : 0 ≤ ‖F0 x - G x‖ ^ 2 * (om x * Real.exp (-p 0 x)) := by
      have := hc.le.trans (hombd x).1; positivity
    have hb : 0 ≤ ‖F0 x - Fk 0 x‖ ^ 2 * (om x * Real.exp (-p 0 x)) := by
      have := hc.le.trans (hombd x).1; positivity
    rw [← ENNReal.ofReal_add ha hb, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    set s := ‖F0 x - G x‖
    set t := ‖F0 x - Fk 0 x‖
    set e := Real.exp (-p 0 x)
    have he : 0 < e := Real.exp_pos _
    have hu : ‖G x - Fk 0 x‖ ≤ s + t := by
      calc ‖G x - Fk 0 x‖ = ‖(F0 x - Fk 0 x) - (F0 x - G x)‖ := by congr 1; ring
        _ ≤ t + s := norm_sub_le _ _
        _ = s + t := add_comm _ _
    have hu2 : ‖G x - Fk 0 x‖ ^ 2 ≤ 2 * (s ^ 2 + t ^ 2) := by
      have h0 := norm_nonneg (G x - Fk 0 x)
      nlinarith [sq_nonneg (s - t), norm_nonneg (F0 x - G x), norm_nonneg (F0 x - Fk 0 x)]
    have hoc : 1 ≤ om x / c := (one_le_div hc).mpr (hombd x).1
    have hst : 0 ≤ s ^ 2 + t ^ 2 := by positivity
    calc ‖G x - Fk 0 x‖ ^ 2 * e ≤ 2 * (s ^ 2 + t ^ 2) * e := by gcongr
      _ ≤ 2 * (s ^ 2 + t ^ 2) * e * (om x / c) := le_mul_of_one_le_right (by positivity) hoc
      _ = 2 / c * (s ^ 2 * (om x * e) + t ^ 2 * (om x * e)) := by field_simp

  have hIfin : ∀ k, Iw 0 (Fk k) ≤ B := fun k => (hmono (Fk k) 0 k (Nat.zero_le k)).trans (hB k)
  have hfin : ENNReal.ofReal (2 / c) * (B + B) < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.mpr ⟨hBtop, hBtop⟩)
  have hbdB : ∀ G : M → ℂ, Continuous G → Iw 0 G ≤ B →
      wint n X.z (fun x => G x - Fk 0 x) (p 0) ≤ ENNReal.ofReal (2 / c) * (B + B) :=
    fun G hG h => (hbd G hG).trans (by gcongr; exact hIfin 0)

  have hEv : ∀ x, ∃ C : ℝ, 0 ≤ C ∧ ∀ (G₁ G₂ : M → ℂ), Holo n X.z G₁ → Holo n X.z G₂ →
      ∀ w : Lp ℂ 2 μ, (w : M → ℂ) =ᵐ[μ] (fun x => G₁ x - G₂ x) → ‖G₁ x - G₂ x‖ ≤ C * ‖w‖ := by
    intro x
    obtain ⟨C, hC⟩ := hE X (p 0) x (hp 0)
    refine ⟨Real.sqrt (max C 0), Real.sqrt_nonneg _, fun G₁ G₂ h₁ h₂ w hw => ?_⟩
    have h := hC _ (Holo.sub n X.z _ _ h₁ h₂)
    rw [hN w _ hw] at h
    have h' : ENNReal.ofReal (‖G₁ x - G₂ x‖ ^ 2) ≤ ENNReal.ofReal (max C 0 * ‖w‖ ^ 2) := by
      rw [ENNReal.ofReal_mul (le_max_right _ _)]
      exact h.trans (by gcongr; exact le_max_left _ _)
    rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h'
    rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero, mul_pow,
      Real.sq_sqrt (le_max_right _ _)]
    exact h'
  choose Cev hCev0 hCev using hEv
  have hmem : ∀ G : M → ℂ, Continuous G → Iw 0 G ≤ B → MemLp (fun x => G x - Fk 0 x) 2 μ :=
    fun G hG h => by
    have h1 := ((hkey _ (hG.sub (hcont _ (hF 0))).measurable.aestronglyMeasurable).symm.trans_le
      (hbdB G hG h)).trans_lt hfin
    exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).mp h1
  let K : ℕ → Set (Lp ℂ 2 μ) := fun k => {v | ∃ G : M → ℂ, Holo n X.z G ∧
    (v : M → ℂ) =ᵐ[μ] (fun x => G x - Fk 0 x) ∧ Iw k G ≤ B}
  have hanti : Antitone K := by
    intro k k' h v hv
    obtain ⟨G, hG, hvG, hI⟩ := hv
    exact ⟨G, hG, hvG, (hmono G k k' h).trans hI⟩
  have hne : ∀ k, (K k).Nonempty := fun k =>
    ⟨(hmem (Fk k) (hcont _ (hF k)) (hIfin k)).toLp _, Fk k, hF k, MemLp.coeFn_toLp _, hB k⟩

  have hclosed : ∀ k, IsClosed (K k) := by
    intro k
    refine IsSeqClosed.isClosed fun vs v hvs hlimv => ?_
    have hvs' : ∀ i, ∃ G : M → ℂ, Holo n X.z G ∧
        (vs i : M → ℂ) =ᵐ[μ] (fun x => G x - Fk 0 x) ∧ Iw k G ≤ B := hvs
    choose G hG hvG hIG using hvs'
    have hvm : Measurable (v : M → ℂ) := (Lp.stronglyMeasurable v).measurable
    have hF0m : Measurable (Fk 0) := (hcont _ (hF 0)).measurable
    have hd : ∀ i, (⇑(vs i - v) : M → ℂ) =ᵐ[μ]
        fun x => G i x - ((v : M → ℂ) x + Fk 0 x) := fun i => by
      filter_upwards [Lp.coeFn_sub (vs i) v, hvG i] with x h1 h2
      rw [h1, Pi.sub_apply, h2]; ring
    have hlim0 : Tendsto (fun i => ‖vs i - v‖) atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.mp hlimv
    have hw : Tendsto (fun i => wint n X.z (fun x => G i x - ((v : M → ℂ) x + Fk 0 x)) (p 0))
        atTop (𝓝 0) := by
      have he : (fun i => wint n X.z (fun x => G i x - ((v : M → ℂ) x + Fk 0 x)) (p 0)) =
          fun i => ENNReal.ofReal (‖vs i - v‖ ^ 2) := funext fun i => hN _ _ (hd i)
      rw [he]
      have : Tendsto (fun i => ENNReal.ofReal (‖vs i - v‖ ^ 2)) atTop
          (𝓝 (ENNReal.ofReal ((0 : ℝ) ^ 2))) :=
        (ENNReal.continuous_ofReal.tendsto _).comp (hlim0.pow 2)
      simpa using this
    obtain ⟨Gl, hGl, hfG⟩ :=
      hC X (p 0) G (fun x => (v : M → ℂ) x + Fk 0 x) (hp 0) hG (hvm.add hF0m) hw
    have hfGμ : (fun x => (v : M → ℂ) x + Fk 0 x) =ᵐ[μ] Gl :=
      (withDensity_absolutelyContinuous _ _).ae_le hfG
    have hvGl : (v : M → ℂ) =ᵐ[μ] fun x => Gl x - Fk 0 x := by
      filter_upwards [hfGμ] with x hx
      rw [← hx]; ring
    have hd2 : ∀ i, (⇑(vs i - v) : M → ℂ) =ᵐ[μ] fun x => G i x - Gl x := fun i => by
      filter_upwards [hd i, hfGμ] with x h1 h2
      rw [h1, h2]
    have hpt : ∀ x, Tendsto (fun i => G i x) atTop (𝓝 (Gl x)) := by
      intro x
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun i => norm_nonneg _)
        (fun i => hCev x (G i) Gl (hG i) hGl _ (hd2 i)) ?_
      simpa using hlim0.const_mul (Cev x)
    refine ⟨Gl, hGl, hvGl, ?_⟩
    have hf : ∀ x, Tendsto (fun i => ENNReal.ofReal (‖F0 x - G i x‖ ^ 2 *
        (om x * Real.exp (-p k x)))) atTop
        (𝓝 (ENNReal.ofReal (‖F0 x - Gl x‖ ^ 2 * (om x * Real.exp (-p k x))))) := fun x =>
      (ENNReal.continuous_ofReal.tendsto _).comp
        (((tendsto_const_nhds.sub (hpt x)).norm.pow 2).mul_const _)
    calc Iw k Gl = ∫⁻ x, liminf (fun i => ENNReal.ofReal (‖F0 x - G i x‖ ^ 2 *
          (om x * Real.exp (-p k x)))) atTop ∂vol n X.z := by
          refine lintegral_congr fun x => ?_
          exact ((hf x).liminf_eq).symm
      _ ≤ liminf (fun i => Iw k (G i)) atTop :=
          lintegral_liminf_le fun i => hmeas _ (hcont _ (hG i)) _ (hpc k)
      _ ≤ B := liminf_le_of_frequently_le' (Frequently.of_forall hIG)
  have hmid : ∀ k, ∀ v ∈ K k, ∀ w ∈ K k, (2 : ℂ)⁻¹ • (v + w) ∈ K k := by
    rintro k v ⟨G, hG, hvG, hIv⟩ w ⟨G', hG', hwG, hIw'⟩
    refine ⟨fun x => (2 : ℂ)⁻¹ * (G x + G' x),
      Holo.mul n X.z _ _ (Holo.const n X.z _) (Holo.add n X.z _ _ hG hG'), ?_, ?_⟩
    · filter_upwards [Lp.coeFn_smul (2 : ℂ)⁻¹ (v + w), Lp.coeFn_add v w, hvG, hwG]
        with x h1 h2 h3 h4
      rw [h1, Pi.smul_apply, h2, Pi.add_apply, h3, h4, smul_eq_mul]; ring
    · have hhalf : ENNReal.ofReal (1 / 2) * (B + B) = B := by
        rw [← two_mul, ← mul_assoc, ← ENNReal.ofReal_ofNat 2,
          ← ENNReal.ofReal_mul (by norm_num)]
        norm_num
      calc Iw k (fun x => (2 : ℂ)⁻¹ * (G x + G' x))
          ≤ ENNReal.ofReal (1 / 2) * (Iw k G + Iw k G') := by
            rw [hIw, ← lintegral_add_left (hmeas G (hcont _ hG) _ (hpc k)),
              ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            refine lintegral_mono fun x => ?_
            have h0 : 0 ≤ om x * Real.exp (-p k x) := by
              have := hc.le.trans (hombd x).1; positivity
            rw [← ENNReal.ofReal_add (by positivity) (by positivity),
              ← ENNReal.ofReal_mul (by norm_num)]
            refine ENNReal.ofReal_le_ofReal ?_
            have hs : F0 x - (2 : ℂ)⁻¹ * (G x + G' x) =
                (2 : ℂ)⁻¹ * ((F0 x - G x) + (F0 x - G' x)) := by ring
            have hn : ‖F0 x - (2 : ℂ)⁻¹ * (G x + G' x)‖ ≤
                (‖F0 x - G x‖ + ‖F0 x - G' x‖) / 2 := by
              rw [hs, norm_mul, norm_inv, Complex.norm_two]
              have := norm_add_le (F0 x - G x) (F0 x - G' x)
              linarith
            have hn2 : ‖F0 x - (2 : ℂ)⁻¹ * (G x + G' x)‖ ^ 2 ≤
                (‖F0 x - G x‖ ^ 2 + ‖F0 x - G' x‖ ^ 2) / 2 := by
              have h0' := norm_nonneg (F0 x - (2 : ℂ)⁻¹ * (G x + G' x))
              nlinarith [sq_nonneg (‖F0 x - G x‖ - ‖F0 x - G' x‖),
                mul_le_mul hn hn h0' (by positivity)]
            nlinarith [mul_le_mul_of_nonneg_right hn2 h0]
        _ ≤ ENNReal.ofReal (1 / 2) * (B + B) := by gcongr
        _ = B := hhalf
  have hbdd : Bornology.IsBounded (K 0) := by
    set R := (ENNReal.ofReal (2 / c) * (B + B)).toReal with hRdef
    refine (Metric.isBounded_closedBall (x := (0 : Lp ℂ 2 μ)) (r := R + 1)).subset ?_
    rintro v ⟨G, hG, hvG, hI⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 := (hN v _ hvG).symm.trans_le (hbdB G (hcont _ hG) hI)
    rw [ENNReal.ofReal_le_iff_le_toReal hfin.ne] at h1
    have hR : 0 ≤ R := ENNReal.toReal_nonneg
    nlinarith [norm_nonneg v, sq_nonneg (‖v‖ - 1)]
  obtain ⟨v, hv⟩ := cvx (Lp ℂ 2 μ) K hanti hne hclosed hmid hbdd
  obtain ⟨G, hG, hvG, -⟩ := hv 0
  have hIk : ∀ k, Iw k G ≤ B := fun k => by
    obtain ⟨G', hG', hvG', hI'⟩ := hv k
    have heq : G = G' := funext fun x => by
      have h0 : (⇑(0 : Lp ℂ 2 μ) : M → ℂ) =ᵐ[μ] fun x => G x - G' x := by
        filter_upwards [Lp.coeFn_zero ℂ 2 μ, hvG, hvG'] with x h1 h2 h3
        rw [h1, Pi.zero_apply]
        linear_combination h2 - h3
      have h1 := hCev x G G' hG hG' 0 h0
      rw [norm_zero, mul_zero] at h1
      exact sub_eq_zero.mp (norm_le_zero_iff.mp h1)
    rw [heq]; exact hI'
  refine ⟨G, hG, ?_⟩
  have hmon : ∀ x, Monotone fun k =>
      ENNReal.ofReal (‖F0 x - G x‖ ^ 2 * (om x * Real.exp (-p k x))) := fun x k k' h => by
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := Real.exp_le_exp.mpr (neg_le_neg (hpanti x h))
    have h0 := hc.le.trans (hombd x).1
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 h0) (by positivity)
  have hlimx : ∀ x, Tendsto (fun k =>
      ENNReal.ofReal (‖F0 x - G x‖ ^ 2 * (om x * Real.exp (-p k x)))) atTop
      (𝓝 (ENNReal.ofReal (‖F0 x - G x‖ ^ 2 * (om x * Real.exp (-q x))))) := fun x =>
    (ENNReal.continuous_ofReal.tendsto _).comp
      ((((Real.continuous_exp.tendsto _).comp (hpq x).neg).const_mul _).const_mul _)
  have hT := lintegral_tendsto_of_tendsto_of_monotone
    (μ := vol n X.z) (fun k => (hmeas G (hcont _ hG) _ (hpc k)).aemeasurable)
    (ae_of_all _ hmon) (ae_of_all _ hlimx)
  exact le_of_tendsto' hT hIk

end

end GlobalTheory
end
end
