module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CuspRepresentativesFiniteStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsCuspReductionBoundStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.MobiusActionUpperHalfPlaneStatement
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.NumberTheory.NumberField.Units.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Module.ZLattice.Basic
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.NumberTheory.NumberField.Units.Basic
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.ReduceModChar

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitBalancingImaginaryParts

section

@[expose] public section

open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem
  IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

namespace GlobalTheory.CompanionTheory.SW.UnitBalance


open NumberField.Units NumberField.Units.dirichletUnitTheorem in
theorem exists_bound_log_centered (E : Type) [Field E] [NumberField E] :
    ∃ R : ℝ, ∀ t : InfinitePlace E → ℝ, ∃ (u : (𝓞 E)ˣ) (s : ℝ), ∀ w : InfinitePlace E,
      |t w + Real.log (w (u : E)) - s| ≤ R := by
  classical
  let B := (NumberField.Units.basisUnitLattice E).ofZLatticeBasis ℝ
    (NumberField.Units.unitLattice E)
  obtain ⟨C, hC⟩ := (ZSpan.fundamentalDomain_isBounded B).exists_norm_le
  refine ⟨Fintype.card (InfinitePlace E) * |C|, fun t => ?_⟩
  have hd : (Module.finrank ℚ E : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  let s : ℝ := (∑ w : InfinitePlace E, (w.mult : ℝ) * t w) / Module.finrank ℚ E
  let l : logSpace E := fun w => (w.1.mult : ℝ) * (t w.1 - s)
  obtain ⟨⟨e, he⟩, h2, -⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain B l
  rw [Module.Basis.ofZLatticeBasis_span ℝ (NumberField.Units.unitLattice E)] at he
  obtain ⟨u, -, rfl⟩ := he
  let a : InfinitePlace E → ℝ := fun w => (w.mult : ℝ) * (t w - s + Real.log (w (u.toMul : E)))
  have hsum : ∑ w, a w = 0 := by
    have h1 := sum_mult_mul_log (K := E) u.toMul
    have h3 : ∑ w : InfinitePlace E, (w.mult : ℝ) = Module.finrank ℚ E := by
      exact_mod_cast InfinitePlace.sum_mult_eq (K := E)
    simp only [a, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, h1, h3, s]
    field_simp
    ring
  have ha : ∀ w, w ≠ w₀ → |a w| ≤ |C| := fun w hw => by
    have h4 := (norm_le_pi_norm _ (⟨w, hw⟩ : {w : InfinitePlace E // w ≠ w₀})).trans (hC _ h2)
    refine le_trans (le_of_eq ?_) (h4.trans (le_abs_self C))
    rw [Real.norm_eq_abs]
    congr 1
    change _ = (w.mult : ℝ) * Real.log (w (u.toMul : E)) + (w.mult : ℝ) * (t w - s)
    simp only [a]
    ring
  have hcard : (1 : ℝ) ≤ Fintype.card (InfinitePlace E) := by exact_mod_cast Fintype.card_pos
  have ha' : ∀ w, |a w| ≤ Fintype.card (InfinitePlace E) * |C| := fun w => by
    by_cases hw : w = w₀
    · subst hw
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ w₀), add_eq_zero_iff_eq_neg] at hsum
      rw [hsum, abs_neg]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_card_nsmul _ _ _ fun w hw => ha w (Finset.ne_of_mem_erase hw)).trans ?_
      rw [nsmul_eq_mul]
      gcongr
      exact Finset.card_le_univ _
    · exact (ha w hw).trans (le_mul_of_one_le_left (abs_nonneg C) hcard)
  refine ⟨u.toMul, s, fun w => ?_⟩
  have h5 : |t w - s + Real.log (w (u.toMul : E))| ≤ |a w| := by
    simp only [a]
    rw [abs_mul]
    refine le_mul_of_one_le_left (abs_nonneg _) ?_
    rw [Nat.abs_cast]
    exact_mod_cast w.mult_pos
  have h6 := h5.trans (ha' w)
  have h7 : t w + Real.log (w (u.toMul : E)) - s = t w - s + Real.log (w (u.toMul : E)) := by ring
  rw [h7]
  exact h6

theorem balance_by_units : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F →
    ∀ ρ : InfinitePlace F → (F →+* ℝ), (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) →
    ∃ κ : ℝ, 0 < κ ∧ ∀ y : InfinitePlace F → ℝ, (∀ w, 0 < y w) →
      ∃ u : (𝓞 F)ˣ, ∀ v w, κ * (ρ w ((u : 𝓞 F) : F) ^ 2 * y w) ≤ ρ v ((u : 𝓞 F) : F) ^ 2 * y v := by
  intro F _ _ _ ρ hρ
  obtain ⟨R, hR⟩ := exists_bound_log_centered F
  refine ⟨Real.exp (-(4 * R)), Real.exp_pos _, fun y hy => ?_⟩
  obtain ⟨u, s, hu⟩ := hR (fun w => Real.log (y w) / 2)
  refine ⟨u, fun v w => ?_⟩
  have hne : ((u : 𝓞 F) : F) ≠ 0 := NumberField.Units.coe_ne_zero u
  have hexp : ∀ w : InfinitePlace F, ρ w ((u : 𝓞 F) : F) ^ 2 * y w =
      Real.exp (2 * (Real.log (y w) / 2 + Real.log (w ((u : 𝓞 F) : F)))) := by
    intro w
    have habs : w ((u : 𝓞 F) : F) = |ρ w ((u : 𝓞 F) : F)| := by
      rw [← InfinitePlace.norm_embedding_eq, ← hρ, Complex.norm_real, Real.norm_eq_abs]
    have hpos : 0 < w ((u : 𝓞 F) : F) := w.pos_iff.2 hne
    have e1 : 2 * (Real.log (y w) / 2 + Real.log (w ((u : 𝓞 F) : F))) =
        Real.log (w ((u : 𝓞 F) : F)) + Real.log (w ((u : 𝓞 F) : F)) + Real.log (y w) := by ring
    rw [e1, Real.exp_add, Real.exp_add, Real.exp_log hpos, Real.exp_log (hy w), habs, ← sq, sq_abs]
  rw [hexp v, hexp w, ← Real.exp_add]
  apply Real.exp_le_exp.2
  have h1 := abs_le.1 (hu v)
  have h2 := abs_le.1 (hu w)
  linarith [h1.1, h1.2, h2.1, h2.2]

end GlobalTheory.CompanionTheory.SW.UnitBalance
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitBalancingImaginaryPartsStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

theorem _root_.GlobalTheory.T.unit_balancing_imaginary_parts : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ ρ : InfinitePlace F → (F →+* ℝ), (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) → ∃ κ : ℝ, 0 < κ ∧ ∀ y : InfinitePlace F → ℝ, (∀ w, 0 < y w) → ∃ u : (𝓞 F)ˣ, ∀ v w, κ * (ρ w ((u : 𝓞 F) : F) ^ 2 * y w) ≤ ρ v ((u : 𝓞 F) : F) ^ 2 * y v := by
  first | exact @GlobalTheory.CompanionTheory.SW.UnitBalance.balance_by_units | exact GlobalTheory.CompanionTheory.SW.UnitBalance.balance_by_units | (intros; apply GlobalTheory.CompanionTheory.SW.UnitBalance.balance_by_units <;> assumption)
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ReductionToSiegelDomain

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

namespace GlobalTheory.CompanionTheory.SW.Red

theorem prod_sq_embedding {F : Type} [Field F] [NumberField F] (hF : IsTotallyReal F)
    (ρ : InfinitePlace F → (F →+* ℝ))
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) (x : F) :
    ∏ w, (ρ w x) ^ 2 = ((Algebra.norm ℚ x : ℚ) : ℝ) ^ 2 := by
  have h1 := InfinitePlace.prod_eq_abs_norm x
  have h2 : ∀ w : InfinitePlace F, w x ^ w.mult = |ρ w x| := by
    intro w
    have hm : w.mult = 1 := by
      simp [InfinitePlace.mult, hF.isReal w]
    rw [hm, pow_one, ← InfinitePlace.norm_embedding_eq, ← hρ]
    simp
  have h3 : ∏ w : InfinitePlace F, |ρ w x| = |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
    rw [← Finset.prod_congr rfl (fun w _ => h2 w), h1]
    simp
  calc ∏ w, (ρ w x) ^ 2 = ∏ w, |ρ w x| ^ 2 := by simp
    _ = (∏ w, |ρ w x|) ^ 2 := by rw [Finset.prod_pow]
    _ = _ := by rw [h3, sq_abs]

theorem balanced_lower {ι : Type} [Fintype ι] (z : ι → ℝ) (hz : ∀ i, 0 < z i) (κ P : ℝ)
    (hκ : 0 < κ) (hbal : ∀ v w, κ * z w ≤ z v) (hprod : P ≤ ∏ i, z i) (w : ι) :
    κ * min 1 P ≤ z w := by
  by_contra h
  push_neg at h
  set q := z w / κ with hq
  have hqpos : 0 < q := div_pos (hz w) hκ
  have hqlt : q < min 1 P := by
    rw [hq, div_lt_iff₀ hκ]; linarith
  have hq1 : q ≤ 1 := (hqlt.trans_le (min_le_left _ _)).le
  have hqP : q < P := hqlt.trans_le (min_le_right _ _)
  have hle : ∀ v, z v ≤ q := by
    intro v
    rw [hq, le_div_iff₀ hκ]
    have := hbal w v
    linarith
  haveI : Nonempty ι := ⟨w⟩
  have hcard : Fintype.card ι ≠ 0 := Fintype.card_ne_zero
  have hp : ∏ i, z i ≤ q ^ Fintype.card ι := by
    calc ∏ i, z i ≤ ∏ _i : ι, q :=
          Finset.prod_le_prod₀ (fun i _ => (hz i).le) (fun i _ => hle i)
      _ = q ^ Fintype.card ι := by simp
  have := pow_le_of_le_one hqpos.le hq1 hcard
  linarith

theorem reduction : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ ρ : InfinitePlace F → (F →+* ℝ), (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) → ∃ (s : Finset SL(2, F)) (κ t : ℝ), 0 < κ ∧ 0 < t ∧ ∀ τ : InfinitePlace F → ℂ, (∀ w, 0 < (τ w).im) → ∃ r ∈ s, ∃ k : SL(2, F), (∀ i j, ∃ z : 𝓞 F, (z : F) = k i j) ∧ (∀ w, t ≤ (mob ρ (r * k) τ w).im) ∧ ∀ v w, κ * (mob ρ (r * k) τ w).im ≤ (mob ρ (r * k) τ v).im := by
  intro F _ _ hF ρ hρ
  obtain ⟨C₁, hC₁⟩ := GlobalTheory.T.exists_cusp_reduction_bound F hF ρ hρ
  obtain ⟨s, C₂, hrow⟩ := GlobalTheory.T.cusp_representatives_finite F
  obtain ⟨κ, hκ, hbal⟩ := GlobalTheory.T.unit_balancing_imaginary_parts F hF ρ hρ
  set n := Fintype.card (InfinitePlace F) with hn
  set A : ℝ := |C₁| + 1 with hAdef
  set B : ℝ := |C₂| + 1 with hBdef
  set P : ℝ := 1 / (A ^ n * B ^ 2) with hPdef
  have hP : 0 < P := by positivity
  refine ⟨s, κ, κ * min 1 P, hκ, mul_pos hκ (lt_min one_pos hP), ?_⟩
  intro τ hτ
  have him := (GlobalTheory.T.mobius_action_upper_half_plane F ρ τ hτ).1
  obtain ⟨c, d, hcd, hD⟩ := hC₁ τ hτ
  obtain ⟨l, hl0, hlN, hl⟩ := hrow c d hcd
  obtain ⟨r₁, -, k₁, -, h₁0, h₁1⟩ := hl 1
  have h₁0' : (r₁ * k₁) 1 0 = l * c := by simpa using h₁0
  have h₁1' : (r₁ * k₁) 1 1 = l * d := by simpa using h₁1
  set y' : InfinitePlace F → ℝ := fun w => (mob ρ (r₁ * k₁) τ w).im with hy'
  have hy'pos : ∀ w, 0 < y' w := fun w => (him _ w).2
  obtain ⟨u, hu⟩ := hbal y' hy'pos
  obtain ⟨r, hr, k, hk, h0, h1⟩ := hl u⁻¹

  set N : InfinitePlace F → ℝ := fun w =>
    ‖((ρ w (l * c) : ℝ) : ℂ) * τ w + (ρ w (l * d) : ℝ)‖ ^ 2 with hN
  have hy'eq : ∀ w, y' w = (τ w).im / N w := by
    intro w
    have := (him (r₁ * k₁) w).1
    rw [h₁0', h₁1'] at this
    exact this
  have hNpos : ∀ w, 0 < N w := by
    intro w
    have hnn : 0 ≤ N w := by positivity
    rcases hnn.lt_or_eq with h | h
    · exact h
    · have := hy'pos w
      rw [hy'eq w, ← h, div_zero] at this
      exact absurd this (lt_irrefl _)
  have hinv : ∀ w, ρ w (((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * ρ w ((u : 𝓞 F) : F) = 1 := by
    intro w
    rw [← map_mul]
    have : (((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * ((u : 𝓞 F) : F) = 1 := by
      have h := congrArg (fun x : 𝓞 F => (x : F)) (Units.inv_mul u)
      simpa using h
    rw [this, map_one]
  have hz : ∀ w, (mob ρ (r * k) τ w).im = ρ w ((u : 𝓞 F) : F) ^ 2 * y' w := by
    intro w
    have hw := (him (r * k) w).1
    rw [h0, h1] at hw
    have hnorm : ‖((ρ w (((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F) * l * c) : ℝ) : ℂ) * τ w
        + (ρ w (((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F) * l * d) : ℝ)‖ ^ 2
        = ρ w (((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) ^ 2 * N w := by
      have : ((ρ w ((((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * l * c) : ℝ) : ℂ) * τ w
          + (ρ w ((((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * l * d) : ℝ)
          = ((ρ w (((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) : ℝ) : ℂ)
            * (((ρ w (l * c) : ℝ) : ℂ) * τ w + (ρ w (l * d) : ℝ)) := by
        simp only [map_mul, Complex.ofReal_mul]
        ring
      rw [this, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [hw, hnorm, hy'eq w]
    have ha := hinv w
    have hNw := (hNpos w).ne'
    have ha0 : ρ w (((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) ≠ 0 := left_ne_zero_of_mul_eq_one ha
    have hb : ρ w ((u : 𝓞 F) : F) = (ρ w (((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F))⁻¹ :=
      eq_inv_of_mul_eq_one_right ha
    rw [hb]
    field_simp
  have hzpos : ∀ w, 0 < (mob ρ (r * k) τ w).im := fun w => (him _ w).2
  have hbal' : ∀ v w, κ * (mob ρ (r * k) τ w).im ≤ (mob ρ (r * k) τ v).im := by
    intro v w
    rw [hz v, hz w]
    exact hu v w

  have hlow : ∀ w, 1 / (A * ρ w l ^ 2) ≤ y' w := by
    intro w
    have hlw : ρ w l ≠ 0 := (map_ne_zero _).2 hl0
    have hlsq : 0 < ρ w l ^ 2 := by positivity
    have hNle : N w ≤ ρ w l ^ 2 * (A * (τ w).im) := by
      have h1' : N w = ρ w l ^ 2 * ‖((ρ w (c : F) : ℝ) : ℂ) * τ w + (ρ w (d : F) : ℝ)‖ ^ 2 := by
        have : ((ρ w (l * c) : ℝ) : ℂ) * τ w + (ρ w (l * d) : ℝ)
            = ((ρ w l : ℝ) : ℂ) * (((ρ w (c : F) : ℝ) : ℂ) * τ w + (ρ w (d : F) : ℝ)) := by
          simp only [map_mul, Complex.ofReal_mul]
          ring
        simp only [hN]
        rw [this, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      rw [h1']
      apply mul_le_mul_of_nonneg_left _ hlsq.le
      refine (hD w).trans ?_
      apply mul_le_mul_of_nonneg_right _ (hτ w).le
      have := le_abs_self C₁
      simp only [hAdef]
      linarith
    rw [hy'eq w, div_le_div_iff₀ (by positivity) (hNpos w)]
    nlinarith [hNle]
  have hprodu : ∏ w, ρ w ((u : 𝓞 F) : F) ^ 2 = 1 := by
    rw [prod_sq_embedding hF ρ hρ]
    have h := (NumberField.isUnit_iff_norm (x := (u : 𝓞 F))).1 u.isUnit
    have h' : |((Algebra.norm ℚ ((u : 𝓞 F) : F) : ℚ) : ℝ)| = 1 := by
      rw [RingOfIntegers.coe_norm] at h
      exact_mod_cast h
    rw [← sq_abs, h', one_pow]
  have hprod : P ≤ ∏ w, (mob ρ (r * k) τ w).im := by
    rw [Finset.prod_congr rfl (fun w _ => hz w), Finset.prod_mul_distrib, hprodu, one_mul]
    have h1' : ∏ w, 1 / (A * ρ w l ^ 2) ≤ ∏ w, y' w :=
      Finset.prod_le_prod₀ (fun w _ => by
        have hlw : ρ w l ≠ 0 := (map_ne_zero _).2 hl0
        positivity) (fun w _ => hlow w)
    refine le_trans ?_ h1'
    have h2' : ∏ w, 1 / (A * ρ w l ^ 2) = 1 / (A ^ n * ((Algebra.norm ℚ l : ℚ) : ℝ) ^ 2) := by
      rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, prod_sq_embedding hF ρ hρ]
      simp [hn]
    rw [h2', hPdef]
    have hN0 : ((Algebra.norm ℚ l : ℚ) : ℝ) ≠ 0 := by
      have : (Algebra.norm ℚ l : ℚ) ≠ 0 := (Algebra.norm_ne_zero_iff).2 hl0
      exact_mod_cast this
    apply one_div_le_one_div_of_le (by positivity)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have h3 : |((Algebra.norm ℚ l : ℚ) : ℝ)| ≤ B := by
      have := le_abs_self C₂
      simp only [hBdef]
      linarith
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h3 2
  refine ⟨r, hr, k, hk, ?_, hbal'⟩
  intro w
  exact balanced_lower _ hzpos κ P hκ hbal' hprod w

end GlobalTheory.CompanionTheory.SW.Red
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ReductionToSiegelDomainStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

theorem _root_.GlobalTheory.T.reduction_to_siegel_domain : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ ρ : InfinitePlace F → (F →+* ℝ), (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) → ∃ (s : Finset SL(2, F)) (κ t : ℝ), 0 < κ ∧ 0 < t ∧ ∀ τ : InfinitePlace F → ℂ, (∀ w, 0 < (τ w).im) → ∃ r ∈ s, ∃ k : SL(2, F), (∀ i j, ∃ z : 𝓞 F, (z : F) = k i j) ∧ (∀ w, t ≤ (mob ρ (r * k) τ w).im) ∧ ∀ v w, κ * (mob ρ (r * k) τ w).im ≤ (mob ρ (r * k) τ v).im := by
  first | exact @GlobalTheory.CompanionTheory.SW.Red.reduction | exact GlobalTheory.CompanionTheory.SW.Red.reduction | (intros; apply GlobalTheory.CompanionTheory.SW.Red.reduction <;> assumption)
end
end
