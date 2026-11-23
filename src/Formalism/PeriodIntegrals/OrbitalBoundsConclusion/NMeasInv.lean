module

public import Formalism.PeriodIntegrals.NMeasInv
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureInverseContraction.Development
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureInverseContraction.AmatInvMul
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.HJMulVecGen
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.KoszulLowersPower
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureInverseContraction.ConjSubMulVec

section

@[expose] public section

noncomputable section

open Matrix

namespace PI.NMeasInv.UnitaryGroupMassFormula

section Tri

variable {n r : ℕ} {ε : Fin n → Bool} {e f : Fin r → Fin n → ℂ}

theorem hJ_add_left (x x' y : Fin n → ℂ) : hJ ε (x + x') y = hJ ε x y + hJ ε x' y := by
  rw [hJ_conj ε y, hJ_conj ε y x, hJ_conj ε y x', hJ_add, star_add]

theorem Pw_add (x y : Fin n → ℂ) : Pw ε e f (x + y) = Pw ε e f x + Pw ε e f y := by
  simp only [Pw, hJ_add, add_smul, Finset.sum_add_distrib]; abel

theorem Pw_smul (c : ℂ) (x : Fin n → ℂ) : Pw ε e f (c • x) = c • Pw ε e f x := by
  simp only [Pw, hJ_smul, mul_smul, ← Finset.smul_sum, smul_sub]

theorem Pw_zero : Pw ε e f 0 = 0 := by simp [Pw, hJ_zero]

theorem Pw_sum {ι : Type*} (s : Finset ι) (x : ι → Fin n → ℂ) :
    Pw ε e f (∑ i ∈ s, x i) = ∑ i ∈ s, Pw ε e f (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Pw_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Pw_add, ih]

theorem mulVec_fsum {ι : Type*} (s : Finset ι) (M : Matrix (Fin n) (Fin n) ℂ) (x : ι → Fin n → ℂ) :
    M *ᵥ (∑ i ∈ s, x i) = ∑ i ∈ s, M *ᵥ x i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, mulVec_add, ih]

theorem hJ_unitary {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) (x y : Fin n → ℂ) :
    hJ ε (g *ᵥ x) (g *ᵥ y) = hJ ε x y := by
  rw [hJ_mulVec_eq, hg]; rfl

theorem conj_sub_mulVec (hG : Gram ε e f) (s : Fin r → ℝ) (hs : ∀ b, s b ≠ 0) (g : Matrix (Fin n) (Fin n) ℂ)
    (y : Fin n → ℂ) : (Amat ε e f s * g * Amat ε e f s⁻¹ - 1) *ᵥ y =
      Afun ε e f s ((g - 1) *ᵥ Afun ε e f s⁻¹ y) := by
  rw [sub_mulVec, one_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, Amat_mulVec, Amat_mulVec, sub_mulVec,
    one_mulVec]
  have := (Alin ε e f s).map_sub (g *ᵥ Afun ε e f s⁻¹ y) (Afun ε e f s⁻¹ y)
  simp only [Alin_apply] at this
  rw [this, A_inv hG s hs]

variable (hG : Gram ε e f)
include hG

theorem Pw_e (d : Fin r) : Pw ε e f (e d) = 0 := by
  unfold Pw
  simp only [fe hG, hG.ee, ite_smul, one_smul, zero_smul, Finset.sum_const_zero, sub_zero]
  simp [Finset.sum_ite_eq]

theorem span_facts (k : ℕ) {v : Fin n → ℂ} (hv : v ∈ spanLt e k) :
    (∀ b : Fin r, k ≤ b.val → hJ ε (f b) v = 0) ∧ (∀ b, hJ ε (e b) v = 0) ∧ Pw ε e f v = 0 := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨d, hd, rfl⟩ := hx
    refine ⟨fun b hb => ?_, fun b => hG.ee b d, Pw_e hG d⟩
    rw [fe hG, if_neg]
    rintro rfl
    exact (not_lt.2 hb) hd
  | zero => exact ⟨fun b _ => hJ_zero ε _, fun b => hJ_zero ε _, Pw_zero⟩
  | add x y _ _ hx hy =>
    exact ⟨fun b hb => by rw [hJ_add, hx.1 b hb, hy.1 b hb, add_zero],
      fun b => by rw [hJ_add, hx.2.1 b, hy.2.1 b, add_zero], by rw [Pw_add, hx.2.2, hy.2.2, add_zero]⟩
  | smul c x _ hx =>
    exact ⟨fun b hb => by rw [hJ_smul, hx.1 b hb, mul_zero], fun b => by rw [hJ_smul, hx.2.1 b, mul_zero],
      by rw [Pw_smul, hx.2.2, smul_zero]⟩

theorem tri_f {z : Fin n → ℂ} {g g' : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) (hgg : g * g' = 1)
    (hN' : InN ε e z g') (b c : Fin r) (hbc : ¬ c < b) : hJ ε (e b) ((g - 1) *ᵥ f c) = 0 := by
  rw [sub_mulVec, one_mulVec, hJ_sub]
  have h1 : e b = g *ᵥ (g' *ᵥ e b) := by rw [mulVec_mulVec, hgg, one_mulVec]
  have h2 : g' *ᵥ e b = e b + (g' - 1) *ᵥ e b := by rw [sub_mulVec, one_mulVec]; abel
  have h3 := (span_facts hG b.val (hN'.1.1 b)).1 c (Fin.le_iff_val_le_val.1 (not_lt.1 hbc))
  have key : hJ ε (e b) (g *ᵥ f c) = hJ ε (e b) (f c) := by
    calc hJ ε (e b) (g *ᵥ f c) = hJ ε (g *ᵥ (g' *ᵥ e b)) (g *ᵥ f c) := by rw [← h1]
      _ = hJ ε (g' *ᵥ e b) (f c) := hJ_unitary hg _ _
      _ = hJ ε (e b) (f c) + hJ ε ((g' - 1) *ᵥ e b) (f c) := by rw [h2, hJ_add_left]
      _ = hJ ε (e b) (f c) := by rw [hJ_conj ε (f c) ((g' - 1) *ᵥ e b), h3, star_zero, add_zero]
  rw [key, sub_self]


omit hG in
def Sb (ε : Fin n → Bool) (e f : Fin r → Fin n → ℂ) (g : Matrix (Fin n) (Fin n) ℂ) (y : Fin n → ℂ)
    (i : Fin n) : ℝ :=
  ∑ b, ((∑ c, ‖hJ ε (f c) y * hJ ε (f b) ((g - 1) *ᵥ e c)‖ +
      ∑ c, ‖hJ ε (e c) y * hJ ε (f b) ((g - 1) *ᵥ f c)‖ +
      ‖hJ ε (f b) ((g - 1) *ᵥ Pw ε e f y)‖) * ‖e b i‖) +
    ∑ b, (∑ c, ‖hJ ε (e c) y * hJ ε (e b) ((g - 1) *ᵥ f c)‖) * ‖f b i‖ +
    ∑ c, ‖hJ ε (e c) y‖ * ‖Pw ε e f ((g - 1) *ᵥ f c) i‖

omit hG in
theorem nb {κ lam : ℝ} {x : ℂ} (hκ0 : 0 ≤ κ) (hκ : κ ≤ lam⁻¹ ∨ x = 0) : ‖(κ : ℂ) * x‖ ≤ lam⁻¹ * ‖x‖ := by
  rcases hκ with h | h
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hκ0]
    exact mul_le_mul_of_nonneg_right h (norm_nonneg _)
  · simp [h]

theorem entry_bound (t : Fin r → ℝ) (lam : ℝ) (hlam : 1 ≤ lam) (ht1 : ∀ b, lam ≤ t b)
    (ht2 : ∀ b c : Fin r, b < c → lam * t c ≤ t b) {z : Fin n → ℂ} {g g' : Matrix (Fin n) (Fin n) ℂ}
    (hg : Formalism.REAL.inUJ ε g) (hgg : g * g' = 1) (hN : InN ε e z g) (hN' : InN ε e z g') (y : Fin n → ℂ)
    (i : Fin n) : ‖Afun ε e f t⁻¹ ((g - 1) *ᵥ Afun ε e f t y) i‖ ≤ lam⁻¹ * Sb ε e f g y i := by
  have hl0 : 0 < lam := lt_of_lt_of_le one_pos hlam
  have ht0 : ∀ b, 0 < t b := fun b => lt_of_lt_of_le hl0 (ht1 b)

  have hXe := fun c => span_facts hG _ (hN.1.1 c)
  have hXw : ∀ v, (∀ a, hJ ε (e a) v = 0) → (∀ b, hJ ε (e b) ((g - 1) *ᵥ v) = 0) ∧ Pw ε e f ((g - 1) *ᵥ v) = 0 :=
    fun v hv => (span_facts hG _ (hN.2 v hv)).2
  have hPwy : ∀ a, hJ ε (e a) (Pw ε e f y) = 0 := fun a => e_Pw hG a y

  have hv : (g - 1) *ᵥ Afun ε e f t y = ∑ c, ((t c : ℂ) * hJ ε (f c) y) • (g - 1) *ᵥ e c +
      ∑ c, ((t c : ℂ)⁻¹ * hJ ε (e c) y) • (g - 1) *ᵥ f c + (g - 1) *ᵥ Pw ε e f y := by
    rw [Afun, mulVec_add, mulVec_add, mulVec_fsum, mulVec_fsum]
    simp only [mulVec_smul]
  set w := (g - 1) *ᵥ Afun ε e f t y with hw
  have hα : ∀ b, hJ ε (f b) w = ∑ c, (t c : ℂ) * (hJ ε (f c) y * hJ ε (f b) ((g - 1) *ᵥ e c)) +
      ∑ c, (t c : ℂ)⁻¹ * (hJ ε (e c) y * hJ ε (f b) ((g - 1) *ᵥ f c)) + hJ ε (f b) ((g - 1) *ᵥ Pw ε e f y) := by
    intro b
    rw [hv, hJ_add, hJ_add, hJ_sum, hJ_sum]
    simp only [hJ_smul, mul_assoc]
  have hβ : ∀ b, hJ ε (e b) w = ∑ c, (t c : ℂ)⁻¹ * (hJ ε (e c) y * hJ ε (e b) ((g - 1) *ᵥ f c)) := by
    intro b
    rw [hv, hJ_add, hJ_add, hJ_sum, hJ_sum, (hXw _ hPwy).1 b]
    simp only [hJ_smul, (hXe _).2.1 b, mul_zero, Finset.sum_const_zero, zero_add, add_zero, mul_assoc]
  have hP : Pw ε e f w = ∑ c, ((t c : ℂ)⁻¹ * hJ ε (e c) y) • Pw ε e f ((g - 1) *ᵥ f c) := by
    rw [hv, Pw_add, Pw_add, Pw_sum, Pw_sum, (hXw _ hPwy).2]
    simp only [Pw_smul, (hXe _).2.2, smul_zero, Finset.sum_const_zero, zero_add, add_zero]

  have hent : Afun ε e f t⁻¹ w i =
      ∑ b, (∑ c, (((t c / t b : ℝ) : ℂ) * (hJ ε (f c) y * hJ ε (f b) ((g - 1) *ᵥ e c))) +
        ∑ c, ((((t c * t b)⁻¹ : ℝ) : ℂ) * (hJ ε (e c) y * hJ ε (f b) ((g - 1) *ᵥ f c))) +
        (((t b)⁻¹ : ℝ) : ℂ) * hJ ε (f b) ((g - 1) *ᵥ Pw ε e f y)) * e b i +
      ∑ b, (∑ c, (((t b / t c : ℝ) : ℂ) * (hJ ε (e c) y * hJ ε (e b) ((g - 1) *ᵥ f c)))) * f b i +
      ∑ c, (((t c)⁻¹ : ℝ) : ℂ) * (hJ ε (e c) y * Pw ε e f ((g - 1) *ᵥ f c) i) := by
    rw [Afun, hP]
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hα, hβ, Pi.inv_apply,
      Complex.ofReal_inv, inv_inv]
    congr 1
    congr 1
    · refine Finset.sum_congr rfl fun b _ => ?_
      congr 1
      rw [mul_add, mul_add, Finset.mul_sum, Finset.mul_sum]
      congr 1
      congr 1
      · refine Finset.sum_congr rfl fun c _ => ?_
        push_cast; ring
      · refine Finset.sum_congr rfl fun c _ => ?_
        push_cast; ring
    · refine Finset.sum_congr rfl fun b _ => ?_
      congr 1
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      push_cast; ring
    · refine Finset.sum_congr rfl fun c _ => ?_
      push_cast; ring
  rw [hent]

  have k1 : ∀ b c : Fin r, ‖(((t c / t b : ℝ) : ℂ) * (hJ ε (f c) y * hJ ε (f b) ((g - 1) *ᵥ e c)))‖ ≤
      lam⁻¹ * ‖hJ ε (f c) y * hJ ε (f b) ((g - 1) *ᵥ e c)‖ := by
    intro b c
    refine nb (div_nonneg (ht0 c).le (ht0 b).le) ?_
    by_cases hbc : b < c
    · left
      rw [div_le_iff₀ (ht0 b)]
      have := ht2 b c hbc
      calc t c = lam⁻¹ * (lam * t c) := by field_simp
        _ ≤ lam⁻¹ * t b := mul_le_mul_of_nonneg_left this (inv_nonneg.2 hl0.le)
    · right
      rw [(hXe c).1 b (Fin.le_iff_val_le_val.1 (not_lt.1 hbc)), mul_zero]
  have k2 : ∀ b c : Fin r, ‖((((t c * t b)⁻¹ : ℝ) : ℂ) * (hJ ε (e c) y * hJ ε (f b) ((g - 1) *ᵥ f c)))‖ ≤
      lam⁻¹ * ‖hJ ε (e c) y * hJ ε (f b) ((g - 1) *ᵥ f c)‖ := by
    intro b c
    refine nb (inv_nonneg.2 (mul_nonneg (ht0 c).le (ht0 b).le)) (Or.inl ?_)
    apply inv_anti₀ hl0
    calc lam = 1 * lam := (one_mul _).symm
      _ ≤ t c * t b := mul_le_mul (hlam.trans (ht1 c)) (ht1 b) hl0.le (ht0 c).le
  have k3 : ∀ b : Fin r, ‖((((t b)⁻¹ : ℝ) : ℂ) * hJ ε (f b) ((g - 1) *ᵥ Pw ε e f y))‖ ≤
      lam⁻¹ * ‖hJ ε (f b) ((g - 1) *ᵥ Pw ε e f y)‖ := fun b =>
    nb (inv_nonneg.2 (ht0 b).le) (Or.inl (inv_anti₀ hl0 (ht1 b)))
  have k4 : ∀ b c : Fin r, ‖(((t b / t c : ℝ) : ℂ) * (hJ ε (e c) y * hJ ε (e b) ((g - 1) *ᵥ f c)))‖ ≤
      lam⁻¹ * ‖hJ ε (e c) y * hJ ε (e b) ((g - 1) *ᵥ f c)‖ := by
    intro b c
    refine nb (div_nonneg (ht0 b).le (ht0 c).le) ?_
    by_cases hcb : c < b
    · left
      rw [div_le_iff₀ (ht0 c)]
      have := ht2 c b hcb
      calc t b = lam⁻¹ * (lam * t b) := by field_simp
        _ ≤ lam⁻¹ * t c := mul_le_mul_of_nonneg_left this (inv_nonneg.2 hl0.le)
    · right
      rw [tri_f hG hg hgg hN' b c hcb, mul_zero]
  have k5 : ∀ c : Fin r, ‖((((t c)⁻¹ : ℝ) : ℂ) * (hJ ε (e c) y * Pw ε e f ((g - 1) *ᵥ f c) i))‖ ≤
      lam⁻¹ * (‖hJ ε (e c) y‖ * ‖Pw ε e f ((g - 1) *ᵥ f c) i‖) := by
    intro c
    rw [← norm_mul]
    exact nb (inv_nonneg.2 (ht0 c).le) (Or.inl (inv_anti₀ hl0 (ht1 c)))

  unfold Sb
  simp only [mul_add, Finset.mul_sum]
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
  · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
    rw [norm_mul, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    refine (norm_add_le _ _).trans ?_
    rw [mul_add]
    refine add_le_add ((norm_add_le _ _).trans ?_) (k3 b)
    rw [mul_add]
    refine add_le_add ((norm_sum_le _ _).trans ?_) ((norm_sum_le _ _).trans ?_)
    · rw [Finset.mul_sum]; exact Finset.sum_le_sum fun c _ => k1 b c
    · rw [Finset.mul_sum]; exact Finset.sum_le_sum fun c _ => k2 b c
  · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
    rw [norm_mul, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]; exact Finset.sum_le_sum fun c _ => k4 b c
  · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
    exact k5 c

end Tri

end PI.NMeasInv.UnitaryGroupMassFormula
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureInverseContraction.MeasureContractionFormula

section

@[expose] public section

noncomputable section

open Matrix MeasureTheory NumberField

namespace PI.NMeasInv.UnitaryGroupMassFormula

section Inst

variable {n r : ℕ} {ε : Fin n → Bool} {e f : Fin r → Fin n → ℂ}

def wt (r : ℕ) (lam : ℝ) : Fin r → ℝ := fun b => lam ^ (r - b.val)

theorem wt_ge (lam : ℝ) (hlam : 1 ≤ lam) (b : Fin r) : lam ≤ wt r lam b := by
  unfold wt
  have := b.isLt
  calc lam = lam ^ 1 := (pow_one _).symm
    _ ≤ lam ^ (r - b.val) := pow_le_pow_right₀ hlam (by omega)

theorem wt_step (lam : ℝ) (hlam : 1 ≤ lam) (b c : Fin r) (hbc : b < c) : lam * wt r lam c ≤ wt r lam b := by
  unfold wt
  have := b.isLt
  have := c.isLt
  have h : b.val < c.val := hbc
  rw [← pow_succ']
  exact pow_le_pow_right₀ hlam (by omega)

def Cmat (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℂ) := {M | ∀ i j, ‖(M - 1) i j‖ ≤ 1}

theorem isCompact_Cmat (n : ℕ) : IsCompact (Cmat n) := by
  have : Cmat n = Set.pi Set.univ (fun i : Fin n =>
      Set.pi Set.univ (fun j : Fin n => Metric.closedBall ((1 : Matrix (Fin n) (Fin n) ℂ) i j) 1)) := by
    ext M
    show (∀ i j, ‖(M - 1) i j‖ ≤ 1) ↔ _
    exact ⟨fun h i _ j _ => by simpa [Metric.mem_closedBall, dist_eq_norm, Matrix.sub_apply] using h i j,
      fun h i j => by
        have := h i (Set.mem_univ _) j (Set.mem_univ _)
        simpa [Metric.mem_closedBall, dist_eq_norm, Matrix.sub_apply] using this⟩
  rw [this]
  exact isCompact_univ_pi fun i => isCompact_univ_pi fun j => isCompact_closedBall _ _

def aUJ (hG : Gram ε e f) (s : Fin r → ℝ) (hs : ∀ b, s b ≠ 0) : Formalism.REAL.UJ ε :=
  ⟨⟨Amat ε e f s, Amat ε e f s⁻¹, Amat_mul_inv hG s hs, Amat_inv_mul hG s hs⟩, inUJ_A hG s hs⟩

theorem local_contract (hG : Gram ε e f) {z : Fin n → ℂ} (g : Formalism.REAL.UJ ε)
    (hgN : InN ε e z (Formalism.MainNotions.S.uMat g)) (hg'N : InN ε e z (Formalism.MainNotions.S.uMat g⁻¹)) :
    ∃ s : Fin r → ℝ, ∃ hs : ∀ b, s b ≠ 0, Formalism.MainNotions.S.uMat (aUJ hG s hs * g * (aUJ hG s hs)⁻¹) ∈ Cmat n := by
  have hSb0 : ∀ y i, 0 ≤ Sb ε e f (Formalism.MainNotions.S.uMat g) y i := fun y i => by unfold Sb; positivity
  set S : ℝ := ∑ i, ∑ j, Sb ε e f (Formalism.MainNotions.S.uMat g) (Pi.single j 1) i with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hSb0 _ _
  set lam : ℝ := 1 + S with hlamdef
  have hlam : 1 ≤ lam := by linarith
  set t := wt r lam with htdef
  have ht0 : ∀ b, 0 < t b := fun b => lt_of_lt_of_le one_pos (hlam.trans (wt_ge lam hlam b))
  have hs : ∀ b, t⁻¹ b ≠ 0 := fun b => by simp [(ht0 b).ne']
  refine ⟨t⁻¹, hs, fun i j => ?_⟩
  have hmat : Formalism.MainNotions.S.uMat (aUJ hG t⁻¹ hs * g * (aUJ hG t⁻¹ hs)⁻¹) =
      Amat ε e f t⁻¹ * Formalism.MainNotions.S.uMat g * Amat ε e f t⁻¹⁻¹ := rfl
  have hentry : ∀ K : Matrix (Fin n) (Fin n) ℂ, K i j = (K *ᵥ Pi.single j 1) i := fun K => by
    simp [mulVec, dotProduct, Pi.single_apply]
  rw [hmat, hentry (Amat ε e f t⁻¹ * Formalism.MainNotions.S.uMat g * Amat ε e f t⁻¹⁻¹ - 1), conj_sub_mulVec hG t⁻¹ hs,
    inv_inv]
  have hgg : Formalism.MainNotions.S.uMat g * Formalism.MainNotions.S.uMat g⁻¹ = 1 := PI.ScMuExists.UnitaryGroupMassFormula.uMat_mul_inv g
  refine (entry_bound hG t lam hlam (wt_ge lam hlam) (wt_step lam hlam) (PI.ScMuExists.UnitaryGroupMassFormula.uMat_inUJ g) hgg
    hgN hg'N _ i).trans ?_
  have h1 : Sb ε e f (Formalism.MainNotions.S.uMat g) (Pi.single j 1) i ≤
      ∑ j', Sb ε e f (Formalism.MainNotions.S.uMat g) (Pi.single j' 1) i :=
    Finset.single_le_sum (f := fun j' => Sb ε e f (Formalism.MainNotions.S.uMat g) (Pi.single j' 1) i)
      (fun j' _ => hSb0 _ _) (Finset.mem_univ j)
  have h2 : ∑ j', Sb ε e f (Formalism.MainNotions.S.uMat g) (Pi.single j' 1) i ≤ S :=
    Finset.single_le_sum (f := fun i => ∑ j', Sb ε e f (Formalism.MainNotions.S.uMat g) (Pi.single j' 1) i)
      (fun i _ => Finset.sum_nonneg fun _ _ => hSb0 _ _) (Finset.mem_univ i)
  rw [inv_mul_le_iff₀ (by linarith)]
  linarith

theorem measure_contraction_formula : Contract := by
  intro I r e f z hF
  refine ⟨Set.pi Set.univ (fun v => {g : Formalism.REAL.UJ (I.ε v) | Formalism.MainNotions.S.uMat g ∈ Cmat I.n}),
    isCompact_univ_pi fun v => (Formalism.REAL.isClosedEmbeddingMatrix I.n (I.ε v)).1.isCompact_preimage (isCompact_Cmat I.n), ?_⟩
  intro m hm
  have hfr := fun v => PI.ScMuExists.UnitaryGroupMassFormula.rv_frame (I := I) hF v
  have hG : ∀ v, Gram (I.ε v) (fun a => rv I v (e a)) (fun a => rv I v (f a)) := fun v =>
    ⟨(hfr v).1, (hfr v).2.1, (hfr v).2.2.1⟩
  have hez : ∀ v a, hJ (I.ε v) (rv I v (e a)) (rv I v z) = 0 := fun v a => ((hfr v).2.2.2.1 a).1
  have hfz : ∀ v a, hJ (I.ε v) (rv I v (f a)) (rv I v z) = 0 := fun v a => ((hfr v).2.2.2.1 a).2
  have hm' : m⁻¹ ∈ Ninf I e z := (PI.ScMuExists.UnitaryGroupMassFormula.NSub I e z).inv_mem hm
  choose s hs hC using fun v => local_contract (hG v) (m v) (hm v) (hm' v)
  refine ⟨fun v => aUJ (hG v) (s v) (hs v), fun x hx v => ?_, fun x hx v => ?_, fun v _ => hC v⟩
  · show InN _ _ _ (Amat _ _ _ (s v) * Formalism.MainNotions.S.uMat (x v) * Amat _ _ _ (s v)⁻¹)
    exact inN_A_conj (hG v) (s v) (hs v) (hez v) (hfz v) (hx v)
  · have hs' : ∀ b, (s v)⁻¹ b ≠ 0 := fun b => by simp [hs v b]
    have := inN_A_conj (hG v) (s v)⁻¹ hs' (hez v) (hfz v) (hx v)
    rw [inv_inv] at this
    show InN _ _ _ (Amat _ _ _ (s v)⁻¹ * Formalism.MainNotions.S.uMat (x v) * Amat _ _ _ (s v))
    exact this

end Inst

end PI.NMeasInv.UnitaryGroupMassFormula
end
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.NMeasInv

section

@[expose] public section

namespace PI

theorem n_measure_invariant : PI.NMeasInv.Target :=
  PI.NMeasInv.UnitaryGroupMassFormula.nMeasInv_of PI.NMeasInv.UnitaryGroupMassFormula.measure_contraction_formula

end PI
end
end
