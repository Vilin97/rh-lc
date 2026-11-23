module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.FormalDegreeG2.FdDefs
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.Transported
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PmatIsHermitian
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.RaisingLoweringNormIdentities
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Residue
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdConst
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.FormalDegreeG2.ProdSubLtEqFactorial
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.RhoNSubNab
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.TraceMulSelfEqSumEigenvaluesSq
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.VolUFactProdMulLe
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.CategoryTheory.Countable
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdLowerA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdScale
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.JacobianLeExp
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PolarBasic
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.FormalDegreeG2.FdPointwise
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdStep
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiExistsStatement
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.FormalDegreeG2.FdUpper
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.FormalDegreeG2.ProdSubLtEqFactorial
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.IntegrableOfContinuousCompact
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.SumNormAdjointSqEqHsOp
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.VolUFactProdMulLe

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.FormalDegreeG2.FdConst

section

@[expose] public section

noncomputable section

open Finset Matrix MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.G2

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem fdc_ncProd (ε : Fin n → Bool) (f : Fin n → Fin n → ℝ) :
    ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b ∧ ¬ ε a = ε b), f a b =
      ∏ ab : PCoord ε, f ab.1.2 ab.1.1 := by
  have e1 : ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b ∧ ¬ ε a = ε b), f a b =
      ∏ x ∈ univ.filter (fun x : Fin n × Fin n => x.1 < x.2 ∧ ¬ ε x.1 = ε x.2), f x.1 x.2 := by
    rw [Finset.prod_filter, Fintype.prod_prod_type]
    simp_rw [Finset.prod_filter]
  rw [e1, ← Finset.prod_subtype (univ.filter (fun x : Fin n × Fin n => x.2 < x.1 ∧ ε x.1 ≠ ε x.2))
    (fun x => by simp) (fun x : Fin n × Fin n => f x.2 x.1)]
  apply Finset.prod_nbij' Prod.swap Prod.swap
  · rintro ⟨a, b⟩ h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.swap_prod_mk] at h ⊢
    exact ⟨h.1, fun e => h.2 e.symm⟩
  · rintro ⟨a, b⟩ h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.swap_prod_mk] at h ⊢
    exact ⟨h.1, fun e => h.2 e.symm⟩
  · intro x _; rfl
  · intro x _; rfl
  · intro x _; rfl

theorem fdc_vand_split (ε : Fin n → Bool) (μ : Fin n → ℝ) :
    Vand μ = (∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b ∧ ε a = ε b), (μ a - μ b)) *
      ∏ ab : PCoord ε, (μ ab.1.2 - μ ab.1.1) := by
  rw [← fdc_ncProd ε (fun a b => μ a - μ b), ← Finset.prod_mul_distrib]
  unfold Vand
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [← Finset.prod_filter_mul_prod_filter_not (univ.filter (fun b : Fin n => a < b)) (fun b => ε a = ε b),
    Finset.filter_filter, Finset.filter_filter]

theorem pi_weight_at_zero_eq (ε : Fin n → Bool) :
    PiW ε 0 = Real.pi ^ (pOf ε * qOf ε) / ∏ ab : PCoord ε, (((ab.1.1 : ℕ) : ℝ) - ((ab.1.2 : ℕ) : ℝ)) := by
  unfold PiW wab
  simp only [Pi.zero_apply, sub_zero, zero_add]
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, card_PCoord]

theorem fdc_ncpos (ε : Fin n → Bool) :
    0 < ∏ ab : PCoord ε, (((ab.1.1 : ℕ) : ℝ) - ((ab.1.2 : ℕ) : ℝ)) := by
  refine Finset.prod_pos fun ab _ => sub_pos.2 ?_
  exact_mod_cast ab.2.1

theorem fdc_tend1 (α k m : ℝ) (hm : 0 < m) :
    Tendsto (fun t : ℕ => (α + (t : ℝ) * m + k) / (α + (t : ℝ) * m)) atTop (𝓝 1) := by
  have h : Tendsto (fun t : ℕ => α + (t : ℝ) * m) atTop atTop :=
    tendsto_atTop_add_const_left _ α (tendsto_natCast_atTop_atTop.atTop_mul_const hm)
  have h2 : Tendsto (fun t : ℕ => k / (α + (t : ℝ) * m)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop h
  have h3 := (tendsto_const_nhds (x := (1 : ℝ))).add h2
  rw [add_zero] at h3
  refine h3.congr' ?_
  filter_upwards [h.eventually_gt_atTop 0] with t ht
  field_simp

theorem fdc_tend2 (α m : ℝ) (hm : 0 < m) :
    Tendsto (fun t : ℕ => (t : ℝ) / (α + (t : ℝ) * m)) atTop (𝓝 (1 / m)) := by
  have h : Tendsto (fun t : ℕ => α + (t : ℝ) * m) atTop atTop :=
    tendsto_atTop_add_const_left _ α (tendsto_natCast_atTop_atTop.atTop_mul_const hm)
  have h3 : Tendsto (fun t : ℕ => α / (t : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have h4 := (tendsto_const_nhds (x := (1 : ℝ))).div (h3.add_const m) (by rw [zero_add]; exact hm.ne')
  rw [zero_add] at h4
  refine h4.congr' ?_
  filter_upwards [h.eventually_gt_atTop 0, eventually_gt_atTop 0] with t ht ht0
  have : (0 : ℝ) < t := by exact_mod_cast ht0
  show (1:ℝ) / (α / (t:ℝ) + m) = (t:ℝ) / (α + (t:ℝ) * m)
  rw [div_add' _ _ _ this.ne', one_div_div, mul_comm m]

theorem formal_degree_constant_eq {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : IsHCParam lam) (d : ℕ → ℝ)
    (T : ∀ t : ℕ, KType ε (lowK ε (lamT lam t)))
    (h1 : ∀ t, d t / Vand (lamT lam t) = d 0 / Vand lam) (hd0 : 0 < d 0)
    (hup : Filter.limsup (fun t : ℕ => ENNReal.ofReal ((t : ℝ) ^ (pOf ε * qOf ε) *
      (Module.finrank ℂ (T t).V : ℝ) / d t)) Filter.atTop ≤ ENNReal.ofReal (cPQ ε * PiW ε 0))
    (hlow : ENNReal.ofReal (cPQ ε * PiW ε 0) ≤ Filter.liminf (fun t : ℕ => ENNReal.ofReal ((t : ℝ) ^ (pOf ε * qOf ε) *
      (Module.finrank ℂ (T t).V : ℝ) / d t)) Filter.atTop) :
    d 0 = dimVlam lam := by
  apply ReciprocityTheory.ChartRestriction.DS.formal_degree_constant_eq <;> assumption

end ReciprocityTheory.ChartRestriction.DS.G2
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.FormalDegreeG2.FdLower

section

@[expose] public section

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.G2

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem formal_degree_liminf_lower_bound {ε : Fin n → Bool} {lam : Fin n → ℝ} (T : ∀ t : ℕ, KType ε (lowK ε (lamT lam t)))
    (hlim : ∀ y : PCoord ε → ℂ, Filter.Tendsto (fun t : ℕ => ⟪(T t).w, fF ε (lamT lam t) (T t) (pmat ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y)) (T t).w⟫_ℂ) Filter.atTop
      (nhds ((Real.exp (-(Qf (0 : Fin n → ℝ) y / 2)) : ℝ) : ℂ))) :
    ENNReal.ofReal (PiW ε 0) ≤ Filter.liminf (fun t : ℕ => ENNReal.ofReal ((t : ℝ) ^ (pOf ε * qOf ε)) *
      ∫⁻ z : PCoord ε → ℂ, ENNReal.ofReal (‖⟪(T t).w, fF ε (lamT lam t) (T t) (pmat z) (T t).w⟫_ℂ‖ ^ 2 * Jac z))
      Filter.atTop := by
  have hscale : ∀ t : ℕ, 1 ≤ t → ENNReal.ofReal ((t : ℝ) ^ (pOf ε * qOf ε)) *
      ∫⁻ z : PCoord ε → ℂ, ENNReal.ofReal (‖⟪(T t).w, fF ε (lamT lam t) (T t) (pmat z) (T t).w⟫_ℂ‖ ^ 2 * Jac z) =
      ∫⁻ y : PCoord ε → ℂ, ENNReal.ofReal (‖⟪(T t).w, fF ε (lamT lam t) (T t)
        (pmat ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y)) (T t).w⟫_ℂ‖ ^ 2 * Jac ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y)) := by
    intro t ht
    have ht' : (0 : ℝ) < t := by exact_mod_cast ht
    have hs : 0 < (Real.sqrt t)⁻¹ := inv_pos.2 (Real.sqrt_pos.2 ht')
    rw [lintegral_pcoord_smul _ hs, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    have e : (t : ℝ) ^ (pOf ε * qOf ε) * ((Real.sqrt t)⁻¹) ^ (2 * (pOf ε * qOf ε)) = 1 := by
      rw [inv_pow, pow_mul (Real.sqrt _) 2, Real.sq_sqrt ht'.le, mul_inv_cancel₀ (pow_ne_zero _ ht'.ne')]
    rw [e, ENNReal.ofReal_one, one_mul]
  rw [Filter.liminf_congr (Filter.eventually_atTop.2 ⟨1, hscale⟩)]
  have hmeas : ∀ t : ℕ, Measurable (fun y : PCoord ε → ℂ => ENNReal.ofReal (‖⟪(T t).w, fF ε (lamT lam t) (T t)
        (pmat ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y)) (T t).w⟫_ℂ‖ ^ 2 * Jac ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y))) := by
    intro t
    refine ENNReal.measurable_ofReal.comp (Continuous.measurable ?_)
    exact ((continuous_norm.comp ((fdl_inner_continuous _ (T t) _ _).comp (continuous_const_smul _))).pow 2).mul
      ((jac_continuous ε).comp (continuous_const_smul _))
  refine le_trans ?_ (lintegral_liminf_le hmeas)
  rw [← fdl_gauss ε]
  refine lintegral_mono fun y => ?_
  have h1 : Filter.Tendsto (fun t : ℕ => ENNReal.ofReal (‖⟪(T t).w, fF ε (lamT lam t) (T t)
      (pmat ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y)) (T t).w⟫_ℂ‖ ^ 2)) Filter.atTop
      (nhds (ENNReal.ofReal (Real.exp (-Qf (0 : Fin n → ℝ) y)))) := by
    have h2 : Filter.Tendsto (fun t : ℕ => ENNReal.ofReal (‖⟪(T t).w, fF ε (lamT lam t) (T t)
        (pmat ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y)) (T t).w⟫_ℂ‖ ^ 2)) Filter.atTop
        (nhds (ENNReal.ofReal (‖((Real.exp (-(Qf (0 : Fin n → ℝ) y / 2)) : ℝ) : ℂ)‖ ^ 2))) :=
      ((ENNReal.continuous_ofReal.comp (continuous_norm.pow 2)).tendsto _).comp (hlim y)
    have e : ‖((Real.exp (-(Qf (0 : Fin n → ℝ) y / 2)) : ℝ) : ℂ)‖ ^ 2 = Real.exp (-Qf (0 : Fin n → ℝ) y) := by
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, sq, ← Real.exp_add]
      congr 1
      ring
    rw [e] at h2
    exact h2
  rw [← h1.liminf_eq]
  exact Filter.liminf_le_liminf (Filter.Eventually.of_forall fun t => ENNReal.ofReal_le_ofReal
    (le_mul_of_one_le_right (sq_nonneg _) (jac_ge_one _)))

end ReciprocityTheory.ChartRestriction.DS.G2
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.FormalDegreeG2.FdStep

section

@[expose] public section

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.G2

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem fdS_strictAnti {lam : Fin n → ℝ} (hlam : StrictAnti lam) {c : Fin n → ℕ} (hc : Antitone c) :
    StrictAnti (lam + fun i => (c i : ℝ)) := by
  intro i j hij
  have h1 := hlam hij
  have h2 : (c j : ℝ) ≤ c i := by exact_mod_cast hc hij.le
  simp only [Pi.add_apply]
  linarith

theorem fdS_hc {lam : Fin n → ℝ} (hlam : IsHCParam lam) {c : Fin n → ℕ} (hc : Antitone c) :
    IsHCParam (lam + fun i => (c i : ℝ)) := by
  apply ReciprocityTheory.ChartRestriction.DS.fdS_hc <;> assumption

theorem fdS_gap {ε : Fin n → Bool} {h : ℝ} {lam : Fin n → ℝ} (hlam : StrictAnti lam)
    (hgap : GapAtLeast ε lam h) {c : Fin n → ℕ} (hc : Antitone c) :
    GapAtLeast ε (lam + fun i => (c i : ℝ)) h := by
  apply ReciprocityTheory.ChartRestriction.DS.fdS_gap <;> assumption

theorem fdS_stepQ {ε : Fin n → Bool} {h : ℝ} (dfun : (Fin n → ℝ) → ℝ)
    (hstep : ∀ (μ : Fin n → ℝ) (s : Fin n), IsHCParam μ → GapAtLeast ε μ h → GapAtLeast ε (μ + Pi.single s 1) h →
      StrictAnti (μ + Pi.single s 1) → dfun (μ + Pi.single s 1) = dfun μ * ratioV μ s)
    {μ : Fin n → ℝ} (hμ : IsHCParam μ) (hg : GapAtLeast ε μ h) (s : Fin n)
    (hg' : GapAtLeast ε (μ + Pi.single s 1) h) (hs : StrictAnti (μ + Pi.single s 1)) :
    dfun (μ + Pi.single s 1) / Vand (μ + Pi.single s 1) = dfun μ / Vand μ := by
  have hμs : StrictAnti μ := hμ.1
  rw [hstep μ s hμ hg hg' hs, ratioV_eq_vand hμs s]
  have h1 := vand_pos hμs
  have h2 := vand_pos hs
  field_simp

theorem fdS_main {ε : Fin n → Bool} {h : ℝ} (dfun : (Fin n → ℝ) → ℝ)
    (hstep : ∀ (μ : Fin n → ℝ) (s : Fin n), IsHCParam μ → GapAtLeast ε μ h → GapAtLeast ε (μ + Pi.single s 1) h →
      StrictAnti (μ + Pi.single s 1) → dfun (μ + Pi.single s 1) = dfun μ * ratioV μ s)
    {lam : Fin n → ℝ} (hlam : IsHCParam lam) (hgap : GapAtLeast ε lam h) :
    ∀ (N : ℕ) (c : Fin n → ℕ), Antitone c → ∑ i, c i = N →
      dfun (lam + fun i => (c i : ℝ)) / Vand (lam + fun i => (c i : ℝ)) = dfun lam / Vand lam := by
  apply ReciprocityTheory.ChartRestriction.DS.fdS_main <;> assumption

theorem fd_step {ε : Fin n → Bool} {h : ℝ} (dfun : (Fin n → ℝ) → ℝ)
    (hstep : ∀ (μ : Fin n → ℝ) (s : Fin n), IsHCParam μ → GapAtLeast ε μ h →
      GapAtLeast ε (μ + Pi.single s 1) h → StrictAnti (μ + Pi.single s 1) → dfun (μ + Pi.single s 1) = dfun μ * ratioV μ s)
    {lam : Fin n → ℝ} (hlam : IsHCParam lam) (hgap : GapAtLeast ε lam h) (t : ℕ) :
    dfun (lamT lam t) / Vand (lamT lam t) = dfun lam / Vand lam := by
  apply ReciprocityTheory.ChartRestriction.DS.fd_step <;> assumption

end ReciprocityTheory.ChartRestriction.DS.G2
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.FormalDegreeG2.ThmFD

section

@[expose] public section

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.G2

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem thmFD (hB3 : Lap.Base.TangentPairingStatement) {ε : Fin n → Bool} {lam : Fin n → ℝ} {h : ℝ} (hp : 1 ≤ pOf ε)
    (hq : 1 ≤ qOf ε) (hlam : IsHCParam lam) (hgap : GapAtLeast ε lam h) (hh : thrS ε + 1 < h)
    (dfun : (Fin n → ℝ) → ℝ)
    (hstep : ∀ (μ : Fin n → ℝ) (s : Fin n), IsHCParam μ → GapAtLeast ε μ h →
      GapAtLeast ε (μ + Pi.single s 1) h → StrictAnti (μ + Pi.single s 1) → dfun (μ + Pi.single s 1) = dfun μ * ratioV μ s)
    (H : ℕ → Type) [∀ t, NormedAddCommGroup (H t)] [∀ t, InnerProductSpace ℂ (H t)] [∀ t, CompleteSpace (H t)]
    (σ : ∀ t : ℕ, Matrix (Fin n) (Fin n) ℂ → (H t →L[ℂ] H t)) (T : ∀ t : ℕ, KType ε (lowK ε (lamT lam t)))
    (j : ∀ t : ℕ, (T t).V →L[ℂ] H t)
    (hF : ∀ᶠ t in Filter.atTop, FData ε (lamT lam t) (σ t) (T t) (j t))
    (hsm : ∀ᶠ t in Filter.atTop, ∃ (H' : Type) (_ : NormedAddCommGroup H') (_ : InnerProductSpace ℂ H')
      (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')) (w' : H'), Lap.Base.IsHWSmooth ε σ' (lamT lam t) w' ∧
        ∀ z : PCoord ε → ℂ, ⟪w', σ' (NormedSpace.exp (pmat z)) w'⟫_ℂ =
          ⟪(T t).w, fF ε (lamT lam t) (T t) (pmat z) (T t).w⟫_ℂ)
    (hd : ∀ᶠ t in Filter.atTop, Formalism.MainNotions.S.IsFdeg (muCD ε) (σ t) (dfun (lamT lam t))) :
    dfun lam = dimVlam lam := by
  have hlam0 : lamT lam 0 = lam := by simp [lamT]
  have hanti : Antitone lam := hlam.1.antitone
  have hcP : 0 < cPQ ε := lt_of_lt_of_le (inv_pos.mpr (pow_pos Real.pi_pos _)) (inv_pi_pow_le_cPQ ε)
  have hpos : ∀ t, (0:ℝ) < Module.finrank ℂ (T t).V := fun t => by
    have : Nontrivial (T t).V := ⟨⟨(T t).w, 0, fun h => by
      have h2 := (T t).w_norm
      rw [h, norm_zero] at h2
      exact zero_ne_one h2⟩⟩
    exact_mod_cast Module.finrank_pos
  have h1 : ∀ t, dfun (lamT lam t) / Vand (lamT lam t) = dfun (lamT lam 0) / Vand lam := fun t => by
    rw [hlam0]; exact fd_step dfun hstep hlam hgap t
  have hd0 : 0 < dfun (lamT lam 0) := by
    obtain ⟨t, ht⟩ := hd.exists
    have hv1 : 0 < Vand (lamT lam t) := vand_pos (isHCParam_lamT hlam t).1
    have hv0 : 0 < Vand lam := vand_pos hlam.1
    have e : dfun (lamT lam 0) = Vand lam * (dfun (lamT lam t) / Vand (lamT lam t)) := by
      rw [h1 t]; field_simp
    rw [e]
    have := ht.1
    positivity
  have hup : Filter.limsup (fun t : ℕ => ENNReal.ofReal ((t : ℝ) ^ (pOf ε * qOf ε) *
      (Module.finrank ℂ (T t).V : ℝ) / dfun (lamT lam t))) Filter.atTop ≤ ENNReal.ofReal (cPQ ε * PiW ε 0) := by
    have hev : ∀ᶠ t : ℕ in Filter.atTop, ENNReal.ofReal ((t : ℝ) ^ (pOf ε * qOf ε) *
        (Module.finrank ℂ (T t).V : ℝ) / dfun (lamT lam t)) ≤ ENNReal.ofReal (cPQ ε) *
        (ENNReal.ofReal ((t : ℝ) ^ (pOf ε * qOf ε)) *
          ∫⁻ z : PCoord ε → ℂ, ENNReal.ofReal (Real.exp (-2 * Ph (lamT lam t) (pmat z)) * Jac z)) := by
      filter_upwards [hF, hd] with t hFt hdt
      have L6 := lemma6c hFt hdt
      have hdt0 := hdt.1
      have hD := hpos t
      have hA : 0 ≤ (t:ℝ) ^ (pOf ε * qOf ε) * (Module.finrank ℂ (T t).V : ℝ) := by positivity
      calc ENNReal.ofReal ((t : ℝ) ^ (pOf ε * qOf ε) * (Module.finrank ℂ (T t).V : ℝ) / dfun (lamT lam t))
          = ENNReal.ofReal ((t:ℝ) ^ (pOf ε * qOf ε) * (Module.finrank ℂ (T t).V : ℝ)) *
              ENNReal.ofReal (1 / dfun (lamT lam t)) := by
            rw [← ENNReal.ofReal_mul hA]; congr 1; ring
        _ ≤ ENNReal.ofReal ((t:ℝ) ^ (pOf ε * qOf ε) * (Module.finrank ℂ (T t).V : ℝ)) *
              (ENNReal.ofReal (cPQ ε / Module.finrank ℂ (T t).V) *
                ∫⁻ z : PCoord ε → ℂ, ENNReal.ofReal (Real.exp (-2 * Ph (lamT lam t) (pmat z)) * Jac z)) := by
            gcongr
        _ = _ := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul hA]
            have e2 : (t:ℝ) ^ (pOf ε * qOf ε) * (Module.finrank ℂ (T t).V : ℝ) *
                (cPQ ε / Module.finrank ℂ (T t).V) = cPQ ε * (t:ℝ) ^ (pOf ε * qOf ε) := by
              field_simp
            rw [e2, ENNReal.ofReal_mul hcP.le, mul_assoc]
    refine le_trans (Filter.limsup_le_limsup hev) ?_
    rw [ENNReal.limsup_const_mul_of_ne_top ENNReal.ofReal_ne_top, ENNReal.ofReal_mul hcP.le]
    gcongr
    exact formal_degree_limsup_upper_bound hanti
  have hlow : ENNReal.ofReal (cPQ ε * PiW ε 0) ≤ Filter.liminf (fun t : ℕ => ENNReal.ofReal ((t : ℝ) ^ (pOf ε * qOf ε) *
      (Module.finrank ℂ (T t).V : ℝ) / dfun (lamT lam t))) Filter.atTop := by
    have hL := formal_degree_liminf_lower_bound T (matrix_coefficient_pointwise_limit hB3 H σ T j hF hsm)
    have hev : ∀ᶠ t : ℕ in Filter.atTop, ENNReal.ofReal (cPQ ε) * (ENNReal.ofReal ((t : ℝ) ^ (pOf ε * qOf ε)) *
        ∫⁻ z : PCoord ε → ℂ, ENNReal.ofReal (‖⟪(T t).w, fF ε (lamT lam t) (T t) (pmat z) (T t).w⟫_ℂ‖ ^ 2 * Jac z)) ≤
        ENNReal.ofReal ((t : ℝ) ^ (pOf ε * qOf ε) * (Module.finrank ℂ (T t).V : ℝ) / dfun (lamT lam t)) := by
      filter_upwards [hF, hd] with t hFt hdt
      have F3 := lintegral_fF_coeff_sq_le_finrank_div_fdeg hFt hdt
      calc _ = ENNReal.ofReal ((t : ℝ) ^ (pOf ε * qOf ε)) * (ENNReal.ofReal (cPQ ε) *
            ∫⁻ z : PCoord ε → ℂ, ENNReal.ofReal (‖⟪(T t).w, fF ε (lamT lam t) (T t) (pmat z) (T t).w⟫_ℂ‖ ^ 2 * Jac z)) := by
            ring
        _ ≤ ENNReal.ofReal ((t : ℝ) ^ (pOf ε * qOf ε)) *
              ENNReal.ofReal ((Module.finrank ℂ (T t).V : ℝ) / dfun (lamT lam t)) := by gcongr
        _ = _ := by rw [← ENNReal.ofReal_mul (by positivity), mul_div_assoc]
    refine le_trans ?_ (Filter.liminf_le_liminf hev)
    rw [ENNReal.liminf_const_mul_of_ne_top ENNReal.ofReal_ne_top, ENNReal.ofReal_mul hcP.le]
    gcongr
  have := formal_degree_constant_eq hlam (fun t => dfun (lamT lam t)) T h1 hd0 hup hlow
  simpa only [hlam0] using this

end ReciprocityTheory.ChartRestriction.DS.G2
end
end
end
