module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.HermitianMeasures.OrbitIntegralAbsConvergent
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.HermitianMeasures.E0EqSingleNhFst
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.HermitianMeasures.NHeisInt

section

@[expose] public section

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A

theorem heis_norm_sq_le (m : ℕ) (x : (Fin m → ℂ) × ℝ) :
    ‖x‖ ^ 2 ≤ ∑ i, Complex.normSq (x.1 i) + x.2 ^ 2 := by
  have hS : 0 ≤ ∑ i, Complex.normSq (x.1 i) :=
    Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  have hT : 0 ≤ ∑ i, Complex.normSq (x.1 i) + x.2 ^ 2 := by positivity
  have h1 : ‖x.1‖ ≤ Real.sqrt (∑ i, Complex.normSq (x.1 i) + x.2 ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 (fun i => ?_)
    calc ‖x.1 i‖ = Real.sqrt (‖x.1 i‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (∑ i, Complex.normSq (x.1 i) + x.2 ^ 2) := by
        apply Real.sqrt_le_sqrt
        have hi : Complex.normSq (x.1 i) ≤ ∑ j, Complex.normSq (x.1 j) :=
          Finset.single_le_sum (f := fun j => Complex.normSq (x.1 j))
            (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
        rw [← Complex.normSq_eq_norm_sq]
        nlinarith [sq_nonneg x.2]
  have h2 : ‖x.2‖ ≤ Real.sqrt (∑ i, Complex.normSq (x.1 i) + x.2 ^ 2) := by
    calc ‖x.2‖ = Real.sqrt (x.2 ^ 2) := by rw [Real.sqrt_sq_eq_abs, Real.norm_eq_abs]
      _ ≤ _ := Real.sqrt_le_sqrt (by linarith)
  have h3 : ‖x‖ ≤ Real.sqrt (∑ i, Complex.normSq (x.1 i) + x.2 ^ 2) := by
    rw [Prod.norm_def]; exact max_le h1 h2
  calc ‖x‖ ^ 2 ≤ (Real.sqrt (∑ i, Complex.normSq (x.1 i) + x.2 ^ 2)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h3 2
    _ = _ := Real.sq_sqrt hT

theorem heis_pointwise (m : ℕ) {d : ℝ} (hd : 0 ≤ d) (x : (Fin m → ℂ) × ℝ) :
    (1 + ∑ i, Complex.normSq (x.1 i) + x.2 ^ 2) ^ (-(d / 2)) ≤
      (2 : ℝ) ^ (d / 2) * (1 + ‖x‖) ^ (-d) := by
  have hn := heis_norm_sq_le m x
  have hS : 0 ≤ ∑ i, Complex.normSq (x.1 i) :=
    Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  set Q := 1 + ∑ i, Complex.normSq (x.1 i) + x.2 ^ 2 with hQ
  have hQ0 : 0 < Q := by nlinarith [sq_nonneg x.2]
  have ha0 : 0 < 1 + ‖x‖ := by have := norm_nonneg x; linarith
  have hsq : (1 + ‖x‖) ^ 2 ≤ 2 * Q := by nlinarith [sq_nonneg (‖x‖ - 1), norm_nonneg x]
  have had : (1 + ‖x‖) ^ d ≤ (2 : ℝ) ^ (d / 2) * Q ^ (d / 2) := by
    have h1 : (1 + ‖x‖) ^ d = ((1 + ‖x‖) ^ (2 : ℝ)) ^ (d / 2) := by
      rw [← Real.rpow_mul ha0.le]; congr 1; ring
    rw [h1, ← Real.mul_rpow (by norm_num) hQ0.le]
    apply Real.rpow_le_rpow (by positivity) _ (by linarith)
    rw [Real.rpow_two]; exact hsq
  have hQd : 0 < Q ^ (d / 2) := Real.rpow_pos_of_pos hQ0 _
  have had0 : 0 < (1 + ‖x‖) ^ d := Real.rpow_pos_of_pos ha0 _
  rw [Real.rpow_neg hQ0.le, Real.rpow_neg ha0.le, ← div_eq_mul_inv, le_div_iff₀ had0]
  calc (Q ^ (d / 2))⁻¹ * (1 + ‖x‖) ^ d ≤ (Q ^ (d / 2))⁻¹ * ((2 : ℝ) ^ (d / 2) * Q ^ (d / 2)) := by
        gcongr
    _ = (2 : ℝ) ^ (d / 2) := by
        rw [mul_comm ((2 : ℝ) ^ (d / 2)), ← mul_assoc, inv_mul_cancel₀ hQd.ne', one_mul]

theorem heis_lint_fin (m : ℕ) {d : ℝ} (hd : (2 * m + 1 : ℝ) < d) :
    ∫⁻ x : (Fin m → ℂ) × ℝ, ENNReal.ofReal ((1 + ∑ i, Complex.normSq (x.1 i) + x.2 ^ 2) ^ (-(d / 2))) < ∞ := by
  have hd0 : 0 ≤ d := by have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith
  have hfin : ∫⁻ x : (Fin m → ℂ) × ℝ, ENNReal.ofReal ((1 + ‖x‖) ^ (-d)) < ⊤ := by
    haveI hC : (volume : Measure ℂ).IsAddHaarMeasure := by
      first
        | infer_instance
        | exact Complex.isAddHaarMeasure_volume
    haveI hP : (volume : Measure (Fin m → ℂ)).IsAddHaarMeasure := by
      first
        | infer_instance
        | exact MeasureTheory.Measure.pi.isAddHaarMeasure _
    haveI hV : (volume : Measure ((Fin m → ℂ) × ℝ)).IsAddHaarMeasure := by
      first
        | infer_instance
        | exact MeasureTheory.Measure.prod.instIsAddHaarMeasure _ _
        | (show ((volume : Measure (Fin m → ℂ)).prod (volume : Measure ℝ)).IsAddHaarMeasure
           infer_instance)
    apply finite_integral_one_add_norm
    simp only [Module.finrank_prod, Module.finrank_pi_fintype, Complex.finrank_real_complex,
      Module.finrank_self, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    push_cast
    linarith
  refine lt_of_le_of_lt (lintegral_mono (g := fun x : (Fin m → ℂ) × ℝ =>
    ENNReal.ofReal ((2 : ℝ) ^ (d / 2)) * ENNReal.ofReal ((1 + ‖x‖) ^ (-d))) fun x => ?_) ?_
  · dsimp only
    rw [← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (heis_pointwise m hd0 x)
  · rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

end ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.HermitianMeasures.NIntStep

section

@[expose] public section

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

def NIntAt (k r : ℕ) : Prop :=
  ∀ μN : Measure (Mt k r), Formalism.FourierDecayAlt.B.IsHaarOn (Nset k r) μN → ∀ b : ℝ, (dimN k r : ℝ) < b →
    ∫⁻ x, ENNReal.ofReal (gN (Matrix.of x) ^ (-b)) ∂μN < ∞

theorem dimN_succ (k r' : ℕ) :
    (dimN k (1 + r') : ℝ) = (dimN k r' : ℝ) + (2 * ((2 * r' + k + 1 : ℕ) : ℝ) + 1) := by
  unfold dimN
  push_cast
  ring

section NIntStepAux

theorem ns_gN_cont_mt {k r : ℕ} : Continuous (fun g : Mt k r => gN (Matrix.of g : Mat k r)) := by
  unfold gN; fun_prop

theorem ns_meas_F {k r : ℕ} (b : ℝ) :
    Measurable (fun x : Mt k r => ENNReal.ofReal (gN (Matrix.of x : Mat k r) ^ (-b))) :=
  ((ns_gN_cont_mt.measurable).pow_const _).ennreal_ofReal

theorem ns_cont_mulM {k r : ℕ} : Continuous (mulM (k := k) (r := r)) := by
  unfold mulM
  exact (continuous_fst (X := Mt k r) (Y := Mt k r)).matrix_mul continuous_snd

theorem ns_cont_levM (k r' : ℕ) : Continuous (levM k r') := by
  refine continuous_pi fun p => continuous_pi fun q => ?_
  show Continuous fun x : Mt k r' => ιLev k 1 r' (Matrix.of x) p q
  unfold ιLev
  split_ifs
  · exact (continuous_apply _).comp (continuous_apply _)
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const

theorem ns_meas_heis0 (k r' : ℕ) :
    @Measurable (HPar k r') (Mt k (1 + r')) _ _ (fun x => heis0 k r' x) := by
  have h : @Continuous (HPar k r') (Mt k (1 + r')) _ _ (fun x => heis0 k r' x) := continuous_heis0 k r'
  exact h.measurable

theorem ns_meas_G (k r' : ℕ) (d : ℝ) :
    Measurable (fun x : HPar k r' => ENNReal.ofReal ((1 + ∑ i, Complex.normSq (x.1 i) + x.2 ^ 2) ^ (-(d / 2)))) := by
  have h : Continuous (fun x : HPar k r' => 1 + ∑ i, Complex.normSq (x.1 i) + x.2 ^ 2) :=
    (continuous_const.add (continuous_finsetSum _ fun i _ =>
      Complex.continuous_normSq.comp ((continuous_apply i).comp continuous_fst))).add (continuous_snd.pow 2)
  exact (h.measurable.pow_const _).ennreal_ofReal

theorem ns_sigmaFinite {k r : ℕ} {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) :
    SigmaFinite μ := by
  have : IsFiniteMeasureOnCompacts μ := ⟨h.finite_compact⟩
  infer_instance

theorem ns_sq_rpow {t : ℝ} (ht : 0 ≤ t) (z : ℝ) : (t ^ 2) ^ z = t ^ (2 * z) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht]
  norm_num

theorem ns_split {a g S t b d : ℝ} (ha : 1 ≤ a) (hg : 0 ≤ g) (hS : 0 ≤ S) (ht : 0 ≤ t)
    (hle : a ^ 2 + S + t ≤ g ^ 2) (hd : 0 ≤ d) (hdb : d ≤ b) :
    g ^ (-b) ≤ (1 + S + t) ^ (-(d / 2)) * a ^ (-(b - d)) := by
  have ha0 : 0 ≤ a := by linarith
  have h1 : 1 + S + t ≤ g ^ 2 := by nlinarith
  have h2 : a ^ 2 ≤ g ^ 2 := by linarith
  have hp : 0 < 1 + S + t := by linarith
  have hp2 : 0 < a ^ 2 := by positivity
  have hg2 : 0 < g ^ 2 := lt_of_lt_of_le hp h1
  have e1 : g ^ (-b) = (g ^ 2) ^ (-(d / 2)) * (g ^ 2) ^ (-((b - d) / 2)) := by
    rw [← Real.rpow_add hg2, ns_sq_rpow hg]
    congr 1; ring
  have e2 : a ^ (-(b - d)) = (a ^ 2) ^ (-((b - d) / 2)) := by
    rw [ns_sq_rpow ha0]; congr 1; ring
  rw [e1, e2]
  have i1 : (g ^ 2) ^ (-(d / 2)) ≤ (1 + S + t) ^ (-(d / 2)) :=
    Real.rpow_le_rpow_of_nonpos hp h1 (by linarith)
  have i2 : (g ^ 2) ^ (-((b - d) / 2)) ≤ (a ^ 2) ^ (-((b - d) / 2)) :=
    Real.rpow_le_rpow_of_nonpos hp2 h2 (by linarith)
  exact mul_le_mul i1 i2 (by positivity) (by positivity)

theorem ns_point (hGL : GNLower) (k r' : ℕ) {b d : ℝ} (hd : 0 ≤ d) (hdb : d ≤ b) (x : HPar k r')
    (n' : Mt k r') (hn : (Matrix.of n' : Mat k r') ∈ Nset k r') :
    ENNReal.ofReal (gN (Matrix.of (mulM ((heis0 k r' x : Mt k (1 + r')), levM k r' n')) : Mat k (1 + r')) ^ (-b)) ≤
      ENNReal.ofReal ((1 + ∑ i, Complex.normSq (x.1 i) + x.2 ^ 2) ^ (-(d / 2))) *
        ENNReal.ofReal (gN (Matrix.of n' : Mat k r') ^ (-(b - d))) := by
  have hS : 0 ≤ ∑ i, Complex.normSq (x.1 i) := Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  rw [← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hm : (Matrix.of (mulM ((heis0 k r' x : Mt k (1 + r')), levM k r' n')) : Mat k (1 + r')) =
      heis0 k r' x * ιLev k 1 r' (Matrix.of n') := rfl
  rw [hm]
  have key := gN_heis_lev k r' x (Matrix.of n')
  have ha := hGL k r' _ hn.1
  exact ns_split ha (Real.sqrt_nonneg _) hS (sq_nonneg _) (by linarith) hd hdb

end NIntStepAux

theorem nIntAt_step (hNR : NRecHaar) (hHU : HaarUnique) (hCN : ClosedN) (hHN : HaarNExists) (hGL : GNLower)
    (k r' : ℕ) (ih : NIntAt k r') : NIntAt k (1 + r') := by
  intro μN hμN b hb
  obtain ⟨μ', hμ'⟩ := hHN k r'
  have hν := hNR k r' μ' hμ'
  obtain ⟨c, hc⟩ := hHU k (1 + r') (Nset k (1 + r')) _ μN (hCN k (1 + r')) hν hμN.conc hμN.left
    hμN.finite_compact
  have hσ : SigmaFinite μ' := ns_sigmaFinite hμ'
  have hdim := dimN_succ k r'
  set m : ℝ := ((2 * r' + k + 1 : ℕ) : ℝ) with hm
  have hm0 : 0 ≤ m := Nat.cast_nonneg _
  set d : ℝ := ((2 * m + 1) + (b - dimN k r')) / 2 with hd
  have hd1 : 2 * m + 1 < d := by rw [hd]; linarith
  have hd2 : (dimN k r' : ℝ) < b - d := by rw [hd]; linarith
  have hd0 : 0 ≤ d := by linarith
  have hdb : d ≤ b := by
    have : (0 : ℝ) ≤ dimN k r' := Nat.cast_nonneg _
    linarith
  have hae : ∀ᵐ z ∂((volume : Measure (HPar k r')).prod μ'), (Matrix.of z.2 : Mat k r') ∈ Nset k r' := by
    have h0 : ∀ᵐ y ∂μ', (Matrix.of y : Mat k r') ∈ Nset k r' := by rw [ae_iff]; exact hμ'.conc
    exact Measure.quasiMeasurePreserving_snd.ae h0
  have hfin : ∫⁻ x : Mt k (1 + r'), ENNReal.ofReal (gN (Matrix.of x : Mat k (1 + r')) ^ (-b))
      ∂(((μHeis k r').prod (μ'.map (levM k r'))).map mulM) < ∞ := by
    rw [lintegral_map (ns_meas_F b) ns_cont_mulM.measurable, μHeis,
      Measure.map_prod_map (volume : Measure (HPar k r')) μ' (ns_meas_heis0 k r') (ns_cont_levM k r').measurable,
      lintegral_map (f := fun a : Mt k (1 + r') × Mt k (1 + r') => ENNReal.ofReal (gN (Matrix.of (mulM a) : Mat k (1 + r')) ^ (-b)))
        ((ns_meas_F b).comp ns_cont_mulM.measurable)
        ((ns_meas_heis0 k r').prodMap (ns_cont_levM k r').measurable)]
    calc _ ≤ ∫⁻ z : HPar k r' × Mt k r',
          ENNReal.ofReal ((1 + ∑ i, Complex.normSq (z.1.1 i) + z.1.2 ^ 2) ^ (-(d / 2))) *
            ENNReal.ofReal (gN (Matrix.of z.2 : Mat k r') ^ (-(b - d))) ∂((volume : Measure (HPar k r')).prod μ') := by
          refine lintegral_mono_ae ?_
          filter_upwards [hae] with z hz
          exact ns_point hGL k r' hd0 hdb z.1 z.2 hz
      _ = (∫⁻ x : HPar k r', ENNReal.ofReal ((1 + ∑ i, Complex.normSq (x.1 i) + x.2 ^ 2) ^ (-(d / 2)))) *
            ∫⁻ y, ENNReal.ofReal (gN (Matrix.of y : Mat k r') ^ (-(b - d))) ∂μ' :=
          lintegral_prod_mul (ns_meas_G k r' d).aemeasurable (ns_meas_F (b - d)).aemeasurable
      _ < ∞ := ENNReal.mul_lt_top (heis_lint_fin (2 * r' + k + 1) (by rw [hm] at hd1; exact_mod_cast hd1))
          (ih μ' hμ' (b - d) hd2)
  rw [hc, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top hfin

end ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A
end
end
end
