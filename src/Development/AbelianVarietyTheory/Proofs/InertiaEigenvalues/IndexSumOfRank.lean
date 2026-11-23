module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Formalism.SatakeDualWeyl.StatementG
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
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
import Mathlib.Tactic.Linter.HaveILetI
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
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertPlaceLatticeIndexSumBoundStatement
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Algebra.BigOperators.Field
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceLatticeIndexSumLeZetaSqSubOneStatement
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CountableIdealSummableAbsNormRpow

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinitePlaceSplitIdempotentOrInert

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.PlaceDichotomy

theorem split_or_inert_idem : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (f : Formalism.L2.Theta.AE D),
    IsFinIdem D v f → (∃ e, Formalism.L2.Theta.IsSplitIdem D e ∧ e + Formalism.L2.Theta.cA D e = f) ∨
      (∃ w : HeightOneSpectrum (𝓞 D.host.E), Formalism.UG.IsInertAt D.host.F D.host.E v w) := by
  intro D v f hf
  obtain ⟨ε, ⟨α, hεα, hα1, hα0⟩, rfl⟩ := hf
  haveI := v.isMaximal
  obtain ⟨⟨P, hPp, hPo⟩⟩ := v.asIdeal.nonempty_primesOver (S := 𝓞 D.host.E)
  let w : HeightOneSpectrum (𝓞 D.host.E) := ⟨P, hPp, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩
  have hw : w.under (𝓞 D.host.F) = v := HeightOneSpectrum.ext hPo.over.symm
  rcases GlobalTheory.LPositivity.split_or_inert D w with hs | hi
  · left
    rw [hw] at hs
    obtain ⟨τ, -⟩ := GlobalTheory.LFun.SplitChart.exists_splitPrime_eq (GlobalTheory.AdelicU.isCMExt_host D) hs hw
    refine ⟨GlobalTheory.EmbChart.idem τ, GlobalTheory.EmbChart.isSplitIdem_idem τ, ?_⟩
    have hα : α = GlobalTheory.AdelicU.singleFin v 1 := by
      refine FiniteAdeleRing.ext _ fun u => ?_
      change evalV D.host.F u α = evalV D.host.F u (GlobalTheory.AdelicU.singleFin v 1)
      by_cases e : u = v
      · subst e; rw [hα1, GlobalTheory.AdelicU.evalV_singleFin_self]
      · rw [hα0 u e, GlobalTheory.AdelicU.evalV_singleFin_ne e]
    rw [GlobalTheory.EmbChart.cA_idem, GlobalTheory.EmbChart.idem, ← LinearMap.map_add (f := _), add_sub_cancel, hεα, hα]
    rfl
  · right
    exact ⟨w, hw ▸ hi⟩

end GlobalTheory.PlaceDichotomy
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinitePlaceSplitIdempotentOrInertStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

theorem _root_.GlobalTheory.T.finite_place_split_idempotent_or_inert : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (f : Formalism.L2.Theta.AE D), IsFinIdem D v f → (∃ e, Formalism.L2.Theta.IsSplitIdem D e ∧ e + Formalism.L2.Theta.cA D e = f) ∨ (∃ w : HeightOneSpectrum (𝓞 D.host.E), Formalism.UG.IsInertAt D.host.F D.host.E v w) := by
  first | exact @GlobalTheory.PlaceDichotomy.split_or_inert_idem | exact GlobalTheory.PlaceDichotomy.split_or_inert_idem | (intros; apply GlobalTheory.PlaceDichotomy.split_or_inert_idem <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneSubSumLeProdOneSubRange

section

@[expose] public section

open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory

theorem one_sub_sum_le_prod_one_sub_range (x : ℕ → ℝ) (h0 : ∀ i, 0 ≤ x i) (h1 : ∀ i, x i ≤ 1)
    (r : ℕ) : 1 - ∑ i ∈ Finset.range r, x i ≤ ∏ i ∈ Finset.range r, (1 - x i) := by
  induction r with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.prod_range_succ]
    have hS : 0 ≤ ∑ i ∈ Finset.range n, x i := Finset.sum_nonneg (fun i _ => h0 i)
    have hx1 : 0 ≤ 1 - x n := by linarith [h1 n]
    have := mul_le_mul_of_nonneg_right ih hx1
    nlinarith [h0 n]

theorem sum_rpow_sub_le (q : ℝ) (r : ℕ) (σ : ℝ) (hq : 2 ≤ q) (hσ : (r : ℝ) + 5 / 2 ≤ σ) :
    ∑ i ∈ Finset.range r, q ^ ((i : ℝ) - σ) ≤ 2 / q ^ 3 := by
  have hq0 : 0 < q := by linarith
  have hterm : ∀ i : ℕ, q ^ ((i : ℝ) - σ) = q ^ i / q ^ σ := by
    intro i; rw [Real.rpow_sub hq0, Real.rpow_natCast]
  simp_rw [hterm]
  rw [← Finset.sum_div, geom_sum_eq (by linarith : q ≠ 1)]
  have hqs : 0 < q ^ σ := Real.rpow_pos_of_pos hq0 σ
  have hrs : q ^ r / q ^ σ ≤ 1 / q ^ 2 := by
    have h1 : q ^ r / q ^ σ = q ^ ((r : ℝ) - σ) := by rw [Real.rpow_sub hq0, Real.rpow_natCast]
    have h2 : q ^ ((r : ℝ) - σ) ≤ q ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have h3 : q ^ (-2 : ℝ) = 1 / q ^ 2 := by
      rw [Real.rpow_neg hq0.le]; norm_num
    rw [h1]; linarith
  have hq1 : 0 < q - 1 := by linarith
  have hpr : 0 < q ^ r := pow_pos hq0 r
  calc (q ^ r - 1) / (q - 1) / q ^ σ ≤ q ^ r / (q - 1) / q ^ σ := by
        gcongr; linarith
    _ = (q ^ r / q ^ σ) / (q - 1) := by ring
    _ ≤ (1 / q ^ 2) / (q - 1) := by gcongr
    _ ≤ 2 / q ^ 3 := by
        rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [pow_pos hq0 2, pow_pos hq0 3]

theorem lattice_zeta_sq_bound : ∀ (q : ℝ) (r : ℕ) (σ : ℝ), 2 ≤ q → (r : ℝ) + 5 / 2 ≤ σ →
    (∏ i ∈ Finset.range r, (1 - q ^ ((i : ℝ) - σ))⁻¹) ^ 2 - 1 < 1 ∧
    (∏ i ∈ Finset.range r, (1 - q ^ ((i : ℝ) - σ))⁻¹) ^ 2 - 1 ≤ 16 * q ^ (-(3 : ℝ)) := by
  intro q r σ hq hσ
  have hq0 : 0 < q := by linarith
  set x : ℕ → ℝ := fun i => q ^ ((i : ℝ) - σ) with hx
  have hS := sum_rpow_sub_le q r σ hq hσ
  have hq3 : 8 ≤ q ^ 3 := by nlinarith [sq_nonneg q, mul_le_mul hq hq (by norm_num) hq0.le]
  set w : ℝ := 1 / q ^ 3 with hw
  have hw0 : 0 < w := by positivity
  have hw8 : w ≤ 1 / 8 := by
    rw [hw]; exact one_div_le_one_div_of_le (by norm_num) hq3
  have h0 : ∀ i, 0 ≤ x i := fun i => (Real.rpow_pos_of_pos hq0 _).le

  have hD := one_sub_sum_le_prod_one_sub_range (fun i => min (x i) 1)
    (fun i => le_min (h0 i) zero_le_one) (fun i => min_le_right _ _) r
  have hmin : ∀ i ∈ Finset.range r, min (x i) 1 = x i := by
    intro i hi
    apply min_eq_left
    have : x i ≤ ∑ j ∈ Finset.range r, x j :=
      Finset.single_le_sum (fun j _ => h0 j) hi
    have : 2 / q ^ 3 ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    linarith
  rw [Finset.sum_congr rfl hmin, Finset.prod_congr rfl (fun i hi => by rw [hmin i hi])] at hD
  set D := ∏ i ∈ Finset.range r, (1 - x i) with hDdef
  have h2w : 2 / q ^ 3 = 2 * w := by rw [hw]; ring
  have hDlow : 1 - 2 * w ≤ D := by linarith
  have hDpos : 0 < D := by linarith
  have hP : ∏ i ∈ Finset.range r, (1 - q ^ ((i : ℝ) - σ))⁻¹ = D⁻¹ := by
    rw [Finset.prod_inv_distrib]
  have hrhs : 16 * q ^ (-(3 : ℝ)) = 16 * w := by
    rw [Real.rpow_neg hq0.le, hw]; norm_num
  rw [hP, hrhs]
  have ha : 0 < 1 - 2 * w := by linarith
  have hPle : D⁻¹ ≤ (1 - 2 * w)⁻¹ := inv_anti₀ ha hDlow
  have hP0 : 0 ≤ D⁻¹ := inv_nonneg.mpr hDpos.le
  have hsq : D⁻¹ ^ 2 ≤ ((1 - 2 * w)⁻¹) ^ 2 := pow_le_pow_left₀ hP0 hPle 2
  have hkey : ((1 - 2 * w)⁻¹) ^ 2 ≤ 1 + 16 * w := by
    rw [inv_pow, inv_le_iff_one_le_mul₀ (by positivity)]
    nlinarith [mul_pos hw0 hw0]
  have hkey2 : ((1 - 2 * w)⁻¹) ^ 2 < 2 := by
    rw [inv_pow, inv_lt_iff_one_lt_mul₀ (by positivity)]
    nlinarith [mul_pos hw0 hw0]
  constructor <;> linarith

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SummableAbsNormRpowHeightOneSpectrum

section

@[expose] public section

open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory

theorem summable_absNorm_rpow_heightOneSpectrum :
    ∀ (F : Type) [Field F] [NumberField F] (σ : ℝ), 1 < σ →
      Summable (fun v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) =>
        (Ideal.absNorm v.asIdeal : ℝ) ^ (-σ)) :=
  fun F _ _ σ hσ => ((GlobalTheory.countable_ideal_and_summable_absNorm_rpow F).2 σ hσ).2

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IndexSumOfRank

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.IndexCount

theorem rank_le (D : D7) (i : Fin D.R.m) : 2 * (Wc D i).rank + 5 ≤ (Vc D i).rank := by
  have hV : (Vc D i).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have hW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have := D.R.rank_add_five_le
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  omega

theorem two_le_absNorm {D : D7} (v : HeightOneSpectrum (𝓞 D.host.F)) : (2 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  have : 2 ≤ Ideal.absNorm v.asIdeal := by omega
  exact_mod_cast this

theorem indexSum_of_rank {D : D7} (W : HSp D) (n : ℕ) (hn : 2 * W.rank + 5 ≤ n) : IndexSum W n := by
  let q : HeightOneSpectrum (𝓞 D.host.F) → ℝ := fun v => (Ideal.absNorm v.asIdeal : ℝ)
  let z : HeightOneSpectrum (𝓞 D.host.F) → ℝ := fun v =>
    (∏ i ∈ Finset.range W.rank, (1 - q v ^ ((i : ℝ) - (n : ℝ) / 2))⁻¹) ^ 2 - 1
  have hq : ∀ v, 2 ≤ q v := fun v => two_le_absNorm v
  have hσ : (W.rank : ℝ) + 5 / 2 ≤ (n : ℝ) / 2 := by
    have : ((2 * W.rank + 5 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at this; linarith
  have hz : ∀ v, z v < 1 ∧ z v ≤ 16 * q v ^ (-(3 : ℝ)) := fun v => GlobalTheory.lattice_zeta_sq_bound (q v) W.rank ((n : ℝ) / 2) (hq v) hσ
  have h8 : ∀ v, 8 * q v ^ (-(4 : ℝ)) ≤ 8 * q v ^ (-(3 : ℝ)) ∧ 8 * q v ^ (-(4 : ℝ)) ≤ 1 / 2 := by
    intro v
    have h1 : (1 : ℝ) ≤ q v := le_trans (by norm_num) (hq v)
    have hle : q v ^ (-(4 : ℝ)) ≤ q v ^ (-(3 : ℝ)) := Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
    refine ⟨by linarith, ?_⟩
    have : q v ^ (-(4 : ℝ)) ≤ (2 : ℝ) ^ (-(4 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) (hq v) (by norm_num)
    have h2 : (2 : ℝ) ^ (-(4 : ℝ)) = 1 / 16 := by
      rw [Real.rpow_neg (by norm_num)]; norm_num
    rw [h2] at this; linarith
  refine ⟨fun v => max (z v) (8 * q v ^ (-(4 : ℝ))), ?_, ?_, ?_⟩
  · have hs : Summable fun v : HeightOneSpectrum (𝓞 D.host.F) => 16 * q v ^ (-(3 : ℝ)) :=
      (GlobalTheory.summable_absNorm_rpow_heightOneSpectrum D.host.F 3 (by norm_num)).mul_left 16
    refine Summable.of_nonneg_of_le (fun v => ?_) (fun v => ?_) hs
    · exact le_trans (by positivity) (le_max_right _ _)
    · refine max_le (hz v).2 ?_
      have h3 : 0 ≤ q v ^ (-(3 : ℝ)) := by positivity
      linarith [(h8 v).1]
  · intro v
    exact max_lt (hz v).1 (by linarith [(h8 v).2])
  · intro v f hf C hC hd
    rcases GlobalTheory.T.finite_place_split_idempotent_or_inert D v f hf with hs | hi
    · exact le_trans (GlobalTheory.T.split_place_lattice_index_sum_le_zeta_sq_sub_one D W n hn v f hf hs C hC hd) (le_max_left _ _)
    · exact le_trans (GlobalTheory.T.inertPlace_latticeIndex_sum_bound D W n hn v f hf hi C hC hd) (le_max_right _ _)

theorem indexSum_holds : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ i, IndexSum (Wc D i) (Vc D i).rank := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F _ _ i
  exact indexSum_of_rank (Wc D i) (Vc D i).rank (rank_le D i)

end GlobalTheory.IndexCount

end
end
end
