module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.SzHypFD
public import Formalism.SharpRestriction.CuspSpanNormBounds.CntPartners
public import Formalism.HermitianCurvature.StatementSz
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CriticalThresholdLowerBound
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SumInvSqLeSub
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CfgTopFalseIff
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyFormalDegreeLowerBound
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.FirstVandermondeNodeLargeOfSmallThreshold

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace GlobalTheory.RowVand

open Formalism.FourierDecayAlt Finset

lemma prod_le_pow_of_le {s : Finset ℕ} {f : ℕ → ℝ} {B : ℝ} (h0 : ∀ i ∈ s, 0 ≤ f i)
    (h : ∀ i ∈ s, f i ≤ B) : ∏ i ∈ s, f i ≤ B ^ s.card := by
  calc ∏ i ∈ s, f i ≤ ∏ _i ∈ s, B := Finset.prod_le_prod₀ h0 h
    _ = B ^ s.card := Finset.prod_const B

lemma one_le_prod_of_le {s : Finset ℕ} {f : ℕ → ℝ} (h : ∀ i ∈ s, 1 ≤ f i) : 1 ≤ ∏ i ∈ s, f i := by
  calc (1 : ℝ) = ∏ _i ∈ s, (1 : ℝ) := (Finset.prod_const_one).symm
    _ ≤ ∏ i ∈ s, f i := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) h

lemma b_le (c : Sz.Cfg) (hc : c.Ok) : ∀ i j, 1 ≤ i → i ≤ j → j ≤ c.m → c.b i ≤ c.b j := by
  intro i j hi hij hj
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
    have := hc.hgap j (by omega) (by omega)
    linarith [ih (by omega)]

lemma one_le_b (c : Sz.Cfg) (hc : c.Ok) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ c.m) : 1 ≤ c.b j :=
  le_trans hc.hb1 (b_le c hc 1 j le_rfl h1 h2)

lemma v_bounds (c : Sz.Cfg) (hc : c.Ok) (i : ℕ) (h1 : 1 ≤ i) (h2 : i + 1 ≤ c.k) :
    0 ≤ c.v i ∧ c.v i ≤ c.v 1 := by
  have hi : (i : ℝ) + 1 ≤ c.k := by exact_mod_cast h2
  have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast h1
  have hD := hc.hDel
  have hv := hc.hv0
  unfold Sz.Cfg.v
  constructor
  · nlinarith
  · push_cast; nlinarith

lemma vlast_le (c : Sz.Cfg) (hc : c.Ok) : c.vlast ≤ c.v 1 := by
  have hk : (4 : ℝ) ≤ c.k := by exact_mod_cast hc.hk
  have hD := hc.hDel
  unfold Sz.Cfg.v
  push_cast
  nlinarith

lemma firstVandermondeNode_large_of_small_threshold (c : Sz.Cfg) (hc : c.Ok) (hs : c.vth ≤ 1 / 10) : 40 * c.m * c.k * c.Del ≤ c.b 1 := by
  have hb : 0 < c.b 1 := lt_of_lt_of_le one_pos hc.hb1
  unfold Sz.Cfg.vth at hs
  rw [div_le_iff₀ hb] at hs
  linarith

lemma vand_inner_le (c : Sz.Cfg) (hc : c.Ok) (hs : c.vth ≤ 1 / 10) (de : ℕ → ℝ) (hw : Sz.IsWord c.k de)
    (hpos : 0 ≤ Sz.Vand (c.k - 2) (fun i => c.u de (i + 1))) :
    Sz.Vand (c.k - 2) (fun i => c.u de (i + 1)) ≤ Sz.Vand c.k (c.u de) := by
  have hk := hc.hk
  have hkR : (4 : ℝ) ≤ c.k := by exact_mod_cast hk
  have hmR : (2 : ℝ) ≤ c.m := by exact_mod_cast hc.hm
  have hD := hc.hDel
  have hb1 := firstVandermondeNode_large_of_small_threshold c hc hs
  have hvl := vlast_le c hc
  have hv0 := hc.hv0
  have ha := hc.ha
  have hde : ∀ i, 0 ≤ de i ∧ de i ≤ 1 := fun i => by rcases hw.1 i with h | h <;> rw [h] <;> norm_num
  have e1 : Sz.Vand c.k (c.u de) =
      (∏ j ∈ Icc 2 c.k, (c.u de 1 - c.u de j)) * Sz.Vand (c.k - 1) (fun i => c.u de (i + 1)) := by
    have := Formalism.FourierDecayAlt.P.Sz4.vand_succ_bot (c.k - 1) (c.u de)
    rwa [Nat.sub_add_cancel (by omega)] at this
  have e2 : Sz.Vand (c.k - 1) (fun i => c.u de (i + 1)) =
      Sz.Vand (c.k - 2) (fun i => c.u de (i + 1)) * ∏ i ∈ Icc 1 (c.k - 2), (c.u de (i + 1) - c.u de c.k) := by
    have := Formalism.FourierDecayAlt.P.Sz4.vand_succ_top (c.k - 2) (fun i => c.u de (i + 1))
    rw [show c.k - 2 + 1 = c.k - 1 by omega] at this
    rw [this]
    congr 2
    ext i
    congr 2
    omega

  have hu1 : c.u de 1 = c.a := by unfold Sz.Cfg.u; simp
  have huk : c.u de c.k = c.ulast := by
    unfold Sz.Cfg.u; rw [if_neg (by omega), if_pos rfl]
  have F1 : ∀ j ∈ Icc 2 c.k, 1 ≤ c.u de 1 - c.u de j := by
    intro j hj
    rw [mem_Icc] at hj
    rw [hu1]
    by_cases hjk : j = c.k
    · rw [hjk, huk]
      unfold Sz.Cfg.ulast
      split_ifs with ht
      · have := (hc.htop ht).1
        have hb0 := hc.hb1
        nlinarith
      · nlinarith
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      rw [Formalism.FourierDecayAlt.P.Sz4.u_succ c de hw i (by omega) (by omega) (Or.inl (by omega))]
      have := (v_bounds c hc i (by omega) (by omega)).2
      have := hde i
      nlinarith

  have F2 : ∀ i ∈ Icc 1 (c.k - 2), 1 ≤ c.u de (i + 1) - c.u de c.k := by
    intro i hi
    rw [mem_Icc] at hi
    rw [Formalism.FourierDecayAlt.P.Sz4.u_succ c de hw i (by omega) (by omega) (Or.inl (by omega)), huk]
    have hvi := v_bounds c hc i (by omega) (by omega)
    have hdi := hde i
    unfold Sz.Cfg.ulast
    split_ifs with ht
    · have := (hc.htop ht).1
      have h8 : (8 : ℝ) ≤ c.m * c.k := by nlinarith
      have h9 : 8 * c.Del ≤ c.m * c.k * c.Del := mul_le_mul_of_nonneg_right h8 (by linarith)
      have h10 : de i * c.Del ≤ 1 * c.Del := mul_le_mul_of_nonneg_right hdi.2 (by linarith)
      linarith [hvi.1]
    · have hsub := Formalism.FourierDecayAlt.P.Sz4.v_sub c i (c.k - 1)
      have hvk : c.v (c.k - 1) = c.vlast := by
        unfold Sz.Cfg.v
        rw [Nat.cast_sub (by omega)]
        push_cast; ring
      have hik : (i : ℝ) + 2 ≤ ((c.k - 1 : ℕ) : ℝ) + 1 := by
        rw [Nat.cast_sub (by omega)]
        have : ((i + 2 : ℕ) : ℝ) ≤ c.k := by exact_mod_cast (by omega : i + 2 ≤ c.k)
        push_cast at this ⊢
        linarith
      rw [hvk] at hsub
      have h10 : de i * c.Del ≤ 1 * c.Del := mul_le_mul_of_nonneg_right hdi.2 (by linarith)
      have h11 : 4 * c.Del * 1 ≤ 4 * c.Del * (((c.k - 1 : ℕ) : ℝ) - i) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      linarith
  rw [e1, e2]
  have P1 := one_le_prod_of_le F1
  have P2 := one_le_prod_of_le F2
  calc Sz.Vand (c.k - 2) (fun i => c.u de (i + 1))
      = 1 * (Sz.Vand (c.k - 2) (fun i => c.u de (i + 1)) * 1) := by ring
    _ ≤ _ := by
      apply mul_le_mul P1 _ (by positivity) (by linarith)
      exact mul_le_mul le_rfl P2 zero_le_one hpos

lemma vand_lam_le_cfg (c : Sz.Cfg) (hc : c.Ok) (hs : c.vth ≤ 1 / 10) (hmk : c.m ≤ c.k) (L : ℝ) (hL : 1 ≤ L)
    (hbj : ∀ j, 1 ≤ j → j ≤ c.m → c.b j ≤ Real.exp (2 * L)) (de : ℕ → ℝ) (hw : Sz.IsWord c.k de) :
    Sz.Vand (c.k + c.m - 1) c.lam ≤ Real.exp (10 * c.k * c.m * L) * Sz.Vand c.k (c.u de) := by
  have hk := hc.hk
  have hm := hc.hm
  have hkR : (4 : ℝ) ≤ c.k := by exact_mod_cast hk
  have hmR : (2 : ℝ) ≤ c.m := by exact_mod_cast hm
  have hmkR : (c.m : ℝ) ≤ c.k := by exact_mod_cast hmk
  have hD := hc.hDel
  have hkD : 0 ≤ (c.k : ℝ) * c.Del := mul_nonneg (by linarith) (by linarith)
  have h4 : 4 * c.k * c.Del ≤ Real.exp (2 * L) := by
    have h1 := firstVandermondeNode_large_of_small_threshold c hc hs
    have h2 := hbj 1 le_rfl (by omega)
    have h3 : 2 * ((c.k : ℝ) * c.Del) ≤ c.m * (c.k * c.Del) := mul_le_mul_of_nonneg_right hmR hkD
    linarith
  obtain ⟨hV, hRel, hRlo, -, hVk⟩ := Formalism.FourierDecayAlt.P.vandermondeTop c de hc hw
  obtain ⟨hLam, -⟩ := Formalism.FourierDecayAlt.P.vandermonde_lambda_lower_bound c hc
  have hR : 0 < Sz.Rde (c.k - 2) de := lt_of_lt_of_le (Real.exp_pos _) hRlo
  have hU0 : 0 ≤ Sz.Vand (c.k - 2) (fun i => c.u de (i + 1)) := by
    rw [hRel]; exact (mul_pos hR hV).le
  have hU := vand_inner_le c hc hs de hw hU0
  have hU1 : 0 ≤ Sz.Vand c.k (c.u de) := le_trans hU0 hU

  have A1 : Sz.Vand (c.k - 2) c.v ≤ Real.exp (((c.k : ℝ) - 1) / 4) * Sz.Vand c.k (c.u de) := by
    have e : Real.exp (((c.k : ℝ) - 1) / 4) * Real.exp (-(((c.k : ℝ) - 1) / 4)) = 1 := by
      rw [← Real.exp_add]; simp
    calc Sz.Vand (c.k - 2) c.v
        = Real.exp (((c.k : ℝ) - 1) / 4) * (Real.exp (-(((c.k : ℝ) - 1) / 4)) * Sz.Vand (c.k - 2) c.v) := by
          rw [← mul_assoc, e, one_mul]
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_left (le_trans ?_ hU) (Real.exp_pos _).le
          rw [hRel]
          exact mul_le_mul_of_nonneg_right hRlo hV.le

  have hE : 1 ≤ Real.exp (2 * L) := Real.one_le_exp (by linarith)
  have A2 : (4 * c.Del) ^ (c.k - 2) * ((c.k - 2).factorial : ℝ) ≤ Real.exp (2 * L) ^ c.k := by
    have f1 : ((c.k - 2).factorial : ℝ) ≤ (c.k : ℝ) ^ (c.k - 2) := by
      have := le_trans (Nat.factorial_le_pow (c.k - 2)) (Nat.pow_le_pow_left (Nat.sub_le c.k 2) (c.k - 2))
      exact_mod_cast this
    calc (4 * c.Del) ^ (c.k - 2) * ((c.k - 2).factorial : ℝ)
        ≤ (4 * c.Del) ^ (c.k - 2) * (c.k : ℝ) ^ (c.k - 2) :=
          mul_le_mul_of_nonneg_left f1 (pow_nonneg (by linarith) _)
      _ = (4 * c.k * c.Del) ^ (c.k - 2) := by rw [← mul_pow]; congr 1; ring
      _ ≤ Real.exp (2 * L) ^ (c.k - 2) := pow_le_pow_left₀ (by linarith) h4 _
      _ ≤ Real.exp (2 * L) ^ c.k := pow_le_pow_right₀ hE (Nat.sub_le _ _)
  have A20 : 0 ≤ (4 * c.Del) ^ (c.k - 2) * ((c.k - 2).factorial : ℝ) :=
    mul_nonneg (pow_nonneg (by linarith) _) (Nat.cast_nonneg _)

  have h23 : 2 * Real.exp (2 * L) ≤ Real.exp (3 * L) := by
    have h1 : 2 ≤ Real.exp L := le_trans (by linarith) (Real.add_one_le_exp L)
    rw [show 3 * L = L + 2 * L by ring, Real.exp_add]
    exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
  have hf : ∀ i ∈ Icc 1 (c.k - 1), ∀ j ∈ Icc 1 c.m, 0 ≤ c.v i + c.b j ∧ c.v i + c.b j ≤ Real.exp (3 * L) := by
    intro i hi j hj
    rw [mem_Icc] at hi hj
    have h1 := v_bounds c hc i hi.1 (by omega)
    have h2 := one_le_b c hc j hj.1 hj.2
    have h3 := hbj j hj.1 hj.2
    have h5 := hc.hv1
    constructor <;> linarith [h1.1, h1.2]
  have A30 : ∀ i ∈ Icc 1 (c.k - 1), 0 ≤ ∏ j ∈ Icc 1 c.m, (c.v i + c.b j) :=
    fun i hi => Finset.prod_nonneg fun j hj => (hf i hi j hj).1
  have A3 : ∏ i ∈ Icc 1 (c.k - 1), ∏ j ∈ Icc 1 c.m, (c.v i + c.b j) ≤ (Real.exp (3 * L) ^ c.m) ^ c.k := by
    refine le_trans (prod_le_pow_of_le (B := Real.exp (3 * L) ^ c.m) A30 fun i hi => ?_) ?_
    · have := prod_le_pow_of_le (fun j hj => (hf i hi j hj).1) (fun j hj => (hf i hi j hj).2)
      simpa using this
    · exact pow_le_pow_right₀ (one_le_pow₀ (by linarith)) (by simp)

  have hg : ∀ i ∈ Icc 1 c.m, ∀ j ∈ Ioc i c.m, 0 ≤ -c.b i - -c.b j ∧ -c.b i - -c.b j ≤ Real.exp (2 * L) := by
    intro i hi j hj
    rw [mem_Icc] at hi
    rw [mem_Ioc] at hj
    have h1 := b_le c hc i j hi.1 hj.1.le hj.2
    have h2 := one_le_b c hc i hi.1 hi.2
    have h3 := hbj j (by omega) hj.2
    constructor <;> linarith
  have A40 : ∀ i ∈ Icc 1 c.m, 0 ≤ ∏ j ∈ Ioc i c.m, (-c.b i - -c.b j) :=
    fun i hi => Finset.prod_nonneg fun j hj => (hg i hi j hj).1
  have A4 : Sz.Vand c.m (fun j => -c.b j) ≤ (Real.exp (2 * L) ^ c.m) ^ c.k := by
    unfold Sz.Vand
    refine le_trans (prod_le_pow_of_le (B := Real.exp (2 * L) ^ c.m) A40 fun i hi => ?_) ?_
    · exact le_trans (prod_le_pow_of_le (fun j hj => (hg i hi j hj).1) (fun j hj => (hg i hi j hj).2))
        (pow_le_pow_right₀ hE (by simp))
    · exact pow_le_pow_right₀ (one_le_pow₀ hE) (by simpa using hmk)
  have A41 : 0 ≤ Sz.Vand c.m (fun j => -c.b j) := Finset.prod_nonneg A40

  have hexp : Real.exp (((c.k : ℝ) - 1) / 4) * Real.exp (2 * L) ^ c.k * (Real.exp (3 * L) ^ c.m) ^ c.k *
      (Real.exp (2 * L) ^ c.m) ^ c.k ≤ Real.exp (10 * c.k * c.m * L) := by
    simp only [← Real.exp_nat_mul, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have h1 : (c.k : ℝ) * 1 ≤ c.k * L := mul_le_mul_of_nonneg_left hL (by linarith)
    have h2 : (c.k : ℝ) * L * 2 ≤ c.k * L * c.m := mul_le_mul_of_nonneg_left hmR (by linarith)
    nlinarith
  rw [hLam, hVk]
  calc Sz.Vand (c.k - 2) c.v * (4 * c.Del) ^ (c.k - 2) * ((c.k - 2).factorial : ℝ) *
        (∏ i ∈ Icc 1 (c.k - 1), ∏ j ∈ Icc 1 c.m, (c.v i + c.b j)) * Sz.Vand c.m (fun j => -c.b j)
      = Sz.Vand (c.k - 2) c.v * ((4 * c.Del) ^ (c.k - 2) * ((c.k - 2).factorial : ℝ)) *
        (∏ i ∈ Icc 1 (c.k - 1), ∏ j ∈ Icc 1 c.m, (c.v i + c.b j)) * Sz.Vand c.m (fun j => -c.b j) := by ring
    _ ≤ (Real.exp (((c.k : ℝ) - 1) / 4) * Sz.Vand c.k (c.u de)) * Real.exp (2 * L) ^ c.k *
        (Real.exp (3 * L) ^ c.m) ^ c.k * (Real.exp (2 * L) ^ c.m) ^ c.k :=
      mul_le_mul (mul_le_mul (mul_le_mul A1 A2 A20 (by positivity)) A3 (Finset.prod_nonneg A30)
        (by positivity)) A4 A41 (by positivity)
    _ = (Real.exp (((c.k : ℝ) - 1) / 4) * Real.exp (2 * L) ^ c.k * (Real.exp (3 * L) ^ c.m) ^ c.k *
        (Real.exp (2 * L) ^ c.m) ^ c.k) * Sz.Vand c.k (c.u de) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hexp hU1

theorem vand_lamSH_le : ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ),
    Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → 40 ≤ Cl → ∀ u τ,
      vand (lamSH D.R (D.hc τ)) ≤ Real.exp (10 * D.R.k * D.R.m * large₂.sc.L) * vand (uS D u τ) := by
  intro D large₂ C' Cl Cg cb Cu cT CT C0 hH h40 u τ
  obtain ⟨hS, hD, -⟩ := hH
  have hok := BridgeLemma.cfg_ok hD hS τ
  have hsm := BridgeLemma.cfg_small hS h40 τ
  unfold StandingNumericalData at hD
  obtain ⟨-, -, -, -, d5, -⟩ := hD
  rw [← BridgeLemma.Vand_lam D τ, ← BridgeLemma.Vand_u D u τ (d5 u τ)]
  have hb : large₂.sc.b ^ 2 = Real.exp (2 * large₂.sc.L) := by
    rw [← BridgeLemma.log_b large₂, two_mul, Real.exp_add, Real.exp_log (by linarith [BridgeLemma.one_lt_b large₂]), sq]
  have hmk : D.R.m ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  exact vand_lam_le_cfg (BridgeLemma.cfgOf D τ) hok hsm.hvth hmk large₂.sc.L (BridgeLemma.one_le_L large₂)
    (fun j h1 h2 => hb ▸ hsm.hbj j h1 h2) _ (BridgeLemma.isWord_deOf D u)

end GlobalTheory.RowVand
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.CriticalLevelLePowAllPlaces

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace GlobalTheory.CritLevelUpper

theorem root_le (ka rd g Q b Cg m k : ℝ) (hb1 : 1 < b) (hm : 2 ≤ m) (hmk : 40 * m ^ 2 ≤ k)
    (hka0 : 0 < ka) (hki : ka⁻¹ ≤ b) (hrd1 : 1 ≤ rd) (hg0 : 0 ≤ g) (hgg : g ≤ b ^ (2 * Cg)) (hCg : 0 ≤ Cg)
    (hQ0 : 0 ≤ Q) (hQ : Q ≤ b ^ (10 * k * m)) :
    (ka ^ (-((m - 1) * k + m * (m - 1) / 2)) * rd ^ (-((m - 1) / 2)) * g ^ (k * m + m * (m - 1) / 2) * Q) ^
      ((1 : ℝ) / k) ≤ b ^ ((4 * Cg + 12) * m) := by
  have hb0 : 0 < b := by linarith
  have hk0 : 0 < k := by nlinarith
  have hkm : 0 ≤ k * m := by positivity
  have hE1a : 0 ≤ (m - 1) * k + m * (m - 1) / 2 := by nlinarith
  have hE1b : (m - 1) * k + m * (m - 1) / 2 ≤ 3 / 2 * (k * m) := by nlinarith
  have hE3a : 0 ≤ k * m + m * (m - 1) / 2 := by nlinarith
  have hE3b : k * m + m * (m - 1) / 2 ≤ 3 / 2 * (k * m) := by nlinarith
  have hP1 : ka ^ (-((m - 1) * k + m * (m - 1) / 2)) ≤ b ^ (3 / 2 * (k * m)) := by
    rw [Real.rpow_neg hka0.le, ← Real.inv_rpow hka0.le]
    calc ka⁻¹ ^ ((m - 1) * k + m * (m - 1) / 2) ≤ b ^ ((m - 1) * k + m * (m - 1) / 2) :=
          Real.rpow_le_rpow (by positivity) hki hE1a
      _ ≤ b ^ (3 / 2 * (k * m)) := Real.rpow_le_rpow_of_exponent_le hb1.le hE1b
  have hP10 : 0 ≤ ka ^ (-((m - 1) * k + m * (m - 1) / 2)) := Real.rpow_nonneg hka0.le _
  have hP2 : rd ^ (-((m - 1) / 2)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hrd1 (by linarith)
  have hP20 : 0 ≤ rd ^ (-((m - 1) / 2)) := Real.rpow_nonneg (by linarith) _
  have hP3 : g ^ (k * m + m * (m - 1) / 2) ≤ b ^ (3 * Cg * (k * m)) := by
    calc g ^ (k * m + m * (m - 1) / 2) ≤ (b ^ (2 * Cg)) ^ (k * m + m * (m - 1) / 2) :=
          Real.rpow_le_rpow hg0 hgg hE3a
      _ = b ^ (2 * Cg * (k * m + m * (m - 1) / 2)) := (Real.rpow_mul hb0.le _ _).symm
      _ ≤ b ^ (3 * Cg * (k * m)) := by
        apply Real.rpow_le_rpow_of_exponent_le hb1.le
        nlinarith
  have hP30 : 0 ≤ g ^ (k * m + m * (m - 1) / 2) := Real.rpow_nonneg hg0 _
  have hX0 : 0 ≤ ka ^ (-((m - 1) * k + m * (m - 1) / 2)) * rd ^ (-((m - 1) / 2)) *
      g ^ (k * m + m * (m - 1) / 2) * Q := by positivity
  have hXb : ka ^ (-((m - 1) * k + m * (m - 1) / 2)) * rd ^ (-((m - 1) / 2)) *
      g ^ (k * m + m * (m - 1) / 2) * Q ≤ b ^ (k * ((4 * Cg + 12) * m)) := by
    calc ka ^ (-((m - 1) * k + m * (m - 1) / 2)) * rd ^ (-((m - 1) / 2)) * g ^ (k * m + m * (m - 1) / 2) * Q
        ≤ b ^ (3 / 2 * (k * m)) * 1 * b ^ (3 * Cg * (k * m)) * b ^ (10 * k * m) := by
          gcongr
      _ = b ^ (3 / 2 * (k * m) + 3 * Cg * (k * m) + 10 * k * m) := by
          rw [Real.rpow_add hb0, Real.rpow_add hb0]; ring
      _ ≤ b ^ (k * ((4 * Cg + 12) * m)) := by
          apply Real.rpow_le_rpow_of_exponent_le hb1.le
          nlinarith
  calc _ ≤ (b ^ (k * ((4 * Cg + 12) * m))) ^ ((1 : ℝ) / k) :=
        Real.rpow_le_rpow hX0 hXb (by positivity)
    _ = b ^ ((4 * Cg + 12) * m) := by
        rw [← Real.rpow_mul hb0.le]
        congr 1
        field_simp

theorem tcrit_le_pow : Formalism.L2.SG.Pf.SzHypFD.DsigHC → ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ), Ties D → Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → 40 ≤ Cl → ∀ u τ, Tcrit D u τ ≤ large₂.sc.b ^ ((4 * Cg + 12) * (D.R.m : ℝ)) := by
  intro hDs D large₂ C' Cl Cg cb Cu cT CT C0 hT h h40 u τ
  haveI : Fact Formalism.L2.SG.Pf.SzHypFD.DsigHC := ⟨hDs⟩
  have hH := h.1
  obtain ⟨_, _, _, _, _, _, hm2L, _, _, _, hlogrd, hkg1, hg1, _, hg2, -⟩ := hH
  have hL : 1 ≤ large₂.sc.L := Formalism.MainNotions.BridgeLemma.one_le_L large₂
  have hbexp : large₂.sc.b = Real.exp large₂.sc.L := rfl
  have hb1 : 1 < large₂.sc.b := by
    rw [hbexp]; exact lt_of_lt_of_le (by linarith) (Real.add_one_le_exp large₂.sc.L)
  have hb0 : 0 < large₂.sc.b := by linarith
  have hm : (2 : ℝ) ≤ (D.R.m : ℝ) := by have := D.R.two_le_m; exact_mod_cast this
  have hmk : 40 * (D.R.m : ℝ) ^ 2 ≤ (D.R.k : ℝ) := by
    have h1 : (D.R.m : ℝ) ^ 2 ≤ (D.R.m : ℝ) ^ 2 * large₂.sc.L := le_mul_of_one_le_right (by positivity) hL
    have h2 : 40 * ((D.R.m : ℝ) ^ 2 * large₂.sc.L) ≤ Cl * ((D.R.m : ℝ) ^ 2 * large₂.sc.L) :=
      mul_le_mul_of_nonneg_right h40 (by positivity)
    linarith
  have hk1 : (1 : ℝ) ≤ (D.R.k : ℝ) := by nlinarith

  have hCL : 1 ≤ Cl * large₂.sc.L := by nlinarith
  have hVV := Formalism.L2.SG.Pf.SzHypFD.vv_eq_vand hT h.1 hCL τ
  have hlam0 : 0 < vand (lamSH D.R (D.hc τ)) :=
    Finset.prod_pos fun _ _ => Finset.prod_pos fun _ hb =>
      sub_pos.2 (Formalism.MainNotions.BridgeLemma.szh_anti h.1 τ (Finset.mem_filter.1 hb).2)
  have hvand : vand (lamSH D.R (D.hc τ)) ≤ Real.exp (10 * D.R.k * D.R.m * large₂.sc.L) * vand (uS D u τ) :=
    GlobalTheory.RowVand.vand_lamSH_le D large₂ C' Cl Cg cb Cu cT CT C0 h h40 u τ
  have hexp : Real.exp (10 * D.R.k * D.R.m * large₂.sc.L) = large₂.sc.b ^ (10 * (D.R.k : ℝ) * D.R.m) := by
    rw [hbexp, ← Real.exp_mul]; ring_nf
  rw [hexp] at hvand
  have hbp : 0 < large₂.sc.b ^ (10 * (D.R.k : ℝ) * D.R.m) := Real.rpow_pos_of_pos hb0 _
  have hu0 : 0 < vand (uS D u τ) := (pos_iff_pos_of_mul_pos (hlam0.trans_le hvand)).1 hbp
  have hQ0 : 0 ≤ VV D τ / vand (uS D u τ) := by rw [hVV]; positivity
  have hQ : VV D τ / vand (uS D u τ) ≤ large₂.sc.b ^ (10 * (D.R.k : ℝ) * D.R.m) := by
    rw [div_le_iff₀ hu0, hVV]; exact hvand

  have hrd1 : 1 ≤ D.host.rdE := by
    have h1 : (1 : ℝ) ≤ |((NumberField.discr D.host.E : ℤ) : ℝ)| := by
      exact_mod_cast Int.one_le_abs (NumberField.discr_ne_zero D.host.E)
    exact Real.one_le_rpow h1 (by positivity)
  have hrd0 : 0 < D.host.rdE := by linarith
  have hrdb : D.host.rdE ≤ large₂.sc.b := by
    have hCl0 : 0 < Cl := by linarith
    have h1 : Real.log D.host.rdE ≤ large₂.sc.L := by
      refine hlogrd.trans ?_
      rw [div_le_iff₀ hCl0]; nlinarith
    calc D.host.rdE = Real.exp (Real.log D.host.rdE) := (Real.exp_log hrd0).symm
      _ ≤ Real.exp large₂.sc.L := Real.exp_le_exp.mpr h1
      _ = large₂.sc.b := hbexp.symm

  have hka : D.host.ka = 2 * Real.pi / D.host.rdE := by
    show Real.pi / (D.host.rdE / 2) = 2 * Real.pi / D.host.rdE
    field_simp
  have hka0 : 0 < D.host.ka := by rw [hka]; positivity
  have hki : D.host.ka⁻¹ ≤ large₂.sc.b := by
    rw [hka, inv_div, div_le_iff₀ (by positivity)]
    nlinarith [Real.pi_gt_three]

  have hg1ge : 1 ≤ (D.host.g 0 : ℝ) :=
    le_trans (one_le_pow₀ (one_le_mul_of_one_le_of_one_le hk1 hb1.le)) hkg1
  have hCg : 0 ≤ Cg := by
    by_contra hc
    push_neg at hc
    have := Real.rpow_lt_one_of_one_lt_of_neg hb1 hc
    linarith
  have hgg : gg D ≤ large₂.sc.b ^ (2 * Cg) := by
    rw [show 2 * Cg = Cg + Cg by ring, Real.rpow_add hb0]
    unfold gg
    exact mul_le_mul hg1 hg2 (by positivity) (by positivity)
  have hgg0 : 0 ≤ gg D := by unfold gg; positivity
  have key := root_le D.host.ka D.host.rdE (gg D) (VV D τ / vand (uS D u τ)) large₂.sc.b Cg D.R.m D.R.k
    hb1 hm hmk hka0 hki hrd1 hgg0 hgg hCg hQ0 hQ
  unfold Tcrit
  rw [mul_div_assoc]
  exact key

end GlobalTheory.CritLevelUpper
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.CriticalLevelLePowAllPlacesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

theorem _root_.GlobalTheory.T.criticalLevel_le_pow_allPlaces : Formalism.L2.SG.Pf.SzHypFD.DsigHC → ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ), Ties D → Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → 40 ≤ Cl → ∀ u τ, Tcrit D u τ ≤ large₂.sc.b ^ ((4 * Cg + 12) * (D.R.m : ℝ)) := by
  first | exact @GlobalTheory.CritLevelUpper.tcrit_le_pow | exact GlobalTheory.CritLevelUpper.tcrit_le_pow | (intros; apply GlobalTheory.CritLevelUpper.tcrit_le_pow <;> assumption)
end
end
