module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThreeLeScaleOfPowBound
public import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Formalism.LocalRingCardinality.DataParams₂
import Mathlib.Algebra.Order.Star.Int
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoPiMulWeightLengthLeMaxWeightDegreeSqStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsPageRunRecord

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiveElementaryInequalitiesEventually

section

@[expose] public section

open Filter Real

namespace GlobalTheory

theorem eventually_const_mul_rpow_le_rpow (a b c : ℝ) (h : a < b) :
    ∀ᶠ x : ℝ in atTop, c * x ^ a ≤ x ^ b := by
  have ht := tendsto_rpow_atTop (sub_pos.2 h)
  filter_upwards [ht.eventually_ge_atTop c, eventually_gt_atTop (0 : ℝ)] with x hx hx0
  have e : x ^ b = x ^ (b - a) * x ^ a := by
    rw [← Real.rpow_add hx0]; ring_nf
  rw [e]
  exact mul_le_mul_of_nonneg_right hx (Real.rpow_nonneg hx0.le _)

theorem sqrt_mul_rpow_neg_eq (eps x : ℝ) (hx : 0 < x) :
    Real.sqrt (x * x ^ (-(eps / 8))) = x ^ (1 / 2 - eps / 16) := by
  have h1 : x * x ^ (-(eps / 8)) = x ^ (1 - eps / 8) := by
    rw [sub_eq_add_neg, Real.rpow_add hx, Real.rpow_one]
  rw [h1, Real.sqrt_eq_rpow, ← Real.rpow_mul hx.le]
  ring_nf

theorem five_elementary_inequalities_eventually :
    ∀ eps : ℝ, 0 < eps → eps < 1 → ∀ᶠ x : ℝ in Filter.atTop,
      x ^ (eps / 4) + x ^ (eps / 3) + 1 + 3 * Real.log x ≤ x ^ eps / 5 ∧
      11 ≤ x ^ (eps / 5) ∧ 8 * Real.log x ^ 2 < x ^ 2 ∧
      2 * x ^ (eps / 5 + eps / 100) ≤ Real.sqrt (x * x ^ (-(eps / 8))) ∧
      44 ≤ Real.sqrt (x * x ^ (-(eps / 8))) := by
  intro eps he he1
  have h1 := eventually_const_mul_rpow_le_rpow (eps / 4) eps 20 (by linarith)
  have h2 := eventually_const_mul_rpow_le_rpow (eps / 3) eps 20 (by linarith)
  have h3 := eventually_const_mul_rpow_le_rpow 0 eps 20 he
  have h4 := (isLittleO_log_rpow_atTop he).bound (show (0:ℝ) < 1 / 60 by norm_num)
  have h5 := eventually_const_mul_rpow_le_rpow 0 (eps / 5) 11 (by linarith)
  have h6 := Real.isLittleO_log_id_atTop.bound (show (0:ℝ) < 1 / 4 by norm_num)
  have h7 := eventually_const_mul_rpow_le_rpow (eps / 5 + eps / 100) (1 / 2 - eps / 16) 2
    (by linarith)
  have h8 := eventually_const_mul_rpow_le_rpow 0 (1 / 2 - eps / 16) 44 (by linarith)
  filter_upwards [h1, h2, h3, h4, h5, h6, h7, h8, eventually_gt_atTop (0 : ℝ)]
    with x h1 h2 h3 h4 h5 h6 h7 h8 hx
  rw [Real.rpow_zero] at h3 h5 h8
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hx _)] at h4
  rw [Real.norm_eq_abs, Real.norm_eq_abs, id, abs_of_pos hx] at h6
  rw [sqrt_mul_rpow_neg_eq eps x hx]
  have hl := le_abs_self (Real.log x)
  refine ⟨by linarith, by linarith, ?_, h7, by linarith⟩
  nlinarith [abs_nonneg (Real.log x), sq_abs (Real.log x)]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiveElementaryInequalitiesEventuallyStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.eventually_rpow_log_inequalities : ∀ eps : ℝ, 0 < eps → eps < 1 → ∀ᶠ x : ℝ in Filter.atTop, x ^ (eps / 4) + x ^ (eps / 3) + 1 + 3 * Real.log x ≤ x ^ eps / 5 ∧ 11 ≤ x ^ (eps / 5) ∧ 8 * Real.log x ^ 2 < x ^ 2 ∧ 2 * x ^ (eps / 5 + eps / 100) ≤ Real.sqrt (x * x ^ (-(eps / 8))) ∧ 44 ≤ Real.sqrt (x * x ^ (-(eps / 8))) := by
  first | exact @GlobalTheory.five_elementary_inequalities_eventually | exact GlobalTheory.five_elementary_inequalities_eventually | (intros; apply GlobalTheory.five_elementary_inequalities_eventually <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickSetDensityLeInvFourLw

section

@[expose] public section

open Formalism.BasicNotions

namespace GlobalTheory

theorem thick_density_le (D : D7) (L : SizeData₂ D) (h8 : 8 * D.host.Lw < D.R.n) :
    L.de2 ≤ 1 / (4 * (D.host.Lw : ℝ)) := by
  have hn : D.R.n0 ≤ D.R.n := by
    have h : addOrderOf D.R.toFrame.a0 ≤ Fintype.card D.R.toFrame.A := addOrderOf_le_card_univ
    rw [D.R.toFrame.card_A] at h
    exact h
  set n := D.R.n with hn'
  set Lw := D.host.Lw with hLw
  have hL2 : 2 ≤ Lw := D.host.two_le_Lw
  have hrange : ∀ s ∈ D.host.T2, 4 * Lw * s < n := by
    intro s hs; exact lt_of_lt_of_le (D.host.second_set_range s hs) hn
  set N := (n - 1) / (4 * Lw) + 1 with hN
  have hsub : D.host.T2 ⊆ Finset.range N := by
    intro s hs
    have h := hrange s hs
    rw [Finset.mem_range, hN, Nat.lt_succ_iff, Nat.le_div_iff_mul_le (by omega)]
    have : s * (4 * Lw) = 4 * Lw * s := by ring
    omega
  have hN3 : 3 ≤ N := by
    have : 2 ≤ (n - 1) / (4 * Lw) := by
      rw [Nat.le_div_iff_mul_le (by omega)]; omega
    omega
  have hne : ¬ Finset.range N ⊆ D.host.T2 := by
    intro hs
    have h0 : 0 ∈ D.host.T2 := hs (Finset.mem_range.2 (by omega))
    have h1 : 1 ∈ D.host.T2 := hs (Finset.mem_range.2 (by omega))
    have h2 : 2 ∈ D.host.T2 := hs (Finset.mem_range.2 (by omega))
    have hnr := D.host.second_set_no_relation
    have hL2' : (2 : ℤ) ≤ (Lw : ℤ) := by exact_mod_cast hL2
    exact hnr 0 h0 1 h1 2 h2 (by norm_num) (by norm_num) (by norm_num) 1 2
      (by norm_num) (by simp; omega) (by norm_num) (by rw [abs_of_pos (by norm_num)]; exact hL2')
      (by norm_num) (by norm_num)
  have hcard : D.host.T2.card ≤ (n - 1) / (4 * Lw) := by
    have h1 : D.host.T2.card ≤ N := by simpa using Finset.card_le_card hsub
    have h2 : D.host.T2.card ≠ N := by
      intro heq
      exact hne (Finset.eq_of_subset_of_card_le hsub (by simp [heq])).symm.subset
    omega
  have hmul : D.host.T2.card * (4 * Lw) < n := by
    have := (Nat.le_div_iff_mul_le (by omega)).1 hcard
    omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hLpos : (0 : ℝ) < 4 * (Lw : ℝ) := by
    have : (2 : ℝ) ≤ Lw := by exact_mod_cast hL2
    linarith
  rw [L.typeDensity_eq_card_div, div_le_div_iff₀ hnpos hLpos, one_mul]
  have : ((D.host.T2.card * (4 * Lw) : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmul.le
  push_cast at this
  linarith

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickSetDensityLeInvFourLwStatement

section

@[expose] public section

open Formalism.BasicNotions

theorem _root_.GlobalTheory.T.thickSet_density_le_inv_four_Lw : ∀ (D : D7) (L : SizeData₂ D), 8 * D.host.Lw < D.R.n → L.de2 ≤ 1 / (4 * (D.host.Lw : ℝ)) := by
  first | exact @GlobalTheory.thick_density_le | exact GlobalTheory.thick_density_le | (intros; apply GlobalTheory.thick_density_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndexBoundParameterRequirementsEventuallyFamily

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies

namespace GlobalTheory.OntoSizeRows

theorem sizeRows_at {D : D7} {L : SizeData₂ D} {Pm : ParameterChoice' D L} (Tp : ParamsT D L Pm) (hK : DV.KapDef D)
    (S : SizesAt L) (hC : Pm.CnW = 10) (hg : ∀ j : Fin 2, ((D.host.g j : ℕ) : ℝ) ≤ Real.exp (9 * L.sc.L))
    (hn : L.sc.x ^ (2 + 8 * L.sc.eps) ≤ D.R.n ∧ (D.R.n : ℝ) ≤ 2 * L.sc.x ^ (2 + 8 * L.sc.eps))
    (hm : Real.sqrt (L.sc.x * L.sc.delta1) ≤ D.R.m)
    (h1 : L.sc.x ^ (L.sc.eps / 4) + L.sc.x ^ (L.sc.eps / 3) + 1 + 3 * Real.log L.sc.x ≤ L.sc.x ^ L.sc.eps / 5)
    (h2 : 11 ≤ L.sc.x ^ (L.sc.ez / 5)) (h6 : 8 * Real.log L.sc.x ^ 2 < L.sc.x ^ 2)
    (h8 : 2 * L.sc.x ^ (L.sc.eps / 5 + L.sc.eps / 100) ≤ Real.sqrt (L.sc.x * L.sc.delta1))
    (h11 : 44 ≤ Real.sqrt (L.sc.x * L.sc.delta1)) : GlobalTheory.IndexAssembly.SizeRows Tp hK := by
  obtain ⟨-, -, -, -, -, -, sQD, -, -, -, -, sDe2, sLw, -⟩ := S
  have hx1 := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have he := L.sc.eps_pos
  have hel := L.sc.eps_lt
  have hm0 : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (show 1 ≤ D.R.m by have := D.R.two_le_m; omega)
  have hn0 : (0 : ℝ) < D.R.n := by have : 1 ≤ D.R.n := Formalism.HC.Frame.ord_pos _; exact_mod_cast this
  refine ⟨?_, h2, GlobalTheory.T.two_pi_mul_weightLength_le_maxWeightDegree_sq D L Pm Tp hK, by rw [hC], sDe2, ?_, ?_, ?_, GlobalTheory.FinalJoin.RecordRun.k_b'_le Pm
    (GlobalTheory.IndexAssembly.three_le_scale_of_pow_bound h2), ?_, by exact_mod_cast (show (44 : ℝ) ≤ D.R.m by linarith), hn0.le⟩
  ·
    have hlogeta := Pm.logeta
    have heta := L.etaSz_pos
    have a1 : L.etaSz ≤ Real.exp (L.sc.x ^ (L.sc.eps / 4)) := (Real.log_le_iff_le_exp heta).1 hlogeta
    have a2 : (D.R.n : ℝ) ≤ Real.exp (1 + 3 * Real.log L.sc.x) := by
      have e3 : Real.exp (3 * Real.log L.sc.x) = L.sc.x ^ 3 := by
        rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.exp_nat_mul, Real.exp_log hx0]
      rw [Real.exp_add, e3]
      have b1 : L.sc.x ^ (2 + 8 * L.sc.eps) ≤ L.sc.x ^ (3 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at b1
      have b2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      have b3 : 0 ≤ L.sc.x ^ 3 := by positivity
      nlinarith [hn.2]
    have key : L.etaSz * L.sc.X' * D.R.n ≤ Real.exp (L.sc.L / 5) := by
      have hX : 0 < L.sc.X' := Real.exp_pos _
      calc L.etaSz * L.sc.X' * D.R.n
          ≤ Real.exp (L.sc.x ^ (L.sc.eps / 4)) * L.sc.X' * Real.exp (1 + 3 * Real.log L.sc.x) := by gcongr
        _ = Real.exp (L.sc.x ^ (L.sc.eps / 4) + L.sc.x ^ (L.sc.eps / 3) + (1 + 3 * Real.log L.sc.x)) := by
          unfold Scale.X'; simp only [Real.exp_add]
        _ ≤ Real.exp (L.sc.L / 5) := by
          apply Real.exp_le_exp.2
          unfold Scale.L
          linarith
    have hb45 : L.sc.b ^ ((4 : ℝ) / 5) = Real.exp (L.sc.L * (4 / 5)) := by
      unfold Scale.b; rw [← Real.exp_mul]
    have hX : 0 < L.sc.X' := Real.exp_pos _
    unfold Scale.w'' Scale.b' Scale.a
    rw [hb45, div_div, le_div_iff₀ (by positivity)]
    have e5 : Real.exp (L.sc.L / 5) * Real.exp (L.sc.L * (4 / 5)) = L.sc.b := by
      unfold Scale.b; rw [← Real.exp_add]; ring_nf
    calc L.etaSz * Real.exp (L.sc.L * (4 / 5)) * (L.sc.X' * (L.sc.x * D.R.n))
        = L.sc.x * (L.etaSz * L.sc.X' * D.R.n) * Real.exp (L.sc.L * (4 / 5)) := by ring
      _ ≤ L.sc.x * Real.exp (L.sc.L / 5) * Real.exp (L.sc.L * (4 / 5)) := by gcongr
      _ = L.sc.x * L.sc.b := by rw [mul_assoc, e5]
  · apply GlobalTheory.T.thickSet_density_le_inv_four_Lw
    have a1 : L.sc.x ^ (2 : ℝ) ≤ L.sc.x ^ (2 + 8 * L.sc.eps) :=
      Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
    rw [Real.rpow_two] at a1
    have : ((8 * D.host.Lw : ℕ) : ℝ) < D.R.n := by
      push_cast
      unfold SizeLw at sLw
      linarith
    exact_mod_cast this
  · intro i
    have e : Real.exp (9 * L.sc.L) = L.sc.b ^ 9 := by
      unfold Scale.b; rw [← Real.exp_nat_mul]; norm_num
    rw [← e]; exact hg i
  ·
    have hq : (0 : ℝ) < D.host.q := lt_trans (by positivity) Pm.qd_pow.1
    have hd : (0 : ℝ) < D.host.d := lt_trans (by positivity) Pm.qd_pow.2
    obtain ⟨-, -, q2, -, d2, -⟩ := sQD
    unfold szTh at q2 d2
    push_cast
    rw [Real.log_mul hq.ne' hd.ne']
    linarith
  ·
    have hD := Pm.Del_ge.2.2.2
    have hl := Pm.logDel
    have hN0 : (0 : ℝ) ≤ D.R.N D.R.m := Nat.cast_nonneg _
    have hm10 : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 10 := one_le_pow₀ hm0
    have a1 : (D.R.N D.R.m : ℝ) ≤ (D.s.Del : ℝ) := le_trans (le_mul_of_one_le_right hN0 hm10) hD
    have hX : 0 < L.sc.X' := Real.exp_pos _
    rcases le_or_gt (D.s.Del : ℝ) 0 with h0 | h0
    · linarith
    · have a2 : (D.s.Del : ℝ) ≤ Real.exp (L.sc.x ^ (L.sc.eps / 4) / 2) := (Real.log_le_iff_le_exp h0).1 hl
      have a3 : L.sc.x ^ (L.sc.eps / 4) ≤ L.sc.x ^ (L.sc.eps / 3) :=
        Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
      have a4 : 0 ≤ L.sc.x ^ (L.sc.eps / 4) := by positivity
      have a5 : Real.exp (L.sc.x ^ (L.sc.eps / 4) / 2) ≤ L.sc.X' := by
        unfold Scale.X'; exact Real.exp_le_exp.2 (by linarith)
      linarith

theorem sizeRows_along : Closed FamHyp fun Fm _ => ∃ x0 : ℝ, ∀ (x : ℝ) (hx : Fm.x1 < x), x0 ≤ x → ∀ ι : Fm.Ix x,
    GlobalTheory.IndexAssembly.SizeRows (Fm.parT x hx ι) (Fm.ex x hx ι).kap_def := by
  refine ⟨1 / 100, by norm_num, fun eps he hle => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH hc _ => ?_⟩⟩
  have hez : 0 < Fm.ez := by
    obtain ⟨i⟩ := Fm.Ix_zero
    rw [← Fm.L_ez 0 i]
    exact (Fm.L 0 i).sc.ez_pos
  have hev : ∀ᶠ x : ℝ in Filter.atTop, 11 ≤ x ^ (Fm.ez / 5) :=
    (tendsto_rpow_atTop (by positivity : 0 < Fm.ez / 5)).eventually_ge_atTop 11
  obtain ⟨x0, hx0⟩ := Filter.eventually_atTop.1 ((GlobalTheory.T.eventually_rpow_log_inequalities eps he (by linarith)).and hev)
  refine ⟨x0, fun x hx hx0' ι => ?_⟩
  have hsx := Fm.L_x x ι hx
  have hse := Fm.L_eps x ι
  obtain ⟨⟨a1, -, a6, a8, a11⟩, a2⟩ := hx0 x hx0'
  obtain ⟨w1, w2, -⟩ := hc.2.1 x hx ι
  have hd : (Fm.L x ι).sc.delta1 = x ^ (-(eps / 8)) := by unfold Scale.delta1; rw [hsx, hse]
  refine sizeRows_at _ _ (Fm.sizes x hx ι) (Fm.fixed.2.2.2.2.2.2.2 x hx ι).1
    ((hc.1.2.2.2.2.2.2.2.2 x hx ι).2.2.1) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hsx, hse]; exact w1
  · rw [hsx]; exact w2.1
  · rw [hsx, hse]; exact a1
  · rw [hsx, Fm.L_ez x ι]; exact a2
  · rw [hsx]; exact a6
  · rw [hd, hsx, hse]; exact a8
  · rw [hd, hsx]; exact a11

end GlobalTheory.OntoSizeRows
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndexBoundParameterRequirementsEventuallyFamilyStatement

section

@[expose] public section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies

theorem _root_.GlobalTheory.T.indexBoundParameterRequirements_eventually_family : Closed FamHyp fun Fm _ => ∃ x0 : ℝ, ∀ (x : ℝ) (hx : Fm.x1 < x), x0 ≤ x → ∀ ι : Fm.Ix x, GlobalTheory.IndexAssembly.SizeRows (Fm.parT x hx ι) (Fm.ex x hx ι).kap_def := by
  first | exact @GlobalTheory.OntoSizeRows.sizeRows_along | exact GlobalTheory.OntoSizeRows.sizeRows_along | (intros; apply GlobalTheory.OntoSizeRows.sizeRows_along <;> assumption)
end
end
