module

import Formalism.LocalRingCardinality.HeightBoundGeFourthPowerRank
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LargeConstantLeParamCube
public import Formalism.LocalRingCardinality.DataParamsT
public import Formalism.SharpRestriction.ElevenLe
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Formalism.SharpRestriction.Divisibility.WeightAlgebra
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.BaseDegreeAtLiftIndex
import Mathlib.Tactic.Linter.Style

-- Source module: Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.DiscriminantPowEightLeSqrt

section

@[expose] public section

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps.Num

variable {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L}

def q0N (T : ParamsT D L P) : ℕ := ⌈L.sc.b / (T.TO : ℝ)⌉₊

theorem f_ge (D : D7) : 8 ≤ D.R.f := by
  apply Formalism.BasicNotions.D7.eight_le_f <;> assumption

theorem r_ge (D : D7) : 6 ≤ D.R.r := by
  unfold Ranks.r
  have := D.R.two_le_m
  have := D.R.m_add_three_le_k
  omega

theorem r_le_2k (D : D7) : D.R.r ≤ 2 * D.R.k := by
  unfold Ranks.r
  have := D.R.m_add_three_le_k
  omega

theorem f_le_k (D : D7) : D.R.f ≤ D.R.k := by
  unfold Ranks.f Ranks.n
  exact D.R.f_le_k

theorem one_le_L (L : SizeData₂ D) : 1 ≤ L.sc.L := by
  unfold Scale.L
  exact Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le

theorem b_pos (L : SizeData₂ D) : 0 < L.sc.b := by
  unfold Scale.b
  exact Real.exp_pos _

theorem A_le_Z (L : SizeData₂ D) : (D.R.f : ℝ) * D.R.r ≤ zBase L := by
  unfold zBase
  exact le_mul_of_one_le_right (by positivity) (one_le_L L)

theorem zBase_pow_twelve_le (T : ParamsT D L P) (hZ : 1 ≤ zBase L) : zBase L ^ 12 ≤ T.PP := by
  rw [T.PP_eq]
  have h1 : zBase L ^ (12 : ℕ) = zBase L ^ (12 : ℝ) := by
    rw [show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have h2 : zBase L ^ (12 : ℝ) ≤ zBase L ^ T.eP := Real.rpow_le_rpow_of_exponent_le hZ T.eP_ge
  have h3 : 0 ≤ zBase L ^ T.eP := Real.rpow_nonneg (by linarith) _
  have h4 : 1 * zBase L ^ T.eP ≤ T.CP * zBase L ^ T.eP := mul_le_mul_of_nonneg_right T.one_le_CP h3
  rw [h1]
  linarith

theorem discriminant_pow_eight_le_sqrt (P : ParameterChoice' D L) (S : SizesAt L) : D.host.rdE ^ 8 ≤ L.sc.b ^ ((1 : ℝ) / 2) := by
  obtain ⟨-, -, -, -, ⟨ht1, -⟩, -, hQD, -⟩ := S
  obtain ⟨-, -, -, -, -, -, hrd1, hrd2⟩ := hQD
  have hc := P.condE_le
  simp only [Formalism.BasicNotions.LevelStarExponents.condE] at hc
  push_cast at hc
  have hq : (1 : ℝ) ≤ D.host.q := by
    have := D.host.qd_big.1
    exact_mod_cast (by omega : 1 ≤ D.host.q)
  have hd : (1 : ℝ) ≤ D.host.d := by
    have := D.host.qd_big.2
    exact_mod_cast (by omega : 1 ≤ D.host.d)
  have hQS : (1 : ℝ) ≤ D.host.QS := by exact_mod_cast D.host.QS_pos
  have hqd : (1 : ℝ) ≤ (D.host.q : ℝ) * D.host.d := by nlinarith
  have hs0 : 0 ≤ Real.sqrt ((D.host.q : ℝ) * D.host.d) := Real.sqrt_nonneg _
  have hsq : Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ (D.host.q : ℝ) * D.host.d := by
    rw [Real.sqrt_le_iff]
    constructor
    · linarith
    · nlinarith
  have hC1 : (1 : ℝ) ≤ (D.host.QS : ℝ) * D.host.q * D.host.d := by nlinarith
  have hrdC : D.host.rdE ≤ (D.host.QS : ℝ) * D.host.q * D.host.d := by
    have h1 : (D.host.QS : ℝ) / 2 * Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤
        (D.host.QS : ℝ) * Real.sqrt ((D.host.q : ℝ) * D.host.d) := by nlinarith
    have h2 : (D.host.QS : ℝ) * Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤
        (D.host.QS : ℝ) * ((D.host.q : ℝ) * D.host.d) := mul_le_mul_of_nonneg_left hsq (by linarith)
    nlinarith
  have h8 : D.host.rdE ^ 8 ≤ ((D.host.QS : ℝ) * D.host.q * D.host.d) ^ 8 :=
    pow_le_pow_left₀ (by linarith) hrdC 8
  have h36 : ((D.host.QS : ℝ) * D.host.q * D.host.d) ^ 8 ≤ ((D.host.QS : ℝ) * D.host.q * D.host.d) ^ 36 :=
    pow_le_pow_right₀ hC1 (by norm_num)
  have ht : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 150 := one_le_pow₀ ht1
  have hpos : 0 ≤ ((D.host.QS : ℝ) * D.host.q * D.host.d) ^ 36 := by positivity
  nlinarith

theorem rn_of (T : ParamsT D L P) (S : SizesAt L) (hZ : 10 ^ 60 ≤ zBase L) :
    Rn ((D.R.f : ℝ) * D.R.r) D.R.k L.sc.b (L.sc.b ^ ((1 : ℝ) / 2)) T.PP T.TO D.host.rdE D.R.r ((T.Dp : ℝ) + 2) T.nWn T.nP
      (q0N T) := by
  have hf8 : (8 : ℝ) ≤ D.R.f := by exact_mod_cast f_ge D
  have hr6 : (6 : ℝ) ≤ D.R.r := by exact_mod_cast r_ge D
  have hfk : (D.R.f : ℝ) ≤ D.R.k := by exact_mod_cast f_le_k D
  have hr2k : (D.R.r : ℝ) ≤ 2 * D.R.k := by exact_mod_cast r_le_2k D
  have hz1 : (1 : ℝ) ≤ zBase L := le_trans (by norm_num) hZ
  have hz12 := zBase_pow_twelve_le T hz1
  have hAZ := A_le_Z L
  have hzz2 : zBase L ^ 2 ≤ zBase L ^ 12 := by
    first
    | exact pow_le_pow_right₀ hz1 (by norm_num)
    | exact pow_le_pow_right hz1 (by norm_num)
  have hPPA : (10 : ℝ) ^ 60 * ((D.R.f : ℝ) * D.R.r) ≤ T.PP := by
    have h1 : (10 : ℝ) ^ 60 * ((D.R.f : ℝ) * D.R.r) ≤ zBase L * zBase L :=
      mul_le_mul hZ hAZ (by positivity) (by linarith)
    nlinarith
  have hTO40 := T.TO_40
  have hTOpos : (0 : ℝ) < T.TO := by exact_mod_cast (by omega : 0 < T.TO)
  have hb := b_pos L
  have hrd1 : (1 : ℝ) ≤ D.host.rdE := by
    have hd : (1 : ℝ) ≤ |(NumberField.discr D.host.E : ℝ)| := by
      have h := NumberField.discr_ne_zero D.host.E
      have h' : (1 : ℤ) ≤ |NumberField.discr D.host.E| := Int.one_le_abs h
      exact_mod_cast h'
    unfold Host.rdE
    exact Real.one_le_rpow hd (by positivity)
  have hnW : 40 ≤ T.nWn := by
    have h1 := T.nW_lo.1
    have h2 := f_ge D
    have h3 := r_ge D
    have h4 : 8 * 6 ≤ D.R.f * D.R.r := Nat.mul_le_mul h2 h3
    have h5 : D.R.f * D.R.r ≤ D.R.f * D.R.r * (D.R.r + 1) := by
      first
      | exact Nat.le_mul_of_pos_right _ (by omega)
      | exact Nat.le_mul_of_pos_right (by omega)
    generalize D.R.f * D.R.r * (D.R.r + 1) = X at *
    generalize D.R.f * D.R.r = Y at *
    omega
  have hq0lo : L.sc.b ≤ (T.TO : ℝ) * (q0N T : ℕ) := by
    unfold q0N
    have h := Nat.le_ceil (L.sc.b / T.TO)
    have e : (T.TO : ℝ) * (L.sc.b / T.TO) = L.sc.b := by
      field_simp
    calc L.sc.b = (T.TO : ℝ) * (L.sc.b / T.TO) := e.symm
      _ ≤ _ := mul_le_mul_of_nonneg_left h hTOpos.le
  have hq0hi : (T.TO : ℝ) * (q0N T : ℕ) ≤ L.sc.b + T.TO := by
    unfold q0N
    have h := Nat.ceil_lt_add_one (div_nonneg hb.le hTOpos.le)
    have e : (T.TO : ℝ) * (L.sc.b / T.TO + 1) = L.sc.b + T.TO := by
      field_simp
      try ring
    have := mul_le_mul_of_nonneg_left h.le hTOpos.le
    linarith
  exact
    { forty_eight_le_constant := by nlinarith
      k8 := by linarith
      Ak := by nlinarith [mul_le_mul hfk hr2k (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
      sb_sq := by
        rw [← Real.sqrt_eq_rpow]
        exact Real.mul_self_sqrt hb.le
      PPA := hPPA
      h32 := T.precision_cube_order_sq_le_sqrt
      hTP := T.TO_PP'
      one_le_order_alt := by exact_mod_cast (by omega : 1 ≤ T.TO)
      rd1 := hrd1
      rd8 := discriminant_pow_eight_le_sqrt P S
      r6 := hr6
      rA := by nlinarith
      two_le_degree_alt := by have : (0 : ℝ) ≤ T.Dp := Nat.cast_nonneg _; linarith
      W := by exact_mod_cast T.TO_nW
      forty_mul_degree_le_order := by exact_mod_cast T.TO_40
      forty_le_weight_count := by exact_mod_cast hnW
      projectivePointSizes := Nat.cast_nonneg _
      nPW := by exact_mod_cast T.nW_lo.2.2
      q0lo := hq0lo
      q0hi := hq0hi }

end Formalism.MainNotions.Gaps.EtaleWeightGaps.Num

end
end
end

-- Source module: Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.NonvanishingSectionCondition

section

@[expose] public section

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps.Num

variable {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L}

theorem dm_eq (T : ParamsT D L P) : WeightFamilies.dimY D D.R.m = T.Dp := by
  rw [T.Dp_eq]
  unfold WeightFamilies.dimY Ranks.sigW Ranks.r
  simp [Nat.choose_two_right]

theorem order_le_modulus (T : ParamsT D L P) (S : SizesAt L) (hZ : 10 ^ 60 ≤ zBase L) : T.TO ≤ q0N T := by
  unfold q0N
  have hT40 := T.TO_40
  have hTpos : (0 : ℝ) < (T.TO : ℝ) := by exact_mod_cast (show 0 < T.TO by omega)
  have hZ' : (1 : ℝ) ≤ zBase L := by
    have h : (1 : ℝ) ≤ 10 ^ 60 := by norm_num
    linarith
  have hPP : 1 ≤ T.PP := by
    rw [T.PP_eq]
    exact one_le_mul_of_one_le_of_one_le T.one_le_CP (Real.one_le_rpow hZ' (by linarith [T.eP_ge]))
  have hbpos : 0 < L.sc.b := by unfold Scale.b; exact Real.exp_pos _
  have h1 : (T.TO : ℝ) ≤ L.sc.b ^ (1 / 2 : ℝ) := le_trans (le_mul_of_one_le_right hTpos.le hPP) T.TO_PP'
  have h2 := mul_self_le_mul_self hTpos.le h1
  rw [← Real.rpow_add hbpos] at h2
  norm_num at h2
  have hq : (T.TO : ℝ) ≤ L.sc.b / (T.TO : ℝ) := by
    rw [le_div_iff₀ hTpos]
    linarith
  exact_mod_cast le_trans hq (Nat.le_ceil _)

abbrev runOf (T : ParamsT D L P) (S : SizesAt L) (hZ : 10 ^ 60 ≤ zBase L) : RunN D where
  T := T.TO
  nW := T.nWn
  nP := T.nP
  Q0 := q0N T
  T_pos := by have := T.TO_40; omega
  nW_even := T.nW_even
  even_nP₂ := T.even_nP₂
  split := T.split
  nP_le_nW := T.nW_lo.2.2
  hQ0 := by
    rw [dm_eq T]
    have := T.TO_nW; have := order_le_modulus T S hZ
    omega

def Kc0 : KAdm := ⟨1, 1, 1, 1, 1, 1, 1, 1, 2⟩

def NonvanishingSectionCondition (T : ParamsT D L P) : KHyp := ⟨10, 20, 1000, 12, T.CP, T.eP, 2⟩

section Run

variable (T : ParamsT D L P) (S : SizesAt L) (hZ : 10 ^ 60 ≤ zBase L)

theorem eTq : ((runOf T S hZ).Tq : ℝ) = (T.TO : ℝ) + ((T.Dp : ℝ) + 2) := by
  unfold RunN.Tq Tp
  dsimp only [runOf]
  rw [dm_eq T]
  push_cast
  ring

theorem eQ : ((runOf T S hZ).Q : ℝ) = (T.TO : ℝ) + ((T.Dp : ℝ) + 2) + 2 * D.R.r := by
  unfold RunN.Q
  push_cast
  linarith [eTq T S hZ]

theorem ekl : ((runOf T S hZ).kl : ℝ) =
    ((T.Dp : ℝ) + 2) * T.nWn + 2 * D.R.r + ((T.TO : ℝ) + ((T.Dp : ℝ) + 2)) * (q0N T : ℝ) := by
  unfold RunN.kl
  push_cast
  rw [eTq T S hZ]
  have hd : (Dm D : ℝ) = (T.Dp : ℝ) := by
    first
    | (unfold Dm; exact_mod_cast dm_eq T)
    | (simp only [Dm]; exact_mod_cast dm_eq T)
    | exact_mod_cast dm_eq T
  rw [hd]

theorem enV : (D.R.nV : ℝ) = (T.nP : ℝ) + (T.TO : ℝ) * T.nWn := by
  have h := T.split
  unfold Ranks.nV
  exact_mod_cast h

theorem ka_le : (runOf T S hZ).ka.size ≤ 4 * ((D.R.f : ℝ) * D.R.r) * L.sc.b := by
  refine (rn_of T S hZ).sK ?_
  have h := (runOf T S hZ).ka_size_le
  rw [ekl, eTq, eQ, enV T] at h
  exact h

theorem b_le_kl : L.sc.b ≤ ((runOf T S hZ).kl : ℝ) := by
  rw [ekl T S hZ]
  have hT40 := T.TO_40
  have hTpos : (0 : ℝ) < (T.TO : ℝ) := by exact_mod_cast (show 0 < T.TO by omega)
  have hq : L.sc.b / (T.TO : ℝ) ≤ (q0N T : ℝ) := by unfold q0N; exact Nat.le_ceil _
  have hq' : L.sc.b ≤ (T.TO : ℝ) * (q0N T : ℝ) := by
    rw [div_le_iff₀ hTpos] at hq
    linarith
  have h0 : (0 : ℝ) ≤ (T.Dp : ℝ) := by positivity
  have h1 : (0 : ℝ) ≤ (T.nWn : ℝ) := by positivity
  have h2 : (0 : ℝ) ≤ (q0N T : ℝ) := by positivity
  have h3 : (0 : ℝ) ≤ (D.R.r : ℝ) := by positivity
  nlinarith [mul_nonneg (add_nonneg h0 (by norm_num : (0 : ℝ) ≤ 2)) h1,
    mul_nonneg (add_nonneg h0 (by norm_num : (0 : ℝ) ≤ 2)) h2]

theorem b_le_ka : L.sc.b ≤ (runOf T S hZ).ka.size := (b_le_kl T S hZ).trans (runOf T S hZ).ka_size_ge

theorem dF_le : (DF (runOf T S hZ).wL : ℝ) ≤ 2 * ((D.R.f : ℝ) * D.R.r) * L.sc.b := by
  refine (rn_of T S hZ).dL ?_
  have h := (runOf T S hZ).DF_wL_le
  rw [eQ] at h
  exact h

theorem g_ge (P : ParameterChoice' D L) (i : Fin 2) : ((D.R.k : ℝ) * L.sc.b) ^ 8 ≤ (D.host.g i : ℝ) := by
  obtain ⟨Y, h1, -, -, h2⟩ := P.g_Y
  exact h1.trans (h2 i).1

theorem qq_ge (P : ParameterChoice' D L) : ((D.R.k : ℝ) * L.sc.b) ^ 8 ≤ (qq D : ℝ) := by
  unfold qq
  first
  | (rw [Nat.cast_min]; exact le_min (g_ge P 0) (g_ge P 1))
  | (push_cast; exact le_min (g_ge P 0) (g_ge P 1))

theorem eRR : WeightFamilies.RRv D 2 = D.host.rdE ^ 2 := by
  unfold WeightFamilies.RRv
  first
  | rfl
  | simp

theorem eg0 : (g0 D : ℝ) = 1250 * D.R.r := by
  unfold g0
  push_cast
  ring

theorem third_hypothesis_of_params : H3 L (NonvanishingSectionCondition T) T.CP T.eP 2 0 (runOf T S hZ).wL T.TO := by
  have hR := rn_of T S hZ
  have hd0 : (0 : ℝ) ≤ (DF (runOf T S hZ).wL : ℝ) := Nat.cast_nonneg _
  have hd := dF_le T S hZ
  have hq := qq_ge P
  have hq0 : (0 : ℝ) < (qq D : ℝ) := lt_of_lt_of_le (by have := hR.b_pos; have := hR.k1; positivity) hq
  have hb := hR.h3b hd0 hd hq
  have hx1 : 1 ≤ L.sc.x ^ T.Cp := Real.one_le_rpow L.sc.one_lt_alt.le T.Cp_nonneg
  have hfk : (D.R.f : ℝ) ≤ D.R.k := by exact_mod_cast f_le_k D
  have hmk : (D.R.m : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (by omega : D.R.m ≤ D.R.k)
  have hm0 : (0 : ℝ) < D.R.m := by
    have := D.R.two_le_m
    exact_mod_cast (by omega : 0 < D.R.m)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Real.rpow_zero, one_mul, eRR, WeightFamilies.PPv_rec T]
    exact hR.h3a hd0 hd hq
  · rw [Real.rpow_zero, one_mul, eRR, WeightFamilies.PPv_rec T, eg0]
    exact hb
  · rw [Real.rpow_zero, one_mul, WeightFamilies.PPv_rec T, dm_eq T]
    refine le_trans ?_ T.TO_ge
    have hden : 0 < (D.R.m : ℝ) * L.de2 := mul_pos hm0 L.thickDensity_pos
    apply div_le_div_of_nonneg_right _ hden.le
    have hP := hR.PP_pos
    exact le_mul_of_one_le_right (by positivity) hx1
  · show (T.TO : ℝ) * (WeightFamilies.RRv D 2 * WeightFamilies.PPv D L T.CP T.eP * (DF (runOf T S hZ).wL : ℝ) ^ 2 / (qq D : ℝ)) * g0 D ≤ 1
    rw [eRR, WeightFamilies.PPv_rec T, eg0]
    have e : (T.TO : ℝ) * (D.host.rdE ^ 2 * T.PP * (DF (runOf T S hZ).wL : ℝ) ^ 2 / (qq D : ℝ)) * (1250 * D.R.r) =
        ((T.TO : ℝ) * (1250 * D.R.r) * D.host.rdE ^ 2 * T.PP * (DF (runOf T S hZ).wL : ℝ) ^ 2) / (qq D : ℝ) := by ring
    rw [e, div_le_one hq0]
    exact hb
  · show (D.R.f : ℝ) * (D.R.m : ℝ) ^ 3 * WeightFamilies.RRv D 2 ^ 2 *
      (WeightFamilies.RRv D 2 * WeightFamilies.PPv D L T.CP T.eP * (DF (runOf T S hZ).wL : ℝ) ^ 2 / (qq D : ℝ)) ≤ 1 / 2
    rw [eRR, WeightFamilies.PPv_rec T]
    have hfm : (D.R.f : ℝ) * (D.R.m : ℝ) ^ 3 ≤ (D.R.k : ℝ) ^ 4 := by
      have : (D.R.m : ℝ) ^ 3 ≤ (D.R.k : ℝ) ^ 3 := pow_le_pow_left₀ hm0.le hmk 3
      calc (D.R.f : ℝ) * (D.R.m : ℝ) ^ 3 ≤ (D.R.k : ℝ) * (D.R.k : ℝ) ^ 3 :=
            mul_le_mul hfk this (by positivity) (by positivity)
        _ = (D.R.k : ℝ) ^ 4 := by ring
    have he := hR.h3e hd0 hd hq (fm := (D.R.f : ℝ) * (D.R.m : ℝ) ^ 3) (by positivity) hfm
    have e : (D.R.f : ℝ) * (D.R.m : ℝ) ^ 3 * (D.host.rdE ^ 2) ^ 2 *
        (D.host.rdE ^ 2 * T.PP * (DF (runOf T S hZ).wL : ℝ) ^ 2 / (qq D : ℝ)) =
        ((D.R.f : ℝ) * (D.R.m : ℝ) ^ 3 * (D.host.rdE ^ 2) ^ 2 *
        (D.host.rdE ^ 2 * T.PP * (DF (runOf T S hZ).wL : ℝ) ^ 2)) / (qq D : ℝ) := by ring
    rw [e, div_le_iff₀ hq0]
    linarith
  · rw [dm_eq T]
    have := hR.h3f hd0 hd hq
    have e : (T.Dp : ℝ) + 2 + 2 = (T.Dp : ℝ) + 4 := by ring
    rw [e] at this
    exact this

end Run

end Formalism.MainNotions.Gaps.EtaleWeightGaps.Num

end
end
end

-- Source module: Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.FourthHypothesisOfParams

section

@[expose] public section

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps.Num

variable {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L}

section Run

variable (T : ParamsT D L P) (S : SizesAt L) (hZ : 10 ^ 60 ≤ zBase L)

def h0R (T : ParamsT D L P) : ℝ := 4 * (T.TO : ℝ) ^ 2 + D.R.t + 1

theorem two_mul_order_sq_le_length : 2 * (T.TO : ℝ) ^ 2 ≤ ((runOf T S hZ).kl : ℝ) := by
  have hR := rn_of T S hZ
  have h1 := hR.sq_mul_sq_le; have h4 := hR.forty_eight_le_constant
  have h5 : 2 * (T.TO : ℝ) ^ 2 ≤ ((D.R.f : ℝ) * D.R.r) ^ 2 * (T.TO : ℝ) ^ 2 := by
    have : (2 : ℝ) ≤ ((D.R.f : ℝ) * D.R.r) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
  linarith [b_le_kl T S hZ]

theorem A_le_kf : (D.R.f : ℝ) * D.R.r ≤ 2 * ((D.R.k : ℝ) * D.R.f) := by
  have h1 : D.R.r ≤ 2 * D.R.k := by
    have := D.R.m_add_three_le_k
    unfold Formalism.BasicNotions.Ranks.r
    omega
  have h2 : (D.R.r : ℝ) ≤ 2 * (D.R.k : ℝ) := by exact_mod_cast h1
  have h3 : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
  have h4 := mul_le_mul_of_nonneg_left h2 h3
  linarith

theorem fourth_hypothesis_of_params : L.sc.b ≤ (runOf T S hZ).ka.size ∧ (T.TO : ℝ) * (runOf T S hZ).wL.size ≤ 2 * (runOf T S hZ).ka.size ∧
    (runOf T S hZ).wF.size ≤ ((WeightFamilies.dimY D D.R.m : ℝ) + 2) * (runOf T S hZ).wL.size + 5 * D.R.f * (D.R.r : ℝ) ^ 2 * T.TO ∧
    WeightFamilies.PPv D L T.CP T.eP ^ 3 * (T.TO : ℝ) ^ 2 ≤ L.sc.b ∧ WeightFamilies.RRv D 2 * WeightFamilies.PPv D L T.CP T.eP ≤ L.sc.b ∧
    (∀ i, 2 * DF (runOf T S hZ).ka + 2 < D.host.g i) := by
  have hR := rn_of T S hZ
  have hbk := b_le_ka T S hZ
  have hTb : (T.TO : ℝ) ≤ L.sc.b := hR.toBs.TO_le_sb.trans hR.toBs.sb_le_b
  refine ⟨hbk, ?_, ?_, ?_, ?_, fun i => ?_⟩
  · have := (runOf T S hZ).T_wL_le
    have e : ((runOf T S hZ).T : ℝ) = (T.TO : ℝ) := rfl
    rw [e] at this
    linarith
  · have h := (runOf T S hZ).wF_size_le
    have e : ((runOf T S hZ).nP : ℝ) = (T.nP : ℝ) := rfl
    rw [e] at h
    have hf : (8 : ℝ) ≤ D.R.f := by exact_mod_cast f_ge D
    have hr := hR.r6; have hT := hR.one_le_order_alt; have hn := hR.nPW; have hn2 := hR.nW_le
    have a0 : (0 : ℝ) ≤ (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 := by positivity
    have a1 : (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * 1 ≤ (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * T.TO := mul_le_mul_of_nonneg_left hT a0
    have a2 : (D.R.f : ℝ) * D.R.r * T.nP ≤ (D.R.f : ℝ) * D.R.r * T.TO :=
      mul_le_mul_of_nonneg_left (hn.trans hn2) (by positivity)
    have a3 : (D.R.f : ℝ) * D.R.r * T.TO ≤ (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * T.TO := by
      have : (D.R.f : ℝ) * D.R.r ≤ (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_right this (by linarith)
    have a4 : (1 : ℝ) ≤ (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 := by nlinarith
    have e2 : ((Dm D : ℕ) : ℝ) = (WeightFamilies.dimY D D.R.m : ℝ) := rfl
    rw [e2] at h
    nlinarith
  · rw [WeightFamilies.PPv_rec T]
    exact hR.h32.trans hR.toBs.sb_le_b
  · rw [WeightFamilies.PPv_rec T, eRR, ← hR.sb_sq]
    exact mul_le_mul (hR.toBs.rd_pow_le (by norm_num)) hR.toBs.PP_le_sb hR.PP_pos.le hR.sb_pos.le
  · have h1 : (DF (runOf T S hZ).ka : ℝ) ≤ 4 * ((D.R.f : ℝ) * D.R.r) * L.sc.b :=
      (DF_le_size _).trans (ka_le T S hZ)
    have h2 := hR.g_gt h1 (g_ge P i)
    exact_mod_cast h2

end Run

end Formalism.MainNotions.Gaps.EtaleWeightGaps.Num

end
end
end
