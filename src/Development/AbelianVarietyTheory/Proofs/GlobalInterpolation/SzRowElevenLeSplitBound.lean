module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RbSNumeric
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowAndImp
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowEtaBounds
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowEtaLeW
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
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowLStar
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitChoiceSizeNodesStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowAndImp
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowCondQdPdeStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ConstMulRpowMulLogPowLeRpow
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GoodTopCountLeConstMulLog
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowRankSizesStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowSizeDelStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogAddRpowMulLogPowLeRpow
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowCardWordsLe
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowSizeKRelStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowSizeWSizeBmSizeXppStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitChoiceSizeEta

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem szRow_sizeEta : SzRow (fun _ _ L => SizeEta L) := by
  refine SzRow.imp (SzRow.and szRow_eta_bounds (SzRow.and szRow_eta_le_w szRow_rbS)) ?_
  rintro C cD ch D L - - ⟨⟨h1, h2, h3, h4, h5⟩, ⟨h6, h7, h8, h9⟩, h10⟩
  exact ⟨h3, h1, h2, h4, h5, h6, h7, h8, h10⟩

end GlobalTheory.EX
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitChoiceSizeEtaStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

theorem _root_.GlobalTheory.T.explicitChoice_sizeEta : SzRow (fun _ _ L => SizeEta L) := by
  first | exact @GlobalTheory.EX.szRow_sizeEta | exact GlobalTheory.EX.szRow_sizeEta | (intros; apply GlobalTheory.EX.szRow_sizeEta <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitChoiceSizeLstar

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem szRow_sizeLstar : SzRow (fun _ _ L => SizeLstar L) := szRow_lStar

end GlobalTheory.EX
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitChoiceSizeLstarStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

theorem _root_.GlobalTheory.T.explicitChoice_sizeLstar : SzRow (fun _ _ L => SizeLstar L) := by
  first | exact @GlobalTheory.EX.szRow_sizeLstar | exact GlobalTheory.EX.szRow_sizeLstar | (intros; apply GlobalTheory.EX.szRow_sizeLstar <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowLaRhoBot

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem szRow_la_rho_bot : SzRow (fun _ _ L => SizeLa L ∧ SizeRho L ∧ SizeBot L) := by
  intro eps he he' C hC
  have hLa1 : 1 ≤ C.GK.La := hC.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ (by simp [FC.cMid])
  obtain ⟨CN, x1, h1⟩ := GlobalTheory.topCount_and_lambda_bounds eps he he'
  obtain ⟨x2, h2⟩ := GlobalTheory.const_mul_rpow_mul_log_pow_le_rpow eps (eps + eps / 100)
    (2 * C.GK.La * CN ^ 2) 2 (by linarith)
  obtain ⟨x3, h3⟩ := GlobalTheory.const_mul_rpow_mul_log_pow_le_rpow
    ((2 + 8 * eps + eps / 100) + -(eps / 8) + eps + (eps + eps / 100)) (-2 + (9 / 2 + 10 * eps)) 32 0 (by linarith)
  obtain ⟨x4, h4⟩ := GlobalTheory.const_mul_rpow_mul_log_pow_le_rpow
    (eps / 100 + (eps + eps / 100)) (-2 + (9 / 2 + 10 * eps)) 2 1 (by linarith)
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨max (max (max x1 x2) (max x3 x4)) 1, ?_⟩⟩⟩
  intro D L hε hx hV
  simp only [max_le_iff] at hx
  obtain ⟨⟨⟨hx1, hx2⟩, hx3, hx4⟩, hone⟩ := hx
  have hpos : 0 < L.sc.x := by linarith
  obtain ⟨hlo, hhi⟩ := (h1 L.sc hε hx1).2.2 C.GK hLa1
  rw [← hV.La_eq] at hlo hhi
  have hup : L.LaG ≤ L.sc.x ^ (eps + eps / 100) := by
    have := h2 _ hx2
    rw [hε] at hhi
    calc L.LaG ≤ _ := hhi
      _ = 2 * C.GK.La * CN ^ 2 * L.sc.x ^ eps * Real.log L.sc.x ^ 2 := by ring
      _ ≤ _ := this
  refine ⟨⟨hlo, ?_⟩, ?_, ?_⟩
  · simpa only [szTh, hε] using hup
  · have hn := hV.ranks.n_le
    obtain ⟨-, -, ⟨hk, -⟩, -⟩ := hV.ranks
    have h3' := h3 _ hx3
    have h4' := h4 _ hx4
    simp only [Real.rpow_add hpos, pow_zero, pow_one, mul_one] at h3' h4'
    rw [← Real.rpow_add hpos 2, ← Real.rpow_add hpos (2 + 8 * eps) (eps / 100), ← Real.rpow_add hpos (9 / 2),
      ← Real.rpow_add hpos eps (eps / 100)] at h3'
    rw [← Real.rpow_add hpos (9 / 2), ← Real.rpow_add hpos eps (eps / 100)] at h4'
    have hL0 : 0 ≤ L.LaG := le_trans (Real.rpow_pos_of_pos hpos _).le hlo
    unfold SizeRho szNst szTh Scale.delta1
    rw [hε] at hn hk ⊢
    have hkpos : (0 : ℝ) < D.R.k := lt_of_lt_of_le (Real.rpow_pos_of_pos hpos _) hk
    have hlog : 0 ≤ Real.log L.sc.x := Real.log_nonneg hone
    rw [← add_div, div_le_iff₀ hkpos]
    have hA : 4 * (2 * (D.R.n : ℝ) * L.sc.x ^ (-(eps / 8))) * L.sc.x ^ eps * L.LaG ≤
        4 * (2 * (2 * L.sc.x ^ (2 + 8 * eps + eps / 100)) * L.sc.x ^ (-(eps / 8))) * L.sc.x ^ eps *
          L.sc.x ^ (eps + eps / 100) := by gcongr
    have hB : L.sc.x ^ (eps / 100) * Real.log L.sc.x * L.LaG ≤
        L.sc.x ^ (eps / 100) * Real.log L.sc.x * L.sc.x ^ (eps + eps / 100) := by gcongr
    have hK : L.sc.x ^ (-2 : ℝ) * L.sc.x ^ (9 / 2 + 10 * eps) ≤ L.sc.x ^ (-2 : ℝ) * D.R.k := by gcongr
    linarith
  · intro t
    have := hV.bT_le t
    unfold szNst
    exact this

end GlobalTheory.EX
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowLaRhoBotStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

theorem _root_.GlobalTheory.T.sizes_sizeLa_sizeRho_sizeBot : SzRow (fun _ _ L => SizeLa L ∧ SizeRho L ∧ SizeBot L) := by
  first | exact @GlobalTheory.EX.szRow_la_rho_bot | exact GlobalTheory.EX.szRow_la_rho_bot | (intros; apply GlobalTheory.EX.szRow_la_rho_bot <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowSizeGSizeWords

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem log_le_of_le_two_mul_pow_eight {x a y k g : ℝ} (hx : 1 < x) (ha : a ≤ 5) (hy : 0 ≤ y) (hk0 : 0 < k)
    (hk : k ≤ 2 * x ^ a) (hg0 : 0 < g) (hg : g ≤ 2 * (k * Real.exp y) ^ 8) :
    Real.log g ≤ 40 * Real.log x + 9 * y + 9 := by
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hl2 : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9
    linarith
  have h1 : Real.log k ≤ Real.log 2 + a * Real.log x := by
    have := Real.log_le_log hk0 hk
    rwa [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hx0 a).ne', Real.log_rpow hx0] at this
  have h2 : Real.log g ≤ Real.log 2 + 8 * (Real.log k + y) := by
    have := Real.log_le_log hg0 hg
    rwa [Real.log_mul (by norm_num) (by positivity), Real.log_pow,
      Real.log_mul hk0.ne' (Real.exp_pos y).ne', Real.log_exp, Nat.cast_ofNat] at this
  have h3 : a * Real.log x ≤ 5 * Real.log x := mul_le_mul_of_nonneg_right ha hlx.le
  linarith

theorem szRow_sizeG : SzRow (fun _ _ L => SizeG L) := by
  intro eps he he' C _
  obtain ⟨x0, hx0⟩ := GlobalTheory.log_add_rpow_mul_log_pow_le_rpow eps (eps + eps / 100) 40 9 1 0 he.le
    (by linarith) one_pos
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨x0, ?_⟩⟩⟩
  intro D L hLe hx hV i j
  obtain ⟨-, -, ⟨hk1, hk2⟩, -⟩ := hV.ranks
  obtain ⟨-, -, -, -, hg, -⟩ := hV.host
  have hx1 := L.sc.one_lt_alt
  have hxp : 0 < L.sc.x := by linarith
  have hk0 : (0 : ℝ) < D.R.k := lt_of_lt_of_le (Real.rpow_pos_of_pos hxp _) hk1
  have hb0 : 0 < L.sc.b := Real.exp_pos _
  refine ⟨(hg i).1, (hg i).2.trans (by linarith [(hg j).1]), ?_⟩
  have hg0 : (0 : ℝ) < D.host.g i := lt_of_lt_of_le (by positivity) (hg i).1
  have hL0 : 0 ≤ L.sc.L := (Real.rpow_pos_of_pos hxp _).le
  have h1 := log_le_of_le_two_mul_pow_eight hx1 (by rw [hLe]; linarith) hL0 hk0 hk2 hg0 (hg i).2
  have h2 := hx0 L.sc.x hx
  have h3 : L.sc.x ^ szTh L * L.sc.L = L.sc.x ^ (eps + eps / 100) := by
    simp only [szTh, Scale.L, hLe]
    rw [← Real.rpow_add hxp, add_comm]
  rw [h3]
  simp only [Scale.L, hLe] at h1
  rw [pow_zero, mul_one, one_mul] at h2
  exact h1.trans h2

theorem szRow_sizeG_sizeWords : SzRow (fun _ _ L => SizeG L ∧ SizeWords L) :=
  szRow_and_imp.1 _ _ szRow_sizeG szRow_card_words_le

end GlobalTheory.EX
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowSizeGSizeWordsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

theorem _root_.GlobalTheory.T.sizes_sizeG_sizeWords : SzRow (fun _ _ L => SizeG L ∧ SizeWords L) := by
  first | exact @GlobalTheory.EX.szRow_sizeG_sizeWords | exact GlobalTheory.EX.szRow_sizeG_sizeWords | (intros; apply GlobalTheory.EX.szRow_sizeG_sizeWords <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowElevenLeSplitBound

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

private theorem szRow_eleven_le_splitBound : SzRow (fun _ D _ => 11 ≤ D.host.splitBound) := by
  intro eps heps _ C _
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨(11 : ℝ) ^ (eps / C.P.Cpde / 5)⁻¹, ?_⟩⟩⟩
  intro D L hε hx hV
  have hH := hV.host
  have hC : (0 : ℝ) < C.P.Cpde := lt_of_lt_of_le one_pos hH.one_le
  have ha : 0 < eps / C.P.Cpde / 5 := by positivity
  have h1 : (11 : ℝ) ≤ L.sc.x ^ (eps / C.P.Cpde / 5) := by
    have h2 := Real.rpow_le_rpow (by positivity) hx ha.le
    rwa [Real.rpow_inv_rpow (by norm_num) ha.ne'] at h2
  have h3 : L.sc.x ^ (eps / C.P.Cpde / 5) ≤ L.sc.x ^ (L.sc.ez / 5) := by
    refine Real.rpow_le_rpow_of_exponent_le L.sc.one_lt_alt.le ?_
    have := hH.eps_div_le_ez
    rw [hε] at this
    linarith
  have h4 : 11 ≤ ⌊L.sc.x ^ (L.sc.ez / 5)⌋₊ := Nat.le_floor (by exact_mod_cast h1.trans h3)
  exact h4.trans hH.split_tie

theorem szRow_sizesAt : SzRow (fun _ _ L => SizesAt L) := by
  have h := ((((((((((GlobalTheory.T.sizes_sizeN_sizeM_sizeK_sizeT_sizeTT_sizeDe2_sizeLw.and GlobalTheory.T.sizes_sizeKRel).and GlobalTheory.T.sizes_sizeCond_sizeQD_sizePde).and GlobalTheory.T.sizes_sizeLa_sizeRho_sizeBot).and GlobalTheory.T.explicitChoice_sizeEta).and
    GlobalTheory.T.explicitChoice_sizeNodes).and GlobalTheory.T.explicitChoice_sizeLstar).and GlobalTheory.T.sizes_sizeDel).and GlobalTheory.T.sizes_sizeW_sizeBm_sizeXpp).and GlobalTheory.T.sizes_sizeG_sizeWords).and
    szRow_eleven_le_splitBound)
  refine h.imp ?_
  rintro C cD ch D L - - ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hN, hM, hK, hT, hTT, hDe, hLw⟩, hKR⟩, hCo, hQD, hP⟩, hLa, hRho, hBot⟩, hEta⟩,
    hNo⟩, hLs⟩, hDel⟩, hW, hBm, hX⟩, hG, hWo⟩, h11⟩
  exact ⟨hN, hM, hK, hKR, hT, hCo, hQD, hTT, hLa, hRho, hBot, hDe, hLw, hEta, hNo, hLs, hDel, hW, hBm, hX, hG,
    hP, hWo, h11⟩

end GlobalTheory.EX
end
end
