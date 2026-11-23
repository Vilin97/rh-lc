module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ModelStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AtPtsImp
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportSt
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
import Development.AbelianVarietyTheory.Definitions.Divisors.SumExpSt
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtPtsImp
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtPtsStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ParOfFurtherStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ParOfHyp
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowsBigStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WtsOkStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParameterHeightLtGenus

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie

namespace GlobalTheory.ExpTie

theorem parOf_h_lt_g {D : D7} (L : SizeData₂ D) (P : ParameterChoice' D L) (j : Fin D.R.m) (a : Fin 2) :
    (parOf L j).h < (D.host.g a : ℝ) := by
  have hx : 1 < L.sc.x := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have hL0 : 0 < L.sc.L := by unfold Scale.L; exact Real.rpow_pos_of_pos hx0 _
  have hb : L.sc.b = Real.exp L.sc.L := rfl
  have hb1 : 1 < L.sc.b := by
    have := Real.add_one_lt_exp (ne_of_gt hL0)
    rw [hb]; linarith
  have hb0 : 0 < L.sc.b := by linarith
  have hb'0 : 0 < L.sc.b' := by
    unfold Scale.b' Scale.a Scale.X' Scale.b
    positivity
  have hS0 : 0 < L.Sc := L.Sc_pos
  have hη0 : 0 < L.etaSz := L.etaSz_pos
  have hm2 : 2 ≤ D.R.m := D.R.two_le_m
  have hmk : D.R.m + 3 ≤ D.R.k := D.R.m_add_three_le_k
  have ht1 : 1 ≤ D.R.t := by have := D.R.three_m_lt_t; omega
  have hn1 : 1 ≤ D.R.n := Formalism.HC.Frame.ord_pos _
  have hmR : (2 : ℝ) ≤ (D.R.m : ℝ) := by exact_mod_cast hm2
  have hmkR : (D.R.m : ℝ) + 3 ≤ (D.R.k : ℝ) := by exact_mod_cast hmk
  have htR : (1 : ℝ) ≤ (D.R.t : ℝ) := by exact_mod_cast ht1
  have hnR : (1 : ℝ) ≤ (D.R.n : ℝ) := by exact_mod_cast hn1

  set den : ℝ := (D.R.n : ℝ) * (D.R.t : ℝ) ^ 2 * ((D.R.N D.R.m : ℝ) + D.R.t) * L.sc.L ^ 2 +
    (D.R.k : ℝ) * (D.R.n : ℝ) ^ 2 * (L.Sc + D.R.t + L.sc.L) with hden
  have hd1 : 0 ≤ (D.R.n : ℝ) * (D.R.t : ℝ) ^ 2 * ((D.R.N D.R.m : ℝ) + D.R.t) * L.sc.L ^ 2 := by positivity
  have hn2 : (1 : ℝ) ≤ (D.R.n : ℝ) ^ 2 := by nlinarith
  have hd2 : (D.R.m : ℝ) ≤ (D.R.k : ℝ) * (D.R.n : ℝ) ^ 2 * (L.Sc + D.R.t + L.sc.L) := by
    have h1 : (1 : ℝ) ≤ (D.R.n : ℝ) ^ 2 * (L.Sc + D.R.t + L.sc.L) := by nlinarith
    have hk0 : (0 : ℝ) ≤ (D.R.k : ℝ) := by positivity
    nlinarith
  have hdm : (D.R.m : ℝ) ≤ den := by rw [hden]; linarith
  have hden0 : 0 < den := by linarith
  have hls : LevelStarExponents.lStar L = (D.R.m : ℝ) * L.sc.b / den := rfl
  have hl0 : 0 < LevelStarExponents.lStar L := by rw [hls]; positivity
  have hlb : LevelStarExponents.lStar L ≤ L.sc.b := by
    rw [hls, div_le_iff₀ hden0]
    nlinarith
  have hbl : 0 < L.sc.b / LevelStarExponents.lStar L := div_pos hb0 hl0
  have h1 := P.lstar1
  have h2 := P.t_le_eta

  have hh : (parOf L j).h = L.sc.b + L.Sc + L.etaSz + (D.R.t : ℝ) + 1 := rfl
  have hh3 : (parOf L j).h < 3 * L.sc.b + 1 := by rw [hh]; linarith

  have hkb : 1 ≤ (D.R.k : ℝ) * L.sc.b := by nlinarith
  have hk8 : (D.R.k : ℝ) * L.sc.b ≤ ((D.R.k : ℝ) * L.sc.b) ^ 8 := le_self_pow₀ hkb (by norm_num)
  have h3 : 3 * L.sc.b + 1 ≤ (D.R.k : ℝ) * L.sc.b := by nlinarith
  obtain ⟨Y, hY, -, -, hg⟩ := P.g_Y
  have := (hg a).1
  linarith

end GlobalTheory.ExpTie

end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtPtsHLtG

section

@[expose] public section



section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie
namespace GlobalTheory.ExpTie
theorem atPts_h_lt_g_alt : _root_.GlobalTheory.BigOn.AtPtsAlt fun Fm x _ i _ =>
    ∀ (j : Fin (Fm.D x i).R.m) a, (GlobalTheory.ExpTie.parOf (Fm.L x i) j).h < ((Fm.D x i).host.g a : ℝ) :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ =>
    ⟨0, fun x hx _ i _ _ _ j a => parOf_h_lt_g (Fm.L x i) (Fm.params x hx i) j a⟩⟩⟩
end GlobalTheory.ExpTie
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtPtsHLtGStatement

section

@[expose] public section



section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie

theorem _root_.GlobalTheory.T.parOf_height_lt_genus_at_pts : _root_.GlobalTheory.BigOn.AtPtsAlt fun Fm x _ i _ => ∀ (j : Fin (Fm.D x i).R.m) a, (GlobalTheory.ExpTie.parOf (Fm.L x i) j).h < ((Fm.D x i).host.g a : ℝ) := by
  first | exact @_root_.GlobalTheory.ExpTie.atPts_h_lt_g_alt | exact _root_.GlobalTheory.ExpTie.atPts_h_lt_g_alt | (intros; apply _root_.GlobalTheory.ExpTie.atPts_h_lt_g_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ParOfHypStatement

section

@[expose] public section



section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie

theorem _root_.GlobalTheory.T.parOf_hyp_at_pts : _root_.GlobalTheory.BigOn.AtPtsAlt fun Fm x _ i _ => ∀ j : Fin (Fm.D x i).R.m, (GlobalTheory.ExpTie.parOf (Fm.L x i) j).Hyp := by
  first | exact @_root_.GlobalTheory.ExpTie.parOf_hyp_alt | exact _root_.GlobalTheory.ExpTie.parOf_hyp_alt | (intros; apply _root_.GlobalTheory.ExpTie.parOf_hyp_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NumSt

section

@[expose] public section



section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
namespace GlobalTheory.ExpTie
theorem numSt_alt : _root_.GlobalTheory.ExpTie.NumStAlt := by
  have H := _root_.GlobalTheory.ExpTie.atPts_and_alt (_root_.GlobalTheory.ExpTie.atPts_and_alt (_root_.GlobalTheory.ExpTie.atPts_and_alt _root_.GlobalTheory.T.parOf_hyp_at_pts _root_.GlobalTheory.T.exists_large_parameter_estimates_at_pts) (_root_.GlobalTheory.ExpTie.atPts_and_alt _root_.GlobalTheory.T.parameter_large_at_all_points _root_.GlobalTheory.T.parOf_height_lt_genus_at_pts))
    (_root_.GlobalTheory.ExpTie.atPts_and_alt _root_.GlobalTheory.T.isLamPrime_at_all_points _root_.GlobalTheory.T.weight_lambda_shift_nonneg')
  refine _root_.GlobalTheory.ExpTie.atPts_mono H fun Fm x hx i p h j => ?_
  obtain ⟨⟨⟨hH, hR⟩, ⟨hL, hB⟩⟩, ⟨hF, hW⟩⟩ := h
  obtain ⟨W, hOk, hlam, hbox, hT, hSp⟩ := hW j
  refine ⟨parOf (Fm.L x i) j, W, ?_, hH j, hL j, hOk, hR j⟩
  exact
    { k := rfl, m := rfl, t := rfl, f := rfl
      card := Nat.card_eq_fintype_card.trans (Fm.D x i).what₂.card_Tau
      Nr := rfl, x := rfl, log := rfl, b := rfl
      lam := hlam, forced := hF j, box := hbox, thick := hT, special := hSp, big := hB j }
end GlobalTheory.ExpTie
end
end
end
end
