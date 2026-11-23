module

public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteKernelNodeRankLeTotalRank
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.FiniteDimensionalNablaSq
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopNodeFormWeightAbsLeLinearStatement
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogBranchingConstantSqLe

section

@[expose] public section

open Formalism.BasicNotions

namespace GlobalTheory.BranchBound

theorem branching_D1_le_weight_difference (n : ℕ) (lam : DomWeight (n + 1)) (sg : DomWeight n) :
    Formalism.MainNotions.PrimeDegreeVariant.D1 rfl lam sg ≤ lam.w 0 - lam.w (Fin.last n) := by
  let g : ℕ → ℤ := fun k => if hk : k < n + 1 then lam.w ⟨k, hk⟩ else 0
  have h1 : Formalism.MainNotions.PrimeDegreeVariant.D1 rfl lam sg ≤ ∑ i : Fin n, (g i - g (i + 1)) := by
    unfold Formalism.MainNotions.PrimeDegreeVariant.D1
    refine Finset.sum_le_sum fun i _ => ?_
    have a : g i = lam.w ⟨i.1, by omega⟩ := by simp [g, show i.1 < n + 1 by omega]
    have b : g (i + 1) = lam.w ⟨i.1 + 1, by omega⟩ := by simp [g, show i.1 + 1 < n + 1 by omega]
    rw [a, b]
    exact min_le_left _ _
  have h2 : ∑ i : Fin n, (g i - g (i + 1)) = g 0 - g n := by
    rw [Fin.sum_univ_eq_sum_range (fun k => g k - g (k + 1)) n]
    exact Finset.sum_range_sub' g n
  have a0 : g 0 = lam.w 0 := by simp [g]
  have an : g n = lam.w (Fin.last n) := by simp [g]; rfl
  rw [h2, a0, an] at h1
  exact h1

end GlobalTheory.BranchBound

namespace GlobalTheory.BranchBound

theorem finrank_delSq_le (N : ℕ) (lam : DomWeight N) (B : ℝ) (hB : 1 ≤ B)
    (hw : ∀ i, |((lam.w i : ℤ) : ℝ)| ≤ B) :
    (Module.finrank ℂ (delSq ℂ N lam) : ℝ) ≤ (6 * B) ^ (N * N) := by
  have hq := GlobalTheory.WeylDimGL.finrank_delSq ℂ N lam
  rw [GlobalTheory.WeylDimGL.weylDim_eq_prod_Ioi] at hq
  have hr : (Module.finrank ℂ (delSq ℂ N lam) : ℝ) = ∏ i : Fin N, ∏ j ∈ Finset.Ioi i,
      (((lam.w i : ℝ) - (lam.w j : ℝ) + ((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) / (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ))) := by
    have := congrArg (Rat.cast : ℚ → ℝ) hq
    push_cast at this
    exact this
  rw [hr]
  have h6 : (1 : ℝ) ≤ 6 * B := by linarith
  have hf : ∀ i : Fin N, ∀ j ∈ Finset.Ioi i,
      0 ≤ ((lam.w i : ℝ) - (lam.w j : ℝ) + ((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) / (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) ∧
      ((lam.w i : ℝ) - (lam.w j : ℝ) + ((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) / (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) ≤ 6 * B := by
    intro i j hj
    have hij : i < j := Finset.mem_Ioi.mp hj
    have hlt : ((i : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by exact_mod_cast hij
    have hanti : (lam.w j : ℝ) ≤ lam.w i := by exact_mod_cast lam.anti hij.le
    have hbi := abs_le.mp (hw i)
    have hbj := abs_le.mp (hw j)
    have hk : (0 : ℝ) < ((j : ℕ) : ℝ) - ((i : ℕ) : ℝ) := by linarith
    constructor
    · apply div_nonneg <;> linarith
    · rw [div_le_iff₀ hk]
      nlinarith
  calc ∏ i : Fin N, ∏ j ∈ Finset.Ioi i,
      (((lam.w i : ℝ) - (lam.w j : ℝ) + ((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) / (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)))
        ≤ ∏ _i : Fin N, (6 * B) ^ N := by
          refine Finset.prod_le_prod₀ (fun i _ => Finset.prod_nonneg fun j hj => (hf i j hj).1) fun i _ => ?_
          calc _ ≤ ∏ _j ∈ Finset.Ioi i, (6 * B) :=
                Finset.prod_le_prod₀ (fun j hj => (hf i j hj).1) fun j hj => (hf i j hj).2
            _ = (6 * B) ^ (Finset.Ioi i).card := Finset.prod_const _
            _ ≤ (6 * B) ^ N := by
                apply pow_le_pow_right₀ h6
                simpa using Finset.card_le_univ (Finset.Ioi i)
      _ = (6 * B) ^ (N * N) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, mul_comm]

end GlobalTheory.BranchBound

namespace GlobalTheory.BranchBound

theorem log_brBd_sq_le : ∀ {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (B : ℝ), 1 ≤ B →
    (N : ℝ) ≤ B → (∀ i, |((lam.w i : ℤ) : ℝ)| ≤ B) →
    Real.log (Formalism.MainNotions.PrimeDegreeVariant.brBd h lam sg ^ 2) ≤ 5 * N * B * Real.log (6 * B) := by
  intro n N h lam sg B hB hN hw
  subst h
  have hNB : ((n + 1 : ℕ) : ℝ) ≤ B := hN
  have hN0 : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by positivity
  have hL : 0 < Real.log (6 * B) := Real.log_pos (by linarith)
  have hR : 0 ≤ 5 * ((n + 1 : ℕ) : ℝ) * B * Real.log (6 * B) := by positivity

  have hsp : lam.spread = lam.w 0 - lam.w (Fin.last n) + ((n + 1 : ℕ) : ℤ) := by
    unfold DomWeight.spread
    rw [dite_eq_left (Nat.succ_pos n)]
    rfl
  have h0 := abs_le.mp (hw 0)
  have hl := abs_le.mp (hw (Fin.last n))
  have hanti : (lam.w (Fin.last n) : ℝ) ≤ lam.w 0 := by exact_mod_cast lam.anti (Fin.zero_le _)
  set s : ℝ := (((2 * lam.spread : ℤ)) : ℝ) with hs
  have hsR : s = 2 * ((lam.w 0 : ℝ) - lam.w (Fin.last n) + ((n + 1 : ℕ) : ℝ)) := by
    rw [hs, hsp]; push_cast; ring
  have hs2 : 2 ≤ s := by rw [hsR]; push_cast at hNB ⊢; linarith
  have hs6 : s ≤ 6 * B := by rw [hsR]; push_cast at hNB ⊢; linarith
  have hls0 : 0 ≤ Real.log s := Real.log_nonneg (by linarith)
  have hls : Real.log s ≤ Real.log (6 * B) := Real.log_le_log (by linarith) hs6

  have hD := branching_D1_le_weight_difference n lam sg
  have hDR : ((Formalism.MainNotions.PrimeDegreeVariant.D1 rfl lam sg : ℤ) : ℝ) ≤ 2 * B := by
    have : ((Formalism.MainNotions.PrimeDegreeVariant.D1 rfl lam sg : ℤ) : ℝ) ≤ (lam.w 0 : ℝ) - lam.w (Fin.last n) := by exact_mod_cast hD
    linarith
  set e : ℝ := ((((n + 1 : ℕ) : ℤ) * Formalism.MainNotions.PrimeDegreeVariant.D1 rfl lam sg : ℤ) : ℝ) with he
  have heR : e = ((n + 1 : ℕ) : ℝ) * ((Formalism.MainNotions.PrimeDegreeVariant.D1 rfl lam sg : ℤ) : ℝ) := by rw [he]; push_cast; ring
  have hel : e * Real.log s ≤ 2 * ((n + 1 : ℕ) : ℝ) * B * Real.log (6 * B) := by
    rcases le_or_gt e 0 with he0 | he0
    · have : e * Real.log s ≤ 0 := mul_nonpos_of_nonpos_of_nonneg he0 hls0
      have : 0 ≤ 2 * ((n + 1 : ℕ) : ℝ) * B * Real.log (6 * B) := by positivity
      linarith
    · have he2 : e ≤ 2 * ((n + 1 : ℕ) : ℝ) * B := by
        rw [heR]; nlinarith
      calc e * Real.log s ≤ (2 * ((n + 1 : ℕ) : ℝ) * B) * Real.log (6 * B) :=
            mul_le_mul he2 hls hls0 (by positivity)
        _ = _ := by ring

  have hc : Formalism.MainNotions.PrimeDegreeVariant.cBd rfl lam sg = s ^ e := rfl
  have hcpos : 0 < s ^ e := Real.rpow_pos_of_pos (by linarith) e
  set d : ℝ := (Module.finrank ℂ (delSq ℂ (n + 1) lam) : ℝ) with hd
  have hd0 : 0 ≤ d := by positivity
  have hb2 : Formalism.MainNotions.PrimeDegreeVariant.brBd rfl lam sg ^ 2 = (s ^ e) ^ 2 * d := by
    unfold Formalism.MainNotions.PrimeDegreeVariant.brBd
    rw [hc, mul_pow, Real.sq_sqrt hd0]
  rw [hb2]
  rcases eq_or_lt_of_le hd0 with hd0' | hdpos
  · rw [← hd0', mul_zero, Real.log_zero]; exact hR
  have hdle := finrank_delSq_le (n + 1) lam B hB hw
  have hlogd : Real.log d ≤ (((n + 1) * (n + 1) : ℕ) : ℝ) * Real.log (6 * B) := by
    rw [← Real.log_pow]
    exact Real.log_le_log hdpos hdle
  have hlogd' : Real.log d ≤ ((n + 1 : ℕ) : ℝ) * B * Real.log (6 * B) := by
    refine hlogd.trans ?_
    push_cast
    have : (((n : ℝ) + 1) * ((n : ℝ) + 1)) ≤ ((n : ℝ) + 1) * B := by
      push_cast at hNB hN0
      exact mul_le_mul_of_nonneg_left hNB hN0
    nlinarith
  rw [Real.log_mul (by positivity) hdpos.ne', Real.log_pow, Real.log_rpow (by linarith)]
  push_cast at hel hlogd' ⊢
  nlinarith

end GlobalTheory.BranchBound
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogBranchingConstantSqLeStatement

section

@[expose] public section

open Formalism.BasicNotions


theorem _root_.GlobalTheory.T.log_branching_constant_sq_le : ∀ {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (B : ℝ), 1 ≤ B → (N : ℝ) ≤ B → (∀ i, |((lam.w i : ℤ) : ℝ)| ≤ B) → Real.log (Formalism.MainNotions.PrimeDegreeVariant.brBd h lam sg ^ 2) ≤ 5 * N * B * Real.log (6 * B) := by
  first | exact @GlobalTheory.BranchBound.log_brBd_sq_le | exact GlobalTheory.BranchBound.log_brBd_sq_le | (intros; apply GlobalTheory.BranchBound.log_brBd_sq_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanBranchingConstantBound

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.InfSize

theorem bigN_le {D : D7} {large₂ : SizeData₂ D} (hs : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂) : (bigN D : ℝ) ≤ 10 * large₂.sc.b := by
  obtain ⟨-, -, hf, hm, -, hb, -⟩ := hs
  have hd : 1 ≤ D.host.d := D.host.hyp.2.1.one_lt.le
  have hm1 : 1 ≤ D.R.m := by omega
  have hf1 : 1 ≤ D.R.f := le_trans (Nat.one_le_pow _ _ (by omega)) hf
  have hN1 : 1 ≤ D.R.N D.R.m := by unfold Ranks.N; have := D.R.m_add_three_le_k; omega
  have key : bigN D ≤ 10 * (D.R.m * D.R.f * D.R.N D.R.m ^ 2 * D.host.d) := by
    have e1 : D.R.N D.R.m ≤ D.R.N D.R.m ^ 2 := Nat.le_self_pow (by norm_num) _
    have e2 : D.R.m * D.R.N D.R.m ≤ D.R.m * D.R.f * D.R.N D.R.m ^ 2 * D.host.d := by
      calc D.R.m * D.R.N D.R.m = D.R.m * 1 * D.R.N D.R.m * 1 := by ring
        _ ≤ D.R.m * D.R.f * D.R.N D.R.m ^ 2 * D.host.d := by gcongr
    have e3 : bigN D ≤ 10 * (D.R.m * D.R.N D.R.m) := by
      have hk := D.R.m_add_three_le_k
      have s1 : bigN D ≤ D.R.k + D.R.m * (D.R.t + (D.R.k + D.R.m + 6) + 1) := by
        simp only [bigN, sLen, Ranks.r]; gcongr; omega
      have a1 : D.R.k ≤ D.R.m * D.R.k := Nat.le_mul_of_pos_left _ (by omega)
      have a2 : D.R.m * D.R.t ≤ D.R.m * (D.R.m * D.R.t) := Nat.le_mul_of_pos_left _ (by omega)
      have a3 : D.R.m ≤ D.R.m * D.R.m := Nat.le_mul_of_pos_left _ (by omega)
      refine s1.trans ?_
      simp only [Ranks.N]
      nlinarith
    omega
  have : (bigN D : ℝ) ≤ 10 * ((D.R.m * D.R.f * D.R.N D.R.m ^ 2 * D.host.d : ℕ) : ℝ) := by exact_mod_cast key
  push_cast at this
  linarith

theorem log_prod_le {ι : Type} [Fintype ι] (a : ι → ℝ) (c : ℝ) (h0 : ∀ i, 0 ≤ a i) (hc : 0 ≤ c)
    (h : ∀ i, Real.log (a i) ≤ c) : Real.log (∏ i, a i) ≤ Fintype.card ι * c := by
  by_cases hz : ∃ i, a i = 0
  · obtain ⟨i, hi⟩ := hz
    rw [Finset.prod_eq_zero (Finset.mem_univ i) hi, Real.log_zero]
    positivity
  · push_neg at hz
    rw [Real.log_prod (fun i _ => hz i)]
    calc ∑ i, Real.log (a i) ≤ ∑ _i : ι, c := Finset.sum_le_sum fun i _ => h i
      _ = Fintype.card ι * c := by simp

end GlobalTheory.InfSize


open GlobalTheory.InfSize in
theorem GlobalTheory.InfSize.main : ∃ CF0 : ℝ, ∀ CF : ℝ, CF0 ≤ CF → ∃ K0 : ℝ, ∀ ε : ℝ, ∃ x₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x →
    ∀ (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m)
      (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), HidaSetting large₂ R F →
      ∀ ch : Choice R, ch.Is → ch.AtScale CF large₂.sc.b →
        1 ≤ large₂.sc.b ∧ Real.log (∏ τ, Formalism.MainNotions.PrimeDegreeVariant.brBd ch.G.sp.topDec.rank (wt ch.G (.top D.R.m) τ)
          (listedWt ch.G (.grid D.R.m D.R.m) τ) ^ 2) ≤ K0 * D.R.f * (bigN D : ℝ) * large₂.sc.b * Real.log large₂.sc.b := by
  obtain ⟨K1, hK1⟩ := GlobalTheory.T.topNodeFormWeight_abs_le_linear
  set c : ℝ := |K1| + 10 with hc
  set c2 : ℝ := Real.log (6 * c) + 1 with hc2
  refine ⟨0, fun CF _ => ⟨5 * c * c2, fun ε => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch _ hAt => ?_⟩⟩⟩
  have hc10 : 10 ≤ c := by rw [hc]; linarith [abs_nonneg K1]
  have hc2p : 1 ≤ c2 := by
    rw [hc2]; have : 0 ≤ Real.log (6 * c) := Real.log_nonneg (by linarith)
    linarith

  have hL : 1 ≤ large₂.sc.L := by
    unfold Scale.L
    exact Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le
  have hlb : Real.log large₂.sc.b = large₂.sc.L := Real.log_exp _
  have hb1 : 1 ≤ large₂.sc.b := Real.one_le_exp (by linarith)
  refine ⟨hb1, ?_⟩
  have hlog1 : 1 ≤ Real.log large₂.sc.b := hlb ▸ hL

  have hcg : ch.sc.cGap = 1 := by rw [hAt]
  have hw := hK1 D large₂ hS.size ch.G hcg
  have hNb := bigN_le hS.size
  have hrk : (ch.G.V (.top D.R.m)).rank ≤ bigN D := GlobalTheory.DefRank.rank_le_bigN ch.G (.top D.R.m) (le_refl D.R.m)
  have hrkR : ((ch.G.V (.top D.R.m)).rank : ℝ) ≤ bigN D := by exact_mod_cast hrk
  set B : ℝ := c * large₂.sc.b with hB
  have hB1 : 1 ≤ B := by rw [hB]; nlinarith
  have hlogB : Real.log (6 * B) ≤ c2 * Real.log large₂.sc.b := by
    rw [hB, ← mul_assoc, Real.log_mul (by positivity) (by positivity), hc2]
    have : 0 ≤ Real.log (6 * c) := Real.log_nonneg (by linarith)
    nlinarith
  have hNB : ((ch.G.V (.top D.R.m)).rank : ℝ) ≤ B := by
    rw [hB]; nlinarith
  have hwB : ∀ τ i, |(((wt ch.G (.top D.R.m) τ).w i : ℤ) : ℝ)| ≤ B := fun τ i => by
    refine (hw τ i).trans ?_
    rw [hB]; exact mul_le_mul_of_nonneg_right (by rw [hc]; linarith [le_abs_self K1]) (by linarith)
  have hτ : ∀ τ, Real.log (Formalism.MainNotions.PrimeDegreeVariant.brBd ch.G.sp.topDec.rank (wt ch.G (.top D.R.m) τ)
      (listedWt ch.G (.grid D.R.m D.R.m) τ) ^ 2) ≤ 5 * c * c2 * (bigN D : ℝ) * large₂.sc.b * Real.log large₂.sc.b := by
    intro τ
    refine (GlobalTheory.T.log_branching_constant_sq_le _ _ _ B hB1 hNB (hwB τ)).trans ?_
    have hl6 : 0 ≤ Real.log (6 * B) := Real.log_nonneg (by linarith)
    calc 5 * ((ch.G.V (.top D.R.m)).rank : ℝ) * B * Real.log (6 * B) ≤ 5 * (bigN D : ℝ) * B * Real.log (6 * B) := by
          gcongr
      _ ≤ 5 * (bigN D : ℝ) * B * (c2 * Real.log large₂.sc.b) := by gcongr
      _ = 5 * c * c2 * (bigN D : ℝ) * large₂.sc.b * Real.log large₂.sc.b := by rw [hB]; ring
  have h0 : 0 ≤ 5 * c * c2 * (bigN D : ℝ) * large₂.sc.b * Real.log large₂.sc.b := by positivity
  refine (log_prod_le _ _ (fun τ => sq_nonneg _) h0 hτ).trans (le_of_eq ?_)
  rw [D.what₂.card_Tau]
  ring
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanBranchingConstantBoundStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.archimedean_branching_constant_bound : ∃ CF0 : ℝ, ∀ CF : ℝ, CF0 ≤ CF → ∃ K0 : ℝ, ∀ ε : ℝ, ∃ x₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x →
    ∀ (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m)
      (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), HidaSetting large₂ R F →
      ∀ ch : Choice R, ch.Is → ch.AtScale CF large₂.sc.b →
        1 ≤ large₂.sc.b ∧ Real.log (∏ τ, Formalism.MainNotions.PrimeDegreeVariant.brBd ch.G.sp.topDec.rank (wt ch.G (.top D.R.m) τ)
          (listedWt ch.G (.grid D.R.m D.R.m) τ) ^ 2) ≤ K0 * D.R.f * (bigN D : ℝ) * large₂.sc.b * Real.log large₂.sc.b := by
  first | exact @GlobalTheory.InfSize.main | exact GlobalTheory.InfSize.main | (intros; apply GlobalTheory.InfSize.main <;> assumption)
end
end
