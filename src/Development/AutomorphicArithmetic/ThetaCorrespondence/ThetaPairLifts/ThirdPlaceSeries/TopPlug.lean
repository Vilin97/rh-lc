module

public import Development.AutomorphicArithmetic.CharacterBoxes.EveryCharacter
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Hyps
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DefiniteSideCondition
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ExplicitFormulaErrorOfHostConditions
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicArithmetic.CharacterBoxes.HalfPlane
public import Development.AutomorphicArithmetic.CharacterBoxes.Supply
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
public import Development.AutomorphicArithmetic.CharacterBoxes.Imports
public import Development.AutomorphicArithmetic.CharacterBoxes.TwistForm
public import Development.AutomorphicArithmetic.ShortNorms.Primes
public import Development.AutomorphicArithmetic.ShortNorms.hostOfFieldOf
public import Development.AutomorphicArithmetic.ShortNorms.supplyOfAdmOf
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Mathlib.Tactic.Linter.Style
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopShapeAlt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopShape
public import Development.AutomorphicArithmetic.CharacterBoxes.ZeroFreeAllOfTopG

-- Source module: Development.AutomorphicArithmetic.CharacterBoxes.Imprimitive

section

@[expose] public section

open Formalism.HC

theorem UpperTheory.Top.imprimitive :
    ZeroFreeAll → ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ), 1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) →
      DirichletCharacter.LFunction χ s ≠ 0 := by
  intro h N _ χ s hs hχs
  have : NeZero χ.conductor := (PChar.of χ).ne
  have hL : DirichletCharacter.LFunction χ.primitiveCharacter s ≠ 0 := h (PChar.of χ) trivial s hs
  have hχ' : χ.primitiveCharacter ≠ 1 ∨ s ≠ 1 := by
    rcases hχs with hχ | hs1
    · left
      intro h1
      apply hχ
      rw [← χ.changeLevel_primitiveCharacter, h1, DirichletCharacter.changeLevel_one]
    · exact Or.inr hs1
  have hrw := DirichletCharacter.LFunction_changeLevel χ.conductor_dvd_level χ.primitiveCharacter hχ'
  rw [χ.changeLevel_primitiveCharacter] at hrw
  rw [hrw]
  exact mul_ne_zero hL <| Finset.prod_ne_zero_iff.mpr fun p hp =>
    Claim.factor_ne_zero χ.primitiveCharacter (lt_trans (by norm_num) hs) p
      (Nat.prime_of_mem_primeFactors hp)
end
end

-- Source module: Development.AutomorphicArithmetic.CharacterBoxes.HostOfField

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.HC GlobalTheory.EX UpperTheory.Top HostParam.Seam

theorem UpperTheory.Top.hostOfField :
    ∀ eps C0 : ℝ, 0 < eps → eps < 1 / 52 → 1 ≤ C0 → ∃ CT2 C8 c6 Cb x0 : ℝ, C0 ≤ C8 ∧ 0 < c6 ∧ 0 < Cb ∧
    ∀ (s : Scale) (R : Ranks) (H0 : HostAx R.toFrame) (M : ℕ) (Y : ℝ), s.eps = eps → x0 ≤ s.x → RankVal s R →
      s.J ≤ C0 → (R.o : ℝ) ≤ C0 → (H0.QS : ℝ) ≤ C0 * R.n → 0 < M → (M : ℝ) ≤ C0 → H0.QS ∣ Nat.lcm (2 ^ (R.e + 2)) M →
      PairWin s Y → PairGood M eps Y s.x H0.q H0.d → FieldRows H0.toHostRaw ⌊Y ^ (eps / 5)⌋₊ → admitted R H0 →
      ∃ (H : Host R) (q0 : ℕ), H.toHostAx = H0 ∧ H.CT2 = CT2 ∧ HostGood s C8 4 c6 Cb H q0 ∧
        R.toFrame.Shares H.TT (s.x ^ (-1 + s.eps)) :=
  UpperTheory.T3.hostOfFieldOf UpperTheory.T3.shortNorm UpperTheory.T3.smallOne

theorem UpperTheory.Top.supplyOfAdm :
    ∀ ψ : PChar, VWinAt ψ 401 →
    (∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x0 : ℝ, ∀ (s : Scale) (φ : Frame) (H0 : HostAx φ), s.eps = eps → x0 ≤ s.x →
      s.x ^ (2 + 8 * eps) ≤ (φ.ord : ℝ) → (φ.ord : ℝ) ≤ 2 * s.x ^ (2 + 8 * eps) → φ.o = (Level.cyc ψ).o → KerChi ψ H0.toHostRaw →
      ∃ (R : Ranks) (h : R.toFrame = φ), RankVal s R ∧ admitted R (h ▸ H0)) →
    HostExW (3 / 2) (fun _ s R H _ => EAtH (Level.cyc ψ) H.toHostRaw H.TT s.x s.eps 4 ∧ VVle H.E R.t (Real.sqrt s.b)) :=
  UpperTheory.T3.supplyOfAdmOf UpperTheory.Top.hostOfField
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsRanksRankValFrame

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem exists_even_between (A : ℝ) (hA : 2 ≤ A) : ∃ m : ℕ, Even m ∧ A ≤ m ∧ (m : ℝ) ≤ 2 * A := by
  refine ⟨2 * ⌈A / 2⌉₊, even_two_mul _, ?_, ?_⟩
  · have := Nat.le_ceil (A / 2)
    push_cast; linarith
  · have := Nat.ceil_lt_add_one (a := A / 2) (by linarith)
    push_cast; linarith

theorem exists_ranks_of_frame (φ : Formalism.HC.Frame) (k m T W : ℕ) (hk : Even k) (hm : Even m) (h2 : 2 ≤ m) (h3 : m + 3 ≤ k)
    (hmf : m ≤ 2 * φ.ord) (hfk : 2 * φ.ord ≤ k) :
    ∃ R : Ranks, R.toFrame = φ ∧ R.k = k ∧ R.m = m ∧ R.r + R.t = 8 * R.f * R.r + 4 + T * (8 * W) := by
  obtain ⟨r, hr⟩ : ∃ r, r = k + m - 1 := ⟨_, rfl⟩
  obtain ⟨f, hf⟩ : ∃ f, f = 2 * φ.ord := ⟨_, rfl⟩
  obtain ⟨p, hp⟩ : ∃ p, p = f * r := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = T * W := ⟨_, rfl⟩
  have hpr : r ≤ p := by
    rw [hp]; exact Nat.le_mul_of_pos_left _ (by omega)
  obtain ⟨k', hk'⟩ := hk
  obtain ⟨m', hm'⟩ := hm
  have hmt : m ≤ 8 * p + 4 + 8 * q - r + 1 := by omega
  refine ⟨⟨φ, k, m, 8 * p + 4 + 8 * q - r, ⟨k', hk'⟩, ⟨m', hm'⟩, ?_, h2, h3, by omega, by omega, hmf, hfk, ?_⟩,
    rfl, rfl, rfl, ?_⟩
  · rw [Nat.odd_iff]; omega
  · rw [sq]
    exact (Nat.mul_le_mul_left m hmt).trans (Nat.le_add_left _ _)
  · show (k + m - 1) + (8 * p + 4 + 8 * q - r) = 8 * (2 * φ.ord) * (k + m - 1) + 4 + T * (8 * W)
    rw [← hr, ← hf, mul_assoc 8 f r, ← hp, mul_left_comm T 8 W, ← hq]
    omega

theorem exists_ranks_rankVal_frame : ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x0 : ℝ, ∀ s : Scale, s.eps = eps → x0 ≤ s.x →
    ∀ φ : Formalism.HC.Frame, s.x ^ (2 + 8 * s.eps) ≤ (φ.ord : ℝ) → (φ.ord : ℝ) ≤ 2 * s.x ^ (2 + 8 * s.eps) →
      ∃ R : Ranks, R.toFrame = φ ∧ RankVal s R := by
  intro eps h0 h1
  refine ⟨16, fun s hs hx φ he1 hp2 => ?_⟩
  subst hs
  have hx1 : (1 : ℝ) ≤ s.x := by linarith
  have hx0 : (0 : ℝ) < s.x := by linarith
  have hH1 : s.x ^ 2 ≤ s.x ^ (2 + 8 * s.eps) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by push_cast; linarith)
  have hH2 : s.x ^ (2 + 8 * s.eps) ≤ s.x ^ 3 := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by push_cast; linarith)
  have he2 : (φ.ord : ℝ) ≤ 2 * s.x ^ 3 := by linarith
  have hB : s.x ^ 4 ≤ s.x ^ (9 / 2 + 10 * s.eps) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by push_cast; linarith)
  have hd : s.x * s.delta1 = s.x ^ (1 - s.eps / 8) := by
    unfold Scale.delta1
    rw [sub_eq_add_neg, Real.rpow_add hx0, Real.rpow_one]
  have hA1 : 2 ≤ Real.sqrt (s.x * s.delta1) := by
    apply Real.le_sqrt_of_sq_le
    rw [hd]
    have h1 : s.x ^ (1 / 2 : ℝ) ≤ s.x ^ (1 - s.eps / 8) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    have h2 : (4 : ℝ) ≤ s.x ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]
      apply Real.le_sqrt_of_sq_le
      linarith
    linarith
  have hA2 : Real.sqrt (s.x * s.delta1) ≤ s.x := by
    rw [Real.sqrt_le_left hx0.le, hd, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by push_cast; linarith)
  have p2 : 16 * s.x ≤ s.x ^ 2 := by nlinarith
  have p3 : 16 * s.x ^ 2 ≤ s.x ^ 3 := by nlinarith
  have p4 : 16 * s.x ^ 3 ≤ s.x ^ 4 := by nlinarith
  obtain ⟨m, hm, hm1, hm2⟩ := exists_even_between _ hA1
  obtain ⟨k, hk, hk1, hk2⟩ := exists_even_between (s.x ^ (9 / 2 + 10 * s.eps)) (by linarith)
  have a1 : 2 ≤ m := by
    have : ((2 : ℕ) : ℝ) ≤ m := by push_cast; linarith
    exact_mod_cast this
  have a2 : m + 3 ≤ k := by
    have : (m : ℝ) + 3 ≤ k := by linarith
    exact_mod_cast this
  have a3 : m ≤ 2 * φ.ord := by
    have : (m : ℝ) ≤ 2 * (φ.ord : ℝ) := by linarith
    exact_mod_cast this
  have a4 : 2 * φ.ord ≤ k := by
    have : 2 * (φ.ord : ℝ) ≤ k := by linarith
    exact_mod_cast this
  obtain ⟨R, rfl, rfl, rfl, hR⟩ := exists_ranks_of_frame φ k m (TOv s)
    ⌈10 * ((k + m - 1 : ℕ) : ℝ) * (((2 * φ.ord : ℕ) : ℝ) +
      ((2 * φ.ord : ℕ) : ℝ) ^ 2 * ((k : ℝ) - 1) ^ 3 * s.L ^ 2 / m) / 8⌉₊ hk hm a1 a2 a3 a4
  exact ⟨R, rfl, ⟨he1, hp2⟩, ⟨hm1, hm2⟩, ⟨hk1, hk2⟩, hR⟩

end GlobalTheory.EX
end
end

-- Source module: Development.AutomorphicArithmetic.CoprimeRanks.AdmChi

section

@[expose] public section

noncomputable section

namespace UpperTheory.Top

open Formalism.BasicNotions Formalism.MainNotions Formalism.HC HostParam.Seam GlobalTheory.EX

theorem admissible_ranks_of_CMDatum (R : Ranks) (H0 : HostAx R.toFrame) : admitted R H0 := fun _ c h hq => exists_host R H0 h hq c

theorem admissibleClassesTwistedChar : ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x0 : ℝ, ∀ (s : Scale) (φ : Frame) (H0 : HostAx φ),
    s.eps = eps → x0 ≤ s.x → s.x ^ (2 + 8 * s.eps) ≤ (φ.ord : ℝ) → (φ.ord : ℝ) ≤ 2 * s.x ^ (2 + 8 * s.eps) →
    ∃ (R : Ranks) (h : R.toFrame = φ), RankVal s R ∧ admitted R (h ▸ H0) := by
  intro eps heps heps'
  obtain ⟨x0, hx0⟩ := GlobalTheory.EX.exists_ranks_rankVal_frame eps heps heps'
  refine ⟨x0, fun s φ H0 hs hx hlo hup => ?_⟩
  obtain ⟨R, h, hRV⟩ := hx0 s hs hx φ hlo hup
  exact ⟨R, h, hRV, admissible_ranks_of_CMDatum R _⟩

end UpperTheory.Top

end
end
end

-- Source module: Development.AutomorphicArithmetic.CharacterBoxes.SupplyChi

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.HC GlobalTheory.EX UpperTheory.Top

theorem UpperTheory.Top.supplyChi :
    ∀ ψ : PChar, VWinAt ψ 401 → HostExW (3 / 2) (GChi ψ).req := by
  intro ψ hψ
  refine supplyOfAdm ψ hψ ?_
  intro eps he0 he1
  obtain ⟨x0, hx0⟩ := admissibleClassesTwistedChar eps he0 he1
  refine ⟨x0, fun s φ H0 hs hx hlo hhi _ _ => ?_⟩
  subst hs
  exact hx0 s φ H0 rfl hx hlo hhi
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ShapeOf

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Fc

theorem GlobalTheory.Fc.goal_of_shape_of_hyps (V NR : Prop) (N : FamClass → Prop) (G : Prop) (t : _root_.GlobalTheory.Fc.TopShapeAlt V NR N G) (hV : V) (hR : NR) (h : _root_.GlobalTheory.Fc.HypsAlt N _root_.GlobalTheory.Fc.DefiniteSideCondition) : G :=
  t h.𝒜 h.cT h.hEx (_root_.GlobalTheory.Fc.familySelection h.σ) h.hduty (_root_.GlobalTheory.Fc.spectralConditionOfRawSelection h.σ) (_root_.GlobalTheory.Fc.baseLevelChoiceOfRawSelection h.σ) (_root_.GlobalTheory.Fc.definiteHeightOfRawSelection h.σ) (fun Fm hc x hx k i => (_root_.GlobalTheory.Fc.columnChoiceOfRawSelection h.σ Fm hc x hx k i).toS) (_root_.GlobalTheory.Fc.selectionBundleOfRawSelection h.σ) h.hRB h.hTw h.hPA h.hLamP
    (fun Fm hc x hx k i => (GlobalTheory.Cp.divRows3G_iff _).1 (h.hDivG Fm hc x hx k i)) h.hDcPtG h.hTu h.hn4 h.hLit hV h.hWu h.hRF h.hTF h.c30 h.hc30 h.sTy h.sNG h.sM h.sLp h.sO h.h30 h.hInstR h.selJ h.jOn h.hMt
    (h.rRows.imp fun Fm CH _ r hc => let ⟨C, h0, x0, r⟩ := r hc
      ⟨C, h0, x0, fun x hx k hx0 i => let ⟨a, d⟩ := r x hx k hx0 i
        ⟨⟨a.w1, a.covol, a.onto, a.lamLow, a.seeIso, a.miStar, a.fun0, a.pass, a.kap⟩, d⟩⟩)
    h.aPt0 h.aPtTw h.aPer0 h.aPerTw h.aP10 h.aAtG h.aC2 ((_root_.GlobalTheory.Cp.serv_t_iff_formalism_serv_t _ _).1 h.hServ) hR h.nRest h.cIc h.hcI h.irrC h.zL h.tie h.hU h.hG
theorem GlobalTheory.Fc.forall_goal_of_shape_of_hyps : ∀ (V NR : Prop) (N : FamClass → Prop) (G : Prop), _root_.GlobalTheory.Fc.TopShapeAlt V NR N G → V → NR → _root_.GlobalTheory.Fc.HypsAlt N _root_.GlobalTheory.Fc.DefiniteSideCondition → G :=
  fun V NR N G t hV hR h => _root_.GlobalTheory.Fc.goal_of_shape_of_hyps V NR N G t hV hR h
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopPlug

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Fc
theorem UpperTheory.Top.zero_free_all_of_green_v_win (hG : GlobalTheory.GLq.Green) (hV : UpperTheory.Top.VWin)
    (h : Nonempty (_root_.GlobalTheory.Fc.HypsAlt (fun 𝒞 => Closed 𝒞 fun Fm _ => LinkN Fm) _root_.GlobalTheory.Fc.DefiniteSideCondition)) : Formalism.HC.ZeroFreeAll :=
  h.elim fun h => UpperTheory.Top.zeroFreeAll_of_topG (la := 3 / 2) (by norm_num)
    (_root_.GlobalTheory.Fc.forall_goal_of_shape_of_hyps _ _ _ _ (_root_.UpperTheory.Top.shape_closed_link_n_of_green hG) trivial trivial h) fun ψ => UpperTheory.Top.supplyChi ψ (hV ψ)
theorem UpperTheory.Top.every_character_of_green_v_win (hG : GlobalTheory.GLq.Green) (hV : UpperTheory.Top.VWin)
    (h : Nonempty (_root_.GlobalTheory.Fc.HypsAlt (fun 𝒞 => Closed 𝒞 fun Fm _ => LinkN Fm) _root_.GlobalTheory.Fc.DefiniteSideCondition)) : UpperTheory.EveryCharacter :=
  UpperTheory.Top.imprimitive (_root_.UpperTheory.Top.zero_free_all_of_green_v_win hG hV h)
end
end
end
