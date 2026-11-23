module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
public import Development.AutomorphicArithmetic.CharacterBoxes.Supply
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsObjectsOfAdmissibleTwistDatumStatement
public import Development.AbelianVarietyTheory.Definitions.Foundations.RayPrimes
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitRanksBasicBoundsLargeScale
public import Development.AutomorphicArithmetic.ShortNorms.Primes
public import Development.AutomorphicArithmetic.ShortNorms.levelPrimeN
public import Development.AutomorphicArithmetic.ShortNorms.normPrimesN
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
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PrimesInProgressionsRelativeError
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ZerosDisc
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PrimesAPIntervalOfPrimesRel
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeMemAvoidedPrimes
public import Formalism.SharpRestriction.GrowthBounds.PlaneCountTheoremWithConstants
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TensorOfPairLift
public import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.MeanNum
import Formalism.SharpRestriction.GrowthBounds.TopChoiceBounds
public import Development.AutomorphicArithmetic.CharacterBoxes.DesignS
public import Development.AutomorphicArithmetic.CharacterBoxes.HostWW
public import Development.AutomorphicArithmetic.CharacterBoxes.KitS
public import Development.AutomorphicArithmetic.CharacterBoxes.SmallestPrimePolynomialBound

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormPrimesAndLevelPrimeUnconditional

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem normOne_pair_form {d M p : ℕ} (h : GlobalTheory.Mem.An.NormOne d M p) : GlobalTheory.EX.NormOne d M p := by
  obtain ⟨A, B, h1, h2, h3⟩ := h
  exact ⟨(A, B), h1, h2, h3⟩

theorem normPrimes_unconditional : NormPrimes := by
  intro eps he0 he1
  obtain ⟨x0, hx0⟩ := UpperTheory.T3.normPrimesN UpperTheory.T3.shortNorm eps he0
  refine ⟨x0, fun s R N d hs hx hR hq => ?_⟩
  have hk : (1 : ℝ) ≤ R.k := by
    have := R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ R.k)
  have hb : 0 < s.b := Real.exp_pos _
  have hY : 0 < ((R.k : ℝ) * s.b) ^ 8 := by positivity
  have hlog : 8 * s.x ^ eps ≤ Real.log (((R.k : ℝ) * s.b) ^ 8) := by
    rw [Real.log_pow, Real.log_mul (by linarith) hb.ne']
    have h1 : Real.log s.b = s.x ^ eps := by
      rw [← hs]; exact Real.log_exp _
    have h2 := Real.log_nonneg hk
    push_cast
    linarith
  refine (hx0 s.x hx N d (hs ▸ hq) _ hY hlog).trans ?_
  refine Nat.cast_le.mpr (Finset.card_le_card fun g hg => ?_)
  simp only [GlobalTheory.Mem.An.normPrimes, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range] at hg ⊢
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hg
  exact ⟨Nat.lt_succ_of_le h2, h3, (Nat.lt_of_floor_lt h1).le, normOne_pair_form h4⟩

theorem levelPrime_unconditional : LevelPrime := by
  intro eps c he0 he1 hc
  obtain ⟨x0, hx0⟩ := UpperTheory.T3.levelPrimeN UpperTheory.T3.shortNorm eps he0 he1 c 9 hc (by norm_num)
  obtain ⟨x1, hx1⟩ := rank_basic_bounds eps he0 he1
  refine ⟨max x0 x1, fun s R N d g0 g1 Ts hs hx hR hq hg0 hg1 hb0 hb1 hTs hlog => ?_⟩
  obtain ⟨hf, -, hr, hkr, -, -, -, -, -, -, -, -, -, -, -, hm, -⟩ :=
    hx1 s R hs (le_trans (le_max_right _ _) hx) hR
  have hx1' := s.one_lt_alt
  have hxp : 0 < s.x := by linarith
  have hn : 1 ≤ R.n := R.toFrame.ord_pos
  have hk : (1 : ℝ) ≤ R.k := by
    have := R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ R.k)
  have hf1 : (1 : ℝ) ≤ R.f := by
    exact_mod_cast (by unfold Ranks.f; omega : 1 ≤ R.f)
  have hL : s.L = s.x ^ eps := by rw [← hs]; rfl
  have hg : ∀ g : ℕ, 1 ≤ g → (g : ℝ) ≤ s.b ^ 9 → Real.log g ≤ 9 * s.x ^ eps := by
    intro g h1 h2
    have h3 : (0 : ℝ) < g := by exact_mod_cast h1
    refine (Real.log_le_log h3 h2).trans (le_of_eq ?_)
    rw [Real.log_pow, Scale.b, Real.log_exp, hL]
    norm_num
  have hm' : s.x ^ ((1 : ℝ) / 3) ≤ (R.m : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hx1'.le (by rw [hs]; linarith)).trans hm
  have hW1 : (1 : ℝ) ≤ (R.f : ℝ) * R.k := one_le_mul_of_one_le_of_one_le hf1 hk
  have hW2 : (R.f : ℝ) * R.k ≤ s.x ^ (12 : ℝ) := by
    have hk5 : (R.k : ℝ) ≤ s.x ^ (5 : ℝ) := (Nat.cast_le.mpr hkr).trans hr
    exact (rank_mul_le hxp (by linarith) hf hk5).trans
      (Real.rpow_le_rpow_of_exponent_le hx1'.le (by norm_num))
  obtain ⟨T, hT1, hT2, hT3, hT4⟩ := hx0 s.x (le_trans (le_max_left _ _) hx) N d g0 g1 R.m (hs ▸ hq)
    hg0 hg1 (hg g0 hg0 hb0) (hg g1 hg1 hb1) hm' _ Ts hW1 hW2 hTs (hL ▸ hlog)
  exact ⟨T, hT1, hT2.le, hT3, normOne_pair_form hT4⟩

theorem normPrimes_and_levelPrime_unconditional : NormPrimes ∧ LevelPrime :=
  ⟨normPrimes_unconditional, levelPrime_unconditional⟩

end GlobalTheory.EX
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SmallPrimeOneOfPrimesRel

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem smallPrimeOne_of_primesRel : GlobalTheory.Lin.PrimesRel → SmallPrimeOne := by
  intro h
  obtain ⟨C₀, Cr, cr, c, h0, h1, h2, h3, H⟩ := GlobalTheory.Lin.primesAPInterval_of_primesRel h
  obtain ⟨s, hsC, hs21, hsr⟩ : ∃ s : ℝ, C₀ ≤ s ∧ 21 ≤ s ∧ 200 * Cr / cr ≤ s :=
    ⟨max C₀ (max 21 (200 * Cr / cr)), le_max_left _ _,
      le_trans (le_max_left _ _) (le_max_right _ _), le_trans (le_max_right _ _) (le_max_right _ _)⟩
  have hss : s ≤ s ^ 2 := by nlinarith
  have hexp : Cr * Real.exp (-cr * s) ≤ 1 / 200 := by
    have e1 : 200 * Cr ≤ cr * s := by
      rw [div_le_iff₀ h2] at hsr; linarith
    have e2 := Real.add_one_le_exp (cr * s)
    have e3 : 0 < Real.exp (cr * s) := Real.exp_pos _
    rw [neg_mul, Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ e3 (by norm_num)]
    linarith
  refine ⟨3 * s ^ 2 + 1, by nlinarith, ?_⟩
  intro M hM
  rcases Nat.eq_or_lt_of_le hM with rfl | hM3
  · refine ⟨3, Nat.prime_three, by norm_num, ?_⟩
    have e1 : ((2 : ℕ) : ℝ) ^ (2 : ℝ) ≤ ((2 : ℕ) : ℝ) ^ (3 * s ^ 2 + 1) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
    refine le_trans ?_ e1
    norm_num
  have hm3 : (3 : ℝ) ≤ M := by exact_mod_cast hM3
  have hB0 : (0 : ℝ) < 4 * (M : ℝ) := by linarith
  have hB1 : (1 : ℝ) ≤ 4 * (M : ℝ) := by linarith
  have hlB : 1 ≤ Real.log (4 * (M : ℝ)) := by
    rw [Real.le_log_iff_exp_le hB0]
    have := Real.exp_one_lt_d9
    linarith
  set Y : ℝ := (4 * (M : ℝ)) ^ (s ^ 2) with hY
  have hY0 : 0 < Y := Real.rpow_pos_of_pos hB0 _
  have hlY : Real.log Y = s ^ 2 * Real.log (4 * (M : ℝ)) := Real.log_rpow hB0 _
  have hlY2 : s ^ 2 ≤ Real.log Y := by rw [hlY]; nlinarith [sq_nonneg s]
  have hlY0 : 0 < Real.log Y := by linarith
  have hrho : Formalism.HermitianLattices.GL2PrimeSums.rhoErr Cr cr (4 * M) Y ≤ 1 / 100 := by
    unfold Formalism.HermitianLattices.GL2PrimeSums.rhoErr
    have a1 : Real.exp (-cr * Real.log Y / Real.log (4 * (M : ℝ))) ≤ Real.exp (-cr * s) := by
      apply Real.exp_le_exp.2
      rw [hlY, ← mul_assoc, mul_div_assoc, div_self (by linarith), mul_one]
      nlinarith
    have a2 : Real.exp (-cr * Real.sqrt (Real.log Y)) ≤ Real.exp (-cr * s) := by
      apply Real.exp_le_exp.2
      have : s ≤ Real.sqrt (Real.log Y) := Real.le_sqrt_of_sq_le hlY2
      nlinarith
    have b1 := mul_le_mul_of_nonneg_left a1 h1.le
    have b2 := mul_le_mul_of_nonneg_left a2 h1.le
    linarith
  have h7 : (4 * (M : ℝ)) ^ (7 : ℝ) ≤ 1 * Y ^ ((1 : ℝ) / 3) := by
    rw [one_mul, hY, ← Real.rpow_mul hB0.le]
    exact Real.rpow_le_rpow_of_exponent_le hB1 (by linarith)
  have hc := H M 1 hM3 (Nat.coprime_one_left M) Y 1
    (Real.rpow_le_rpow_of_exponent_le hB1 (by linarith)) le_rfl hrho h7
  have hpos : 0 < c * 1 * (4 * (M : ℝ)) ^ (-6 : ℝ) * Y / Real.log Y := by
    have := Real.rpow_pos_of_pos hB0 (-6 : ℝ)
    positivity
  have hcard := lt_of_lt_of_le hpos hc
  rw [Nat.cast_pos, Finset.card_pos] at hcard
  obtain ⟨p, hp⟩ := hcard
  rw [Finset.mem_filter, Finset.mem_Ioc] at hp
  obtain ⟨⟨-, hp2⟩, hpp, hpm⟩ := hp
  refine ⟨p, hpp, ?_, ?_⟩
  · have : p % M = 1 % M := hpm
    rw [this]; exact Nat.mod_eq_of_lt (by omega)
  · have e1 : (p : ℝ) ≤ Y * (1 + 1) :=
      le_trans (Nat.cast_le.2 hp2) (Nat.floor_le (by positivity))
    have hM0 : (0 : ℝ) < M := by linarith
    have e2 : Y ≤ (M : ℝ) ^ (3 * s ^ 2) := by
      rw [Real.rpow_mul hM0.le]
      apply Real.rpow_le_rpow hB0.le _ (by positivity)
      have : (M : ℝ) ^ (3 : ℝ) = (M : ℝ) ^ (3 : ℕ) := by exact_mod_cast Real.rpow_natCast (M : ℝ) 3
      rw [this]
      have : (4 : ℝ) ≤ (M : ℝ) ^ 2 := by nlinarith
      nlinarith
    rw [Real.rpow_add hM0, Real.rpow_one]
    nlinarith

end GlobalTheory.EX
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WindowShareRequirementClosedFormProof

section

@[expose] public section

noncomputable section

namespace GlobalTheory.EX.G4

open Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

theorem w_of {eps : ℝ} (Fm : FamP eps) (h13 : FirstTheoremAtFamily Fm) (hLa : 0 < Fm.GK.La) (hCN : CornerGLContinuity.FamilyWindowLogBound Fm) :
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, AuxBlock8.WeightVectorExists (Fm.D x i) (Fm.L x i) (Fm.Gx x i) Fm.GK := by
  have he : 0 < eps := by
    obtain ⟨i⟩ := Fm.Ix_zero
    have := (Fm.L 0 i).sc.eps_pos
    rwa [Fm.L_eps] at this
  obtain ⟨CH, C', b0, b1, b2, b3, b4, b5, b6, hp13⟩ := h13
  obtain ⟨Cm, hCm, h8⟩ := family_first_bound_of_theorem Fm CH C' (kapIDefF Fm) b0 b1 b2 b3 b4 b5 b6 hp13
  obtain ⟨C31, -, h1⟩ := family_first_lemma Fm
  obtain ⟨x0, h⟩ := ((((h1.and (family_orders_bound_of_lemma Fm (TopChoiceBounds.family_band_ratio_holds Fm) hCN)).and
    (family_sizes_bound Fm hLa (eps / 48) (by positivity))).and h8).and (eventually_sizes_admitted Fm)).and (Ev.x1 Fm)
  obtain ⟨x2, H2⟩ := Filter.eventually_atTop.1 (AuxBlock8.Pf.numMean_ev eps Fm.GK Fm.GK_nonneg Cm hCm)
  obtain ⟨x3, H3⟩ := Filter.eventually_atTop.1 (AuxBlock8.Pf.restHypI_ev eps Fm.GK Fm.GK_nonneg Cm C31)
  refine ⟨max x0 (max x2 x3), fun x hx i => ?_⟩
  have e0 : x ≥ x0 := le_trans (le_max_left _ _) hx
  have e2 : x ≥ x2 := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have e3 : x ≥ x3 := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  obtain ⟨⟨⟨⟨⟨a1, a4⟩, a5⟩, a8⟩, aSz⟩, hx1⟩ := h x e0 i
  have NM := H2 x e2 (Fm.D x i) (Fm.L x i) (Fm.L_x x i hx1) (Fm.L_eps x i) aSz.1 a5
  have HI := H3 x e3 (Fm.D x i) (Fm.L x i) (Fm.Gx x i) (Fm.L_x x i hx1) (Fm.L_eps x i) aSz a5 a4 a1 NM
  exact AuxBlock8.Pf.weight_condition_of_mean_excess _ _ (AuxBlock8.Pf.meanEx_of (Fm.Gx x i) Fm.GK Fm.GK_nonneg Cm a8 NM HI a4.2.2.1
    (AuxBlock8.Pf.slopeEstimate_of_lemmaB_slopeLine (Fm.Gx x i) Fm.GK Fm.GK_nonneg Cm a8 NM HI a4.2.2.1))

theorem wClosed : DC.WClosed :=
  (((first_theorem_closed_form (fun _ => True) RangeOne.rangeOne_abs).and (signs_closed (fun _ => True))).and
    (TopChoiceBounds.family_log_bound_closed (fun _ => True))).imp fun Fm _ _ h => w_of Fm h.1.1 h.1.2.1 h.2

end GlobalTheory.EX.G4
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WindowShareRequirementClosedFormProofStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

theorem _root_.GlobalTheory.T.windowShareRequirementClosedForm_proof : DC.WClosed := by
  first | exact @GlobalTheory.EX.G4.wClosed | exact GlobalTheory.EX.G4.wClosed | (intros; apply GlobalTheory.EX.G4.wClosed <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.CharacterBoxes.ObjCTrue

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc NumberField IsDedekindDomain

namespace UpperTheory.Top

theorem objC_true {Q : Par → PtProp} (h : ObjCP Q) : DC.ObjC (fun _ _ _ _ _ _ _ _ _ => True) := by
  obtain ⟨ε0, h0, h⟩ := h
  refine ⟨ε0, h0, fun eps C8 C5 c6 Cb a1 a2 a3 a4 => ?_⟩
  obtain ⟨K0, h⟩ := h eps C8 C5 c6 Cb a1 a2 a3 a4
  refine ⟨K0, fun C b1 b2 b3 => ?_⟩
  obtain ⟨c1, h⟩ := h C b1 b2 b3
  refine ⟨c1, fun cD hcD => ?_⟩
  obtain ⟨c2, h⟩ := h cD hcD
  refine ⟨c2, fun ch hch => ?_⟩
  obtain ⟨x0, h⟩ := h ch hch
  refine ⟨x0, fun s R H q0 a b M c u0 d1 d2 d3 d4 d5 d0 d6 d7 d8 d9 => ?_⟩
  obtain ⟨p, e1, e2, e3, e4, e5, -⟩ := h s R H q0 a b M c u0 d1 d2 d3 d4 (by rw [← b2] at d5; exact d5) d0 d6 d7 d8 d9
  exact ⟨p, e1, e2, e3, e4, e5, trivial⟩

theorem recS (QO : Par → ∀ D : D7, Obj D → Prop) (cT : ℝ → ℝ → ℝ) (hR : DC.MinkDiv → RecExP (fun κ => DQ.withQD (QO κ)))
    (hM : DC.MinkDiv) : ExD (clsP QO) cT := by
  intro la G hla hH
  have hS : SmallPrimeOne := GlobalTheory.EX.smallPrimeOne_of_primesRel GlobalTheory.Lin.primesRel_holds
  have hO := GlobalTheory.T.existsObjects_of_admissibleTwistDatum _ GlobalTheory.EX.normPrimes_and_levelPrime_unconditional.2 (hR hM)
  have hW : DC.HostWW la G.req := hostWW _ la _ hla (hostQ hS la G hH) (objC_true hO) GlobalTheory.T.windowShareRequirementClosedForm_proof
  exact designS (fun κ => ptO (DQ.withQD (QO κ))) cT la G hla hM (kitS _ la G hW hO)

end UpperTheory.Top
end
end
