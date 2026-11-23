module

public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementI
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalE
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.LinearCoeffLogShiftedWeierstrass
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalB
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.CoeffPowEqZeroOfCc
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.USideA
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.USideB
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementE
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementI
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalB
import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.StatementT
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.Closure
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.Points
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.UnitaryInverseIdentity
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.PhNormFromDatum
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.SecondCoeffConsistency
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.OneAddMulDerivLogSubst
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.ConstantCoeffVecConsPairEqZero
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.FirstLevelFromUniversalLaw
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs

-- Source module: Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.PhENormOf

section

@[expose] public section

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.B.Nrm

open Formalism.G (unitBall)
open Formalism.L2.Th1.C (wpShift IsLogPair mulBy PhNormAt Cong LG IntMv IntPS mvExp IsOneUnit XIsWp)
open Formalism.L2.Th1.C.USideB

theorem PhENorm_of (hI : Th0Isogeny) : PhENorm := by
  intro K _ _ _ g2 g3 s2 c0 xT al albar S P l linv i ep F ι _ xQ wp wm hP hT hL hC hxT hxQ hZ hN hS
  have hl := hL.1
  have hsl := hs_of hl
  have hcv : PowerSeries.constantCoeff (mulBy l linv al) = 0 := cc_mulBy hL al
  have hsv := hs_of hcv
  have hS' : (al ^ 2 - 2 * (Fintype.card ι : K)) * s2 = S := by rw [← hN, ← hS]; ring
  have hF := hI K g2 g3 s2 c0 xT al S P ι (fun Q => xQ Q + c0) wp wm hP hT hZ hS'
  obtain ⟨hph0, hphd⟩ :=
    phEDef K s2 (xT + c0) (3 * (xT + c0) ^ 2 - g2 / 4) (wOf (xT + c0) P) l hl
  generalize hn : Fintype.card ι = n at *
  have hthl : PowerSeries.subst l (thTw g2 s2 c0 xT P) = mvExp (-(phTw g2 s2 c0 xT P l)) := hphd
  have hph0' : PowerSeries.constantCoeff (phTw g2 s2 c0 xT P l) = 0 := hph0
  generalize phTw g2 s2 c0 xT P l = ph at *
  generalize thTw g2 s2 c0 xT P = th at *
  set v := mulBy l linv al with hv
  have hnph : PowerSeries.constantCoeff (-ph) = 0 := by simp [hph0']
  have hphv : PowerSeries.constantCoeff (PowerSeries.subst v ph) = 0 := cc_subst hcv hph0'
  have hnphv : PowerSeries.constantCoeff (-(PowerSeries.subst v ph)) = 0 := by simp [hphv]
  have hX : XIsWp P l ep c0 := by
    unfold XIsWp
    rw [Formalism.L2.Th1.C.USideA.subst_wpShift_zero hsl, hC.2.2.1]
    ring

  have h1 : PowerSeries.subst l (PowerSeries.rescale al th) =
      mvExp (-(PowerSeries.subst v ph)) := by
    rw [subst_rescale hL, hthl, Formalism.L2.Th1.C.subst_mvExp hnph hcv]
    have h3 : PowerSeries.subst v (-ph) = -(PowerSeries.subst v ph) := by
      rw [← PowerSeries.coe_substAlgHom hsv, map_neg]
    rw [h3]

  have h4 := congrArg (PowerSeries.subst l) hF
  rw [PowerSeries.subst_mul hsl, PowerSeries.subst_pow hsl, PowerSeries.subst_mul hsl,
    PowerSeries.subst_pow hsl, h1, hthl] at h4
  have h6 : PowerSeries.subst l (∏ Q, wpShift P (xQ Q + c0)) =
      ∏ Q, PowerSeries.subst l (wpShift P (xQ Q + c0)) := by
    rw [← PowerSeries.coe_substAlgHom hsl, map_prod]
  rw [h6] at h4
  have h7 : PowerSeries.X ^ (2 * n) * ∏ Q, PowerSeries.subst l (wpShift P (xQ Q + c0)) =
      (∏ Q, (ep - PowerSeries.C (xQ Q) * PowerSeries.X ^ 2)) * l ^ (2 * n) := by
    rw [pow_mul, pow_mul, ← hn, ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_const,
      ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun Q _ => subst_wpShift hl hX (xQ Q)
  have h8 := subst_wpShift hl hX xT
  set B : PowerSeries K := ∏ Q, (ep - PowerSeries.C (xQ Q) * PowerSeries.X ^ 2) with hB
  set G : PowerSeries K := ep - PowerSeries.C xT * PowerSeries.X ^ 2 with hG
  have hl0 : l ^ (2 * n) ≠ 0 := pow_ne_zero _ (l_ne_zero hL)
  have h9 : (mvExp (-(PowerSeries.subst v ph)) : PowerSeries K) * G ^ n =
      mvExp (-ph) ^ (2 * n) * B := by
    apply mul_right_cancel₀ hl0
    calc (mvExp (-(PowerSeries.subst v ph)) : PowerSeries K) * G ^ n * l ^ (2 * n)
        = mvExp (-(PowerSeries.subst v ph)) * (G * l ^ 2) ^ n := by
          rw [mul_pow, ← pow_mul, mul_assoc]
      _ = (mvExp (-(PowerSeries.subst v ph)) *
            PowerSeries.subst l (wpShift P (xT + c0)) ^ n) * PowerSeries.X ^ (2 * n) := by
          rw [← h8]; ring
      _ = mvExp (-ph) ^ (2 * n) *
            (PowerSeries.X ^ (2 * n) * ∏ Q, PowerSeries.subst l (wpShift P (xQ Q + c0))) := by
          rw [h4]; ring
      _ = _ := by rw [h7]; ring

  have hepi : ep ∈ intSub (unitBall K) := fun k => hC.1 (Finsupp.single () k)
  have hBi : B ∈ intSub (unitBall K) :=
    Subring.prod_mem _ fun Q _ => Subring.sub_mem _ hepi
      (Subring.mul_mem _ (C_mem_intSub (hxQ Q)) (Subring.pow_mem _ (X_mem_intSub _) 2))
  have hGi : G ∈ intSub (unitBall K) :=
    Subring.sub_mem _ hepi
      (Subring.mul_mem _ (C_mem_intSub hxT) (Subring.pow_mem _ (X_mem_intSub _) 2))
  have hB1 : PowerSeries.constantCoeff B = 1 := by
    rw [hB, map_prod]
    apply Finset.prod_eq_one
    intro Q _
    simp [hC.2.1]
  have hNph : (al * albar) • ph = ((2 * n : ℕ) : K) • ph := by rw [hN]; push_cast; rfl
  have hNph0 : PowerSeries.constantCoeff (((2 * n : ℕ) : K) • ph) = 0 := by simp [hph0']
  have h10 : (mvExp (PowerSeries.subst v ph - (al * albar) • ph) : PowerSeries K) * B = G ^ n := by
    rw [hNph, Formalism.L2.Th1.C.mvExp_sub hphv hNph0, ← smul_neg,
      Formalism.L2.Th1.C.mvExp_smul_nat hnph, mul_assoc, ← h9, ← mul_assoc,
      Formalism.L2.Th1.C.mvExp_mul_neg hphv, one_mul]
  have h11 : IntPS (unitBall K) (mvExp (PowerSeries.subst v ph - (al * albar) • ph)) :=
    int_of_mul ⟨hB1, hBi⟩ (Subring.pow_mem _ hGi n) h10
  refine ⟨?_, intMv_of_intPS h11⟩
  have : PowerSeries.constantCoeff (PowerSeries.subst v ph - (al * albar) • ph) = 0 := by
    simp [hphv, hph0']
  exact this

end Formalism.L2.Th1.B.Nrm
end
end
end

-- Source module: Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.BiextensionFormalMulMul

section

section

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.B.Split

open Formalism.L2.Th1.C Formalism.L2.Th1.C.Pts Formalism.L2.Th1.C.Calc

variable {K : Type} [Field K] [CharZero K] {R : Subring K} {l linv ph : PowerSeries K}

theorem cong_smul {σ : Type} {z : K} (hz : IsBinomScalar R z) {f g : MvPowerSeries σ K}
    (h : Cong R f g) : Cong R (z • f) (z • g) := by
  have := lGBinom K R σ z hz _ h
  unfold Cong
  rwa [← smul_sub]

theorem lg_of_smul {σ : Type} {c : K} (hc : c ≠ 0) (hz : IsBinomScalar R c⁻¹)
    {f : MvPowerSeries σ K} (h : LG R (c • f)) : LG R f := by
  have := lGBinom K R σ _ hz _ h
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this

theorem biextension_formal_mul_mul (hF : Frame R l linv ph) {a b : K} (hN : PhNormAt R l linv ph a b)
    {σ : Type} {x y : MvPowerSeries σ K} (hx : IsPt R x) (hy : IsPt R y) :
    Cong R (be0 l linv ph (fmul l linv a x) (fmul l linv a y)) ((a * b) • be0 l linv ph x y) := by
  have e1 := phNorm_pt hF.1 hN (isPt_fadd hF.1 hF.2.1 hx hy)
  have e2 := phNorm_pt hF.1 hN hx
  have e3 := phNorm_pt hF.1 hN hy
  rw [fmul_fadd hF.1 a hx.1 hy.1] at e1
  have := cong_sub (cong_sub e1 e2) e3
  rw [← smul_sub, ← smul_sub] at this
  exact this

theorem biextension_vanishes_split (hF : Frame R l linv ph) {a b : K} (ha : EndInt R l linv a)
    (hB : IsBinomScalar R a) (hZ : ZLinAt R l linv ph a) (hN : PhNormAt R l linv ph a b)
    (hc : a * (a - b) ≠ 0) (hinv : IsBinomScalar R (a * (a - b))⁻¹)
    {σ : Type} {x y : MvPowerSeries σ K} (hx : IsPt R x) (hy : IsPt R y) :
    LG R (be0 l linv ph x y) := by
  have hax : IsPt R (fmul l linv a x) := isPt_fmul hF.1 ha hx
  have e1 : Cong R (be0 l linv ph (fmul l linv a x) (fmul l linv a y))
      (a • be0 l linv ph (fmul l linv a x) y) := hZ σ _ _ hax hy
  have e2 : Cong R (be0 l linv ph (fmul l linv a x) y) (a • be0 l linv ph x y) := by
    have := hZ σ y x hy hx
    rwa [addDefect_comm ph y (fmul l linv a x), addDefect_comm ph y x] at this
  have e3 : Cong R (a • a • be0 l linv ph x y) ((a * b) • be0 l linv ph x y) :=
    cong_trans (cong_symm (cong_trans e1 (cong_smul hB e2))) (biextension_formal_mul_mul hF hN hx hy)
  refine lg_of_smul hc hinv ?_
  have e : (a * (a - b)) • be0 l linv ph x y =
      a • a • be0 l linv ph x y - (a * b) • be0 l linv ph x y := by
    rw [smul_smul, ← sub_smul, mul_sub]
  rw [e]
  exact e3

theorem phNorm_one_iff (c : K) :
    PhNormAt R l linv ph c 1 ↔
      Cong R (PowerSeries.subst (fmul l linv c (PowerSeries.X : MvPowerSeries Unit K)) ph)
        (c • (ph : MvPowerSeries Unit K)) := by
  rw [PhNormAt, mulBy_eq_fmul, mul_one]

theorem phNorm_natCast (hF : Frame R l linv ph)
    (key : ∀ x y : MvPowerSeries Unit K, IsPt R x → IsPt R y → LG R (be0 l linv ph x y)) (n : ℕ) :
    PhNormAt R l linv ph (n : K) 1 := by
  have hX : IsPt R (PowerSeries.X : MvPowerSeries Unit K) := isPt_X
  have hXs : PowerSeries.subst (PowerSeries.X : MvPowerSeries Unit K) ph = ph :=
    PowerSeries.X_subst ph
  rw [phNorm_one_iff]
  induction n with
  | zero =>
    rw [Nat.cast_zero, fmul_zero_left hF.1, PowerSeries.subst_zero_of_constantCoeff_zero hF.2.2,
      zero_smul]
    exact cong_refl _
  | succ n ih =>
    have k := key _ _ (isPt_fmul hF.1 (Clo.endInt_natCast hF.1 hF.2.1 n) hX) hX
    rw [be0, hXs] at k
    rw [Nat.cast_succ, fmul_add hF.1 _ _ hX.1, fmul_one hF.1 hX.1, add_smul, one_smul]
    have := lg_add k ih
    unfold Cong
    convert this using 1
    abel

theorem phNorm_intCast (hF : Frame R l linv ph)
    (key : ∀ x y : MvPowerSeries Unit K, IsPt R x → IsPt R y → LG R (be0 l linv ph x y)) (n : ℤ) :
    PhNormAt R l linv ph (n : K) 1 := by
  have hX : IsPt R (PowerSeries.X : MvPowerSeries Unit K) := isPt_X
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · rw [Int.cast_natCast]
    exact phNorm_natCast hF key m
  · rw [Int.cast_neg, Int.cast_natCast]
    have hm := Clo.endInt_natCast (R := R) hF.1 hF.2.1 m
    have k := key _ _ (isPt_fmul hF.1 hm hX) (isPt_fmul hF.1 (endInt_neg hF.1 hF.2.1 hm) hX)
    rw [be0, fadd_fmul_neg hF.1 _ hX.1, PowerSeries.subst_zero_of_constantCoeff_zero hF.2.2] at k
    have h1 := (phNorm_one_iff (R := R) (l := l) (linv := linv) (ph := ph) (m : K)).1
      (phNorm_natCast hF key m)
    rw [phNorm_one_iff, neg_smul]
    have := lg_neg (lg_add k h1)
    unfold Cong
    convert this using 1
    abel

theorem split_vanishing_at_two : Formalism.L2.Th1.G.SplitVanishTwo := by
  intro K _ _ _ _ R hR l linv ph a b hF hF1 ha hcl hN ha0 hab hb1 hi1 hi2
  have hl := hF.1.1
  have hli := hF.1.2.2.1
  have hph := hF.2.2
  have hB : IsBinomScalar R a := by
    refine closure_minimal ?_ (binomClosed K R hR) hcl
    rintro _ ⟨n, rfl⟩
    exact intBinomScalar K R n
  have hZ : ZLinAt R l linv ph a := by
    refine closure_minimal ?_ (zLinClosed K R hR l linv ph hl hli hph) hcl
    rintro _ ⟨n, rfl⟩
    exact zLinInt K R l linv ph hF hF1 n
  have key : ∀ x y : MvPowerSeries Unit K, IsPt R x → IsPt R y → LG R (be0 l linv ph x y) :=
    fun x y hx hy =>
      biextension_vanishes_split hF ha hB hZ hN (mul_ne_zero ha0 (sub_ne_zero.2 hab)) hi1 hx hy
  have hA : PhNormAt R l linv ph a 1 := by
    have hc : IsClosed {c : K | PhNormAt R l linv ph c 1} :=
      (phNormClosed K R hR l linv ph hl hli hph).preimage
        (continuous_id.prodMk continuous_const)
    refine closure_minimal ?_ hc hcl
    rintro _ ⟨n, rfl⟩
    exact phNorm_intCast hF key n
  refine lg_of_smul (mul_ne_zero ha0 (sub_ne_zero.2 (Ne.symm hb1))) hi2 ?_
  have e3 : Cong R ((a * 1) • (ph : MvPowerSeries Unit K)) ((a * b) • ph) :=
    cong_trans (cong_symm hA) hN
  have e : (a * (1 - b)) • (ph : MvPowerSeries Unit K) = (a * 1) • ph - (a * b) • ph := by
    rw [← sub_smul, mul_sub]
  rw [e]
  exact e3

end Formalism.L2.Th1.B.Split
end
end
end

-- Source module: Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.TwoAdicScalarConditions

section

section

noncomputable section

namespace Formalism.L2.Th1.B.Van

open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 swap2 DivAB)
open Formalism.G (unitBall)
open Formalism.L2.Th1.C (IsLogPair mulBy EndInt PhNormAt IsBinomScalar FGInt LG)

theorem Th0Vanish_of (hC : CubeE) (hN : PhENorm) : ThetaZeroVanishing := by
  intro K _ _ _ g2 g3 s2 c0 a1 a3 xT yT al albar S P l linv i ep F ι _ xQ wp wm hP hL hI hlp hCu
    hCu3 hT hQ hFib hN1 hS hEnd hcl h0 hne h1 hb1 hb2
  have hl0 : PowerSeries.constantCoeff l = 0 := hL.2.2.1
  obtain ⟨hc0, hth⟩ :=
    phEDef K s2 (xT + c0) (3 * (xT + c0) ^ 2 - g2 / 4) (wOf (xT + c0) P) l hl0
  obtain ⟨-, -, hd1, -⟩ := hC K g2 g3 s2 c0 a1 a3 xT yT P l i ep F hP hL hI hCu hCu3 hT
  obtain ⟨-, hFG, hF1⟩ := Formalism.L2.Th1.C.first_level_from_universal_law K F l linv _ hlp hL hc0 hd1
  have hPN := hN K g2 g3 s2 c0 xT al albar S P l linv i ep F ι xQ wp wm hP hT.2.1 hlp hCu
    hT.2.2.1 hQ hFib hN1 hS
  have hLG : LG (unitBall K) (phTw g2 s2 c0 xT P l) :=
    Split.split_vanishing_at_two K (unitBall K) (Formalism.L2.Th1.C.unitBallClosed K) l linv _ al albar
      ⟨hlp, hFG, hc0⟩ hF1 hEnd hcl hPN h0 hne h1 hb1 hb2
  have hth' : PowerSeries.subst l (thTw g2 s2 c0 xT P) = fExp (-phTw g2 s2 c0 xT P l) := hth
  have hneg : LG (unitBall K) (-phTw g2 s2 c0 xT P l) :=
    (Formalism.L2.Th1.C.lGSubgroup K (unitBall K) Unit).2.2 _ hLG
  refine ⟨?_, ?_, ?_⟩
  · refine (Formalism.L2.Th1.C.simeqIffCong K Unit _ _).2 ?_
    rw [Formalism.L2.Th1.C.Cong, sub_zero]
    exact hLG
  · rw [hth']
    exact constantCoeff_fExp hneg.1
  · rw [hth']
    exact hneg.2

section Two

variable {K : Type} [NormedField K] [NormedAlgebra ℚ_[2] K]

def phi (K : Type) [NormedField K] [NormedAlgebra ℚ_[2] K] : ℤ_[2] →+* K :=
  (algebraMap ℚ_[2] K).comp PadicInt.Coe.ringHom

theorem continuous_phi : Continuous (phi K) := by
  exact (continuous_algebraMap ℚ_[2] K).comp continuous_subtype_val

theorem phi_mem_closure (x : ℤ_[2]) : phi K x ∈ closure (Set.range (fun n : ℤ => (n : K))) := by
  have hd : DenseRange (Int.cast : ℤ → ℤ_[2]) := PadicInt.denseRange_intCast
  have h1 : x ∈ closure (Set.range (Int.cast : ℤ → ℤ_[2])) := by rw [hd.closure_eq]; trivial
  refine map_mem_closure continuous_phi h1 ?_
  rintro _ ⟨n, rfl⟩
  exact ⟨n, by rw [map_intCast]⟩

theorem phi_mem_of_closed {s : Set K} (hs : IsClosed s) (hn : ∀ n : ℤ, (n : K) ∈ s) (x : ℤ_[2]) :
    phi K x ∈ s := closure_minimal (Set.range_subset_iff.mpr hn) hs (phi_mem_closure x)

theorem phi_injective : Function.Injective (phi K) := (algebraMap ℚ_[2] K).injective.comp Subtype.val_injective

theorem phi_inv {x : ℤ_[2]} (hx : ‖x‖ = 1) : ∃ y : ℤ_[2], (phi K x)⁻¹ = phi K y := by
  obtain ⟨u, rfl⟩ := PadicInt.isUnit_iff.mpr hx
  exact ⟨((u⁻¹ : ℤ_[2]ˣ) : ℤ_[2]), by rw [map_units_inv]⟩

end Two

theorem norm_sub_eq_one {b b' : ℤ_[2]} (hb : ‖b‖ = 1) (hb' : ‖b'‖ < 1) : ‖b - b'‖ = 1 := by
  have h1 : ‖b - b'‖ ≤ max ‖b‖ ‖b'‖ := by
    have h3 := PadicInt.nonarchimedean b (-b')
    rwa [norm_neg, ← sub_eq_add_neg] at h3
  have h2 : ‖b‖ ≤ max ‖b - b'‖ ‖b'‖ := by
    have h3 := PadicInt.nonarchimedean (b - b') b'
    rwa [sub_add_cancel] at h3
  rw [hb] at h1 h2
  rcases le_total ‖b - b'‖ ‖b'‖ with h | h
  · rw [max_eq_right h] at h2
    linarith
  · rw [max_eq_left (by linarith)] at h1
    rw [max_eq_left h] at h2
    linarith

theorem endInt_int {K : Type} [Field K] (R : Subring K) {l linv : PowerSeries K}
    (h : IsLogPair l linv) (hF : FGInt R l linv) (n : ℤ) : EndInt R l linv (n : K) := by
  obtain ⟨-, -, h0, h1, hm, hadd, -⟩ := Formalism.L2.Th1.C.ptClosure K R l linv h hF
  induction n using Int.induction_on with
  | zero => simpa using h0
  | succ n ih =>
    have := hadd _ _ ih h1
    simpa using this
  | pred n ih =>
    have := hadd _ _ ih hm
    simpa [sub_eq_add_neg] using this

theorem two_adic_scalar_conditions : TwoAdicScalars := by
  intro K _ _ _ _ F l linv b b' hL hlp hb hb' al albar
  have hcl := Formalism.L2.Th1.C.unitBallClosed K
  have hFG : FGInt (unitBall K) l linv := by
    rw [FGInt, ← Formalism.L2.Th1.C.Dict.law_eq hlp hL.1 hL.2.2.2.2]
    exact hL.2.1
  have hbin : ∀ x : ℤ_[2], IsBinomScalar (unitBall K) (phi K x) :=
    phi_mem_of_closed (Formalism.L2.Th1.C.binomClosed K (unitBall K) hcl)
      (Formalism.L2.Th1.C.intBinomScalar K (unitBall K))
  have hal : al = phi K b := rfl
  have halb : albar = phi K b' := rfl
  have h1b' : ‖(1 : ℤ_[2]) - b'‖ = 1 := norm_sub_eq_one norm_one hb'
  have hbb' : ‖b - b'‖ = 1 := norm_sub_eq_one hb hb'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact phi_mem_of_closed (Formalism.L2.Th1.C.endIntClosed K (unitBall K) hcl l linv hlp.1)
      (endInt_int (unitBall K) hlp hFG) b
  · exact phi_mem_closure b
  · rw [hal, ← map_zero (phi K)]
    intro h
    have := phi_injective h
    rw [this, norm_zero] at hb
    exact zero_ne_one hb
  · rw [hal, halb]
    intro h
    have := phi_injective h
    rw [this] at hb
    exact hb'.ne hb
  · rw [halb, ← map_one (phi K)]
    intro h
    have := phi_injective h
    rw [this, norm_one] at hb'
    exact lt_irrefl _ hb'
  · have e : al * (al - albar) = phi K (b * (b - b')) := by
      rw [hal, halb, map_mul, map_sub]
    obtain ⟨y, hy⟩ := phi_inv (K := K) (x := b * (b - b')) (by rw [norm_mul, hb, hbb', one_mul])
    rw [e, hy]
    exact hbin y
  · have e : al * (1 - albar) = phi K (b * (1 - b')) := by
      rw [hal, halb, map_mul, map_sub, map_one]
    obtain ⟨y, hy⟩ := phi_inv (K := K) (x := b * (1 - b')) (by rw [norm_mul, hb, h1b', one_mul])
    rw [e, hy]
    exact hbin y

end Formalism.L2.Th1.B.Van
end
end
end

-- Source module: Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalI

section

@[expose] public section

namespace Formalism.L2.Th1.B

theorem th0Isogeny : Th0Isogeny := Iso.theta_zero_isogeny_holds
theorem phENorm : PhENorm := Nrm.PhENorm_of th0Isogeny
theorem th0Vanish : ThetaZeroVanishing := Van.Th0Vanish_of cubeE phENorm
theorem twoAdicScalars : TwoAdicScalars := Van.two_adic_scalar_conditions

end Formalism.L2.Th1.B
end
end
