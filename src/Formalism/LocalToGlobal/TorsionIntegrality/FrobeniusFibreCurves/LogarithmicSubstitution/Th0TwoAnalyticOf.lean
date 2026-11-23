module

public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementJ
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EllipticOnePole
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.QuasiPeriodConstIsogeny
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalI
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.BaseChangeCompatible
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.DivByXSq
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.HasSecondLogDeriv
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementJ
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.NormHalfB2SubTwoTorsionLeOne
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.CurveSecondLogDerivative
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
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.CurveEndoAll
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.BridgeTwoMore
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.AnaSysW
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.CurveHyp
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.IsTransSys
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.OneAddMulDerivLogSubst
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.Series
import Mathlib.RingTheory.SimpleRing.Principal
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementX
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.Joints
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.BridgeTwoMore
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.TwoTorsionU

-- Source module: Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.TwoTorsionCurveToSeries

section

@[expose] public section

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.B.Crv2

open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 swap2 DivAB)
open Formalism.G (unitBall)
open Formalism.L2.Th1.C (wpShift HasSecondLogDeriv wTr IsLogPair mulBy EndInt PhNormAt IsBinomScalar)
open Formalism.L2.Th1.A (fgl iSer logSer expSer wpReg g₂ g₃ IntModel xS tS xPlus bridgeWp bridgeLaw
  bridgeCurve bridgeCurve3)

section Alg

variable {K : Type} [Field K] [CharZero K]

theorem logPair (W : WeierstrassCurve K) : IsLogPair (logSer W) (expSer W) :=
  (Formalism.L2.Th1.C.curveFrame K ⊤ W ⟨trivial, trivial, trivial, trivial, trivial⟩).1

end Alg

section Norm

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K]

theorem twoHyp (W : WeierstrassCurve K) (xT yT : K) (hW : IntModel W)
    (hE : W.toAffine.Equation xT yT) (h2 : 2 * yT + W.a₁ * xT + W.a₃ = 0) (hx : ‖xT‖ ≤ 1)
    (hy : ‖yT‖ ≤ 1) : TwoHyp (g₂ W) (g₃ W) (W.b₂ / 12) W.a₁ W.a₃ xT yT :=
  ⟨h2, Crv.two_torsion_x_root_of_cubic W xT yT hE h2, hx, hy, hW.1, Crv.norm_kap W xT yT hW h2 hx hy⟩

end Norm

end Formalism.L2.Th1.B.Crv2
end
end
end

-- Source module: Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.ThetaFromPhiDerivative

section

@[expose] public section

open PowerSeries

noncomputable section

namespace Formalism.L2.Th1.E

namespace Two

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K]

theorem fExp_zero : Formalism.L2.Th1.B.fExp (0 : PowerSeries K) = 1 := by
  have h := Formalism.L2.Th1.B.fExp_add (K := K) (ι := Unit) (f := 0) (g := 0) (map_zero _) (map_zero _)
  rw [add_zero] at h
  have hc : MvPowerSeries.constantCoeff (Formalism.L2.Th1.B.fExp (0 : MvPowerSeries Unit K)) = 1 :=
    Formalism.L2.Th1.B.constantCoeff_fExp (map_zero _)
  have hne : Formalism.L2.Th1.B.fExp (0 : MvPowerSeries Unit K) ≠ 0 := by
    intro h0; rw [h0, map_zero] at hc; exact zero_ne_one hc
  exact (mul_left_cancel₀ hne (h.symm.trans (mul_one _).symm))

theorem oneUnit_fExp_neg {f : PowerSeries K} (h : Formalism.InvariantFactorPaths.G7.Simeq (ι := Unit) f 0) :
    OneUnit (Formalism.L2.Th1.B.fExp (-f)) := by
  obtain ⟨h0, hI⟩ := h
  rw [sub_zero] at h0 hI
  have h0n : MvPowerSeries.constantCoeff (-f : MvPowerSeries Unit K) = 0 := by
    rw [map_neg, h0, neg_zero]
  have hf : OneUnit (Formalism.L2.Th1.B.fExp f) :=
    ⟨Formalism.L2.Th1.B.constantCoeff_fExp h0, (Ser.intS_iff_integral _).2 hI⟩
  refine Ser.oneUnit_of_mul_eq_one hf ?_
  rw [← Formalism.L2.Th1.B.fExp_add h0 h0n, add_neg_cancel]
  exact fExp_zero

end Two

end Formalism.L2.Th1.E
end
end
end

-- Source module: Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.Th0FromPhPrime

section

@[expose] public section

namespace Formalism.L2.Th1.E

theorem inWTh0 : InWTh0 := even_theta_half_period_in_model

end Formalism.L2.Th1.E
end
end

-- Source module: Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.Th0TwoAnalyticOf

section

@[expose] public section

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.B.An2

open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq)
open Formalism.G (unitBall)
open Formalism.L2.Th1.F (MulStable IsKerReps taylor0 pSeries)
open Formalism.L2.Th1.E (Unif ptW inW px py IntCurve OneUnit)
open Formalism.L2.Th1.A (fgl iSer logSer expSer wpReg g₂ g₃ IntModel xS)

theorem norm_transport (ι : ℂ ≃+* ℂ_[2]) (α : ℂ) (n : ℕ) (h : ((n : ℝ) + 1) = Complex.normSq α) :
    ι α * ι (conj α) = (n : ℂ_[2]) + 1 := by
  rw [← map_mul, Complex.mul_conj, ← h]
  push_cast
  rw [map_add (f := _), map_natCast, map_one]

theorem Th0TwoAnalytic_of (hE : HalfFibreExists) (hF : FibreZInstance) (hH : HalfShiftSeries)
    (hM : FibreMap) : ThetaZeroTwoAnalytic := by
  intro L ι W hU hW α ω₀ b b' hα hmul hω hω2 hb hb' hnb hnb' hno hxT hxQ
  obtain ⟨Sq, hSq⟩ := hE L α ω₀ hα hmul hω hno
  obtain ⟨S, hS⟩ := Formalism.L2.Th1.F.kerRepsExist L α hα hmul
  obtain ⟨hcard, hfib⟩ := hF L α ω₀ S Sq hα hmul hS hω hω2 hSq
  rw [hH L ω₀ hω hω2] at hfib
  have hfib' := hM ℂ ℂ_[2] (ι : ℂ →+* ℂ_[2]) _ _ Sq _ _ _ _ _ hfib
  have hP := Formalism.L2.Th1.E.weierstrass_series_eq_transported 2 L ι W hU

  have hpx : px W (ptW 2 L ι W (ω₀ / 2)) = ι (L.weierstrassP (ω₀ / 2)) - W.b₂ / 12 :=
    Formalism.L2.Th1.E.AnaSysW.px_ptW hU _ hω2
  have he : px W (ptW 2 L ι W (ω₀ / 2)) + W.b₂ / 12 = ι (L.weierstrassP (ω₀ / 2)) := by
    rw [hpx]; ring
  have hEq : W.toAffine.Equation (px W (ptW 2 L ι W (ω₀ / 2)))
      (Formalism.L2.Th1.E.AnaSysW.yc 2 L ι W (ω₀ / 2)) := by
    rw [hpx]
    exact (Formalism.L2.Th1.E.AnaSysW.nonsing hU _ hω2).1
  have hd : L.derivWeierstrassP (ω₀ / 2) = 0 :=
    (Formalism.L2.Th1.F.pDerivZero L _ hω2).2 (by
      have : 2 * (ω₀ / 2) = ω₀ := by ring
      rw [this]; exact hω)
  have h2 : 2 * Formalism.L2.Th1.E.AnaSysW.yc 2 L ι W (ω₀ / 2) + W.a₁ * px W (ptW 2 L ι W (ω₀ / 2)) + W.a₃
      = 0 := by
    rw [hpx]
    unfold Formalism.L2.Th1.E.AnaSysW.yc
    rw [hd, map_zero]
    ring
  have hy : ‖Formalism.L2.Th1.E.AnaSysW.yc 2 L ι W (ω₀ / 2)‖ ≤ 1 :=
    ((Formalism.L2.Th1.A.bridgeTwoMore ℂ_[2] W _ _ hEq h2).2.2 hW hxT).1

  obtain ⟨hLaw, hi, -⟩ := Formalism.L2.Th1.A.bridgeLaw ℂ_[2] W hW
  have hlp := Crv2.logPair W
  obtain ⟨hEnd, hcl, h0, hne, h1, hb1, hb2⟩ :=
    twoAdicScalars ℂ_[2] (fgl W) (logSer W) (expSer W) b b' hLaw hlp hnb hnb'

  have hQn : ∀ Q : Sq, (Q : ℂ) ∉ L.lattice := by
    intro Q hQ
    apply (hSq.1 Q Q.2).2
    rw [two_mul]
    exact add_mem hQ hQ
  have hcQ : ∀ Q : Sq, px W (ptW 2 L ι W (Q : ℂ)) + W.b₂ / 12 = ι (L.weierstrassP (Q : ℂ)) := by
    intro Q
    rw [Formalism.L2.Th1.E.AnaSysW.px_ptW hU _ (hQn Q)]
    ring
  have hk : (ι : ℂ →+* ℂ_[2]) (3 * L.weierstrassP (ω₀ / 2) ^ 2 - L.g₂ / 4) =
      3 * ι (L.weierstrassP (ω₀ / 2)) ^ 2 - ι L.g₂ / 4 := by
    simp only [RingEquiv.coe_toRingHom, map_sub, map_mul, map_pow, map_div₀, map_ofNat]
  rw [map_add (f := _), map_mul, PowerSeries.map_C, PowerSeries.map_C, Map.map_wOf, hk, ← hP] at hfib'
  have hZ : IsFibreZ (wpReg W)
      (PowerSeries.C (px W (ptW 2 L ι W (ω₀ / 2)) + W.b₂ / 12) +
        PowerSeries.C (3 * (px W (ptW 2 L ι W (ω₀ / 2)) + W.b₂ / 12) ^ 2 - g₂ W / 4) *
          wOf (px W (ptW 2 L ι W (ω₀ / 2)) + W.b₂ / 12) (wpReg W))
      (fun Q : Sq => px W (ptW 2 L ι W (Q : ℂ)) + W.b₂ / 12)
      (fun Q : Sq => PowerSeries.map (ι : ℂ →+* ℂ_[2]) (taylor0 fun z => L.weierstrassP (z + (Q : ℂ))))
      (fun Q : Sq => PowerSeries.map (ι : ℂ →+* ℂ_[2]) (taylor0 fun z => L.weierstrassP (z - (Q : ℂ))))
      (ι α)
      (ι (∑ P ∈ S, L.weierstrassP P)) := by
    rw [he, hU.1]
    simp only [hcQ]
    exact hfib'
  have hN : ι α * ι (conj α) = 2 * (Fintype.card Sq : ℂ_[2]) := by
    rw [norm_transport ι α S.card (Formalism.L2.Th1.F.kerRepsCard L α S hα hmul hS), Fintype.card_coe]
    exact_mod_cast hcard.symm
  have hS2 : ι α * (ι α - ι (conj α)) * ι (Formalism.L2.Th1.F.s2 L) = ι (∑ P ∈ S, L.weierstrassP P) := by
    rw [← Formalism.L2.Th1.F.quasiPeriodConstIsogeny L α S hα hmul hS, ← Complex.mul_conj, ← map_sub, ← map_mul,
      ← map_mul]
    congr 1
    ring
  have hal : algebraMap ℚ_[2] ℂ_[2] (b : ℚ_[2]) = ι α := hb.symm
  have halb : algebraMap ℚ_[2] ℂ_[2] (b' : ℚ_[2]) = ι (conj α) := hb'.symm
  simp only [hal, halb] at hEnd hcl h0 hne h1 hb1 hb2
  have hV := (th0Vanish ℂ_[2] (g₂ W) (g₃ W) (ι (Formalism.L2.Th1.F.s2 L)) (W.b₂ / 12) W.a₁ W.a₃
    (px W (ptW 2 L ι W (ω₀ / 2))) (Formalism.L2.Th1.E.AnaSysW.yc 2 L ι W (ω₀ / 2)) (ι α) (ι (conj α))
    (ι (∑ P ∈ S, L.weierstrassP P)) (wpReg W) (logSer W) (expSer W) (iSer W) (xS W) (fgl W) Sq
    (fun Q : Sq => px W (ptW 2 L ι W (Q : ℂ))) _ _ (Formalism.L2.Th1.A.bridgeWp ℂ_[2] W) hLaw hi hlp
    (Formalism.L2.Th1.A.bridgeCurve ℂ_[2] W hW) (Formalism.L2.Th1.A.bridgeCurve3 ℂ_[2] W hW)
    (Crv2.twoHyp W _ _ hW hEq h2 hxT hy) (fun Q => hxQ _ (hSq.1 Q Q.2).1) hZ hN hS2 hEnd hcl h0 hne
    h1 hb1 hb2).1
  have hV' : Simeq (ι := Unit)
      (evenSigmaLogAtTwoTorsion W (ι (Formalism.L2.Th1.F.s2 L)) (px W (ptW 2 L ι W (ω₀ / 2)))) 0 := hV
  refine ⟨hV', ?_⟩
  rw [Formalism.L2.Th1.E.inWTh0 2 L ι W hU ω₀ hω hω2]
  exact Formalism.L2.Th1.E.Two.oneUnit_fExp_neg hV'

end Formalism.L2.Th1.B.An2
end
end
end
