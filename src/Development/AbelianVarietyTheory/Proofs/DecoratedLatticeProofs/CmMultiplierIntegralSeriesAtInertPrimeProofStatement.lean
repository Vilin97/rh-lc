module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHomotheticPeriodPairLatticeStatement
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.IsogenyFormulaInstance
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.SecondLogDerivativeUnique
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.CurveSecondLogDerivative
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.PhNormFromDatum
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.AnalyticTransOfAdd
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.CmIntegralityOfTorsionPoints
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.CubeThreeR
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EndoZInstance
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FormalGroupMulByIntegralOfKernelPrimeToL

section

@[expose] public section

open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM

namespace GlobalTheory.Honda


open Formalism.L2.Th1 in
theorem mulBy_coefLe_of_kernel_prime_to :
    ∀ (L : PeriodPair) (l : ℕ) [Fact l.Prime], 5 ≤ l → ∀ (ι : ℂ ≃+* ℂ_[l]), ‖ι L.g₂‖ ≤ 1 → ‖ι L.g₃‖ ≤ 1 → ‖ι L.g₂ ^ 3 - 27 * ι L.g₃ ^ 2‖ = 1 → ∀ (β : ℂ) (N : ℕ), Formalism.L2.Th1.F.MulStable L β → ‖ι β‖ = 1 → 0 < N → ¬ l ∣ N → (∀ z, β * z ∈ L.lattice → (N : ℂ) * z ∈ L.lattice) → CoefLe 1 (Formalism.L2.Th1.C.mulBy (Formalism.L2.Th1.A.logSer (Formalism.L2.Th1.A.shortW (ι L.g₂) (ι L.g₃))) (Formalism.L2.Th1.A.expSer (Formalism.L2.Th1.A.shortW (ι L.g₂) (ι L.g₃))) (ι β)) := by
  intro L l _ hl ι h2 h3 hD β N hst hβ hN hlN hker
  have hβp : ι β ≠ 0 := by
    intro h
    rw [h, norm_zero] at hβ
    exact zero_ne_one hβ
  have hβ0 : β ≠ 0 := by
    intro h
    rw [h, map_zero] at hβp
    exact hβp rfl
  have hW : E.IntCurve (E.curveL l L ι) := E.ScaledModelNorms.intCurve_short l hl _ _ h2 h3 hD
  have hΔ : (E.curveL l L ι).Δ ≠ 0 := by
    intro h
    have := hW.2.2.2.2.2
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have htwo := E.ScaledModelNorms.norm_two l hl
  have hC : C.CoeffIn (Formalism.G.unitBall ℂ_[l]) (E.curveL l L ι) :=
    ⟨hW.1, hW.2.1, hW.2.2.1, hW.2.2.2.1, hW.2.2.2.2.1⟩
  obtain ⟨S, hS⟩ := F.kerRepsExist L β hβ0 hst
  obtain ⟨neg, -, hE⟩ := F.endoZInstance L β S hβ0 hst hS
  have hb2 : (E.curveL l L ι).b₂ = 0 := (A.shortInv ℂ_[l] _ _).1
  have hEp := D.CurveNormEndomorphisms.isEndoZ_map (ι : ℂ →+* ℂ_[l]) hE
  rw [← E.wpBridge l L ι] at hEp
  have hEp' : C.IsEndoZ (A.wpReg (E.curveL l L ι)) neg
      (fun P : S => ι (L.weierstrassP (P : ℂ)) + (E.curveL l L ι).b₂ / 12)
      (fun P : S => PowerSeries.map (ι : ℂ →+* ℂ_[l])
        (F.taylor0 (fun z => L.weierstrassP (z + (P : ℂ))))) (ι β) := by
    rw [hb2]
    simpa using hEp
  have hint : ∀ P : S, ‖ι (L.weierstrassP (P : ℂ))‖ ≤ 1 ∧ ‖ι (L.derivWeierstrassP (P : ℂ))‖ ≤ 1 := by
    intro P
    have := E.cm4Int L l hl ι 1 one_ne_zero (by simpa using h2) (by simpa using h3) (by simpa using hD)
      (P : ℂ) N hN hlN (hker _ (hS.1 P P.2).1) (hS.1 P P.2).2
    simpa using this
  obtain ⟨hLP, hXW, hA, -, -⟩ := C.curveFrame ℂ_[l] (Formalism.G.unitBall ℂ_[l]) (E.curveL l L ι) hC
  have hinv : ∀ x : ℂ_[l], ‖x‖ = 1 → x⁻¹ ∈ Formalism.G.unitBall ℂ_[l] := by
    intro x hx
    show ‖x⁻¹‖ ≤ 1
    rw [norm_inv, hx, inv_one]
  have hM := A.coeffMem.{0} ℂ_[l] (E.curveL l L ι) (Formalism.G.unitBall ℂ_[l]) hC.1 hC.2.1 hC.2.2.1 hC.2.2.2.1
    hC.2.2.2.2
  have key := C.endIntFromDatum ℂ_[l] (Formalism.G.unitBall ℂ_[l]) (A.wpReg (E.curveL l L ι))
    (A.logSer (E.curveL l L ι)) (A.expSer (E.curveL l L ι)) (A.xS (E.curveL l L ι))
    ((E.curveL l L ι).b₂ / 12) S neg (fun P : S => ι (L.weierstrassP (P : ℂ)))
    (fun P : S => PowerSeries.map (ι : ℂ →+* ℂ_[l])
        (F.taylor0 (fun z => L.weierstrassP (z + (P : ℂ)))))
    (fun P : S => E.xT (E.curveL l L ι) (E.ptOf l L ι (P : ℂ))) (ι β)
    ((ι β)⁻¹ * ((Fintype.card S : ℂ_[l]) + 1)) hLP hXW hA (hinv _ htwo)
    ⟨hEp', by rw [← mul_assoc, mul_inv_cancel₀ hβp, one_mul], ?_, ?_, fun P => (hint P).1, hβ.le,
      hinv _ hβ, by rw [hb2, zero_div, mul_zero]; exact zero_mem _⟩
  · exact fun n => key n
  · intro P
    rw [hb2, zero_div, map_zero, add_zero]
    exact E.transWpBridge l L ι (P : ℂ) (hS.1 P P.2).2
  · intro P n
    unfold E.xT
    beta_reduce
    rw [E.ScaledModelNorms.px_ptOf l L ι hΔ _ (hS.1 P P.2).2, E.ScaledModelNorms.py_ptOf l L ι hΔ _ (hS.1 P P.2).2]
    refine (hM.2.2.2.2.2.2.2.2.2.2 _ (hint P).1 _ ?_ n).1
    show ‖ι (L.derivWeierstrassP (P : ℂ)) / 2‖ ≤ 1
    rw [norm_div, htwo, div_one]
    exact (hint P).2

end GlobalTheory.Honda
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FormalGroupMulByIntegralOfKernelPrimeToLStatement

section

@[expose] public section

open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM

theorem _root_.GlobalTheory.T.formalGroup_mulBy_integral_of_kernel_prime_to_l : ∀ (L : PeriodPair) (l : ℕ) [Fact l.Prime], 5 ≤ l → ∀ (ι : ℂ ≃+* ℂ_[l]), ‖ι L.g₂‖ ≤ 1 → ‖ι L.g₃‖ ≤ 1 → ‖ι L.g₂ ^ 3 - 27 * ι L.g₃ ^ 2‖ = 1 → ∀ (β : ℂ) (N : ℕ), Formalism.L2.Th1.F.MulStable L β → ‖ι β‖ = 1 → 0 < N → ¬ l ∣ N → (∀ z, β * z ∈ L.lattice → (N : ℂ) * z ∈ L.lattice) → CoefLe 1 (Formalism.L2.Th1.C.mulBy (Formalism.L2.Th1.A.logSer (Formalism.L2.Th1.A.shortW (ι L.g₂) (ι L.g₃))) (Formalism.L2.Th1.A.expSer (Formalism.L2.Th1.A.shortW (ι L.g₂) (ι L.g₃))) (ι β)) := by
  first | exact @GlobalTheory.Honda.mulBy_coefLe_of_kernel_prime_to | exact GlobalTheory.Honda.mulBy_coefLe_of_kernel_prime_to | (intros; apply GlobalTheory.Honda.mulBy_coefLe_of_kernel_prime_to <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OmegaKSqSubSelfAddEqZero

section

@[expose] public section

open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM

namespace GlobalTheory

theorem omegaK_quadratic : ∀ d : ℕ, d % 4 = 3 → omegaK d ^ 2 - omegaK d + (((d + 1) / 4 : ℕ) : ℂ) = 0 := by
  intro d hd
  have h4 : 4 ∣ d + 1 := by omega
  obtain ⟨k, hk⟩ := h4
  have hk' : (d + 1) / 4 = k := by omega
  rw [hk']
  have hdk : (d : ℂ) = 4 * k - 1 := by
    have : ((d + 1 : ℕ) : ℂ) = ((4 * k : ℕ) : ℂ) := by rw [hk]
    push_cast at this
    linear_combination this
  have hs : ((Real.sqrt d : ℝ) : ℂ) ^ 2 = (d : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    simp
  unfold omegaK
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  linear_combination (-(1:ℂ)/4) * hs + ((Real.sqrt d : ℝ) : ℂ) ^ 2 / 4 * hI - (1/4 : ℂ) * hdk
end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OmegaKSqSubSelfAddEqZeroStatement

section

@[expose] public section

open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM

theorem _root_.GlobalTheory.T.omegaK_sq_sub_self_add_eq_zero : ∀ d : ℕ, d % 4 = 3 → omegaK d ^ 2 - omegaK d + (((d + 1) / 4 : ℕ) : ℂ) = 0 := by
  first | exact @GlobalTheory.omegaK_quadratic | exact GlobalTheory.omegaK_quadratic | (intros; apply GlobalTheory.omegaK_quadratic <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmMultiplierIntegralSeriesAtInertPrimeProof

section

@[expose] public section

open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM

namespace GlobalTheory.Honda

theorem norm_eq_one_of_quad_root {l : ℕ} [Fact l.Prime] (x : ℂ_[l]) (N : ℕ) (hN : ¬ l ∣ N)
    (hx : x ^ 2 - x + (N : ℂ_[l]) = 0) : ‖x‖ = 1 := by
  have hNn : ‖(N : ℂ_[l])‖ = 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] ℂ_[l]), norm_algebraMap', Padic.norm_natCast_eq_one_iff]
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hN
  have hle : ∀ y : ℂ_[l], y ^ 2 - y + (N : ℂ_[l]) = 0 → ‖y‖ ≤ 1 := by
    intro y hy
    by_contra h
    push_neg at h
    have h1 : y ^ 2 = y - N := by linear_combination hy
    have h2 : ‖y - (N : ℂ_[l])‖ ≤ max ‖y‖ ‖(N : ℂ_[l])‖ := by
      rw [sub_eq_add_neg, ← norm_neg (N : ℂ_[l])]
      exact IsUltrametricDist.norm_add_le_max _ _
    rw [hNn, max_eq_left h.le] at h2
    have h3 : ‖y‖ ^ 2 ≤ ‖y‖ := by rw [← norm_pow, h1]; exact h2
    nlinarith
  have h1 := hle x hx
  have h2 := hle (1 - x) (by linear_combination hx)
  have hprod : x * (1 - x) = N := by linear_combination -hx
  have h4 : ‖x‖ * ‖1 - x‖ = 1 := by rw [← norm_mul, hprod, hNn]
  refine le_antisymm h1 ?_
  calc (1 : ℝ) = ‖x‖ * ‖1 - x‖ := h4.symm
    _ ≤ ‖x‖ * 1 := mul_le_mul_of_nonneg_left h2 (norm_nonneg x)
    _ = ‖x‖ := mul_one _

theorem endOmega_holds : EndOmega := by
  intro d L hd hL l _ hl5 hld hsq ι g2 g3 hG n
  obtain ⟨-, -, h2, h3, hΔ, lam, hlam, rfl, rfl⟩ := hG
  have hc0 : ι.symm lam ≠ 0 := by simpa using hlam
  obtain ⟨L', -, hg2, hg3, -, hCM⟩ := GlobalTheory.T.exists_homothetic_periodPair_lattice L (ι.symm lam) hc0
  have hιc : ι (ι.symm lam) = lam := ι.apply_symm_apply lam
  have e2 : ι L'.g₂ = lam ^ 4 * ι L.g₂ := by rw [hg2, map_mul, map_pow, hιc]
  have e3 : ι L'.g₃ = lam ^ 6 * ι L.g₃ := by rw [hg3, map_mul, map_pow, hιc]
  have hL' : HasCMBy d L' := hCM d hL
  have hq := GlobalTheory.T.omegaK_sq_sub_self_add_eq_zero d hd
  set N := (d + 1) / 4 with hNdef
  have hN0 : 0 < N := by omega
  have hlN : ¬ l ∣ N := by
    intro h
    apply hsq
    refine ⟨1, ?_⟩
    have h4 : 4 * N = d + 1 := by omega
    have h5 : ((4 * N : ℕ) : ZMod l) = 0 := by
      rw [Nat.cast_mul, (ZMod.natCast_eq_zero_iff N l).mpr h, mul_zero]
    rw [h4] at h5
    push_cast at h5
    linear_combination h5
  have hιβ : ‖ι (omegaK d)‖ = 1 := by
    apply norm_eq_one_of_quad_root _ N hlN
    have := congrArg ι hq
    simpa using this
  have hNz : ∀ z, omegaK d * z ∈ L'.lattice → (N : ℂ) * z ∈ L'.lattice := by
    intro z hz
    have hz2 : omegaK d * (omegaK d * z) ∈ L'.lattice := hL' _ hz
    have e : (N : ℂ) * z = omegaK d * z - omegaK d * (omegaK d * z) := by linear_combination z * hq
    rw [e]
    exact sub_mem hz hz2
  have key := GlobalTheory.T.formalGroup_mulBy_integral_of_kernel_prime_to_l L' l hl5 ι (by rw [e2]; exact h2) (by rw [e3]; exact h3)
    (by rw [e2, e3]; exact hΔ) (omegaK d) N hL' hιβ hN0 hlN hNz
  rw [e2, e3] at key
  rw [Formalism.L2.Th1.A.uSerEq ℂ_[l]]
  exact key n

end GlobalTheory.Honda
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmMultiplierIntegralSeriesAtInertPrimeProofStatement

section

@[expose] public section

open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM

theorem _root_.GlobalTheory.T.cmMultiplierIntegralSeriesAtInertPrime_proof : EndOmega := by
  first | exact @GlobalTheory.Honda.endOmega_holds | exact GlobalTheory.Honda.endOmega_holds | (intros; apply GlobalTheory.Honda.endOmega_holds <;> assumption)
end
end
