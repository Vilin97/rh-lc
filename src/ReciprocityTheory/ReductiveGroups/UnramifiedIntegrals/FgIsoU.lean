module

public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.HasSecondLogDeriv
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementK
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgDefs
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.LatModel
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
public import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.FinalA
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.CurveSecondLogDerivative
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.FirstLevelFromUniversalLaw
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.SecondCoeffConsistency
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.CoeffOneSubstOfConstantCoeffEqZero
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.IsogenyFormulaInstance
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgAnWp
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EndoZInstance
import Formalism.TorsionNormIteration.InvIntegralOfClass
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.IsotropicVanish
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.Points
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.UnitaryInverseIdentity
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.PhNormFromDatum
import Mathlib.Tactic.Polynomial.Basic
import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.NormNatCastClOfNotDvd
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ShortWIntModel
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.CurveHyp

-- Source module: ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgAnIso

section

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
open Formalism.L2.Th1

section MapLemmas

variable {K K' : Type} [Field K] [Field K'] (φ : K →+* K')

theorem anIso_map_dblInt (e : PowerSeries K) :
    PowerSeries.map φ (C.dblInt e) = C.dblInt (PowerSeries.map φ e) := by
  ext n
  simp only [C.dblInt, PowerSeries.coeff_map, PowerSeries.coeff_mk]
  split_ifs
  · simp
  · simp [map_div₀]

theorem anIso_constantCoeff_dblInt (e : PowerSeries K) :
    PowerSeries.constantCoeff (C.dblInt e) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [C.dblInt]

theorem anIso_map_lam (e : PowerSeries K) (s2 : K) :
    PowerSeries.map φ (C.lam e s2) = C.lam (PowerSeries.map φ e) (φ s2) := by
  simp only [C.lam, map_add (f := _), map_mul, map_pow, anIso_map_dblInt, PowerSeries.map_C, PowerSeries.map_X,
    map_div₀, map_ofNat]

theorem anIso_constantCoeff_lam (e : PowerSeries K) (s2 : K) :
    PowerSeries.constantCoeff (C.lam e s2) = 0 := by
  simp [C.lam, anIso_constantCoeff_dblInt]

theorem anIso_map_sgStar [CharZero K] [CharZero K'] (e : PowerSeries K) (s2 : K) :
    PowerSeries.map φ (C.sgStar e s2) = C.sgStar (PowerSeries.map φ e) (φ s2) := by
  have h0 : PowerSeries.constantCoeff (-(C.lam e s2)) = 0 := by
    simp [anIso_constantCoeff_lam]
  have h1 : PowerSeries.map φ (C.mvExp (-(C.lam e s2)))
      = C.mvExp (-(C.lam (PowerSeries.map φ e) (φ s2))) := by
    unfold C.mvExp
    have := PowerSeries.map_subst (h := φ) (PowerSeries.HasSubst.of_constantCoeff_zero' h0)
      (PowerSeries.exp K)
    rw [PowerSeries.map_exp] at this
    rw [← anIso_map_lam, ← map_neg]
    exact this
  rw [C.sgStar, map_mul, PowerSeries.map_X, h1, C.sgStar]

theorem anIso_map_wpShift (e : PowerSeries K) (c : K) :
    PowerSeries.map φ (C.wpShift e c) = C.wpShift (PowerSeries.map φ e) (φ c) := by
  simp only [C.wpShift, map_add (f := _), map_one, map_mul, map_pow, map_sub, PowerSeries.map_C,
    PowerSeries.map_X]

end MapLemmas

theorem isogenyFormula_map {K K' : Type} [Field K] [CharZero K] [Field K'] [CharZero K']
    (φ : K →+* K') (e : PowerSeries K) (s2 : K) {κ : Type} [Fintype κ] (c : κ → K) (al : K)
    (h : C.IsogenyFormula e s2 c al) :
    C.IsogenyFormula (PowerSeries.map φ e) (φ s2) (fun P => φ (c P)) (φ al) := by
  have h' := congrArg (PowerSeries.map φ) h
  unfold C.IsogenyFormula
  simp only [map_mul, map_pow, map_prod, PowerSeries.map_X, PowerSeries.map_C, anIso_map_wpShift,
    anIso_map_sgStar, ← PowerSeries.rescale_map] at h'
  rw [map_pow]
  exact h'

theorem iso_formula (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (α : ℂ)
    (S : Finset ℂ) (hα : α ≠ 0) (hst : F.MulStable L α) (hS : F.IsKerReps L α S) :
    C.IsogenyFormula (A.wpReg (A.shortW (ι L.g₂) (ι L.g₃))) (ι (F.s2 L))
      (fun P : S => ι (L.weierstrassP (P : ℂ))) (ι α) := by
  rw [wp_bridge]
  exact isogenyFormula_map (ι : ℂ →+* ℂ_[l]) (F.pSeries L) (F.s2 L)
    (fun P : S => L.weierstrassP (P : ℂ)) α (F.isogenyFormulaInstance L α S hα hst hS)

end ReciprocityTheory.ChartRestriction.L1
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgPhInt

section

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
open Formalism.L2.Th1

theorem phNorm_int {K : Type} [Field K] [CharZero K] (R : Subring K) (l linv ph : PowerSeries K)
    (hF : C.Frame R l linv ph) (h1 : C.F1 R l linv ph) (hneg : C.PhNormAt R l linv ph (-1) (-1))
    (h2 : (2 : K)⁻¹ ∈ R) (n : ℤ) : C.PhNormAt R l linv ph (n : K) (n : K) := by
  have hl : C.IsLogPair l linv := hF.1
  have hX : MvPowerSeries.constantCoeff (PowerSeries.X : MvPowerSeries Unit K) = 0 :=
    PowerSeries.constantCoeff_X
  have hXpt : C.IsPt R (PowerSeries.X : MvPowerSeries Unit K) := C.Pts.isPt_X

  set q : K → MvPowerSeries Unit K :=
    fun a => PowerSeries.subst (C.fmul l linv a (PowerSeries.X : MvPowerSeries Unit K)) ph with hq
  set B : MvPowerSeries Unit K :=
    C.be0 l linv ph (PowerSeries.X : MvPowerSeries Unit K) (PowerSeries.X : MvPowerSeries Unit K)
    with hB
  have hphX : PowerSeries.subst (PowerSeries.X : MvPowerSeries Unit K) ph = ph :=
    PowerSeries.X_subst ph

  have hE : ∀ m : ℤ, C.LG R (q (1 + (m : K)) - ph - q (m : K) - (m : K) • B) := by
    intro m
    have h := C.zLinInt K R l linv ph hF h1 m Unit _ _ hXpt hXpt
    unfold C.Cong at h
    rw [C.be0] at h
    have e : C.fadd l linv (PowerSeries.X : MvPowerSeries Unit K)
        (C.fmul l linv (m : K) (PowerSeries.X : MvPowerSeries Unit K)) =
        C.fmul l linv (1 + (m : K)) (PowerSeries.X : MvPowerSeries Unit K) := by
      rw [C.Pts.fmul_add hl 1 (m : K) hX, C.Pts.fmul_one hl hX]
    rw [e, hphX] at h
    exact h
  have hq0 : q 0 = 0 := by
    simp only [hq]
    rw [C.Pts.fmul_zero_left hl, PowerSeries.subst_zero_of_constantCoeff_zero hF.2.2]
  have hN : C.LG R (q (-1) - (((-1 : K) * (-1 : K)) • (ph : MvPowerSeries Unit K))) := by
    have h := hneg
    unfold C.PhNormAt C.Cong at h
    rw [C.Pts.mulBy_eq_fmul] at h
    exact h

  have hG : C.LG R (B - (2 : K) • (ph : MvPowerSeries Unit K)) := by
    have h := C.Calc.lg_add (hE (-1)) hN
    have e : (q (1 + ((-1 : ℤ) : K)) - ph - q ((-1 : ℤ) : K) - ((-1 : ℤ) : K) • B) +
        (q (-1) - (((-1 : K) * (-1 : K)) • (ph : MvPowerSeries Unit K))) =
        B - (2 : K) • (ph : MvPowerSeries Unit K) := by
      have e0 : (1 : K) + ((-1 : ℤ) : K) = 0 := by push_cast; ring
      have e1 : (((-1 : ℤ) : K)) = -1 := by push_cast; ring
      rw [e0, hq0, e1]
      module
    rwa [e] at h
  have hstep : ∀ m : ℤ, C.LG R ((q (((m + 1 : ℤ)) : K) -
      ((((m + 1 : ℤ)) : K) * (((m + 1 : ℤ)) : K)) • (ph : MvPowerSeries Unit K)) -
      (q (m : K) - ((m : K) * (m : K)) • (ph : MvPowerSeries Unit K))) := by
    intro m
    have h := C.Calc.lg_add (hE m) (C.lGBinom K R Unit (m : K) (C.intBinomScalar K R m) _ hG)
    have e1 : (((m + 1 : ℤ)) : K) = 1 + (m : K) := by push_cast; ring
    rw [e1]
    convert h using 1
    module
  have main : ∀ m : ℤ, C.LG R (q (m : K) - ((m : K) * (m : K)) • (ph : MvPowerSeries Unit K)) := by
    intro m
    induction m using Int.induction_on with
    | zero =>
      have : q ((0 : ℤ) : K) - (((0 : ℤ) : K) * ((0 : ℤ) : K)) • (ph : MvPowerSeries Unit K) = 0 := by
        rw [Int.cast_zero, hq0]; simp
      rw [this]; exact C.Calc.lg_zero
    | succ i ih =>
      have h := C.Calc.lg_add (hstep i) ih
      rwa [sub_add_cancel] at h
    | pred i ih =>
      have h := C.Calc.lg_add (C.Calc.lg_neg (hstep (-(i : ℤ) - 1))) ih
      rw [sub_add_cancel] at h
      convert h using 1
      abel
  have h := main n
  unfold C.PhNormAt C.Cong
  rw [C.Pts.mulBy_eq_fmul]
  exact h

end ReciprocityTheory.ChartRestriction.L1
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgIsoU

section

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
open Formalism.L2.Th1

theorem exists_powerSeries_square_formula {K : Type} [Field K] [CharZero K] (R : Subring K) (M a ph G : PowerSeries K)
    (c : ℕ) (m : K) (ha : constantCoeff a = 0) (hph : constantCoeff ph = 0)
    (hc : (c : K) + 1 = m)
    (hiso : M ^ 2 * C.mvExp (-((2 : K) • a)) * X ^ (2 * c) =
      G * X ^ (2 * (c + 1)) * C.mvExp (-((2 * ((c : K) + 1)) • ph)))
    (hcong : C.Cong R a (m • ph)) :
    ∃ U : PowerSeries K, constantCoeff U = 1 ∧ C.IntPS R U ∧ M ^ 2 = X ^ 2 * U * G := by
  obtain ⟨h0, h1, hadd, -⟩ := C.mvExpLaws K Unit
  obtain ⟨-, hLadd, -⟩ := C.lGSubgroup K R Unit
  have hD : C.LG R ((a - m • ph) + (a - m • ph)) := hLadd _ _ hcong hcong
  have ha' : MvPowerSeries.constantCoeff a = 0 := ha
  have hph' : MvPowerSeries.constantCoeff ph = 0 := hph
  have c1 : MvPowerSeries.constantCoeff (-((2 : K) • a)) = 0 := by
    rw [map_neg, MvPowerSeries.smul_eq_C_mul, map_mul, ha', mul_zero, neg_zero]
  have c2 : MvPowerSeries.constantCoeff ((2 : K) • a) = 0 := by
    rw [MvPowerSeries.smul_eq_C_mul, map_mul, ha', mul_zero]
  have c3 : MvPowerSeries.constantCoeff (-((2 * ((c : K) + 1)) • ph)) = 0 := by
    rw [map_neg, MvPowerSeries.smul_eq_C_mul, map_mul, hph', mul_zero, neg_zero]
  refine ⟨C.mvExp ((a - m • ph) + (a - m • ph)), h1 _ hD.1, fun n => hD.2 _, ?_⟩
  have e1 : C.mvExp (-((2 : K) • a)) * C.mvExp ((2 : K) • a) = 1 := by
    rw [← hadd _ _ c1 c2, neg_add_cancel, h0]
  have e2 : C.mvExp (-((2 * ((c : K) + 1)) • ph)) * C.mvExp ((2 : K) • a)
      = C.mvExp ((a - m • ph) + (a - m • ph)) := by
    rw [← hadd _ _ c3 c2, hc]
    congr 1
    rw [mul_smul, two_smul, two_smul]
    abel
  have hX : (X : PowerSeries K) ^ (2 * c) ≠ 0 := pow_ne_zero _ X_ne_zero
  apply mul_right_cancel₀ hX
  calc M ^ 2 * X ^ (2 * c)
      = (M ^ 2 * C.mvExp (-((2 : K) • a)) * X ^ (2 * c)) * C.mvExp ((2 : K) • a) := by
        rw [show M ^ 2 * C.mvExp (-((2 : K) • a)) * X ^ (2 * c) * C.mvExp ((2 : K) • a)
          = M ^ 2 * X ^ (2 * c) * (C.mvExp (-((2 : K) • a)) * C.mvExp ((2 : K) • a)) by ring,
          e1, mul_one]
    _ = G * X ^ (2 * (c + 1)) *
          (C.mvExp (-((2 * ((c : K) + 1)) • ph)) * C.mvExp ((2 : K) • a)) := by
        rw [hiso]; ring
    _ = X ^ 2 * C.mvExp ((a - m • ph) + (a - m • ph)) * G * X ^ (2 * c) := by
        rw [e2]; ring

theorem sq_formula (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l])
    (g2 g3 : ℂ_[l]) (hM : LatModel l L ι g2 g3) (n : ℕ) (hn : 0 < n) (S : Finset ℂ)
    (hS : F.IsKerReps L (n : ℂ) S) :
    ∃ U : PowerSeries ℂ_[l], constantCoeff U = 1 ∧ IntegralPS U ∧
      ((uSer g2 g3).subst (C (n : ℂ_[l]) * lgS g2 g3)) ^ 2 =
        X ^ 2 * U * (C ((n : ℂ_[l]) ^ 2) *
          ∏ P ∈ S, (A.xS (A.shortW g2 g3) - C (ι (L.weierstrassP P)) * X ^ 2)) := by
  have h2 : ‖(2 : ℂ_[l])‖ = 1 := by
    have : ¬ l ∣ 2 := fun hd => hl ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp hd)
    exact_mod_cast norm_natCast_Cl_of_not_dvd l this
  have h2R : (2 : ℂ_[l])⁻¹ ∈ unitBall ℂ_[l] := by
    change ‖(2 : ℂ_[l])⁻¹‖ ≤ 1
    rw [norm_inv, h2, inv_one]
  have h4 : ‖(4 : ℂ_[l])‖ = 1 := by
    have : (4 : ℂ_[l]) = 2 * 2 := by norm_num
    rw [this, norm_mul, h2, one_mul]
  set W := A.shortW g2 g3 with hW
  have hco : C.CoeffIn (unitBall ℂ_[l]) W := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact (unitBall ℂ_[l]).zero_mem
    · exact (unitBall ℂ_[l]).zero_mem
    · exact (unitBall ℂ_[l]).zero_mem
    · change ‖-g2 / 4‖ ≤ 1
      rw [norm_div, norm_neg, h4, div_one]; exact hM.n2
    · change ‖-g3 / 4‖ ≤ 1
      rw [norm_div, norm_neg, h4, div_one]; exact hM.n3
  have hb2 : W.b₂ / 12 = 0 := by
    rw [(A.shortInv ℂ_[l] g2 g3).1, zero_div]
  obtain ⟨hLP, hXW, -, hFG, -⟩ := C.curveFrame ℂ_[l] (unitBall ℂ_[l]) W hco
  set s2 : ℂ_[l] := ι (F.s2 L) with hs2
  set ph := B.phO s2 (A.wpReg W) (A.logSer W) with hph
  have hPh : C.IsPh (A.wpReg W) s2 (A.logSer W) ph :=
    (C.phOIsPh ℂ_[l] (A.wpReg W) (A.logSer W) s2 hLP.1 hLP.2.1).2
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hst : F.MulStable L (n : ℂ) := by
    intro ω hω
    have := L.lattice.nsmul_mem hω n
    rwa [nsmul_eq_mul] at this
  have hIF := iso_formula l L ι (n : ℂ) S hn0 hst hS
  rw [← hM.eq2, ← hM.eq3, map_natCast] at hIF
  have hcard : ((Fintype.card S : ℕ) : ℂ_[l]) + 1 = (n : ℂ_[l]) * (n : ℂ_[l]) := by
    have h := F.kerRepsCard L (n : ℂ) S hn0 hst hS
    rw [Complex.normSq_natCast] at h
    have h' : S.card + 1 = n * n := by exact_mod_cast h
    rw [Fintype.card_coe]
    exact_mod_cast h'
  have hU := C.isogenyU ℂ_[l] (A.wpReg W) s2 (A.logSer W) (A.expSer W) ph (A.xS W) (W.b₂ / 12) S
    (fun P : S => ι (L.weierstrassP (P : ℂ))) (n : ℂ_[l]) hLP hPh hXW
    (by simpa only [hb2, add_zero] using hIF)
  have hFr : C.Frame (unitBall ℂ_[l]) (A.logSer W) (A.expSer W) ph := ⟨hLP, hFG, hPh.1⟩
  have hN := phNorm_int (unitBall ℂ_[l]) (A.logSer W) (A.expSer W) ph hFr
    (G.weierstrass_biadditive_mod_equiv ℂ_[l] W hco h2 s2) (G.curveNegNorm ℂ_[l] (unitBall ℂ_[l]) W hco h2R s2) h2R (n : ℤ)
  rw [Int.cast_natCast] at hN
  have hMul : (uSer g2 g3).subst (C (n : ℂ_[l]) * lgS g2 g3)
      = C.mulBy (A.logSer W) (A.expSer W) (n : ℂ_[l]) := by
    rw [lgS_eq_logSer, A.uSerEq ℂ_[l] g2 g3]; rfl
  have hM0 : constantCoeff (C.mulBy (A.logSer W) (A.expSer W) (n : ℂ_[l])) = 0 := by
    rw [← hMul]; exact mult_const g2 g3 _
  have ha : constantCoeff (PowerSeries.subst (C.mulBy (A.logSer W) (A.expSer W) (n : ℂ_[l])) ph) = 0 :=
    constantCoeff_subst_eq_zero hM0 _ hPh.1
  obtain ⟨U, hU1, hU2, hU3⟩ := exists_powerSeries_square_formula (unitBall ℂ_[l])
    (C.mulBy (A.logSer W) (A.expSer W) (n : ℂ_[l]))
    (PowerSeries.subst (C.mulBy (A.logSer W) (A.expSer W) (n : ℂ_[l])) ph) ph
    (C ((n : ℂ_[l]) ^ 2) * ∏ P : S, (A.xS W - C (ι (L.weierstrassP (P : ℂ))) * X ^ 2))
    (Fintype.card S) ((n : ℂ_[l]) * (n : ℂ_[l])) ha hPh.1 hcard
    (by rw [hU]; ring) hN
  refine ⟨U, hU1, hU2, ?_⟩
  rw [hMul, hU3, Finset.prod_coe_sort S
    (fun P => A.xS W - C (ι (L.weierstrassP P)) * X ^ 2)]

end ReciprocityTheory.ChartRestriction.L1
end
end
end
