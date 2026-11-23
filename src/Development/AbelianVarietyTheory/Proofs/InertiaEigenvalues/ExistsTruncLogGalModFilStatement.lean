module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.CrystallinePeriods.CrisIncl
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinApproxRootGaloisSubMemBdRFilStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsApproxRootEisensteinAwayPrimeStatement
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisGaloisActionFontaineTEqCyclotomic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisLogTeichmullerUniqueGaloisFrobeniusBdR
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeffEqMkRootT
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLogTeichmullerAcrisEqMuMulUnit
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KummerNotCoboundary
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddMulDerivativeTrunc

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMulSubPrimePowDvdEPow

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.BK

theorem exists_mul_sub_pow_dvd_of_dvd_sub : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (M m : ℕ) (q : bk.S),
    bk.E ∣ q - (l : bk.S) ^ M * X → ∃ (N : ℕ) (r : bk.S), bk.E ^ m ∣ q * r - (l : bk.S) ^ N := by
  intro l _ K bk M m q hq
  obtain ⟨w, hw⟩ := bk.coeff_zero
  obtain ⟨t, ht⟩ := hq
  set P : bk.S := ((bk.Ep.divX : Polynomial (Wq l bk.a)) : (Wq l bk.a)⟦X⟧) with hP
  have hE : bk.E = X * P + (l : bk.S) * C (w : Wq l bk.a) := by
    have h := Polynomial.X_mul_divX_add bk.Ep
    have h2 := congrArg (fun p : Polynomial (Wq l bk.a) => (p : (Wq l bk.a)⟦X⟧)) h
    simp only [Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_X, Polynomial.coe_C, hw, map_mul,
      map_natCast] at h2
    change (bk.Ep : (Wq l bk.a)⟦X⟧) = _
    rw [← h2, hP]
    congr 2
    rw [← map_natCast (Polynomial.C (R := Wq l bk.a)), Polynomial.coe_C, map_natCast]
  have hu : C (w : Wq l bk.a) * C ((w⁻¹ : (Wq l bk.a)ˣ) : Wq l bk.a) = (1 : bk.S) := by
    rw [← map_mul, Units.mul_inv, map_one]
  set c' : bk.S := C ((w⁻¹ : (Wq l bk.a)ˣ) : Wq l bk.a)
  set a : bk.S := (l : bk.S) ^ (M + 1)
  set h₁ : bk.S := -((l : bk.S) ^ M + t * P) * c'
  set b : bk.S := bk.E * h₁
  have hqr : q * (-c' * P) = a + b := by
    simp only [a, b, h₁]
    linear_combination (-c' * P) * ht + (c' * (l : bk.S) ^ M) * hE + (l : bk.S) ^ (M + 1) * hu
  have key := geom_sum₂_mul a (-b) m
  rw [sub_neg_eq_add] at key
  refine ⟨(M + 1) * m, (-c' * P) * ∑ i ∈ Finset.range m, a ^ i * (-b) ^ (m - 1 - i), -((-h₁) ^ m), ?_⟩
  rw [pow_mul, ← mul_assoc, hqr, mul_comm (a + b), key]
  simp only [b]
  rw [neg_pow, mul_pow, neg_pow h₁]
  ring

end GlobalTheory.BSP.BK
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMulSubPrimePowDvdEPowStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_mul_sub_prime_pow_dvd_E_pow : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (M m : ℕ) (q : bk.S),
    bk.E ∣ q - (l : bk.S) ^ M * X → ∃ (N : ℕ) (r : bk.S), bk.E ^ m ∣ q * r - (l : bk.S) ^ N := by
  first | (exact @GlobalTheory.BSP.BK.exists_mul_sub_pow_dvd_of_dvd_sub) | (exact GlobalTheory.BSP.BK.exists_mul_sub_pow_dvd_of_dvd_sub) | (intros; apply GlobalTheory.BSP.BK.exists_mul_sub_pow_dvd_of_dvd_sub  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisFactorTiltLogBdRPlus

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.InertiaEigenvalues.TiltGalLog

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem zeta_pow_compat {l : ℕ} [Fact l.Prime] (C : Core l) (c : ℤ_[l]) (m : ℕ) :
    C.ζ m ^ (PadicInt.toZModPow (m + 1) c).val = C.ζ m ^ (PadicInt.toZModPow m c).val := by
  have hz : C.ζ m ^ (l ^ m) = 1 := TAct.zeta_pow C m
  have hred : ∀ a : ℕ, C.ζ m ^ a = C.ζ m ^ (a % l ^ m) := fun a => by
    conv_lhs => rw [← Nat.mod_add_div a (l ^ m), pow_add, pow_mul, hz, one_pow, mul_one]
  have hmod : (PadicInt.toZModPow (m + 1) c).val ≡ (PadicInt.toZModPow m c).val [MOD l ^ m] := by
    rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_val, ZMod.natCast_zmod_val]
    have h := congrArg (fun f : ℤ_[l] →+* ZMod (l ^ m) => f c)
      (PadicInt.zmod_cast_comp_toZModPow (p := l) m (m + 1) (Nat.le_succ m))
    simpa using h
  rw [hred, hmod, ← hred]

theorem rootT_mul {l : ℕ} [Fact l.Prime] (a b : Per.Fl l) (m : ℕ) :
    rootT (a * b) m = rootT a m * rootT b m := by
  unfold rootT
  rw [← map_mul]
  congr 1
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      Function.iterate_succ_apply', ih, map_mul]

theorem gal_factor_log : ∀ (l : ℕ) [Fact l.Prime] (C : Core l) (x : Per.Fl l) (g : GQ l) (c : ℤ_[l]),
    (∀ m : ℕ, rootT (Per.σF g x) m = rootT C.ε m ^ (PadicInt.toZModPow m c).val * rootT x m) →
    ∃ e : Per.Fl l, Per.σF g x = x * e ∧ e.untilt = 1 ∧
      Per.IsLog l e (aDp l (Per.zA l c) * C.j C.t) := by
  intro l _ C x g c H
  obtain ⟨e, he⟩ := NoLog.exists_tilt (fun m => C.ζ m ^ (PadicInt.toZModPow m c).val)
    (fun m => by
      show (C.ζ (m + 1) ^ (PadicInt.toZModPow (m + 1) c).val) ^ l = C.ζ m ^ (PadicInt.toZModPow m c).val
      rw [← pow_mul, mul_comm, pow_mul, C.ζ_succ, zeta_pow_compat]) 1 (by simp [C.ζ_zero])
  have he1 : e.untilt = 1 := Subtype.ext (by
    have := he 0
    rw [C.ζ_zero, one_pow, map_one] at this
    exact this)
  have hre : ∀ m, rootT e m = rootT C.ε m ^ (PadicInt.toZModPow m c).val := fun m =>
    Subtype.ext (by rw [he m, SubmonoidClass.coe_pow, C.ε_root m, map_pow])
  have hxe : Per.σF g x = x * e := by
    refine Perfection.ext fun n => ?_
    change PreTilt.coeff n (Per.σF g x) = PreTilt.coeff n (x * e)
    rw [coeff_eq_mk_rootT, coeff_eq_mk_rootT, H n, rootT_mul, hre n, mul_comm]
  obtain ⟨y, -, hy, -⟩ := exists_isLogA l e he1
  have hyeq := NoLog.log_eq C e c y he hy
  refine ⟨e, hxe, he1, ?_⟩
  have h := LogFun.isLog_map he1 hy C.j_cris
  have hj : C.j (algebraMap (Per.Ainf l) (Per.Acris l) (Per.zA l c)) = aDp l (Per.zA l c) := by
    rw [GlobalTheory.RingIface.tower, C.j_cris.on0, Subalgebra.coe_algebraMap, aDp, RingHom.comp_apply]
  rwa [hyeq, map_mul, hj] at h

end GlobalTheory.InertiaEigenvalues.TiltGalLog
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisFactorTiltLogBdRPlusStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.galois_factor_tilt_log_bdRPlus : ∀ (l : ℕ) [Fact l.Prime] (C : Core l) (x : Per.Fl l) (g : GQ l) (c : ℤ_[l]),
    (∀ m : ℕ, rootT (Per.σF g x) m = rootT C.ε m ^ (PadicInt.toZModPow m c).val * rootT x m) →
    ∃ e : Per.Fl l, Per.σF g x = x * e ∧ e.untilt = 1 ∧
      Per.IsLog l e (aDp l (Per.zA l c) * C.j C.t) := by
  first | (exact @GlobalTheory.InertiaEigenvalues.TiltGalLog.gal_factor_log) | (exact GlobalTheory.InertiaEigenvalues.TiltGalLog.gal_factor_log) | (intros; apply GlobalTheory.InertiaEigenvalues.TiltGalLog.gal_factor_log  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTruncLogGalModFil

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.BK

theorem exists_truncLog_gal_mod_fil : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l) (c : ↥(GK K) → ℤ_[l]),
    (∀ (g : ↥(GK K)) (m : ℕ), rootT (Per.σF (g : GQ l) bk.flat) m =
      rootT C.ε m ^ (PadicInt.toZModPow m (c g)).val * rootT bk.flat m) →
    ∀ m : ℕ, ∃ (k : ℕ) (s : bk.S), bk.E ∣ s ∧ ∀ g : ↥(GK K),
      aDp l (Per.σA (g : GQ l) (bk.ev s) - bk.ev s) -
        (l : Per.BdRp l) ^ k * (aDp l (Per.zA l ((bk.Ep.natDegree : ℤ_[l]) * c g)) * C.j C.t) ∈ Per.FilP l m := by
  intro l _ K bk C c hc m
  obtain ⟨M, q, hq1, hq2⟩ := GlobalTheory.T.exists_approx_root_eisenstein_away_prime l K bk m
  obtain ⟨N, r, hr⟩ := GlobalTheory.T.exists_mul_sub_prime_pow_dvd_E_pow l K bk M m q hq1
  obtain ⟨d, hd⟩ := GlobalTheory.RingBasics.exists_pow_div_factorial l m
  set w₀ : bk.S := ((l : bk.S) ^ M * X - q) * r with hw₀
  have hE : bk.E ∣ w₀ := by
    have e1 : (l : bk.S) ^ M * X - q = -(q - (l : bk.S) ^ M * X) := by ring
    rw [hw₀, e1]
    exact (dvd_neg.2 hq1).mul_right _
  set s' : bk.S := ∑ j ∈ Finset.range m, (-1) ^ j * ((m.factorial / (j + 1) : ℕ) : bk.S) * w₀ ^ (j + 1) *
    (l : bk.S) ^ (N * (m - (j + 1))) with hs'
  set s : bk.S := (bk.Ep.natDegree : bk.S) * PowerSeries.C (algebraMap ℤ_[l] (Wq l bk.a) d) * s' with hsdef
  refine ⟨m + N * m, s, ?_, fun g => ?_⟩
  · rw [hsdef]
    apply Dvd.dvd.mul_left
    apply Finset.dvd_sum
    intro j _
    exact ((hE.pow (Nat.succ_ne_zero j)).mul_left _).mul_right _

  set R := Per.AinfP l ⧸ Per.kerP l ^ m
  let qm : Per.AinfP l →+* R := Ideal.Quotient.mk _
  let ι : Per.Ainf l →+* Per.AinfP l := algebraMap (Per.Ainf l) (Per.AinfP l)
  have hev : ∀ x, Per.ev l m (aDp l x) = qm (ι x) := fun x => LogFun.ev_alg m (ι x)
  let I : Ideal R := (Per.kerP l).map qm
  have hI : I ^ m = ⊥ := by
    rw [← Ideal.map_pow]
    exact Ideal.map_quotient_self _
  have hnil : ∀ x ∈ I, x ^ m = 0 := fun x hx => by
    have := Ideal.pow_mem_pow hx m
    rwa [hI, Ideal.mem_bot] at this
  have hR : ∀ n : ℕ, n ≠ 0 → IsUnit (n : R) := fun n hn => by
    have := (GlobalTheory.RingBasics.isUnit_nat l n hn).map qm
    rwa [map_natCast] at this
  obtain ⟨lam, hlam⟩ : ∃ lam : R, (l : R) * lam = 1 := by
    have := (GlobalTheory.RingBasics.isUnit_l l).map qm
    rw [map_natCast] at this
    exact this.exists_right_inv
  let f : bk.S →+* R := qm.comp (ι.comp bk.ev)
  let fσ : bk.S →+* R := qm.comp (ι.comp ((Per.σA (g : GQ l)).comp bk.ev))
  have hEm : ι (bk.ev bk.E) ∈ Per.kerP l := by
    have h0 : Per.θ l (bk.ev bk.E) = 0 := by
      have : bk.ev bk.E ∈ RingHom.ker (Per.θ l) := bk.span_ev ▸ Ideal.mem_span_singleton_self _
      exact this
    first | exact GlobalTheory.RingIface.alg_mem_kerP _ h0 | exact GlobalTheory.RingIface.alg_mem_kerP h0
  have hfE : f bk.E ∈ I := Ideal.mem_map_of_mem _ hEm
  have hfσE : fσ bk.E ∈ I := by
    refine Ideal.mem_map_of_mem _ ?_
    have := GlobalTheory.RingBasics.ker_σ (g : GQ l) hEm
    rwa [Ideal.mem_comap, GlobalTheory.RingBasics.awayMap_algebraMap₂] at this
  have hdvd : ∀ (φ : bk.S →+* R), φ bk.E ∈ I → ∀ x : bk.S, bk.E ^ m ∣ x → φ x = 0 := by
    intro φ hφ x ⟨y, hy⟩
    rw [hy, map_mul, map_pow, hnil _ hφ, zero_mul]
  have hfr : f q * f r = (l : R) ^ N := by
    have := hdvd f hfE _ hr
    rw [map_sub, map_mul, map_pow, map_natCast] at this
    exact sub_eq_zero.1 this
  have hfσr : fσ q * fσ r = (l : R) ^ N := by
    have := hdvd fσ hfσE _ hr
    rw [map_sub, map_mul, map_pow, map_natCast] at this
    exact sub_eq_zero.1 this
  have hσq : fσ q = f q := by
    have h := GlobalTheory.T.eisensteinApproxRoot_galois_sub_mem_bdRFil l K bk m M q hq1 hq2 g
    rw [GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow, hev, map_sub, map_sub] at h
    exact sub_eq_zero.1 h
  have hlamN : (l : R) ^ N * lam ^ N = 1 := by rw [← mul_pow, hlam, one_pow]
  have hσr : fσ r = f r := by
    have hu : IsUnit (f q) := isUnit_iff_exists_inv.2 ⟨f r * lam ^ N, by rw [← mul_assoc, hfr, hlamN]⟩
    apply hu.mul_left_cancel
    rw [← hσq, hfσr, hσq, hfr]
  obtain ⟨e, hxe, he1, hlog⟩ := GlobalTheory.T.galois_factor_tilt_log_bdRPlus l C bk.flat (g : GQ l) (c g) (hc g)
  set τ : R := qm (ι (Per.tm e)) with hτ
  have hσX : fσ X = f X * τ := by
    change qm (ι (Per.σA (g : GQ l) (bk.ev X))) = qm (ι (bk.ev X)) * qm (ι (Per.tm e))
    rw [bk.ev_X, ← map_mul, ← map_mul]
    congr 2
    change Per.σA (g : GQ l) (WittVector.teichmuller l _) = _
    rw [GlobalTheory.RingIface.sigA_teich, hxe, map_mul]
  have hσC : ∀ w, fσ (PowerSeries.C w) = f (PowerSeries.C w) := fun w => by
    change qm (ι (Per.σA (g : GQ l) (bk.ev (PowerSeries.C w)))) = qm (ι (bk.ev (PowerSeries.C w)))
    rw [bk.ev_C, bk.gal_w]
  let T : R → R := fun a => ∑ j ∈ Finset.range m, (-1) ^ j * ((m.factorial / (j + 1) : ℕ) : R) * a ^ (j + 1)
  have hT : ∀ (φ : bk.S →+* R) (a : R), φ w₀ = a * (l : R) ^ N → φ s' = (l : R) ^ (N * m) * T a := by
    intro φ a ha

    simp only [hs', map_sum, map_mul, map_pow, map_neg, map_one, map_natCast, ha, T, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjm : N * m = N * (j + 1) + N * (m - (j + 1)) := by
      rw [← mul_add]; congr 1; have := Finset.mem_range.1 hj; omega
    rw [hjm]
    ring
  set A : R := f w₀ * lam ^ N with hAdef
  set B : R := fσ w₀ * lam ^ N with hBdef
  have hA : f w₀ = A * (l : R) ^ N := by rw [hAdef]; linear_combination (-(f w₀)) * hlamN
  have hB' : fσ w₀ = B * (l : R) ^ N := by rw [hBdef]; linear_combination (-(fσ w₀)) * hlamN
  have hAI : A ∈ I := by
    obtain ⟨u, hu⟩ := hE
    rw [hAdef, hu, map_mul]
    exact I.mul_mem_right _ (I.mul_mem_right _ hfE)
  have hbI : τ - 1 ∈ I := by
    have := Ideal.mem_map_of_mem qm (LogFun.mu_mem he1)
    simpa [GlobalTheory.MemLoc.mu, hτ] using this
  have hB : B = A + (τ - 1) + A * (τ - 1) := by
    rw [hBdef, hAdef]
    simp only [hw₀, map_mul, map_sub, map_pow, map_natCast, hσX, hσq, hσr]
    linear_combination (τ - 1) * lam ^ N * hfr + (τ - 1) * hlamN
  have htr : T B = T A + T (τ - 1) := by
    rw [hB]
    exact LogAdd.trunc_add hR m I hI A (τ - 1) hAI hbI
  have hl := GlobalTheory.CrisIncl.factorial_mul_ev l e _ he1 hlog m
  have hl2 : (m.factorial : R) * Per.ev l m (aDp l (Per.zA l (c g)) * C.j C.t) = T (τ - 1) := by
    rw [hl]

    simp only [T, map_sum, map_mul, map_pow, map_sub, map_one, map_natCast, map_neg, hτ]
    rfl
  have hfC : (m.factorial : R) * f (PowerSeries.C (algebraMap ℤ_[l] (Wq l bk.a) d)) = (l : R) ^ m := by
    have := congrArg (f.comp (PowerSeries.C.comp (algebraMap ℤ_[l] (Wq l bk.a)))) hd
    simpa only [map_mul, map_natCast, map_pow, RingHom.comp_apply] using this
  have hfs' := hT f A hA
  have hfσs' := hT fσ B hB'
  rw [GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow]
  have e1 : Per.ev l m (aDp l (Per.σA (g : GQ l) (bk.ev s) - bk.ev s)) = fσ s - f s := by
    rw [hev, map_sub, map_sub]; rfl
  have e2 : Per.ev l m ((l : Per.BdRp l) ^ (m + N * m) *
      (aDp l (Per.zA l ((bk.Ep.natDegree : ℤ_[l]) * c g)) * C.j C.t)) =
      (l : R) ^ (m + N * m) * ((bk.Ep.natDegree : R) * Per.ev l m (aDp l (Per.zA l (c g)) * C.j C.t)) := by
    simp only [map_mul, map_pow, map_natCast]; ring
  rw [map_sub, e1, e2]
  have e3 : fσ s = (bk.Ep.natDegree : R) * f (PowerSeries.C (algebraMap ℤ_[l] (Wq l bk.a) d)) * fσ s' := by
    rw [hsdef, map_mul, map_mul, map_natCast, hσC]
  have e4 : f s = (bk.Ep.natDegree : R) * f (PowerSeries.C (algebraMap ℤ_[l] (Wq l bk.a) d)) * f s' := by
    rw [hsdef, map_mul, map_mul, map_natCast]
  rw [e3, e4, hfs', hfσs']
  apply (hR _ m.factorial_ne_zero).mul_left_cancel
  rw [mul_zero]
  linear_combination ((bk.Ep.natDegree : R) * (l : R) ^ (N * m) * (T B - T A)) * hfC -
    ((l : R) ^ (m + N * m) * (bk.Ep.natDegree : R)) * hl2 + ((bk.Ep.natDegree : R) * (l : R) ^ (N * m) * (l : R) ^ m) * htr

end GlobalTheory.BSP.BK
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTruncLogGalModFilStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_truncLog_gal_mod_filP : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l) (c : ↥(GK K) → ℤ_[l]),
    (∀ (g : ↥(GK K)) (m : ℕ), rootT (Per.σF (g : GQ l) bk.flat) m =
      rootT C.ε m ^ (PadicInt.toZModPow m (c g)).val * rootT bk.flat m) →
    ∀ m : ℕ, ∃ (k : ℕ) (s : bk.S), bk.E ∣ s ∧ ∀ g : ↥(GK K),
      aDp l (Per.σA (g : GQ l) (bk.ev s) - bk.ev s) -
        (l : Per.BdRp l) ^ k * (aDp l (Per.zA l ((bk.Ep.natDegree : ℤ_[l]) * c g)) * C.j C.t) ∈ Per.FilP l m := by
  first | (exact @GlobalTheory.BSP.BK.exists_truncLog_gal_mod_fil) | (exact GlobalTheory.BSP.BK.exists_truncLog_gal_mod_fil) | (intros; apply GlobalTheory.BSP.BK.exists_truncLog_gal_mod_fil  <;> assumption)
end
end
