module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousTerm
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GammaIntegralExpSubstitutionRealLine

section

@[expose] public section

open NumberField MeasureTheory

namespace GlobalTheory.HeckeMellin

open Set

theorem integrableOn_cpow_mul_exp_neg_mul {w : ℂ} (hw : 0 < w.re) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (w - 1) * Complex.exp (-((c : ℂ) * x))) (Ioi 0) := by
  have h := Complex.GammaIntegral_convergent hw
  rw [← mul_zero c, ← integrableOn_Ioi_comp_mul_left_iff _ _ hc] at h
  refine (IntegrableOn.congr_fun (h.const_mul (1 / (c : ℂ) ^ (w - 1)))
    (fun t (ht : 0 < t) => ?_) measurableSet_Ioi)
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hc.le ht.le, Complex.ofReal_exp]
  push_cast
  have hne : (c : ℂ) ^ (w - 1) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
    exact Or.inl (Complex.ofReal_ne_zero.mpr hc.ne')
  field_simp

theorem exp_smul_integrand (w : ℂ) (c t : ℝ) :
    |Real.exp t| • (((Real.exp t : ℝ) : ℂ) ^ (w - 1) * Complex.exp (-((c : ℂ) * (Real.exp t : ℝ)))) =
      Complex.exp (w * t) * Complex.exp (-(c * Real.exp t : ℝ)) := by
  rw [abs_of_pos (Real.exp_pos t), Complex.real_smul]
  have hne : ((Real.exp t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos t).ne'
  rw [Complex.cpow_def_of_ne_zero hne, ← Complex.ofReal_log (Real.exp_pos t).le, Real.log_exp]
  rw [Complex.ofReal_exp]
  push_cast
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

theorem gamma_integral_exp_substitution :
    ∀ (r : ℝ), 0 < r → ∀ w : ℂ, 0 < w.re → Integrable (fun t : ℝ => Complex.exp (w * t) * Complex.exp (-(2 * Real.pi * r * Real.exp t : ℝ))) ∧ ∫ t : ℝ, Complex.exp (w * t) * Complex.exp (-(2 * Real.pi * r * Real.exp t : ℝ)) = Complex.Gamma w * ((2 * Real.pi * r : ℝ) : ℂ) ^ (-w) := by
  intro r hr w hw
  set c : ℝ := 2 * Real.pi * r with hcdef
  have hc : 0 < c := by positivity
  set g : ℝ → ℂ := fun x => (x : ℂ) ^ (w - 1) * Complex.exp (-((c : ℂ) * x)) with hg
  have himg : Real.exp '' univ = Ioi 0 := by rw [image_univ, Real.range_exp]
  have hder : ∀ x ∈ (univ : Set ℝ), HasDerivWithinAt Real.exp (Real.exp x) univ x :=
    fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt
  have hinj : InjOn Real.exp univ := fun x _ y _ h => Real.exp_injective h
  have hfun : (fun t : ℝ => |Real.exp t| • g (Real.exp t)) =
      fun t : ℝ => Complex.exp (w * t) * Complex.exp (-(c * Real.exp t : ℝ)) := by
    funext t
    exact exp_smul_integrand w c t
  constructor
  · have h1 := (integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ hder hinj g).mp
      (by rw [himg]; exact integrableOn_cpow_mul_exp_neg_mul hw hc)
    rw [hfun, integrableOn_univ] at h1
    exact h1
  · have h2 := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hder hinj g
    rw [himg, hfun, Measure.restrict_univ] at h2
    rw [← h2, hg, Complex.integral_cpow_mul_exp_neg_mul_Ioi hw hc, one_div,
      Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hc.le]; exact Real.pi_pos.ne),
      Complex.cpow_neg, mul_comm]

end GlobalTheory.HeckeMellin
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GammaIntegralExpSubstitutionRealLineStatement

section

@[expose] public section

open NumberField MeasureTheory

theorem _root_.GlobalTheory.T.gamma_integral_exp_substitution_real_line : ∀ (r : ℝ), 0 < r → ∀ w : ℂ, 0 < w.re → Integrable (fun t : ℝ => Complex.exp (w * t) * Complex.exp (-(2 * Real.pi * r * Real.exp t : ℝ))) ∧ ∫ t : ℝ, Complex.exp (w * t) * Complex.exp (-(2 * Real.pi * r * Real.exp t : ℝ)) = Complex.Gamma w * ((2 * Real.pi * r : ℝ) : ℂ) ^ (-w) := by
  first | exact @GlobalTheory.HeckeMellin.gamma_integral_exp_substitution | exact GlobalTheory.HeckeMellin.gamma_integral_exp_substitution | (intros; apply GlobalTheory.HeckeMellin.gamma_integral_exp_substitution <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralHeckeMellinGaussIntegrandEqProdGamma

section

@[expose] public section

open NumberField MeasureTheory

noncomputable section
namespace GlobalTheory.HeckeMellinProd

theorem hmon_real_mul (n : ℤ) (c : ℝ) (z : ℂ) :
    GlobalTheory.HeckeTheta.hmon n ((c : ℂ) * z) = (c : ℂ) ^ n.natAbs * GlobalTheory.HeckeTheta.hmon n z := by
  unfold GlobalTheory.HeckeTheta.hmon
  split_ifs with h
  · rw [map_mul, Complex.conj_ofReal, mul_pow]; congr 2; omega
  · rw [mul_pow]; congr 2; omega

def fac (w : ℂ) (r : ℝ) (t : ℝ) : ℂ :=
  Complex.exp (w * t) * Complex.exp (-(2 * Real.pi * r * Real.exp t : ℝ))

theorem coord (n : ℤ) (s : ℂ) (v : ℂ) (y : ℝ) :
    GlobalTheory.HeckeTheta.hmon n ((Real.exp (y / 2) : ℂ) * v) *
      Complex.exp ((-2 * Real.pi * ‖(Real.exp (y / 2) : ℂ) * v‖ ^ 2 : ℝ) : ℂ) * Complex.exp (s * (y : ℂ)) =
    GlobalTheory.HeckeTheta.hmon n v * fac (s + ((|n| : ℤ) : ℂ) / 2) (‖v‖ ^ 2) y := by
  rw [hmon_real_mul, fac]
  have h1 : ((Real.exp (y / 2) : ℝ) : ℂ) ^ n.natAbs = Complex.exp ((n.natAbs : ℂ) * (y / 2)) := by
    rw [Complex.ofReal_exp, ← Complex.exp_nat_mul]; push_cast; rfl
  have h2 : ‖(Real.exp (y / 2) : ℂ) * v‖ ^ 2 = Real.exp y * ‖v‖ ^ 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow,
      ← Real.exp_nat_mul]; congr 2; push_cast; ring
  have h3 : ((|n| : ℤ) : ℂ) = (n.natAbs : ℂ) := by
    rw [← Int.natCast_natAbs, Int.cast_natCast]
  rw [h1, h2, h3]
  have e1 : ((-2 * Real.pi * (Real.exp y * ‖v‖ ^ 2) : ℝ) : ℂ) = -(((2 * Real.pi * ‖v‖ ^ 2 * Real.exp y) : ℝ) : ℂ) := by
    push_cast; ring
  rw [e1]
  calc _ = GlobalTheory.HeckeTheta.hmon n v * (Complex.exp ((n.natAbs : ℂ) * (y / 2)) * Complex.exp (s * (y : ℂ))) *
        Complex.exp (-(((2 * Real.pi * ‖v‖ ^ 2 * Real.exp y) : ℝ) : ℂ)) := by ring
    _ = _ := by rw [← Complex.exp_add, mul_assoc]; congr 3; ring

theorem term_eq (I : Type) [Fintype I] (n : I → ℤ) (s : ℂ) (v : I → ℂ) (y : I → ℝ) :
    GlobalTheory.HeckeMellin.term n s v y =
      ∏ i, GlobalTheory.HeckeTheta.hmon (n i) (v i) * fac (s + ((|n i| : ℤ) : ℂ) / 2) (‖v i‖ ^ 2) (y i) := by
  unfold GlobalTheory.HeckeMellin.term GlobalTheory.HeckeTheta.gauss GlobalTheory.HeckeTheta.dil
  rw [Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact coord (n i) s (v i) (y i)

theorem norm_fac (w : ℂ) (r : ℝ) (t : ℝ) :
    ‖fac w r t‖ = Real.exp (w.re * t) * Real.exp (-(2 * Real.pi * r * Real.exp t)) := by
  rw [fac, norm_mul, Complex.norm_exp, Complex.norm_exp]
  congr 2
  · simp

theorem ofReal_norm_fac (w : ℂ) (r : ℝ) (t : ℝ) :
    ((‖fac w r t‖ : ℝ) : ℂ) = fac (w.re : ℂ) r t := by
  rw [norm_fac, fac]; push_cast; rfl

end GlobalTheory.HeckeMellinProd

namespace GlobalTheory.HeckeMellinProd

theorem fac_int (w : ℂ) (hw : 0 < w.re) (r : ℝ) (hr : 0 < r) :
    Integrable (fac w r) ∧ ∫ t, fac w r t = Complex.Gamma w * ((2 * Real.pi * r : ℝ) : ℂ) ^ (-w) :=
  GlobalTheory.T.gamma_integral_exp_substitution_real_line r hr w hw

theorem norm_fac_int (w : ℂ) (hw : 0 < w.re) (r : ℝ) (hr : 0 < r) :
    ∫ t, ‖fac w r t‖ = Real.Gamma w.re * (2 * Real.pi * r) ^ (-w.re) := by
  have h := (fac_int (w.re : ℂ) (by simpa using hw) r hr).2
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [ofReal_norm_fac]
  rw [h, Complex.ofReal_mul (Real.Gamma w.re), Complex.ofReal_cpow (by positivity), ← Complex.Gamma_ofReal]
  push_cast; ring_nf

theorem mellin_prod : ∀ (I : Type) [Fintype I] (n : I → ℤ) (s : ℂ), 0 < s.re → ∀ v : I → ℂ, (∀ i, v i ≠ 0) → Integrable (GlobalTheory.HeckeMellin.term n s v) ∧ ∫ y, GlobalTheory.HeckeMellin.term n s v y = ∏ i, GlobalTheory.HeckeTheta.hmon (n i) (v i) * Complex.Gamma (s + ((|n i| : ℤ) : ℂ) / 2) * ((2 * Real.pi * ‖v i‖ ^ 2 : ℝ) : ℂ) ^ (-(s + ((|n i| : ℤ) : ℂ) / 2)) ∧ ∫ y, ‖GlobalTheory.HeckeMellin.term n s v y‖ = ∏ i, ‖v i‖ ^ (n i).natAbs * Real.Gamma (s.re + (|n i| : ℝ) / 2) * (2 * Real.pi * ‖v i‖ ^ 2) ^ (-(s.re + (|n i| : ℝ) / 2)) := by
  intro I _ n s hs v hv
  have hw : ∀ i, 0 < (s + ((|n i| : ℤ) : ℂ) / 2).re := fun i => by
    have : (0 : ℝ) ≤ |((n i : ℤ) : ℝ)| := abs_nonneg _
    simp only [Complex.add_re, Complex.div_re, Complex.intCast_re, Complex.intCast_im]
    norm_num
    positivity
  have hr : ∀ i, 0 < ‖v i‖ ^ 2 := fun i => pow_pos (norm_pos_iff.2 (hv i)) 2
  have hwre : ∀ i, (s + ((|n i| : ℤ) : ℂ) / 2).re = s.re + (|n i| : ℝ) / 2 := fun i => by
    simp [Complex.add_re, Complex.div_re]
  set g : I → ℝ → ℂ := fun i t => GlobalTheory.HeckeTheta.hmon (n i) (v i) * fac (s + ((|n i| : ℤ) : ℂ) / 2) (‖v i‖ ^ 2) t with hg
  have hterm : GlobalTheory.HeckeMellin.term n s v = fun y => ∏ i, g i (y i) := funext (term_eq I n s v)
  have hgi : ∀ i, Integrable (g i) := fun i => ((fac_int _ (hw i) _ (hr i)).1.const_mul _)
  refine ⟨?_, ?_, ?_⟩
  · rw [hterm]; exact Integrable.fintype_prod (μ := fun _ => volume) hgi
  · rw [hterm, integral_fintype_prod_volume_eq_prod g]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [hg]
    rw [integral_const_mul, (fac_int _ (hw i) _ (hr i)).2]; ring
  · have hn : (fun y => ‖GlobalTheory.HeckeMellin.term n s v y‖) = fun y => ∏ i, (fun i t => ‖g i t‖) i (y i) := by
      rw [hterm]; funext y; exact norm_prod _ _
    rw [hn, integral_fintype_prod_volume_eq_prod (fun i t => ‖g i t‖)]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [hg, norm_mul]
    rw [integral_const_mul, norm_fac_int _ (hw i) _ (hr i), GlobalTheory.HeckeTheta.norm_hmon, hwre]; ring

end GlobalTheory.HeckeMellinProd
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralHeckeMellinGaussIntegrandEqProdGammaStatement

section

@[expose] public section

open NumberField MeasureTheory

theorem _root_.GlobalTheory.T.integral_heckeMellinGaussIntegrand_eq_prod_gamma : ∀ (I : Type) [Fintype I] (n : I → ℤ) (s : ℂ), 0 < s.re → ∀ v : I → ℂ, (∀ i, v i ≠ 0) → Integrable (GlobalTheory.HeckeMellin.term n s v) ∧ ∫ y, GlobalTheory.HeckeMellin.term n s v y = ∏ i, GlobalTheory.HeckeTheta.hmon (n i) (v i) * Complex.Gamma (s + ((|n i| : ℤ) : ℂ) / 2) * ((2 * Real.pi * ‖v i‖ ^ 2 : ℝ) : ℂ) ^ (-(s + ((|n i| : ℤ) : ℂ) / 2)) ∧ ∫ y, ‖GlobalTheory.HeckeMellin.term n s v y‖ = ∏ i, ‖v i‖ ^ (n i).natAbs * Real.Gamma (s.re + (|n i| : ℝ) / 2) * (2 * Real.pi * ‖v i‖ ^ 2) ^ (-(s.re + (|n i| : ℝ) / 2)) := by
  first | exact @GlobalTheory.HeckeMellinProd.mellin_prod | exact GlobalTheory.HeckeMellinProd.mellin_prod | (intros; apply GlobalTheory.HeckeMellinProd.mellin_prod <;> assumption)
end
end
