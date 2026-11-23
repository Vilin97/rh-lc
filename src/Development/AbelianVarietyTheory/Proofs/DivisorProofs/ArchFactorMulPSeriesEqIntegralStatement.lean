module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CompletedLStripBounds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormWt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousTerm
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeMellinGaussIntegralNonzeroIntegerStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeMellinGaussIntegrandUnitMulStatement
public import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
public import Mathlib.MeasureTheory.Group.Integral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumNonzeroIntegersPrincipalIdealsUnitsStatement
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
public import ReciprocityTheory.Chebotarev.EulerSum

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumIntegralThetaMellinInterchange

section

@[expose] public section

noncomputable section

open NumberField MeasureTheory

namespace GlobalTheory.HeckeMellin

theorem hasSum_integral_theta (I : Type) [Fintype I] (ι : Type) [Countable ι] (e : ι → I → ℂ) (a : ι → ℂ) (C : ℝ)
    (hC : ∀ j, ‖a j‖ ≤ C) (n : I → ℤ) (s : ℂ) (p : (I → ℝ) → ℝ) (hp : Measurable p) (hp0 : ∀ y, 0 ≤ p y)
    (hp1 : ∀ y, p y ≤ 1) (hint : ∀ j, Integrable (GlobalTheory.HeckeMellin.term n s (e j)))
    (hsum : Summable (fun j => ∫ y, p y * ‖GlobalTheory.HeckeMellin.term n s (e j) y‖)) :
    HasSum (fun j => a j * ∫ y, (p y : ℂ) * GlobalTheory.HeckeMellin.term n s (e j) y)
      (∫ y, (p y : ℂ) * GlobalTheory.HeckeTheta.theta e a n y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ))) := by
  set F : ι → (I → ℝ) → ℂ := fun j y => a j * ((p y : ℂ) * term n s (e j) y) with hF
  have hpm : AEStronglyMeasurable (fun y => (p y : ℂ)) volume :=
    (Complex.measurable_ofReal.comp hp).aestronglyMeasurable
  have hpb : ∀ᵐ y ∂(volume : Measure (I → ℝ)), ‖(p y : ℂ)‖ ≤ 1 := by
    refine Filter.Eventually.of_forall fun y => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp0 y)]; exact hp1 y
  have hpint : ∀ j, Integrable (fun y => (p y : ℂ) * term n s (e j) y) :=
    fun j => (hint j).bdd_mul hpm hpb
  have hFint : ∀ j, Integrable (F j) := fun j => (hpint j).const_mul (a j)
  have hnorm : ∀ j y, ‖F j y‖ = ‖a j‖ * (p y * ‖term n s (e j) y‖) := by
    intro j y
    simp only [hF, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp0 y)]
  have hFsum : Summable fun j => ∫ y, ‖F j y‖ := by
    have hi : ∀ j, ∫ y, ‖F j y‖ = ‖a j‖ * ∫ y, p y * ‖term n s (e j) y‖ := by
      intro j; simp_rw [hnorm]; exact integral_const_mul _ _
    refine Summable.of_nonneg_of_le (fun j => integral_nonneg fun y => norm_nonneg _) (fun j => ?_) (hsum.mul_left C)
    rw [hi]
    exact mul_le_mul_of_nonneg_right (hC j)
      (integral_nonneg fun y => mul_nonneg (hp0 y) (norm_nonneg _))
  have h := hasSum_integral_of_summable_integral_norm hFint hFsum
  have hl : (fun j => ∫ y, F j y) = fun j => a j * ∫ y, (p y : ℂ) * term n s (e j) y := by
    funext j; exact integral_const_mul _ _
  have hr : (fun y => ∑' j, F j y) =
      fun y => (p y : ℂ) * GlobalTheory.HeckeTheta.theta e a n y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ)) := by
    funext y
    simp only [hF, GlobalTheory.HeckeTheta.theta, term]
    rw [← tsum_mul_left, ← tsum_mul_right]
    congr 1; funext j; ring
  rw [hl, hr] at h
  exact h

end GlobalTheory.HeckeMellin
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumIntegralThetaMellinInterchangeStatement

section

@[expose] public section

open NumberField MeasureTheory

theorem _root_.GlobalTheory.T.hasSum_integral_theta_mellin_interchange : ∀ (I : Type) [Fintype I] (ι : Type) [Countable ι] (e : ι → I → ℂ) (a : ι → ℂ) (C : ℝ), (∀ j, ‖a j‖ ≤ C) → ∀ (n : I → ℤ) (s : ℂ) (p : (I → ℝ) → ℝ), Measurable p → (∀ y, 0 ≤ p y) → (∀ y, p y ≤ 1) → (∀ j, Integrable (GlobalTheory.HeckeMellin.term n s (e j))) → Summable (fun j => ∫ y, p y * ‖GlobalTheory.HeckeMellin.term n s (e j) y‖) → HasSum (fun j => a j * ∫ y, (p y : ℂ) * GlobalTheory.HeckeMellin.term n s (e j) y) (∫ y, (p y : ℂ) * GlobalTheory.HeckeTheta.theta e a n y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ))) := by
  first | exact @GlobalTheory.HeckeMellin.hasSum_integral_theta | exact GlobalTheory.HeckeMellin.hasSum_integral_theta | (intros; apply GlobalTheory.HeckeMellin.hasSum_integral_theta <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitUnfoldIntegralPartitionOfUnity

section

@[expose] public section

open NumberField MeasureTheory

namespace GlobalTheory.OrbitUnfold

theorem hasSum_integral_translate {I : Type} [Fintype I] {U : Type} [Countable U]
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (t : U → I → ℝ) (p : (I → ℝ) → ℝ) (hp : Measurable p) (hp0 : ∀ y, 0 ≤ p y)
    (hsum : ∀ y, HasSum (fun u => p (y - t u)) 1) (h : (I → ℝ) → E) (hh : Integrable h) :
    HasSum (fun u => ∫ y, p y • h (y + t u)) (∫ y, h y) := by
  have key : ∀ u, ∫ y, p y • h (y + t u) = ∫ y, p (y - t u) • h y := by
    intro u
    have := integral_add_right_eq_self (μ := (volume : Measure (I → ℝ)))
      (fun y => p (y - t u) • h y) (t u)
    simpa using this
  simp_rw [key]
  refine hasSum_integral_of_dominated_convergence (fun u y => p (y - t u) * ‖h y‖) ?_ ?_ ?_ ?_ ?_
  · intro u
    exact ((hp.comp (measurable_sub_const (t u))).aestronglyMeasurable).smul
      hh.aestronglyMeasurable
  · intro u
    refine ae_of_all _ (fun y => ?_)
    rw [norm_smul, Real.norm_of_nonneg (hp0 _)]
  · exact ae_of_all _ (fun y => ((hsum y).mul_right ‖h y‖).summable)
  · refine hh.norm.congr (ae_of_all _ (fun y => ?_))
    simp only [((hsum y).mul_right ‖h y‖).tsum_eq, one_mul]
  · refine ae_of_all _ (fun y => ?_)
    simpa using (hsum y).smul_const (h y)

theorem orbit_unfold : ∀ (I : Type) [Fintype I] (U : Type) [Countable U] (t : U → I → ℝ)
    (p : (I → ℝ) → ℝ), Measurable p → (∀ y, 0 ≤ p y) → (∀ y, HasSum (fun u => p (y - t u)) 1) →
    ∀ g : (I → ℝ) → ℂ, Integrable g →
      HasSum (fun u => ∫ y, (p y : ℂ) * g (y + t u)) (∫ y, g y) ∧
      HasSum (fun u => ∫ y, p y * ‖g (y + t u)‖) (∫ y, ‖g y‖) := by
  intro I _ U _ t p hp hp0 hsum g hg
  refine ⟨?_, ?_⟩
  · have := hasSum_integral_translate t p hp hp0 hsum g hg
    simpa [Complex.real_smul] using this
  · have := hasSum_integral_translate t p hp hp0 hsum (fun y => ‖g y‖) hg.norm
    simpa [smul_eq_mul] using this

end GlobalTheory.OrbitUnfold
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitUnfoldIntegralPartitionOfUnityStatement

section

@[expose] public section

open NumberField MeasureTheory

theorem _root_.GlobalTheory.T.orbit_unfold_integral_partition_of_unity : ∀ (I : Type) [Fintype I] (U : Type) [Countable U] (t : U → I → ℝ) (p : (I → ℝ) → ℝ), Measurable p → (∀ y, 0 ≤ p y) → (∀ y, HasSum (fun u => p (y - t u)) 1) → ∀ g : (I → ℝ) → ℂ, Integrable g → HasSum (fun u => ∫ y, (p y : ℂ) * g (y + t u)) (∫ y, g y) ∧ HasSum (fun u => ∫ y, p y * ‖g (y + t u)‖) (∫ y, ‖g y‖) := by
  first | exact @GlobalTheory.OrbitUnfold.orbit_unfold | exact GlobalTheory.OrbitUnfold.orbit_unfold | (intros; apply GlobalTheory.OrbitUnfold.orbit_unfold <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchFactorMulPSeriesEqIntegral

section

@[expose] public section

noncomputable section

open NumberField MeasureTheory

namespace GlobalTheory.HeckeMellin

theorem archFactor_mul_pSeries_eq_integral : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∀ (n : I → ℤ), (∃ i, n i ≠ 0) → ∀ (F : NumberField.RingOfIntegers K → ℂ) (C : ℝ), (∀ α, ‖F α‖ ≤ C) → (∀ (u : (NumberField.RingOfIntegers K)ˣ) (α : NumberField.RingOfIntegers K), F ((u : NumberField.RingOfIntegers K) * α) * GlobalTheory.HeckeStrip.wt φ n (((u : NumberField.RingOfIntegers K) * α : NumberField.RingOfIntegers K) : K) = F α * GlobalTheory.HeckeStrip.wt φ n (α : K)) → ∀ p : (I → ℝ) → ℝ, Measurable p → (∀ y, 0 ≤ p y) → (∀ y, HasSum (fun u : (NumberField.RingOfIntegers K)ˣ => p (y + GlobalTheory.HeckeTheta.ulog φ u)) 1) → ∀ s : ℂ, 1 < s.re → GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.archFactor n s * GlobalTheory.HeckeStrip.pSeries F φ n s = 2 ^ Fintype.card I * ∫ y, (p y : ℂ) * GlobalTheory.HeckeTheta.theta (fun α : NumberField.RingOfIntegers K => GlobalTheory.HeckeTheta.emb φ (α : K)) F n y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ)) := by
  intro K _ _ _ I _ φ hφ n hn F C hF hinv p hp hp0 hsum s hs
  haveI : Countable (𝓞 K) := (RingOfIntegers.basis K).equivFun.injective.countable
  haveI : Countable (𝓞 K)ˣ := (Units.val_injective (α := 𝓞 K)).countable
  have hs0 : 0 < s.re := by linarith
  set tm : 𝓞 K → (I → ℝ) → ℂ := fun α => GlobalTheory.HeckeMellin.term n s (GlobalTheory.HeckeTheta.emb φ (α : K)) with htm
  have hulog_inv : ∀ u : (𝓞 K)ˣ, GlobalTheory.HeckeTheta.ulog φ u⁻¹ = - GlobalTheory.HeckeTheta.ulog φ u := by
    intro u; funext i
    simp only [GlobalTheory.HeckeTheta.ulog, Pi.neg_apply]
    rw [← Real.log_inv, ← inv_pow, ← norm_inv, ← map_inv₀]
    congr 4
    have h := congrArg (fun x : 𝓞 K => (x : K)) (Units.inv_mul u)
    push_cast at h
    exact eq_inv_of_mul_eq_one_left h
  have hsum' : ∀ y, HasSum (fun u : (𝓞 K)ˣ => p (y - GlobalTheory.HeckeTheta.ulog φ u)) 1 := by
    intro y
    rw [← (Equiv.inv (𝓞 K)ˣ).hasSum_iff]
    simpa [Function.comp_def, hulog_inv, sub_neg_eq_add] using hsum y
  have hp1 : ∀ y, p y ≤ 1 := fun y => by
    have h := le_hasSum (hsum y) 1 (fun u _ => hp0 _)
    have h1 : GlobalTheory.HeckeTheta.ulog φ (1 : (𝓞 K)ˣ) = 0 := by funext i; simp [GlobalTheory.HeckeTheta.ulog]
    simpa [h1] using h
  have hemb0 : GlobalTheory.HeckeTheta.emb φ ((0 : 𝓞 K) : K) = 0 := by funext i; simp [GlobalTheory.HeckeTheta.emb]
  have htm0 : tm 0 = 0 := by funext y; simp only [htm, hemb0, GlobalTheory.HeckeMellin.term_zero hn]; rfl
  have hint : ∀ α : 𝓞 K, Integrable (tm α) := by
    intro α
    by_cases h : α = 0
    · subst h; rw [htm0]; exact integrable_zero _ _ _
    · exact (GlobalTheory.T.heckeMellinGaussIntegral_nonzero_integer K I φ hφ n s hs0 α h).1
  have hshift : ∀ (u : (𝓞 K)ˣ) (α : 𝓞 K) y, tm ((u : 𝓞 K) * α) y =
      GlobalTheory.HeckeStrip.wt φ n ((u : 𝓞 K) : K) * tm α (y + GlobalTheory.HeckeTheta.ulog φ u) := by
    intro u α y
    have : (((u : 𝓞 K) * α : 𝓞 K) : K) = ((u : 𝓞 K) : K) * (α : K) := by push_cast; rfl
    simp only [htm, this]
    exact GlobalTheory.T.heckeMellinGaussIntegrand_unit_mul K I φ hφ n s u α y
  have hwtu : ∀ u : (𝓞 K)ˣ, ‖GlobalTheory.HeckeStrip.wt φ n ((u : 𝓞 K) : K)‖ = 1 := fun u =>
    GlobalTheory.HeckeStrip.norm_wt φ n (by
      have := u.ne_zero
      exact_mod_cast this)
  have hgen : ∀ J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal}, (haveI := J.2.2; Submodule.IsPrincipal.generator J.1) ≠ 0 := by
    intro J h
    haveI := J.2.2
    exact J.2.1 ((Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero J.1).2 h)
  have hspan : ∀ J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal}, Ideal.span {(haveI := J.2.2; Submodule.IsPrincipal.generator J.1)} = J.1 := by
    intro J; haveI := J.2.2; exact Ideal.span_singleton_generator J.1

  have horb : ∀ g : 𝓞 K, g ≠ 0 → HasSum (fun u : (𝓞 K)ˣ => ∫ y, p y * ‖tm ((u : 𝓞 K) * g) y‖) (∫ y, ‖tm g y‖) ∧
      HasSum (fun u : (𝓞 K)ˣ => F ((u : 𝓞 K) * g) * ∫ y, (p y : ℂ) * tm ((u : 𝓞 K) * g) y) (F g * ∫ y, tm g y) := by
    intro g hg
    have hO := GlobalTheory.T.orbit_unfold_integral_partition_of_unity I (𝓞 K)ˣ (GlobalTheory.HeckeTheta.ulog φ) p hp hp0 hsum' (tm g) (hint g)
    constructor
    · refine (congrArg (fun f => HasSum f _) (funext fun u => ?_)).mpr hO.2
      simp only [hshift, norm_mul, hwtu, one_mul]
    · refine (congrArg (fun f => HasSum f _) (funext fun u => ?_)).mpr (hO.1.mul_left (F g))
      have hw : F ((u : 𝓞 K) * g) * GlobalTheory.HeckeStrip.wt φ n ((u : 𝓞 K) : K) = F g := by
        have h1 := hinv u g
        have hgK : (g : K) ≠ 0 := by exact_mod_cast hg
        have : (((u : 𝓞 K) * g : 𝓞 K) : K) = ((u : 𝓞 K) : K) * (g : K) := by push_cast; rfl
        rw [this, GlobalTheory.HeckeStrip.wt_mul] at h1
        have hne : GlobalTheory.HeckeStrip.wt φ n (g : K) ≠ 0 := by
          rw [← norm_ne_zero_iff, GlobalTheory.HeckeStrip.norm_wt φ n hgK]; exact one_ne_zero
        exact mul_right_cancel₀ hne (by rw [mul_assoc, h1])
      simp only [hshift]
      rw [← hw, mul_assoc]
      congr 1
      rw [← integral_const_mul]
      congr 1; funext y; ring

  set cst : ℝ := ∏ i, (2 * Real.pi) ^ (-(s.re + (|n i| : ℝ) / 2)) * Real.Gamma (s.re + (|n i| : ℝ) / 2) with hcst
  have hnorm : ∀ J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal}, ∫ y, ‖tm (haveI := J.2.2; Submodule.IsPrincipal.generator J.1) y‖ = cst * ((Ideal.absNorm J.1 : ℕ) : ℝ) ^ (-s.re) := by
    intro J
    rw [(GlobalTheory.T.heckeMellinGaussIntegral_nonzero_integer K I φ hφ n s hs0 _ (hgen J)).2.2, hspan J]
  have hb : Summable (fun J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal} => ∫ y, ‖tm (haveI := J.2.2; Submodule.IsPrincipal.generator J.1) y‖) := by
    simp only [hnorm]
    exact (((ReciprocityTheory.Cheb.summable_absNorm_rpow_ideal K hs).comp_injective Subtype.val_injective).mul_left cst)
  have hR := GlobalTheory.T.sum_nonzero_integers_principal_ideals_units K ℝ (fun α => ∫ y, p y * ‖tm α y‖) (by simp [htm0])
    (fun J => ∫ y, ‖tm (haveI := J.2.2; Submodule.IsPrincipal.generator J.1) y‖) (fun J u => ∫ y, p y * ‖tm ((u : 𝓞 K) * (haveI := J.2.2; Submodule.IsPrincipal.generator J.1)) y‖)
    (fun J => ∫ y, ‖tm (haveI := J.2.2; Submodule.IsPrincipal.generator J.1) y‖) (fun J => (horb _ (hgen J)).1)
    (fun J u => le_of_eq (Real.norm_of_nonneg (integral_nonneg fun y => mul_nonneg (hp0 y) (norm_nonneg _))))
    (fun J => (horb _ (hgen J)).1) hb
  have hI := GlobalTheory.T.hasSum_integral_theta_mellin_interchange I (𝓞 K) (fun α => GlobalTheory.HeckeTheta.emb φ (α : K)) F C hF n s p hp hp0 hp1 hint hR.summable
  have hU := GlobalTheory.T.sum_nonzero_integers_principal_ideals_units K ℂ (fun α => F α * ∫ y, (p y : ℂ) * tm α y) (by simp [htm0])
    (fun J => F (haveI := J.2.2; Submodule.IsPrincipal.generator J.1) * ∫ y, tm (haveI := J.2.2; Submodule.IsPrincipal.generator J.1) y) (fun J u => C * ∫ y, p y * ‖tm ((u : 𝓞 K) * (haveI := J.2.2; Submodule.IsPrincipal.generator J.1)) y‖)
    (fun J => C * ∫ y, ‖tm (haveI := J.2.2; Submodule.IsPrincipal.generator J.1) y‖) (fun J => (horb _ (hgen J)).2)
    (fun J u => by
      rw [norm_mul]
      refine mul_le_mul (hF _) ((norm_integral_le_integral_norm _).trans (le_of_eq ?_)) (norm_nonneg _)
        ((norm_nonneg _).trans (hF 0))
      congr 1; funext y; rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hp0 y)])
    (fun J => (horb _ (hgen J)).1.mul_left C) (hb.mul_left C)
  rw [hI.unique hU, GlobalTheory.HeckeStrip.pSeries, ← tsum_mul_left, ← tsum_mul_left]
  congr 1; funext J
  have h3 := (GlobalTheory.T.heckeMellinGaussIntegral_nonzero_integer K I φ hφ n s hs0 _ (hgen J)).2.1
  rw [hspan J] at h3
  simp only [GlobalTheory.HeckeStrip.pval]
  linear_combination (-F (haveI := J.2.2; Submodule.IsPrincipal.generator J.1)) * h3

end GlobalTheory.HeckeMellin
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchFactorMulPSeriesEqIntegralStatement

section

@[expose] public section

open NumberField MeasureTheory

theorem _root_.GlobalTheory.T.archFactor_mul_pSeries_eq_integral_alt : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∀ (n : I → ℤ), (∃ i, n i ≠ 0) → ∀ (F : NumberField.RingOfIntegers K → ℂ) (C : ℝ), (∀ α, ‖F α‖ ≤ C) → (∀ (u : (NumberField.RingOfIntegers K)ˣ) (α : NumberField.RingOfIntegers K), F ((u : NumberField.RingOfIntegers K) * α) * GlobalTheory.HeckeStrip.wt φ n (((u : NumberField.RingOfIntegers K) * α : NumberField.RingOfIntegers K) : K) = F α * GlobalTheory.HeckeStrip.wt φ n (α : K)) → ∀ p : (I → ℝ) → ℝ, Measurable p → (∀ y, 0 ≤ p y) → (∀ y, HasSum (fun u : (NumberField.RingOfIntegers K)ˣ => p (y + GlobalTheory.HeckeTheta.ulog φ u)) 1) → ∀ s : ℂ, 1 < s.re → GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.archFactor n s * GlobalTheory.HeckeStrip.pSeries F φ n s = 2 ^ Fintype.card I * ∫ y, (p y : ℂ) * GlobalTheory.HeckeTheta.theta (fun α : NumberField.RingOfIntegers K => GlobalTheory.HeckeTheta.emb φ (α : K)) F n y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ)) := by
  first | exact @GlobalTheory.HeckeMellin.archFactor_mul_pSeries_eq_integral | exact GlobalTheory.HeckeMellin.archFactor_mul_pSeries_eq_integral | (intros; apply GlobalTheory.HeckeMellin.archFactor_mul_pSeries_eq_integral <;> assumption)
end
end
