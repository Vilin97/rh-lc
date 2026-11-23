module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairInfApply
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContDiffFockGaussianFormOfLinearMapFamilyStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockFormApply
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
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
public import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtDiagSumProdPairingStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsUnitUpperRightBlockOfHeisenbergDerivativeSolutStatement
public import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UniformlyNegDefiniteNearOfContinuousQuadFormFamiStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContDiffProdLinearMapUpperRightLowerRightBlocks

section

@[expose] public section

open MeasureTheory

namespace GlobalTheory.FockFamily

theorem contDiff_blockB_blockD {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (J : ℝ → (V × V) →ₗ[ℝ] (V × V)) (hJ : ∀ w, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => J t w) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => GlobalTheory.FockFamily.blockB (J t)) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => GlobalTheory.FockFamily.blockD (J t)) := by
  constructor
  · rw [contDiff_clm_apply_iff]
    intro q
    simpa only [blockB_apply] using (hJ (0, q)).fst
  · rw [contDiff_clm_apply_iff]
    intro q
    simpa only [blockD_apply] using (hJ (0, q)).snd

end GlobalTheory.FockFamily
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContDiffProdLinearMapUpperRightLowerRightBlocksStatement

section

@[expose] public section

open MeasureTheory

theorem _root_.GlobalTheory.T.contDiff_prodLinearMap_upperRight_lowerRight_blocks : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (J : ℝ → (V × V) →ₗ[ℝ] (V × V)), (∀ w, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => J t w) →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => GlobalTheory.FockFamily.blockB (J t)) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => GlobalTheory.FockFamily.blockD (J t)) := by
  first | exact @GlobalTheory.FockFamily.contDiff_blockB_blockD | exact GlobalTheory.FockFamily.contDiff_blockB_blockD | (intros; apply GlobalTheory.FockFamily.contDiff_blockB_blockD <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqExpFockGaussianFormOfHeisenbergDerivativeEq

section

@[expose] public section

open MeasureTheory

noncomputable section

namespace GlobalTheory.FockFamily

theorem fderiv_eq_of_dHeis {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (J : (V × V) →ₗ[ℝ] (V × V)) (hB : IsUnit (blockB J)) (g : V → ℂ)
    (heq : ∀ w x, GlobalTheory.GaussLine.dHeis β (J w) g x = Complex.I * GlobalTheory.GaussLine.dHeis β w g x) (x y : V) :
    fderiv ℝ g x y = 2 * fockForm β J x y * g x := by
  have h := heq (0, Ring.inverse (blockB J) y) x
  have h1 : (J (0, Ring.inverse (blockB J) y)).1 = y := by
    rw [← blockB_apply, ← ContinuousLinearMap.mul_apply, Ring.mul_inverse_cancel _ hB]; rfl
  have h2 : (J (0, Ring.inverse (blockB J) y)).2 = blockD J (Ring.inverse (blockB J) y) := rfl
  simp only [GlobalTheory.GaussLine.dHeis, h1, h2, map_zero, zero_sub] at h
  rw [fockForm_apply]
  push_cast
  linear_combination h - 2 * Real.pi * (β x (Ring.inverse (blockB J) y) : ℂ) * g x * Complex.I_sq

theorem solution_eq_gauss {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (J : (V × V) →ₗ[ℝ] (V × V)) (hB : IsUnit (blockB J)) (g : V → ℂ)
    (hg : Differentiable ℝ g)
    (heq : ∀ w x, GlobalTheory.GaussLine.dHeis β (J w) g x = Complex.I * GlobalTheory.GaussLine.dHeis β w g x) (x : V) :
    g x = g 0 * Complex.exp (fockForm β J x x) := by
  set c : ℂ := fockForm β J x x with hc
  let h : ℝ → ℂ := fun s => g (s • x) * Complex.exp (-(((s ^ 2 : ℝ)) : ℂ) * c)
  have hd : ∀ s : ℝ, HasDerivAt h 0 s := by
    intro s
    have e1 : HasDerivAt (fun t : ℝ => g (t • x)) (fderiv ℝ g (s • x) x) s := by
      have := (hg (s • x)).hasFDerivAt.comp_hasDerivAt s ((hasDerivAt_id s).smul_const x)
      simp only [one_smul] at this
      exact this
    have e2 : HasDerivAt (fun t : ℝ => Complex.exp (-(((t ^ 2 : ℝ)) : ℂ) * c))
        (Complex.exp (-(((s ^ 2 : ℝ)) : ℂ) * c) * (-((((2 : ℕ) : ℝ) * s ^ (2 - 1) * 1 : ℝ) : ℂ) * c)) s := by
      exact ((((hasDerivAt_id s).pow 2).ofReal_comp).neg.mul_const c).cexp
    have hf : fderiv ℝ g (s • x) x = 2 * ((s : ℂ) * c) * g (s • x) := by
      rw [fderiv_eq_of_dHeis β J hB g heq, map_smul, LinearMap.smul_apply, Complex.real_smul]
    show HasDerivAt (fun t : ℝ => g (t • x) * Complex.exp (-(((t ^ 2 : ℝ)) : ℂ) * c)) 0 s
    refine (e1.mul e2).congr_deriv ?_
    rw [hf]
    push_cast
    ring
  have hconst : ∀ a b : ℝ, h a = h b := fun a b =>
    is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) a b
  have := hconst 1 0
  simp only [h, one_smul, zero_smul, one_pow, Complex.ofReal_one, neg_mul, one_mul, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, Complex.ofReal_zero, zero_mul, neg_zero, Complex.exp_zero, mul_one] at this
  rw [← this, mul_assoc, ← Complex.exp_add]
  simp

end GlobalTheory.FockFamily

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqExpFockGaussianFormOfHeisenbergDerivativeEqStatement

section

@[expose] public section

open MeasureTheory

theorem _root_.GlobalTheory.T.eq_exp_fockGaussianForm_of_heisenbergDerivative_eq : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (J : (V × V) →ₗ[ℝ] (V × V)), IsUnit (GlobalTheory.FockFamily.blockB J) → ∀ g : V → ℂ, Differentiable ℝ g →
    (∀ w x, GlobalTheory.GaussLine.dHeis β (J w) g x = Complex.I * GlobalTheory.GaussLine.dHeis β w g x) →
    ∀ x, g x = g 0 * Complex.exp (GlobalTheory.FockFamily.fockForm β J x x) := by
  first | exact @GlobalTheory.FockFamily.solution_eq_gauss | exact GlobalTheory.FockFamily.solution_eq_gauss | (intros; apply GlobalTheory.FockFamily.solution_eq_gauss <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzGaussianFormReNeg

section

@[expose] public section

open MeasureTheory

namespace GlobalTheory

theorem schwartz_gaussian_form_re_neg {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (M : V →ₗ[ℝ] V →ₗ[ℝ] ℂ) (g : SchwartzMap V ℂ) (hg : g ≠ 0)
    (hform : ∀ x, g x = g 0 * Complex.exp (M x x)) (v : V) (hv : v ≠ 0) : (M v v).re < 0 := by
  have hg0 : g 0 ≠ 0 := by
    intro h0
    apply hg
    ext x
    rw [hform x, h0]; simp
  by_contra hre
  push_neg at hre
  obtain ⟨C, hC, hdec⟩ := g.decay 1 0
  have hgn : 0 < ‖g 0‖ := norm_pos_iff.mpr hg0
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  set s : ℝ := (C + 1) / (‖v‖ * ‖g 0‖) with hs
  have hspos : 0 < s := by positivity
  have key := hdec (s • v)
  rw [norm_iteratedFDeriv_zero, pow_one, hform (s • v)] at key
  have hM : M (s • v) (s • v) = ((s ^ 2 : ℝ) : ℂ) * M v v := by
    simp only [map_smul, LinearMap.smul_apply, smul_smul]
    rw [Complex.real_smul]; push_cast; ring
  rw [hM, norm_mul, Complex.norm_exp] at key
  have hexp : 1 ≤ Real.exp ((((s ^ 2 : ℝ) : ℂ) * M v v).re) := by
    apply Real.one_le_exp
    rw [Complex.re_ofReal_mul]
    positivity
  have hnorm : ‖s • v‖ = s * ‖v‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hspos]
  rw [hnorm] at key
  have h1 : s * ‖v‖ * ‖g 0‖ = C + 1 := by
    rw [hs]; field_simp
  have h2 : s * ‖v‖ * ‖g 0‖ ≤ s * ‖v‖ * (‖g 0‖ * Real.exp ((((s ^ 2 : ℝ) : ℂ) * M v v).re)) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    nlinarith
  linarith

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzGaussianFormReNegStatement

section

@[expose] public section

open MeasureTheory

theorem _root_.GlobalTheory.T.gaussian_form_re_neg_of_ne_zero : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (M : V →ₗ[ℝ] V →ₗ[ℝ] ℂ) (g : SchwartzMap V ℂ), g ≠ 0 →
    (∀ x, g x = g 0 * Complex.exp (M x x)) → ∀ v, v ≠ 0 → (M v v).re < 0 := by
  first | exact @GlobalTheory.schwartz_gaussian_form_re_neg | exact GlobalTheory.schwartz_gaussian_form_re_neg | (intros; apply GlobalTheory.schwartz_gaussian_form_re_neg <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVacuaSmoothFamilyComplexGaussians

section

@[expose] public section

open MeasureTheory

namespace GlobalTheory.FockFamily

theorem fock_vacua_family : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ), (∀ q, (∀ x, β x q = 0) → q = 0) →
    ∀ J : ℝ → (V × V) →ₗ[ℝ] (V × V), (∀ w, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => J t w) → (∀ t w, J t (J t w) = -w) →
    (∀ t, ∃ g : SchwartzMap V ℂ, g ≠ 0 ∧ ∀ w x, GlobalTheory.GaussLine.dHeis β (J t w) ⇑g x = Complex.I * GlobalTheory.GaussLine.dHeis β w ⇑g x) →
    ∃ M : ℝ → V →ₗ[ℝ] V →ₗ[ℝ] ℂ, (∀ x y, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => M t x y) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × V => M p.1 p.2 p.2) ∧
      (∀ t₀ : ℝ, ∃ ε > 0, ∀ᶠ t in nhds t₀, ∀ x, (M t x x).re ≤ -(ε * ‖x‖ ^ 2)) ∧
      (∀ t (g : SchwartzMap V ℂ), (∀ w x, GlobalTheory.GaussLine.dHeis β (J t w) ⇑g x = Complex.I * GlobalTheory.GaussLine.dHeis β w ⇑g x) →
        ∀ x, g x = g 0 * Complex.exp (M t x x)) ∧
      ∃ (n : ℕ) (qs qs' : Fin n → V) (cs : Fin n → ℂ), ∀ x,
        HasDerivAt (fun t => M t x x) (∑ i, cs i * (β x (qs i) : ℂ) * (β x (qs' i) : ℂ)) 0 := by
  intro V _ _ _ β hβ J hJ _ hex
  choose g0 hg0ne hg0 using hex
  have hunit : ∀ t, IsUnit (GlobalTheory.FockFamily.blockB (J t)) := fun t =>
    GlobalTheory.T.isUnit_upperRightBlock_of_heisenbergDerivative_solution β hβ (J t) (g0 t) (g0 t).continuous (fun h => hg0ne t (SchwartzMap.ext (fun x => congrFun h x))) (hg0 t)
  obtain ⟨hB, hD⟩ := GlobalTheory.T.contDiff_prodLinearMap_upperRight_lowerRight_blocks J hJ
  obtain ⟨hsm, hjoint⟩ := GlobalTheory.T.contDiff_fockGaussianFormOfLinearMap_family β J hB hD hunit
  have hray : ∀ t (g : SchwartzMap V ℂ), (∀ w x, GlobalTheory.GaussLine.dHeis β (J t w) ⇑g x =
      Complex.I * GlobalTheory.GaussLine.dHeis β w ⇑g x) → ∀ x, g x = g 0 * Complex.exp (GlobalTheory.FockFamily.fockForm β (J t) x x) :=
    fun t g hg => GlobalTheory.T.eq_exp_fockGaussianForm_of_heisenbergDerivative_eq β (J t) (hunit t) g g.differentiable hg
  refine ⟨fun t => GlobalTheory.FockFamily.fockForm β (J t), hsm, hjoint, ?_, hray, ?_⟩
  · exact GlobalTheory.T.uniformly_negDefinite_near_of_continuous_quadForm_family (fun t => GlobalTheory.FockFamily.fockForm β (J t)) hjoint.continuous
      (fun t v hv => GlobalTheory.T.gaussian_form_re_neg_of_ne_zero _ (g0 t) (hg0ne t) (hray t (g0 t) (hg0 t)) v hv)
  · exact GlobalTheory.T.exists_hasDerivAt_diag_eq_sum_mul_pairings β hβ _ (fun x y => ((hsm x y).differentiable (by simp)).differentiableAt)

end GlobalTheory.FockFamily
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVacuaSmoothFamilyComplexGaussiansStatement

section

@[expose] public section

open MeasureTheory

theorem _root_.GlobalTheory.T.fockVacua_smooth_family_complexGaussians : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ), (∀ q, (∀ x, β x q = 0) → q = 0) →
    ∀ J : ℝ → (V × V) →ₗ[ℝ] (V × V), (∀ w, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => J t w) → (∀ t w, J t (J t w) = -w) →
    (∀ t, ∃ g : SchwartzMap V ℂ, g ≠ 0 ∧ ∀ w x, GlobalTheory.GaussLine.dHeis β (J t w) ⇑g x = Complex.I * GlobalTheory.GaussLine.dHeis β w ⇑g x) →
    ∃ M : ℝ → V →ₗ[ℝ] V →ₗ[ℝ] ℂ, (∀ x y, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => M t x y) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × V => M p.1 p.2 p.2) ∧
      (∀ t₀ : ℝ, ∃ ε > 0, ∀ᶠ t in nhds t₀, ∀ x, (M t x x).re ≤ -(ε * ‖x‖ ^ 2)) ∧
      (∀ t (g : SchwartzMap V ℂ), (∀ w x, GlobalTheory.GaussLine.dHeis β (J t w) ⇑g x = Complex.I * GlobalTheory.GaussLine.dHeis β w ⇑g x) →
        ∀ x, g x = g 0 * Complex.exp (M t x x)) ∧
      ∃ (n : ℕ) (qs qs' : Fin n → V) (cs : Fin n → ℂ), ∀ x,
        HasDerivAt (fun t => M t x x) (∑ i, cs i * (β x (qs i) : ℂ) * (β x (qs' i) : ℂ)) 0 := by
  first | exact @GlobalTheory.FockFamily.fock_vacua_family | exact GlobalTheory.FockFamily.fock_vacua_family | (intros; apply GlobalTheory.FockFamily.fock_vacua_family <;> assumption)
end
end
