module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPureTensorO
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockBargmannReproducingFormulaStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockGaussianJetsAtOriginEqFockVectorsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockGaussianReadingDifferentiableStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjMono
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockRealPointTransportContinuousIntegral
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GaussianConjMonomialMomentEqTaylorCoefficientStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableConjMonomialBargmannGaussianStatement
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSquareIntegrable

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockRealPointTransportContinuousIntegralStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

theorem _root_.GlobalTheory.T.fockRealPoint_transport_continuous_integral : ∀ (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart θ σ → ∀ (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T), Continuous (fockPt σ A B) ∧ (∀ w : WO S T, w.map (finPart D) = 0 → ∃ z, fockPt σ A B z = w) ∧ ∀ g : VCx D.what₂.Tau S.rank T.rank → ℂ, Integrable g → ∃ (m : Measure (WO S T)) (α : WO S T → ℂ), SFinite m ∧ Integrable α m ∧ ∀ H : WO S T → ℂ, ∫ w, α w * H w ∂m = ∫ z, g z * H (fockPt σ A B z) := by
  first | exact @GlobalTheory.FockTransport.fockPt_transport | exact GlobalTheory.FockTransport.fockPt_transport | (intros; apply GlobalTheory.FockTransport.fockPt_transport <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralBargmannEqZeroOfMoments

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

noncomputable section

namespace GlobalTheory.FockTransl

section BargmannUnique

variable {ι : Type} [Fintype ι] {a b : ℕ}

theorem bk_smul_left (c : ι → ℝ) (u : ℂ) (z₀ z : VCx ι a b) : bk c (u • z₀) z = u * bk c z₀ z := by
  unfold bk
  simp only [Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem conjMono_add (m m' : DVar ι a b →₀ ℕ) (z : VCx ι a b) :
    conjMono (m + m') z = conjMono m z * conjMono m' z := by
  unfold conjMono
  exact Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)

theorem conjMono_single_one (k : DVar ι a b) (z : VCx ι a b) :
    conjMono (Finsupp.single k 1) z = conj (z k.1 k.2.1 k.2.2) := by
  unfold conjMono; simp [Finsupp.prod_single_index]

abbrev monoSpan (ι : Type) [Fintype ι] (a b : ℕ) : Submodule ℂ (VCx ι a b → ℂ) :=
  Submodule.span ℂ (Set.range fun m : DVar ι a b →₀ ℕ => conjMono m)

theorem monoSpan_mul {P Q : VCx ι a b → ℂ} (hP : P ∈ monoSpan ι a b) (hQ : Q ∈ monoSpan ι a b) :
    P * Q ∈ monoSpan ι a b := by
  have h := Submodule.mul_mem_mul hP hQ
  rw [Submodule.span_mul_span] at h
  refine Submodule.span_mono ?_ h
  rintro _ ⟨_, ⟨m, rfl⟩, _, ⟨m', rfl⟩, rfl⟩
  exact ⟨m + m', funext fun z => conjMono_add m m' z⟩

theorem bk_mem_monoSpan (c : ι → ℝ) (z₀ : VCx ι a b) : (fun z => bk c z₀ z) ∈ monoSpan ι a b := by
  have : (fun z => bk c z₀ z) = ∑ τ, ∑ i, ∑ j,
      ((c τ : ℂ) * z₀ τ i j) • conjMono (Finsupp.single (τ, i, j) 1) := by
    funext z
    simp only [bk, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, conjMono_single_one]
  rw [this]
  exact Submodule.sum_mem _ fun τ _ => Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

theorem bk_pow_mem_monoSpan (c : ι → ℝ) (z₀ : VCx ι a b) (n : ℕ) :
    (fun z => bk c z₀ z ^ n) ∈ monoSpan ι a b := by
  induction n with
  | zero =>
    have : (fun z : VCx ι a b => bk c z₀ z ^ 0) = conjMono 0 := by funext z; simp [conjMono]
    rw [this]; exact Submodule.subset_span ⟨0, rfl⟩
  | succ n ih =>
    have := monoSpan_mul ih (bk_mem_monoSpan c z₀)
    convert this using 1
    funext z; simp [pow_succ]

theorem exp_norm_le_four (w : ℂ) : Real.exp ‖w‖ ≤ Real.exp ((1 - Complex.I) * w).re +
    Real.exp ((1 + Complex.I) * w).re + Real.exp ((-1 - Complex.I) * w).re + Real.exp ((-1 + Complex.I) * w).re := by
  have h1 : ((1 - Complex.I) * w).re = w.re + w.im := by simp [Complex.mul_re] <;> ring
  have h2 : ((1 + Complex.I) * w).re = w.re + -w.im := by simp [Complex.mul_re] <;> ring
  have h3 : ((-1 - Complex.I) * w).re = -w.re + w.im := by simp [Complex.mul_re] <;> ring
  have h4 : ((-1 + Complex.I) * w).re = -w.re + -w.im := by simp [Complex.mul_re] <;> ring
  rw [h1, h2, h3, h4]
  have key : Real.exp ‖w‖ ≤ Real.exp |w.re| * Real.exp |w.im| := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.2 (Complex.norm_le_abs_re_add_abs_im w)
  have hre : Real.exp |w.re| ≤ Real.exp w.re + Real.exp (-w.re) := by
    rcases abs_cases w.re with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> linarith [Real.exp_pos w.re, Real.exp_pos (-w.re)]
  have him : Real.exp |w.im| ≤ Real.exp w.im + Real.exp (-w.im) := by
    rcases abs_cases w.im with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> linarith [Real.exp_pos w.im, Real.exp_pos (-w.im)]
  calc Real.exp ‖w‖ ≤ (Real.exp w.re + Real.exp (-w.re)) * (Real.exp w.im + Real.exp (-w.im)) :=
        key.trans (mul_le_mul hre him (by positivity) (by positivity))
    _ = _ := by simp only [add_mul, mul_add, ← Real.exp_add]; ring

theorem integral_moment_span_eq_zero {c : ι → ℝ} (hc : ∀ τ, 0 < c τ) {F : VCx ι a b → ℂ}
    (hF : Continuous F) {M : ℝ} (hM : ∀ z, ‖F z‖ ≤ M)
    (hmom : ∀ m : DVar ι a b →₀ ℕ, ∫ z, conjMono m z * (Real.exp (-gq c z / 2) : ℂ) * F z = 0)
    {P : VCx ι a b → ℂ} (hP : P ∈ monoSpan ι a b) :
    Integrable (fun z => P z * (Real.exp (-gq c z / 2) : ℂ) * F z) ∧
      ∫ z, P z * (Real.exp (-gq c z / 2) : ℂ) * F z = 0 := by
  induction hP using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, rfl⟩ := hx
    exact ⟨((GlobalTheory.T.integrable_conjMonomial_bargmann_gaussian ι a b c hc).1 m).mul_bdd hF.aestronglyMeasurable
      (Filter.Eventually.of_forall hM), hmom m⟩
  | zero => simp
  | add x y _ _ hx hy =>
    have e : (fun z => (x + y) z * (Real.exp (-gq c z / 2) : ℂ) * F z) =
        fun z => x z * (Real.exp (-gq c z / 2) : ℂ) * F z + y z * (Real.exp (-gq c z / 2) : ℂ) * F z := by
      funext z; simp only [Pi.add_apply]; ring
    rw [e]
    exact ⟨hx.1.add hy.1, by rw [integral_add hx.1 hy.1, hx.2, hy.2, add_zero]⟩
  | smul r x _ hx =>
    have e : (fun z => (r • x) z * (Real.exp (-gq c z / 2) : ℂ) * F z) =
        fun z => r * (x z * (Real.exp (-gq c z / 2) : ℂ) * F z) := by
      funext z; simp only [Pi.smul_apply, smul_eq_mul]; ring
    rw [e]
    exact ⟨hx.1.const_mul r, by rw [integral_const_mul, hx.2, mul_zero]⟩

theorem integral_bargmann_eq_zero_of_moments : ∀ (ι : Type) [Fintype ι] (a b : ℕ) (c : ι → ℝ), (∀ τ, 0 < c τ) → ∀ F : VCx ι a b → ℂ, Continuous F → (∃ M : ℝ, ∀ z, ‖F z‖ ≤ M) → (∀ m : DVar ι a b →₀ ℕ, ∫ z, conjMono m z * (Real.exp (-gq c z / 2) : ℂ) * F z = 0) → ∀ z₀, ∫ z, Complex.exp (bk c z₀ z) * (Real.exp (-gq c z / 2) : ℂ) * F z = 0 := by
  intro ι _ a b c hc F hF hMex hmom z₀
  obtain ⟨M, hM⟩ := hMex
  have hexpR : ∀ x : ℝ, HasSum (fun n : ℕ => x ^ n / (Nat.factorial n : ℝ)) (Real.exp x) := fun x => by
    rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp _
  have hexpC : ∀ x : ℂ, HasSum (fun n : ℕ => x ^ n / (Nat.factorial n : ℂ)) (Complex.exp x) := fun x => by
    rw [Complex.exp_eq_exp_ℂ]; exact NormedSpace.expSeries_div_hasSum_exp _
  have hgq : Continuous (fun z : VCx ι a b => gq c z) := by unfold gq; fun_prop
  have hbk : Continuous (fun z : VCx ι a b => bk c z₀ z) := by unfold bk; fun_prop
  have hg : Continuous (fun z : VCx ι a b => ((Real.exp (-gq c z / 2) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuous_exp.comp (hgq.neg.div_const 2))
  have hsum := hasSum_integral_of_dominated_convergence (μ := volume)
    (F := fun (n : ℕ) z => bk c z₀ z ^ n / (Nat.factorial n : ℂ) * (Real.exp (-gq c z / 2) : ℂ) * F z)
    (f := fun z => Complex.exp (bk c z₀ z) * (Real.exp (-gq c z / 2) : ℂ) * F z)
    (fun n z => ‖bk c z₀ z‖ ^ n / (Nat.factorial n : ℝ) * (Real.exp (-gq c z / 2) * M))
    (fun n => ((((hbk.pow n).div_const _).mul hg).mul hF).aestronglyMeasurable)
    (fun n => Filter.Eventually.of_forall fun z => by
      simp only [norm_mul, norm_div, norm_pow, Complex.norm_natCast, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      rw [mul_assoc]
      gcongr
      exact hM z)
    (Filter.Eventually.of_forall fun z => (hexpR ‖bk c z₀ z‖).summable.mul_right _)
    (by
      have htsum : (fun z => ∑' n : ℕ, ‖bk c z₀ z‖ ^ n / (Nat.factorial n : ℝ) * (Real.exp (-gq c z / 2) * M)) =
          fun z => Real.exp ‖bk c z₀ z‖ * (Real.exp (-gq c z / 2) * M) := by
        funext z; rw [tsum_mul_right, (hexpR _).tsum_eq]
      rw [htsum]
      have hI : ∀ u : ℂ, Integrable fun z : VCx ι a b =>
          ‖Complex.exp (bk c (u • z₀) z) * (Real.exp (-gq c z / 2) : ℂ)‖ :=
        fun u => ((GlobalTheory.T.integrable_conjMonomial_bargmann_gaussian ι a b c hc).2 (u • z₀)).norm
      have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
      refine Integrable.mono' ((((hI (1 - Complex.I)).add (hI (1 + Complex.I))).add
        (hI (-1 - Complex.I))).add (hI (-1 + Complex.I)) |>.const_mul M)
        ((Real.continuous_exp.comp (continuous_norm.comp hbk)).mul
          ((Real.continuous_exp.comp (hgq.neg.div_const 2)).mul continuous_const)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun z => ?_)
      simp only [Pi.add_apply, bk_smul_left, norm_mul, Complex.norm_exp, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      rw [abs_of_nonneg (by positivity)]
      have h4 := exp_norm_le_four (bk c z₀ z)
      have he := Real.exp_pos (-gq c z / 2)
      calc Real.exp ‖bk c z₀ z‖ * (Real.exp (-gq c z / 2) * M)
          = (M * Real.exp (-gq c z / 2)) * Real.exp ‖bk c z₀ z‖ := by ring
        _ ≤ (M * Real.exp (-gq c z / 2)) * (Real.exp ((1 - Complex.I) * bk c z₀ z).re +
            Real.exp ((1 + Complex.I) * bk c z₀ z).re + Real.exp ((-1 - Complex.I) * bk c z₀ z).re +
            Real.exp ((-1 + Complex.I) * bk c z₀ z).re) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
        _ = _ := by ring)
    (Filter.Eventually.of_forall fun z => by
      simpa only [mul_assoc] using (hexpC (bk c z₀ z)).mul_right ((Real.exp (-gq c z / 2) : ℂ) * F z))
  have h0 : ∀ n : ℕ, ∫ z, bk c z₀ z ^ n / (Nat.factorial n : ℂ) * (Real.exp (-gq c z / 2) : ℂ) * F z = 0 := by
    intro n
    have := (integral_moment_span_eq_zero hc hF hM hmom
      (Submodule.smul_mem _ ((Nat.factorial n : ℂ)⁻¹) (bk_pow_mem_monoSpan c z₀ n))).2
    have e : (fun z => bk c z₀ z ^ n / (Nat.factorial n : ℂ) * (Real.exp (-gq c z / 2) : ℂ) * F z) =
        fun z => ((Nat.factorial n : ℂ)⁻¹ • fun z => bk c z₀ z ^ n) z * (Real.exp (-gq c z / 2) : ℂ) * F z := by
      funext z; simp only [Pi.smul_apply, smul_eq_mul]; ring
    rw [e]; exact this
  simp only [h0] at hsum
  exact hsum.unique hasSum_zero

end BargmannUnique

end GlobalTheory.FockTransl

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralBargmannEqZeroOfMomentsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

theorem _root_.GlobalTheory.T.integral_exp_bk_mul_eq_zero_of_moments_zero : ∀ (ι : Type) [Fintype ι] (a b : ℕ) (c : ι → ℝ), (∀ τ, 0 < c τ) → ∀ F : VCx ι a b → ℂ, Continuous F → (∃ M : ℝ, ∀ z, ‖F z‖ ≤ M) → (∀ m : DVar ι a b →₀ ℕ, ∫ z, conjMono m z * (Real.exp (-gq c z / 2) : ℂ) * F z = 0) → ∀ z₀, ∫ z, Complex.exp (bk c z₀ z) * (Real.exp (-gq c z / 2) : ℂ) * F z = 0 := by
  first | exact @GlobalTheory.FockTransl.integral_bargmann_eq_zero_of_moments | exact GlobalTheory.FockTransl.integral_bargmann_eq_zero_of_moments | (intros; apply GlobalTheory.FockTransl.integral_bargmann_eq_zero_of_moments <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameFunctionalKillsFockVacuumRealTranslates

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.FockTransl

open Formalism.L2.Ker (VCx DVar derivAt0)

theorem tame_kills_real_translates : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (ℓ : (WO S T → ℂ) → ℂ), Tame ψ S T ℓ →
    ∀ f, GlobalTheory.ChainFr.IsVacF ψ θ A B f → (∀ P, ℓ (GlobalTheory.ChainFr.ptF ψ θ A B f P) = 0) →
    ∀ w : WO S T, w.map (finPart D) = 0 → ℓ (heisO ψ S T w f) = 0 := by
  intro D ψ θ hψ hθ S T A B ℓ hℓ f hf hP w hw
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨hcont, hsurj, htr⟩ := GlobalTheory.T.fockRealPoint_transport_continuous_integral D θ σ hσ S T A B
  obtain ⟨z₀, rfl⟩ := hsurj w hw
  have hth := hf.1
  set F : VCx D.what₂.Tau S.rank T.rank → ℂ := fun z => ℓ (heisO ψ S T (fockPt σ A B z) f) with hFdef
  have hFc : Continuous F := (hℓ.cont f hth).comp hcont
  obtain ⟨M, hM⟩ := hℓ.bdd f hth
  have hFb : ∃ M : ℝ, ∀ z, ‖F z‖ ≤ M := ⟨M, fun z => hM _⟩
  have key : ∀ g : VCx D.what₂.Tau S.rank T.rank → ℂ, Integrable g →
      IsThetaFunO ψ S T (fun x => ∫ z, g z * heisO ψ S T (fockPt σ A B z) f x) →
      ℓ (fun x => ∫ z, g z * heisO ψ S T (fockPt σ A B z) f x) = ∫ z, g z * F z := by
    intro g hg hthg
    obtain ⟨m, α, hm, hα, hH⟩ := htr g hg
    have e1 : (fun x => ∫ z, g z * heisO ψ S T (fockPt σ A B z) f x) = fun x => ∫ w, α w * heisO ψ S T w f x ∂m := by
      funext x; exact (hH fun w => heisO ψ S T w f x).symm
    rw [e1] at hthg ⊢
    rw [hℓ.sup f hth m α hα hthg]
    exact hH fun w => ℓ (heisO ψ S T w f)
  obtain ⟨C, hC⟩ := ((GlobalTheory.ThetaSquare.squareIntegrable hψ) f hth).2.1
  have hG : ∀ x, ∃ M : ℝ, ∀ z, ‖rd ψ σ A B f x z‖ ≤ M * Real.exp (gq (fw D) z / 2) := by
    intro x
    refine ⟨C, fun z => ?_⟩
    rw [rd, norm_mul, GlobalTheory.ThetaSquare.norm_heisO hψ, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), mul_comm]
    exact mul_le_mul_of_nonneg_right (hC _) (Real.exp_pos _).le
  have hent := GlobalTheory.T.fockGaussianReading_differentiable D ψ θ σ hψ hσ S T A B f hf
  have hc : ∀ τ, 0 < fw D τ := fw_pos D
  obtain ⟨hint1, hint2⟩ := GlobalTheory.T.integrable_conjMonomial_bargmann_gaussian D.what₂.Tau S.rank T.rank (fw D) hc
  have hgq : ∀ z : VCx D.what₂.Tau S.rank T.rank, ∀ x, (Real.exp (-gq (fw D) z) : ℂ) * rd ψ σ A B f x z =
      (Real.exp (-gq (fw D) z / 2) : ℂ) * heisO ψ S T (fockPt σ A B z) f x := by
    intro z x
    rw [rd, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
    congr 3; ring

  obtain ⟨Cj, hCj⟩ := GlobalTheory.T.fock_gaussian_jets_at_origin_eq_fock_vectors D ψ θ σ hψ hσ S T A B
  have hpt : ∀ P, IsThetaFunO ψ S T (GlobalTheory.ChainFr.ptF ψ θ A B f P) :=
    fun P => GlobalTheory.GalLift.Vec.theta_pureTensorO hψ hθ _ _ _ _ hth P
  have hmom : ∀ m : DVar D.what₂.Tau S.rank T.rank →₀ ℕ,
      ∫ z, conjMono m z * (Real.exp (-gq (fw D) z / 2) : ℂ) * F z = 0 := by
    intro m
    set K : ℂ := ((∏ τ, (Real.pi / fw D τ) ^ (S.rank * T.rank) : ℝ) : ℂ) *
      ((m.prod fun k n => (fw D k.1)⁻¹ ^ n : ℝ) : ℂ) with hK
    have e : (fun x => ∫ z, conjMono m z * (Real.exp (-gq (fw D) z / 2) : ℂ) * heisO ψ S T (fockPt σ A B z) f x) =
        (K * Cj m) • GlobalTheory.ChainFr.ptF ψ θ A B f (MvPolynomial.monomial m 1) := by
      funext x
      have h1 := GlobalTheory.T.gaussian_conjMonomial_moment_eq_taylor_coefficient D.what₂.Tau S.rank T.rank (fw D) hc (rd ψ σ A B f x) (hent x) (hG x) m
      rw [hCj f hf x m] at h1
      have h2 : (fun z => conjMono m z * (Real.exp (-gq (fw D) z / 2) : ℂ) * heisO ψ S T (fockPt σ A B z) f x) =
          fun z => conjMono m z * (Real.exp (-gq (fw D) z) : ℂ) * rd ψ σ A B f x z := by
        funext z; rw [mul_assoc, mul_assoc, hgq]
      rw [h2, h1, Pi.smul_apply, smul_eq_mul]
      ring
    have hthe : IsThetaFunO ψ S T (fun x => ∫ z, conjMono m z * (Real.exp (-gq (fw D) z / 2) : ℂ) *
        heisO ψ S T (fockPt σ A B z) f x) := by
      rw [e]
      exact GlobalTheory.OrientedHeis.theta_smul _ (hpt _)
    have := key _ (hint1 m) hthe
    rw [← this, e, hℓ.smul _ _ (hpt _), hP, mul_zero]

  have hU := GlobalTheory.T.integral_exp_bk_mul_eq_zero_of_moments_zero D.what₂.Tau S.rank T.rank (fw D) hc F hFc hFb hmom z₀
  set K' : ℂ := ((∏ τ, (fw D τ / Real.pi) ^ (S.rank * T.rank) : ℝ) : ℂ) * (Real.exp (-gq (fw D) z₀ / 2) : ℂ) with hK'
  have e : (fun x => ∫ z, (K' * (Complex.exp (bk (fw D) z₀ z) * (Real.exp (-gq (fw D) z / 2) : ℂ))) *
      heisO ψ S T (fockPt σ A B z) f x) = heisO ψ S T (fockPt σ A B z₀) f := by
    funext x
    have h1 := GlobalTheory.T.fock_bargmann_reproducing_formula D.what₂.Tau S.rank T.rank (fw D) hc (rd ψ σ A B f x) (hent x) (hG x) z₀
    have h2 : heisO ψ S T (fockPt σ A B z₀) f x = (Real.exp (-gq (fw D) z₀ / 2) : ℂ) * rd ψ σ A B f x z₀ := by
      rw [rd, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
      rw [show -gq (fw D) z₀ / 2 + gq (fw D) z₀ / 2 = 0 by ring, Real.exp_zero, Complex.ofReal_one, one_mul]
    rw [h2, h1]
    have h3 : (fun z => (K' * (Complex.exp (bk (fw D) z₀ z) * (Real.exp (-gq (fw D) z / 2) : ℂ))) *
        heisO ψ S T (fockPt σ A B z) f x) = fun z => K' * (Complex.exp (bk (fw D) z₀ z) *
          ((Real.exp (-gq (fw D) z) : ℂ) * rd ψ σ A B f x z)) := by
      funext z; rw [hgq]; ring
    rw [h3, integral_const_mul, hK']
    simp only [mul_assoc]
    ring
  have hthe : IsThetaFunO ψ S T (fun x => ∫ z, (K' * (Complex.exp (bk (fw D) z₀ z) * (Real.exp (-gq (fw D) z / 2) : ℂ))) *
      heisO ψ S T (fockPt σ A B z) f x) := by
    rw [e]; exact (GlobalTheory.ThetaSquare.heisUnitary hψ).2.2.1 _ _ hth
  have := key _ ((hint2 z₀).const_mul K') hthe
  rw [e] at this
  change ℓ (heisO ψ S T (fockPt σ A B z₀) f) = 0
  rw [this]
  simp_rw [mul_assoc]
  rw [integral_const_mul]
  simp_rw [← mul_assoc] at hU ⊢
  rw [hU, mul_zero]

end GlobalTheory.FockTransl

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameFunctionalKillsFockVacuumRealTranslatesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

theorem _root_.GlobalTheory.T.tameFunctional_kills_fockVacuum_realTranslates : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (ℓ : (WO S T → ℂ) → ℂ), Tame ψ S T ℓ → ∀ f, GlobalTheory.ChainFr.IsVacF ψ θ A B f → (∀ P, ℓ (GlobalTheory.ChainFr.ptF ψ θ A B f P) = 0) → ∀ w : WO S T, w.map (finPart D) = 0 → ℓ (heisO ψ S T w f) = 0 := by
  first | exact @GlobalTheory.FockTransl.tame_kills_real_translates | exact GlobalTheory.FockTransl.tame_kills_real_translates | (intros; apply GlobalTheory.FockTransl.tame_kills_real_translates <;> assumption)
end
end
