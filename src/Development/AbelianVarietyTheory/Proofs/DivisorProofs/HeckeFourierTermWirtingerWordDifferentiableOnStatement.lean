module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HTransABTwoZero
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeHankelTransformABDifferentiableOnSigmaStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeHankelTransformABHasDerivAtYStatement
import Mathlib.Algebra.Order.Archimedean.Real.Hom
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothHolomorphicInSigmaFamilyAdd

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeYDerivativeTermHasFDerivUpperHalfPlane

section

@[expose] public section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
open Classical

noncomputable section

namespace GlobalTheory.HeckeTwo

theorem fderiv_prod_coord {ι : Type} [Fintype ι] [DecidableEq ι] (g : ι → ℂ → ℂ) (L : ι → ℂ →L[ℝ] ℂ) (z : ι → ℂ)
    (hg : ∀ i, HasFDerivAt (g i) (L i) (z i)) :
    DifferentiableAt ℝ (fun w : ι → ℂ => ∏ i, g i (w i)) z ∧
    ∀ (j : ι) (v : ℂ), fderiv ℝ (fun w : ι → ℂ => ∏ i, g i (w i)) z (Pi.single j v) =
      L j v * ∏ i ∈ Finset.univ.erase j, g i (z i) := by
  have h1 : ∀ i ∈ (Finset.univ : Finset ι), HasFDerivAt (fun w : ι → ℂ => g i (w i))
      ((L i).comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℂ) i)) z := fun i _ =>
    (hg i).comp z (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℂ) i).hasFDerivAt
  have h2 := HasFDerivAt.finsetProd h1
  refine ⟨h2.differentiableAt, fun j v => ?_⟩
  rw [h2.fderiv, ContinuousLinearMap.sum_apply, Finset.sum_eq_single j]
  · simp [mul_comm]
  · intro i _ hij
    simp [Pi.single_eq_of_ne hij]
  · simp

theorem hasFDerivAt_factor (c : ℂ) (a β : ℝ) (h : ℝ → ℂ) (h' : ℂ) (w : ℂ) (hh : HasDerivAt h h' (β * w.im)) :
    ∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt (fun u : ℂ => Complex.exp (c * ((a * u.re : ℝ) : ℂ)) * h (β * u.im)) L w ∧
      L 1 = c * (a : ℂ) * (Complex.exp (c * ((a * w.re : ℝ) : ℂ)) * h (β * w.im)) ∧
      L I = (β : ℂ) * (Complex.exp (c * ((a * w.re : ℝ) : ℂ)) * h') := by
  have e1 : HasFDerivAt (fun u : ℂ => ((a * u.re : ℝ) : ℂ)) (Complex.ofRealCLM.comp (a • Complex.reCLM)) w :=
    (Complex.ofRealCLM.comp (a • Complex.reCLM)).hasFDerivAt
  have e2 := (e1.const_mul c).cexp
  have e3 : HasFDerivAt (fun u : ℂ => β * u.im) (β • Complex.imCLM) w := (β • Complex.imCLM).hasFDerivAt
  have e4 := hh.hasFDerivAt.comp w e3
  refine ⟨_, e2.mul e4, ?_, ?_⟩
  · simp; ring
  · simp; ring

theorem termQ_fderiv : ∀ (F : Type) [Field F] [NumberField F] (b ν : F), b ≠ 0 → (∀ (n : ℝ) (k : ℕ) (y : ℝ), y ≠ 0 →
    (∀ σ ∈ halfPlane, HasDerivAt (iteratedDeriv k (hTrans σ n)) (iteratedDeriv (k + 1) (hTrans σ n) y) y) ∧
    DifferentiableOn ℂ (fun σ => iteratedDeriv k (hTrans σ n) y) halfPlane) →
    ∀ σ ∈ halfPlane, ∀ (q : Emb F → ℕ), ∀ z ∈ upperHalf F, ∀ τ₀ : Emb F,
    DifferentiableAt ℝ (termQ σ b ν q) z ∧
    fderiv ℝ (termQ σ b ν q) z (Pi.single τ₀ 1) = 2 * (Real.pi : ℂ) * I * ((τ₀ ν * τ₀ b : ℝ) : ℂ) * termQ σ b ν q z ∧
    fderiv ℝ (termQ σ b ν q) z (Pi.single τ₀ I) = ((τ₀ b : ℝ) : ℂ) * termQ σ b ν (q + Pi.single τ₀ 1) z := by
  intro F _ _ b ν hb H σ hσ q z hz τ₀
  have hne : ∀ τ : Emb F, τ b * (z τ).im ≠ 0 := fun τ =>
    mul_ne_zero ((map_ne_zero τ).2 hb) (hz τ).ne'
  choose L hL hL1 hLI using fun τ : Emb F => hasFDerivAt_factor (2 * (Real.pi : ℂ) * I) (τ ν * τ b) (τ b)
    (iteratedDeriv (q τ) (hTrans σ (τ ν))) _ (z τ) ((H (τ ν) (q τ) _ (hne τ)).1 σ hσ)
  obtain ⟨hd, hf⟩ := fderiv_prod_coord _ L z hL
  refine ⟨hd, ?_, ?_⟩
  · refine (hf τ₀ 1).trans ?_
    unfold termQ
    rw [hL1, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ τ₀)]
    ring
  · refine (hf τ₀ I).trans ?_
    unfold termQ
    rw [hLI, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ τ₀), mul_assoc]
    congr 2
    · simp
    · refine Finset.prod_congr rfl fun τ hτ => ?_
      simp [Pi.single_eq_of_ne (Finset.ne_of_mem_erase hτ)]

end GlobalTheory.HeckeTwo
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeYDerivativeTermHasFDerivUpperHalfPlaneStatement

section

@[expose] public section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
open Classical


theorem _root_.GlobalTheory.T.heckeYDerivativeTerm_hasFDeriv_upperHalfPlane : ∀ (F : Type) [Field F] [NumberField F] (b ν : F), b ≠ 0 → (∀ (n : ℝ) (k : ℕ) (y : ℝ), y ≠ 0 →
    (∀ σ ∈ halfPlane, HasDerivAt (iteratedDeriv k (hTrans σ n)) (iteratedDeriv (k + 1) (hTrans σ n) y) y) ∧
    DifferentiableOn ℂ (fun σ => iteratedDeriv k (hTrans σ n) y) halfPlane) →
    ∀ σ ∈ halfPlane, ∀ (q : Emb F → ℕ), ∀ z ∈ upperHalf F, ∀ τ₀ : Emb F,
    DifferentiableAt ℝ (termQ σ b ν q) z ∧
    fderiv ℝ (termQ σ b ν q) z (Pi.single τ₀ 1) = 2 * (Real.pi : ℂ) * I * ((τ₀ ν * τ₀ b : ℝ) : ℂ) * termQ σ b ν q z ∧
    fderiv ℝ (termQ σ b ν q) z (Pi.single τ₀ I) = ((τ₀ b : ℝ) : ℂ) * termQ σ b ν (q + Pi.single τ₀ 1) z := by
  first | exact @GlobalTheory.HeckeTwo.termQ_fderiv | exact GlobalTheory.HeckeTwo.termQ_fderiv | (intros; apply GlobalTheory.HeckeTwo.termQ_fderiv <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedDerivHeckePhiTransformHasDerivAtHolo

section

@[expose] public section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

namespace GlobalTheory.HeckeTwo

theorem iteratedDeriv_hTrans_eq_sum
    (h1 : ∀ (a b : ℕ) (σ : ℂ) (ν y : ℝ), 2 ≤ a + b → σ ∈ halfPlane → y ≠ 0 →
    HasDerivAt (fun y' : ℝ => hTransAB a b σ ν y')
      (I * (-(a : ℂ) - σ) * hTransAB (a + 1) b σ ν y + I * ((b : ℂ) + σ) * hTransAB a (b + 1) σ ν y) y)
    (n : ℝ) (k : ℕ) :
    ∃ (ι : Type) (_ : Fintype ι) (c : ι → ℂ → ℂ) (ab : ι → ℕ × ℕ),
      (∀ i, Differentiable ℂ (c i)) ∧ (∀ i, 2 ≤ (ab i).1 + (ab i).2) ∧
      ∀ σ ∈ halfPlane, ∀ y : ℝ, y ≠ 0 →
        iteratedDeriv k (hTrans σ n) y = ∑ i, c i σ * hTransAB (ab i).1 (ab i).2 σ n y := by
  induction k with
  | zero =>
    refine ⟨Unit, inferInstance, fun _ _ => 1, fun _ => (2, 0), fun _ => by fun_prop,
      fun _ => by simp, fun σ _ y _ => ?_⟩
    simp [hTransAB_two_zero]
  | succ k ih =>
    obtain ⟨ι, _, c, ab, hc, hab, h⟩ := ih
    refine ⟨ι ⊕ ι, inferInstance,
      Sum.elim (fun i σ => c i σ * (I * (-((ab i).1 : ℂ) - σ)))
        (fun i σ => c i σ * (I * (((ab i).2 : ℂ) + σ))),
      Sum.elim (fun i => ((ab i).1 + 1, (ab i).2)) (fun i => ((ab i).1, (ab i).2 + 1)),
      ?_, ?_, ?_⟩
    · rintro (i | i)
      · have := hc i
        simp only [Sum.elim_inl]; fun_prop
      · have := hc i
        simp only [Sum.elim_inr]; fun_prop
    · rintro (i | i)
      · have := hab i
        simp only [Sum.elim_inl]; omega
      · have := hab i
        simp only [Sum.elim_inr]; omega
    · intro σ hσ y hy
      have hev : iteratedDeriv k (hTrans σ n) =ᶠ[nhds y]
          fun y' => ∑ i, c i σ * hTransAB (ab i).1 (ab i).2 σ n y' := by
        filter_upwards [isOpen_ne.mem_nhds hy] with y' hy' using h σ hσ y' hy'
      have hd := (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
        (h1 (ab i).1 (ab i).2 σ n y (hab i) hσ hy).const_mul (c i σ))).congr_of_eventuallyEq hev
      rw [iteratedDeriv_succ, hd.deriv, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Sum.elim_inl, Sum.elim_inr]
      ring

theorem iteratedDeriv_hTrans_jet :
    (∀ (a b : ℕ) (σ : ℂ) (ν y : ℝ), 2 ≤ a + b → σ ∈ halfPlane → y ≠ 0 →
    HasDerivAt (fun y' : ℝ => hTransAB a b σ ν y')
      (I * (-(a : ℂ) - σ) * hTransAB (a + 1) b σ ν y + I * ((b : ℂ) + σ) * hTransAB a (b + 1) σ ν y) y) → (∀ (a b : ℕ) (ν y : ℝ), 2 ≤ a + b → y ≠ 0 → DifferentiableOn ℂ (fun σ => hTransAB a b σ ν y) halfPlane) →
  (∀ (n : ℝ) (k : ℕ) (y : ℝ), y ≠ 0 →
    (∀ σ ∈ halfPlane, HasDerivAt (iteratedDeriv k (hTrans σ n)) (iteratedDeriv (k + 1) (hTrans σ n) y) y) ∧
    DifferentiableOn ℂ (fun σ => iteratedDeriv k (hTrans σ n) y) halfPlane) := by
  intro h1 h2 n k y hy
  obtain ⟨ι, _, c, ab, hc, hab, h⟩ := iteratedDeriv_hTrans_eq_sum h1 n k
  refine ⟨fun σ hσ => ?_, ?_⟩
  · have hev : iteratedDeriv k (hTrans σ n) =ᶠ[nhds y]
        fun y' => ∑ i, c i σ * hTransAB (ab i).1 (ab i).2 σ n y' := by
      filter_upwards [isOpen_ne.mem_nhds hy] with y' hy' using h σ hσ y' hy'
    have hd := (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
      (h1 (ab i).1 (ab i).2 σ n y (hab i) hσ hy).const_mul (c i σ))).congr_of_eventuallyEq hev
    rw [iteratedDeriv_succ]
    exact hd.differentiableAt.hasDerivAt
  · refine DifferentiableOn.congr
      (f := fun σ => ∑ i, c i σ * hTransAB (ab i).1 (ab i).2 σ n y) ?_ (fun σ hσ => h σ hσ y hy)
    exact DifferentiableOn.fun_sum fun i _ =>
      (hc i).differentiableOn.mul (h2 _ _ n y (hab i) hy)

end GlobalTheory.HeckeTwo
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedDerivHeckePhiTransformHasDerivAtHoloStatement

section

@[expose] public section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo


theorem _root_.GlobalTheory.T.iteratedDeriv_heckePhiTransform_hasDerivAt_holo : (∀ (a b : ℕ) (σ : ℂ) (ν y : ℝ), 2 ≤ a + b → σ ∈ halfPlane → y ≠ 0 →
    HasDerivAt (fun y' : ℝ => hTransAB a b σ ν y')
      (I * (-(a : ℂ) - σ) * hTransAB (a + 1) b σ ν y + I * ((b : ℂ) + σ) * hTransAB a (b + 1) σ ν y) y) → (∀ (a b : ℕ) (ν y : ℝ), 2 ≤ a + b → y ≠ 0 → DifferentiableOn ℂ (fun σ => hTransAB a b σ ν y) halfPlane) →
  (∀ (n : ℝ) (k : ℕ) (y : ℝ), y ≠ 0 →
    (∀ σ ∈ halfPlane, HasDerivAt (iteratedDeriv k (hTrans σ n)) (iteratedDeriv (k + 1) (hTrans σ n) y) y) ∧
    DifferentiableOn ℂ (fun σ => iteratedDeriv k (hTrans σ n) y) halfPlane) := by
  first | exact @GlobalTheory.HeckeTwo.iteratedDeriv_hTrans_jet | exact GlobalTheory.HeckeTwo.iteratedDeriv_hTrans_jet | (intros; apply GlobalTheory.HeckeTwo.iteratedDeriv_hTrans_jet <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeFourierTermWirtingerWordDifferentiableOn

section

@[expose] public section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

namespace GlobalTheory.HeckeTwo.TermHol


open Classical in
theorem wirtWord_eq_sum (F : Type) [Field F] [NumberField F] (b ν : F) (hb : b ≠ 0) (hJ : (∀ (n : ℝ) (k : ℕ) (y : ℝ), y ≠ 0 →
    (∀ σ ∈ halfPlane, HasDerivAt (iteratedDeriv k (hTrans σ n)) (iteratedDeriv (k + 1) (hTrans σ n) y) y) ∧
    DifferentiableOn ℂ (fun σ => iteratedDeriv k (hTrans σ n) y) halfPlane))
    (w : List (Emb F × Bool)) :
    ∃ (ι : Type) (_ : Fintype ι) (c : ι → ℂ) (qf : ι → Emb F → ℕ), ∀ σ ∈ halfPlane, ∀ z ∈ upperHalf F,
      wirtWord w (fun z : Emb F → ℂ => fTerm σ z b ν) z = ∑ i, c i * termQ σ b ν (qf i) z := by
  have hU := GlobalTheory.HeckeTwo.GoodAdd.upperHalf_isOpen F
  induction w with
  | nil =>
    refine ⟨Unit, inferInstance, fun _ => 1, fun _ => 0, fun σ _ z _ => ?_⟩
    simp [wirtWord_nil, termQ_zero]
  | cons x ws ih =>
    obtain ⟨ι, _, c, qf, h⟩ := ih
    obtain ⟨τ₀, bar⟩ := x
    refine ⟨ι ⊕ ι, inferInstance,
      Sum.elim (fun i => c i * (2 * (Real.pi : ℂ) * I * ((τ₀ ν * τ₀ b : ℝ) : ℂ)) / 2)
        (fun i => (if bar then I else -I) * c i * ((τ₀ b : ℝ) : ℂ) / 2),
      Sum.elim qf (fun i => qf i + Pi.single τ₀ 1), fun σ hσ z hz => ?_⟩
    rw [wirtWord_cons]
    rw [GlobalTheory.HeckeTwo.GoodAdd.wirt_congr hU (g := fun z => ∑ i, c i * termQ σ b ν (qf i) z)
      (fun z hz => h σ hσ z hz) _ _ hz]
    have hd := fun i => GlobalTheory.T.heckeYDerivativeTerm_hasFDeriv_upperHalfPlane F b ν hb hJ σ hσ (qf i) z hz τ₀
    have hF : HasFDerivAt (fun z => ∑ i, c i * termQ σ b ν (qf i) z)
        (∑ i, c i • fderiv ℝ (termQ σ b ν (qf i)) z) z :=
      HasFDerivAt.fun_sum fun i _ => ((hd i).1.hasFDerivAt.const_mul (c i))
    simp only [wirt, hF.fderiv, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, (hd _).2.1, (hd _).2.2, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

end GlobalTheory.HeckeTwo.TermHol


open GlobalTheory.HeckeTwo.TermHol in
theorem GlobalTheory.HeckeTwo.fTerm_wirtWord_differentiableOn : ∀ (F : Type) [Field F] [NumberField F] (b ν : F), b ≠ 0 → ∀ w : List (Emb F × Bool), ∀ z ∈ upperHalf F,
  DifferentiableOn ℂ (fun σ => wirtWord w (fun z : Emb F → ℂ => fTerm σ z b ν) z) halfPlane := by
  intro F _ _ b ν hb w z hz
  have hJ := GlobalTheory.T.iteratedDeriv_heckePhiTransform_hasDerivAt_holo GlobalTheory.T.heckeHankelTransformAB_hasDerivAt_y GlobalTheory.T.heckeHankelTransformAB_differentiableOn_sigma
  obtain ⟨ι, _, c, qf, h⟩ := wirtWord_eq_sum F b ν hb hJ w
  refine DifferentiableOn.congr ?_ (fun σ hσ => h σ hσ z hz)
  refine DifferentiableOn.fun_sum fun i _ => DifferentiableOn.const_mul ?_ _
  unfold termQ
  refine DifferentiableOn.fun_finsetProd fun τ _ => DifferentiableOn.const_mul ?_ _
  have hy : (τ b : ℝ) * (z τ).im ≠ 0 :=
    mul_ne_zero ((map_ne_zero τ).2 hb) (hz τ).ne'
  exact (hJ (τ ν) (qf i τ) _ hy).2
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeFourierTermWirtingerWordDifferentiableOnStatement

section

@[expose] public section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo


theorem _root_.GlobalTheory.T.heckeFourierTerm_wirtingerWord_differentiableOn : ∀ (F : Type) [Field F] [NumberField F] (b ν : F), b ≠ 0 → ∀ w : List (Emb F × Bool), ∀ z ∈ upperHalf F,
  DifferentiableOn ℂ (fun σ => wirtWord w (fun z : Emb F → ℂ => fTerm σ z b ν) z) halfPlane := by
  first | exact @GlobalTheory.HeckeTwo.fTerm_wirtWord_differentiableOn | exact GlobalTheory.HeckeTwo.fTerm_wirtWord_differentiableOn | (intros; apply GlobalTheory.HeckeTwo.fTerm_wirtWord_differentiableOn <;> assumption)
end
end
