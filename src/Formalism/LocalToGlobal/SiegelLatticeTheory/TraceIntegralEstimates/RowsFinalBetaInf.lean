module

public import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.BetaCut
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.SchurDecayBounds.SchurH
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanCoefficientNonzero.Development
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegralZeroFrequencyInvariant
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanCoefficientNonzero.InnerInvOfDS
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DilationScalesHeisenbergMeasure
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjointnessPolynomiallyBounded
import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanCoefficientNonzero.LimRightLimit

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanCoefficientNonzero.Factor

section

@[expose] public section

open MeasureTheory
open scoped InnerProductSpace ENNReal

noncomputable section

namespace PI.BICNZ

open Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.MainNotions.S.Pv.BetaCut

theorem sf_of_haar {k r : ℕ} {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) : SigmaFinite μ := by
  haveI : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => h.finite_compact K hK⟩
  infer_instance

theorem itD_const_mul (a : ℂ) (f : ℝ → ℂ) (n : ℕ) :
    iteratedDeriv n (fun y => a * f y) = fun y => a * iteratedDeriv n f y := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]
    exact deriv_const_mul_field' a

theorem oneMinusDD_prod (c : ℂ) (f g : ℝ → ℂ) (t₁ t₂ : ℝ) :
    oneMinusDD (fun a b => c * f a * g b) t₁ t₂ =
      c * (f t₁ - iteratedDeriv 2 f t₁) * (g t₂ - iteratedDeriv 2 g t₂) := by
  have e3 : ∀ (K : ℂ) (u : ℝ → ℂ) (t : ℝ), iteratedDeriv 2 (fun x => K * u x) t = K * iteratedDeriv 2 u t := by
    intro K u t
    rw [itD_const_mul]
  have e1 : ∀ x, iteratedDeriv 2 (fun y => c * f x * g y) t₂ = c * f x * iteratedDeriv 2 g t₂ := fun x =>
    e3 (c * f x) g t₂
  have e2 : (fun x => c * f x * g t₂ - iteratedDeriv 2 (fun y => c * f x * g y) t₂) =
      fun x => (c * (g t₂ - iteratedDeriv 2 g t₂)) * f x := by
    funext x
    rw [e1]
    ring
  show (c * f t₁ * g t₂ - iteratedDeriv 2 (fun y => c * f t₁ * g y) t₂) -
    iteratedDeriv 2 (fun x => c * f x * g t₂ - iteratedDeriv 2 (fun y => c * f x * g y) t₂) t₁ = _
  rw [e2, e3, e3]
  ring

theorem chi_eq_zero {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : RealPlaceData k r Wp Wq) {t : ℝ} (ht : t ≤ 0) : D.χ t = 0 := by
  by_contra hne
  have hs : t ∈ tsupport D.χ := subset_tsupport _ hne
  have := (D.χ_supp hs).1
  linarith

theorem chi_hasCompactSupport {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : RealPlaceData k r Wp Wq) : HasCompactSupport D.χ :=
  IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) (D.χ_supp.trans Set.Ioo_subset_Icc_self)

theorem regBracket_eq {k r : ℕ} {Wp Wq H : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (D : RealPlaceData k r Wp Wq) (σ : Mat k r → (H →L[ℂ] H)) (v v' : H) (ξ : Wp) (ξ' : Wq)
    (d : ℝ) (p : SS k r)
    (hΦ : ∀ t : ℝ × ℝ, 0 < t.1 → 0 < t.2 →
      Ph D (coefM σ v v' ξ ξ') (coefM σ v v' ξ ξ') (dilation₂ t p) =
        (d : ℂ)⁻¹ * Lf D σ v ξ (p.1.1, conjM (aDil k r t.1) p.1.2) *
          Rf D σ v' ξ' (p.2.1, conjM (aDil k r t.2) p.2.2)) :
    regBracket D (coefM σ v v' ξ ξ') (coefM σ v v' ξ ξ') p =
      fun a b => (d : ℂ)⁻¹ * H1 D σ v ξ p.1 a * H2 D σ v' ξ' p.2 b := by
  funext a b
  simp only [regBracket, H1, H2]
  by_cases ha : 0 < a
  · by_cases hb : 0 < b
    · have h := hΦ (a, b) ha hb
      dsimp only at h
      rw [h]
      have hk : (a * b) ^ kap k r = a ^ kap k r * b ^ kap k r := by
        first
        | exact mul_pow a b _
        | exact Real.mul_rpow ha.le hb.le
      rw [hk]
      simp only [Complex.ofReal_mul]
      ring
    · have h0 : D.χ b = 0 := chi_eq_zero D (not_lt.mp hb)
      simp [h0]
  · have h0 : D.χ a = 0 := chi_eq_zero D (not_lt.mp ha)
    simp [h0]

theorem hasCompactSupport_left_profile {k r : ℕ} {Wp Wq H : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (D : RealPlaceData k r Wp Wq) (σ : Mat k r → (H →L[ℂ] H)) (v : H) (ξ : Wp) (x : Mt k r × Mt k r) :
    HasCompactSupport (H1 D σ v ξ x) := by
  have h1 : HasCompactSupport (fun t : ℝ => D.χ t * t ^ kap k r) := (chi_hasCompactSupport D).mul_right
  have h2 : HasCompactSupport (fun t : ℝ => ((D.χ t * t ^ kap k r : ℝ) : ℂ)) := h1.comp_left Complex.ofReal_zero
  exact h2.mul_right (f' := fun t : ℝ => Lf D σ v ξ (x.1, conjM (aDil k r t) x.2))

theorem hasCompactSupport_right_profile {k r : ℕ} {Wp Wq H : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (D : RealPlaceData k r Wp Wq) (σ : Mat k r → (H →L[ℂ] H)) (v' : H) (ξ' : Wq) (x : Mt k r × Mt k r) :
    HasCompactSupport (H2 D σ v' ξ' x) := by
  have h1 : HasCompactSupport (fun t : ℝ => D.χ t * t ^ kap k r) := (chi_hasCompactSupport D).mul_right
  have h2 : HasCompactSupport (fun t : ℝ => ((D.χ t * t ^ kap k r : ℝ) : ℂ)) := h1.comp_left Complex.ofReal_zero
  exact h2.mul_right (f' := fun t : ℝ => Rf D σ v' ξ' (x.1, conjM (aDil k r t) x.2))

theorem ae_inSS {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : RealPlaceData k r Wp Wq) :
    ∀ᵐ p ∂((D.μW.prod D.μN).prod (D.μW'.prod D.μN)), D.inSS p := by
  haveI := sf_of_haar D.haarW
  haveI := sf_of_haar D.haarN
  haveI := sf_of_haar D.haarW'
  have hW : ∀ᵐ x ∂D.μW, Matrix.of x ∈ UWset k r D.z := by
    rw [ae_iff]
    exact D.haarW.conc
  have hN : ∀ᵐ x ∂D.μN, Matrix.of x ∈ Nset k r := by
    rw [ae_iff]
    exact D.haarN.conc
  have hW' : ∀ᵐ x ∂D.μW', Matrix.of x ∈ UWset k r D.z' := by
    rw [ae_iff]
    exact D.haarW'.conc
  have h1 : ∀ᵐ q ∂(D.μW.prod D.μN), Matrix.of q.1 ∈ UWset k r D.z ∧ Matrix.of q.2 ∈ Nset k r :=
    (Measure.quasiMeasurePreserving_fst.ae hW).and (Measure.quasiMeasurePreserving_snd.ae hN)
  have h2 : ∀ᵐ q ∂(D.μW'.prod D.μN), Matrix.of q.1 ∈ UWset k r D.z' ∧ Matrix.of q.2 ∈ Nset k r :=
    (Measure.quasiMeasurePreserving_fst.ae hW').and (Measure.quasiMeasurePreserving_snd.ae hN)
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae h1, Measure.quasiMeasurePreserving_snd.ae h2]
    with p hp1 hp2
  exact ⟨hp1.1, hp1.2, hp2.1, hp2.2⟩

theorem exp_split (t₁ t₂ a b : ℝ) :
    Complex.exp (Complex.I * (((1 : ℝ) * t₁ * a - (1 : ℝ) * t₂ * b : ℝ) : ℂ)) =
      Complex.exp (Complex.I * ((a * t₁ : ℝ) : ℂ)) * Complex.exp (Complex.I * ((-b * t₂ : ℝ) : ℂ)) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem betaFactor_of (hP : PhiAt) (hL : LeftProfileContDiffTwo) (hR : RightProfileContDiffTwo) : BetaFactor := by
  intro k r Wp Wq _ _ _ _ _ _ D ε lm H _ _ _ σ hHC hDS
  obtain ⟨d, hd, hΦ⟩ := hP k r Wp Wq D ε lm H σ hHC hDS
  refine ⟨d, hd, fun v v' ξ ξ' hv hv' => ?_⟩
  haveI := sf_of_haar D.haarW
  haveI := sf_of_haar D.haarN
  haveI := sf_of_haar D.haarW'
  have hpt : ∀ p : SS k r, D.inSS p →
      ((((1 + (1 : ℝ) ^ 2 * lam k r D.z (Matrix.of p.1.2) ^ 2)⁻¹ *
        (1 + (1 : ℝ) ^ 2 * lam k r D.z' (Matrix.of p.2.2) ^ 2)⁻¹ : ℝ) : ℂ) *
      ∫ t : ℝ × ℝ, oneMinusDD (regBracket D (coefM σ v v' ξ ξ') (coefM σ v v' ξ ξ') p) t.1 t.2 *
        Complex.exp (Complex.I * (((1 : ℝ) * t.1 * lam k r D.z (Matrix.of p.1.2) -
          (1 : ℝ) * t.2 * lam k r D.z' (Matrix.of p.2.2) : ℝ) : ℂ))) =
      (d : ℂ)⁻¹ * I1 D σ v ξ p.1 * I2 D σ v' ξ' p.2 := by
    intro p hp
    set a := lam k r D.z (Matrix.of p.1.2) with ha
    set b := lam k r D.z' (Matrix.of p.2.2) with hb
    have hreg := regBracket_eq D σ v v' ξ ξ' d p (fun t h1 h2 => hΦ v v' ξ ξ' p hp t h1 h2)
    have hA : ContDiff ℝ 2 (H1 D σ v ξ p.1) := hL k r Wp Wq D ε lm H σ hHC hDS v ξ hv p.1 hp.1 hp.2.1
    have hB : ContDiff ℝ 2 (H2 D σ v' ξ' p.2) := hR k r Wp Wq D ε lm H σ hHC hDS v' ξ' hv' p.2 hp.2.2.1 hp.2.2.2
    have iA := Formalism.FourierDecayAlt.P.integration_by_parts_regularised (H1 D σ v ξ p.1) hA (hasCompactSupport_left_profile D σ v ξ p.1) a
    have iB := Formalism.FourierDecayAlt.P.integration_by_parts_regularised (H2 D σ v' ξ' p.2) hB (hasCompactSupport_right_profile D σ v' ξ' p.2) (-b)
    have hsplit : (∫ t : ℝ × ℝ, oneMinusDD (regBracket D (coefM σ v v' ξ ξ') (coefM σ v v' ξ ξ') p) t.1 t.2 *
        Complex.exp (Complex.I * (((1 : ℝ) * t.1 * a - (1 : ℝ) * t.2 * b : ℝ) : ℂ))) =
        (d : ℂ)⁻¹ * ((∫ s : ℝ, (H1 D σ v ξ p.1 s - iteratedDeriv 2 (H1 D σ v ξ p.1) s) *
            Complex.exp (Complex.I * ((a * s : ℝ) : ℂ))) *
          (∫ s : ℝ, (H2 D σ v' ξ' p.2 s - iteratedDeriv 2 (H2 D σ v' ξ' p.2) s) *
            Complex.exp (Complex.I * ((-b * s : ℝ) : ℂ)))) := by
      rw [hreg]
      have e : ∀ t : ℝ × ℝ, oneMinusDD (fun a' b' => (d : ℂ)⁻¹ * H1 D σ v ξ p.1 a' * H2 D σ v' ξ' p.2 b') t.1 t.2 *
          Complex.exp (Complex.I * (((1 : ℝ) * t.1 * a - (1 : ℝ) * t.2 * b : ℝ) : ℂ)) =
          (d : ℂ)⁻¹ * (((H1 D σ v ξ p.1 t.1 - iteratedDeriv 2 (H1 D σ v ξ p.1) t.1) *
              Complex.exp (Complex.I * ((a * t.1 : ℝ) : ℂ))) *
            ((H2 D σ v' ξ' p.2 t.2 - iteratedDeriv 2 (H2 D σ v' ξ' p.2) t.2) *
              Complex.exp (Complex.I * ((-b * t.2 : ℝ) : ℂ)))) := by
        intro t
        rw [oneMinusDD_prod, exp_split]
        ring
      simp_rw [e]
      rw [integral_const_mul, Measure.volume_eq_prod]
      congr 1
      exact integral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
        (fun s => (H1 D σ v ξ p.1 s - iteratedDeriv 2 (H1 D σ v ξ p.1) s) *
            Complex.exp (Complex.I * ((a * s : ℝ) : ℂ)))
        (fun s => (H2 D σ v' ξ' p.2 s - iteratedDeriv 2 (H2 D σ v' ξ' p.2) s) *
            Complex.exp (Complex.I * ((-b * s : ℝ) : ℂ)))
    rw [hsplit, iA, iB]
    unfold I1 I2
    rw [← ha, ← hb]
    have h1 : (1 + a ^ 2 : ℝ) ≠ 0 := by positivity
    have h2 : (1 + b ^ 2 : ℝ) ≠ 0 := by positivity
    have hw : ((1 + (1 : ℝ) ^ 2 * a ^ 2)⁻¹ * (1 + (1 : ℝ) ^ 2 * b ^ 2)⁻¹) * ((1 + a ^ 2) * (1 + (-b) ^ 2)) = (1 : ℝ) := by
      rw [neg_sq, one_pow, one_mul, one_mul]
      field_simp
    have hw' : ((((1 + (1 : ℝ) ^ 2 * a ^ 2)⁻¹ * (1 + (1 : ℝ) ^ 2 * b ^ 2)⁻¹ : ℝ) : ℂ)) *
        (((1 + a ^ 2 : ℝ) : ℂ) * ((1 + (-b) ^ 2 : ℝ) : ℂ)) = 1 := by
      exact_mod_cast hw
    linear_combination ((d : ℂ)⁻¹ * (∫ t : ℝ, H1 D σ v ξ p.1 t * Complex.exp (Complex.I * ((a * t : ℝ) : ℂ))) *
      (∫ t : ℝ, H2 D σ v' ξ' p.2 t * Complex.exp (Complex.I * ((-b * t : ℝ) : ℂ)))) * hw'
  unfold betaInf betaInfTau RealPlaceData.μSS
  refine (integral_congr_ae (g := fun p : SS k r => (d : ℂ)⁻¹ * (I1 D σ v ξ p.1 * I2 D σ v' ξ' p.2)) ?_).trans ?_
  · filter_upwards [ae_inSS D] with p hp
    rw [← mul_assoc]
    exact hpt p hp
  · rw [integral_const_mul, mul_assoc]
    congr 1
    exact integral_prod_mul (μ := D.μW.prod D.μN) (ν := D.μW'.prod D.μN) (I1 D σ v ξ) (I2 D σ v' ξ')

end PI.BICNZ
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanCoefficientNonzero.Smooth

section

@[expose] public section

open MeasureTheory Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace PI.BICNZ

open Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.MainNotions.S.Pv.BetaCut

theorem two_le_smooth : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)

section curve

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

theorem ofReal_contDiffAt {f : ℝ → ℝ} {x : ℝ} {m : WithTop ℕ∞} (hf : ContDiffAt ℝ m f x) :
    ContDiffAt ℝ m (fun t => (f t : ℂ)) x := Complex.ofRealCLM.contDiff.contDiffAt.comp x hf

theorem dgR_contDiffAt (i : Fin (2 * r + k + 1)) {t₀ : ℝ} (h0 : t₀ ≠ 0) :
    ContDiffAt ℝ 2 (fun t => Formalism.FourierDecayAlt.P.B2x7.dgR k r t i) t₀ := by
  unfold Formalism.FourierDecayAlt.P.B2x7.dgR
  split_ifs
  · exact (contDiff_id.pow _).contDiffAt
  · exact contDiffAt_const
  · exact ((contDiff_id.pow _).contDiffAt).inv (pow_ne_zero _ h0)

theorem curve_eq (n h : Mt k r) {t : ℝ} (ht : t ≠ 0) :
    Matrix.of (conjM (aDil k r t) n) * Matrix.of h =
      Matrix.of fun i j => ∑ l, (((Formalism.FourierDecayAlt.P.B2x7.dgR k r t i : ℝ) : ℂ) * n i l *
        ((Formalism.FourierDecayAlt.P.B2x7.dgR k r t⁻¹ l : ℝ) : ℂ)) * h l j := by
  show aDil k r t * Matrix.of n * (aDil k r t)⁻¹ * Matrix.of h = _
  rw [Formalism.FourierDecayAlt.P.B2.aDil_inv k r t ht, Formalism.FourierDecayAlt.P.B2x7.aDil_eq, Formalism.FourierDecayAlt.P.B2x7.aDil_eq]
  ext i j
  rw [Matrix.mul_apply, Matrix.of_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rfl

theorem curve_contDiffAt (n h : Mt k r) {t₀ : ℝ} (h0 : t₀ ≠ 0) :
    ContDiffAt ℝ 2 (fun t : ℝ => Matrix.of (conjM (aDil k r t) n) * Matrix.of h) t₀ := by
  have hev : (fun t : ℝ => Matrix.of (conjM (aDil k r t) n) * Matrix.of h) =ᶠ[𝓝 t₀]
      (fun t => Matrix.of fun i j => ∑ l, (((Formalism.FourierDecayAlt.P.B2x7.dgR k r t i : ℝ) : ℂ) * n i l *
        ((Formalism.FourierDecayAlt.P.B2x7.dgR k r t⁻¹ l : ℝ) : ℂ)) * h l j) := by
    filter_upwards [isOpen_ne.mem_nhds h0] with t ht
    exact curve_eq n h ht
  refine ContDiffAt.congr_of_eventuallyEq ?_ hev
  refine contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun j => ?_
  simp only [Matrix.of_apply]
  refine ContDiffAt.sum fun l _ => ?_
  exact (((ofReal_contDiffAt (dgR_contDiffAt i h0)).mul contDiffAt_const).mul
    (ofReal_contDiffAt ((dgR_contDiffAt l (inv_ne_zero h0)).comp t₀ (contDiffAt_inv ℝ h0)))).mul contDiffAt_const

theorem coef_contDiffAt {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat k r → (H →L[ℂ] H)) (w : H) (hw : w ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ) (n h : Mt k r)
    (hn : Matrix.of n ∈ UH (Hpk k r)) (hh : Matrix.of h ∈ UH (Hpk k r)) {t₀ : ℝ} (h0 : t₀ ≠ 0) :
    ContDiffAt ℝ 2 (fun t : ℝ => σ (Matrix.of (conjM (aDil k r t) n) * Matrix.of h) w) t₀ := by
  set c : ℝ → Mat k r := fun t => Matrix.of (conjM (aDil k r t) n) * Matrix.of h with hc
  have hmem : ∀ t : ℝ, t ≠ 0 → c t ∈ UH (Hpk k r) := fun t ht =>
    WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul (Formalism.FourierDecayAlt.P.dilation_mem_group k r t ht) hn)
      (WeylGroupFacts.uh_inv (Formalism.FourierDecayAlt.P.dilation_mem_group k r t ht))) hh
  have hw' : PI.UpqRep.SmoothOnH (PI.UpqRep.Hpk k r) (fun g => σ g w) := hw
  obtain ⟨U, F, hU, hcU, hF, hFeq⟩ := hw' (c t₀) (hmem t₀ h0)
  have hcd : ContDiffAt ℝ 2 c t₀ := curve_contDiffAt n h h0
  have hFc : ContDiffAt ℝ 2 (F ∘ c) t₀ :=
    ((hF.contDiffAt (hU.mem_nhds hcU)).of_le two_le_smooth).comp t₀ hcd
  refine hFc.congr_of_eventuallyEq ?_
  filter_upwards [hcd.continuousAt.preimage_mem_nhds (hU.mem_nhds hcU), eventually_ne_nhds h0] with t htU ht
  exact hFeq (c t) htU (hmem t ht)

end curve

theorem chi_factor_contDiffAt {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : RealPlaceData k r Wp Wq) (t₀ : ℝ) :
    ContDiffAt ℝ 2 (fun t : ℝ => ((D.χ t * t ^ kap k r : ℝ) : ℂ)) t₀ := ofReal_contDiffAt ((D.χ_smooth.contDiffAt.of_le two_le_smooth).mul ((contDiff_id.pow _).contDiffAt))

theorem pos_of_mem_tsupport {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : RealPlaceData k r Wp Wq) {t₀ : ℝ}
    (ht : t₀ ∈ tsupport D.χ) : t₀ ≠ 0 := fun h => by
  have := D.χ_supp ht
  rw [h] at this
  norm_num at this

theorem left_profile_contDiff_two : LeftProfileContDiffTwo := by
  intro k r Wp Wq _ _ _ _ _ _ D ε lm H _ _ _ σ hHC hDS v ξ hv x hx1 hx2
  rw [contDiff_iff_contDiffAt]
  intro t₀
  by_cases ht : t₀ ∈ tsupport D.χ
  · have hw := coef_contDiffAt σ v hv x.2 x.1 hx2.1 hx1.1 (pos_of_mem_tsupport D ht)
    have hin : ContDiffAt ℝ 2
        (fun t : ℝ => ⟪σ (Matrix.of (conjM (aDil k r t) x.2) * Matrix.of x.1) v, v⟫_ℂ) t₀ :=
      hw.inner ℂ contDiffAt_const
    show ContDiffAt ℝ 2 (fun t : ℝ => ((D.χ t * t ^ kap k r : ℝ) : ℂ) *
      (⟪ξ, D.π (Matrix.of x.1) ξ⟫_ℂ * ⟪σ (Matrix.of (conjM (aDil k r t) x.2) * Matrix.of x.1) v, v⟫_ℂ)) t₀
    exact (chi_factor_contDiffAt D t₀).mul (contDiffAt_const.mul hin)
  · have hz : D.χ =ᶠ[𝓝 t₀] 0 := notMem_tsupport_iff_eventuallyEq.1 ht
    refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [hz] with t htz
    simp [H1, htz]

theorem right_profile_contDiff_two : RightProfileContDiffTwo := by
  intro k r Wp Wq _ _ _ _ _ _ D ε lm H _ _ _ σ hHC hDS v' ξ' hv' x hx1 hx2
  rw [contDiff_iff_contDiffAt]
  intro t₀
  by_cases ht : t₀ ∈ tsupport D.χ
  · have hw := coef_contDiffAt σ v' hv' x.2 x.1 hx2.1 hx1.1 (pos_of_mem_tsupport D ht)
    have hin : ContDiffAt ℝ 2
        (fun t : ℝ => ⟪v', σ (Matrix.of (conjM (aDil k r t) x.2) * Matrix.of x.1) v'⟫_ℂ) t₀ :=
      contDiffAt_const.inner ℂ hw
    show ContDiffAt ℝ 2 (fun t : ℝ => ((D.χ t * t ^ kap k r : ℝ) : ℂ) *
      (⟪ξ', D.π' (Matrix.of x.1)⁻¹ ξ'⟫_ℂ * ⟪v', σ (Matrix.of (conjM (aDil k r t) x.2) * Matrix.of x.1) v'⟫_ℂ)) t₀
    exact (chi_factor_contDiffAt D t₀).mul (contDiffAt_const.mul hin)
  · have hz : D.χ =ᶠ[𝓝 t₀] 0 := notMem_tsupport_iff_eventuallyEq.1 ht
    refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [hz] with t htz
    simp [H2, htz]

end PI.BICNZ
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanCoefficientNonzero.Assemble

section

@[expose] public section

namespace PI.BICNZ

theorem betaInfCoefNZ_of_limits (hS : Formalism.FourierDecayAlt.ThreeDimData.SchurH) (hL : LeftLimit) (hR : RightLimit) :
    Formalism.MainNotions.S.Pv.BetaCut.BetaInfCoefNZ :=
  betaInfCoefNZ_of (betaFactor_of (phiAt_of hS) left_profile_contDiff_two right_profile_contDiff_two) hL hR

end PI.BICNZ
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BetaInfCoefNZ

section

@[expose] public section

namespace PI.BICNZ

theorem betaInfCoefNZ_proof_of (hS : Formalism.FourierDecayAlt.ThreeDimData.SchurH) : Formalism.MainNotions.S.Pv.BetaCut.BetaInfCoefNZ :=
  betaInfCoefNZ_of_limits hS lim_leftLimit lim_rightLimit

end PI.BICNZ
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.RowsFinalBetaInf

section

@[expose] public section

namespace Formalism.MainNotions.S.Pv.BetaCut

theorem betaInfCoef_ne_zero : BetaInfCoefNZ := PI.BICNZ.betaInfCoefNZ_proof_of PI.WBL.NIS.schurH

end Formalism.MainNotions.S.Pv.BetaCut
end
end
