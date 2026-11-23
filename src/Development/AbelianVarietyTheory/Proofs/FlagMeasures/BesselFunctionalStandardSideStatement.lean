module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFormConvergesEquivariantHermitianStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupRepTwistedIsUnitaryRepStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupsClosedUnitaryWCompactStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnimodularBesselSubgroupsUWNStatement
import Formalism.FormalDegreeBessel.FinalG
import Mathlib.Tactic.TypeStar
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrableBesselCoefficientSmulEquivariantStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilFormulaBesselUnitaryIntegrableStatement
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFormalDegreeEqOfSchurOrthogonality

section

@[expose] public section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

theorem fdegH_eq_of_schurH (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mat k r → (H →L[ℂ] H)) (μG : Measure (Mt k r)) (d : ℝ) (w : H)
    (hS : SchurH μG σ d) (hw : w ≠ 0) : fdegH μG σ w = d := by
  obtain ⟨hd, hrel⟩ := hS
  obtain ⟨-, hint⟩ := hrel w w w w
  have hpt : ∀ g : Mt k r, coef σ w w (Matrix.of g) * star (coef σ w w (Matrix.of g))
      = ((‖⟪w, σ (Matrix.of g) w⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    intro g
    simp only [coef]
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp_rw [hpt] at hint
  rw [integral_complex_ofReal, inner_self_eq_norm_sq_to_K] at hint
  have hreal : ∫ x, ‖⟪w, σ (Matrix.of x) w⟫_ℂ‖ ^ 2 ∂μG = ‖w‖ ^ 4 / d := by
    apply Complex.ofReal_injective
    rw [hint]
    push_cast
    rw [← pow_add]
    rfl
  have hn : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw
  unfold fdegH
  rw [hreal]
  have h4 : (‖w‖ ^ 4 : ℝ) ≠ 0 := by positivity
  field_simp

end GlobalTheory.SgInf
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFormalDegreeEqOfSchurOrthogonalityStatement

section

@[expose] public section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.besselFormalDegree_eq_of_schurOrthogonality : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat k r → (H →L[ℂ] H)) (μG : Measure (Mt k r)) (d : ℝ) (w : H), SchurH μG σ d → w ≠ 0 → fdegH μG σ w = d := by
  first | exact @GlobalTheory.SgInf.fdegH_eq_of_schurH | exact GlobalTheory.SgInf.fdegH_eq_of_schurH | (intros; apply GlobalTheory.SgInf.fdegH_eq_of_schurH <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselInnerIntegralEqForm

section

@[expose] public section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.SgInf.InnerInt

theorem hpk_det_isUnit (k r : ℕ) : IsUnit (Hpk k r).det :=
  Matrix.isUnit_det_of_left_inverse (hpkFacts k r).2.1

theorem gg_mul {k r : ℕ} {a b : Mat k r} (ha : a ∈ GG k r) (hb : b ∈ GG k r) : a * b ∈ GG k r :=
  (uHGroup _ (Hpk k r) (hpk_det_isUnit k r)).2.1 a ha b hb

theorem gg_inv {k r : ℕ} {a : Mat k r} (ha : a ∈ GG k r) : IsUnit a.det ∧ a⁻¹ ∈ GG k r :=
  (uHGroup _ (Hpk k r) (hpk_det_isUnit k r)).2.2 a ha

theorem inner_map_of_norm {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (T : H →L[ℂ] H)
    (hT : ∀ v, ‖T v‖ = ‖v‖) (u v : H) : ⟪T u, T v⟫_ℂ = ⟪u, v⟫_ℂ :=
  (⟨T.toLinearMap, fun v => hT v⟩ : H →ₗᵢ[ℂ] H).inner_map_map u v

theorem star_coef_mul_eq {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat k r → (H →L[ℂ] H)) (hσ : IsURepOn (GG k r) σ) (w : H) {y s x : Mat k r}
    (hy : y ∈ GG k r) (hs : s ∈ GG k r) (hx : x ∈ GG k r) :
    star (coef σ w w (y⁻¹ * (s * x))) = coef σ (σ y w) (σ x w) s⁻¹ := by
  obtain ⟨⟨h1, hmul⟩, hiso, -⟩ := hσ
  obtain ⟨hyu, hyi⟩ := gg_inv hy
  obtain ⟨hsu, hsi⟩ := gg_inv hs
  have e1 : σ (y⁻¹ * (s * x)) = (σ y⁻¹).comp ((σ s).comp (σ x)) := by
    rw [hmul _ hyi _ (gg_mul hs hx), hmul _ hs _ hx]
  have e2 : ∀ v, σ y (σ y⁻¹ v) = v := by
    intro v
    have h := hmul _ hy _ hyi
    rw [Matrix.mul_nonsing_inv _ hyu, h1] at h
    have := congrArg (fun T : H →L[ℂ] H => T v) h
    simpa using this.symm
  have e3 : ∀ v, σ s⁻¹ (σ s v) = v := by
    intro v
    have h := hmul _ hsi _ hs
    rw [Matrix.nonsing_inv_mul _ hsu, h1] at h
    have := congrArg (fun T : H →L[ℂ] H => T v) h
    simpa using this.symm
  simp only [coef]
  rw [e1, ← starRingEnd_apply, inner_conj_symm]
  simp only [ContinuousLinearMap.comp_apply]
  have i1 := inner_map_of_norm (σ y) (hiso y hy) (σ y⁻¹ (σ s (σ x w))) w
  rw [e2] at i1
  rw [← i1]
  have i2 := inner_map_of_norm (σ s⁻¹) (hiso _ hsi) (σ s (σ x w)) (σ y w)
  rw [e3] at i2
  rw [← i2]

end GlobalTheory.SgInf.InnerInt


open GlobalTheory.SgInf.InnerInt in
theorem GlobalTheory.SgInf.inner_integral_eq_be : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ W : Mat k r → Wp, IsSPsiEquiv z (psiGen k r z c) π W → ∀ y ∈ GG k r, ∀ x : Mt k r, Matrix.of x ∈ GG k r → ∫ s, star (coef σ w w (y⁻¹ * (Matrix.of s * Matrix.of x))) • W (Matrix.of s * Matrix.of x) ∂μS = be (psiGen k r z c) π μS σ (σ y w) (σ (Matrix.of x) w) (W (Matrix.of x)) := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hstd hside W hW y hy x hx
  have hσ : IsURepOn (GG k r) σ := hstd.2.1
  have hdec : Decay σ (DD σ w : Set H) a := hstd.2.2.2.2.2.2.2.1
  have hz := hside.1
  have hT := hside.2.1
  have hπ := hside.2.2.1
  have hhaar := hside.2.2.2.1
  have hSG : Sset k r z ⊆ GG k r := (GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z hz hT).2.2.2.1.1
  have hpis := GlobalTheory.T.besselSubgroupRepTwisted_isUnitaryRep k r z c π hz hT hπ
  have huni := (GlobalTheory.T.unimodular_besselSubgroups_UW_N k r z hz hT μS).1 hhaar
  have hstab : ∀ g ∈ GG k r, ∀ v ∈ (DD σ w : Set H), σ g v ∈ (DD σ w : Set H) := by
    intro g hg v hv
    have hle : Submodule.map (σ g).toLinearMap (DD σ w) ≤ DD σ w := by
      rw [DD, Submodule.map_span_le]
      rintro _ ⟨g', hg', rfl⟩
      have : (σ g).toLinearMap (σ g' w) = σ (g * g') w := by
        rw [hσ.1.2 g hg g' hg']; rfl
      rw [this]; exact mem_DD σ w (gg_mul hg hg')
    exact hle ⟨v, hv, rfl⟩
  have hD := GlobalTheory.T.besselForm_converges_equivariant_hermitian k r σ w a μG d z c π μS hstd hside (DD σ w : Set H) hstab hdec
    (σ y w) (mem_DD σ w hy) (σ (Matrix.of x) w) (mem_DD σ w hx)
  have hFi := hD.1
  have hGi := hFi.apply_continuousLinearMap (W (Matrix.of x))
  have hm : AEStronglyMeasurable (fun s : Mt k r => (coef σ (σ y w) (σ (Matrix.of x) w) (Matrix.of s) •
      PiS (psiGen k r z c) π (Matrix.of s)⁻¹) (W (Matrix.of x))) (μS.map invM) := by
    rw [huni.2]; exact hGi.aestronglyMeasurable
  have hmap := integral_map measurable_invM.aemeasurable hm
  rw [huni.2] at hmap
  unfold be
  rw [ContinuousLinearMap.integral_apply hFi, hmap]
  refine integral_congr_ae ?_
  have hae : ∀ᵐ s ∂μS, Matrix.of s ∈ Sset k r z := ae_iff.2 hhaar.2.2.1
  filter_upwards [hae] with s hs
  have hsG := hSG hs
  have hdet := (gg_inv hsG).1
  obtain ⟨h, hh, m, hm', hsm⟩ := hs
  rw [of_invM, Matrix.nonsing_inv_nonsing_inv _ hdet, ContinuousLinearMap.smul_apply,
    star_coef_mul_eq σ hσ w hy hsG hx]
  congr 1
  rw [hsm, hW h hh m hm' _ hx, (hpis.1 h hh m hm').2, ContinuousLinearMap.smul_apply]
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselInnerIntegralEqFormStatement

section

@[expose] public section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.bessel_inner_integral_eq_form : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ W : Mat k r → Wp, IsSPsiEquiv z (psiGen k r z c) π W → ∀ y ∈ GG k r, ∀ x : Mt k r, Matrix.of x ∈ GG k r → ∫ s, star (coef σ w w (y⁻¹ * (Matrix.of s * Matrix.of x))) • W (Matrix.of s * Matrix.of x) ∂μS = be (psiGen k r z c) π μS σ (σ y w) (σ (Matrix.of x) w) (W (Matrix.of x)) := by
  first | exact @GlobalTheory.SgInf.inner_integral_eq_be | exact GlobalTheory.SgInf.inner_integral_eq_be | (intros; apply GlobalTheory.SgInf.inner_integral_eq_be <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFunctionalStandardSide

section

@[expose] public section

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.KernelRe

variable {k r : ℕ}

theorem hpk_unit : IsUnit (Hpk k r).det :=
  Matrix.isUnit_det_of_left_inverse (hpkFacts k r).2.1

theorem GG_unit {a : Mat k r} (ha : a ∈ GG k r) : IsUnit a.det := ((uHGroup _ _ hpk_unit).2.2 a ha).1

theorem GG_inv {a : Mat k r} (ha : a ∈ GG k r) : a⁻¹ ∈ GG k r := ((uHGroup _ _ hpk_unit).2.2 a ha).2

def lmulEquiv (a : Mat k r) (ha : IsUnit a.det) : Mt k r ≃ᵐ Mt k r where
  toFun x := lmulM a x
  invFun x := lmulM a⁻¹ x
  left_inv x := by
    show (a⁻¹ * (a * Matrix.of x) : Mat k r) = Matrix.of x
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ha, Matrix.one_mul]
  right_inv x := by
    show (a * (a⁻¹ * Matrix.of x) : Mat k r) = Matrix.of x
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ha, Matrix.one_mul]
  measurable_toFun := Continuous.measurable (α := Mt k r) (γ := Mt k r)
    (continuous_const.matrix_mul (continuous_id (X := Mat k r)))
  measurable_invFun := Continuous.measurable (α := Mt k r) (γ := Mt k r)
    (continuous_const.matrix_mul (continuous_id (X := Mat k r)))

theorem rconv_eq_translate {Wp : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
    (μG : Measure (Mt k r)) (e : Mat k r → ℂ) (W : Mat k r → Wp) (hμ : IsHaarOn (GG k r) μG)
    {y : Mat k r} (hy : y ∈ GG k r) :
    rconv μG e W y = ∫ g, e (y⁻¹ * Matrix.of g) • W (Matrix.of g) ∂μG := by
  have hyu : IsUnit y⁻¹.det := GG_unit (GG_inv hy)
  have hmap : μG.map (lmulM y⁻¹) = μG := hμ.2.2.2 _ (GG_inv hy)
  have hme : MeasurableEmbedding (lmulM (k := k) (r := r) y⁻¹) :=
    (lmulEquiv y⁻¹ hyu).measurableEmbedding
  unfold rconv
  conv_lhs => rw [← hmap]
  rw [hme.integral_map]
  congr 1; funext g
  show e (Matrix.of (lmulM y⁻¹ g)) • W (y * Matrix.of (lmulM y⁻¹ g)) = _
  show e (y⁻¹ * Matrix.of g) • W (y * (y⁻¹ * Matrix.of g)) = _
  rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (GG_unit hy), Matrix.one_mul]

theorem kernel_rconv : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → ∀ ν : Measure (Mt k r), IsQuotMeas μG μS ν → ∀ W : Mat k r → Wp, AEStronglyMeasurable (fun x : Mt k r => W (Matrix.of x)) μG → AEStronglyMeasurable (fun x : Mt k r => W (Matrix.of x)) ν → IsSPsiEquiv z (psiGen k r z c) π W → l2SG ν W < ⊤ → ∀ y ∈ GG k r, Integrable (fun g : Mt k r => be (psiGen k r z c) π μS σ (σ y w) (σ (Matrix.of g) w) (W (Matrix.of g))) ν ∧ rconv μG (eFun μG σ w) W y = (d : ℂ) • ∫ g, be (psiGen k r z c) π μS σ (σ y w) (σ (Matrix.of g) w) (W (Matrix.of g)) ∂ν := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide ν hν W hWG hWν hW hL2 y hy
  obtain ⟨hz, hT, hπ, hμS, _⟩ := hSide
  have hcl := GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z hz hT
  have hun := (GlobalTheory.T.unimodular_besselSubgroups_UW_N k r z hz hT μS).1 hμS
  have hμG : IsHaarOn (GG k r) μG := hStd.2.2.2.2.1
  have hWeil := GlobalTheory.T.weil_formula_besselUnitary_integrable k r (Sset k r z) μG μS ν hcl.2.2.2.1 hμG hμS hun hν
  have hFint : Integrable (fun g : Mt k r => star (coef σ w w (y⁻¹ * Matrix.of g)) • W (Matrix.of g)) μG :=
    GlobalTheory.T.integrable_besselCoefficient_smul_equivariant k r σ w a μG d z c π μS hStd ⟨hz, hT, hπ, hμS, inferInstance⟩ ν hν W hWG hWν hW hL2 y hy
  obtain ⟨hI, hEq⟩ := hWeil.2.2.2.1 Wp _ hFint
  have hae : ∀ᵐ x ∂ν, (∫ s, star (coef σ w w (y⁻¹ * Matrix.of (lmulM (Matrix.of s) x))) •
      W (Matrix.of (lmulM (Matrix.of s) x)) ∂μS) =
      be (psiGen k r z c) π μS σ (σ y w) (σ (Matrix.of x) w) (W (Matrix.of x)) := by
    have h0 : ∀ᵐ x ∂ν, Matrix.of x ∈ GG k r := by
      rw [ae_iff]; simpa using hWeil.2.1
    filter_upwards [h0] with x hx
    exact GlobalTheory.T.bessel_inner_integral_eq_form k r σ w a μG d z c π μS hStd ⟨hz, hT, hπ, hμS, inferInstance⟩ W hW y hy x hx
  have hfd : fdegH μG σ w = d :=
    GlobalTheory.T.besselFormalDegree_eq_of_schurOrthogonality k r σ μG d w hStd.2.2.2.2.2.1 (by
      intro h0; have := hStd.2.2.2.1; rw [h0, norm_zero] at this; exact zero_ne_one this)
  refine ⟨hI.congr hae, ?_⟩
  rw [rconv_eq_translate μG _ W hμG hy]
  have hfun : (fun g : Mt k r => eFun μG σ w (y⁻¹ * Matrix.of g) • W (Matrix.of g)) =
      fun g => (d : ℂ) • (star (coef σ w w (y⁻¹ * Matrix.of g)) • W (Matrix.of g)) := by
    funext g; simp only [eFun, hfd, coef, smul_smul]
  rw [hfun, integral_smul, hEq, integral_congr_ae hae]

end GlobalTheory.SgInf.KernelRe
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFunctionalStandardSideStatement

section

@[expose] public section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.bessel_functional_standard_side : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → ∀ ν : Measure (Mt k r), IsQuotMeas μG μS ν → ∀ W : Mat k r → Wp, AEStronglyMeasurable (fun x : Mt k r => W (Matrix.of x)) μG → AEStronglyMeasurable (fun x : Mt k r => W (Matrix.of x)) ν → IsSPsiEquiv z (psiGen k r z c) π W → l2SG ν W < ⊤ → ∀ y ∈ GG k r, Integrable (fun g : Mt k r => be (psiGen k r z c) π μS σ (σ y w) (σ (Matrix.of g) w) (W (Matrix.of g))) ν ∧ rconv μG (eFun μG σ w) W y = (d : ℂ) • ∫ g, be (psiGen k r z c) π μS σ (σ y w) (σ (Matrix.of g) w) (W (Matrix.of g)) ∂ν := by
  first | exact @GlobalTheory.SgInf.KernelRe.kernel_rconv | exact GlobalTheory.SgInf.KernelRe.kernel_rconv | (intros; apply GlobalTheory.SgInf.KernelRe.kernel_rconv <;> assumption)
end
end
