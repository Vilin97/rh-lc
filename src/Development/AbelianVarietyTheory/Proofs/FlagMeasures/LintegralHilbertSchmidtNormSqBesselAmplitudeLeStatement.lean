module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeEqAmpJAndBesselEqDoubleIntegralStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselModelProjectorOnLineStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsBesselMapRankOneFactorisationTranslateSpan
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
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsNonzeroFixedOfSquareIntegrableBesselStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IintEqEll
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralHsNormSqDoubleCosetLeFatouStatement
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothVectorsDenseInvariantStatement
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UhMeasurableSet
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsBesselMapRankOneFactorisationTranslateSpanStatement

section

@[expose] public section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.exists_besselMap_rankOne_factorisation_translateSpan : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → IsSmoothVec σ w → MultOne z (psiGen k r z c) σ π → ∀ ν : Measure (Mt k r), IsQuotMeas μG μS ν → NonVan z (psiGen k r z c) σ π w μG ν → ∃ l : H → Wp, IsEll z (psiGen k r z c) π μS σ (DD σ w) l := by
  first | exact @GlobalTheory.SgInf.exists_isEll_DD | exact GlobalTheory.SgInf.exists_isEll_DD | (intros; apply GlobalTheory.SgInf.exists_isEll_DD <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.IintEqEllStatement

section

@[expose] public section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.iint_eq_ell_alt : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [CompleteSpace Wq] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) (z' : Fin (2 * r + k + 1) → ℂ) (c' : Fin r → ℂ) (π' : Mat k r → (Wq →L[ℂ] Wq)) (μS' : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → Side z' π' μS' → ∀ (l : H → Wp) (l' : H → Wq), IsEll z (psiGen k r z c) π μS σ (DD σ w) l → IsEll z' (psiGen k r z' c') π' μS' σ (DD σ w) l' → ∀ γ ∈ Greg k r z z', Integrable (fun x : Mt k r => rk1 (l (σ (Matrix.of x) w)) (l' (σ (γ⁻¹ * Matrix.of x) w))) μG ∧ ∀ w₀ ∈ DD σ w, ∀ w₀' ∈ DD σ w, ∀ (ξ : Wp) (ξ' : Wq), Iint (psiGen k r z c) (psiGen k r z' c') π π' μS μS' σ w₀' w₀ ξ ξ' γ = (⟪l w₀, ξ⟫_ℂ * ⟪ξ', l' w₀'⟫_ℂ * (d : ℂ)) • OO μG (fun x => l (σ x w)) (fun x => l' (σ x w)) γ := by
  first | exact @GlobalTheory.SgInf.EllName.iint_eq_ell | exact GlobalTheory.SgInf.EllName.iint_eq_ell | (intros; apply GlobalTheory.SgInf.EllName.iint_eq_ell <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralHsNormSqMatrixCoeffLeFormalDegree

section

@[expose] public section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.EllBound

theorem exists_inner_eq_one {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {v : E}
    (hv : v ≠ 0) : ∃ ξ : E, ⟪v, ξ⟫_ℂ = 1 ∧ ⟪ξ, v⟫_ℂ = 1 := by
  have hvv : ⟪v, v⟫_ℂ ≠ 0 := inner_self_ne_zero.mpr hv
  refine ⟨(⟪v, v⟫_ℂ)⁻¹ • v, ?_, ?_⟩
  · rw [inner_smul_right]
    exact inv_mul_cancel₀ hvv
  · rw [inner_smul_left, map_inv₀, inner_conj_symm]
    exact inv_mul_cancel₀ hvv

theorem lintegral_hsNormSq_ell_le : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [CompleteSpace Wq] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) (z' : Fin (2 * r + k + 1) → ℂ) (c' : Fin r → ℂ) (π' : Mat k r → (Wq →L[ℂ] Wq)) (μS' : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → Side z' π' μS' → ∀ ν : Measure (Mt k r), IsDis (Greg k r z z') μG μS μS' ν → ∀ (l : H → Wp) (l' : H → Wq), IsEll z (psiGen k r z c) π μS σ (DD σ w) l → IsEll z' (psiGen k r z' c') π' μS' σ (DD σ w) l' → ∫⁻ γ, ENNReal.ofReal (hsNormSq ((d : ℂ) • OO μG (fun x => l (σ x w)) (fun x => l' (σ x w)) (Matrix.of γ))) ∂ν ≤ ENNReal.ofReal d⁻¹ := by
  intro k r H _ _ _ Wp _ _ _ _ Wq _ _ _ _ σ w a μG d z c π μS z' c' π' μS' hStd hS hS' ν hν l l' hl hl'

  obtain ⟨w₀, hw₀, hlw₀⟩ := hl.2.1
  obtain ⟨w₀', hw₀', hlw₀'⟩ := hl'.2.1
  obtain ⟨ξ, hξ₁, hξ₂⟩ := exists_inner_eq_one hlw₀
  obtain ⟨ξ', hξ₁', hξ₂'⟩ := exists_inner_eq_one hlw₀'

  have hbe : (⟪ξ, be (psiGen k r z c) π μS σ w₀ w₀ ξ⟫_ℂ).re = 1 := by
    rw [hl.2.2 w₀ hw₀ w₀ hw₀, rankOneInnerOperator_apply, inner_smul_right, hξ₁, hξ₂]
    simp
  have hbe' : (⟪ξ', be (psiGen k r z' c') π' μS' σ w₀' w₀' ξ'⟫_ℂ).re = 1 := by
    rw [hl'.2.2 w₀' hw₀' w₀' hw₀', rankOneInnerOperator_apply, inner_smul_right, hξ₁', hξ₂']
    simp
  have hbound := GlobalTheory.T.lintegral_hsNormSq_doubleCoset_le_fatou k r σ w a μG d z c π μS z' c' π' μS' hStd hS hS' ν hν
    w₀' hw₀' w₀ hw₀ ξ ξ'
  rw [hbe, hbe', mul_one, mul_one] at hbound
  refine le_trans (le_of_eq ?_) hbound

  have hreg : ∀ᵐ γ ∂ν, Matrix.of γ ∈ Greg k r z z' := ae_iff.mpr hν.2.1
  refine lintegral_congr_ae ?_
  filter_upwards [hreg] with γ hγ
  rw [(GlobalTheory.T.iint_eq_ell_alt k r σ w a μG d z c π μS z' c' π' μS' hStd hS hS' l l' hl hl' _ hγ).2
    w₀ hw₀ w₀' hw₀' ξ ξ', hξ₁, hξ₂']
  simp

end GlobalTheory.SgInf.EllBound
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralHsNormSqMatrixCoeffLeFormalDegreeStatement

section

@[expose] public section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.lintegral_hsNormSq_matrixCoeff_le_formalDegree : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [CompleteSpace Wq] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) (z' : Fin (2 * r + k + 1) → ℂ) (c' : Fin r → ℂ) (π' : Mat k r → (Wq →L[ℂ] Wq)) (μS' : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → Side z' π' μS' → ∀ ν : Measure (Mt k r), IsDis (Greg k r z z') μG μS μS' ν → ∀ (l : H → Wp) (l' : H → Wq), IsEll z (psiGen k r z c) π μS σ (DD σ w) l → IsEll z' (psiGen k r z' c') π' μS' σ (DD σ w) l' → ∫⁻ γ, ENNReal.ofReal (hsNormSq ((d : ℂ) • OO μG (fun x => l (σ x w)) (fun x => l' (σ x w)) (Matrix.of γ))) ∂ν ≤ ENNReal.ofReal d⁻¹ := by
  first | exact @GlobalTheory.SgInf.EllBound.lintegral_hsNormSq_ell_le | exact GlobalTheory.SgInf.EllBound.lintegral_hsNormSq_ell_le | (intros; apply GlobalTheory.SgInf.EllBound.lintegral_hsNormSq_ell_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralHilbertSchmidtNormSqBesselAmplitudeLe

section

@[expose] public section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.SchurNorm

theorem hsNormSq_smul {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (t : ℂ) (A : Wq →L[ℂ] Wp) :
    hsNormSq (t • A) = ‖t‖ ^ 2 * hsNormSq A := by
  have h : hsInner (t • A) (t • A) = ((‖t‖ ^ 2 : ℝ) : ℂ) * hsInner A A := by
    simp only [hsInner, Finset.mul_sum, ContinuousLinearMap.smul_apply, inner_smul_left, inner_smul_right]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hsNormSq, h, Complex.re_ofReal_mul, hsNormSq]

theorem ampJ_of_smul {k r : ℕ} {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] {μ : Measure (Mt k r)} (hμ : IsHaarOn (GG k r) μ)
    (c : ℝ) (t t' : ℂ) {Φ Ψ : Mat k r → Wp} {Φ' Ψ' : Mat k r → Wq} (h : ∀ g ∈ GG k r, Φ g = t • Ψ g)
    (h' : ∀ g ∈ GG k r, Φ' g = t' • Ψ' g) {γ : Mat k r} (hγ : γ ∈ GG k r) :
    ampJ μ c Φ Φ' γ = ((c : ℂ)⁻¹ * (t * star t')) • ampJ μ 1 Ψ Ψ' γ := by
  unfold ampJ
  rw [Complex.ofReal_one, inv_one, one_smul, mul_smul, ← integral_smul (t * star t')]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [show ∀ᵐ x ∂μ, Matrix.of x ∈ GG k r from hμ.2.2.1] with x hx
  rw [h _ (Formalism.FourierDecayAlt.P.DDSmoothness.uh_mul hγ hx), h' _ hx]
  ext η
  simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, ContinuousLinearMap.smul_apply,
    inner_smul_left, smul_smul, Complex.star_def]
  congr 1
  ring

theorem exists_isEll_smul (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp]
    (σ : Mat k r → (H →L[ℂ] H)) (v₀ : H) (a d c₀ : ℝ) (μG μS νS : Measure (Mt k r))
    (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (B : H → Wp) (hv : v₀ ≠ 0)
    (hS : StdSm σ (((‖v₀‖ : ℝ) : ℂ)⁻¹ • v₀) a μG d) (hz : SideIrr z π μS) (hq : IsQuotMeas μG μS νS)
    (hm : MultOne z (psiGen k r z c) σ π) (hB : IsBesselMapSm z (psiGen k r z c) σ π B) (hc : 0 < c₀)
    (h0 : l2SG νS (fun g => B (σ g v₀)) = ENNReal.ofReal (c₀ * Module.finrank ℂ Wp))
    (h1 : ∀ v ∈ smoothVecs σ, l2SG νS (fun g => B (σ g v)) * (‖v₀‖₊ : ℝ≥0∞) ^ 2 =
      l2SG νS (fun g => B (σ g v₀)) * (‖v‖₊ : ℝ≥0∞) ^ 2) :
    ∃ l : H → Wp, IsEll z (psiGen k r z c) π μS σ (DD σ (((‖v₀‖ : ℝ) : ℂ)⁻¹ • v₀)) l ∧
      ∃ t : ℂ, ‖t‖ ^ 2 = c₀ * Module.finrank ℂ Wp * d ∧
        ∀ g ∈ GG k r, B (σ g v₀) = t • l (σ g (((‖v₀‖ : ℝ) : ℂ)⁻¹ • v₀)) := by
  set w : H := ((‖v₀‖ : ℝ) : ℂ)⁻¹ • v₀ with hw
  have hn : ((‖v₀‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hv
  have hvw : v₀ = ((‖v₀‖ : ℝ) : ℂ) • w := by rw [hw, smul_smul, mul_inv_cancel₀ hn, one_smul]
  obtain ⟨hStd, hsm⟩ := hS
  have hU : IsURepOn (GG k r) σ := hStd.2.1
  have hw1 : ‖w‖ = 1 := hStd.2.2.2.1
  have hw1' : ‖w‖₊ = 1 := NNReal.eq hw1
  have hG : IsHaarOn (GG k r) μG := hStd.2.2.2.2.1
  have hd : 0 < d := hStd.2.2.2.2.2.1.1
  obtain ⟨-, -, hle, hact, hinf⟩ := GlobalTheory.T.smooth_vectors_dense_invariant k r σ w hU
  have hgw : ∀ g ∈ GG k r, σ g w ∈ smoothVecs (k := k) (r := r) σ := (hact w hsm).1
  haveI : Nontrivial Wp := hz.2.2
  have hdim : (0 : ℝ) < Module.finrank ℂ Wp := by exact_mod_cast Module.finrank_pos
  have hn0 : ((‖v₀‖₊ : ℝ≥0∞)) ^ 2 ≠ 0 := pow_ne_zero _ (by simpa using hv)
  have hnt : ((‖v₀‖₊ : ℝ≥0∞)) ^ 2 ≠ ⊤ := ENNReal.pow_ne_top ENNReal.coe_ne_top
  have hLw : l2SG νS (fun g => B (σ g w)) * (‖v₀‖₊ : ℝ≥0∞) ^ 2 = l2SG νS (fun g => B (σ g v₀)) := by
    rw [h1 w hsm, hw1']; simp
  have hnv : NonVan z (psiGen k r z c) σ π w μG νS := by
    refine GlobalTheory.T.exists_nonzero_fixed_of_squareIntegrable_bessel k r σ w a d μG μS νS z c π B ⟨hStd, hsm⟩ hz.1 hq hB ?_ ?_ ?_
    · intro h
      rw [h, zero_mul, h0] at hLw
      exact (ENNReal.ofReal_pos.2 (mul_pos hc hdim)).ne hLw
    · intro h
      rw [h, ENNReal.top_mul hn0, h0] at hLw
      exact ENNReal.ofReal_ne_top hLw.symm
    · intro v hv'
      refine (ENNReal.mul_left_inj hn0 hnt).1 ?_
      rw [h1 v hv', ← hLw]; ring
  obtain ⟨l, hl⟩ := GlobalTheory.T.exists_besselMap_rankOne_factorisation_translateSpan k r σ w a μG d z c π μS hStd hz.1 hsm hm νS hq hnv
  refine ⟨l, hl, ?_⟩
  have hs : ∃ s : ℂ, ∀ x ∈ smoothVecs (k := k) (r := r) σ, B x = s • l x := by
    obtain ⟨s, hs | hs⟩ := hm B l hB hl.1
    · exact ⟨s, hs⟩
    · obtain ⟨u, hu, hu0⟩ := hl.2.1
      have hs0 : s ≠ 0 := by
        rintro rfl
        exact hu0 ((hs u ((hinf hsm).1 u (hle hu))).trans (zero_smul _ _))
      exact ⟨s⁻¹, fun x hx => by rw [hs x hx, smul_smul, inv_mul_cancel₀ hs0, one_smul]⟩
  obtain ⟨s, hs⟩ := hs
  have key : ∀ g ∈ GG k r, B (σ g v₀) = (((‖v₀‖ : ℝ) : ℂ) * s) • l (σ g w) := by
    intro g hg
    have e : σ g v₀ = ((‖v₀‖ : ℝ) : ℂ) • σ g w := by rw [← map_smul, ← hvw]
    rw [e, hB.2.1 _ _ (hgw g hg), hs _ (hgw g hg), smul_smul]
  refine ⟨_, ?_, key⟩
  generalize ((‖v₀‖ : ℝ) : ℂ) * s = t at key
  have hone : (1 : Mat k r) ∈ GG k r := by simp [UH]
  have hwD : w ∈ DD σ w := by
    have := mem_DD σ w hone
    rwa [hU.1.1] at this
  have hlw := (GlobalTheory.T.besselModel_projector_on_line k r σ w a μG d z c π μS hStd hz.1 νS hq l hl).1 w hwD
  have hμS : IsHaarOn (Sset k r z) μS := hz.1.2.2.2.1
  have hae := Formalism.FourierDecayAlt.P.DDSmoothness.ae_UH_of_quot hG.2.2.1 hμS.2.1 (measure_mono_null (by
    rintro x hx ⟨h, hh, m, hm', e⟩
    exact hx (e ▸ Formalism.FourierDecayAlt.P.DDSmoothness.uh_mul hh.1 hm'.1)) hμS.2.2.1) hq
  have e : l2SG νS (fun g => B (σ g v₀)) = ENNReal.ofReal (‖t‖ ^ 2) * l2SG νS (fun x => l (σ x w)) := by
    unfold l2SG
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [key _ hx, nnnorm_smul, ENNReal.coe_mul, mul_pow, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
    rfl
  rw [h0, hlw, hw1, ← ENNReal.ofReal_mul (sq_nonneg _),
    ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)] at e
  rw [e]; field_simp

theorem lintegral_hsNormSq_ampJ_le : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [CompleteSpace Wq] (σ : Mat k r → (H →L[ℂ] H)) (v₀ : H) (a d c₀ : ℝ) (μG μS μS' νS νS' ν : Measure (Mt k r)) (z z' : (Fin (2 * r + k + 1) → ℂ)) (c c' : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (π' : Mat k r → (Wq →L[ℂ] Wq)) (B : H → Wp) (B' : H → Wq), v₀ ≠ 0 → StdSm σ (((‖v₀‖ : ℝ) : ℂ)⁻¹ • v₀) a μG d → SideIrr z π μS → SideIrr z' π' μS' → IsQuotMeas μG μS νS → IsQuotMeas μG μS' νS' → MultOne z (psiGen k r z c) σ π → MultOne z' (psiGen k r z' c') σ π' → IsBesselMapSm z (psiGen k r z c) σ π B → IsBesselMapSm z' (psiGen k r z' c') σ π' B' → 0 < c₀ → l2SG νS (fun g => B (σ g v₀)) = ENNReal.ofReal (c₀ * Module.finrank ℂ Wp) → l2SG νS' (fun g => B' (σ g v₀)) = ENNReal.ofReal (c₀ * Module.finrank ℂ Wq) → (∀ v ∈ smoothVecs σ, l2SG νS (fun g => B (σ g v)) * (‖v₀‖₊ : ℝ≥0∞) ^ 2 = l2SG νS (fun g => B (σ g v₀)) * (‖v‖₊ : ℝ≥0∞) ^ 2) → (∀ v ∈ smoothVecs σ, l2SG νS' (fun g => B' (σ g v)) * (‖v₀‖₊ : ℝ≥0∞) ^ 2 = l2SG νS' (fun g => B' (σ g v₀)) * (‖v‖₊ : ℝ≥0∞) ^ 2) → IsDis (Greg k r z z') μG μS μS' ν → ∫⁻ γ, ENNReal.ofReal (hsNormSq (ampJ μG c₀ (fun g => B (σ g v₀)) (fun g => B' (σ g v₀)) (Matrix.of γ))) ∂ν ≤ ENNReal.ofReal ((Module.finrank ℂ Wp : ℝ) * Module.finrank ℂ Wq / d) := by
  intro k r H _ _ _ Wp _ _ _ _ Wq _ _ _ _ σ v₀ a d c₀ μG μS μS' νS νS' ν z z' c c' π π' B B' hv hS hz hz' hq hq'
    hm hm' hB hB' hc h0 h0' h1 h1' hν
  obtain ⟨l, hl, t, ht, key⟩ := exists_isEll_smul k r σ v₀ a d c₀ μG μS νS z c π B hv hS hz hq hm hB hc h0 h1
  obtain ⟨l', hl', t', ht', key'⟩ :=
    exists_isEll_smul k r σ v₀ a d c₀ μG μS' νS' z' c' π' B' hv hS hz' hq' hm' hB' hc h0' h1'
  set w : H := ((‖v₀‖ : ℝ) : ℂ)⁻¹ • v₀ with hw
  have hG : IsHaarOn (GG k r) μG := hS.1.2.2.2.2.1
  have hd : 0 < d := hS.1.2.2.2.2.2.1.1
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have h5 := GlobalTheory.T.lintegral_hsNormSq_matrixCoeff_le_formalDegree k r σ w a μG d z c π μS z' c' π' μS' hS.1 hz.1 hz'.1 ν hν l l' hl hl'
  have hJ := (GlobalTheory.T.amplitude_eq_ampJ_and_bessel_eq_doubleIntegral k r (H := H) (Wp := Wp) (Wq := Wq)).1 μG (fun x => l (σ x w)) (fun x => l' (σ x w)) hG
  have hD : (0 : ℝ) ≤ (Module.finrank ℂ Wp : ℝ) * Module.finrank ℂ Wq := by positivity
  rw [div_eq_mul_inv, ENNReal.ofReal_mul hD]
  refine le_trans (le_of_eq ?_) (mul_le_mul_right h5 _)
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr_ae ?_
  filter_upwards [show ∀ᵐ γ ∂ν, Matrix.of γ ∈ Greg k r z z' from hν.2.1] with γ hγ
  rw [ampJ_of_smul hG c₀ t t' (Ψ := fun x => l (σ x w)) (Ψ' := fun x => l' (σ x w)) key key' hγ.1,
    ← hJ _ hγ.1, ← ENNReal.ofReal_mul hD, hsNormSq_smul, hsNormSq_smul]
  congr 1
  rw [norm_mul, norm_mul, norm_star, norm_inv, mul_pow, mul_pow, ht, ht', Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg hc.le, Real.norm_of_nonneg hd.le]
  field_simp

end GlobalTheory.Amp.SchurNorm
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralHilbertSchmidtNormSqBesselAmplitudeLeStatement

section

@[expose] public section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.lintegral_hilbertSchmidtNormSq_besselAmplitude_le : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [CompleteSpace Wq] (σ : Mat k r → (H →L[ℂ] H)) (v₀ : H) (a d c₀ : ℝ) (μG μS μS' νS νS' ν : Measure (Mt k r)) (z z' : (Fin (2 * r + k + 1) → ℂ)) (c c' : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (π' : Mat k r → (Wq →L[ℂ] Wq)) (B : H → Wp) (B' : H → Wq), v₀ ≠ 0 → StdSm σ (((‖v₀‖ : ℝ) : ℂ)⁻¹ • v₀) a μG d → SideIrr z π μS → SideIrr z' π' μS' → IsQuotMeas μG μS νS → IsQuotMeas μG μS' νS' → MultOne z (psiGen k r z c) σ π → MultOne z' (psiGen k r z' c') σ π' → IsBesselMapSm z (psiGen k r z c) σ π B → IsBesselMapSm z' (psiGen k r z' c') σ π' B' → 0 < c₀ → l2SG νS (fun g => B (σ g v₀)) = ENNReal.ofReal (c₀ * Module.finrank ℂ Wp) → l2SG νS' (fun g => B' (σ g v₀)) = ENNReal.ofReal (c₀ * Module.finrank ℂ Wq) → (∀ v ∈ smoothVecs σ, l2SG νS (fun g => B (σ g v)) * (‖v₀‖₊ : ℝ≥0∞) ^ 2 = l2SG νS (fun g => B (σ g v₀)) * (‖v‖₊ : ℝ≥0∞) ^ 2) → (∀ v ∈ smoothVecs σ, l2SG νS' (fun g => B' (σ g v)) * (‖v₀‖₊ : ℝ≥0∞) ^ 2 = l2SG νS' (fun g => B' (σ g v₀)) * (‖v‖₊ : ℝ≥0∞) ^ 2) → IsDis (Greg k r z z') μG μS μS' ν → ∫⁻ γ, ENNReal.ofReal (hsNormSq (ampJ μG c₀ (fun g => B (σ g v₀)) (fun g => B' (σ g v₀)) (Matrix.of γ))) ∂ν ≤ ENNReal.ofReal ((Module.finrank ℂ Wp : ℝ) * Module.finrank ℂ Wq / d) := by
  first | exact @GlobalTheory.Amp.SchurNorm.lintegral_hsNormSq_ampJ_le | exact GlobalTheory.Amp.SchurNorm.lintegral_hsNormSq_ampJ_le | (intros; apply GlobalTheory.Amp.SchurNorm.lintegral_hsNormSq_ampJ_le <;> assumption)
end
end
