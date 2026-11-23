module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.PsiDatumStatement
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.CayleyConjInvMemHermitianGroup
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.LholClmEventually
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.ReproducingKernels.OneLeGN
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.ReproducingKernels.ProductBoundOfFactorBounds
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.ReproducingKernels.DecDeriv
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.ReproducingKernels.ProductBoundOfFactorBounds
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.ContinuousBlkWConj

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.FinBFrobConjGe

section

@[expose] public section

noncomputable section

open Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

theorem finB_umat_inv {n : ℕ} {ε : Fin n → Bool} (y : Formalism.REAL.UJ ε) :
    Formalism.MainNotions.S.umat y⁻¹ = (Formalism.MainNotions.S.umat y)⁻¹ := by
  show ((y⁻¹ : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ).val = _
  rw [Subgroup.coe_inv, Matrix.coe_units_inv]

theorem finB_umat_mul {n : ℕ} {ε : Fin n → Bool} (a b : Formalism.REAL.UJ ε) :
    Formalism.MainNotions.S.umat (a * b) = Formalism.MainNotions.S.umat a * Formalism.MainNotions.S.umat b := rfl

theorem finB_intJ_shift {k r : ℕ} (ε : Fin (2 * r + k + 1) → Bool) (b : ℝ)
    (hI : Integrable (fun y : Formalism.REAL.UJ ε => frob (Formalism.MainNotions.S.umat y) ^ (-b)) (Formalism.REAL.muG ε))
    (γ : Formalism.REAL.UJ ε) :
    Integrable (fun y : Formalism.REAL.UJ ε => frob ((Formalism.MainNotions.S.umat y)⁻¹ * Formalism.MainNotions.S.umat γ) ^ (-b)) (Formalism.REAL.muG ε) ∧
    ∫ y, frob ((Formalism.MainNotions.S.umat y)⁻¹ * Formalism.MainNotions.S.umat γ) ^ (-b) ∂(Formalism.REAL.muG ε) =
      ∫ y, frob (Formalism.MainNotions.S.umat y) ^ (-b) ∂(Formalism.REAL.muG ε) := by
  have e : (fun y : Formalism.REAL.UJ ε => frob ((Formalism.MainNotions.S.umat y)⁻¹ * Formalism.MainNotions.S.umat γ) ^ (-b)) =
      fun y => (fun y' : Formalism.REAL.UJ ε => frob (Formalism.MainNotions.S.umat y') ^ (-b)) (γ⁻¹ * y) := by
    funext y
    have h1 : (Formalism.MainNotions.S.umat y)⁻¹ * Formalism.MainNotions.S.umat γ = (Formalism.MainNotions.S.umat (γ⁻¹ * y))⁻¹ := by
      rw [← finB_umat_inv, ← finB_umat_inv, ← finB_umat_mul, _root_.mul_inv_rev, inv_inv]
    simp only
    rw [h1, finB_frob_inv (unitary_matrix_mem_set ε _)]
  rw [e]
  exact ⟨hI.comp_mul_left γ⁻¹,
    integral_mul_left_eq_self (μ := Formalism.REAL.muG ε) (fun y' : Formalism.REAL.UJ ε => frob (Formalism.MainNotions.S.umat y') ^ (-b)) γ⁻¹⟩

theorem finB_pair {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} (β : ℝ) (hβ : 0 ≤ β) {Y g : Mat k r}
    (hY : Y ∈ UJset ε) (hg : g ∈ UJset ε) (hYg : Y⁻¹ * g ∈ UJset ε) :
    frob Y ^ (-β) * frob (Y⁻¹ * g) ^ (-β) ≤
      frob g ^ (-(β / 4)) * (frob Y ^ (-(β / 2)) + frob (Y⁻¹ * g) ^ (-(β / 2))) := by
  have hA := finB_one_le hY
  have hB := finB_one_le hYg
  have hG := finB_one_le hg
  have hle := finB_le_mul hY g
  have hAh : 0 ≤ frob Y ^ (-(β / 2)) := Real.rpow_nonneg (by linarith) _
  have hBh : 0 ≤ frob (Y⁻¹ * g) ^ (-(β / 2)) := Real.rpow_nonneg (by linarith) _
  have hGq : 0 ≤ frob g ^ (-(β / 4)) := Real.rpow_nonneg (by linarith) _
  rcases le_total (frob Y) (frob (Y⁻¹ * g)) with h | h
  · calc _ ≤ frob g ^ (-(β / 4)) * frob (Y⁻¹ * g) ^ (-(β / 2)) :=
          S0.DecA.pb_real β _ _ _ hβ hA hB (by linarith) (le_of_le_of_eq hle (mul_comm _ _)) h
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hAh) hGq
  · have := S0.DecA.pb_real β (frob (Y⁻¹ * g)) (frob Y) (frob g) hβ hB hA (by linarith) hle h
    rw [mul_comm] at this
    calc _ ≤ frob g ^ (-(β / 4)) * frob Y ^ (-(β / 2)) := this
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hBh) hGq

theorem finB_one_UH (k r : ℕ) : (1 : Mat k r) ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
  show (1 : Mat k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r * 1 = Formalism.QuantumDeterminants.Hpk k r
  simp

theorem finB_frob_conj_ge {k r : ℕ} {P : Mat k r} (hP : IsUnit P.det) :
    ∃ c : ℝ, 0 < c ∧ ∀ g : Mat k r, c * Formalism.FourierDecayAlt.B.gN g ≤ frob (P * g * P⁻¹) := by
  letI : NormedAddCommGroup (Mat k r) := Matrix.frobeniusNormedAddCommGroup
  have hg : ∀ A : Mat k r, Formalism.FourierDecayAlt.B.gN A = ‖A‖ := by
    intro A
    rw [Matrix.frobenius_norm_def, Formalism.FourierDecayAlt.B.gN, Real.sqrt_eq_rpow]
    congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.normSq_eq_norm_sq, Real.rpow_two]
  have hf : ∀ A : Mat k r, frob A = ‖A‖ := by
    intro A
    rw [Matrix.frobenius_norm_def, frob, Real.sqrt_eq_rpow]
    congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Real.rpow_two]
  refine ⟨1 / (‖P⁻¹‖ * ‖P‖ + 1), by positivity, fun g => ?_⟩
  have e : g = P⁻¹ * (P * g * P⁻¹) * P := by
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hP, Matrix.nonsing_inv_mul _ hP,
      Matrix.mul_one]
  have h1 : ‖g‖ ≤ ‖P⁻¹‖ * ‖P * g * P⁻¹‖ * ‖P‖ := by
    conv_lhs => rw [e]
    calc ‖P⁻¹ * (P * g * P⁻¹) * P‖ ≤ ‖P⁻¹ * (P * g * P⁻¹)‖ * ‖P‖ := Matrix.frobenius_norm_mul _ _
      _ ≤ ‖P⁻¹‖ * ‖P * g * P⁻¹‖ * ‖P‖ :=
        mul_le_mul_of_nonneg_right (Matrix.frobenius_norm_mul _ _) (norm_nonneg _)
  rw [hg, hf, div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
  nlinarith [norm_nonneg (P * g * P⁻¹), norm_nonneg P⁻¹, norm_nonneg P,
    mul_nonneg (norm_nonneg P⁻¹) (norm_nonneg P)]

theorem finB_intS (hIS : S0.IntSStatement) {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}
    {P : Mat k r} (hP : Formalism.MainNotions.S.IsCayley k r ε P) (z : Fin (2 * r + k + 1) → ℂ) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r))
    (hz : Formalism.QuantumDeterminants.inWb k r z) (hT : 0 < Formalism.QuantumDeterminants.Tz k r z)
    (hW : Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW) (hN : Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN)
    (x : Mat k r) (hx : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (b : ℝ) (hb : S0.bS k r < b) :
    Integrable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      frob (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹) ^ (-b)) (μW.prod μN) := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP.1
  have hb0 : 0 ≤ b := by
    have : 0 ≤ S0.bS k r := by unfold S0.bS S0.nS; positivity
    linarith
  obtain ⟨c0, hc0, hcg⟩ := finB_frob_conj_ge hd
  have h1 := hIS k r z μW μN hz hT hW hN 1 (finB_one_UH k r) x hx b hb
  simp only [inv_one, Matrix.one_mul] at h1
  have hae := ae_mem_unitary_nilpotent_product z μW μN hW hN
  have hof : Continuous (fun g : Formalism.QuantumDeterminants.Mt k r => (Matrix.of g : Mat k r)) := S0.Dec.of_cont k r
  have hfc : Continuous (fun M : Mat k r => frob M) := by
    have : (fun M : Mat k r => frob M) = fun M => Formalism.FourierDecayAlt.B.gN M := funext finB_frob_eq
    rw [this]; exact S0.Dec.gN_cont k r
  have hgc : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹) :=
    (continuous_const.matrix_mul (((hof.comp continuous_fst).matrix_mul (hof.comp continuous_snd)).matrix_mul
      continuous_const)).matrix_mul continuous_const
  refine Integrable.mono' (h1.const_mul (c0 ^ (-b))) ((hfc.comp hgc).measurable.pow_const _).aestronglyMeasurable ?_
  filter_upwards [hae] with p hp
  have hM : Matrix.of p.1 * Matrix.of p.2 * x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
    unitary_hermitian_form_mul_mem (unitary_hermitian_form_mul_mem hp.1.1 hp.2.1) hx
  have hg1 := S0.DecA.one_le_gN' hM
  have hge := hcg (Matrix.of p.1 * Matrix.of p.2 * x)
  have hpos : 0 < c0 * Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2 * x) := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
  calc frob (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹) ^ (-b)
      ≤ (c0 * Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2 * x)) ^ (-b) :=
        Real.rpow_le_rpow_of_nonpos hpos hge (by linarith)
    _ = c0 ^ (-b) * Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2 * x) ^ (-b) :=
        Real.mul_rpow hc0.le (by linarith)

theorem finB_UJ_mul {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {a b : Mat k r} (ha : a ∈ UJset ε)
    (hb : b ∈ UJset ε) : a * b ∈ UJset ε := by
  have ha' : aᴴ * Formalism.REAL.Jm ε * a = Formalism.REAL.Jm ε := (mir_inUJ_iff ε a).2 ha
  have hb' : bᴴ * Formalism.REAL.Jm ε * b = Formalism.REAL.Jm ε := (mir_inUJ_iff ε b).2 hb
  show inUJ ε (a * b)
  rw [← mir_inUJ_iff]
  show (a * b)ᴴ * Formalism.REAL.Jm ε * (a * b) = Formalism.REAL.Jm ε
  calc (a * b)ᴴ * Formalism.REAL.Jm ε * (a * b) = bᴴ * (aᴴ * Formalism.REAL.Jm ε * a) * b := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [ha', hb']

theorem finB_UJ_closed {k r : ℕ} (ε : Fin (2 * r + k + 1) → Bool) : IsClosed (UJset ε : Set (Mat k r)) :=
  isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
    continuous_const

theorem finB_gap {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {h : ℝ} (hgap : StepGap ε r h) :
    1 ≤ S7.q0 ε ∧ 0 < h ∧
      4 * max (2 * ((2 * r + k + 1 : ℕ) : ℝ) * (S7.q0 ε : ℝ)) (2 * (r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2) <
        aExp ε h - 1 := by
  obtain ⟨h1, h2⟩ := hgap
  have e : min (pOf ε : ℝ) (qOf ε : ℝ) = (S7.q0 ε : ℝ) := by unfold S7.q0; push_cast; rfl
  rw [e] at h2
  have hn : (0 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hmax0 : 0 ≤ max (2 * ((2 * r + k + 1 : ℕ) : ℝ) * (S7.q0 ε : ℝ)) (2 * (r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2) :=
    le_max_of_le_left (by positivity)
  refine ⟨?_, ?_, h2⟩
  · by_contra hq
    have hq0 : S7.q0 ε = 0 := by omega
    rw [hq0] at h2
    simp at h2
    have : (0 : ℝ) ≤ max 0 (2 * (r : ℝ) * (2 * (r : ℝ) + (k : ℝ) + 1) ^ 2) := le_max_left _ _
    linarith
  · have : 0 ≤ 3 * ((2 * r + k + 1 : ℕ) : ℝ) / 2 := by positivity
    have := le_max_left (3 * ((2 * r + k + 1 : ℕ) : ℝ) / 2) (1 + ((2 * r + k + 1 : ℕ) : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ))
    linarith

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.ProductBoundThreeFactors

section

@[expose] public section

noncomputable section

open Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

def finKer {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {Λ : Fin (2 * r + k + 1) → ℝ} (T' : S7.KType ε Λ)
    (μ' : Fin (2 * r + k + 1) → ℤ) (v₁ v₂ : T'.V) (P : Mat k r) (x : Mat k r) (y : Mat k r)
    (p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) : ℂ :=
  ⟪v₂, S7.PsiM T' μ' (y⁻¹ * (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹)) v₁⟫_ℂ

theorem finB_frob_nonneg {k r : ℕ} (g : Mat k r) : 0 ≤ frob g := Real.sqrt_nonneg _

theorem product_bound_three_factors (A B X p1 p2 Φ C0 C1 V : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hX : 0 ≤ X)
    (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) (hV : 0 ≤ V) (hp1 : 0 ≤ p1) (hp2 : 0 ≤ p2)
    (h1 : A ≤ C0 * p1) (h2 : B ≤ C1 * V * p2) (h3 : p1 * p2 ≤ Φ) :
    A * (B * X) ≤ C0 * C1 * V * X * Φ := by
  have e1 : A * (B * X) ≤ (C0 * p1) * ((C1 * V * p2) * X) :=
    mul_le_mul h1 (mul_le_mul_of_nonneg_right h2 hX) (mul_nonneg hB hX) (by positivity)
  have e2 : (C0 * p1) * ((C1 * V * p2) * X) = C0 * C1 * V * X * (p1 * p2) := by ring
  have e3 : C0 * C1 * V * X * (p1 * p2) ≤ C0 * C1 * V * X * Φ :=
    mul_le_mul_of_nonneg_left h3 (by positivity)
  linarith

theorem finFub_int' (hIS : S0.IntSStatement) (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (u : Fin k → ℝ)
    (lam' : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (Vp : Type) [NormedAddCommGroup Vp]
    [InnerProductSpace ℂ Vp] [CompleteSpace Vp] (π : Mat k r → (Vp →L[ℂ] Vp)) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r))
    (P : Mat k r) (hP : Formalism.MainNotions.S.IsCayley k r ε P) (hB : IsBData z c u π μW μN)
    (hgap : StepGap ε r h) (hlam : S7.IsHCParam lam')
    (hgl : GapAtLeast ε lam' h) (T' : S7.KType ε (lowK ε lam')) (μ' : Fin (2 * r + k + 1) → ℤ)
    (hμ : S7.IsMu lam' μ') (v₁ v₂ : T'.V) (ξ : Vp) (F : Mat k r → ℂ) (C : ℝ)
    (hFc : ContinuousOn F (UJset ε)) (hFb : ∀ g ∈ UJset ε, ‖F g‖ ≤ C * frob g ^ (1 - aExp ε h))
    (x : Mat k r) (hx : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    Integrable (fun q : Formalism.REAL.UJ ε × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      F (Formalism.MainNotions.S.umat q.1) • (finKer T' μ' v₁ v₂ P x (Formalism.MainNotions.S.umat q.1) q.2 •
        chiInv (Formalism.MainNotions.S.psiGen k r z c) π (Matrix.of q.2.1) (Matrix.of q.2.2) ξ))
      ((Formalism.REAL.muG ε).prod (μW.prod μN)) := by
  obtain ⟨hz, hT, -, hπW, hHW, hHN⟩ := hB
  haveI : SigmaFinite μW := hHW.1
  haveI : SigmaFinite μN := hHN.1
  obtain ⟨hq0, hh, hmax⟩ := finB_gap hgap
  set a := aExp ε h with ha
  set β := a - 1 with hβ
  have hm1 := le_max_left (2 * ((2 * r + k + 1 : ℕ) : ℝ) * (S7.q0 ε : ℝ)) (2 * (r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2)
  have hm2 := le_max_right (2 * ((2 * r + k + 1 : ℕ) : ℝ) * (S7.q0 ε : ℝ)) (2 * (r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2)
  have hpos1 : (0 : ℝ) ≤ 2 * ((2 * r + k + 1 : ℕ) : ℝ) * (S7.q0 ε : ℝ) := by positivity
  have hβ0 : 0 ≤ β := by linarith
  have hIJ := finB_intJ ε hq0 (β / 2) (by linarith)
  have hIS' := finB_intS hIS hP z μW μN hz hT hHW hHN x hx (β / 4) (by unfold S0.bS S0.nS; linarith)
  obtain ⟨C', hC'⟩ := S0.DecDeriv.psiM_frob_dec ε lam' h T' μ' hlam hgl hh hq0 hμ
  have hπU := hcTypeW_uRep k r z u Vp π hz hT hπW
  have hPae := ae_mem_unitary_nilpotent_product z μW μN hHW hHN
  have hQae : ∀ᵐ q ∂((Formalism.REAL.muG ε).prod (μW.prod μN)),
      Matrix.of q.2.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of q.2.2 ∈ Formalism.QuantumDeterminants.Nset k r :=
    Measure.quasiMeasurePreserving_snd.ae hPae
  have hgpJ : ∀ p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r,
      Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r →
        P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹ ∈ UJset ε := fun p hp =>
    cayley_conj_mem_unitary_group hP (unitary_hermitian_form_mul_mem (unitary_hermitian_form_mul_mem hp.1.1 hp.2.1) hx)

  have hof := S0.Dec.of_cont k r
  have hfc : Continuous (fun M : Mat k r => frob M) := by
    have : (fun M : Mat k r => frob M) = fun M => Formalism.FourierDecayAlt.B.gN M := funext finB_frob_eq
    rw [this]; exact S0.Dec.gN_cont k r
  have hgpc : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹) :=
    (continuous_const.matrix_mul (((hof.comp continuous_fst).matrix_mul (hof.comp continuous_snd)).matrix_mul
      continuous_const)).matrix_mul continuous_const
  have humc := continuous_unitary_matrix ε
  have hinvc : Continuous (fun y : Formalism.REAL.UJ ε => (Formalism.MainNotions.S.umat y)⁻¹) := by
    have : (fun y : Formalism.REAL.UJ ε => (Formalism.MainNotions.S.umat y)⁻¹) = fun y => Formalism.MainNotions.S.umat y⁻¹ :=
      funext fun y => (finB_umat_inv y).symm
    rw [this]; exact humc.comp continuous_inv
  have hmc : Continuous (fun q : Formalism.REAL.UJ ε × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      (Formalism.MainNotions.S.umat q.1)⁻¹ * (P * (Matrix.of q.2.1 * Matrix.of q.2.2 * x) * P⁻¹)) :=
    (hinvc.comp continuous_fst).matrix_mul (hgpc.comp continuous_snd)

  have hT2m : Measurable (fun q : Formalism.REAL.UJ ε × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      frob (P * (Matrix.of q.2.1 * Matrix.of q.2.2 * x) * P⁻¹) ^ (-(β / 4)) *
        frob ((Formalism.MainNotions.S.umat q.1)⁻¹ * (P * (Matrix.of q.2.1 * Matrix.of q.2.2 * x) * P⁻¹)) ^ (-(β / 2))) :=
    ((hfc.comp (hgpc.comp continuous_snd)).measurable.pow_const _).mul ((hfc.comp hmc).measurable.pow_const _)
  have hT1 : Integrable (fun q : Formalism.REAL.UJ ε × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      frob (Formalism.MainNotions.S.umat q.1) ^ (-(β / 2)) * frob (P * (Matrix.of q.2.1 * Matrix.of q.2.2 * x) * P⁻¹) ^ (-(β / 4)))
      ((Formalism.REAL.muG ε).prod (μW.prod μN)) := hIJ.mul_prod hIS'
  have hT2 : Integrable (fun q : Formalism.REAL.UJ ε × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      frob (P * (Matrix.of q.2.1 * Matrix.of q.2.2 * x) * P⁻¹) ^ (-(β / 4)) *
        frob ((Formalism.MainNotions.S.umat q.1)⁻¹ * (P * (Matrix.of q.2.1 * Matrix.of q.2.2 * x) * P⁻¹)) ^ (-(β / 2)))
      ((Formalism.REAL.muG ε).prod (μW.prod μN)) := by
    rw [integrable_prod_iff' hT2m.aestronglyMeasurable]
    constructor
    · filter_upwards [hPae] with p hp
      obtain ⟨γ, hγ⟩ := exists_unitary_preimage ε (hgpJ p hp)
      have h1 := (finB_intJ_shift ε (β / 2) hIJ γ).1
      rw [hγ] at h1
      exact h1.const_mul _
    · refine (hIS'.mul_const (∫ y, frob (Formalism.MainNotions.S.umat y) ^ (-(β / 2)) ∂(Formalism.REAL.muG ε))).congr ?_
      filter_upwards [hPae] with p hp
      obtain ⟨γ, hγ⟩ := exists_unitary_preimage ε (hgpJ p hp)
      have h2 := (finB_intJ_shift ε (β / 2) hIJ γ).2
      rw [hγ] at h2
      have hnn : ∀ y : Formalism.REAL.UJ ε,
          ‖frob (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹) ^ (-(β / 4)) *
            frob ((Formalism.MainNotions.S.umat y)⁻¹ * (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹)) ^ (-(β / 2))‖ =
          frob (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹) ^ (-(β / 4)) *
            frob ((Formalism.MainNotions.S.umat y)⁻¹ * (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹)) ^ (-(β / 2)) := by
        intro y
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (finB_frob_nonneg _) _)
          (Real.rpow_nonneg (finB_frob_nonneg _) _))]
      simp only [hnn]
      rw [integral_const_mul, h2]
  have hΦ : Integrable (fun q : Formalism.REAL.UJ ε × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      frob (P * (Matrix.of q.2.1 * Matrix.of q.2.2 * x) * P⁻¹) ^ (-(β / 4)) *
        (frob (Formalism.MainNotions.S.umat q.1) ^ (-(β / 2)) +
          frob ((Formalism.MainNotions.S.umat q.1)⁻¹ * (P * (Matrix.of q.2.1 * Matrix.of q.2.2 * x) * P⁻¹)) ^ (-(β / 2))))
      ((Formalism.REAL.muG ε).prod (μW.prod μN)) := by
    refine (hT1.add hT2).congr (Filter.Eventually.of_forall fun q => ?_)
    simp only [Pi.add_apply]; ring
  set S3 : Set (Formalism.REAL.UJ ε × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) :=
    {q | Matrix.of q.2.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ P * (Matrix.of q.2.1 * Matrix.of q.2.2 * x) * P⁻¹ ∈ UJset ε}
    with hS3
  have hScl : IsClosed S3 :=
    ((S0.Dec.UW_closed k r z).preimage (hof.comp (continuous_fst.comp continuous_snd))).inter
      ((finB_UJ_closed ε).preimage (hgpc.comp continuous_snd))
  have hSae : ∀ᵐ q ∂((Formalism.REAL.muG ε).prod (μW.prod μN)), q ∈ S3 := by
    filter_upwards [hQae] with q hq
    exact ⟨hq.1, hgpJ q.2 hq⟩
  have hE1 : ContinuousOn (fun q : Formalism.REAL.UJ ε × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      F (Formalism.MainNotions.S.umat q.1)) S3 :=
    (hFc.comp_continuous (humc.comp continuous_fst) (fun q => unitary_matrix_mem_set ε _)).continuousOn
  have hE2 : ContinuousOn (fun q : Formalism.REAL.UJ ε × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      finKer T' μ' v₁ v₂ P x (Formalism.MainNotions.S.umat q.1) q.2) S3 := by
    unfold finKer
    have hmaps : Set.MapsTo (fun q : Formalism.REAL.UJ ε × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
        (Formalism.MainNotions.S.umat q.1)⁻¹ * (P * (Matrix.of q.2.1 * Matrix.of q.2.2 * x) * P⁻¹)) S3 {g | inUJ ε g} := by
      intro q hq
      show (Formalism.MainNotions.S.umat q.1)⁻¹ * (P * (Matrix.of q.2.1 * Matrix.of q.2.2 * x) * P⁻¹) ∈ UJset ε
      rw [← finB_umat_inv]
      exact finB_UJ_mul (unitary_matrix_mem_set ε _) hq.2
    have h := (S7.psiM_continuousOn T' μ' hμ).comp hmc.continuousOn hmaps
    exact continuousOn_const.inner (h.clm_apply continuousOn_const)
  have hE3 : ContinuousOn (fun q : Formalism.REAL.UJ ε × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      chiInv (Formalism.MainNotions.S.psiGen k r z c) π (Matrix.of q.2.1) (Matrix.of q.2.2) ξ) S3 := by
    show ContinuousOn (fun q : Formalism.REAL.UJ ε × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      star (Formalism.MainNotions.S.psiGen k r z c (Matrix.of q.2.2)) • π (Matrix.of q.2.1)⁻¹ ξ) S3
    have hq21 : Continuous (fun q : Formalism.REAL.UJ ε × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) => Matrix.of q.2.1) :=
      hof.comp (continuous_fst.comp continuous_snd)
    have hinvc' : ContinuousOn (fun q : Formalism.REAL.UJ ε × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
        (Matrix.of q.2.1)⁻¹) S3 :=
      (((continuous_const.matrix_mul hq21.matrix_conjTranspose).matrix_mul continuous_const).continuousOn).congr
        (fun q hq => S0.DecA.inv_eq hq.1.1)
    have h := (hπU.2.2 ξ).comp hinvc' (fun q hq => S0.Dec.UW_inv_mem hq.1)
    exact (continuous_star.comp ((S0.Dec.psiGen_cont k r z c).comp
      (hof.comp (continuous_snd.comp continuous_snd)))).continuousOn.smul h
  refine Integrable.mono' (hΦ.const_mul (max C 0 * max C' 0 * (‖v₁‖ * ‖v₂‖) * ‖ξ‖)) ?_ ?_
  · rw [← Measure.restrict_eq_self_of_ae_mem hSae]
    exact (hE1.smul (hE2.smul hE3)).aestronglyMeasurable hScl.measurableSet
  filter_upwards [hQae] with q hq
  have hY := unitary_matrix_mem_set ε q.1
  have hg := hgpJ q.2 hq
  have hYg : (Formalism.MainNotions.S.umat q.1)⁻¹ * (P * (Matrix.of q.2.1 * Matrix.of q.2.2 * x) * P⁻¹) ∈ UJset ε := by
    rw [← finB_umat_inv]; exact finB_UJ_mul (unitary_matrix_mem_set ε _) hg
  have hψ : ‖Formalism.MainNotions.S.psiGen k r z c (Matrix.of q.2.2)‖ = 1 := by
    unfold Formalism.MainNotions.S.psiGen; rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I _
  have hπ' : ‖π (Matrix.of q.2.1)⁻¹ ξ‖ = ‖ξ‖ := hπU.2.1 _ (S0.Dec.UW_inv_mem hq.1) ξ
  have hchi : ‖chiInv (Formalism.MainNotions.S.psiGen k r z c) π (Matrix.of q.2.1) (Matrix.of q.2.2) ξ‖ = ‖ξ‖ := by
    simp only [chiInv, norm_smul, norm_star, hψ, hπ', one_mul]
  have hF1 : ‖F (Formalism.MainNotions.S.umat q.1)‖ ≤ max C 0 * frob (Formalism.MainNotions.S.umat q.1) ^ (-β) := by
    have h1 := hFb _ hY
    rw [show 1 - a = -β by rw [hβ]; ring] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (finB_frob_nonneg _) _))
  have hK1 : ‖finKer T' μ' v₁ v₂ P x (Formalism.MainNotions.S.umat q.1) q.2‖ ≤ max C' 0 * (‖v₁‖ * ‖v₂‖) *
      frob ((Formalism.MainNotions.S.umat q.1)⁻¹ * (P * (Matrix.of q.2.1 * Matrix.of q.2.2 * x) * P⁻¹)) ^ (-β) := by
    unfold finKer
    have h1 := hC' _ hYg
    have ea : h / (8 * Real.sqrt (2 * (S7.q0 ε : ℝ))) = a := rfl
    rw [ea] at h1
    have hle : frob ((Formalism.MainNotions.S.umat q.1)⁻¹ * (P * (Matrix.of q.2.1 * Matrix.of q.2.2 * x) * P⁻¹)) ^ (-a) ≤
        frob ((Formalism.MainNotions.S.umat q.1)⁻¹ * (P * (Matrix.of q.2.1 * Matrix.of q.2.2 * x) * P⁻¹)) ^ (-β) :=
      Real.rpow_le_rpow_of_exponent_le (finB_one_le hYg) (by rw [hβ]; linarith)
    have h2 : ‖S7.PsiM T' μ' ((Formalism.MainNotions.S.umat q.1)⁻¹ * (P * (Matrix.of q.2.1 * Matrix.of q.2.2 * x) * P⁻¹))‖ ≤
        max C' 0 * frob ((Formalism.MainNotions.S.umat q.1)⁻¹ * (P * (Matrix.of q.2.1 * Matrix.of q.2.2 * x) * P⁻¹)) ^ (-β) :=
      h1.trans (mul_le_mul (le_max_left _ _) hle (Real.rpow_nonneg (finB_frob_nonneg _) _) (le_max_right _ _))
    calc _ ≤ ‖v₂‖ * ‖S7.PsiM T' μ' ((Formalism.MainNotions.S.umat q.1)⁻¹ * (P * (Matrix.of q.2.1 * Matrix.of q.2.2 * x) * P⁻¹)) v₁‖ :=
          norm_inner_le_norm _ _
      _ ≤ ‖v₂‖ * (‖S7.PsiM T' μ' ((Formalism.MainNotions.S.umat q.1)⁻¹ * (P * (Matrix.of q.2.1 * Matrix.of q.2.2 * x) * P⁻¹))‖ * ‖v₁‖) :=
          mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ ≤ ‖v₂‖ * ((max C' 0 * frob ((Formalism.MainNotions.S.umat q.1)⁻¹ * (P * (Matrix.of q.2.1 * Matrix.of q.2.2 * x) * P⁻¹)) ^ (-β)) * ‖v₁‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 (norm_nonneg _)) (norm_nonneg _)
      _ = _ := by ring
  have hpair := finB_pair β hβ0 hY hg hYg
  rw [norm_smul, norm_smul, hchi]
  exact product_bound_three_factors _ _ _ _ _ _ _ _ _ (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (le_max_right _ _)
    (le_max_right _ _) (by positivity) (Real.rpow_nonneg (finB_frob_nonneg _) _)
    (Real.rpow_nonneg (finB_frob_nonneg _) _) hF1 hK1 hpair

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.FinFub

section

@[expose] public section

noncomputable section

open Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap
theorem finFub (hIS : S0.IntSStatement) (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (u : Fin k → ℝ) (lam' : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (Vp : Type) [NormedAddCommGroup Vp]
    [InnerProductSpace ℂ Vp] [CompleteSpace Vp] (π : Mat k r → (Vp →L[ℂ] Vp)) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r))
    (P : Mat k r) (hP : Formalism.MainNotions.S.IsCayley k r ε P) (hB : IsBData z c u π μW μN)
    (hp : pOf ε = k + r) (hq : qOf ε = r + 1) (hgap : StepGap ε r h) (hlam : S7.IsHCParam lam')
    (hgl : GapAtLeast ε lam' h) (T' : S7.KType ε (lowK ε lam')) (μ' : Fin (2 * r + k + 1) → ℤ)
    (hμ : S7.IsMu lam' μ') (v₁ v₂ : T'.V) (ξ : Vp) (F : Mat k r → ℂ) (C : ℝ)
    (hFc : ContinuousOn F (UJset ε)) (hFb : ∀ g ∈ UJset ε, ‖F g‖ ≤ C * frob g ^ (1 - aExp ε h))
    (hrep : ∀ x ∈ UJset ε, F x = ∫ y, F (Formalism.MainNotions.S.umat y) *
        ⟪v₂, S7.PsiM T' μ' ((Formalism.MainNotions.S.umat y)⁻¹ * x) v₁⟫_ℂ ∂(Formalism.REAL.muG ε))
    (x : Mat k r) (hx : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hne : per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π F ξ x ≠ 0) :
    ∃ x₀ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
      aaFun T' μ' P μW μN (Formalism.MainNotions.S.psiGen k r z c) π v₁ v₂ ξ x₀ x ≠ 0 := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP.1
  have hHW := hB.2.2.2.2.1
  have hHN := hB.2.2.2.2.2
  haveI : SigmaFinite μW := hHW.1
  haveI : SigmaFinite μN := hHN.1
  let integrand (y : Formalism.REAL.UJ ε)
      (p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) : Vp :=
    F (Formalism.MainNotions.S.umat y) • (finKer T' μ' v₁ v₂ P x (Formalism.MainNotions.S.umat y) p •
      chiInv (Formalism.MainNotions.S.psiGen k r z c) π (Matrix.of p.1) (Matrix.of p.2) ξ)
  have hint : Integrable (Function.uncurry integrand) ((Formalism.REAL.muG ε).prod (μW.prod μN)) :=
    finFub_int' hIS k r ε u lam' h z c Vp π μW μN P hP hB hgap hlam hgl T' μ' hμ v₁ v₂ ξ F C hFc hFb x hx
  by_contra hall
  push Not at hall
  apply hne
  have hae := ae_mem_unitary_nilpotent_product z μW μN hHW hHN
  have step1 : per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π F ξ x =
      ∫ p, ∫ y, integrand y p ∂(Formalism.REAL.muG ε) ∂(μW.prod μN) := by
    delta per sInt
    apply integral_congr_ae
    filter_upwards [hae] with p hp'
    have hs : Matrix.of p.1 * Matrix.of p.2 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
      unitary_hermitian_form_mul_mem hp'.1.1 hp'.2.1
    have hJ := cayley_conj_mem_unitary_group hP (unitary_hermitian_form_mul_mem hs hx)
    show F (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹) • _ = _
    rw [hrep _ hJ, ← integral_smul_const]
    congr 1
    funext y
    exact mul_smul _ _ _
  rw [step1, ← integral_integral_swap hint]
  have hz : ∀ y, ∫ p, integrand y p ∂(μW.prod μN) = 0 := by
    intro y
    dsimp only [integrand]
    rw [integral_smul]
    have hy := unitary_matrix_mem_set ε y
    have h0 := hall _ (cayley_conj_inv_mem_hermitian_group hP hy)
    unfold aaFun sInt psiCoef at h0
    have hfun : (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
        finKer T' μ' v₁ v₂ P x (Formalism.MainNotions.S.umat y) p •
          chiInv (Formalism.MainNotions.S.psiGen k r z c) π (Matrix.of p.1) (Matrix.of p.2) ξ) =
        fun p => ⟪v₂, S7.PsiM T' μ' (P * ((P⁻¹ * Formalism.MainNotions.S.umat y * P)⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * x)) * P⁻¹) v₁⟫_ℂ •
          chiInv (Formalism.MainNotions.S.psiGen k r z c) π (Matrix.of p.1) (Matrix.of p.2) ξ := by
      funext p
      delta finKer
      rw [conj_inv_mul_conj _ _ _ hd]
    rw [hfun, h0, smul_zero]
  simp only [hz, integral_zero]

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end
end
