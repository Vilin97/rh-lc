module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocInOfUniqOfDecLow
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselOpNormPowerIntegralLtTopClosedSubgroupStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselModelUnitaryGroupOpNormPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselZhatInvAndRegularIffStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsometryOpNormBoundedByTwoFramesStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SiegelRegionNormBound
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
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupsClosedUnitaryWCompactStatement
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.SiegelRegionNormBoundStatement

section

@[expose] public section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.siegel_region_norm_bound : ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (C : Set (Mat k r)), inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → IsCompact C → C ⊆ Greg k r z z' → ∃ C0 : ℝ, ∀ γ ∈ C, ∀ s ∈ Sset k r z, ∀ s' ∈ Sset k r z', ∀ b : Fin (r + 1), eucl (s *ᵥ fvec k r z b) ≤ C0 * opn (s * γ * s'⁻¹) ^ (r * (r + 1)) ∧ eucl (s' *ᵥ fvec k r z' b) ≤ C0 * opn (s * γ * s'⁻¹) ^ (r * (r + 1)) := by
  first | exact @GlobalTheory.SgInf.frame_image_bound | exact GlobalTheory.SgInf.frame_image_bound | (intros; apply GlobalTheory.SgInf.frame_image_bound <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselRegularDoubleCosetPolynomialProperness

section

@[expose] public section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.PolyProper

variable {k r : ℕ}

theorem gram_det_unit : IsUnit (Hpk k r).det :=
  Matrix.isUnit_det_of_right_inverse (hermitian_pos_facts_hold k r).2.1

theorem mul_mem {g h : Mat k r} (hg : g ∈ GG k r) (hh : h ∈ GG k r) : g * h ∈ GG k r :=
  (unitary_group_holds _ _ gram_det_unit).2.1 g hg h hh

theorem inv_mem {g : Mat k r} (hg : g ∈ GG k r) : g⁻¹ ∈ GG k r :=
  ((unitary_group_holds _ _ gram_det_unit).2.2 g hg).2

theorem det_unit {g : Mat k r} (hg : g ∈ GG k r) : IsUnit g.det :=
  ((unitary_group_holds _ _ gram_det_unit).2.2 g hg).1

theorem mem_of_S {z : Fin (2 * r + k + 1) → ℂ} {s : Mat k r} (hs : s ∈ Sset k r z) : s ∈ GG k r := by
  obtain ⟨h, hh, m, hm, rfl⟩ := hs
  exact mul_mem hh.1 hm.1

theorem inv_eq {g : Mat k r} (hg : g ∈ GG k r) : g⁻¹ = Hpk k r * gᴴ * Hpk k r := by
  apply Matrix.inv_eq_left_inv
  have h : gᴴ * Hpk k r * g = Hpk k r := hg
  rw [Matrix.mul_assoc (Hpk k r), Matrix.mul_assoc (Hpk k r), h]
  exact (hermitian_pos_facts_hold k r).2.1

theorem left_bound (z z' : Fin (2 * r + k + 1) → ℂ) (C : Set (Mat k r)) (hz : inWb k r z)
    (hz' : inWb k r z') (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z') (hC : IsCompact C)
    (hCr : C ⊆ Greg k r z z') :
    ∃ C0 : ℝ, ∀ γ ∈ C, ∀ s ∈ Sset k r z, ∀ s' ∈ Sset k r z',
      opn s ≤ C0 * opn (s * γ * s'⁻¹) ^ (2 * (r ^ 2 + r + 1)) := by
  obtain ⟨C1, h1⟩ := GlobalTheory.T.siegel_region_norm_bound k r z z' C hz hz' hT hT' hC hCr
  obtain ⟨C2, h2⟩ := GlobalTheory.T.isometry_opNorm_bounded_by_two_frames k r z z' C hz hz' hT hT' hC
    (fun γ hγ => ⟨(hCr hγ).1, (hCr hγ).2.2⟩)
  obtain ⟨hN1, -, -, -, hN5, -⟩ := GlobalTheory.T.besselModelUnitaryGroup_opNorm_properties k r
  refine ⟨C2 * (max 1 C1) ^ 2, fun γ hγ s hs s' hs' => ?_⟩
  have hsG := mem_of_S hs
  have hs'G := mem_of_S hs'
  have hγG : γ ∈ GG k r := (hCr hγ).1
  have hxG : s * γ * s'⁻¹ ∈ GG k r := mul_mem (mul_mem hsG hγG) (inv_mem hs'G)
  have hx1 : 1 ≤ opn (s * γ * s'⁻¹) := (hN1 _ hxG).2
  have hxs : (s * γ * s'⁻¹) * s' = s * γ := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (det_unit hs'G), Matrix.mul_one]
  have h1' := h1 γ hγ s hs s' hs'
  have h5 := hN5 (s * γ * s'⁻¹)
  set X := opn (s * γ * s'⁻¹) with hX
  have hp1 : 1 ≤ X ^ (r * (r + 1)) := one_le_pow₀ hx1
  have hm1 : (1 : ℝ) ≤ max 1 C1 := le_max_left _ _
  have hle : C1 * X ^ (r * (r + 1)) ≤ max 1 C1 * X ^ (r * (r + 1)) :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  have hQ1 : 1 ≤ max 1 C1 * X ^ (r * (r + 1)) := one_le_mul_of_one_le_of_one_le hm1 hp1
  have hB : 1 ≤ X * (max 1 C1 * X ^ (r * (r + 1))) := one_le_mul_of_one_le_of_one_le hx1 hQ1
  have key := h2 γ hγ s hsG (X * (max 1 C1 * X ^ (r * (r + 1)))) hB (by
    rintro (a | b)
    · show eucl (s *ᵥ fvec k r z a) ≤ _
      refine ((h1' a).1.trans hle).trans ?_
      exact le_mul_of_one_le_left (by linarith) hx1
    · show eucl (s *ᵥ (γ *ᵥ fvec k r z' b)) ≤ _
      rw [Matrix.mulVec_mulVec, ← hxs, ← Matrix.mulVec_mulVec]
      refine (h5 _).trans ?_
      exact mul_le_mul_of_nonneg_left ((h1' b).2.trans hle) (by linarith))
  refine key.trans (le_of_eq ?_)
  ring

theorem poly_proper : ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (C : Set (Mat k r)), inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → IsCompact C → C ⊆ Greg k r z z' → ∃ C0 : ℝ, 1 ≤ C0 ∧ ∀ γ ∈ C, ∀ s ∈ Sset k r z, ∀ s' ∈ Sset k r z', max (opn s) (opn s') ≤ C0 * opn (s * γ * s'⁻¹) ^ (2 * (r ^ 2 + r + 1)) := by
  intro k r z z' C hz hz' hT hT' hC hCr
  obtain ⟨C1, h1⟩ := left_bound z z' C hz hz' hT hT' hC hCr
  have hcont : Continuous fun g : Mat k r => Hpk k r * gᴴ * Hpk k r :=
    (continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const
  have hCr' : (fun g : Mat k r => Hpk k r * gᴴ * Hpk k r) '' C ⊆ Greg k r z' z := by
    rintro _ ⟨γ, hγ, rfl⟩
    have hγG : γ ∈ GG k r := (hCr hγ).1
    show Hpk k r * γᴴ * Hpk k r ∈ _
    rw [← inv_eq hγG]
    exact (GlobalTheory.T.besselZhat_inv_and_regular_iff k r z z' γ hγG).2.1 (hCr hγ)
  obtain ⟨C2, h2⟩ := left_bound z' z _ hz' hz hT' hT (hC.image hcont) hCr'
  obtain ⟨hN1, -⟩ := GlobalTheory.T.besselModelUnitaryGroup_opNorm_properties k r
  refine ⟨max 1 (max C1 C2), le_max_left _ _, fun γ hγ s hs s' hs' => ?_⟩
  have hsG := mem_of_S hs
  have hs'G := mem_of_S hs'
  have hγG : γ ∈ GG k r := (hCr hγ).1
  have hxG : s * γ * s'⁻¹ ∈ GG k r := mul_mem (mul_mem hsG hγG) (inv_mem hs'G)
  have hinv : s' * γ⁻¹ * s⁻¹ = (s * γ * s'⁻¹)⁻¹ := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (det_unit hs'G),
      Matrix.mul_assoc]
  have ha := h1 γ hγ s hs s' hs'
  have hb := h2 γ⁻¹ ⟨γ, hγ, (inv_eq hγG).symm⟩ s' hs' s hs
  rw [hinv, (hN1 _ hxG).1] at hb
  have hp : 0 ≤ opn (s * γ * s'⁻¹) ^ (2 * (r ^ 2 + r + 1)) := pow_nonneg (opn_nonneg _) _
  refine max_le (ha.trans ?_) (hb.trans ?_)
  · exact mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _)) hp
  · exact mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_right _ _)) hp

end GlobalTheory.SgInf.PolyProper
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselRegularDoubleCosetPolynomialPropernessStatement

section

@[expose] public section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.besselRegularDoubleCoset_polynomial_properness : ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (C : Set (Mat k r)), inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → IsCompact C → C ⊆ Greg k r z z' → ∃ C0 : ℝ, 1 ≤ C0 ∧ ∀ γ ∈ C, ∀ s ∈ Sset k r z, ∀ s' ∈ Sset k r z', max (opn s) (opn s') ≤ C0 * opn (s * γ * s'⁻¹) ^ (2 * (r ^ 2 + r + 1)) := by
  first | exact @GlobalTheory.SgInf.PolyProper.poly_proper | exact GlobalTheory.SgInf.PolyProper.poly_proper | (intros; apply GlobalTheory.SgInf.PolyProper.poly_proper <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselOrbitOpNormIntegralFiniteOnCompactRegular

section

@[expose] public section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.OrbNorm

theorem continuous_opn {n : ℕ} : Continuous (opn : Matrix (Fin n) (Fin n) ℂ → ℝ) := by
  unfold opn
  have h : Continuous (fun g : Matrix (Fin n) (Fin n) ℂ => Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) g) :=
    LinearMap.continuous_of_finiteDimensional
      ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).toAlgEquiv.toLinearEquiv.toLinearMap)
  exact continuous_norm.comp h

theorem opn_pos {k r : ℕ} {g : Mat k r} (hg : g ∈ GG k r) : 0 < opn g := by
  apply GlobalTheory.Amp.LocalInputs.opn_pos <;> assumption

theorem integrable_of_normInt {k r : ℕ} {μ : Measure (Mt k r)} {A : ℝ} (h : normInt μ A < ⊤) :
    Integrable (fun x : Mt k r => opn (Matrix.of x) ^ (-A)) μ := by
  have hm : Measurable (fun x : Mt k r => opn (Matrix.of x) ^ (-A)) :=
    ((continuous_opn.comp (continuous_id : Continuous (fun x : Mt k r => (Matrix.of x : Mat k r)))).measurable).pow_const _
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (opn_nonneg _) _)]
  exact h

theorem rpow_le {a a' x C0 A : ℝ} {M : ℕ} (ha : 0 < a) (ha' : 0 < a') (hx : 0 ≤ x) (hC : 0 < C0)
    (hA : 0 ≤ A) (h : max a a' ≤ C0 * x ^ M) :
    x ^ (-(2 * M * A)) ≤ C0 ^ (2 * A) * (a ^ (-A) * a' ^ (-A)) := by
  have hy : 0 < x ^ M := by
    have h1 : 0 < max a a' := lt_max_of_lt_left ha
    exact pos_of_mul_pos_right (lt_of_lt_of_le h1 h) hC.le
  have hCy : 0 < C0 * x ^ M := mul_pos hC hy
  have hx' : x ^ (-(2 * M * A)) = (x ^ M) ^ (-(2 * A)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
    congr 1
    ring
  have h1 : (C0 * x ^ M) ^ (-A) ≤ a ^ (-A) :=
    Real.rpow_le_rpow_of_nonpos ha (le_trans (le_max_left _ _) h) (by linarith)
  have h2 : (C0 * x ^ M) ^ (-A) ≤ a' ^ (-A) :=
    Real.rpow_le_rpow_of_nonpos ha' (le_trans (le_max_right _ _) h) (by linarith)
  have key : C0 ^ (2 * A) * ((C0 * x ^ M) ^ (-A) * (C0 * x ^ M) ^ (-A)) = (x ^ M) ^ (-(2 * A)) := by
    rw [← Real.rpow_add hCy, Real.mul_rpow hC.le hy.le, ← mul_assoc, ← Real.rpow_add hC]
    have e1 : 2 * A + (-A + -A) = 0 := by ring
    have e2 : -A + -A = -(2 * A) := by ring
    rw [e1, e2, Real.rpow_zero, one_mul]
  rw [hx', ← key]
  exact mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (Real.rpow_nonneg hCy.le _) (Real.rpow_nonneg ha.le _))
    (Real.rpow_nonneg hC.le _)

theorem orbNormInt_lt_top : ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μS μS' : Measure (Mt k r)) (b : ℝ) (C : Set (Mat k r)), inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → IsHaarOn (Sset k r z) μS → IsHaarOn (Sset k r z') μS' → 2 * ((2 * (r ^ 2 + r + 1) : ℕ) : ℝ) * (2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2) < b → IsCompact C → C ⊆ Greg k r z z' → (∀ γ ∈ C, orbNormInt μS μS' b γ < ⊤) ∧ ∃ F : Mt k r × Mt k r → ℝ, Integrable F (μS.prod μS') ∧ ∀ γ ∈ C, ∀ p : Mt k r × Mt k r, Matrix.of p.1 ∈ Sset k r z → Matrix.of p.2 ∈ Sset k r z' → opn (Matrix.of (act2 γ p)) ^ (-b) ≤ F p := by
  intro k r z z' μS μS' b C hz hz' hT hT' hS hS' hb hC hCr
  obtain ⟨C0, hC0, hbd⟩ := GlobalTheory.T.besselRegularDoubleCoset_polynomial_properness k r z z' C hz hz' hT hT' hC hCr
  obtain ⟨-, -, -, hSS, -⟩ := GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z hz hT
  obtain ⟨-, -, -, hSS', -⟩ := GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z' hz' hT'
  set M : ℕ := 2 * (r ^ 2 + r + 1) with hM
  have hM0 : 0 < M := by rw [hM]; positivity
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM0
  have hMpos : (0 : ℝ) < 2 * (M : ℝ) := by linarith
  set A : ℝ := b / (2 * (M : ℝ)) with hA
  have hA2 : 2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 < A := by
    rw [hA, lt_div_iff₀ hMpos]
    linarith
  have hA0 : 0 ≤ A := le_of_lt (lt_of_le_of_lt (by positivity) hA2)
  have hbA : b = 2 * (M : ℝ) * A := by
    rw [hA]
    field_simp
  have hi := integrable_of_normInt (GlobalTheory.T.besselOpNormPowerIntegral_lt_top_closedSubgroup k r (Sset k r z) μS A hSS hS hA2)
  have hi' := integrable_of_normInt (GlobalTheory.T.besselOpNormPowerIntegral_lt_top_closedSubgroup k r (Sset k r z') μS' A hSS' hS' hA2)
  have : SigmaFinite μS := hS.1
  have : SigmaFinite μS' := hS'.1
  let F : Mt k r × Mt k r → ℝ := fun p =>
    C0 ^ (2 * A) * (opn (Matrix.of p.1) ^ (-A) * opn (Matrix.of p.2) ^ (-A))
  have hF : Integrable F (μS.prod μS') := (hi.mul_prod hi').const_mul _
  have hbound : ∀ γ ∈ C, ∀ p : Mt k r × Mt k r, Matrix.of p.1 ∈ Sset k r z → Matrix.of p.2 ∈ Sset k r z' →
      opn (Matrix.of (act2 γ p)) ^ (-b) ≤ F p := by
    intro γ hγ p h1 h2
    have hg1 := opn_pos (hSS.1 h1)
    have hg2 := opn_pos (hSS'.1 h2)
    have hmax := hbd γ hγ _ h1 _ h2
    rw [hbA]
    exact rpow_le hg1 hg2 (opn_nonneg _) (by linarith) hA0 hmax
  refine ⟨fun γ hγ => ?_, F, hF, hbound⟩
  have e1 : ∀ᵐ p ∂(μS.prod μS'), Matrix.of p.1 ∈ Sset k r z := by
    rw [ae_iff]
    refine measure_mono_null (t := {x : Mt k r | Matrix.of x ∉ Sset k r z} ×ˢ Set.univ)
      (fun p hp => ⟨hp, trivial⟩) ?_
    rw [Measure.prod_prod, hS.2.2.1, zero_mul]
  have e2 : ∀ᵐ p ∂(μS.prod μS'), Matrix.of p.2 ∈ Sset k r z' := by
    rw [ae_iff]
    refine measure_mono_null (t := Set.univ ×ˢ {x : Mt k r | Matrix.of x ∉ Sset k r z'})
      (fun p hp => ⟨trivial, hp⟩) ?_
    rw [Measure.prod_prod, hS'.2.2.1, mul_zero]
  calc orbNormInt μS μS' b γ ≤ ∫⁻ p, ENNReal.ofReal (F p) ∂(μS.prod μS') := by
        unfold orbNormInt
        apply lintegral_mono_ae
        filter_upwards [e1, e2] with p h1 h2
        exact ENNReal.ofReal_le_ofReal (hbound γ hγ p h1 h2)
    _ < ⊤ := hF.lintegral_lt_top

end GlobalTheory.SgInf.OrbNorm
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselOrbitOpNormIntegralFiniteOnCompactRegularStatement

section

@[expose] public section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.besselOrbitOpNormIntegral_finite_on_compact_regular : ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μS μS' : Measure (Mt k r)) (b : ℝ) (C : Set (Mat k r)), inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → IsHaarOn (Sset k r z) μS → IsHaarOn (Sset k r z') μS' → 2 * ((2 * (r ^ 2 + r + 1) : ℕ) : ℝ) * (2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2) < b → IsCompact C → C ⊆ Greg k r z z' → (∀ γ ∈ C, orbNormInt μS μS' b γ < ⊤) ∧ ∃ F : Mt k r × Mt k r → ℝ, Integrable F (μS.prod μS') ∧ ∀ γ ∈ C, ∀ p : Mt k r × Mt k r, Matrix.of p.1 ∈ Sset k r z → Matrix.of p.2 ∈ Sset k r z' → opn (Matrix.of (act2 γ p)) ^ (-b) ≤ F p := by
  first | exact @GlobalTheory.SgInf.OrbNorm.orbNormInt_lt_top | exact GlobalTheory.SgInf.OrbNorm.orbNormInt_lt_top | (intros; apply GlobalTheory.SgInf.OrbNorm.orbNormInt_lt_top <;> assumption)
end
end
