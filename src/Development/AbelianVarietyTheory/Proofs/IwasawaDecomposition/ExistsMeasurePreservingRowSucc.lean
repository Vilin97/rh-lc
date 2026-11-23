module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
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
public import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.Analysis.Matrix.Order
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.CovolumeBounds.LintegralProdPartialSums

section

@[expose] public section

open MeasureTheory Real Set Filter Topology
open scoped ENNReal Nat

namespace GlobalTheory.FlagVolume

theorem lintegral_radial {A : ℝ} (hA : 0 < A) (m : ℕ) :
    ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r * ((A + r ^ 2) ^ (m + 2))⁻¹) =
      ENNReal.ofReal ((2 * (m + 1) * A ^ (m + 1))⁻¹) := by
  have hd : ∀ r ∈ Ici (0 : ℝ), HasDerivAt (fun r : ℝ ↦ -(2 * (m + 1) * (A + r ^ 2) ^ (m + 1))⁻¹)
      (r * ((A + r ^ 2) ^ (m + 2))⁻¹) r := by
    intro r _
    have hp : 0 < A + r ^ 2 := by positivity
    have h1 : HasDerivAt (fun r : ℝ ↦ A + r ^ 2) (2 * r) r := by
      simpa using (hasDerivAt_pow 2 r).const_add A
    have h2 := ((h1.pow (m + 1)).const_mul (2 * ((m : ℝ) + 1))).fun_inv
      (show 2 * ((m : ℝ) + 1) * (A + r ^ 2) ^ (m + 1) ≠ 0 by positivity)
    refine h2.fun_neg.congr_deriv ?_
    simp only [Pi.pow_apply, Nat.add_sub_cancel]
    push_cast
    field_simp
    ring
  have hnn : ∀ r ∈ Ioi (0 : ℝ), 0 ≤ r * ((A + r ^ 2) ^ (m + 2))⁻¹ := fun r hr ↦ by
    have : 0 < r := hr
    positivity
  have hl : Tendsto (fun r : ℝ ↦ -(2 * (m + 1) * (A + r ^ 2) ^ (m + 1))⁻¹) atTop (𝓝 0) := by
    rw [← neg_zero]
    refine Tendsto.neg (Tendsto.inv_tendsto_atTop ?_)
    refine Tendsto.const_mul_atTop (by change (0 : ℝ) < 2 * ((m : ℝ) + 1); positivity) ?_
    exact (tendsto_pow_atTop (Nat.succ_ne_zero m)).comp
      (tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop two_ne_zero))
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_Ioi_deriv_of_nonneg' hd hnn hl)
    ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ hnn)),
    integral_Ioi_of_hasDerivAt_of_nonneg' hd hnn hl]
  simp

theorem lintegral_complex_inv_pow {A : ℝ} (hA : 0 < A) (m : ℕ) :
    ∫⁻ z : ℂ, ENNReal.ofReal (((A + ‖z‖ ^ 2) ^ (m + 2))⁻¹) =
      ENNReal.ofReal (π / (m + 1) * (A ^ (m + 1))⁻¹) := by
  rw [← Complex.lintegral_comp_polarCoord_symm, polarCoord_target]
  have h1 : ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, ENNReal.ofReal p.1 •
      ENNReal.ofReal (((A + ‖Complex.polarCoord.symm p‖ ^ 2) ^ (m + 2))⁻¹) =
      ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π,
        ENNReal.ofReal (p.1 * ((A + p.1 ^ 2) ^ (m + 2))⁻¹) * (fun _ : ℝ ↦ (1 : ℝ≥0∞)) p.2 := by
    refine setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) fun p hp ↦ ?_
    simp only [Complex.norm_polarCoord_symm, sq_abs, smul_eq_mul, mul_one]
    rw [ENNReal.ofReal_mul (le_of_lt hp.1)]
  rw [h1, Measure.volume_eq_prod, ← Measure.prod_restrict,
    lintegral_prod_mul (f := fun r : ℝ ↦ ENNReal.ofReal (r * ((A + r ^ 2) ^ (m + 2))⁻¹))
      (g := fun _ : ℝ ↦ (1 : ℝ≥0∞)) (by fun_prop) (by fun_prop), lintegral_radial hA]
  simp only [lintegral_const, one_mul, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Real.volume_Ioo]
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp
  ring

theorem lintegral_fin_succ {n : ℕ} {f : (Fin (n + 1) → ℂ) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f y = ∫⁻ z : ℂ, ∫⁻ w : Fin n → ℂ, f (Fin.cons z w) := by
  have h := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℂ) 0).symm
  rw [← h.lintegral_comp hf, Measure.volume_eq_prod, lintegral_prod
    (fun a ↦ f ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℂ) 0).symm a))
    (hf.comp h.measurable).aemeasurable]
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]

theorem lintegral_pi_inv_pow (n : ℕ) : ∀ (m : ℕ) {A : ℝ}, 0 < A →
    ∫⁻ z : Fin n → ℂ, ENNReal.ofReal (((A + ∑ k, ‖z k‖ ^ 2) ^ (m + n + 1))⁻¹) =
      ENNReal.ofReal (π ^ n * m ! / (m + n)! * (A ^ (m + 1))⁻¹) := by
  induction n with
  | zero =>
    intro m A hA
    have : (m ! : ℝ) ≠ 0 := by positivity
    simp [volume_pi, this]
  | succ n ih =>
    intro m A hA
    rw [lintegral_fin_succ (by fun_prop)]
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, ← add_assoc]
    have h : ∀ z : ℂ, ∫⁻ w : Fin n → ℂ,
        ENNReal.ofReal (((A + ‖z‖ ^ 2 + ∑ k, ‖w k‖ ^ 2) ^ (m + n + 1 + 1))⁻¹) =
        ENNReal.ofReal (π ^ n * (m + 1)! / (m + 1 + n)!) *
          ENNReal.ofReal (((A + ‖z‖ ^ 2) ^ (m + 2))⁻¹) := fun z ↦ by
      rw [← ENNReal.ofReal_mul (by positivity), ← ih (m + 1) (by positivity),
        show m + 1 + n = m + n + 1 by ring]
    simp only [h]
    rw [lintegral_const_mul _ (by fun_prop), lintegral_complex_inv_pow hA,
      ← ENNReal.ofReal_mul (by positivity), show m + 1 + n = m + n + 1 by ring,
      Nat.factorial_succ m]
    congr 1
    push_cast
    field_simp
    ring

theorem lintegral_comp_vecMul {n : Type*} [Fintype n] [DecidableEq n] (R : Matrix n n ℂ)
    (hR : R.det ≠ 0) {f : (n → ℂ) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ b, f b = ENNReal.ofReal (‖R.det‖ ^ 2) * ∫⁻ y, f (Matrix.vecMul y R) := by
  let T : (n → ℂ) →ₗ[ℝ] (n → ℂ) := (Matrix.toLin' R.transpose).restrictScalars ℝ
  have hT : LinearMap.det T = ‖R.det‖ ^ 2 := by
    rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Matrix.det_transpose,
      Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq]
  have hp : 0 < ‖R.det‖ ^ 2 := by positivity
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (n → ℂ))
    (f := T) (hT ▸ hp.ne')
  have hTm : Measurable T := T.continuous_of_finiteDimensional.measurable
  have h1 : ∫⁻ y, f (Matrix.vecMul y R) = ∫⁻ y, f (T y) := by
    simp [T, Matrix.mulVec_transpose]
  rw [h1, ← lintegral_map hf hTm, hmap, lintegral_smul_measure, hT, smul_eq_mul, ← mul_assoc,
    ← ENNReal.ofReal_mul hp.le, abs_of_pos (inv_pos.2 hp), mul_inv_cancel₀ hp.ne']
  simp

end GlobalTheory.FlagVolume
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMeasurePreservingRowSucc

section

@[expose] public section

open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open scoped ComplexOrder ENNReal Nat

namespace GlobalTheory.HuaIntegral

open GlobalTheory.FlagVolume

theorem exists_factor {q : ℕ} {A : Matrix (Fin q) (Fin q) ℂ} (hA : A.PosDef) :
    ∃ R : Matrix (Fin q) (Fin q) ℂ, R.det ≠ 0 ∧ A = Rᴴ * R := by
  open scoped MatrixOrder in
  obtain ⟨R, hR⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.1 hA.posSemidef.nonneg
  refine ⟨R, fun h0 => ?_, hR⟩
  have := hA.det_pos.ne'
  rw [hR, det_mul, h0, mul_zero] at this
  exact this rfl

theorem det_conjTranspose_mul_re {q : ℕ} (R : Matrix (Fin q) (Fin q) ℂ) : (Rᴴ * R).det.re = ‖R.det‖ ^ 2 := by
  rw [det_mul, det_conjTranspose, RCLike.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

theorem det_add_row {q : ℕ} (R : Matrix (Fin q) (Fin q) ℂ) (y : Fin q → ℂ) :
    (Rᴴ * R + vecMulVec (star (vecMul y R)) (vecMul y R)).det.re = ‖R.det‖ ^ 2 * (1 + ∑ k, ‖y k‖ ^ 2) := by
  have h : Rᴴ * R + vecMulVec (star (vecMul y R)) (vecMul y R) =
      Rᴴ * (1 + replicateCol Unit (star y) * replicateRow Unit y) * R := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, ← Matrix.mul_assoc,
      Matrix.mul_assoc _ _ R, ← replicateCol_mulVec, ← replicateRow_vecMul, ← star_vecMul, vecMulVec_eq Unit]
  have h2 : (1 + y ⬝ᵥ star y : ℂ) = ((1 + ∑ k, ‖y k‖ ^ 2 : ℝ) : ℂ) := by
    simp [dotProduct, Complex.mul_conj']
  rw [h, det_mul, det_mul, det_one_add_replicateCol_mul_replicateRow, mul_right_comm, ← det_mul, h2,
    Complex.re_mul_ofReal, det_conjTranspose_mul_re]

theorem lintegral_add_row {q : ℕ} {A : Matrix (Fin q) (Fin q) ℂ} (hA : A.PosDef) (m : ℕ) :
    ∫⁻ u : Fin q → ℂ, ENNReal.ofReal (((A + vecMulVec (star u) u).det.re ^ (m + q + 1))⁻¹) =
      ENNReal.ofReal ((A.det.re ^ (m + q))⁻¹) * ENNReal.ofReal (Real.pi ^ q * m ! / (m + q)!) := by
  obtain ⟨R, hR, rfl⟩ := exists_factor hA
  have hc : Continuous fun u : Fin q → ℂ => (Rᴴ * R + vecMulVec (star u) u).det.re := by
    refine Complex.continuous_re.comp (Continuous.matrix_det (continuous_const.add ?_))
    refine continuous_matrix fun i j => ?_
    simp only [vecMulVec_apply, Pi.star_apply]
    fun_prop
  have hp : 0 < ‖R.det‖ ^ 2 := by positivity
  rw [lintegral_comp_vecMul R hR (by exact (hc.measurable.pow_const _).inv.ennreal_ofReal), det_conjTranspose_mul_re]
  simp only [det_add_row, mul_pow, mul_inv,
    ENNReal.ofReal_mul (show 0 ≤ ((‖R.det‖ ^ 2) ^ (m + q + 1))⁻¹ by positivity)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_pi_inv_pow q m one_pos, ← mul_assoc,
    ← ENNReal.ofReal_mul hp.le]
  congr 2
  · field_simp
    ring
  · simp

def rowSucc (p q : ℕ) : (Fin p × Fin q) ⊕ Fin q → Fin (p + 1) × Fin q
  | .inl a => (a.1.castSucc, a.2)
  | .inr j => (Fin.last p, j)

theorem rowSucc_bijective (p q : ℕ) : Function.Bijective (rowSucc p q) := by
  constructor
  · rintro (⟨a, b⟩ | j) (⟨a', b'⟩ | j') hh <;>
      simp_all [rowSucc, (Fin.castSucc_ne_last _).symm]
  · rintro ⟨a, b⟩
    induction a using Fin.lastCases with
    | last => exact ⟨.inr b, rfl⟩
    | cast a => exact ⟨.inl (a, b), rfl⟩

theorem exists_measurePreserving_rowSucc (p q : ℕ) :
    ∃ Φ : (Fin p × Fin q → ℂ) × (Fin q → ℂ) → (Fin (p + 1) × Fin q → ℂ),
      MeasurePreserving Φ ∧ ∀ v u, (∀ a b, Φ (v, u) (a.castSucc, b) = v (a, b)) ∧
        ∀ j, Φ (v, u) (Fin.last p, j) = u j := by
  let e := Equiv.ofBijective _ (rowSucc_bijective p q)
  refine ⟨_, (volume_measurePreserving_piCongrLeft (fun _ ↦ ℂ) e).comp
    (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ ↦ ℂ)), fun u b ↦
    ⟨fun a c ↦ ?_, fun j ↦ ?_⟩⟩
  · exact MeasurableEquiv.piCongrLeft_apply_apply e _ (.inl (a, c))
  · exact MeasurableEquiv.piCongrLeft_apply_apply e _ (.inr j)

theorem lintegral_det_inv_pow (m q p : ℕ) :
    ∫⁻ v : Fin p × Fin q → ℂ, ENNReal.ofReal
        (((1 + (Matrix.of fun a b => v (a, b))ᴴ * (Matrix.of fun a b => v (a, b))).det.re ^ (m + p + q))⁻¹) =
      ENNReal.ofReal (∏ i ∈ Finset.range p, (Real.pi ^ q * (m + i)! / (m + i + q)!)) := by
  have hm : ∀ p s : ℕ, Measurable fun v : Fin p × Fin q → ℂ => ENNReal.ofReal
      (((1 + (Matrix.of fun a b => v (a, b))ᴴ * (Matrix.of fun a b => v (a, b))).det.re ^ s)⁻¹) := by
    intro p s
    have hc : Continuous fun v : Fin p × Fin q → ℂ => (Matrix.of fun a b => v (a, b)) :=
      continuous_matrix fun i j => by simp only [of_apply]; fun_prop
    exact ((Complex.continuous_re.comp
      (continuous_const.add (hc.matrix_conjTranspose.matrix_mul hc)).matrix_det).measurable.pow_const
        s).inv.ennreal_ofReal
  induction p with
  | zero => simp [volume_pi]
  | succ p ih =>
    obtain ⟨Φ, hΦ, hΦ'⟩ := exists_measurePreserving_rowSucc p q
    rw [← hΦ.lintegral_comp (hm _ _), Measure.volume_eq_prod,
      lintegral_prod _ (by exact ((hm _ _).comp hΦ.measurable).aemeasurable)]
    have h : ∀ (v : Fin p × Fin q → ℂ) (u : Fin q → ℂ),
        1 + (Matrix.of fun a b => Φ (v, u) (a, b))ᴴ * (Matrix.of fun a b => Φ (v, u) (a, b)) =
        (1 + (Matrix.of fun a b => v (a, b))ᴴ * (Matrix.of fun a b => v (a, b))) + vecMulVec (star u) u := by
      intro v u
      rw [add_assoc]
      congr 1
      ext i j
      simp [Matrix.mul_apply, Fin.sum_univ_castSucc, (hΦ' v u).1, (hΦ' v u).2, vecMulVec_apply]
    have hpos : ∀ v : Fin p × Fin q → ℂ,
        (1 + (Matrix.of fun a b => v (a, b))ᴴ * (Matrix.of fun a b => v (a, b))).PosDef := fun v =>
      PosDef.one.add_posSemidef (posSemidef_conjTranspose_mul_self _)
    simp only [h, show m + (p + 1) + q = (m + p) + q + 1 by ring, lintegral_add_row (hpos _)]
    rw [lintegral_mul_const _ (hm _ _), ih, Finset.prod_range_succ, ENNReal.ofReal_mul (by positivity)]

theorem dual_mass : ∀ p q : ℕ, ∫⁻ v : Fin p × Fin q → ℂ, ENNReal.ofReal ((1 + (Matrix.of fun a b => v (a, b))ᴴ * (Matrix.of fun a b => v (a, b))).det.re ^ (-((p + q : ℕ) : ℤ))) = ENNReal.ofReal (grassConst p q)⁻¹ := by
  intro p q
  have h := lintegral_det_inv_pow 0 q p
  simp only [zero_add] at h
  simp only [_root_.zpow_neg, _root_.zpow_natCast]
  rw [h, grassConst, inv_div, div_eq_mul_inv, ← Finset.prod_inv_distrib, mul_comm p q, pow_mul,
    ← Finset.card_range p, ← Finset.prod_const, Finset.card_range, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [inv_div, add_comm q i, mul_div_assoc]

end GlobalTheory.HuaIntegral
end
end
