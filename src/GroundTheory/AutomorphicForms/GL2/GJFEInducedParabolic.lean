module

public import GroundTheory.AutomorphicForms.GL2.GJFEInducedTensor
public import GroundTheory.AutomorphicForms.GL2.GJFEInducedChar
public import GroundTheory.AutomorphicForms.GL2.GJInducedZeta
import GroundTheory.AutomorphicForms.GL2.ExistsEqPowMulOfValuationLe
public import GroundTheory.AutomorphicForms.MeasuresChart
public import Mathlib.Analysis.CStarAlgebra.Classes
import GroundTheory.AutomorphicForms.LocallyProfinite
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Algebra.Order.Star.Real
import Mathlib.CategoryTheory.Countable
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: GroundTheory.AutomorphicForms.GL2.GJFEInducedInv

section

@[expose] public section

noncomputable section

namespace GroundTheory.Automorphic

namespace Measures

namespace LinearChart

open MeasureTheory Measure Set
open scoped NNReal ENNReal Pointwise

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F] {ι : Type*} [Fintype ι]
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  (C : LinearChart F ι G) (μ₀ : Measure (ι → F)) [μ₀.IsAddHaarMeasure]

theorem map_mul_right_haar_modular (h : G) :
    map (· * h) (C.haar μ₀) = modularCharacter h • C.haar μ₀ := by
  rw [C.map_mul_right_haar μ₀ h, C.modularCharacter_eq h]


include C in
theorem continuous_modularCharacter : Continuous (modularCharacter : G → ℝ≥0) := by
  have : (modularCharacter : G → ℝ≥0) = fun g => C.leftModulus g * (C.rightModulus g)⁻¹ := by
    funext g
    rw [C.modularCharacter_eq, div_eq_mul_inv]
  rw [this]
  exact C.continuous_leftModulus.mul
    (C.continuous_rightModulus.inv₀ fun g => (C.rightModulus_pos g).ne')

include C in
theorem measurable_modularCharacter :
    Measurable fun g : G => ((modularCharacter g : ℝ≥0) : ℝ≥0∞) :=
  (ENNReal.continuous_coe.comp (continuous_modularCharacter C)).measurable

theorem lintegral_mul_right_haar (h : G) {f : G → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f (x * h) ∂C.haar μ₀ = modularCharacter h * ∫⁻ x, f x ∂C.haar μ₀ := by
  rw [← lintegral_map hf (measurable_mul_const h), C.map_mul_right_haar_modular,
    lintegral_smul_measure]
  rfl


include C in
theorem modularCharacter_eq_one_of_mem {V : OpenSubgroup G} (hV : IsCompact (V : Set G)) {v : G}
    (hv : v ∈ V) : modularCharacter v = 1 := by
  obtain ⟨h1, h2⟩ := C.modulus_eq_one_of_mem hV hv
  rw [C.modularCharacter_eq, h1, h2, div_one]

variable [SecondCountableTopology G]

theorem map_inv_withDensity_haar :
    map (·⁻¹) ((C.haar μ₀).withDensity fun x => (modularCharacter x : ℝ≥0∞)) = C.haar μ₀ := by
  set μ := C.haar μ₀ with hμ
  set Δ : G → ℝ≥0∞ := fun x => (modularCharacter x : ℝ≥0∞) with hΔ
  have hΔm : Measurable Δ := (measurable_modularCharacter C)
  set ν := map (·⁻¹) (μ.withDensity Δ) with hνdef
  have hν : ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂ν = ∫⁻ x, f x⁻¹ * Δ x ∂μ := by
    intro f hf
    rw [hνdef, lintegral_map hf measurable_inv]
    have := lintegral_withDensity_eq_lintegral_mul μ hΔm (hf.comp measurable_inv)
    simp only [Function.comp_def, Pi.mul_apply] at this
    rw [this]
    congr 1
    funext x
    ring

  have hleft : ∀ g : G, ∀ f : G → ℝ≥0∞, Measurable f →
      ∫⁻ x, f (g * x) ∂ν = ∫⁻ x, f x ∂ν := by
    intro g f hf
    rw [hν (fun x => f (g * x)) (hf.comp (measurable_const_mul g)), hν f hf]
    set L : G → ℝ≥0∞ := fun y => f y⁻¹ * Δ y with hLdef
    have hL : Measurable L := (hf.comp measurable_inv).mul hΔm
    have key : (fun x => f (g * x⁻¹) * Δ x) =
        fun x => (modularCharacter g : ℝ≥0∞) * L (x * g⁻¹) := by
      funext x
      have h1 : (x * g⁻¹)⁻¹ = g * x⁻¹ := by group
      have h2 : Δ x = (modularCharacter (x * g⁻¹) : ℝ≥0∞) * modularCharacter g := by
        rw [hΔ, ← ENNReal.coe_mul, ← map_mul, inv_mul_cancel_right]
      simp only [hLdef, h1, h2]
      ring
    show ∫⁻ x, f (g * x⁻¹) * Δ x ∂μ = ∫⁻ x, L x ∂μ
    rw [key, lintegral_const_mul (f := fun x => L (x * g⁻¹)) _ (hL.comp (measurable_mul_const _)),
      C.lintegral_mul_right_haar μ₀ g⁻¹ hL, ← mul_assoc, ← ENNReal.coe_mul, ← map_mul,
      mul_inv_cancel, map_one, ENNReal.coe_one, one_mul]
  have hinv : ν.IsMulLeftInvariant := ⟨fun g => by
    ext s hs
    rw [map_apply (measurable_const_mul g) hs, ← lintegral_indicator_one hs,
      ← lintegral_indicator_one (measurable_const_mul g hs)]
    exact hleft g (s.indicator 1) (measurable_one.indicator hs)⟩
  have hfin : IsFiniteMeasureOnCompacts ν := ⟨fun K hK => by
    rw [hνdef, map_apply measurable_inv hK.isClosed.measurableSet,
      withDensity_apply _ (measurable_inv hK.isClosed.measurableSet)]
    have hK' : IsCompact ((·⁻¹) ⁻¹' K : Set G) := by
      rw [Set.inv_preimage]
      exact hK.inv
    exact setLIntegral_lt_top_of_isCompact (hK'.measure_lt_top).ne hK'
      (continuous_modularCharacter C)⟩
  have hsmul := isMulLeftInvariant_eq_smul ν μ
  obtain ⟨V, hV⟩ := exists_compactOpenSubgroup (G := G)
  have hVm : MeasurableSet (V : Set G) := V.isOpen.measurableSet
  have hVinv : ((·⁻¹) ⁻¹' (V : Set G) : Set G) = V := by
    ext x
    simp
  have hνV : ν V = μ V := by
    rw [hνdef, map_apply measurable_inv hVm, withDensity_apply _ (measurable_inv hVm), hVinv]
    rw [setLIntegral_congr_fun hVm (g := fun _ => (1 : ℝ≥0∞)) fun x hx => by
      simp [hΔ, modularCharacter_eq_one_of_mem C hV hx]]
    simp
  have hμV0 : μ V ≠ 0 := V.isOpen.measure_ne_zero μ ⟨1, V.one_mem⟩
  have hμVt : μ V ≠ ∞ := hV.measure_lt_top.ne
  have hc : haarScalarFactor ν μ = 1 := by
    have := congrArg (fun m : Measure G => m V) hsmul
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at this
    rw [hνV] at this
    have h1 : (haarScalarFactor ν μ : ℝ≥0∞) * μ V = 1 * μ V := by rw [one_mul, ← this]
    exact_mod_cast (ENNReal.mul_left_inj hμV0 hμVt).1 h1
  rw [hsmul, hc, one_smul]

theorem lintegral_inv_haar {f : G → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x⁻¹ ∂C.haar μ₀ = ∫⁻ x, (modularCharacter x : ℝ≥0∞) * f x ∂C.haar μ₀ := by
  conv_lhs => rw [← C.map_inv_withDensity_haar μ₀]
  have h1 := lintegral_map (μ := (C.haar μ₀).withDensity fun x => (modularCharacter x : ℝ≥0∞))
    (f := fun x => f x⁻¹) (hf.comp measurable_inv) measurable_inv
  have h2 := lintegral_withDensity_eq_lintegral_mul (C.haar μ₀) (measurable_modularCharacter C) hf
  simp only [inv_inv] at h1
  rw [h1, h2]
  rfl

theorem integral_inv_haar {f : G → ℂ} (hf : Continuous f) :
    ∫ x, f x⁻¹ ∂C.haar μ₀ = ∫ x, (modularCharacter x : ℂ) * f x ∂C.haar μ₀ := by
  conv_lhs => rw [← C.map_inv_withDensity_haar μ₀]
  have h1 := integral_map (μ := (C.haar μ₀).withDensity fun x => (modularCharacter x : ℝ≥0∞))
    (φ := fun x : G => x⁻¹) (f := fun x => f x⁻¹) measurable_inv.aemeasurable
    (hf.comp continuous_inv).aestronglyMeasurable
  simp only [inv_inv] at h1
  rw [h1, integral_withDensity_eq_integral_smul (continuous_modularCharacter C).measurable]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [NNReal.smul_def, Complex.real_smul]

end LinearChart

end Measures

end GroundTheory.Automorphic
end
end
end

-- Source module: GroundTheory.AutomorphicForms.GL2.GJFEInducedParabolic

section

@[expose] public section

noncomputable section

namespace GroundTheory.Automorphic

namespace GodementJacquet

open Matrix GLnLocal Parabolic Iwasawa Measures MeasureTheory GJMatrix
open scoped NNReal ENNReal Pointwise

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F] {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
  {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (levi F n β) W}


variable (β) in
def leviCoordMeasure (ψ : AddChar F Circle) : Measure (LeviIndex n β → F) :=
  Measure.pi fun _ => LocalField.selfDualMeasure ψ

instance (ψ : AddChar F Circle) : (leviCoordMeasure β ψ).IsAddHaarMeasure := by
  unfold leviCoordMeasure
  infer_instance


variable (β) in
def leviAbsDetShift : levi F n β →* ℝ≥0 where
  toFun m := leviAbsDet β m ^ (((n : ℝ) - 1) / 2)
  map_one' := by simp
  map_mul' m m' := by simp [NNReal.mul_rpow]


variable (β) in
def inducedChar : levi F n β →* ℝ≥0 :=
  leviRatio β * leviSqrtModular β * leviAbsDetShift β

omit [MeasurableSpace F] [BorelSpace F] in
theorem detPow_eq_cpow (g : GL (Fin n) F) (s : ℂ) :
    detPow g s = ((LocalField.modulus ((g : Matrix (Fin n) (Fin n) F).det) : ℝ) : ℂ) ^ s := rfl

omit [MeasurableSpace F] [BorelSpace F] in
theorem modulus_det_pos (g : GL (Fin n) F) :
    0 < LocalField.modulus ((g : Matrix (Fin n) (Fin n) F).det) :=
  LocalField.modulus_pos (det_ne_zero g)


omit [MeasurableSpace F] [BorelSpace F] in
theorem detPow_add_shift (m : levi F n β) (s : ℂ) :
    detPow (m : GL (Fin n) F) (s + ((n : ℂ) - 1) / 2) =
      detPow (m : GL (Fin n) F) s * ((leviAbsDetShift β m : ℝ≥0) : ℂ) := by
  have hx := modulus_det_pos (m : GL (Fin n) F)
  rw [detPow_eq_cpow, detPow_eq_cpow, Complex.cpow_add _ _ (by exact_mod_cast hx.ne')]
  congr 1
  rw [leviAbsDetShift, MonoidHom.coe_mk, OneHom.coe_mk, leviAbsDet_apply, NNReal.coe_rpow,
    Complex.ofReal_cpow (NNReal.coe_nonneg _)]
  push_cast
  rfl


omit [MeasurableSpace F] [BorelSpace F] in
theorem leviIntegrand_shift (Ψ : Matrix (Fin n) (Fin n) F → ℂ) (w : W) (ℓ : Module.Dual ℂ W)
    (s : ℂ) (m : levi F n β) :
    leviIntegrand σ (leviRatio β * leviSqrtModular β) Ψ w ℓ (s + ((n : ℂ) - 1) / 2) m =
      leviIntegrand σ (inducedChar β) Ψ w ℓ s m := by
  simp only [leviIntegrand, inducedChar, MonoidHom.mul_apply, detPow_add_shift]
  push_cast
  ring


omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
  [BorelSpace F] in
theorem monoidHom_ne_zero {G : Type*} [Group G] (χ : G →* ℝ≥0) (g : G) : χ g ≠ 0 :=
  left_ne_zero_of_mul_eq_one (map_mul_eq_one χ (mul_inv_cancel g))

theorem weightB_eq (m : levi F n β) (s : ℂ) :
    ((leviRatio β m * leviSqrtModular β m : ℝ≥0) : ℂ) *
        detPow (m : GL (Fin n) F) (1 - s + ((n : ℂ) - 1) / 2) =
      (((inducedChar β m)⁻¹ * leviModulus β m : ℝ≥0) : ℂ) * detPow (m : GL (Fin n) F) (-s) := by
  set x : ℝ≥0 := leviAbsDet β m with hxdef
  have hx : x ≠ 0 := (modulus_det_pos (m : GL (Fin n) F)).ne'
  set c : ℝ := ((n : ℝ) - 1) / 2 with hc
  have hsplit : detPow (m : GL (Fin n) F) (1 - s + ((n : ℂ) - 1) / 2) =
      ((x ^ (1 + c) : ℝ≥0) : ℂ) * detPow (m : GL (Fin n) F) (-s) := by
    have hx' : ((x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hx
    rw [detPow_eq_cpow, detPow_eq_cpow]
    show ((x : ℝ) : ℂ) ^ (1 - s + ((n : ℂ) - 1) / 2) = ((x ^ (1 + c) : ℝ≥0) : ℂ) * ((x : ℝ) : ℂ) ^ (-s)
    rw [show (1 - s + ((n : ℂ) - 1) / 2) = ((1 + c : ℝ) : ℂ) + (-s) by rw [hc]; push_cast; ring,
      Complex.cpow_add _ _ hx', NNReal.coe_rpow, Complex.ofReal_cpow (NNReal.coe_nonneg _)]
  have hid : leviRatio β m ^ 2 * Measure.modularCharacter (leviIncl m) * x ^ n = leviModulus β m :=
    leviRatio_sq_mul_modular_mul_det (F := F) m
  have hsq : leviSqrtModular β m * leviSqrtModular β m =
      Measure.modularCharacter (leviIncl m) := by
    simp [leviSqrtModular, NNReal.mul_self_sqrt]
  have hpow : x ^ c * x ^ (1 + c) = x ^ n := by
    rw [← NNReal.rpow_add hx, show c + (1 + c) = (n : ℝ) by rw [hc]; ring, NNReal.rpow_natCast]
  have hκ : inducedChar β m = leviRatio β m * leviSqrtModular β m * x ^ c := rfl
  have hκ0 : inducedChar β m ≠ 0 := monoidHom_ne_zero _ m
  have key : leviRatio β m * leviSqrtModular β m * x ^ (1 + c) =
      (inducedChar β m)⁻¹ * leviModulus β m := by
    rw [eq_inv_mul_iff_mul_eq₀ hκ0, hκ, ← hid, ← hsq, ← hpow]
    ring
  rw [hsplit, ← mul_assoc, ← Complex.ofReal_mul, ← NNReal.coe_mul, key]

theorem leviIntegrandB_eq (Ψ : Matrix (Fin n) (Fin n) F → ℂ) (w : W) (ℓ : Module.Dual ℂ W)
    (s : ℂ) (m : levi F n β) :
    Ψ ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
        (((leviRatio β m * leviSqrtModular β m : ℝ≥0) : ℂ) *
          detPow (m : GL (Fin n) F) (1 - s + ((n : ℂ) - 1) / 2)) * ℓ (σ m⁻¹ w) =
      leviIntegrandB σ (inducedChar β) Ψ w ℓ s m := by
  rw [weightB_eq, leviIntegrandB]
  ring

section ParabolicB


omit [MeasurableSpace F] [BorelSpace F] in
theorem modularCharacter_leviProj (p : blockUpper F n β) :
    Measure.modularCharacter (leviIncl (leviProj F n β p)) = Measure.modularCharacter p := by
  have h := modularCharacter_eq_one_of_mem _ (leviProj_inv_mul_mem p)
  rw [map_mul, map_inv] at h
  exact (inv_mul_eq_one₀ (monoidHom_ne_zero _ _)).1 h

omit [MeasurableSpace F] [BorelSpace F] in
theorem modularCharacter_parabolicMk (m : levi F n β) (u : UnipotentIndex n β → F) :
    Measure.modularCharacter (parabolicMk β m u) = Measure.modularCharacter (leviIncl m) := by
  rw [← modularCharacter_leviProj, leviProj_parabolicMk]

omit [MeasurableSpace F] [BorelSpace F] in
theorem sqrtModular_parabolicMk (m : levi F n β) (u : UnipotentIndex n β → F) :
    sqrtModular F n β (parabolicMk β m u) = ((leviSqrtModular β m : ℝ≥0) : ℂ) := by
  rw [coe_leviSqrtModular, ← sqrtModular_leviProj, leviProj_parabolicMk]

omit [MeasurableSpace F] [BorelSpace F] in
theorem leviSqrtModular_mul_self (m : levi F n β) :
    leviSqrtModular β m * leviSqrtModular β m = Measure.modularCharacter (leviIncl m) := by
  simp [leviSqrtModular, NNReal.mul_self_sqrt]


variable (β) in
def parabolicB (Ξ : Matrix (Fin n) (Fin n) F → ℂ) (φ : GL (Fin n) F → W) (ℓ : Module.Dual ℂ W)
    (s : ℂ) (y : GL (Fin n) F) (p : blockUpper F n β) : ℂ :=
  Ξ ((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
    detPow (p : GL (Fin n) F) (1 - s + ((n : ℂ) - 1) / 2) * ℓ (φ ((p : GL (Fin n) F)⁻¹ * y))


omit [MeasurableSpace F] [BorelSpace F] in
theorem modular_mul_parabolicB {φ : GL (Fin n) F → W} (hφ : φ ∈ parabolicIndSpace F n β σ)
    (Ξ : Matrix (Fin n) (Fin n) F → ℂ) (ℓ : Module.Dual ℂ W) (s : ℂ) (y : GL (Fin n) F)
    (m : levi F n β) (u : UnipotentIndex n β → F) :
    (Measure.modularCharacter (parabolicMk β m u) : ℂ) * parabolicB β Ξ φ ℓ s y (parabolicMk β m u) =
      Ξ (((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) + unipMatrix F u) *
        (((leviSqrtModular β m : ℝ≥0) : ℂ) *
          detPow (m : GL (Fin n) F) (1 - s + ((n : ℂ) - 1) / 2) * ℓ (σ m⁻¹ (φ y))) := by
  have h1 := hφ.1 (parabolicMk β m u)⁻¹ y
  rw [inflateTwist_apply, map_inv, map_inv, leviProj_parabolicMk, sqrtModular_parabolicMk,
    Subgroup.coe_inv] at h1
  have hs0 : ((leviSqrtModular β m : ℝ≥0) : ℂ) ≠ 0 := by
    exact_mod_cast monoidHom_ne_zero (leviSqrtModular β) m
  rw [parabolicB, h1, map_smul, smul_eq_mul, modularCharacter_parabolicMk,
    ← leviSqrtModular_mul_self, coe_parabolicMk, detPow_parabolicMk]
  push_cast
  field_simp

variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)] (ψ : AddChar F Circle)


variable (β) in
abbrev measureP : Measure (blockUpper F n β) :=
  haarParabolic (parabolicMeasure β (leviCoordMeasure β ψ) (unipMeasure β ψ))


variable (β) in
abbrev measureM : Measure (levi F n β) := haarLevi β (leviCoordMeasure β ψ)

omit [MeasurableSpace F] [BorelSpace F] [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)] in
theorem continuous_parabolicB {φ : GL (Fin n) F → W} (hφ : φ ∈ parabolicIndSpace F n β σ)
    {Ξ : Matrix (Fin n) (Fin n) F → ℂ} (hΞ : IsSchwartzBruhat Ξ) (ℓ : Module.Dual ℂ W) (s : ℂ)
    (y : GL (Fin n) F) : Continuous (parabolicB β Ξ φ ℓ s y) := by
  obtain ⟨K, hKo, hK⟩ := hφ.2
  have hℓφ : Continuous fun g => ℓ (φ g) := by
    refine IsLocallyConstant.continuous fun S => isOpen_iff_forall_mem_open.2 fun g hg => ?_
    refine ⟨g • (K : Set (GL (Fin n) F)), ?_, hKo.smul g, ⟨1, one_mem _, mul_one g⟩⟩
    rintro _ ⟨k, hk, rfl⟩
    simp only [Set.mem_preimage, smul_eq_mul, hK k hk]
    exact hg
  have hv : Continuous fun p : blockUpper F n β => (p : GL (Fin n) F) := continuous_subtype_val
  exact ((hΞ.1.continuous.comp (Units.continuous_val.comp hv)).mul
    ((continuous_detPow _).comp hv)).mul (hℓφ.comp ((hv.inv).mul continuous_const))

theorem lintegral_parabolicB_inv {φ : GL (Fin n) F → W} (hφ : φ ∈ parabolicIndSpace F n β σ)
    {Ξ : Matrix (Fin n) (Fin n) F → ℂ} (hΞ : IsSchwartzBruhat Ξ) (ℓ : Module.Dual ℂ W) (s : ℂ)
    (y : GL (Fin n) F) :
    ∫⁻ p, ‖parabolicB β Ξ φ ℓ s y p⁻¹‖ₑ ∂measureP β ψ =
      ∫⁻ m, ‖leviIntegrandB σ (inducedChar β)
        (fun X => ∫ u, ((‖Ξ (X + unipMatrix F u)‖ : ℝ) : ℂ) ∂unipMeasure β ψ) (φ y) ℓ s m‖ₑ
          ∂measureM β ψ := by
  have : SecondCountableTopology (blockUpper F n β) :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
  have hc := continuous_parabolicB hφ hΞ ℓ s y
  have hmeas : Measurable fun p => ‖parabolicB β Ξ φ ℓ s y p‖ₑ := hc.enorm.measurable
  have hΔ := LinearChart.measurable_modularCharacter (parabolicChart F n β)
  rw [show measureP β ψ = (parabolicChart F n β).haar
      (parabolicMeasure β (leviCoordMeasure β ψ) (unipMeasure β ψ)) from rfl,
    LinearChart.lintegral_inv_haar _ _ hmeas,
    show (parabolicChart F n β).haar (parabolicMeasure β (leviCoordMeasure β ψ) (unipMeasure β ψ)) =
      measureP β ψ from rfl,
    lintegral_haarParabolic (leviCoordMeasure β ψ) (unipMeasure β ψ)
      (H := fun p => (Measure.modularCharacter p : ℝ≥0∞) * ‖parabolicB β Ξ φ ℓ s y p‖ₑ)
      (hΔ.mul hmeas)]
  refine lintegral_congr fun m => ?_
  have hint := integrable_add_unipMatrix (unipMeasure β ψ) hΞ
    (X := ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) (mem_levi.1 m.2)
  set c : ℂ := ((leviSqrtModular β m : ℝ≥0) : ℂ) *
    detPow (m : GL (Fin n) F) (1 - s + ((n : ℂ) - 1) / 2) * ℓ (σ m⁻¹ (φ y)) with hcdef
  have hpt : ∀ u, (Measure.modularCharacter (parabolicMk β m u) : ℝ≥0∞) *
      ‖parabolicB β Ξ φ ℓ s y (parabolicMk β m u)‖ₑ =
        ‖Ξ (((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) + unipMatrix F u)‖ₑ * ‖c‖ₑ := by
    intro u
    rw [← enorm_coe_nnreal, ← enorm_mul]
    have := modular_mul_parabolicB (σ := σ) hφ Ξ ℓ s y m u
    rw [this, enorm_mul]
  simp_rw [hpt]
  have hΞm : Measurable fun u : UnipotentIndex n β → F =>
      ‖Ξ (((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) + unipMatrix F u)‖ₑ :=
    (hΞ.1.continuous.comp (continuous_const.add continuous_unipMatrix)).enorm.measurable
  rw [lintegral_mul_const _ hΞm, ← ofReal_integral_norm_eq_lintegral_enorm hint]
  have hI : 0 ≤ ∫ u, ‖Ξ (((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) + unipMatrix F u)‖
      ∂unipMeasure β ψ := integral_nonneg fun _ => norm_nonneg _
  rw [← leviIntegrandB_eq, integral_complex_ofReal, hcdef]
  simp only [enorm_mul]
  rw [enorm_ofReal_complex hI, enorm_coe_nnreal, enorm_coe_nnreal]
  push_cast
  ring

theorem integral_parabolicB_inv {φ : GL (Fin n) F → W} (hφ : φ ∈ parabolicIndSpace F n β σ)
    {Ξ : Matrix (Fin n) (Fin n) F → ℂ} (hΞ : IsSchwartzBruhat Ξ) (ℓ : Module.Dual ℂ W) (s : ℂ)
    (y : GL (Fin n) F)
    (hint : Integrable (fun p => parabolicB β Ξ φ ℓ s y p⁻¹) (measureP β ψ)) :
    ∫ p, parabolicB β Ξ φ ℓ s y p⁻¹ ∂measureP β ψ =
      ∫ m, leviIntegrandB σ (inducedChar β)
        (fun X => ∫ u, Ξ (X + unipMatrix F u) ∂unipMeasure β ψ) (φ y) ℓ s m ∂measureM β ψ := by
  have : SecondCountableTopology (blockUpper F n β) :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
  have hc := continuous_parabolicB hφ hΞ ℓ s y
  have hΔc : Continuous fun p : blockUpper F n β => ((Measure.modularCharacter p : ℝ≥0) : ℂ) :=
    (Complex.continuous_ofReal.comp NNReal.continuous_coe).comp
      (LinearChart.continuous_modularCharacter (parabolicChart F n β))
  have hint2 : Integrable (fun p => ((Measure.modularCharacter p : ℝ≥0) : ℂ) *
      parabolicB β Ξ φ ℓ s y p) (measureP β ψ) := by
    refine ⟨(hΔc.mul hc).aestronglyMeasurable, ?_⟩
    show ∫⁻ p, ‖((Measure.modularCharacter p : ℝ≥0) : ℂ) * parabolicB β Ξ φ ℓ s y p‖ₑ
      ∂measureP β ψ < ⊤
    have h1 : ∫⁻ p, ‖((Measure.modularCharacter p : ℝ≥0) : ℂ) * parabolicB β Ξ φ ℓ s y p‖ₑ
        ∂measureP β ψ = ∫⁻ p, ‖parabolicB β Ξ φ ℓ s y p⁻¹‖ₑ ∂measureP β ψ := by
      rw [show measureP β ψ = (parabolicChart F n β).haar
          (parabolicMeasure β (leviCoordMeasure β ψ) (unipMeasure β ψ)) from rfl,
        LinearChart.lintegral_inv_haar _ _ hc.enorm.measurable]
      refine lintegral_congr fun p => ?_
      rw [enorm_mul, enorm_coe_nnreal]
    rw [h1]
    exact hint.2
  rw [show measureP β ψ = (parabolicChart F n β).haar
      (parabolicMeasure β (leviCoordMeasure β ψ) (unipMeasure β ψ)) from rfl,
    LinearChart.integral_inv_haar _ _ hc,
    show (parabolicChart F n β).haar (parabolicMeasure β (leviCoordMeasure β ψ) (unipMeasure β ψ)) =
      measureP β ψ from rfl,
    integral_haarParabolic (leviCoordMeasure β ψ) (unipMeasure β ψ) hint2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun m => ?_)
  simp only
  simp_rw [modular_mul_parabolicB (σ := σ) hφ Ξ ℓ s y m]
  rw [integral_mul_const, ← leviIntegrandB_eq]
  push_cast
  ring

end ParabolicB

end GodementJacquet

end GroundTheory.Automorphic
end
end
end
