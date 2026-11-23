module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFinsetIntegralScaledBoxPiCosetRepsStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralScaledBoxPiSupersetOfIsCompactStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumIntegralScaledBoxPiCosetRepsShiftInvariantStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddCharConductorAndHaarIntegersExist
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSchwartzBruhatConvolutionLocalFieldPower
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatFunctionalZeroOfFibreIntegralZeroStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSchwartzBruhatConvolutionLocalFieldPower
import Mathlib.Tactic.TypeStar

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCutoffOfAddCharTranslationInvariantFunctio

section

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
open scoped Topology

noncomputable section
namespace GlobalTheory.CharCutoff

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem dot_eq_one {ψ : AddChar k Circle} {c : kˣ} (h : HasConductor ψ c) {n : Type} [Fintype n]
    (R : kˣ) {t y : n → k} (ht : t ∈ box n (c * R⁻¹)) (hy : y ∈ box n R) : ψ (t ⬝ᵥ y) = 1 := by
  apply h.eq_one
  show valuation k (∑ i, t i * y i) ≤ valuation k (c : k)
  refine Valuation.map_sum_le (valuation k) fun i _ => ?_
  have h2 : valuation k (t i * y i) ≤ valuation k (((c * R⁻¹ : kˣ) : k) * R) := by
    rw [map_mul, map_mul]
    exact mul_le_mul' (ht i trivial) (hy i trivial)
  rwa [← Units.val_mul, inv_mul_cancel_right] at h2

theorem exists_dot_ne_one {ψ : AddChar k Circle} {c : kˣ} (h : HasConductor ψ c) {n : Type} [Fintype n]
    (s : kˣ) {y : n → k} (hy : y ∉ box n s) : ∃ b ∈ box n (c * s⁻¹), ψ (b ⬝ᵥ y) ≠ 1 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, y i ∉ cball s := by
    by_contra hne
    push_neg at hne
    exact hy fun i _ => hne i
  have hcs : c * (c * s⁻¹)⁻¹ = s := by
    rw [_root_.mul_inv_rev, inv_inv, mul_comm s, mul_inv_cancel_left]
  obtain ⟨t, ht, hne⟩ := h.exists_ne_one (c * s⁻¹) (x := y i) (by rwa [hcs])
  refine ⟨Pi.single i t, fun j _ => ?_, ?_⟩
  · by_cases hj : j = i
    · subst hj; simpa using ht
    · simp [Pi.single_eq_of_ne hj, cball]
  · rwa [single_dotProduct]

theorem sum_char {ψ : AddChar k Circle} {c : kˣ} (h : HasConductor ψ c) {n : Type} [Fintype n]
    (s R : kˣ) (S : Finset (n → k)) (hS : ∀ b ∈ S, b ∈ box n (c * s⁻¹))
    (hU : ∀ a ∈ box n (c * s⁻¹), ∃! b, b ∈ S ∧ a - b ∈ box n (c * R⁻¹)) {y : n → k}
    (hy : y ∈ box n R) :
    ∑ b ∈ S, (ψ (b ⬝ᵥ y) : ℂ) = (box n s).indicator (fun _ => (1 : ℂ)) y * S.card := by
  by_cases hys : y ∈ box n s
  · rw [Set.indicator_of_mem hys, one_mul]
    rw [Finset.sum_congr rfl fun b hb => by rw [dot_eq_one h s (hS b hb) hys, Circle.coe_one]]
    simp
  · rw [Set.indicator_of_notMem hys, zero_mul]
    obtain ⟨a, ha, hne⟩ := exists_dot_ne_one h s hys
    have key := GlobalTheory.T.sum_integralScaledBoxPi_coset_reps_shift_invariant k n (c * R⁻¹) (c * s⁻¹) S hS hU (fun b => (ψ (b ⬝ᵥ y) : ℂ))
      (fun t ht z => by
        rw [add_dotProduct, AddChar.map_add_eq_mul, Circle.coe_mul, dot_eq_one h R ht hy,
          Circle.coe_one, mul_one]) a ha
    simp only [add_dotProduct, AddChar.map_add_eq_mul, Circle.coe_mul, ← Finset.mul_sum] at key
    have h3 : (ψ (a ⬝ᵥ y) : ℂ) - 1 ≠ 0 := fun h4 => hne (Circle.ext (by simpa using sub_eq_zero.mp h4))
    refine (mul_eq_zero.mp ?_).resolve_left h3
    rw [sub_mul, key, one_mul, sub_self]

theorem exists_cutoff_of_char_invariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (I₀ I₁ I₂ : Type) [Fintype I₀] [Fintype I₁] [Fintype I₂] (M : Type) [AddCommGroup M] [Module ℂ M] (l : SB ((I₀ → k) × (I₁ → k) × (I₂ → k)) →ₗ[ℂ] M), (∀ (b : I₁ → k) (Φ Φ' : SB ((I₀ → k) × (I₁ → k) × (I₂ → k))), (∀ x, Φ'.1 x = (ψ (b ⬝ᵥ x.2.1) : ℂ) * Φ.1 x) → l Φ' = l Φ) → ∀ (Φ : SB ((I₀ → k) × (I₁ → k) × (I₂ → k))) (s : kˣ), ∃ Φ' : SB ((I₀ → k) × (I₁ → k) × (I₂ → k)), (∀ x, Φ'.1 x = (box I₁ s).indicator (fun _ => (1 : ℂ)) x.2.1 * Φ.1 x) ∧ l Φ = l Φ' := by
  intro k _ _ _ _ ψ hψ h1 I₀ I₁ I₂ _ _ _ M _ _ l hl Φ s
  haveI := t2Space k
  obtain ⟨c, hc⟩ := exists_hasConductor_of_continuous ψ hψ h1
  have hK : IsCompact ((fun x : (I₀ → k) × (I₁ → k) × (I₂ → k) => x.2.1) '' tsupport Φ.1) :=
    Φ.2.2.image (by fun_prop)
  obtain ⟨R, hsR, hKR⟩ := GlobalTheory.T.exists_integralScaledBoxPi_superset_of_isCompact k I₁ _ hK s
  have hvr : valuation k ((c * R⁻¹ : kˣ) : k) ≤ valuation k ((c * s⁻¹ : kˣ) : k) := by
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀]
    exact mul_le_mul' le_rfl (inv_anti₀ (by simp [zero_lt_iff]) hsR)
  obtain ⟨S, hS, hU⟩ := GlobalTheory.T.exists_finset_integralScaledBoxPi_coset_reps k I₁ (c * R⁻¹) (c * s⁻¹) hvr
  have hmem : ∀ b : I₁ → k,
      (fun x : (I₀ → k) × (I₁ → k) × (I₂ → k) => (ψ (b ⬝ᵥ x.2.1) : ℂ) * Φ.1 x) ∈
        SB ((I₀ → k) × (I₁ → k) × (I₂ → k)) := fun b => by
    have hcont : Continuous fun x : (I₀ → k) × (I₁ → k) × (I₂ → k) => b ⬝ᵥ x.2.1 :=
      continuous_const.dotProduct (continuous_fst.comp continuous_snd)
    have h2 : IsLocallyConstant fun x : (I₀ → k) × (I₁ → k) × (I₂ → k) => (ψ (b ⬝ᵥ x.2.1) : ℂ) :=
      (IsLocallyConstant.comp_continuous hc.isLocallyConstant hcont).comp (fun z : Circle => (z : ℂ))
    exact ⟨IsLocallyConstant.mul h2 Φ.2.1, Φ.2.2.mul_left⟩
  let Φb : (I₁ → k) → SB ((I₀ → k) × (I₁ → k) × (I₂ → k)) := fun b => ⟨_, hmem b⟩
  have hlb : ∀ b, l (Φb b) = l Φ := fun b => hl b Φ (Φb b) (fun x => rfl)
  have h0 : (0 : I₁ → k) ∈ box I₁ (c * s⁻¹) := fun i _ => by simp [cball]
  obtain ⟨b0, ⟨hb0, _⟩, _⟩ := hU 0 h0
  have hcard : (S.card : ℂ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr ⟨b0, hb0⟩).ne'
  refine ⟨(S.card : ℂ)⁻¹ • ∑ b ∈ S, Φb b, fun x => ?_, ?_⟩
  · simp only [Submodule.coe_smul, Submodule.coe_sum, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    show (S.card : ℂ)⁻¹ * ∑ b ∈ S, (ψ (b ⬝ᵥ x.2.1) : ℂ) * Φ.1 x = _
    rw [← Finset.sum_mul]
    by_cases hx : x ∈ tsupport Φ.1
    · rw [sum_char hc s R S hS hU (hKR ⟨x, hx, rfl⟩), ← mul_assoc, mul_comm ((S.card : ℂ)⁻¹),
        mul_inv_cancel_right₀ hcard]
    · rw [image_eq_zero_of_notMem_tsupport hx]; simp

  · rw [map_smul, map_sum, Finset.sum_congr rfl fun b _ => hlb b, Finset.sum_const,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hcard, one_smul]

end GlobalTheory.CharCutoff
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCutoffOfAddCharTranslationInvariantFunctioStatement

section

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
open scoped Topology

theorem _root_.GlobalTheory.T.exists_cutoff_of_addChar_translation_invariant_functional : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (I₀ I₁ I₂ : Type) [Fintype I₀] [Fintype I₁] [Fintype I₂] (M : Type) [AddCommGroup M] [Module ℂ M] (l : SB ((I₀ → k) × (I₁ → k) × (I₂ → k)) →ₗ[ℂ] M), (∀ (b : I₁ → k) (Φ Φ' : SB ((I₀ → k) × (I₁ → k) × (I₂ → k))), (∀ x, Φ'.1 x = (ψ (b ⬝ᵥ x.2.1) : ℂ) * Φ.1 x) → l Φ' = l Φ) → ∀ (Φ : SB ((I₀ → k) × (I₁ → k) × (I₂ → k))) (s : kˣ), ∃ Φ' : SB ((I₀ → k) × (I₁ → k) × (I₂ → k)), (∀ x, Φ'.1 x = (box I₁ s).indicator (fun _ => (1 : ℂ)) x.2.1 * Φ.1 x) ∧ l Φ = l Φ' := by
  first | exact @GlobalTheory.CharCutoff.exists_cutoff_of_char_invariant | exact GlobalTheory.CharCutoff.exists_cutoff_of_char_invariant | (intros; apply GlobalTheory.CharCutoff.exists_cutoff_of_char_invariant <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralLastFactorSliceMemSchwartzBruhat

section

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
open scoped Topology

noncomputable section
namespace GlobalTheory.SliceIntegral

theorem integral_slice_mem_SB (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k)
    (I₀ I₁ I₂ : Type) [Fintype I₀] [Fintype I₁] [Fintype I₂]
    (Φ : SB ((I₀ → k) × (I₁ → k) × (I₂ → k))) :
    (fun x => ∫ a, Φ.1 (x, 0, a) ∂(Measure.pi fun _ => ν)) ∈ SB (I₀ → k) := by
  haveI := t2Space k
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_,
    HasCompactSupport.intro (IsCompact.image Φ.2.2 continuous_fst) fun x hx => ?_⟩
  · have ht : Filter.Tendsto (fun x' : I₀ → k => ((x - x', (0 : I₁ → k), (0 : I₂ → k)) :
        (I₀ → k) × (I₁ → k) × (I₂ → k))) (𝓝 x) (𝓝 0) := by
      have hc : Continuous (fun x' : I₀ → k => ((x - x', (0 : I₁ → k), (0 : I₂ → k)) :
          (I₀ → k) × (I₁ → k) × (I₂ → k))) := by fun_prop
      have := hc.tendsto x
      rwa [sub_self, ← Prod.zero_eq_mk, ← Prod.zero_eq_mk] at this
    filter_upwards [ht.eventually (GlobalTheory.SBConv.eventually_translate Φ.2)] with x' hx'
    congr 1
    funext a
    have := hx' (x, 0, a)
    simpa using this
  · have h0 : ∀ a, Φ.1 (x, 0, a) = 0 := fun a =>
      image_eq_zero_of_notMem_tsupport fun h => hx ⟨_, h, rfl⟩
    simp [h0]

end GlobalTheory.SliceIntegral
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralLastFactorSliceMemSchwartzBruhatStatement

section

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
open scoped Topology

theorem _root_.GlobalTheory.T.integral_last_factor_slice_mem_schwartzBruhat : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) (I₀ I₁ I₂ : Type) [Fintype I₀] [Fintype I₁] [Fintype I₂] (Φ : SB ((I₀ → k) × (I₁ → k) × (I₂ → k))), (fun x => ∫ a, Φ.1 (x, 0, a) ∂(Measure.pi fun _ => ν)) ∈ SB (I₀ → k) := by
  first | exact @GlobalTheory.SliceIntegral.integral_slice_mem_SB | exact GlobalTheory.SliceIntegral.integral_slice_mem_SB | (intros; apply GlobalTheory.SliceIntegral.integral_slice_mem_SB <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatLinearFunctional

section

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
open scoped Topology

noncomputable section
namespace GlobalTheory.CoinvSB

theorem isLocallyConstant_indicator_const {X : Type*} [TopologicalSpace X] {U : Set X} (h1 : IsOpen U)
    (h2 : IsClosed U) (c : ℂ) : IsLocallyConstant (U.indicator fun _ => c) := by
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_
  by_cases hx : x ∈ U
  · filter_upwards [h1.mem_nhds hx] with y hy
    simp [Set.indicator_of_mem hx, Set.indicator_of_mem hy]
  · filter_upwards [h2.isOpen_compl.mem_nhds hx] with y hy
    simp [Set.indicator_of_notMem hx, Set.indicator_of_notMem hy]

theorem kernel : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (I₀ I₁ I₂ : Type) [Fintype I₀] [Fintype I₁] [Fintype I₂] (M : Type) [AddCommGroup M] [Module ℂ M] (l : SB ((I₀ → k) × (I₁ → k) × (I₂ → k)) →ₗ[ℂ] M), (∀ (b : I₁ → k) (Φ Φ' : SB ((I₀ → k) × (I₁ → k) × (I₂ → k))), (∀ x, Φ'.1 x = (ψ (b ⬝ᵥ x.2.1) : ℂ) * Φ.1 x) → l Φ' = l Φ) → (∀ (a : I₂ → k) (Φ Φ' : SB ((I₀ → k) × (I₁ → k) × (I₂ → k))), (∀ x, Φ'.1 x = Φ.1 (x + (0, 0, a))) → l Φ' = l Φ) → ∀ D : SB ((I₀ → k) × (I₁ → k) × (I₂ → k)), (∀ x₀, ∫ a, D.1 (x₀, 0, a) ∂(Measure.pi fun _ => ν) = 0) → l D = 0 := by
  intro k _ _ _ _ _ _ ψ ν hψc hψ1 hν I₀ I₁ I₂ _ _ _ M _ _ l h1 h2 D hD
  obtain ⟨s, hs⟩ : ∃ s : kˣ, ∀ t ∈ box I₁ s, ∀ y : (I₀ → k) × (I₁ → k) × (I₂ → k),
      D.1 (y + (0, t, 0)) = D.1 y := by
    have h := GlobalTheory.SBConv.eventually_translate D.2
    have hT : Filter.Tendsto (fun t : I₁ → k => ((0 : I₀ → k), -t, (0 : I₂ → k))) (𝓝 0) (𝓝 0) := by
      have : Continuous (fun t : I₁ → k => ((0 : I₀ → k), -t, (0 : I₂ → k))) := by fun_prop
      exact this.tendsto' 0 0 (by simp)
    obtain ⟨s, hs⟩ := exists_box_subset (hT.eventually h)
    refine ⟨s, fun t ht y => ?_⟩
    have := hs ht y
    simpa [sub_eq_add_neg] using this
  obtain ⟨Φ', hΦ', hl⟩ := GlobalTheory.T.exists_cutoff_of_addChar_translation_invariant_functional k ψ hψc hψ1 I₀ I₁ I₂ M l h1 D s
  have hz : ∀ x₀ x₁, ∫ a, Φ'.1 (x₀, x₁, a) ∂(Measure.pi fun _ => ν) = 0 := by
    intro x₀ x₁
    simp_rw [hΦ']
    by_cases hx : x₁ ∈ box I₁ s
    · have e : ∀ a, D.1 (x₀, x₁, a) = D.1 (x₀, 0, a) := fun a => by
        simpa using hs x₁ hx (x₀, 0, a)
      simp only [Set.indicator_of_mem hx, one_mul, e]
      exact hD x₀
    · simp [Set.indicator_of_notMem hx]
  rw [hl]
  exact GlobalTheory.T.schwartzBruhat_functional_zero_of_fibre_integral_zero k ν hν I₀ I₁ I₂ M l h2 Φ' hz

theorem coinvariants : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (I₀ I₁ I₂ : Type) [Fintype I₀] [Fintype I₁] [Fintype I₂] (M : Type) [AddCommGroup M] [Module ℂ M] (l : SB ((I₀ → k) × (I₁ → k) × (I₂ → k)) →ₗ[ℂ] M), (∀ (b : I₁ → k) (Φ Φ' : SB ((I₀ → k) × (I₁ → k) × (I₂ → k))), (∀ x, Φ'.1 x = (ψ (b ⬝ᵥ x.2.1) : ℂ) * Φ.1 x) → l Φ' = l Φ) → (∀ (a : I₂ → k) (Φ Φ' : SB ((I₀ → k) × (I₁ → k) × (I₂ → k))), (∀ x, Φ'.1 x = Φ.1 (x + (0, 0, a))) → l Φ' = l Φ) → ∃! l₀ : SB (I₀ → k) →ₗ[ℂ] M, ∀ Φ : SB ((I₀ → k) × (I₁ → k) × (I₂ → k)), ∃ Ψ : SB (I₀ → k), (∀ x, Ψ.1 x = ∫ a, Φ.1 (x, 0, a) ∂(Measure.pi fun _ => ν)) ∧ l Φ = l₀ Ψ := by
  intro k _ _ _ _ _ _ ψ ν hψc hψ1 hν I₀ I₁ I₂ _ _ _ M _ _ l h1 h2
  haveI := secondCountable k
  haveI := t2Space k
  set μ : Measure (I₂ → k) := Measure.pi fun _ => ν with hμ
  haveI : μ.IsAddHaarMeasure := by rw [hμ]; infer_instance
  set vol : ℝ := μ.real (box I₂ 1) with hvol
  have hvol0 : vol ≠ 0 := by
    refine (ENNReal.toReal_pos ?_ ?_).ne'
    · exact (isOpen_box 1).measure_ne_zero μ ⟨0, fun i _ => by simp [cball]⟩
    · exact (isCompact_box 1).measure_lt_top.ne
  have hlc : ∀ (n : Type) [Fintype n] (c : ℂ), IsLocallyConstant ((box n (1 : kˣ)).indicator fun _ => c) :=
    fun n _ c => isLocallyConstant_indicator_const (isOpen_box 1) (isCompact_box 1).isClosed c
  let σf : SB (I₀ → k) → (I₀ → k) × (I₁ → k) × (I₂ → k) → ℂ := fun Ψ x =>
    Ψ.1 x.1 * ((box I₁ (1 : kˣ)).indicator (fun _ => (1 : ℂ)) x.2.1 *
      (box I₂ (1 : kˣ)).indicator (fun _ => ((vol : ℂ))⁻¹) x.2.2)
  have hσ : ∀ Ψ, σf Ψ ∈ SB ((I₀ → k) × (I₁ → k) × (I₂ → k)) := by
    intro Ψ
    refine ⟨(Ψ.2.1.comp_continuous continuous_fst).mul
      (((hlc I₁ 1).comp_continuous (by fun_prop)).mul ((hlc I₂ _).comp_continuous (by fun_prop))), ?_⟩
    refine HasCompactSupport.intro (Ψ.2.2.prod ((isCompact_box (1 : kˣ)).prod (isCompact_box (1 : kˣ)))) ?_
    intro x hx
    simp only [σf]
    by_cases h0 : x.1 ∈ tsupport Ψ.1
    · by_cases h1' : x.2.1 ∈ box I₁ (1 : kˣ)
      · have h2' : x.2.2 ∉ box I₂ (1 : kˣ) := fun h => hx ⟨h0, h1', h⟩
        simp [Set.indicator_of_notMem h2']
      · simp [Set.indicator_of_notMem h1']
    · simp [image_eq_zero_of_notMem_tsupport h0]
  let σ : SB (I₀ → k) →ₗ[ℂ] SB ((I₀ → k) × (I₁ → k) × (I₂ → k)) :=
    { toFun := fun Ψ => ⟨σf Ψ, hσ Ψ⟩
      map_add' := fun Ψ Ψ' => by
        apply Subtype.ext; funext x; simp only [σf, Submodule.coe_add, Pi.add_apply]; ring
      map_smul' := fun c Ψ => by
        apply Subtype.ext; funext x; simp only [σf, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
          RingHom.id_apply]; ring }
  have hσv : ∀ Ψ x, (σ Ψ).1 x = σf Ψ x := fun _ _ => rfl
  have hInt : ∀ (Φ : SB ((I₀ → k) × (I₁ → k) × (I₂ → k))) (x : I₀ → k),
      Integrable (fun a => Φ.1 (x, 0, a)) μ := by
    intro Φ x
    refine Continuous.integrable_of_hasCompactSupport (Φ.2.1.continuous.comp (by fun_prop)) ?_
    refine HasCompactSupport.intro (IsCompact.image Φ.2.2 (continuous_snd.comp continuous_snd)) fun a ha => ?_
    exact image_eq_zero_of_notMem_tsupport fun h => ha ⟨_, h, rfl⟩
  have hσi : ∀ Ψ x, ∫ a, (σ Ψ).1 (x, 0, a) ∂μ = Ψ.1 x := by
    intro Ψ x
    simp only [hσv, σf]
    have h0 : (0 : I₁ → k) ∈ box I₁ (1 : kˣ) := fun i _ => by simp [cball]
    simp only [Set.indicator_of_mem h0, one_mul]
    rw [integral_const_mul, integral_indicator_const _ (isOpen_box _).measurableSet]
    rw [← hvol, Complex.real_smul, mul_inv_cancel₀ (by exact_mod_cast hvol0), mul_one]
  refine ⟨l ∘ₗ σ, fun Φ => ⟨⟨_, GlobalTheory.T.integral_last_factor_slice_mem_schwartzBruhat k ν I₀ I₁ I₂ Φ⟩, fun x => rfl, ?_⟩, ?_⟩
  · set Ψ : SB (I₀ → k) := ⟨_, GlobalTheory.T.integral_last_factor_slice_mem_schwartzBruhat k ν I₀ I₁ I₂ Φ⟩
    have hk := kernel k ψ ν hψc hψ1 hν I₀ I₁ I₂ M l h1 h2 (Φ - σ Ψ) (fun x₀ => by
      simp only [Submodule.coe_sub, Pi.sub_apply]
      rw [integral_sub (hInt Φ x₀) (hInt (σ Ψ) x₀), hσi]
      exact sub_self _)
    rw [map_sub, sub_eq_zero] at hk
    simpa using hk
  · intro l₀ hl₀
    ext1 Ψ
    obtain ⟨Ψ', hΨ', hl⟩ := hl₀ (σ Ψ)
    have : Ψ' = Ψ := Subtype.ext (funext fun x => (hΨ' x).trans (hσi Ψ x))
    subst this
    simp [← hl]

end GlobalTheory.CoinvSB
end
end
end
