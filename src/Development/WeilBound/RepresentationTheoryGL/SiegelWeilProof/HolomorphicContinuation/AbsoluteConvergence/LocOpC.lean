module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.DerivativeVacuumDilationsAlt
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.LocOpA
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.LocOpB
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
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.LocOpB
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.SphericalCharacterInvCompact

section

@[expose] public section

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal ComplexOrder

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw LocOpA

variable {n : ℕ}

def jLoc (p q : ℕ) (e : ℤ) (A B : GR n) (ψ : (Fin n → Fin n → ℝ) → ℂ) (w : ℂ) (g : GR n) : ℂ :=
  ∫ x, ((hLoc (g * A * nbEl x * B) : ℂ) ^ w * F0 p q e (g * A * nbEl x * B)) * ψ x

def czLoc (p q : ℕ) (e : ℤ) (A B : GR n) (ψ : (Fin n → Fin n → ℝ) → ℂ) [MeasurableSpace (KR n)] (μ : Measure (KR n))
    (w : ℂ) : ℂ :=
  ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * jLoc p q e A B ψ w (k : GR n) ∂μ

theorem eigen (hI : Iwa) (hM : Mult) (p q : ℕ) (e : ℤ) (A B : GR n) (ψ : (Fin n → Fin n → ℝ) → ℂ)
    [MeasurableSpace (KR n)] [BorelSpace (KR n)] (μ : Measure (KR n)) [μ.IsHaarMeasure] (w : ℂ) (y : GR n) :
    ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * (∫ x, ((hLoc (y * (k : GR n) * A * nbEl x * B) : ℂ) ^ w *
        F0 p q e (y * (k : GR n) * A * nbEl x * B)) * ψ x) ∂μ =
      czLoc p q e A B ψ μ w * ((hLoc y : ℂ) ^ w * F0 p q e y) := by
  obtain ⟨p0, k0, hp, hk0, rfl⟩ := hI n y
  have hM1 := (hM n p q e).1
  have hM2 := (hM n p q e).2
  have hJ : ∀ g : GR n, jLoc p q e A B ψ w (p0 * g) =
      ((hLoc p0 : ℂ) ^ w * F0 p q e p0) * jLoc p q e A B ψ w g := by
    intro g
    unfold jLoc
    rw [← integral_const_mul]
    congr 1
    funext x
    have h1 : p0 * g * A * nbEl x * B = p0 * (g * A * nbEl x * B) := by simp only [mul_assoc]
    rw [h1, (hM2 p0 _ hp).1, (hM2 p0 _ hp).2]
    push_cast
    rw [Complex.mul_cpow_ofReal_nonneg (by unfold hLoc; positivity) (by unfold hLoc; positivity)]
    ring
  have hne : F0 p q e k0 ≠ 0 := by
    intro h0
    have h2 := (hM1 k0 k0⁻¹ (inv_mem hk0)).1
    rw [mul_inv_cancel, weight_factor_one, h0, zero_mul] at h2
    exact one_ne_zero h2
  let K0 : KR n := ⟨k0, hk0⟩
  have hK0 : (K0 : GR n) = k0 := rfl
  have hshift : ∀ k : KR n, (F0 p q e (k : GR n))⁻¹ =
      F0 p q e k0 * (F0 p q e ((K0 * k : KR n) : GR n))⁻¹ := by
    intro k
    rw [Subgroup.coe_mul, hK0, (hM1 k0 k k.2).1, mul_inv, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
  calc _ = ∫ k : KR n, ((hLoc p0 : ℂ) ^ w * F0 p q e p0 * F0 p q e k0) *
        ((F0 p q e ((K0 * k : KR n) : GR n))⁻¹ * jLoc p q e A B ψ w ((K0 * k : KR n) : GR n)) ∂μ := by
        congr 1
        funext k
        show (F0 p q e (k : GR n))⁻¹ * jLoc p q e A B ψ w (p0 * k0 * (k : GR n)) = _
        rw [show p0 * k0 * (k : GR n) = p0 * ((K0 * k : KR n) : GR n) by
          rw [Subgroup.coe_mul, hK0, mul_assoc], hJ, hshift k]
        ring
    _ = ((hLoc p0 : ℂ) ^ w * F0 p q e p0 * F0 p q e k0) *
        ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * jLoc p q e A B ψ w (k : GR n) ∂μ := by
        rw [integral_const_mul]
        congr 1
        exact integral_mul_left_eq_self
          (fun k : KR n => (F0 p q e (k : GR n))⁻¹ * jLoc p q e A B ψ w (k : GR n)) K0
    _ = _ := by
        rw [(hM1 p0 k0 hk0).1, (hM1 p0 k0 hk0).2]
        unfold czLoc
        ring

theorem cz_zero (p q : ℕ) (e : ℤ) (a b : M2 n) (ha : InG a) (hb : InG b) (ψ : (Fin n → Fin n → ℝ) → ℂ)
    [MeasurableSpace (KR n)] (μ : Measure (KR n)) :
    czLoc p q e (mkG a ha) (mkG b hb) ψ μ 0 = (a.det * b.det) ^ e *
      ∫ k : KR n, (∫ x, f0 p q (mR (k : GR n) * a * nU (herm x) * b) * ψ x) * (f0 p q (mR (k : GR n)))⁻¹ ∂μ := by
  have hmul : ∀ g h : GR n, mR (g * h) = mR g * mR h := fun _ _ => rfl
  have hdetN : ∀ x, (nU (herm x) : M2 n).det = 1 := by
    intro x
    simp [nU, det_fromBlocks_zero₂₁]
  unfold czLoc
  rw [← integral_const_mul]
  congr 1
  funext k
  have hk : (mR (k : GR n)).det ^ e ≠ 0 := by
    apply zpow_ne_zero
    have h1 : (mR (k : GR n)).det * (mR ((k : GR n)⁻¹)).det = 1 := by
      rw [← det_mul, ← hmul, mul_inv_cancel]
      exact det_one
    exact left_ne_zero_of_mul_eq_one h1
  unfold jLoc
  simp only [Complex.cpow_zero, one_mul, F0, hmul, mR_mkG, nbEl, det_mul, hdetN, mul_one, mul_zpow,
    mul_assoc, integral_const_mul]
  generalize (mR (k : GR n)).det ^ e = D at hk ⊢
  have hD := inv_mul_cancel₀ hk
  rw [mul_inv]
  linear_combination (det a ^ e * (det b ^ e *
    ((∫ (x : Fin n → Fin n → ℝ), f0 (↑p) (↑q) (mR (k : GR n) * (a * (nU (herm x) * b))) * ψ x) *
      (f0 (↑p) (↑q) (mR (k : GR n)))⁻¹))) * hD

end PositivityTheory.Rg.Sw.AbsSt
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.LocOpC

section

@[expose] public section

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal ComplexOrder

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw LocOpA

variable {n : ℕ}

def fLoc (p q : ℕ) (e : ℤ) (A B : GR n) (ψ : (Fin n → Fin n → ℝ) → ℂ) (y : KR n × (Fin n → Fin n → ℝ)) (w : ℂ) : ℂ :=
  (F0 p q e (y.1 : GR n))⁻¹ * (((hLoc ((y.1 : GR n) * A * nbEl y.2 * B) : ℂ) ^ w *
    F0 p q e ((y.1 : GR n) * A * nbEl y.2 * B)) * ψ y.2)

theorem continuous_fLoc (p q : ℕ) (e : ℤ) (A B : GR n) {ψ : (Fin n → Fin n → ℝ) → ℂ} (hψ : Continuous ψ) :
    Continuous (fun y : (KR n × (Fin n → Fin n → ℝ)) × ℂ => fLoc p q e A B ψ y.1 y.2) := by
  have hg : Continuous (fun y : (KR n × (Fin n → Fin n → ℝ)) × ℂ => ((y.1.1 : GR n) * A * nbEl y.1.2 * B)) :=
    (((continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).mul continuous_const).mul
      (continuous_nbEl.comp (continuous_snd.comp continuous_fst))).mul continuous_const
  unfold fLoc
  refine (((continuous_weight_factor p q e).comp (continuous_subtype_val.comp (continuous_fst.comp continuous_fst))).inv₀
    (fun _ => weight_factor_ne_zero _ _ _ _)).mul ?_
  refine ((Continuous.cpow ?_ continuous_snd ?_).mul ((continuous_weight_factor p q e).comp hg)).mul
    (hψ.comp (continuous_snd.comp continuous_fst))
  · exact Complex.continuous_ofReal.comp (continuous_hLoc.comp hg)
  · intro y
    exact Complex.ofReal_mem_slitPlane.2 (hLoc_pos _)

theorem continuous_fLoc_w (p q : ℕ) (e : ℤ) (A B : GR n) {ψ : (Fin n → Fin n → ℝ) → ℂ} (hψ : Continuous ψ) (w : ℂ) :
    Continuous (fun y : KR n × (Fin n → Fin n → ℝ) => fLoc p q e A B ψ y w) := by
  have h1 := continuous_fLoc p q e A B hψ
  have h2 : Continuous (fun y : KR n × (Fin n → Fin n → ℝ) => ((y, w) : (KR n × (Fin n → Fin n → ℝ)) × ℂ)) :=
    continuous_id.prodMk continuous_const
  have h3 := h1.comp h2
  exact h3

theorem cz_eq (p q : ℕ) (e : ℤ) (A B : GR n) {ψ : (Fin n → Fin n → ℝ) → ℂ} (hψ : IsSingTest ψ)
    [MeasurableSpace (KR n)] [BorelSpace (KR n)] (μ : Measure (KR n)) [IsProbabilityMeasure μ] (w : ℂ) :
    czLoc p q e A B ψ μ w =
      ∫ y, fLoc p q e A B ψ y w ∂((μ.prod volume).restrict (univ ×ˢ tsupport ψ)) := by
  have hK : IsCompact ((univ : Set (KR n)) ×ˢ tsupport ψ) := isCompact_univ.prod hψ.2.1
  have hint : Integrable (fun y => fLoc p q e A B ψ y w) ((μ.prod volume).restrict (univ ×ˢ tsupport ψ)) :=
    ((continuous_fLoc_w p q e A B hψ.1 w).continuousOn).integrableOn_compact hK
  rw [← Measure.prod_restrict, Measure.restrict_univ] at hint ⊢
  rw [integral_prod _ hint]
  unfold czLoc jLoc
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp only [fLoc]
  rw [integral_const_mul]
  congr 1
  symm
  refine setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => ?_)
  have h0 : ψ x = 0 := by
    by_contra h
    exact hx (subset_tsupport ψ (Function.mem_support.2 h))
  simp [h0]

theorem cz_diff (hH : HolParam) (p q : ℕ) (e : ℤ) (A B : GR n) {ψ : (Fin n → Fin n → ℝ) → ℂ} (hψ : IsSingTest ψ)
    [MeasurableSpace (KR n)] [BorelSpace (KR n)] (μ : Measure (KR n)) [IsProbabilityMeasure μ] :
    Differentiable ℂ (czLoc p q e A B ψ μ) := by
  have hK : IsCompact ((univ : Set (KR n)) ×ˢ tsupport ψ) := isCompact_univ.prod hψ.2.1
  have hmeas : MeasurableSet ((univ : Set (KR n)) ×ˢ tsupport ψ) :=
    MeasurableSet.univ.prod (isClosed_tsupport ψ).measurableSet
  haveI : IsFiniteMeasure ((μ.prod volume).restrict ((univ : Set (KR n)) ×ˢ tsupport ψ)) :=
    ⟨by
      rw [Measure.restrict_apply_univ, Measure.prod_prod]
      exact ENNReal.mul_lt_top (measure_lt_top _ _) hψ.2.1.measure_lt_top⟩
  have hnull : ((μ.prod volume).restrict ((univ : Set (KR n)) ×ˢ tsupport ψ))
      ((univ : Set (KR n)) ×ˢ tsupport ψ)ᶜ = 0 := by
    rw [Measure.restrict_apply' hmeas, compl_inter_self, measure_empty]
  have hcont := (continuous_fLoc p q e A B hψ.1).continuousOn (s := ((univ : Set (KR n)) ×ˢ tsupport ψ) ×ˢ (univ : Set ℂ))
  have hdiff : ∀ y ∈ ((univ : Set (KR n)) ×ˢ tsupport ψ),
      DifferentiableOn ℂ (fun w => fLoc p q e A B ψ y w) univ := by
    intro y _
    refine Differentiable.differentiableOn ?_
    unfold fLoc
    refine Differentiable.const_mul ?_ _
    refine Differentiable.mul_const ?_ _
    refine Differentiable.mul_const ?_ _
    refine Differentiable.const_cpow differentiable_id (Or.inl ?_)
    exact_mod_cast (hLoc_pos _).ne'
  have h := (hH (KR n × (Fin n → Fin n → ℝ)) ((μ.prod volume).restrict ((univ : Set (KR n)) ×ˢ tsupport ψ))
    _ hK hnull univ (fun y w => fLoc p q e A B ψ y w) isOpen_univ hcont hdiff).1
  have heq : czLoc p q e A B ψ μ = fun w =>
      ∫ y, fLoc p q e A B ψ y w ∂((μ.prod volume).restrict (univ ×ˢ tsupport ψ)) :=
    funext (cz_eq p q e A B hψ μ)
  rw [heq]
  exact differentiableOn_univ.1 h


theorem locOp : LV → Iwa → Mult → HolParam → LocOp := by
  intro hLV hIwa hMult hHol n p q e hgood _ _ μ _ _
  let ι : KR n →* M2 n := (Units.coeHom (M2 n)).comp ((GR n).subtype.comp (KR n).subtype)
  have hι : Continuous ι := continuous_mR.comp continuous_subtype_val
  have hιs : ∀ g : M2 n, InK g ↔ ∃ k, ι k = g := by
    intro g
    constructor
    · intro hg
      exact ⟨kOf ⟨g, hg⟩, rfl⟩
    · rintro ⟨k, rfl⟩
      exact k.2
  obtain ⟨ψ, a, b, hψ, ha, hb, hne⟩ := hLV n p q hgood (KR n) μ ι hι hιs
  refine ⟨ψ, mkG a ha, mkG b hb, nbEl, czLoc p q e (mkG a ha) (mkG b hb) ψ μ, hψ, fun x => rfl, continuous_nbEl,
    cz_diff hHol p q e _ _ hψ μ, ?_, fun w y => eigen hIwa hMult p q e _ _ ψ μ w y⟩
  rw [cz_zero]
  refine mul_ne_zero (zpow_ne_zero _ (mul_ne_zero (det_mR_ne (mkG a ha)) (det_mR_ne (mkG b hb)))) ?_
  exact hne

end PositivityTheory.Rg.Sw.AbsSt
end
end
end
