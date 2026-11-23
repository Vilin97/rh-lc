module

public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WhittakerVanishingImpliesZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStandardAdelicAddChar
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensChLift
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensSAChar
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensSAInt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensVolS
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensSA

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensChLift

section

@[expose] public section

noncomputable section

open NumberField Complex

namespace PI.VolStabSW

namespace ChLiftW

theorem lift_normed {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] (χ : W → ℂ)
    (hc : Continuous χ) (hadd : ∀ x y, χ (x + y) = χ x * χ y) (h0 : χ 0 = 1) :
    ∃ ℓ : W →+ ℂ, Continuous ℓ ∧ ∀ x, χ x = exp (ℓ x) := by
  apply PI.VolStabS.ChLiftW.lift_normed <;> assumption

theorem lift_homeo {X W : Type*} [AddCommGroup X] [TopologicalSpace X] [NormedAddCommGroup W]
    [NormedSpace ℝ W] (e : X ≃ₜ W) (he : ∀ x y, e (x + y) = e x + e y) (χ : X → ℂ)
    (hc : Continuous χ) (hadd : ∀ x y, χ (x + y) = χ x * χ y) (h0 : χ 0 = 1) :
    ∃ ℓ : X →+ ℂ, Continuous ℓ ∧ ∀ x, χ x = exp (ℓ x) := by
  have he0 : e 0 = 0 := by simpa using he 0 0
  have hs0 : e.symm 0 = 0 := by rw [← he0, Homeomorph.symm_apply_apply]
  have hsadd : ∀ w w' : W, e.symm (w + w') = e.symm w + e.symm w' := by
    intro w w'
    apply e.injective
    rw [he, Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]
  obtain ⟨ℓ', hℓc, hℓ⟩ := lift_normed (fun w => χ (e.symm w)) (hc.comp e.symm.continuous)
    (fun w w' => by simp only [hsadd, hadd]) (by simp only [hs0, h0])
  refine ⟨AddMonoidHom.mk' (fun x => ℓ' (e x)) (fun x y => by simp only [he, map_add (f := _)]),
    hℓc.comp e.continuous, fun x => ?_⟩
  have h1 := hℓ (e x)
  simp only [Homeomorph.symm_apply_apply] at h1
  exact h1

theorem lift_place {F : Type} [Field F] (v : InfinitePlace F) (χ : v.Completion → ℂ)
    (hc : Continuous χ) (hadd : ∀ x y, χ (x + y) = χ x * χ y) (h0 : χ 0 = 1) :
    ∃ ℓ : v.Completion →+ ℂ, Continuous ℓ ∧ ∀ x, χ x = exp (ℓ x) := by
  rcases v.isReal_or_isComplex with hv | hv
  · exact lift_homeo (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hv).toHomeomorph
      (fun x y => map_add (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv) x y) χ hc hadd h0
  · exact lift_homeo (NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv).toHomeomorph
      (fun x y => map_add (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hv) x y) χ hc hadd h0

theorem addChar_sum {ι A : Type*} [AddCommMonoid A] (χ : AddChar A ℂ) (s : Finset ι) (f : ι → A) :
    χ (∑ i ∈ s, f i) = ∏ i ∈ s, χ (f i) := by
  classical
  refine Finset.induction_on s (by simp [AddChar.map_zero_eq_one]) ?_
  intro a s ha ih
  rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

end ChLiftW


open Classical in
def sgl {F : Type} [Field F] (v : InfinitePlace F) (t : v.Completion) : InfiniteAdeleRing F :=
  Pi.single v t

open Classical in
theorem sgl_add {F : Type} [Field F] (v : InfinitePlace F) (x y : v.Completion) :
    sgl v (x + y) = sgl v x + sgl v y :=
  Pi.single_add v x y

open Classical in
theorem sgl_zero {F : Type} [Field F] (v : InfinitePlace F) : sgl v (0 : v.Completion) = 0 :=
  Pi.single_zero v

open Classical in
theorem continuous_sgl {F : Type} [Field F] (v : InfinitePlace F) : Continuous (sgl v) :=
  continuous_single v

open Classical in
theorem sum_sgl {F : Type} [Field F] [NumberField F] (x : InfiniteAdeleRing F) :
    ∑ v, sgl v (x v) = x := by
  simp only [sgl]
  exact Finset.univ_sum_single x

open ChLiftW in
theorem chLift_holds : ChLift := by
  intro F _ _ χ hχ
  have key : ∀ v : InfinitePlace F, ∃ ℓ : v.Completion →+ ℂ, Continuous ℓ ∧
      ∀ t, χ (sgl v t) = exp (ℓ t) := by
    intro v
    exact lift_place v (fun t => χ (sgl v t)) (hχ.comp (continuous_sgl v))
      (fun x y => by simp only [sgl_add, AddChar.map_add_eq_mul]) (by simp only [sgl_zero, AddChar.map_zero_eq_one])
  choose ℓ hℓc hℓ using key
  refine ⟨AddMonoidHom.mk' (fun x => ∑ v, ℓ v (x v)) (fun x y => ?_), ?_, fun x => ?_⟩
  · rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← map_add (f := _)]
    rfl
  · exact continuous_finsetSum _ fun v _ => (hℓc v).comp (continuous_apply v)
  · show χ x = Complex.exp (∑ v, ℓ v (x v))
    conv_lhs => rw [← sum_sgl x]
    rw [ChLiftW.addChar_sum, Complex.exp_sum]
    exact Finset.prod_congr rfl fun v _ => hℓ v (x v)

end PI.VolStabSW
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.AdelicCharacterCondition

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

namespace PositivityTheory.jumpWindows

namespace AdelicCharacterCondition

theorem isCharAF_of {E : Type} [Field E] [NumberField E] {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF E ψ := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 E)
  have hb : M ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField E)
  obtain ⟨y, hy⟩ := hψ.loc ⟨M, hM.isPrime, hb⟩
  exact ⟨hψ.cont, hψ.norm, hψ.rat, _, hy⟩

theorem condAA {E : Type} [Field E] [NumberField E] {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) :
    ∀ᶠ v in (cofinite : Filter (HeightOneSpectrum (𝓞 E))), ∀ t : v.adicCompletion E,
      (∀ s ∈ v.adicCompletionIntegers E, ψ (sFin E (sLoc E v (s * t))) = 1) ↔ t ∈ v.adicCompletionIntegers E := by
  have h := _root_.PI.VolStabSW.VolAAW.condAA_of (_root_.PI.VolStabSW.VolAAW.condExact_of _root_.PI.VolStabSW.sAf_holds
    (_root_.PI.VolStabSW.chInf_of_lift _root_.PI.VolStabSW.chLift_holds)) E ψ (isCharAF_of hψ)
  filter_upwards [h] with v hv t
  simp only [sFin_sLoc_eq]
  exact hv t

end AdelicCharacterCondition

theorem adelic_character_holds : StandardCharacterExists := by
  intro E _ _ _
  obtain ⟨ψ, hψ⟩ := exists_stdPsi E
  refine ⟨ψ, hψ, ?_⟩
  filter_upwards [AdelicCharacterCondition.condAA hψ] with w hw
  have hint : ∀ y ∈ Ov E w, ψ (sFin E (sLoc E w y)) = 1 := by
    intro y hy
    have := (hw 1).2 (one_mem _) y hy
    rwa [mul_one] at this
  refine ⟨hint, ?_⟩
  set ϖ := _root_.PI.VolStabSW.unifV w with hϖ
  have hϖ0 : ϖ ≠ 0 := (_root_.PI.VolStabSW.unifV_spec w).1
  have hu : IsUnifV E w ϖ := _root_.PI.VolStabSW.unifV_val w
  have hnot : ϖ⁻¹ ∉ w.adicCompletionIntegers E := by
    intro h
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀] at h
    have hv : Valued.v ϖ = WithZero.exp (-1 : ℤ) := _root_.PI.VolStabSW.unifV_val w
    rw [hv] at h
    exact absurd h (by decide)
  have hex : ¬ ∀ s ∈ w.adicCompletionIntegers E, ψ (sFin E (sLoc E w (s * ϖ⁻¹))) = 1 :=
    fun h => hnot ((hw _).1 h)
  push Not at hex
  obtain ⟨s, hs, hne⟩ := hex
  refine ⟨ϖ, s * ϖ⁻¹, hu, ?_, hne⟩
  rw [mul_comm s, ← mul_assoc, mul_inv_cancel₀ hϖ0, one_mul]
  exact hs

end PositivityTheory.jumpWindows

end
end
end
