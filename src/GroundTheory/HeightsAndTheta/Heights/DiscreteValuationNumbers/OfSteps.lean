module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SpanTwoIsPrimeRelevant
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Statements
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsMaxHeight
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyCN
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.CycEvalEqAddMulOfCycle
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
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.MemMinimalPrimesOfDivCycleNeZero
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PConservationOfNumberLE
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsMultiHomogIdealSpanSingleton
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Cartier
import Mathlib.Tactic.TypeStar
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleFiniteSupport
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleMul
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericCycleCorresp
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericDimBound
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericFibProps
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PIntNumAddFirstField
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMaximalIdealHeightFG
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMinimalPrimeMultiHomog
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PRepresentative
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialQuotDim
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSupSpanMultiHomog
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Assembly

-- Source module: GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsAlt

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem EffectiveCase.proof (h₀ : NoCommonComponentCase.Statement.{u}) (h₁ : CommonFactorInduction.Statement.{u}) :
    EffectiveCase.Statement.{u} := by
  intro O _ _ _ ϖ hϖ

  suffices H : ∀ n : ℕ, ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
      [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
      ∀ (b : K → ℤ) (f g : MRing ι O), IsEffectiveVertical P ϖ b f g →
      ∀ (c : K → ℕ) (s : MRing ι O), IsMultiHomog s c → s ∉ P →
      (∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H → IsVerticalDivisor H ϖ b f g) →
      commonExcess ϖ P f g s = n → ∀ L : Fin d → K → ℤ, cutIdentity ϖ P b f g c s L by
    intro K _ _ ι _ P d hP b f g hD c s hs hsP hH L
    exact H _ K ι P d hP b f g hD c s hs hsP hH rfl L
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro K _ _ ι _ P d hP b f g hD c s hs hsP hH hn L
    by_cases hcom : ∃ G, (C ϖ : MRing ι O) ∈ G ∧ divCycle P s G ≠ 0 ∧ ratDiv P f g G ≠ 0
    · refine h₁ O ϖ hϖ K ι P d hP b f g hD c s hs hsP hH hcom ?_ L
      intro K' _ _ ι' _ P' d' hP' b' f' g' hD' c' s' hs' hsP' hH' hlt L'
      exact ih _ (hn ▸ hlt) K' ι' P' d' hP' b' f' g' hD' c' s' hs' hsP' hH' rfl L'
    · refine h₀ O ϖ hϖ K ι P d hP b f g hD c s hs hsP hH (fun G hG hsG => ?_) L
      by_contra hDG
      exact hcom ⟨G, hG, hsG, hDG⟩

end GroundTheory.Heights₂.Heights.NumbersDVR
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PCutByEffectiveDivisor

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem IsVerticalDivisor.uniformiser_pow_mul {K : Type*} [DecidableEq K] {ι : K → Type*}
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {H : Ideal (MRing ι O)}
    [hH : H.IsPrime] {ϖ : O} (hϖ : (C ϖ : MRing ι O) ∉ H) {b : K → ℤ} {f g : MRing ι O}
    (hD : IsVerticalDivisor H ϖ b f g) (n : ℕ) :
    IsVerticalDivisor H ϖ b (C ϖ ^ n * f) g := by
  obtain ⟨bf, bg, hf, hg, hb⟩ := hD.degrees
  refine IsVerticalDivisor.of_unit_off_special ⟨bf, bg, ?_, hg, hb⟩ ?_ hD.den_not_mem ?_
  · have h0 : IsMultiHomog (C ϖ ^ n : MRing ι O) 0 := by
      rw [← map_pow]
      exact isWeightedHomogeneous_C _ _
    have := h0.mul hf
    rwa [zero_add] at this
  · exact hH.mul_notMem (fun h => hϖ (hH.mem_of_pow_mem n h)) hD.num_not_mem
  · intro W hW hHW hrel hϖW
    obtain ⟨u, v, hu, hv, huv⟩ := hD.unit_off_special W hW hHW hrel hϖW
    refine ⟨u, C ϖ ^ n * v, hu, hW.mul_notMem (fun h => hϖW (hW.mem_of_pow_mem n h)) hv, ?_⟩
    have e : u * (C ϖ ^ n * f) - C ϖ ^ n * v * g = C ϖ ^ n * (u * f - v * g) := by ring
    rw [e]
    exact H.mul_mem_left _ huv

theorem CutByEffectiveDivisor.proof (h1 : EffectiveCase.Statement.{u})
    (h2 : UniformiserCase.Statement.{u}) (h3 : ShiftByUniformiser.Statement.{u})
    (h4 : EffectiveShift.Statement.{u}) : CutByEffectiveDivisor.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD c s hs hsP hH L
  obtain ⟨n, hEff⟩ := h4 O ϖ hϖ K ι P (d + 1) hP b f g hD
  have hH' : ∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H →
      IsVerticalDivisor H ϖ b (C ϖ ^ n * f) g := by
    intro H hsH hϖH
    have := (le_and_isRelevant_of_divCycle_ne_zero hsH).1
    exact (hH H hsH hϖH).uniformiser_pow_mul hϖH n
  have e1 := h1 O ϖ hϖ K ι P d hP b (C ϖ ^ n * f) g hEff c s hs hsP hH' L
  have e2 := h2 O ϖ hϖ K ι P d hP c s hs hsP L
  exact h3 O ϖ hϖ K ι P d hP b f g hD c s hs hsP hH L n e1 e2

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PEffectiveShift

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

theorem EffectiveShift.proof : EffectiveShift.Statement := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P e hP b f g hD
  classical
  have hPr : P.IsPrime := hP.multiProj.isPrime
  have hCP : (C ϖ : MRing ι O) ∉ P := by
    intro h
    have h' : ϖ ∈ P.comap (C : O →+* MRing ι O) := h
    rw [hP.noTorsion, Ideal.mem_bot] at h'
    exact hϖ.ne_zero h'

  let J : Ideal (MRing ι O) :=
    { carrier := {u | ∃ v, u * f - v * g ∈ P}
      add_mem' := by
        rintro a c ⟨v, hv⟩ ⟨w, hw⟩
        exact ⟨v + w, by convert P.add_mem hv hw using 1; ring⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c a ⟨v, hv⟩
        exact ⟨c * v, by convert P.mul_mem_left c hv using 1; simp only [smul_eq_mul]; ring⟩ }
  have hJ : ∀ u, u ∈ J ↔ ∃ v, u * f - v * g ∈ P := fun u => Iff.rfl
  have hPJ : P ≤ J := fun p hp => (hJ p).2 ⟨0, by simpa using P.mul_mem_right f hp⟩

  let 𝔞 : Ideal (MRing ι O) :=
    ∏ k : K, Ideal.span (Set.range fun i : ι k => (X ⟨k, i⟩ : MRing ι O))
  let I : Ideal (MRing ι O) := Ideal.span {(C ϖ : MRing ι O)} * 𝔞
  have hIJ : I ≤ J.radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf fun W hW => ?_
    obtain ⟨hJW, hWp⟩ := hW
    by_cases hϖW : (C ϖ : MRing ι O) ∈ W
    · exact Ideal.mul_le_left.trans ((Ideal.span_singleton_le_iff_mem W).2 hϖW)
    · have hrel : ¬ IsRelevant W := by
        intro hrel
        obtain ⟨u, v, hu, -, huv⟩ := hD.unit_off_special W hWp (hPJ.trans hJW) hrel hϖW
        exact hu (hJW ((hJ u).2 ⟨v, huv⟩))
      simp only [IsRelevant, not_forall, not_exists, not_not] at hrel
      obtain ⟨k, hk⟩ := hrel
      refine Ideal.mul_le_right.trans
        (Ideal.prod_le_inf.trans ((Finset.inf_le (Finset.mem_univ k)).trans ?_))
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact hk i
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hIJ (IsNoetherian.noetherian I)
  have hCN : (C ϖ : MRing ι O) ^ N ∉ P := fun h => hCP (hPr.mem_of_pow_mem N h)
  refine ⟨N, ?_, ?_⟩
  · obtain ⟨bf, bg, hf, hg, hb⟩ := hD.degrees
    refine IsVerticalDivisor.of_unit_off_special ⟨bf, bg, ?_, hg, hb⟩ ?_ hD.den_not_mem ?_
    · have h := (isWeightedHomogeneous_C (blockWeight ι) (ϖ ^ N)).mul hf
      rw [zero_add, map_pow] at h
      exact h
    · exact fun h => (hPr.mem_or_mem h).elim hCN hD.num_not_mem
    · intro W hW hPW hrel hϖW
      obtain ⟨u, v, hu, hv, huv⟩ := hD.unit_off_special W hW hPW hrel hϖW
      refine ⟨u, C ϖ ^ N * v, hu, ?_, ?_⟩
      · exact fun h => (hW.mem_or_mem h).elim (fun h' => hϖW (hW.mem_of_pow_mem N h')) hv
      · convert P.mul_mem_left (C ϖ ^ N) huv using 1; ring
  · intro W hW hPW hrel
    choose i hi using hrel
    have hz : (∏ k, (X ⟨k, i k⟩ : MRing ι O)) ∉ W := by
      rw [hW.prod_mem_iff]
      rintro ⟨k, -, hk⟩
      exact hi k hk
    have hz𝔞 : (∏ k, (X ⟨k, i k⟩ : MRing ι O)) ∈ 𝔞 :=
      Ideal.prod_mem_prod fun k _ => Ideal.subset_span ⟨i k, rfl⟩
    have hmem : (C ϖ * ∏ k, (X ⟨k, i k⟩ : MRing ι O)) ^ N ∈ J :=
      hN (Ideal.pow_mem_pow (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hz𝔞) N)
    obtain ⟨v, hv⟩ := (hJ _).1 hmem
    refine ⟨(∏ k, (X ⟨k, i k⟩ : MRing ι O)) ^ N, v, fun h => hz (hW.mem_of_pow_mem N h), ?_⟩
    convert hv using 1
    ring

end GroundTheory.Heights₂.Heights.NumbersDVR
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.OfSteps

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

theorem DivCycleMul.full : DivCycleMul.Statement.{u} := DivCycleMul.proof

theorem DivCycleFiniteSupport.full : DivCycleFiniteSupport.Statement.{u} :=
  DivCycleFiniteSupport.proof

theorem SupSpanMultiHomog.full : SupSpanMultiHomog.Statement.{u} := SupSpanMultiHomog.proof

theorem MinimalPrimeMultiHomog.full : MinimalPrimeMultiHomog.Statement.{u} :=
  MinimalPrimeMultiHomog.proof

theorem SpecialQuotDim.full : SpecialQuotDim.Statement.{u} := SpecialQuotDim.proof

theorem MaximalIdealHeightFG.full : MaximalIdealHeightFG.Statement.{u} := MaximalIdealHeightFG.proof

theorem GenericDimBound.full : GenericDimBound.Statement.{u} :=
  GenericDimBound.proof MaximalIdealHeightFG.full

theorem GenericFibProps.full : GenericFibProps.Statement.{u} := GenericFibProps.proof

theorem GenericCycleCorresp.full : GenericCycleCorresp.Statement.{u} := GenericCycleCorresp.proof

theorem ConservationOfNumberLE.full : ConservationOfNumberLE.Statement.{u} :=
  ConservationOfNumberLE.proof IntNumAssoc.full SpecialCycleEval.full SpecialPieceRank.full
    GenericPieceRank.full SpecialIdealMultiHomog.full

theorem UniformiserCase.full : UniformiserCase.Statement.{u} :=
  UniformiserCase.proof ConservationOfNumberLE.full GenericDimBound.full GenericFibProps.full
    GenericCycleCorresp.full MinimalPrimeMultiHomog.full SupSpanMultiHomog.full DimStrictDrop.full
    CutByForm.full

theorem ShiftByUniformiser.full : ShiftByUniformiser.Statement.{u} :=
  ShiftByUniformiser.proof DivCycleMul.full DivCycleFiniteSupport.full

theorem EffectiveShift.full : EffectiveShift.Statement.{u} := EffectiveShift.proof

theorem Representative.full : Representative.Statement.{u} := Representative.proof DivCycleMul.full

theorem IntNumAddFirst.full : IntNumAddFirst.Statement.{u} :=
  IntNumAddFirst.proof FieldNumbers.IntNumAdd.full FieldNumbers.IntNumZeroSlot.full
    FieldNumbers.HilbDegreeBound.full

theorem EffectiveCase.of_steps (h₀ : NoCommonComponentCase.Statement.{u}) (h₁ : CommonFactorInduction.Statement.{u}) :
    EffectiveCase.Statement.{u} :=
  EffectiveCase.proof h₀ h₁

theorem CutByEffectiveDivisor.of_steps (h₀ : NoCommonComponentCase.Statement.{u})
    (h₁ : CommonFactorInduction.Statement.{u}) : CutByEffectiveDivisor.Statement.{u} :=
  CutByEffectiveDivisor.proof (EffectiveCase.of_steps h₀ h₁) UniformiserCase.full
    ShiftByUniformiser.full EffectiveShift.full

end GroundTheory.Heights₂.Heights.NumbersDVR
end
end
