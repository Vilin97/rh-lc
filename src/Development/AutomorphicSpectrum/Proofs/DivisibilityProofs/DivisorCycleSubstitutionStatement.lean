module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CycleListPermInvariant
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
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.VerticalNumberZeroOfHorizontalStatement
public import Development.WeilBound.CoreStatements.IdealCycleValues.IntNumLCons
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyCN
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.OfSteps
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.WithBotLtOfAddOneLe
import Mathlib.Tactic.Linter.Style
public import Mathlib.Basic.Real.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Development.WeilBound.CoreStatements.IdealCycleValues.ProdMapToMultiset
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairNumSectionCut
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CycleListPermInvariantStatement

section

@[expose] public section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

theorem _root_.GlobalTheory.T.cycle_list_perm_invariant : (∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (V : Ideal (MRing ι F)) (l l' : List (K → ℤ)), l.Perm l' → intNumL F V l = intNumL F V l') ∧ (∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Z : Ideal (MRing ι O) → ℤ) (l l' : List (K → ℤ)), l.Perm l' → cycList Z l = cycList Z l') := by
  exact GlobalTheory.CompanionTheory.Ar.Num.numbers_list_perm
end
end

-- Source module: Development.WeilBound.CoreStatements.IdealCycleValues.CycListAdditiveFirstClass

section

@[expose] public section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

theorem BaseChangeColon.cycList_additive_first_class : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d → ∀ (a : K → ℕ) (f : MRing ι O), IsMultiHomog f a → f ∉ P → ∀ (b b' : K → ℤ) (l : List (K → ℤ)), l.length + 1 = d → cycList (divCycle P f) ((b + b') :: l) = cycList (divCycle P f) (b :: l) + cycList (divCycle P f) (b' :: l) := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP a f hf hfP b b' l hl
  have hPp : P.IsPrime := hP.multiProj.isPrime
  unfold cycList
  refine AdditivityInDivisor.cycEval_add_fn (DivCycleFiniteSupport.full O K ι P f) fun W hW => ?_
  by_cases hϖW : (C ϖ : MRing ι O) ∈ W
  · have hWmin : W ∈ (P ⊔ Ideal.span {f}).minimalPrimes := by
      unfold divCycle at hW
      split_ifs at hW with h
      · exact h.1
      · exact absurd rfl hW
    have hWp : W.IsPrime := hWmin.1.1
    have hPW : P ≤ W := le_sup_left.trans hWmin.1.2
    have hWh : IsMultiHomogIdeal W := MinimalPrimeMultiHomog.full O K ι _ W
      (SupSpanMultiHomog.full O K ι P f a hP.multiProj.multiHomog hf) hWmin
    have hfW : f ∈ W := hWmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
    have hlt : P < W := lt_of_le_of_ne hPW fun h => hfP (h ▸ hfW)
    have hdim := DimStrictDrop.full (MRing ι O) P W hlt
    rw [hP.dim, ← SpecialQuotDim.full O ϖ hϖ K ι W hϖW,
      show d + 1 + Fintype.card K = l.length + 2 + Fintype.card K by omega] at hdim
    have key := IntNumAddFirst.full _ K ι l.length (specialIdeal W)
      (SpecialIdealCorresp.full O ϖ hϖ K ι P W hWp hϖW).1 (SpecialIdealMultiHomog.full O K ι W hWh)
      (AdditivityInDivisor.withBot_lt_of_add_one_le hdim) b b' l.get
    rw [← BaseChangeColon.intNumL_cons, ← BaseChangeColon.intNumL_cons, ← BaseChangeColon.intNumL_cons] at key
    exact key
  · have h0 := GlobalTheory.T.vertical_number_zero_of_horizontal O ϖ hϖ K ι P d hP a f hf hfP W hW hϖW
    show vNumL W _ = vNumL W _ + vNumL W _
    rw [h0 _ (by simpa using hl), h0 _ (by simpa using hl), h0 _ (by simpa using hl), add_zero]
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.DivisorCycleListAdditive

section

@[expose] public section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem cycList_divCycle_add_first : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d → ∀ (a : K → ℕ) (f : MRing ι O), IsMultiHomog f a → f ∉ P → ∀ (b b' : K → ℤ) (l : List (K → ℤ)), l.length + 1 = d → cycList (divCycle P f) ((b + b') :: l) = cycList (divCycle P f) (b :: l) + cycList (divCycle P f) (b' :: l) := by
  exact @BaseChangeColon.cycList_additive_first_class

end GlobalTheory.CompanionTheory.Ar.Num
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.DivisorCycleListAdditiveStatement

section

@[expose] public section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

theorem _root_.GlobalTheory.T.divisor_cycle_list_additive : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d → ∀ (a : K → ℕ) (f : MRing ι O), IsMultiHomog f a → f ∉ P → ∀ (b b' : K → ℤ) (l : List (K → ℤ)), l.length + 1 = d → cycList (divCycle P f) ((b + b') :: l) = cycList (divCycle P f) (b :: l) + cycList (divCycle P f) (b' :: l) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.cycList_divCycle_add_first | exact GlobalTheory.CompanionTheory.Ar.Num.cycList_divCycle_add_first | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.cycList_divCycle_add_first <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.IdealCycleValues.HomogeneousSumLinearChangeClasses

section

@[expose] public section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

theorem BaseChangeColon.homogeneous_sum_linear_change_classes : ∀ (G : Type) [AddCommGroup G] (d : ℕ) (n : List G → ℝ), (∀ l l', l.Perm l' → n l = n l') → (∀ b b' l, l.length + 1 = d → n ((b + b') :: l) = n (b :: l) + n (b' :: l)) → ∀ (σ σ' : Type) [Fintype σ] (cls : σ → G) (M : σ' → σ → ℤ) (H : MvPolynomial σ' ℝ) (m : ℕ), H.IsHomogeneous m → ∀ Q : List G, m + Q.length = d → (∑ μ ∈ H.support, H.coeff μ * n ((μ.toMultiset.map fun t => ∑ i, M t i • cls i).toList ++ Q)) = ∑ μ ∈ (aeval (fun t => ∑ i, (C (M t i : ℝ) * X i : MvPolynomial σ ℝ)) H).support, (aeval (fun t => ∑ i, (C (M t i : ℝ) * X i : MvPolynomial σ ℝ)) H).coeff μ * n ((μ.toMultiset.map cls).toList ++ Q) := by
  intro G _ d n hperm hadd σ σ' _ cls M H m hH Q hQ
  exact (BaseChangeColon.subst_abs d n hperm hadd cls M H m hH Q hQ).trans
    (BaseChangeColon.evL_eq _ _).symm
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.HomogeneousClassSubstitution

section

@[expose] public section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem subst_abs_list : ∀ (G : Type) [AddCommGroup G] (d : ℕ) (n : List G → ℝ), (∀ l l', l.Perm l' → n l = n l') → (∀ b b' l, l.length + 1 = d → n ((b + b') :: l) = n (b :: l) + n (b' :: l)) → ∀ (σ σ' : Type) [Fintype σ] (cls : σ → G) (M : σ' → σ → ℤ) (H : MvPolynomial σ' ℝ) (m : ℕ), H.IsHomogeneous m → ∀ Q : List G, m + Q.length = d → (∑ μ ∈ H.support, H.coeff μ * n ((μ.toMultiset.map fun t => ∑ i, M t i • cls i).toList ++ Q)) = ∑ μ ∈ (aeval (fun t => ∑ i, (C (M t i : ℝ) * X i : MvPolynomial σ ℝ)) H).support, (aeval (fun t => ∑ i, (C (M t i : ℝ) * X i : MvPolynomial σ ℝ)) H).coeff μ * n ((μ.toMultiset.map cls).toList ++ Q) := by
  exact @BaseChangeColon.homogeneous_sum_linear_change_classes

end GlobalTheory.CompanionTheory.Ar.Num
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.HomogeneousClassSubstitutionStatement

section

@[expose] public section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

theorem _root_.GlobalTheory.T.homogeneous_class_substitution : ∀ (G : Type) [AddCommGroup G] (d : ℕ) (n : List G → ℝ), (∀ l l', l.Perm l' → n l = n l') → (∀ b b' l, l.length + 1 = d → n ((b + b') :: l) = n (b :: l) + n (b' :: l)) → ∀ (σ σ' : Type) [Fintype σ] (cls : σ → G) (M : σ' → σ → ℤ) (H : MvPolynomial σ' ℝ) (m : ℕ), H.IsHomogeneous m → ∀ Q : List G, m + Q.length = d → (∑ μ ∈ H.support, H.coeff μ * n ((μ.toMultiset.map fun t => ∑ i, M t i • cls i).toList ++ Q)) = ∑ μ ∈ (aeval (fun t => ∑ i, (C (M t i : ℝ) * X i : MvPolynomial σ ℝ)) H).support, (aeval (fun t => ∑ i, (C (M t i : ℝ) * X i : MvPolynomial σ ℝ)) H).coeff μ * n ((μ.toMultiset.map cls).toList ++ Q) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.subst_abs_list | exact GlobalTheory.CompanionTheory.Ar.Num.subst_abs_list | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.subst_abs_list <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.DivisorCycleSubstitution

section

@[expose] public section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem divCycle_support_finite {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι O)) (f : MRing ι O) : (Function.support (divCycle P f)).Finite := by
  haveI : IsNoetherianRing (MRing ι O) := by
    unfold MRing
    infer_instance
  refine (Ideal.finite_minimalPrimes_of_isNoetherianRing (MRing ι O) (P ⊔ Ideal.span {f})).subset ?_
  intro W hW
  by_contra hn
  apply hW
  unfold divCycle
  rw [dite_eq_right]
  exact fun h => hn h.1

theorem cycList_ratDiv {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι O)) (f g : MRing ι O) (l : List (K → ℤ)) :
    cycList (ratDiv P f g) l = cycList (divCycle P f) l - cycList (divCycle P g) l := by
  have e : ratDiv P f g = divCycle P f - divCycle P g := rfl
  unfold cycList
  rw [e]
  exact (cycEval_sub_cycle _ _ _ (divCycle_support_finite P f) (divCycle_support_finite P g)).symm

theorem cycNum_subst_of_add {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (Z : Ideal (MRing ι O) → ℤ) (d : ℕ)
    (hadd : ∀ (b b' : K → ℤ) (l : List (K → ℤ)), l.length + 1 = d →
      cycList Z ((b + b') :: l) = cycList Z (b :: l) + cycList Z (b' :: l))
    {σ σ' : Type} [Fintype σ] (cls : σ → K → ℤ) (M : σ' → σ → ℤ) (H : MvPolynomial σ' ℝ) (m : ℕ)
    (hH : H.IsHomogeneous m) (Q : List (K → ℤ)) (hQ : m + Q.length = d) :
    cycNum Z (fun t => ∑ i, M t i • cls i) H Q =
      cycNum Z cls (aeval (fun t => ∑ i, (C (M t i : ℝ) * X i : MvPolynomial σ ℝ)) H) Q :=
  GlobalTheory.T.homogeneous_class_substitution (K → ℤ) d (fun l => (cycList Z l : ℝ))
    (fun l l' h => by rw [GlobalTheory.T.cycle_list_perm_invariant.2 O K ι Z l l' h])
    (fun b b' l h => by rw [hadd b b' l h]; push_cast; rfl)
    σ σ' cls M H m hH Q hQ

theorem cycNum_linear_subst : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d → ∀ (a a' : K → ℕ) (f g : MRing ι O), IsMultiHomog f a → IsMultiHomog g a' → f ∉ P → g ∉ P → ∀ (σ σ' : Type) [Fintype σ] (cls : σ → K → ℤ) (M : σ' → σ → ℤ) (H : MvPolynomial σ' ℝ) (m : ℕ), H.IsHomogeneous m → ∀ Q : List (K → ℤ), m + Q.length = d → cycNum (ratDiv P f g) (fun t => ∑ i, M t i • cls i) H Q = cycNum (ratDiv P f g) cls (aeval (fun t => ∑ i, (C (M t i : ℝ) * X i : MvPolynomial σ ℝ)) H) Q ∧ cycNum (divCycle P f) (fun t => ∑ i, M t i • cls i) H Q = cycNum (divCycle P f) cls (aeval (fun t => ∑ i, (C (M t i : ℝ) * X i : MvPolynomial σ ℝ)) H) Q := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP a a' f g hf hg hfP hgP σ σ' _ cls M H m hH Q hQ
  have af := GlobalTheory.T.divisor_cycle_list_additive O ϖ hϖ K ι P d hP a f hf hfP
  have ag := GlobalTheory.T.divisor_cycle_list_additive O ϖ hϖ K ι P d hP a' g hg hgP
  refine ⟨cycNum_subst_of_add _ d (fun b b' l h => ?_) cls M H m hH Q hQ,
    cycNum_subst_of_add _ d (af · · · ·) cls M H m hH Q hQ⟩
  rw [cycList_ratDiv, cycList_ratDiv, cycList_ratDiv, af b b' l h, ag b b' l h]
  ring

end GlobalTheory.CompanionTheory.Ar.Num
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.DivisorCycleSubstitutionStatement

section

@[expose] public section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

theorem _root_.GlobalTheory.T.divisor_cycle_substitution : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d → ∀ (a a' : K → ℕ) (f g : MRing ι O), IsMultiHomog f a → IsMultiHomog g a' → f ∉ P → g ∉ P → ∀ (σ σ' : Type) [Fintype σ] (cls : σ → K → ℤ) (M : σ' → σ → ℤ) (H : MvPolynomial σ' ℝ) (m : ℕ), H.IsHomogeneous m → ∀ Q : List (K → ℤ), m + Q.length = d → cycNum (ratDiv P f g) (fun t => ∑ i, M t i • cls i) H Q = cycNum (ratDiv P f g) cls (aeval (fun t => ∑ i, (C (M t i : ℝ) * X i : MvPolynomial σ ℝ)) H) Q ∧ cycNum (divCycle P f) (fun t => ∑ i, M t i • cls i) H Q = cycNum (divCycle P f) cls (aeval (fun t => ∑ i, (C (M t i : ℝ) * X i : MvPolynomial σ ℝ)) H) Q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.cycNum_linear_subst | exact GlobalTheory.CompanionTheory.Ar.Num.cycNum_linear_subst | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.cycNum_linear_subst <;> assumption)
end
end
