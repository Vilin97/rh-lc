module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairNumSectionCut
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CycleListPermInvariantStatement
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.DivisorCycleListAdditiveStatement
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.HomogeneousClassSubstitutionStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily

@[expose] public section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem divCycle_support_finite {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)) (f : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) : (Function.support ((fun W => ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P f) W : ℤ)))).Finite := by
  haveI : IsNoetherianRing (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) := by
    unfold ReciprocityTheory.ChartRestriction.G.Geo.MRingOver refine infer_instance (Ideal.finite_minimalPrimes_of_isNoetherianRing (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) (P ⊔ Ideal.span {f})).subset ?_
  intro W hW
  by_contra hn
  apply hW
  unfold ReciprocityTheory.ChartRestriction.G.Geo.divCycle
  rw [dite_eq_right]
  exact fun h => hn h.1

theorem cycList_ratDiv {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)) (f g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) (l : List (K → ℤ)) :
    cycList (ratDiv P f g) l = cycList ((fun W => ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P f) W : ℤ))) l - cycList ((fun W => ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P g) W : ℤ))) l := by
  have e : ratDiv P f g = divCycle P f - (fun W => ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P g) W : ℤ)) := rfl
  unfold cycList
  rw [e]
  exact (cycEval_sub_cycle _ _ _ (divCycle_support_finite P f) (divCycle_support_finite P g)).symm

theorem cycNum_subst_of_add {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (Z : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) → ℤ) (d : ℕ)
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

theorem cycNum_linear_subst : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)) (d : ℕ), IsModelOver P d → ∀ (a a' : K → ℕ) (f g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), IsMultiHomog f a → IsMultiHomog g a' → f ∉ P → g ∉ P → ∀ (σ σ' : Type) [Fintype σ] (cls : σ → K → ℤ) (M : σ' → σ → ℤ) (H : MvPolynomial σ' ℝ) (m : ℕ), H.IsHomogeneous m → ∀ Q : List (K → ℤ), m + Q.length = d → cycNum (ratDiv P f g) (fun t => ∑ i, M t i • cls i) H Q = cycNum (ratDiv P f g) cls (aeval (fun t => ∑ i, (C (M t i : ℝ) * X i : MvPolynomial σ ℝ)) H) Q ∧ cycNum ((fun W => ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P f) W : ℤ))) (fun t => ∑ i, M t i • cls i) H Q = cycNum ((fun W => ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P f) W : ℤ))) cls (aeval (fun t => ∑ i, (C (M t i : ℝ) * X i : MvPolynomial σ ℝ)) H) Q := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP a a' f g hf hg hfP hgP σ σ' _ cls M H m hH Q hQ
  have af := GlobalTheory.T.divisor_cycle_list_additive O ϖ hϖ K ι P d hP a f hf hfP
  have ag := GlobalTheory.T.divisor_cycle_list_additive O ϖ hϖ K ι P d hP a' g hg hgP
  refine ⟨cycNum_subst_of_add _ d (fun b b' l h => ?_) cls M H m hH Q hQ,
    cycNum_subst_of_add _ d (af · · · ·) cls M H m hH Q hQ⟩
  rw [cycList_ratDiv, cycList_ratDiv, cycList_ratDiv, af b b' l h, ag b b' l h]
  ring

end GlobalTheory.CompanionTheory.Ar.Num
