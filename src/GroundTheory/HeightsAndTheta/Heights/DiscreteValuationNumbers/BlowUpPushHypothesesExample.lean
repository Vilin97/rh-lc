module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.CutIdentityRightSideCongrOfSubMem
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Lemmas

def BlowUpVerticalPush.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)) (n : ℕ), IsModelOver P n →
    ∀ (N : K → ℕ) (u : J → ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    ∀ (c : K → ℕ) (x : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), IsMultiHomog x c → x ∉ P →
    ∀ a : Fin n → K → ℤ,
      (open Classical in
        cycEval (fun W => if (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O (extIdx ι J)) ∈ W then vNum W (liftDegs a) else 0)
          ((fun W => ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle (blowUpOf P u) (liftForm x)) W : ℤ)))) =
      (open Classical in
        cycEval (fun W => if (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) ∈ W then vNum W a else 0) ((fun W => ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P x) W : ℤ))))

def BlowUpDivisorPush.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)) (n : ℕ), IsModelOver P n →
    ∀ (b : K → ℤ) (f g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), IsVerticalDivisor P ϖ b f g →
    ∀ (N : K → ℕ) (u : J → ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    ∀ a : Fin n → K → ℤ,
      cycEval (fun G => vNum G (liftDegs a)) (ratDiv (blowUpOf P u) (liftForm (J := J) f) (liftForm g)) =
        cycEval (fun G => vNum G a) (ratDiv P f g)

def BlowUpHorizontalCorresp.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)) (n : ℕ), IsModelOver P n →
    ∀ (N : K → ℕ) (u : J → ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    (∀ W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), W.IsPrime → P ≤ W → IsRelevant W → (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) ∉ W →
      ∃ j, ∀ j', ∃ v w : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι, v ∉ W ∧ v * u j' - w * u j ∈ P) →
    ∀ (c : K → ℕ) (x : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), IsMultiHomog x c → x ∉ P →
    (∀ h : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) → ℤ,
      (open Classical in
        cycEval (fun W => if (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O (extIdx ι J)) ∈ W then 0
            else h (W.comap (liftForm (ι := ι) (J := J) (R := O))))
          ((fun W => ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle (blowUpOf P u) (liftForm x)) W : ℤ)))) =
      (open Classical in
        cycEval (fun W => if (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) ∈ W then 0 else h W) ((fun W => ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P x) W : ℤ))))) ∧
    ∀ W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O (extIdx ι J)), ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle (blowUpOf P u) (liftForm x)) W : ℤ) ≠ 0 →
      (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O (extIdx ι J)) ∉ W →
      ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P x) (W.comap (liftForm (ι := ι) (J := J) (R := O))) : ℤ) ≠ 0 ∧
      ((∃ j, u j ∉ W.comap (liftForm (ι := ι) (J := J) (R := O))) →
        W = blowUpOf (W.comap (liftForm (ι := ι) (J := J) (R := O))) u)

def HorizontalComponentModel.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (c : K → ℕ) (x : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P x) W : ℤ) ≠ 0 → (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) ∉ W → IsModelOver W d

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
