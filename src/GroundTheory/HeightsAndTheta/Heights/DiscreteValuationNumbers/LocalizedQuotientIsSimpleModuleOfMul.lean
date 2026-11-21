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

def ResidualComparison.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (b : K → ℤ) (f g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), IsEffectiveVertical P ϖ b f g →
    ∀ (c : K → ℕ) (s : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), IsMultiHomog s c → s ∉ P →
    (∀ H, ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s) H : ℤ) ≠ 0 → (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) ∉ H → IsVerticalDivisor H ϖ b f g) →
    ∀ e : K → ℕ, (∀ k, (c k : ℤ) = b k + e k) →
    ∀ m : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι, IsMultiHomog m e → m ∉ P →
    (∀ H, ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s) H : ℤ) ≠ 0 → (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) ∉ H → m ∉ H) →
    ∀ G' : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O (extIdx ι (BlowUpIdx ι))),
      (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O (extIdx ι (BlowUpIdx ι))) ∈ G' →
      0 < ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle (blowUpOf P (blowUpGens s g f m e)) (liftForm s)) G' : ℤ) →
      0 < ratDiv (blowUpOf P (blowUpGens s g f m e)) (newVar (some none)) (liftForm m) G' →
      ∃ G : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) ∈ G ∧
        ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle (blowUpOf P (blowUpGens s g f m e)) (liftForm s)) G' : ℤ) ≤ ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s) G : ℤ) ∧
        ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle (blowUpOf P (blowUpGens s g f m e)) (liftForm s)) G' : ℤ) +
            ratDiv (blowUpOf P (blowUpGens s g f m e)) (newVar (some none)) (liftForm m) G' ≤
          ratDiv P f g G

def ExceptionalComparison.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (b : K → ℤ) (f g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), IsEffectiveVertical P ϖ b f g →
    ∀ (c : K → ℕ) (s : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), IsMultiHomog s c → s ∉ P →
    (∀ H, ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s) H : ℤ) ≠ 0 → (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) ∉ H → IsVerticalDivisor H ϖ b f g) →
    ∀ e : K → ℕ, (∀ k, (c k : ℤ) = b k + e k) →
    ∀ m : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι, IsMultiHomog m e → m ∉ P →
    (∀ H, ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s) H : ℤ) ≠ 0 → (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) ∉ H → m ∉ H) →
    ∀ G' : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O (extIdx ι (BlowUpIdx ι))),
      (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O (extIdx ι (BlowUpIdx ι))) ∈ G' →
      0 < ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle (blowUpOf P (blowUpGens s g f m e)) (newVar none)) G' : ℤ) →
      0 < ratDiv (blowUpOf P (blowUpGens s g f m e)) (liftForm (f * m))
        (liftForm g * newVar (some none)) G' →
      ∃ G : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) ∈ G ∧
        ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle (blowUpOf P (blowUpGens s g f m e)) (newVar none)) G' : ℤ) +
            ratDiv (blowUpOf P (blowUpGens s g f m e)) (liftForm (f * m))
              (liftForm g * newVar (some none)) G' ≤ ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s) G : ℤ) ∧
        ratDiv (blowUpOf P (blowUpGens s g f m e)) (liftForm (f * m))
            (liftForm g * newVar (some none)) G' ≤ ratDiv P f g G

end Lemmas

section Examples

section Simple

variable {A : Type*} [CommRing A]

end Simple

theorem form_mem_of_divCycle_ne_zero {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]
    {P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι)} {x : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι} {W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι)} (h : ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P x) W : ℤ) ≠ 0) : x ∈ W := by
  unfold ReciprocityTheory.ChartRestriction.G.Geo.divCycle at h
  split_ifs at h with hW
  · exact hW.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x))
  · exact absurd rfl h

section Constants

set_option linter.unusedSectionVars false

variable {K : Type} {ι : K → Type} {J : Type} {O : Type*} [CommRing O] [IsDomain O]

theorem liftForm_const (a : O) : liftForm (J := J) (C a : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) = C a :=
  (liftForm (J := J) (ι := ι) (R := O)).commutes a

end Constants

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
