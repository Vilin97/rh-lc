import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.LB.SheafModel

variable {X : Scheme.{0}} {L : LB X}

section ProjectiveLine

open GlobalTheory.ProjSpace

variable (R : Type) [CommRing R] [IsDomain R]

def genericPt : PSpace R 1 :=
  (⟨⊥, Ideal.isPrime_bot, fun h => by
    have : (MvPolynomial.X 0 : MvPolynomial (Fin 2) R) ∈ (⊥ : Ideal (MvPolynomial (Fin 2) R)) :=
      h (HomogeneousIdeal.mem_irrelevant_of_mem _ one_pos (X_mem R 1 0))
    exact X_ne_zero _ (Ideal.mem_bot.1 this)⟩ : ProjectiveSpectrum (grading R 1))

theorem genericPt_mem {f : MvPolynomial (Fin 2) R} (hf : f ≠ 0) :
    genericPt R ∈ Proj.basicOpen (grading R 1) f :=
  fun h => hf (Ideal.mem_bot.1 h)

theorem exists_const (i : Fin 2) (u : Γ(PSpace R 1, chart R 1 i)ˣ) :
    ∃ c : R, c ≠ 0 ∧ (u : Γ(PSpace R 1, chart R 1 i)) = algebraMap R _ c := by
  have h : IsUnit ((chartAlgEquiv R 1 i).symm u) := u.isUnit.map _
  obtain ⟨c, hc, e⟩ := isUnit_iff_eq_C_of_isReduced.1 h
  refine ⟨c, hc.ne_zero, ?_⟩
  rw [← (chartAlgEquiv R 1 i).apply_symm_apply u, e]
  exact (chartAlgEquiv R 1 i).commutes c

theorem not_exists_gen : ¬ ∃ t : LB.Gen (O1 R 1), t.IsGen := by
  rintro ⟨t, ht⟩
  obtain ⟨c₀, h₀, e₀⟩ := exists_const R 0 (t.s (0 : Fin 2))
  obtain ⟨c₁, h₁, e₁⟩ := exists_const R 1 (t.s (1 : Fin 2))
  let W : (PSpace R 1).Opens := chart R 1 0 ⊓ chart R 1 1
  have hW : W ≤ chart R 1 0 := inf_le_left
  have e : resG _ hW (t.s (0 : Fin 2)).val = ratioOn W 0 hW 1 *
      resG _ (inf_le_right : W ≤ chart R 1 1) (t.s (1 : Fin 2)).val :=
    congrArg Units.val (ht (0 : Fin 2) (1 : Fin 2))
  rw [e₀, e₁, resG_algebraMap, resG_algebraMap] at e
  have hf : (C c₀ * MvPolynomial.X 0 - C c₁ * MvPolynomial.X 1 :
      MvPolynomial (Fin 2) R).IsHomogeneous 1 :=
    ((isHomogeneous_X R 0).C_mul c₀).sub ((isHomogeneous_X R 1).C_mul c₁)
  have hz : formOn W 0 hW 1 _ hf = 0 := by
    rw [formOn_eq_aeval]
    simp only [map_sub, map_mul, aeval_C, aeval_X, ratioOn_self, mul_one]
    rw [e, mul_comm, sub_self]
  have hb := basicOpen_formOn (U := W) (hi := hW) hf
  rw [hz, Scheme.basicOpen_zero] at hb
  have hne : (C c₀ * MvPolynomial.X 0 - C c₁ * MvPolynomial.X 1 : MvPolynomial (Fin 2) R) ≠ 0 := by
    intro h
    have := congrArg (eval ![1, 0]) h
    simp at this
    exact h₀ this
  exact hb.ge (⟨⟨genericPt_mem R (X_ne_zero 0), genericPt_mem R (X_ne_zero 1)⟩,
    genericPt_mem R hne⟩ : genericPt R ∈ W ⊓ _)

omit [IsDomain R] in

omit [IsDomain R] in

omit [IsDomain R] in

omit [IsDomain R] in

end ProjectiveLine

end GlobalTheory.LB.SheafModel
