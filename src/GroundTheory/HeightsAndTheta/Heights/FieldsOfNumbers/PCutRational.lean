import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open GroundTheory.Heights₂.Heights.NumbersDVR

universe u

theorem divCycle_support_finite {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K]
    {ι : K → Type} [∀ k, Fintype (ι k)] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)) (f : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι) :
    (Function.support ((fun W => ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P f) W : ℤ)))).Finite := by
  apply (Ideal.finite_minimalPrimes_of_isNoetherianRing (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)
    (P ⊔ Ideal.span {f})).subset
  intro W hW
  by_contra h
  apply hW
  simp only [divCycle]
  rw [dite_eq_right (fun h' => h h'.1)]

theorem cycEval_ratDiv {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K]
    {ι : K → Type} [∀ k, Fintype (ι k)] (N : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι) → ℤ) (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι))
    (f g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι) :
    cycEval N (ratDiv P f g) = cycEval N ((fun W => ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P f) W : ℤ))) - cycEval N ((fun W => ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P g) W : ℤ))) := by
  simp only [cycEval, ratDiv, sub_mul]
  apply finsum_sub_distrib
  · exact (divCycle_support_finite P f).subset (Function.support_mul_subset_left _ _)
  · exact (divCycle_support_finite P g).subset (Function.support_mul_subset_left _ _)

theorem CutRational.proof (h1 : CutRegular.Statement.{u}) (h2 : IntNumAdd.Statement.{u}) :
    CutRational.Statement.{u} := by
  intro F _ K _ _ ι _ P hP n hn bf bg f g hf hg hfP hgP bs
  have hadd := h2 F K ι P hP.multiHomog hP.relevant (n + 1) hn
    (Fin.snoc (α := fun _ => K → ℤ) bs 0) (Fin.last n)
    (fun k => (bf k : ℤ) - bg k) (fun k => (bg k : ℤ))
  simp only [Fin.update_snoc_last] at hadd
  have hsum : ((fun k => (bf k : ℤ) - bg k) + fun k => (bg k : ℤ)) = fun k => (bf k : ℤ) := by
    funext k; simp
  rw [hsum, h1 F K ι P hP n hn bf f hf hfP bs, h1 F K ι P hP n hn bg g hg hgP bs] at hadd
  rw [cycEval_ratDiv]
  linarith

end GroundTheory.Heights₂.Heights.FieldNumbers
