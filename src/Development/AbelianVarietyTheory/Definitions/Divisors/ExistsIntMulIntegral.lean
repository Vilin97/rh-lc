import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne

noncomputable section

open NumberField Matrix Polynomial

namespace GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime] (D : Datum p)

def Datum.skewFun (x y : D.La) : Module.Dual ℚ D.F :=
  (integralBasis D.F).constr ℚ fun k => ((D.EF (D.smulF (RingOfIntegers.basis D.F k) x) y : ℤ) : ℚ)

theorem Datum.EF_swap (x y : D.La) : D.EF y x = - D.EF x y := by
  have h := D.alt (x + y)
  simp only [map_add, LinearMap.add_apply, D.alt, zero_add, add_zero] at h
  linarith

def Datum.Kq : Subfield D.F := (IntermediateField.adjoin ℚ {(D.ω : D.F)}).toSubfield

section Places

variable {F : Type} [Field F] [NumberField F] (Kq : Subfield F) (u : Kq →+* ℚ_[p])

end Places

section Examples

variable {p : ℕ} [Fact p.Prime] (D : Datum p)

end Examples

end GlobalTheory.UPel.HT
