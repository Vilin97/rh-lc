module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CechPic GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.AV.LTors GlobalTheory.PDivGroup GlobalTheory.Dieu
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IsogParam

def zpW (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] : ℤ_[p] →+* WittVector p k :=
  (WittVector.map (ZMod.castHom (dvd_refl p) k)).comp (WittVector.equiv p).symm.toRingHom

section

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k]

variable {O : Type} [Ring O] {star : O ≃+* Oᵐᵒᵖ} {A₀ : AbVar k} {ι₀ : O →+* End A₀} {c₀ : Pic A₀.X.left}

variable (p) in

variable [CharP k p] [PerfectRing k p]

end

end GlobalTheory.IsogParam
