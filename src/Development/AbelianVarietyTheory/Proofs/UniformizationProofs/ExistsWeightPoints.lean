module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPointRepresentingWeightMumfordQuotient
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.MumfordTowerRepWtMulAdd
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.MumfordTowerRepWtUnique
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPointRepresentingWeightMumfordQuotientStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_point_representing_weight_mumfordQuotient : Laws → AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg), KTriv a.B a.M.L.L → ∀ χ : s.X, ∃ c : 𝟙_ _ ⟶ a.B, ∀ e, a.RepWt c χ e := by
  first | exact @GlobalTheory.exists_point_repWt | exact GlobalTheory.exists_point_repWt | (intros; apply GlobalTheory.exists_point_repWt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.MumfordTowerRepWtMulAddStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.mumfordTower_repWt_mul_add : AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg) (χ χ' : s.X) (c c' : 𝟙_ _ ⟶ a.B) (e : ℕ), a.RepWt c χ e → a.RepWt c' χ' e → a.RepWt (c * c') (χ + χ') e := by
  first | exact @GlobalTheory.UU.repWt_add | exact GlobalTheory.UU.repWt_add | (intros; apply GlobalTheory.UU.repWt_add <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.MumfordTowerRepWtUniqueStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.mumfordTower_repWt_unique : Laws → AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg), KTriv a.B a.M.L.L → ∀ (χ : s.X) (c c' : 𝟙_ _ ⟶ a.B), (∀ e, a.RepWt c χ e) → (∀ e, a.RepWt c' χ e) → c = c' := by
  first | exact @GlobalTheory.UU.repWt_unique | exact GlobalTheory.UU.repWt_unique | (intros; apply GlobalTheory.UU.repWt_unique <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsWeightPoints

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UU

theorem exists_weightPoints : Laws → AllSet fun s => ∀ (t : Tower s) (a : t.Alg), KTriv a.B a.M.L.L → ∃ c : s.X → (𝟙_ _ ⟶ a.B), (∀ χ χ', c (χ + χ') = c χ * c χ') ∧ ∀ χ e, a.RepWt (c χ) χ e := by
  intro hL V _ _ _ A G _ _ s
  have h1 := GlobalTheory.T.exists_point_representing_weight_mumfordQuotient hL V A G s
  have h2 := GlobalTheory.T.mumfordTower_repWt_unique hL V A G s
  have h3 := GlobalTheory.T.mumfordTower_repWt_mul_add V A G s
  intro t a hK
  choose c hc using h1 t a hK
  refine ⟨c, fun χ χ' => ?_, hc⟩
  exact h2 t a hK (χ + χ') _ _ (hc _) fun e => h3 t a χ χ' _ _ e (hc χ e) (hc χ' e)

end GlobalTheory.UU
end
end
