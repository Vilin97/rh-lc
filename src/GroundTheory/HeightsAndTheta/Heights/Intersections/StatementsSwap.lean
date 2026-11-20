import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsArith
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def SwapCycles.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ)
    (a a' : K → ℕ) (s s' : MRing ι),
    IsArithVar P d → IsMultiHomog s a → IsMultiHomog s' a' → s ∉ P → s' ∉ P →
    (∀ W, W ∈ divSupp P s → W ∉ divSupp P s') →
    (((fun W => ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s) W : ℤ))).sum fun W m => m • (fun W => ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle W s') W : ℤ))) =
      ((fun W => ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s') W : ℤ))).sum fun W m => m • ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle W s) def : ℤ) GeoNumCut.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (V : Ideal (MRing ι)) (n : ℕ)
    (a : Fin n → K → ℤ) (b : K → ℕ) (t : MRing ι),
    IsMultiProjPrime V → (charOf V).Prime →
    ringKrullDim (MRing ι ⧸ V) = ((n + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) →
    IsMultiHomog t b → t ∉ V →
    geoNum (n + 1) V (Fin.snoc a fun k => (b k : ℤ)) =
      ∑ᶠ U ∈ divSupp V t, (multAt (V ⊔ Ideal.span {t}) U : ℤ) * geoNum n U a

section Inhabitants

def fibTwo : Ideal (MRing (PBlk 2)) := Ideal.span {C 2}

end Inhabitants

end

end GroundTheory.Heights₂.Heights.Inter
