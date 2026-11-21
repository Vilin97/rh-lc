import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped ComplexConjugate

namespace GlobalTheory.CompanionTheory.Ar.HS.Tuple

section Tuple

open ReciprocityTheory.ChartRestriction.G.T0 (TVar OmS sImg)

variable (K : Type) [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  {Ω : Type} [Field Ω] [Algebra K Ω]

open Classical in

def sphP (n : ℕ) : Measure (Metric.sphere (0 : EuclideanSpace ℂ (Fin n)) 1) :=
  ((volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere Set.univ)⁻¹ • (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere

open Classical in

end Tuple

end GlobalTheory.CompanionTheory.Ar.HS.Tuple
