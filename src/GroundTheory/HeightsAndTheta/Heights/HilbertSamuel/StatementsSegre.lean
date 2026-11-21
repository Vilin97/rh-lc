module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsMultiDegreePositive
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

variable {K : Type} [Fintype K] {ι : K → Type} (F : Type) [Field F]

def segreMap : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F (fun _ : Unit => ∀ k, ι k) →ₐ[F] ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι :=
  aeval fun v => ∏ k, X ⟨k, v.2 k⟩

def segrePrime (q : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)) : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F (fun _ : Unit => ∀ k, ι k)) :=
  q.comap (segreMap F)

theorem segreMap_X (f : ∀ k, ι k) :
    segreMap F (X ⟨(), f⟩ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F (fun _ : Unit => ∀ k, ι k)) = ∏ k, X ⟨k, f k⟩ :=
  aeval_X _ _

instance segrePrime.isPrime (q : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)) [q.IsPrime] : (segrePrime F q).IsPrime :=
  Ideal.comap_isPrime _ _

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
