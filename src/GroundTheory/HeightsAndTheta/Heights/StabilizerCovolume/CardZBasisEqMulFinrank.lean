import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Covolume
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.ThreeLeLevel
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.GaussCM
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.DataHodge
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.IsFrameOverLine
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Values
import GroundTheory.HeightsAndTheta.Heights.Intersections.Statements
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField NumberField.ComplexEmbedding GroundTheory.Heights₂.Heights.LowerBoundFree
  Module Matrix
open scoped Matrix ComplexConjugate Kronecker

section Tower

variable {Em : Type} [Field Em] [NumberField Em]

def towerZBasis {M : Type} [AddCommGroup M] [Module (𝓞 Em) M] {ρ : ℕ} {v : Fin ρ → M}
    (hv : LinearIndependent (𝓞 Em) v) :
    Basis (Fin ρ × (Em →+* ℂ)) ℤ (Submodule.span (𝓞 Em) (Set.range v)) :=
  ((RingOfIntegers.basis Em).smulTower' (Basis.span hv)).reindex
    (Equiv.prodCongr (Equiv.refl _) (equivReindex Em).symm)

theorem towerZBasis_apply {M : Type} [AddCommGroup M] [Module (𝓞 Em) M] {ρ : ℕ} {v : Fin ρ → M}
    (hv : LinearIndependent (𝓞 Em) v) (p : Fin ρ × (Em →+* ℂ)) :
    (towerZBasis hv p : M) = RingOfIntegers.basis Em (equivReindex Em p.2) • v p.1 := by
  simp [towerZBasis, Basis.smulTower'_apply, Basis.span_apply]

open Classical in

end Tower

namespace FullerData

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)] {Em : Type} [Field Em] [NumberField Em] [IsCMField Em]
  (D : FullerData II Ψ K ι Ω E Em)

open Classical in

open Classical in

end FullerData

end GroundTheory.Heights₂.Heights.NineStatements
