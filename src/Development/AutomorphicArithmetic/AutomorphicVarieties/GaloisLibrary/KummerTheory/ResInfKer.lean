import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.CobOfGen
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ExistsGen
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ResInfInj
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.QzBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.NonemptyH0GlobalEquivGaloisImage
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.PrincTop
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.CyclotomicTotient.TotientLeOfCycPowEqOne

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

section Index

variable {R Γ M : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ] [AddCommGroup M] [Module R M]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] (ρ : Representation R Γ M)
  (H : Subgroup Γ) (hH : ∀ g g', g ∉ H → g' ∉ H → g * g' ∈ H)
include hH

private theorem val_eq (z : Z1 ρ) (hz : ∀ g ∈ H, z.1 g = 0) {g g' : Γ} (hg : g ∉ H) (hg' : g' ∉ H) :
    z.1 g' = z.1 g := by
  have h := z.2.2 g (g⁻¹ * g')
  rw [hz _ (hH _ _ (fun h => hg (H.inv_mem_iff.1 h)) hg'), map_zero, add_zero, mul_inv_cancel_left] at h
  exact h

end Index
