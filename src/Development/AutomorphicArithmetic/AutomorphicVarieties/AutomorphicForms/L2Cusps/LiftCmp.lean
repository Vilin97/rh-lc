module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.AbsCompactAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.QuotMk

@[expose] public section

open MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GlobalTheory.DiscSpec
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum

theorem UpperTheory.V.KernelIndexFullLattice.liftCmp_holds :
    UpperTheory.V.KernelIndexFullLattice.LiftCmp := by
  intro E _ _ _ a μ _ μ₁ _ hp v Φ hΦ
  have hcmp : (UpperTheory.V.KernelIndexFullLattice.cmp hp v : Quot (latticeGL E a) → ℂ)
      =ᵐ[quotMeasure (latticeGL E a) μ] (toLp μ₁ v) ∘ UpperTheory.V.KernelIndexFullLattice.quotMap E a :=
    Lp.coeFn_compMeasurePreserving (toLp μ₁ v) hp
  have hquot := hcmp.trans (hp.quasiMeasurePreserving.ae hΦ)
  filter_upwards [ae_quotMeasure_iff.1 hquot] with g hg
  rw [← UpperTheory.V.KernelIndexFullLattice.quotMk_holds E a g]
  exact hg
