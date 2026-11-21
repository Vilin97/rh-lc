module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.AbsCompactAlt
public import GroundTheory.AutomorphicForms.L2LocalComponents

@[expose] public section

theorem UpperTheory.V.KernelIndexFullLattice.dense_holds :
    UpperTheory.V.KernelIndexFullLattice.Dense :=
  fun _ _ _ _ μ₁ _ => GroundTheory.Automorphic.CuspidalSpectrum.topologicalClosure_map_centralCuspForms μ₁
