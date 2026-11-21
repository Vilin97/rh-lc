module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.AuxiliaryPrimeFunction
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriDoubleCosetTorusNilpotent
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAddCharConductorMaxIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeedOrbKVanish
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IwahoriSubgroupDefinitionsAgree
public import Development.AutomorphicArithmetic.IwahoriCommensurability.IsCommensuratedIwahoriGl

@[expose] public section

open Formalism.UG

theorem UpperTheory.isCommensurated_iwahoriSubgroup_gl_fin :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ), Formalism.UG.IsCommensurated (GlobalTheory.SmGL.iwahori k (Fin n)) := by
  intro k _ _ _ _ n
  rw [GlobalTheory.IwEq.iwahori_eq_glnLocal_iwahori k n]
  exact UpperTheory.isCommensurated_iwahori_gl k n
