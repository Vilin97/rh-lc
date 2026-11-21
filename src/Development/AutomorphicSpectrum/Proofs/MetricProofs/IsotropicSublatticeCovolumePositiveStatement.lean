module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsotropicSublatticeCovolumePositive
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement

@[expose] public section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropic_sublattice_covolume_positive : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (R : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (I : Submodule (𝓞 E) Λ), IsCMFam σ → IsIsoSub R.form I → I ≠ ⊥ → (∃ r v, IsNzFamily I r v) ∧ ∀ r v, IsNzFamily I r v → R.nz σ I = R.nzOf σ I v ∧ 0 < R.nz σ I ∧ r = Module.finrank (𝓞 E) I := by
  intro E _ _ _ g Λ _ _ Ψ _ R σ I hσ hI hne
  have := R.free
  have := R.fin
  have hFamily : ∃ r v, IsNzFamily I r v := LevelTowerAlt.exists_family hne
  refine ⟨hFamily, fun r v hv => ?_⟩
  have hEq : R.nz σ I = R.nzOf σ I v := by
    rw [RiemLat.nz, dite_eq_left hFamily]
    exact LevelTowerAlt.nzOf_eq R hσ hv hFamily.choose_spec.choose_spec
  exact ⟨hEq, hEq.symm ▸ LevelTowerAlt.nzOf_pos R σ hI hv, LevelTowerAlt.family_rank hv⟩
