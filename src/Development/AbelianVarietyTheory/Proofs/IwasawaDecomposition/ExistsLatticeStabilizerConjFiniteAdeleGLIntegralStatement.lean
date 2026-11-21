module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLatticeStabilizerConjFiniteAdeleGLIntegral
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteVolumeAdelicUnitaryQuotient
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.BorelGL
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.LatticeIdealNonzero

@[expose] public section

open NumberField IsDedekindDomain Matrix MeasureTheory Topology
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lattice_stabilizer_conj_finiteAdeleGL_integral : ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (s : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)), ∃ Λ : Submodule (𝓞 F) (Fin n → F), Submodule.IsLattice F Λ ∧ ∀ γ : GL (Fin n) F, (∀ y, (γ : Matrix (Fin n) (Fin n) F) *ᵥ y ∈ Λ ↔ y ∈ Λ) → s⁻¹ * PIW.ClassFinD.glIncl F n γ * s ∈ PIW.ClassFinD.KGL F n := by
  first | exact @GlobalTheory.StabLat.exists_lattice_stab_conj | exact GlobalTheory.StabLat.exists_lattice_stab_conj | (intros; apply GlobalTheory.StabLat.exists_lattice_stab_conj <;> assumption)
