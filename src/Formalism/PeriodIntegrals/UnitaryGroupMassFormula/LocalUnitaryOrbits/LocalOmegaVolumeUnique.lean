module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.SdVolHOfPerf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.TrPerfOfRes
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.OmLocUOfOnto
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.UnitaryOrbitCounting
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.UnitNormOfRes
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.TrOntoHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.GramInvOHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.EtaSpHolds
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.OmFibreUniq
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SelfDualContinuity.SdExistsHolds

@[expose] public section

noncomputable section

namespace PI.OmLocU.Done

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU

theorem local_omega_volume_unique {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E)) (a : ℕ) (Y : TupV (E := E) v n a)
    (hSd : StdHyp σ J ψ → (∃ μ, SdW F E σ n J (Fv F v) (psiV F ψ v) a μ) ∧
      ∃ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν)
    (hOm : OmUnique σ J ψ v a) :
    Formalism.L2.SG.Pf.NcLoc.OmLocU σ J ψ v Λ a Y := by
  have hR : Red.ResAlg σ J ψ v := Red.resAlg_of_sp σ J ψ v (Red.etaSp_holds σ J ψ v)
  have hUN := UnN.unitNorm_of_res σ J ψ v Λ hR
  have hP : SdB.TrPerf σ J ψ v := SdB.trPerf_of_res σ J ψ v hR
  intro hS
  exact omLocU_of_tr σ J ψ v Λ a Y hSd hOm (UnitaryOrbitCounting.orbAll_of_res σ J ψ v Λ a Y hR hUN)
    (gramInvO_holds σ J v Λ ψ a Y) (Red.trOnto_holds σ J ψ v hS) (UnitaryOrbitCounting.countU_of_res' σ J ψ v Λ a Y hR hUN)
    (SdB.sdVolW_of_perf σ J ψ v Λ a hP) (SdB.sdVolH_of_perf σ J ψ v a hP) hS

theorem omLocU_closed {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E)) (a : ℕ) (Y : TupV (E := E) v n a) :
    Formalism.L2.SG.Pf.NcLoc.OmLocU σ J ψ v Λ a Y :=
  local_omega_volume_unique σ J ψ v Λ a Y
    (fun hS => ⟨(PI.SelfDualBridge.W.sdExists_holds σ J ψ v a (Fin 1) hS).1,
      (PI.SelfDualBridge.W.sdExists_holds σ J ψ v a (Fin 1) hS).2.1⟩)
    (omUnique σ J ψ v a)

end PI.OmLocU.Done
