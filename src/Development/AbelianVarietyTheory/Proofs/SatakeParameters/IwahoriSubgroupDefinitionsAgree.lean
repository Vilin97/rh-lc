import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import CompanionTheory.EightfoldTheory.VariationTheory.PublishedTheorems.ImportsAlt
import CompanionTheory.EightfoldTheory.VariationTheory.SelfDualForms.SelfDualWeylChambers.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FoundBridge
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IwahoriDoubleCosets
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.HolCap
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.ExistsIdele
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.HolLin
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.ExpInj
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.ExpUnique
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.KLocal
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.DirChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CharVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.ArchBd
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.LiftEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.LiftSm
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.LiftLie
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.LiftCent
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.OrthCases
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.LiftCT
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CuspCrit
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.LiftExp
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.HkCoef
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.InfGLScalar
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.SatComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.SatHol
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.SatOfVec
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import GroundTheory.AutomorphicForms.AffineBruhat
open GlobalTheory.IwFn GlobalTheory.SmGL GlobalTheory.TfJl ValuativeRel Matrix

namespace GlobalTheory.IwEq

theorem iwahori_eq_glnLocal_iwahori : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (a : ℕ),
    iwahori k (Fin a) = GroundTheory.Automorphic.GLnLocal.iwahori k a := by
  intro k _ _ _ _ a
  ext g
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, mem_borel] at hu
    refine ⟨u, ?_, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_comap, GroundTheory.Automorphic.mem_borel_iff]
      intro i j hij
      rw [GroundTheory.Automorphic.GLnLocal.residueReduction_apply]
      exact hu i j hij
    · ext i j
      rfl
  · rintro ⟨u, hu, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, GroundTheory.Automorphic.mem_borel_iff] at hu
    refine ⟨u, ?_, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_comap, mem_borel]
      intro i j hij
      have h := hu i j hij
      rw [GroundTheory.Automorphic.GLnLocal.residueReduction_apply] at h
      exact h
    · ext i j
      rfl

end GlobalTheory.IwEq
