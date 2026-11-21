import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IrreducibleCharacterSeries.ConjugateCharacterFormula
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimpleIffIrreducibleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SeparableIrreducibleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralIdempotentPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TraceCompLeftFunLeft
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IrreducibleCharacterSeries.FrobeniusSumFormula
import GroundTheory.AutomorphicForms.FiniteBruhat
import Formalism.PadicSubsetSums.CentralIdempotents.IsConstituent
import Formalism.PadicSubsetSums.CentralIdempotents.GaloisConjCentralIdempotent
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimpleIffIrreducible
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GreenLabelSurjective.Simple
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PatternGroupStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasLabelTransportEquiv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalWhittaker
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalOfUnipotentSumsVanishStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCuspidalWithLabelStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalLabelUniqueStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalParametrization

open Polynomial CategoryTheory
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal

noncomputable section

namespace ReciprocityTheory.Ty.Fin

section Gen

variable {Γ : Type} [Group Γ] [Fintype Γ]

theorem isIrr_of_simple (τ : FDRep ℂ Γ) [h : Simple τ] : IsIrr τ.ρ := (GlobalTheory.T.simple_iff_irreducible.1 Γ τ).1 h

theorem zIdemIdemCentral_holds (Γ : Type) [Group Γ] [Fintype Γ] (τ : FDRep ℂ Γ) (hτ : Simple τ) :
    zIdem τ * zIdem τ = zIdem τ ∧ ∀ a, zIdem τ * a = a * zIdem τ := GlobalTheory.T.central_idempotent_properties.1 Γ τ hτ

theorem zIdemOrthogonal_holds (Γ : Type) [Group Γ] [Fintype Γ] (τ σ : FDRep ℂ Γ) (hτ : Simple τ) (hσ : Simple σ)
    (h : ¬ Nonempty (τ ≅ σ)) : zIdem τ * zIdem σ = 0 := GlobalTheory.T.central_idempotent_properties.2.1 Γ τ σ hτ hσ h

end Gen

section GeneralLinearIntegers

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

variable (K) in

variable (K) in

variable (K) in

variable (K) in

variable (K) in

end GeneralLinearIntegers

end ReciprocityTheory.Ty.Fin
