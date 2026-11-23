module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.ThickFrames
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeProjectorNewformGaloisImageStatement
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsZetaTW
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ZetaUr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UntwistedRepresentationOrdinaryTriangularShape
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.AdmissibleFunctionalOfProjection
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.AqBdPlace
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.CgAppr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.CgpTrans
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.ChiQuad
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.ChiQuadAlt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeLetterPreservesBasisSetStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerBAdmissibleHeckeCommuteStatement
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.CoefUb
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.EulerSystemNorms
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.FinSuppCompLift
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.FormPLamSmul
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.JEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.RhoFrob
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.SgDOneMem

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.UntwistedRepresentationOrdinaryTriangularShapeStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.CyclotomicQExpansion
open scoped Matrix MatrixGroups

theorem _root_.GlobalTheory.T.untwisted_representation_ordinary_triangular_shape : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (S : Finset Pl)
    (A : ValuationSubring Ω) (W : R2 Ω l) (g : Newform (2 * e + 1)) (ψ : ZMod l → Qbar l),
  Nf e S A W → SrcUr ι e A W g →
  (∃ χ : G ℚ Ω →* (Qbar l)ˣ, KillsMu l χ ∧
    (∀ s ∈ Ine (F := ℚ) A, mat W s 1 1 * (cycBar ℚ Ω l s : Qbar l) ^ (e : ℤ) * ((dt W s : Qbar l)⁻¹ * (χ s : Qbar l)) = 1) ∧
    ∀ s : G ℚ Ω, (χ s : Qbar l) = ψ ((((cycMod (F := ℚ) (Ω := Ω) l 1 s : ZMod (l ^ 1))).val : ℕ) : ZMod l)) →
  ∃ ρ : (Ω ≃ₐ[ℚ] Ω) →* GL (Fin 2) (Qbar l),
    (∀ s, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) = rhoK W e ψ s) ∧ Continuous ρ ∧
    (∀ s ∈ Dec (F := ℚ) A, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 1 0 = 0) ∧
    (∀ s ∈ Ine (F := ℚ) A, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 1 1 = 1) ∧
    ∃ F : Finset Ω, ∀ s ∈ Ine (F := ℚ) A, (∀ y ∈ F, s y = y) →
      (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 0 0 = ((cycZ ℚ Ω l s : ℤ_[l]) : Qbar l) ^ (2 * e) := by
  first | (exact @GlobalTheory.RhoAdm.rho_ordinary_shape) | (exact GlobalTheory.RhoAdm.rho_ordinary_shape) | (intros; apply GlobalTheory.RhoAdm.rho_ordinary_shape  <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.ChiStab

section

@[expose] public section

open UpperTheory.V.Z.Kato.Joint

theorem UpperTheory.V.Z.Kato.Joint.chiStab :
    UpperTheory.V.Z.Kato.Joint.ChiStab := by
  intro l hp Ω _ _ _ ε X N w χ hl hlN hN hw T b hT hb
  have hNl : Nat.Coprime N l := ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hlN).symm
  obtain ⟨φ, h1, h2⟩ := X.j_hol
  refine ⟨GlobalTheory.T.hecke_letter_preserves_basis_set ε X ε.injective ⟨φ, h2, h1⟩ N l w hl hN hNl hw T hT b hb.1, fun d hd => ?_⟩
  have h := GlobalTheory.T.modularTowerB_admissibleHecke_commute ε X ε.injective ⟨φ, h2, h1⟩ N l w hl hN hNl hw T (GlobalTheory.KZ.Letter.D d) hT hd b hb.1
  change X.op N l T (X.diam N l d b) = X.diam N l d (X.op N l T b) at h
  rw [← h, hb.2 d hd, map_smul]
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.RhoFrobAlt

section

@[expose] public section

open UpperTheory.V.Z.Kato.Joint

theorem UpperTheory.V.Z.Kato.Joint.rhoFrob :
    UpperTheory.V.Z.Kato.Joint.RhoFrob := by
  intro l _ Ω _ _ _ ι e S A W g χ hN _ hatt ρ hρ
  have h : ∀ s, (ρ s : Matrix (Fin 2) (Fin 2) (Formalism.ConjugateSelfDual.Qbar l)) = _ := fun s =>
    (hρ s).trans (GlobalTheory.RhoAdm.untw_val' e W χ s).symm
  refine ⟨?_, fun V hV => GlobalTheory.RhoAdm.untw_irr e W χ hN.irr V fun s v hv => ?_⟩
  · obtain ⟨S0, hS0⟩ := GlobalTheory.RhoAdm.frob_trace_det ι e W g χ hatt
    refine ⟨S0, fun q hq hqS s hs => ?_⟩
    rw [h s]
    exact hS0 q hq hqS s hs
  · rw [← h s]
    exact hV s v hv
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.KatoGlobalAdmissibilityOfAdmissible

section

@[expose] public section

namespace UpperTheory.V.Z.Kato.Joint

theorem kato_global_admissibility_of_admissible (hA : AdmTop) : AdmFR := by
  have hK : NewformPartOfTowerModule := fun {Ω} _ _ _ ε X => GlobalTheory.T.heckeProjector_newform_galoisImage ε X
  have hR : AdmRho := GlobalTheory.T.untwisted_representation_ordinary_triangular_shape
  exact admissibleFunctional_of_projection hA hK hR jEx rhoFrob unif LocFacts₂ finP coefUb thLin thOp chiStab thP lamEig2 chiQuad aqBd

end UpperTheory.V.Z.Kato.Joint
end
end
