module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.AdmissibleResidualTameEigenvalues
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.TrivialLocalCondition
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsobaricDiscreteSelfDualStrongMultiplicityOne
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepthZeroLabelsOfLabelLaws
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.TameGeneratorResidual

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFrobeniusConjInertiaPowModWild

section

@[expose] public section

noncomputable section

namespace GlobalTheory.TameRel

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem wild_conj {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {s u : G E Ω} (hs : s ∈ Dec (F := E) A)
    (hu : ∀ y : Ω, y ≠ 0 → A.valuation (u y / y - 1) < 1) :
    ∀ y : Ω, y ≠ 0 → A.valuation ((s * u * s⁻¹) y / y - 1) < 1 := by
  intro y hy
  set z := (s⁻¹ : G E Ω) y with hz
  have hsz : s z = y := mul_inv_apply y
  have hz0 : z ≠ 0 := by
    intro h; apply hy; rw [← hsz, h, map_zero]
  have e : (s * u * s⁻¹) y / y - 1 = s (u z / z - 1) := by
    rw [map_sub, map_div₀, map_one, hsz]
    rfl
  rw [e, GlobalTheory.TameLabels.valuation_apply_of_mem_Dec hs]
  exact hu z hz0

end GlobalTheory.TameRel

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem GlobalTheory.TameRel.main : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N) (k : Fin 2) (v : N.PlG k), ∀ γ ∈ Ine (F := H.E) (N.plOm.1 (A.plGw k v)), ∃ φ : G H.E N.Om, φ * γ * φ⁻¹ * (γ ^ H.g k)⁻¹ ∈ Ine (F := H.E) (N.plOm.1 (A.plGw k v)) ∧ φ * γ * φ⁻¹ * (γ ^ H.g k)⁻¹ ∈ wildSet N (N.plOm.1 (A.plGw k v)) := by
  intro R H what₂ N A k v γ hγ
  obtain ⟨φ, hφ⟩ := exists_isFrob (N.plOm.2 (A.plGw k v))
  rw [GlobalTheory.TameLabels.normV_eq_of_split (H.g_prime k) (N.g_split k) (A.plGw_over k v)] at hφ
  refine ⟨φ, ?_, ?_⟩
  · exact Subgroup.mul_mem _ (conj_mem_Ine hφ.1 hγ) (Subgroup.inv_mem _ (Subgroup.pow_mem _ hγ _))
  · have hu := GlobalTheory.TameLabels.wild_of_frob hγ hφ
    have hs : γ ^ H.g k ∈ Dec (F := H.E) (N.plOm.1 (A.plGw k v)) :=
      (Dec (F := H.E) _).pow_mem (Ine_le_Dec _ hγ) _
    have h := GlobalTheory.TameRel.wild_conj hs hu
    have e : γ ^ H.g k * ((γ ^ H.g k)⁻¹ * (φ * γ * φ⁻¹)) * (γ ^ H.g k)⁻¹ = φ * γ * φ⁻¹ * (γ ^ H.g k)⁻¹ := by
      group
    rw [e] at h
    exact h
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFrobeniusConjInertiaPowModWildStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.exists_frobenius_conj_inertia_pow_mod_wild : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N) (k : Fin 2) (v : N.PlG k), ∀ γ ∈ Ine (F := H.E) (N.plOm.1 (A.plGw k v)), ∃ φ : G H.E N.Om, φ * γ * φ⁻¹ * (γ ^ H.g k)⁻¹ ∈ Ine (F := H.E) (N.plOm.1 (A.plGw k v)) ∧ φ * γ * φ⁻¹ * (γ ^ H.g k)⁻¹ ∈ wildSet N (N.plOm.1 (A.plGw k v)) := by
  first | exact @GlobalTheory.TameRel.main | exact GlobalTheory.TameRel.main | (intros; apply GlobalTheory.TameRel.main <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReductionTrivialOnWildInertia

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.rbar_wild_inertia_of_labTame_repAtGN : ∀ (D : D7), GlobalTheory.RowCopy.RbarTie D → _root_.UpperTheory.GalS.LabTameS D.nd D.naut → _root_.UpperTheory.GalS.RowRepAtGN D → ∀ (σ : D.what₂.FT) (k : Fin 2) (v : D.nd.PlG k) (i : D.nd.Loc), D.nd.l i ≠ D.host.g k → D.what₂.isot (D.nd.j i) σ ≠ ⊥ → D.nd.goodRow σ → ∀ s ∈ Ine (F := D.host.E) (D.nd.plOm.1 (D.naut.plGw k v)), s ∈ wildSet D.nd (D.nd.plOm.1 (D.naut.plGw k v)) → D.ntypes.rbar σ (D.nd.w i) s = 1 := by
  first | exact @_root_.GlobalTheory.RowWildTame.main_alt | exact _root_.GlobalTheory.RowWildTame.main_alt | (intros; apply _root_.GlobalTheory.RowWildTame.main_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TameGeneratorResidual

section

@[expose] public section



section
noncomputable section
namespace GlobalTheory.ResidualTame
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
end GlobalTheory.ResidualTame
namespace GlobalTheory.RowWildTame
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
end GlobalTheory.RowWildTame
namespace GlobalTheory.RowTie
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
theorem tameGenerator_residual_alt_alt (D : D7) (h1 : GlobalTheory.RowCopy.RbarTie D) (h2 : GlobalTheory.RowTie.IotaRed D)
    (h3 : _root_.UpperTheory.GalS.LabTameS D.nd D.naut) (h4 : _root_.UpperTheory.GalS.RowRepAtGN D) :
    GlobalTheory.RowCopy.JointOccurrenceCondition D := by
  intro σ k v _ _ i hl hne hg
  refine ⟨_root_.GlobalTheory.ResidualTame.cpAt' D h1 h2 h3 h4 σ k v i hl hne hg, ?_⟩
  obtain ⟨φ, hI, hW⟩ := GlobalTheory.T.exists_frobenius_conj_inertia_pow_mod_wild _ _ _ D.nd D.naut k v _ (D.ntypes.tg_mem k v)
  refine ⟨φ, ?_⟩
  have h := _root_.GlobalTheory.T.rbar_wild_inertia_of_labTame_repAtGN D h1 h3 h4 σ k v i hl hne hg _ hI hW
  rw [map_mul, map_inv, map_pow, mul_inv_eq_one] at h
  exact h
end GlobalTheory.RowTie
end
end
end
end
