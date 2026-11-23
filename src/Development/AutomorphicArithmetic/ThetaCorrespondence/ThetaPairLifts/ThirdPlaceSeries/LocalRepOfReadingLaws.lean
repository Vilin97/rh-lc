module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Laws
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AlgebraicModularFormsHeckeModulesIsoAllPlacesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeDEqSum
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SatUOfFixed
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Formalism.AlgebraicWeights.InertDatumExists
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNonsplitPlaceWithInertDatum
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
public import ReciprocityTheory.Automorphisms.SplitCoeAlgebraMap
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSplitPlaceOfSplitPlaceRealSubfieldHost
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Formalism.SatakeDualWeyl.StatementF
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitarySatakeEqOfSameUnramifiedBaseChange
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import ReciprocityTheory.Automorphisms.PlaceA
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.SphRead
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MAvGood

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.AlgebraicModularFormsStrongMultiplicityOne

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.GlobDet

theorem main : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S₁ S₂ : Submodule ℂ (GAf L n → a.W)) (h₁ : NG.IsIrrRep a.ρ S₁) (h₂ : NG.IsIrrRep a.ρ S₂), (∀ s : SplitPlace L, ∃ σ₁ σ₂ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)), IsLocS S₁ s σ₁ ∧ IsLocS S₂ s σ₂ ∧ Nonempty (σ₁.ρ.Equiv σ₂.ρ)) → (∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)), (∀ s : SplitPlace L, s.v ≠ v) → ∃ (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ), NG.OverPl w v ∧ NG.SatAt { a with S := S₁, irrS := h₁ } Dv α ∧ NG.SatAt { a with S := S₂, irrS := h₂ } Dv α) → NG.IsoRep S₁ S₂ := by
  intro L _ _ _ n a S₁ S₂ h₁ h₂ hsplit hinert
  obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h₁.2.1
  obtain ⟨N, hN, hNf⟩ := (h₁.1.le hf).2
  have hfix : ∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f := fun κ hκ => funext fun g => hNf κ hκ g
  obtain ⟨φ, hφ1, hφ2, hφ3⟩ := GlobalTheory.T.algebraicModularForms_heckeModules_iso_all_places L n a S₁ S₂ h₁ h₂ hsplit (fun v hv => by
    obtain ⟨w, Dv, α, hw, hs1, hs2⟩ := hinert v hv
    have k1 : ∃ f ∈ S₁, f ≠ 0 ∧ ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ f = f := by
      obtain ⟨f, hf, hf0, U, hfU, hU, -⟩ := hs1
      exact ⟨f, hf, hf0, fun κ hκ ht => hfU κ ((hU κ ht).2 hκ)⟩
    have k2 : ∃ f ∈ S₂, f ≠ 0 ∧ ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ f = f := by
      obtain ⟨f, hf, hf0, U, hfU, hU, -⟩ := hs2
      exact ⟨f, hf, hf0, fun κ hκ ht => hfU κ ((hU κ ht).2 hκ)⟩
    exact ⟨w, Dv, α, hw, k1, k2, fun U hU h hh =>
      ⟨fun f hf hfU => GlobalTheory.InertSph.satU_of_fixed L n a S₁ h₁ v w Dv α hw hs1 U hU f hf hfU h hh,
       fun f hf hfU => GlobalTheory.InertSph.satU_of_fixed L n a S₂ h₂ v w Dv α hw hs2 U hU f hf hfU h hh⟩⟩) N hN ⟨f, hf, hfix, hf0⟩
  exact GlobalTheory.HeckeRecon.recon L n a a S₁ S₂ h₁ h₂ N hN φ hφ1 hφ2 hφ3

end GlobalTheory.GlobDet
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.AlgebraicModularFormsStrongMultiplicityOneStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.algebraic_modular_forms_strong_multiplicity_one : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S₁ S₂ : Submodule ℂ (GAf L n → a.W)) (h₁ : NG.IsIrrRep a.ρ S₁) (h₂ : NG.IsIrrRep a.ρ S₂), (∀ s : SplitPlace L, ∃ σ₁ σ₂ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)), IsLocS S₁ s σ₁ ∧ IsLocS S₂ s σ₂ ∧ Nonempty (σ₁.ρ.Equiv σ₂.ρ)) → (∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)), (∀ s : SplitPlace L, s.v ≠ v) → ∃ (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ), NG.OverPl w v ∧ NG.SatAt { a with S := S₁, irrS := h₁ } Dv α ∧ NG.SatAt { a with S := S₂, irrS := h₂ } Dv α) → NG.IsoRep S₁ S₂ := by
  first | exact @GlobalTheory.GlobDet.main | exact GlobalTheory.GlobDet.main | (intros; apply GlobalTheory.GlobDet.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNonsplitPlaceWithInertDatumStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.exists_nonsplit_place_with_inertDatum : ∀ (D : D7) (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))), (∀ s : SplitPlace D.host.E, s.v ≠ v) → ∃ w : HeightOneSpectrum (𝓞 D.host.E), NG.OverPl w v ∧ ¬ IsSplitPl D.host w ∧ Nonempty (InertDatum D.host.E n v w) := by
  first | exact @GlobalTheory.InertDatumExist.exists_inertDatum | exact GlobalTheory.InertDatumExist.exists_inertDatum | (intros; apply GlobalTheory.InertDatumExist.exists_inertDatum <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSplitPlaceOfSplitPlaceRealSubfieldHostStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.isSplitPlace_of_splitPlace_realSubfield_host : ∀ (D : D7) (s : SplitPlace D.host.E), IsSplitPl D.host s.w := by
  first | exact @GlobalTheory.SplitPlaceConj.isSplitPl_w | exact GlobalTheory.SplitPlaceConj.isSplitPl_w | (intros; apply GlobalTheory.SplitPlaceConj.isSplitPl_w <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitarySatakeEqOfSameUnramifiedBaseChangeStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.unitarySatake_eq_of_same_unramifiedBaseChange : ∀ (K : Type) [Field K] [Valued K (WithZero (Multiplicative ℤ))] [CompleteSpace K] (ϖ : K) (σ : K →+* K) (q n : ℕ), Formalism.UG.IsUnramInv ϖ σ q → ∀ α α' : Fin (n / 2) → ℂ, ubc n (Finset.univ.val.map α) = ubc n (Finset.univ.val.map α') → ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), Formalism.UG.SatU ϖ q h α = Formalism.UG.SatU ϖ q h α' := by
  first | exact @GlobalTheory.SatBcZero.satU_eq_of_ubc_eq | exact GlobalTheory.SatBcZero.satU_eq_of_ubc_eq | (intros; apply GlobalTheory.SatBcZero.satU_eq_of_ubc_eq <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MRepOfLocalH

section

@[expose] public section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.One.M
theorem repOfLocal_h_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ S : Reading P.T, _root_.GlobalTheory.NPin.IsFaithfulReading P S → _root_.GlobalTheory.SplitRead.LawsAlt S → ∀ i, RepOfLoc D.nd D.naut i := by
  intro hL D P S hT hLaws i P₁ P₂ hsplit hns
  apply P.H.av.inj i P₁ P₂
  refine GlobalTheory.T.algebraic_modular_forms_strong_multiplicity_one D.host.E D.R.nV (P.M.loc i).wt (P.H.av.S i P₁) (P.H.av.S i P₂) (P.H.av.irr i P₁) (P.H.av.irr i P₂) ?_ ?_
  · intro s
    have hw := GlobalTheory.T.isSplitPlace_of_splitPlace_realSubfield_host D s
    refine ⟨((S i s.w hw).rep P₁).toIrrRep, ((S i s.w hw).rep P₂).toIrrRep, hT.rep i s hw P₁, hT.rep i s hw P₂, ?_⟩
    have e1 := (S i s.w hw).locV P₁
    have e2 := (S i s.w hw).locV P₂
    rw [hsplit s.w hw, e2] at e1
    exact (_root_.UpperTheory.One.M.RecLawsH.iso (hLaws i s.w hw) _ _ _ (_root_.UpperTheory.One.M.good_cls_of_isLocS_av P i P₂ s _ (hT.rep i s hw P₂))).1 e1.symm
  · intro v hv
    obtain ⟨w, hO, hns', ⟨Dv⟩⟩ := GlobalTheory.T.exists_nonsplit_place_with_inertDatum D D.R.nV v hv
    have hsph : ∀ Q : D.naut.AV i, (P.H.av.rep i Q).SphericalAtPlace v := fun Q => by
      have h := D.nbc.embAV_sph i Q w hns'
      rw [P.H.emb i Q] at h
      exact (P.H.au.sph _ _ _ _ w v hns' hO).1 h
    obtain ⟨α₁, hα₁, e₁⟩ :=
      P.H.au.sat _ _ _ (P.H.av.rep i P₁) v w hO Dv (_root_.UpperTheory.One.M.Sph.exists_satAt_of_overPl_sphAtG _ _ _ v w hO (hsph P₁) Dv)
    obtain ⟨α₂, hα₂, e₂⟩ :=
      P.H.au.sat _ _ _ (P.H.av.rep i P₂) v w hO Dv (_root_.UpperTheory.One.M.Sph.exists_satAt_of_overPl_sphAtG _ _ _ v w hO (hsph P₂) Dv)
    have hu := hns w hns'
    rw [D.nbc.embAV_sat, D.nbc.embAV_sat, P.H.emb, P.H.emb, e₁, e₂] at hu
    refine ⟨w, Dv, α₁, hO, hα₁, ?_⟩
    obtain ⟨f, hf, hf0, U, hU, hUv, hh⟩ := hα₂
    refine ⟨f, hf, hf0, U, hU, hUv, fun h hh' => ?_⟩
    rw [GlobalTheory.T.unitarySatake_eq_of_same_unramifiedBaseChange _ Dv.ϖ Dv.σw _ D.R.nV Dv.unram α₁ α₂ hu h hh']
    exact hh h hh'
end UpperTheory.One.M
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalRepOfReadingLaws

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.repOfLoc_of_isTrue_laws : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ S : Reading P.T, _root_.GlobalTheory.NPin.IsFaithfulReading P S → _root_.GlobalTheory.SplitRead.LawsAlt S → ∀ i, RepOfLoc D.nd D.naut i := by
  first | exact @_root_.UpperTheory.One.M.repOfLocal_h_alt | exact _root_.UpperTheory.One.M.repOfLocal_h_alt | (intros; apply _root_.UpperTheory.One.M.repOfLocal_h_alt <;> assumption)
end
end
end
