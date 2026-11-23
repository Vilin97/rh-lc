module

public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteDvrIntegralClosureFinite
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsogenousRetractPolarisedFiniteExt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PotentialSemiAbelianModelOfSymmetryHypStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PotentialSemiAbelianReductionOfIsogenyStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PotentialSemiAbelianReductionOfRetract
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteDvrIntegralClosureFiniteStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem _root_.GlobalTheory.T.exists_complete_dvr_integral_closure_finite : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L], ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : IsAdicComplete (IsLocalRing.maximalIdeal W) W) (_ : Algebra V W) (_ : Algebra W L) (_ : IsFractionRing W L), (algebraMap W L).comp (algebraMap V W) = (algebraMap K L).comp (algebraMap V K) ∧ Module.Finite V W ∧ Function.Injective (algebraMap V W) ∧ IsLocalHom (algebraMap V W) ∧ (∀ x : L, RingHom.IsIntegralElem ((algebraMap K L).comp (algebraMap V K)) x → x ∈ Set.range (algebraMap W L)) ∧ ∀ (A : Over (Sp K)) [GrpObj A] Q, PotModel W L ((Over.pullback (spMap (algebraMap K L))).obj A) Q → PotModel V K A Q := by
  first | exact @GlobalTheory.SS.exists_complete_dvr_finite_extension | exact GlobalTheory.SS.exists_complete_dvr_finite_extension | (intros; apply GlobalTheory.SS.exists_complete_dvr_finite_extension <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsogenousRetractPolarisedFiniteExtStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem _root_.GlobalTheory.T.exists_isogenous_retract_polarised_finiteExt : ∀ (K : Type) [Field K] [CharZero K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L) (B : Over (Sp L)) (_ : GrpObj B) (Q : Out.PolAV (Sp L)) (g m : ℕ) (i : (Over.pullback (spMap (algebraMap K L))).obj A ⟶ B) (r : B ⟶ (Over.pullback (spMap (algebraMap K L))).obj A) (i' : B ⟶ Q.A) (r' : Q.A ⟶ B), GlobalTheory.AbLaw.IsProjBy ((Over.pullback (spMap (algebraMap K L))).obj A).hom ∧ SmoothOfRelativeDimension g ((Over.pullback (spMap (algebraMap K L))).obj A).hom ∧ SmoothOfRelativeDimension g B.hom ∧ IsMonHom i ∧ IsMonHom r ∧ 1 ≤ m ∧ r ≫ i = 𝟙 _ ^ m ∧ IsMonHom i' ∧ IsMonHom r' ∧ i' ≫ r' = 𝟙 B ∧ (letI := Q.isAb.comm; GlobalTheory.ZH.HypS Q.A Q.L) := by
  first | exact @GlobalTheory.FiniteData.exists_isogenous_retract | exact GlobalTheory.FiniteData.exists_isogenous_retract | (intros; apply GlobalTheory.FiniteData.exists_isogenous_retract <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PotentialSemiAbelianReductionOfRetractStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem _root_.GlobalTheory.T.potentialSemiAbelianReduction_of_retract : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (B Q : Over (Sp K)) [GrpObj B] [GrpObj Q] (i : B ⟶ Q) (r : Q ⟶ B), IsMonHom i → IsMonHom r → i ≫ r = 𝟙 B → PotModel V K Q (fun _ _ _ G _ => IsSemiAbelian G) → PotModel V K B (fun _ _ _ G _ => IsSemiAbelian G) := by
  first | exact @GlobalTheory.SS.potModel_semiAbelian_of_retract | exact GlobalTheory.SS.potModel_semiAbelian_of_retract | (intros; apply GlobalTheory.SS.potModel_semiAbelian_of_retract <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianVarietyPotentialSemiAbelianModel

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
namespace GlobalTheory.SS

theorem potModel_isSemiAbelian : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] (K : Type) [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (A : Over (Spec (CommRingCat.of K))) [GrpObj A], IsAbelianScheme A → PotModel V K A (fun _ _ _ G _ => IsSemiAbelian G) := by
  intro V _ _ _ _ K _ _ _ _ A _ hA
  obtain ⟨L, _, _, _, B, _, Q, g, m, i, r, i', r', hp, hs, hsB, hi, hr, hm, hri, hi', hr', hir, hS⟩ :=
    GlobalTheory.T.exists_isogenous_retract_polarised_finiteExt K A hA
  obtain ⟨W, _, _, _, _, _, _, _, -, -, -, -, -, hup⟩ := GlobalTheory.T.exists_complete_dvr_integral_closure_finite V K L
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  letI := Q.grp
  have hQ := GlobalTheory.T.potentialSemiAbelianModel_of_symmetryHyp W L Q hS
  have hB := GlobalTheory.T.potentialSemiAbelianReduction_of_retract W L B Q.A i' r' hi' hr' hir hQ
  have hAL : IsAbelianScheme ((Over.pullback (spMap (algebraMap K L))).obj A) := by
    have := hA.comm
    have := hA.smooth
    have := hA.proper
    have := hA.geomConnected
    exact
      { comm := Functor.isCommMonObj_obj
        smooth := by change Smooth (pullback.snd A.hom _); infer_instance
        proper := by change IsProper (pullback.snd A.hom _); infer_instance
        geomConnected := by change GeometricallyConnected (pullback.snd A.hom _); infer_instance }
  exact hup A _ (GlobalTheory.T.potentialSemiAbelianReduction_of_isogeny W L _ B g m hAL hp hs hsB i r hi hr hm hri hB)
end GlobalTheory.SS
end
end
