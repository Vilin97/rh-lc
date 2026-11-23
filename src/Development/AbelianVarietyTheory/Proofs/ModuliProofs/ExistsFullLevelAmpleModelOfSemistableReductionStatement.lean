module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFullLevelModelAmpleFrames
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GoodReductionOfThetaPointUnitsStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HomExtensionSemiAbelianDiscreteValuationRingStatement
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSemiAbelianModelSplitSpecialFibre
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyPadicIntRingHomOfIsAdicComplete
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TheoremOfCubePolAbelianSchemeStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaUniformisationComplexAbelianVarietiesStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformisationExistenceAndTorsionStatementsStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ZarhinGeometricOfSemistableReductionStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHoldStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFullLevelModelAmpleFramesStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

theorem _root_.GlobalTheory.T.exists_fullLevel_model_ample_frames : GlobalTheory.LN.HomExtSt → Out.Laws → Out.Laws2 → GlobalTheory.Published.SemistableReductionSt → GlobalTheory.ZH.ThmUSt → GlobalTheory.ZH.UTorsSt → GlobalTheory.ZH.ZHGeoSt → (∀ (g n : ℕ) (J : Type) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Finite (IsLocalRing.ResidueField V)] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (β : o →+* V) (t : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V K) ≫ spMap β)) (v : Ix g ((n ^ j) ^ 2) → V), t.Prim w w' → t.HasTh (𝟙 _) (fun a => algebraMap V K (v a)) → Coset n (n ^ j) v (IsLocalRing.maximalIdeal V) → ∃ (V' K' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : Field K') (_ : Algebra V' K') (_ : IsFractionRing V' K') (φ : V →+* V') (ψ : K →+* K') (t' : TObj g ((n ^ j) ^ 2) J b (spMap φ ≫ spMap β)) (tK : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V' K') ≫ spMap φ ≫ spMap β)), IsLocalHom φ ∧ ψ.comp (algebraMap V K) = (algebraMap V' K').comp φ ∧ TMap tK t (spMap ψ) ∧ TMap tK t' (spMap (algebraMap V' K')) ∧ t'.HasTh (𝟙 _) (fun a => φ (v a))) → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → TopAmpExists := by
  first | exact @GlobalTheory.Models.topAmpExists | exact GlobalTheory.Models.topAmpExists | (intros; apply GlobalTheory.Models.topAmpExists <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.SemistableReductionSplitOfPadic

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SS

theorem semistablePol_of_padic : GlobalTheory.Published.SemistableReductionSt → GlobalTheory.SS.SemistablePol := by
  intro H V K _ _ _ _ _ _ _ _ hfin A
  obtain ⟨p, hp, K₀, e, e₀, hK₀, he⟩ := GlobalTheory.completeDVR_eq_integralClosure_padicInt.1 V K hfin
  obtain ⟨P, ψ, hψ⟩ : ∃ (P : PolAV (Sp K₀)) (ψ : P.A.left ⟶ A.A.left),
      IsGrpPullback P.A A.A (spMap e.toRingHom) ψ := by
    obtain ⟨P', g, hg, -, hm, -⟩ := GlobalTheory.polBaseChange_holds _ _ (spMap e.toRingHom) A
    refine ⟨P', g, hg, fun T x y x₀ y₀ hx hy => ?_⟩
    rw [(Over.OverMorphism.ext hx : x₀ = Out.toBase hg.w x), (Over.OverMorphism.ext hy : y₀ = Out.toBase hg.w y), ← hm]
    rfl
  obtain ⟨K', h, hloc, hK', G, gG, hG, hE, φ, hφ⟩ :=
    GlobalTheory.exists_semiAbelian_model_split_specialFibre H p K₀ P
  obtain ⟨hdvr, hfr, hc, f, hf, hlf, hfx⟩ := GlobalTheory.completeDVR_eq_integralClosure_padicInt.2 p K₀ K' h hK'
  letI aV : Algebra V (integralClosure ℤ_[p] K') := (f.comp e₀.toRingHom).toAlgebra
  letI aK : Algebra K K' := ((IntermediateField.inclusion h).toRingHom.comp e.toRingHom).toAlgebra
  refine ⟨integralClosure ℤ_[p] K', K', inferInstance, inferInstance, hdvr, inferInstance, aV, inferInstance, aK, hfr,
    ?_, ?_, ?_, hc, G, gG, ?_, hG, hE⟩
  · ext1 x
    change ((f (e₀ x) : integralClosure ℤ_[p] K') : K') = IntermediateField.inclusion h (e (algebraMap V K x))
    rw [hfx, he]
  · exact RingHom.Finite.comp hf (RingHom.Finite.of_surjective _ e₀.surjective)
  · haveI : IsLocalHom e₀.toRingHom := isLocalHom_of_leftInverse e₀.symm.toRingHom e₀.left_inv
    exact RingHom.isLocalHom_comp f e₀.toRingHom
  · obtain ⟨i, hi, -⟩ := grpPullback_iso
      ((hφ.comp hψ).congr (GlobalTheory.SplitReduction.spMap_comp _ _) rfl)
      (isGrpPullback_pullback A.A (spMap (algebraMap K K')))
    exact ⟨i, hi⟩

end GlobalTheory.SS
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.SemistableReductionSplitOfPadicStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.semistableReductionSplit_of_padic : GlobalTheory.Published.SemistableReductionSt → GlobalTheory.SS.SemistablePol := by
  first | exact @GlobalTheory.SS.semistablePol_of_padic | exact GlobalTheory.SS.semistablePol_of_padic | (intros; apply GlobalTheory.SS.semistablePol_of_padic <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFullLevelAmpleModelOfSemistableReduction

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem topAmpExists_of_semistableReduction :
    GlobalTheory.Published.SemistableReductionSt → GlobalTheory.Models.TopAmpExists :=
  fun S => GlobalTheory.T.exists_fullLevel_model_ample_frames GlobalTheory.T.homExtension_semiAbelian_discreteValuationRing GlobalTheory.T.all_six_abelian_scheme_laws_hold.1 GlobalTheory.T.all_six_abelian_scheme_laws_hold.2.1 S GlobalTheory.T.uniformisationExistence_and_torsion_statements.1 GlobalTheory.T.uniformisationExistence_and_torsion_statements.2
    (GlobalTheory.T.zarhinGeometric_of_semistableReduction S)
    (GlobalTheory.T.goodReduction_of_thetaPoint_units GlobalTheory.T.all_six_abelian_scheme_laws_hold.1 GlobalTheory.T.all_six_abelian_scheme_laws_hold.2.1 (GlobalTheory.T.semistableReductionSplit_of_padic S) GlobalTheory.T.uniformisationExistence_and_torsion_statements.1 GlobalTheory.T.uniformisationExistence_and_torsion_statements.2)
    GlobalTheory.T.theorem_of_cube_polAbelianScheme GlobalTheory.T.theta_uniformisation_complex_abelian_varieties

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFullLevelAmpleModelOfSemistableReductionStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_fullLevelAmpleModel_of_semistableReduction : GlobalTheory.Published.SemistableReductionSt → GlobalTheory.Models.TopAmpExists := by
  first | exact @GlobalTheory.topAmpExists_of_semistableReduction | exact GlobalTheory.topAmpExists_of_semistableReduction | (intros; apply GlobalTheory.topAmpExists_of_semistableReduction <;> assumption)
end
end
