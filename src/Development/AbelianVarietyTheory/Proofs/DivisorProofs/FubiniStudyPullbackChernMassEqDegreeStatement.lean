module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.LocusEqTopOfDualPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormFubiniStudyTotalStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernIntPullFubiniStudyEqZeroOfNotDominantStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernMassPullMulDegreeFieldStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericDegreePullbackFormula
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeGenericPointNeZeroProjectiveSameDim
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopSelfIntersectionO1ProjectiveStatement
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineEtaleFiniteFreeNbhdStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyPullbackStructureModuleIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopSelfIntersectionPullbackEqZeroOfNotDominant
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveSpaceIntegralSmoothProjectiveDim

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory

theorem pspace_integral_dim_proj_smooth :
    ∀ (k : Type) [Field k] (N : ℕ), IsIntegral (PSpace k N) ∧ topologicalKrullDim (PSpace k N) = N ∧ IsProjOver (PSpace.str k N) ∧ SmoothOfRelativeDimension N (PSpace.str k N) :=
  fun k _ N => ⟨ProjSpace.isIntegral_of_isDomain k N, ProjSpace.topologicalKrullDim_eq k N,
    ⟨N, 𝟙 _, inferInstance, by simp⟩, inferInstance⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveSpaceIntegralSmoothProjectiveDimStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

theorem _root_.GlobalTheory.T.projectiveSpace_integral_smooth_projective_dim : ∀ (k : Type) [Field k] (N : ℕ), IsIntegral (PSpace k N) ∧ topologicalKrullDim (PSpace k N) = N ∧ IsProjOver (PSpace.str k N) ∧ SmoothOfRelativeDimension N (PSpace.str k N) := by
  first | exact @GlobalTheory.pspace_integral_dim_proj_smooth | exact GlobalTheory.pspace_integral_dim_proj_smooth | (intros; apply GlobalTheory.pspace_integral_dim_proj_smooth <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeGenericPointNeZeroProjectiveSameDimStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

theorem _root_.GlobalTheory.T.residueDegree_genericPoint_ne_zero_projective_same_dim : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D : ℕ), IsProjOver p → IsProjOver q → topologicalKrullDim X = D → topologicalKrullDim Y = D → ∀ (π : Y ⟶ X), π ≫ p = q → π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 := by
  first | exact @GlobalTheory.DominantProjDegree.residueDegree_ne_zero_of_map_genericPoint | exact GlobalTheory.DominantProjDegree.residueDegree_ne_zero_of_map_genericPoint | (intros; apply GlobalTheory.DominantProjDegree.residueDegree_ne_zero_of_map_genericPoint <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopSelfIntersectionPullbackEqDegreeMul

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory.ProjFormulaTop

theorem topSelf_pull_eq_mul : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) [CharZero k] (D : ℕ), IsProjOver p → IsProjOver q → topologicalKrullDim X ≤ D → ∀ (π : Y ⟶ X), π ≫ p = q → π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∀ B : LB X, B.IsLB → letI := GlobalTheory.algebraΓOfHom p; letI := GlobalTheory.algebraΓOfHom q; topSelfIntersection k (B.pull π) D = (π.residueDegree (genericPoint Y) : ℤ) * topSelfIntersection k B D := by
  intro k _ X Y _ _ p q _ D hp hq hD π hπ hgen hdeg B hB
  obtain ⟨U, hU, hgU, hU', -, hfin, hfree, hrank⟩ :=
    GlobalTheory.T.exists_affine_etale_finite_free_nbhd k X Y p q hp hq π hπ hgen hdeg
  subst hπ
  letI := GlobalTheory.algebraΓOfHom p
  letI := GlobalTheory.algebraΓOfHom (π ≫ p)
  rw [topSelf_def, topSelf_def]
  letI := (π.app U).hom.toAlgebra
  have hfin' : Module.Finite Γ(X, U) Γ(Y, π ⁻¹ᵁ U) := hfin
  exact GlobalTheory.FieldProj.interNum_pull_eq_mul k Y X p π hq hp U _ hgU hU hU'
    ⟨hfree, hfin', hrank⟩ D hD (fun _ => B) (fun _ => hB)

end GlobalTheory.ProjFormulaTop
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopSelfIntersectionPullbackEqDegreeMulStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

theorem _root_.GlobalTheory.T.topSelfIntersection_pullback_eq_degree_mul : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) [CharZero k] (D : ℕ), IsProjOver p → IsProjOver q → topologicalKrullDim X ≤ D → ∀ (π : Y ⟶ X), π ≫ p = q → π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∀ B : LB X, B.IsLB → letI := GlobalTheory.algebraΓOfHom p; letI := GlobalTheory.algebraΓOfHom q; topSelfIntersection k (B.pull π) D = (π.residueDegree (genericPoint Y) : ℤ) * topSelfIntersection k B D := by
  first | exact @GlobalTheory.ProjFormulaTop.topSelf_pull_eq_mul | exact GlobalTheory.ProjFormulaTop.topSelf_pull_eq_mul | (intros; apply GlobalTheory.ProjFormulaTop.topSelf_pull_eq_mul <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopSelfIntersectionPullbackEqZeroOfNotDominantStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

theorem _root_.GlobalTheory.T.topSelfIntersection_pullback_eq_zero_of_not_dominant : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D : ℕ), IsProjOver q → topologicalKrullDim X ≤ D → topologicalKrullDim Y ≤ D → ∀ (π : Y ⟶ X), π (genericPoint Y) ≠ genericPoint X → ∀ B : LB X, B.IsLB → letI := GlobalTheory.algebraΓOfHom q; topSelfIntersection k (B.pull π) D = 0 := by
  first | exact @GlobalTheory.PullVanish.topSelf_pull_eq_zero_of_not_dominant | exact GlobalTheory.PullVanish.topSelf_pull_eq_zero_of_not_dominant | (intros; apply GlobalTheory.PullVanish.topSelf_pull_eq_zero_of_not_dominant <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudyPullbackChernMassEqDegree

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FubiniStudyPull

theorem fubiniStudy_pullback_chern_mass_eq_degree : ∀ (Y : Var ℂ) (π : Y.X ⟶ PSpace ℂ Y.dim)
    (hπ : π ≫ PSpace.str ℂ Y.dim = Y.str),
    Weight.chernInt (((ProjSpace.hermitianTwistingSheaf ℂ Y.dim).φ (RingHom.id ℂ)).pull π hπ) Y.dim Set.univ
      (fun _ => 1) = (topSelfIntersection ℂ ((ProjSpace.O1 ℂ Y.dim).pull π) Y.dim : ℝ) := by
  intro Y π hπ
  obtain ⟨hPI, hPdim, hPproj, hPsm⟩ := GlobalTheory.T.projectiveSpace_integral_smooth_projective_dim ℂ Y.dim
  haveI := hPI
  by_cases hη : π (genericPoint Y.X) = genericPoint (PSpace ℂ Y.dim)
  · have hδ := GlobalTheory.T.residueDegree_genericPoint_ne_zero_projective_same_dim ℂ (PSpace ℂ Y.dim) Y.X (PSpace.str ℂ Y.dim) Y.str Y.dim hPproj
      Y.isProjOver hPdim Y.topologicalKrullDim_eq π hπ hη
    have hm := fun ε => GlobalTheory.T.chernMass_pull_mul_degree_field ℂ (PSpace ℂ Y.dim) Y.X (PSpace.str ℂ Y.dim) Y.str (RingHom.id ℂ)
      Y.dim hPproj Y.isProjOver hPsm π hπ hη hδ (ProjSpace.hermitianTwistingSheaf ℂ Y.dim).B
      ((ProjSpace.hermitianTwistingSheaf ℂ Y.dim).φ (RingHom.id ℂ)) ((ProjSpace.hermitianTwistingSheaf ℂ Y.dim).cInf _) ε
    obtain ⟨h1, h0⟩ := GlobalTheory.T.chern_form_fubini_study_total Y.dim
    have hi := GlobalTheory.T.topSelfIntersection_pullback_eq_degree_mul ℂ (PSpace ℂ Y.dim) Y.X (PSpace.str ℂ Y.dim) Y.str Y.dim hPproj
      Y.isProjOver hPdim.le π hπ hη hδ (ProjSpace.O1 ℂ Y.dim) (ProjSpace.O1_isLB ℂ Y.dim)
    have ht := GlobalTheory.T.top_self_intersection_O1_projective ℂ Y.dim
    rw [GdegPullProof.chernInt_one, hm 1, hm (-1), h1, h0]
    change _ = ((topSelfIntersection ℂ ((ProjSpace.O1 ℂ Y.dim).pull π) Y.dim : ℤ) : ℝ)
    rw [hi, ht]
    simp
  · have hc := GlobalTheory.T.chernInt_pull_fubiniStudy_eq_zero_of_not_specializes Y π hπ ⟨genericPoint (PSpace ℂ Y.dim), fun h =>
      hη (h.antisymm (genericPoint_specializes _)).eq⟩
    have hn := GlobalTheory.T.topSelfIntersection_pullback_eq_zero_of_not_dominant ℂ (PSpace ℂ Y.dim) Y.X (PSpace.str ℂ Y.dim) Y.str Y.dim Y.isProjOver
      hPdim.le Y.topologicalKrullDim_eq.le π hη (ProjSpace.O1 ℂ Y.dim) (ProjSpace.O1_isLB ℂ Y.dim)
    rw [hc]
    change (0 : ℝ) = ((topSelfIntersection ℂ ((ProjSpace.O1 ℂ Y.dim).pull π) Y.dim : ℤ) : ℝ)
    rw [hn]
    simp

end GlobalTheory.FubiniStudyPull

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudyPullbackChernMassEqDegreeStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

theorem _root_.GlobalTheory.T.chernInt_pull_fubiniStudy_eq_topSelf : ∀ (Y : Var ℂ) (π : Y.X ⟶ PSpace ℂ Y.dim) (hπ : π ≫ PSpace.str ℂ Y.dim = Y.str), Weight.chernInt (((ProjSpace.hermitianTwistingSheaf ℂ Y.dim).φ (RingHom.id ℂ)).pull π hπ) Y.dim Set.univ (fun _ => 1) = (topSelfIntersection ℂ ((ProjSpace.O1 ℂ Y.dim).pull π) Y.dim : ℝ) := by
  first | exact @GlobalTheory.FubiniStudyPull.fubiniStudy_pullback_chern_mass_eq_degree | exact GlobalTheory.FubiniStudyPull.fubiniStudy_pullback_chern_mass_eq_degree | (intros; apply GlobalTheory.FubiniStudyPull.fubiniStudy_pullback_chern_mass_eq_degree <;> assumption)
end
end
