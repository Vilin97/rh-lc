module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjBySmoothIsProperGeometricallyIntegral
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteTypeSchemeRepresentingPolarizedHomsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomFixedPullbackRepresentableGlueStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedBundlePullbackIsoOfLocalIsoAbelianHom
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeRestrictOpenImmersion

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.OpenRestrictPol

theorem exists_restrict_open : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left),
    IsAbelianScheme A → L.IsLB → Out.Rigidified A L → Out.RelAmple A L → ∀ (V : Scheme.{0}) (j : V ⟶ S),
    IsOpenImmersion j → ∃ (A' : Over V) (_ : GrpObj A') (_ : IsCommMonObj A') (φ : A'.left ⟶ A.left),
    IsGrpPullback A' A j φ ∧ IsAbelianScheme A' ∧ (L.pull φ).IsLB ∧ Out.Rigidified A' (L.pull φ) ∧
    Out.RelAmple A' (L.pull φ) := by
  intro S A _ _ L hA hL hr hamp V j _
  have hpb := isGrpPullback_pullback A j
  have := hA.proper
  exact ⟨(Over.pullback j).obj A, inferInstance, GlobalTheory.PolPull.isCommMonObj_of_isGrpPullback hpb,
    pullback.fst A.hom j, hpb, GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA hpb, pull_isLB hL _,
    GlobalTheory.PolBaseChange.rigidified_pull hpb hr, GlobalTheory.AmpleBaseChange.relAmple_of_isPullback hL hamp hpb.1⟩

end GlobalTheory.OpenRestrictPol
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeRestrictOpenImmersionStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_abelianScheme_restrict_openImmersion : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left), IsAbelianScheme A → L.IsLB → Out.Rigidified A L → Out.RelAmple A L → ∀ (V : Scheme.{0}) (j : V ⟶ S), IsOpenImmersion j → ∃ (A' : Over V) (_ : GrpObj A') (_ : IsCommMonObj A') (φ : A'.left ⟶ A.left), IsGrpPullback A' A j φ ∧ IsAbelianScheme A' ∧ (L.pull φ).IsLB ∧ Out.Rigidified A' (L.pull φ) ∧ Out.RelAmple A' (L.pull φ) := by
  first | exact @GlobalTheory.OpenRestrictPol.exists_restrict_open | exact GlobalTheory.OpenRestrictPol.exists_restrict_open | (intros; apply GlobalTheory.OpenRestrictPol.exists_restrict_open <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedBundlePullbackIsoOfLocalIsoAbelianHomStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.rigidifiedBundle_pullbackIso_of_localIso_abelianHom : ∀ (H : Scheme.{0}) (A B : Over H) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (Φ : A ⟶ B), IsMonHom Φ → IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Out.Rigidified A L → Out.Rigidified B M → (∀ h : H, ∃ W : H.Opens, h ∈ W ∧ LBIso (L.pull (A.hom ⁻¹ᵁ W).ι) ((M.pull Φ.left).pull (A.hom ⁻¹ᵁ W).ι)) → LBIso L (M.pull Φ.left) := by
  first | exact @GlobalTheory.HomFixLocal.lbIso_pull_of_local | exact GlobalTheory.HomFixLocal.lbIso_pull_of_local | (intros; apply GlobalTheory.HomFixLocal.lbIso_pull_of_local <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteTypeRepresentingPolarizedHomsLocNoet

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.HomFixGlue

theorem homFix_finiteType : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Out.Rigidified A L → Out.Rigidified B M → Out.RelAmple A L → Out.RelAmple B M → ∃ R : HomFixRep A B L M, QuasiCompact R.π ∧ IsSeparated R.π ∧ LocallyOfFiniteType R.π := by
  intro S _ A B _ _ _ _ L M hA hB hL hM rA rB aA aB
  refine GlobalTheory.T.homFixedPullback_representable_glue GlobalTheory.T.rigidifiedBundle_pullbackIso_of_localIso_abelianHom S A B L M hA hB hL hM rA rB S.affineOpens (fun U => Sp Γ(S, U)) (fun U => U.2.fromSpec)
    (fun U => IsAffineOpen.isOpenImmersion_fromSpec U.2) ?_ ?_
  · intro s
    obtain ⟨U, hU, hs, -⟩ := exists_isAffineOpen_mem_and_subset (show s ∈ (⊤ : S.Opens) from trivial)
    exact ⟨⟨U, hU⟩, hU.range_fromSpec.ge hs⟩
  · intro U
    haveI : IsNoetherianRing Γ(S, U) := IsLocallyNoetherian.component_noetherian U
    obtain ⟨A', _, _, φA, gA, hA', hL', rA', aA'⟩ := GlobalTheory.T.exists_abelianScheme_restrict_openImmersion S A L hA hL rA aA _ U.2.fromSpec (IsAffineOpen.isOpenImmersion_fromSpec U.2)
    obtain ⟨B', _, _, φB, gB, hB', hM', rB', aB'⟩ := GlobalTheory.T.exists_abelianScheme_restrict_openImmersion S B M hB hM rB aB _ U.2.fromSpec (IsAffineOpen.isOpenImmersion_fromSpec U.2)
    obtain ⟨R, h1, h2, h3⟩ := GlobalTheory.T.exists_finiteType_scheme_representing_polarizedHoms Γ(S, U) A' B' (L.pull φA) (M.pull φB) hA' hB' hL' hM' rA' rB' aA' aB'
    exact ⟨A', B', _, _, φA, φB, R, gA, gB, h1, h2, h3⟩

end GlobalTheory.HomFixGlue
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteTypeRepresentingPolarizedHomsLocNoetStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_finiteType_representing_polarizedHoms_locNoeth : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Out.Rigidified A L → Out.Rigidified B M → Out.RelAmple A L → Out.RelAmple B M → ∃ R : HomFixRep A B L M, QuasiCompact R.π ∧ IsSeparated R.π ∧ LocallyOfFiniteType R.π := by
  first | (exact @GlobalTheory.HomFixGlue.homFix_finiteType) | (exact GlobalTheory.HomFixGlue.homFix_finiteType) | (intros; apply GlobalTheory.HomFixGlue.homFix_finiteType  <;> assumption)
end
end
