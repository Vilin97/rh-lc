module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleSpreadSubring
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.AdelicGL2ExtOfLocalComponents
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteTypeSubringModelAbelianLineBundleStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegelObjectOfDescendedData
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LineBundleIsoDescendsToSubringOfFinset
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
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegelObjectOfDescendedData
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaPointShapePrimitivityNearGeneric
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsFiniteTypeSubringAdjoin
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullbackFactor
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGDatumOneOneOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinsetGeneratorDescendsSubring

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.SiegelDescent ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison

namespace GlobalTheory

theorem lbIso_triv_pull_triv {X Y : Scheme.{0}} (f : Y ⟶ X) : LBIso ((LB.triv X).pull f) (LB.triv Y) :=
  Ex.ValInh.lbIso_of_g_one (fun i j => by
    simp only [LB.pull, LB.LinComb, LB.triv, map_one, one_zpow, Finset.prod_const_one]
    simp only [Finset.univ_unique, Finset.prod_singleton, zpow_one]
    exact (res _).map_one) (fun i j => rfl)

theorem exists_finset_gen_descends : ∀ (R : Type) [CommRing R] (S : Subring R) (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (B : Over (Sp S)) [GrpObj B] [IsCommMonObj B] (φ : A.left ⟶ B.left) (φ₂ : (G2 A).left ⟶ (G2 B).left) (P : LB (G2 A).left) (P₀ : LB (G2 B).left) (a : A ⟶ G2 A) (a₀ : B ⟶ G2 B), IsAbelianScheme B → IsGrpPullback A B (spMap S.subtype) φ → IsSquare φ φ₂ → P.IsLB → P₀.IsLB → LBIso P (P₀.pull φ₂) → a.left ≫ φ₂ = φ ≫ a₀.left → (∃ t : (P.pull a.left).Gen, t.IsGen) → ∃ F : Finset R, ∀ (R₁ : Subring R) (h : S ≤ R₁), (F : Set R) ⊆ R₁ → ∀ a₁ : (Over.pullback (spMap (Subring.inclusion h))).obj B ⟶ G2 ((Over.pullback (spMap (Subring.inclusion h))).obj B), a₁.left ≫ pφ₂ (spMap (Subring.inclusion h)) B = pφ (spMap (Subring.inclusion h)) B ≫ a₀.left → ∃ t : ((P₀.pull (pφ₂ (spMap (Subring.inclusion h)) B)).pull a₁.left).Gen, t.IsGen := by
  intro R _ S A _ _ B _ _ φ φ₂ P P₀ a a₀ hB hφ sq hP hP₀ hw e ht
  haveI := hB.proper
  have hN : (P₀.pull a₀.left).IsLB := pull_isLB hP₀ _
  have hT : ∀ X : Scheme.{0}, (LB.triv X).IsLB := fun X => LB.isLB_triv X
  have H₀ : LBIso (LB.triv A.left) ((P₀.pull a₀.left).pull φ) :=
    LBIso.trans (hT _) (pull_isLB hP _) (pull_isLB hN _) ((CechPic.iso_triv_iff _).2 ht)
      (lbIso_square hP hP₀ hw e)
  have H : LBIso ((LB.triv B.left).pull φ) ((P₀.pull a₀.left).pull φ) :=
    LBIso.trans (pull_isLB (hT _) _) (hT _) (pull_isLB hN _) (lbIso_triv_pull_triv φ) H₀
  obtain ⟨F, hF⟩ := lbIso_descends_to_subring_containing_finset R S A.left B.left A.hom B.hom φ
    (LB.triv B.left) (P₀.pull a₀.left) hφ.1 (hT _) hN H
  refine ⟨F, fun R₁ h hs a₁ e₁ => ?_⟩
  have H₁ := hF R₁ h hs _ _ (pφ (spMap (Subring.inclusion h)) B)
    (isGrpPullback (spMap (Subring.inclusion h)) B).1
  have H₂ : LBIso ((P₀.pull (pφ₂ (spMap (Subring.inclusion h)) B)).pull a₁.left)
      ((P₀.pull a₀.left).pull (pφ (spMap (Subring.inclusion h)) B)) :=
    lbIso_square (pull_isLB hP₀ _) hP₀ (PolBaseChange.lbIso_refl (pull_isLB hP₀ _)) e₁
  refine (CechPic.iso_triv_iff _).1 ?_
  exact LBIso.trans (hT _) (pull_isLB (hT _) _) (pull_isLB (pull_isLB hP₀ _) _)
    (lbIso_triv_pull_triv _).symm
    (LBIso.trans (pull_isLB (hT _) _) (pull_isLB hN _) (pull_isLB (pull_isLB hP₀ _) _) H₁ H₂.symm)

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinsetGeneratorDescendsSubringStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.SiegelDescent ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison


theorem _root_.GlobalTheory.T.exists_finset_generator_descends_subring : ∀ (R : Type) [CommRing R] (S : Subring R) (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (B : Over (Sp S)) [GrpObj B] [IsCommMonObj B] (φ : A.left ⟶ B.left) (φ₂ : (G2 A).left ⟶ (G2 B).left) (P : LB (G2 A).left) (P₀ : LB (G2 B).left) (a : A ⟶ G2 A) (a₀ : B ⟶ G2 B), IsAbelianScheme B → IsGrpPullback A B (spMap S.subtype) φ → IsSquare φ φ₂ → P.IsLB → P₀.IsLB → LBIso P (P₀.pull φ₂) → a.left ≫ φ₂ = φ ≫ a₀.left → (∃ t : (P.pull a.left).Gen, t.IsGen) → ∃ F : Finset R, ∀ (R₁ : Subring R) (h : S ≤ R₁), (F : Set R) ⊆ R₁ → ∀ a₁ : (Over.pullback (spMap (Subring.inclusion h))).obj B ⟶ G2 ((Over.pullback (spMap (Subring.inclusion h))).obj B), a₁.left ≫ pφ₂ (spMap (Subring.inclusion h)) B = pφ (spMap (Subring.inclusion h)) B ≫ a₀.left → ∃ t : ((P₀.pull (pφ₂ (spMap (Subring.inclusion h)) B)).pull a₁.left).Gen, t.IsGen := by
  first | exact @GlobalTheory.exists_finset_gen_descends | exact GlobalTheory.exists_finset_gen_descends | (intros; apply GlobalTheory.exists_finset_gen_descends <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmLineBundleIsoDescendsSubringFinset

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.SiegelDescent ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

theorem symm_lbIso_descends_to_subring_containing_finset : ∀ (R : Type) [CommRing R] (S : Subring R) (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (B : Over (Sp S)) [GrpObj B] [IsCommMonObj B] (φ : A.left ⟶ B.left) (φ₂ : (G2 A).left ⟶ (G2 B).left) (P : LB (G2 A).left) (P₀ : LB (G2 B).left), IsAbelianScheme B → IsGrpPullback A B (spMap S.subtype) φ → IsSquare φ φ₂ → P.IsLB → P₀.IsLB → LBIso P (P₀.pull φ₂) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → ∃ F : Finset R, ∀ (R₁ : Subring R) (h : S ≤ R₁), (F : Set R) ⊆ R₁ → LBIso (P₀.pull (pφ₂ (spMap (Subring.inclusion h)) B)) ((P₀.pull (pφ₂ (spMap (Subring.inclusion h)) B)).pull (lift (snd ((Over.pullback (spMap (Subring.inclusion h))).obj B) ((Over.pullback (spMap (Subring.inclusion h))).obj B)) (fst ((Over.pullback (spMap (Subring.inclusion h))).obj B) ((Over.pullback (spMap (Subring.inclusion h))).obj B))).left) := by
  intro R _ S A _ _ B _ _ φ φ₂ P P₀ hB hφ sq hP hP₀ hw hsym
  haveI := hB.proper
  have hprop : IsProper (G2 B).hom := by rw [Over.tensorObj_hom]; infer_instance
  haveI : QuasiCompact (G2 B).hom := inferInstance
  haveI : QuasiSeparated (G2 B).hom := inferInstance
  set sw₀ := (lift (snd B B) (fst B B)).left with hsw₀
  have hpb := isPullback_square hφ.1 φ₂ sq
  have H : LBIso (P₀.pull φ₂) ((P₀.pull sw₀).pull φ₂) :=
    LBIso.trans (pull_isLB hP₀ _) hP (pull_isLB (pull_isLB hP₀ _) _) hw.symm
      (LBIso.trans hP (pull_isLB hP _) (pull_isLB (pull_isLB hP₀ _) _) hsym
        (lbIso_square hP hP₀ hw (lift_square sq sq.2.symm sq.1.symm)))
  obtain ⟨F, hF⟩ := lbIso_descends_to_subring_containing_finset R S (G2 A).left (G2 B).left (G2 A).hom
    (G2 B).hom φ₂ P₀ (P₀.pull sw₀) hpb hP₀ (pull_isLB hP₀ _) H
  refine ⟨F, fun R₁ h hF₁ => ?_⟩
  have hpb₁ := isPullback_square (isGrpPullback (spMap (Subring.inclusion h)) B).1 _
    (isSquare (spMap (Subring.inclusion h)) B)
  have H₁ := hF R₁ h hF₁ _ _ _ hpb₁
  have e := lift_swap (spMap (Subring.inclusion h)) B
  refine LBIso.trans (pull_isLB hP₀ _) (pull_isLB (pull_isLB hP₀ _) _) (pull_isLB (pull_isLB hP₀ _) _) H₁ ?_
  exact lbIso_square (pull_isLB hP₀ _) hP₀ (lbIso_refl (pull_isLB hP₀ sw₀)) e.symm

end GlobalTheory
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmLineBundleIsoDescendsSubringFinsetStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.SiegelDescent ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison


theorem _root_.GlobalTheory.T.symm_lineBundleIso_descends_subring_finset : ∀ (R : Type) [CommRing R] (S : Subring R) (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (B : Over (Sp S)) [GrpObj B] [IsCommMonObj B] (φ : A.left ⟶ B.left) (φ₂ : (G2 A).left ⟶ (G2 B).left) (P : LB (G2 A).left) (P₀ : LB (G2 B).left), IsAbelianScheme B → IsGrpPullback A B (spMap S.subtype) φ → IsSquare φ φ₂ → P.IsLB → P₀.IsLB → LBIso P (P₀.pull φ₂) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → ∃ F : Finset R, ∀ (R₁ : Subring R) (h : S ≤ R₁), (F : Set R) ⊆ R₁ → LBIso (P₀.pull (pφ₂ (spMap (Subring.inclusion h)) B)) ((P₀.pull (pφ₂ (spMap (Subring.inclusion h)) B)).pull (lift (snd ((Over.pullback (spMap (Subring.inclusion h))).obj B) ((Over.pullback (spMap (Subring.inclusion h))).obj B)) (fst ((Over.pullback (spMap (Subring.inclusion h))).obj B) ((Over.pullback (spMap (Subring.inclusion h))).obj B))).left) := by
  first | exact @GlobalTheory.symm_lbIso_descends_to_subring_containing_finset | exact GlobalTheory.symm_lbIso_descends_to_subring_containing_finset | (intros; apply GlobalTheory.symm_lbIso_descends_to_subring_containing_finset <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegPreDataDescends

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.SiegApprox

open GlobalTheory.SiegelDescent ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison

theorem model_exists : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (F : Finset R), IsAbelianScheme A → ∀ P : LB (G2 A).left, P.IsLB → ∃ (S : Subring R) (B : Over (Sp S)) (_ : GrpObj B) (_ : IsCommMonObj B) (φ : A.left ⟶ B.left) (φ₂ : (G2 A).left ⟶ (G2 B).left) (P₀ : LB (G2 B).left), (F : Set R) ⊆ S ∧ Algebra.FiniteType ℤ S ∧ IsAbelianScheme B ∧ IsGrpPullback A B (spMap S.subtype) φ ∧ IsSquare φ φ₂ ∧ P₀.IsLB ∧ LBIso P (P₀.pull φ₂) := GlobalTheory.T.exists_finiteType_subring_model_abelian_lineBundle

theorem rig_descends : ∀ (R : Type) [CommRing R] (S : Subring R) (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (B : Over (Sp S)) [GrpObj B] [IsCommMonObj B] (φ : A.left ⟶ B.left) (φ₂ : (G2 A).left ⟶ (G2 B).left) (P : LB (G2 A).left) (P₀ : LB (G2 B).left) (a : A ⟶ G2 A) (a₀ : B ⟶ G2 B), IsAbelianScheme B → IsGrpPullback A B (spMap S.subtype) φ → IsSquare φ φ₂ → P.IsLB → P₀.IsLB → LBIso P (P₀.pull φ₂) → a.left ≫ φ₂ = φ ≫ a₀.left → (∃ t : (P.pull a.left).Gen, t.IsGen) → ∃ F : Finset R, ∀ (R₁ : Subring R) (h : S ≤ R₁), (F : Set R) ⊆ R₁ → ∀ a₁ : (Over.pullback (spMap (Subring.inclusion h))).obj B ⟶ G2 ((Over.pullback (spMap (Subring.inclusion h))).obj B), a₁.left ≫ pφ₂ (spMap (Subring.inclusion h)) B = pφ (spMap (Subring.inclusion h)) B ≫ a₀.left → ∃ t : ((P₀.pull (pφ₂ (spMap (Subring.inclusion h)) B)).pull a₁.left).Gen, t.IsGen := GlobalTheory.T.exists_finset_generator_descends_subring

theorem symm_descends : ∀ (R : Type) [CommRing R] (S : Subring R) (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (B : Over (Sp S)) [GrpObj B] [IsCommMonObj B] (φ : A.left ⟶ B.left) (φ₂ : (G2 A).left ⟶ (G2 B).left) (P : LB (G2 A).left) (P₀ : LB (G2 B).left), IsAbelianScheme B → IsGrpPullback A B (spMap S.subtype) φ → IsSquare φ φ₂ → P.IsLB → P₀.IsLB → LBIso P (P₀.pull φ₂) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → ∃ F : Finset R, ∀ (R₁ : Subring R) (h : S ≤ R₁), (F : Set R) ⊆ R₁ → LBIso (P₀.pull (pφ₂ (spMap (Subring.inclusion h)) B)) ((P₀.pull (pφ₂ (spMap (Subring.inclusion h)) B)).pull (lift (snd ((Over.pullback (spMap (Subring.inclusion h))).obj B) ((Over.pullback (spMap (Subring.inclusion h))).obj B)) (fst ((Over.pullback (spMap (Subring.inclusion h))).obj B) ((Over.pullback (spMap (Subring.inclusion h))).obj B))).left) := GlobalTheory.T.symm_lineBundleIso_descends_subring_finset

end GlobalTheory.SiegApprox
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedAbelianSchemeDescendsFiniteType

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.PolModel

open GlobalTheory.SiegApprox GlobalTheory.SiegelDescent ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison

theorem polarised_descends : ∀ (B : Type) [CommRing B] (A : Over (Sp B)) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left), IsAbelianScheme A → P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∃ (B₀ : Subring B) (A₀ : Over (Sp B₀)) (_ : GrpObj A₀) (_ : IsCommMonObj A₀) (φ : A.left ⟶ A₀.left) (φ₂ : (G2 A).left ⟶ (G2 A₀).left) (P₀ : LB (G2 A₀).left), Algebra.FiniteType ℤ B₀ ∧ IsAbelianScheme A₀ ∧ IsGrpPullback A A₀ (spMap B₀.subtype) φ ∧ IsSquare φ φ₂ ∧ P₀.IsLB ∧ LBIso P (P₀.pull φ₂) ∧ (∃ t : (P₀.pull (lift (1 : A₀ ⟶ A₀) (𝟙 A₀)).left).Gen, t.IsGen) ∧ (∃ t : (P₀.pull (lift (𝟙 A₀) (1 : A₀ ⟶ A₀)).left).Gen, t.IsGen) ∧ LBIso P₀ (P₀.pull (lift (snd A₀ A₀) (fst A₀ A₀)).left) ∧ Out.RelAmple A₀ (P₀.pull (lift (𝟙 A₀) (𝟙 A₀)).left) := by
  intro R _ A _ _ P hA hP rig₁ rig₂ hsymm hamp
  classical
  obtain ⟨S, B, _, _, φ, φ₂, P₀, -, hS, hB, hφ, sq, hP₀, hw⟩ := model_exists R A ∅ hA P hP
  have one : (1 : A ⟶ A).left ≫ φ = φ ≫ (1 : B ⟶ B).left := one_comp hφ A B φ hφ.1.w
  have idφ : (𝟙 A : A ⟶ A).left ≫ φ = φ ≫ (𝟙 B : B ⟶ B).left := by simp
  obtain ⟨F₁, hF₁⟩ := rig_descends R S A B φ φ₂ P P₀ (lift 1 (𝟙 A)) (lift 1 (𝟙 B)) hB hφ sq hP hP₀ hw
    (lift_square sq one idφ) rig₁
  obtain ⟨F₂, hF₂⟩ := rig_descends R S A B φ φ₂ P P₀ (lift (𝟙 A) 1) (lift (𝟙 B) 1) hB hφ sq hP hP₀ hw
    (lift_square sq idφ one) rig₂
  obtain ⟨F₃, hF₃⟩ := symm_descends R S A B φ φ₂ P P₀ hB hφ sq hP hP₀ hw hsymm
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing ℤ S
  have := hB.proper
  have : Flat B.hom := by have := hB.smooth; infer_instance
  obtain ⟨F₄, hF₄⟩ := GlobalTheory.AmpleApprox.relAmple_spread_subring (pull_isLB hP₀ _) hφ.1 (pull_isLB hP _)
    (GlobalTheory.SiegelPull.diag_iso sq hw) hamp
  let F : Finset R := F₁ ∪ F₂ ∪ F₃ ∪ F₄
  obtain ⟨R₁, hSR, hFR, hR₁⟩ := GlobalTheory.KeyTf.exists_finiteType_subring_adjoin R S F hS
  have hF₁R : (F₁ : Set R) ⊆ R₁ := fun x hx => hFR (by simp [F, hx])
  have hF₂R : (F₂ : Set R) ⊆ R₁ := fun x hx => hFR (by simp [F, hx])
  have hF₃R : (F₃ : Set R) ⊆ R₁ := fun x hx => hFR (by simp [F, hx])
  have hF₄R : (F₄ : Set R) ⊆ R₁ := fun x hx => hFR (by simp [F, hx])
  let iS : Sp R₁ ⟶ Sp S := spMap (Subring.inclusion hSR)
  have hiS : spMap S.subtype = spMap R₁.subtype ≫ iS := by
    simp only [iS, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have hφ' : IsGrpPullback A B (spMap R₁.subtype ≫ iS) φ := hiS ▸ hφ
  have hφ₁ := ReciprocityTheory.ChartRestriction.G.Chart.isGrpPullback_factor iS (spMap R₁.subtype) hφ'
  set φ₁ := pullback.lift φ (A.hom ≫ spMap R₁.subtype) (by rw [hφ'.1.w, Category.assoc]) with hφ₁def
  let B₁ := (Over.pullback iS).obj B
  have hB₁ : IsAbelianScheme B₁ := GlobalTheory.isAbelianScheme_pullback_obj iS B hB
  have hψφ : φ₁ ≫ pφ iS B = φ := pullback.lift_fst _ _ _
  let φ₂₁ := (GlobalTheory.GenericSpread.sqMap hφ₁).left
  have sq₁ : IsSquare φ₁ φ₂₁ :=
    ⟨congrArg (fun z => z.left) (lift_fst (pushPt hφ₁.1.w (fst A A)) (pushPt hφ₁.1.w (snd A A))),
     congrArg (fun z => z.left) (lift_snd (pushPt hφ₁.1.w (fst A A)) (pushPt hφ₁.1.w (snd A A)))⟩
  have hψ₂ : φ₂₁ ≫ pφ₂ iS B = φ₂ := by
    apply adelic_GL2_ext_of_local_components
    · rw [Category.assoc, pφ₂_fst, ← Category.assoc, sq₁.1, Category.assoc, hψφ, sq.1]
    · rw [Category.assoc, pφ₂_snd, ← Category.assoc, sq₁.2, Category.assoc, hψφ, sq.2]
  have hP₁ : (P₀.pull (pφ₂ iS B)).IsLB := pull_isLB hP₀ _
  have r₁ := hF₁ R₁ hSR hF₁R (lift 1 (𝟙 B₁)) (lift_one_id iS B)
  have r₂ := hF₂ R₁ hSR hF₂R (lift (𝟙 B₁) 1) (lift_id_one iS B)
  have s₁ := hF₃ R₁ hSR hF₃R
  have sqp : IsSquare (G' := B₁) (G := B) (pφ iS B) (pφ₂ iS B) := ⟨pφ₂_fst iS B, pφ₂_snd iS B⟩
  have := hB₁.proper
  have amp : Out.RelAmple B₁ ((P₀.pull (pφ₂ iS B)).pull (lift (𝟙 B₁) (𝟙 B₁)).left) :=
    GlobalTheory.AmpleApprox.relAmple_of_lbIso_self (pull_isLB (pull_isLB hP₀ _) _) (pull_isLB hP₁ _)
      (GlobalTheory.SiegelPull.diag_iso sqp (GlobalTheory.lbIso_refl hP₁))
      (hF₄ R₁ hSR hF₄R B₁ (pφ iS B) (IsPullback.of_hasPullback B.hom iS))
  refine ⟨R₁, B₁, inferInstance, inferInstance, φ₁, φ₂₁, P₀.pull (pφ₂ iS B), hR₁, hB₁, hφ₁, sq₁, hP₁, ?_, r₁, r₂,
    s₁, amp⟩
  exact LBIso.trans hP (pull_isLB hP₀ _) (pull_isLB hP₁ _) hw
    (GlobalTheory.GenSpread.lbIso_pull_pull hP₀ φ₂₁ hψ₂.symm)

end GlobalTheory.PolModel
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedAbelianSchemeDescendsFiniteTypeStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev

theorem _root_.GlobalTheory.T.polarised_abelian_scheme_descends_finite_type : ∀ (B : Type) [CommRing B] (A : Over (Sp B)) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left), IsAbelianScheme A → P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∃ (B₀ : Subring B) (A₀ : Over (Sp B₀)) (_ : GrpObj A₀) (_ : IsCommMonObj A₀) (φ : A.left ⟶ A₀.left) (φ₂ : (G2 A).left ⟶ (G2 A₀).left) (P₀ : LB (G2 A₀).left), Algebra.FiniteType ℤ B₀ ∧ IsAbelianScheme A₀ ∧ IsGrpPullback A A₀ (spMap B₀.subtype) φ ∧ IsSquare φ φ₂ ∧ P₀.IsLB ∧ LBIso P (P₀.pull φ₂) ∧ (∃ t : (P₀.pull (lift (1 : A₀ ⟶ A₀) (𝟙 A₀)).left).Gen, t.IsGen) ∧ (∃ t : (P₀.pull (lift (𝟙 A₀) (1 : A₀ ⟶ A₀)).left).Gen, t.IsGen) ∧ LBIso P₀ (P₀.pull (lift (snd A₀ A₀) (fst A₀ A₀)).left) ∧ Out.RelAmple A₀ (P₀.pull (lift (𝟙 A₀) (𝟙 A₀)).left) := by
  first | (exact @GlobalTheory.PolModel.polarised_descends) | (exact GlobalTheory.PolModel.polarised_descends) | (intros; apply GlobalTheory.PolModel.polarised_descends  <;> assumption)
end
end
