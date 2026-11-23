module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Formalism.SharpRestriction.LevelLetterCocycles.ElementDenominator
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineRestrictFiniteExtensionJumpsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1fGeneratedLatticeStatement
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineBounds
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsBisRest
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftingTheoremWachModuleLemmaHypothesesAdmittedStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalConstantsFromAdmittedLocalGaloisStatementsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictionCorestrictionH1fStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StrictAdm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleLocalConclusionsUsedFormsStatement
public import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ElementDenominatorAdm7

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem elementDenominator_adm7 : ∀ D : D7, Formalism.MainNotions.ElementDenominator.adm7 D := by
  intro D l _ _ K LL _ T _
  haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  exact @GlobalTheory.T.h1f_generated_lattice l _ (D.loc l) (D.locA l) (D.locT l) K LL (Fintype.ofFinite _) T _

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ElementDenominatorAdm7Statement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

theorem _root_.GlobalTheory.T.adm7_elementDenominator : ∀ D : D7, Formalism.MainNotions.ElementDenominator.adm7 D := by
  first | exact @GlobalTheory.elementDenominator_adm7 | exact GlobalTheory.elementDenominator_adm7 | (intros; apply GlobalTheory.elementDenominator_adm7 <;> assumption)
end
end

-- Source module: Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.WachRestrictionOfLiftingPackage

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions

theorem lifting_local_of_package (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C CA CB CK : ℝ) (h : Formalism.MainNotions.LiftingTheory.aux₃ D HW F C CA CB CK) :
    Formalism.MainNotions.LiftingTheory.ConclusionL D HW F := h.1

theorem wach_of_lifting_package (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C CA CB CK : ℝ) (h : Formalism.MainNotions.LiftingTheory.aux₃ D HW F C CA CB CK) :
    Formalism.MainNotions.LiftingTheory.ConclusionW D HW F := h.2.1

theorem lift_of_lifting_package (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C CA CB CK : ℝ) (h : Formalism.MainNotions.LiftingTheory.aux₃ D HW F C CA CB CK) :
    Formalism.MainNotions.LiftingTheory.LiftTheoremAllCases D HW F CA CB CK := h.2.2.2.2.2.2.2

end Formalism.MainNotions.N
end
end
end

-- Source module: Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ArchimedeanSignatureMatchingOfLiftingTheory

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions

theorem archimedean_signature_matching_of_liftingTheory (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (CA : ℝ) (CB : ℝ) (CK : ℝ) (C : ℝ)
    (h54 : Formalism.MainNotions.LiftingTheory.aux₃ D HW F C CA CB CK) :
    Formalism.MainNotions.ElementDenominator.ArchimedeanSignatureMatching D HW F CA CB CK := by
  unfold Formalism.MainNotions.ElementDenominator.ArchimedeanSignatureMatching
  exact lift_of_lifting_package D HW F C CA CB CK h54

theorem lifting_input_five_of_lifting (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C CA CB CK : ℝ)
    (h54 : Formalism.MainNotions.LiftingTheory.aux₃ D HW F C CA CB CK) :
    Formalism.MainNotions.ElementDenominator.adm5 D HW F := by
  unfold Formalism.MainNotions.ElementDenominator.adm5
  exact wach_of_lifting_package D HW F C CA CB CK h54

theorem lifting_input_six_of_lifting (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C CA CB CK : ℝ)
    (h54 : Formalism.MainNotions.LiftingTheory.aux₃ D HW F C CA CB CK) :
    Formalism.MainNotions.ElementDenominator.adm6 D HW F := by
  unfold Formalism.MainNotions.ElementDenominator.adm6
  exact lifting_local_of_package D HW F C CA CB CK h54

end Formalism.MainNotions.N
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLiftingTheoremAHypothesesAdmitted

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.AdmittedPartOne

theorem all_admitted : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK →
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
      ElementDenominator.Adm1 D HW F Cm 23 32 32 := by
  intro hBK hTD hEC D HW F Cm
  have hU := (GlobalTheory.T.wachModuleLocalConclusions_usedForms D HW F Cm).1
  have h54 := GlobalTheory.T.localConstants_from_admitted_local_Galois_statements hBK hTD hEC D HW F Cm
  have hA := (GlobalTheory.T.liftingTheorem_wachModuleLemma_hypotheses_admitted D HW F Cm).1
  refine ⟨hU.1, hU.2.2.1, GlobalTheory.T.restriction_corestriction_H1f D HW F, hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    GlobalTheory.AdmHerrLocal.main D HW F, hU.2.2.2, archimedean_signature_matching_of_liftingTheory D HW F 23 32 32 10 h54,
    lifting_input_five_of_lifting D HW F 10 23 32 32 h54, lifting_input_six_of_lifting D HW F 10 23 32 32 h54,
    GlobalTheory.T.adm7_elementDenominator D, GlobalTheory.Per.FontaineAdm.fontaine_bounds D, GlobalTheory.Per.StrictAdm.strict_adm D, GlobalTheory.T.crystalline_restrict_finite_extension_jumps D⟩

end GlobalTheory.AdmittedPartOne
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLiftingTheoremAHypothesesAdmittedStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

theorem _root_.GlobalTheory.T.localLifting_theoremA_hypotheses_admitted : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), ElementDenominator.Adm1 D HW F Cm 23 32 32 := by
  first | exact @GlobalTheory.AdmittedPartOne.all_admitted | exact GlobalTheory.AdmittedPartOne.all_admitted | (intros; apply GlobalTheory.AdmittedPartOne.all_admitted <;> assumption)
end
end
