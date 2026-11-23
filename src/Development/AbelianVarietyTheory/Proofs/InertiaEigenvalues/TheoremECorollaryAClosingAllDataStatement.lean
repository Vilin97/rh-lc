module

public import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineAndDecompletion
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFullFaithfulExactPsiStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLiftingTheoremEHypothesesAdmittedStatement
public import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineMapLemmas
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapDcrisEqDdRCrystallineUnramified
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.SharpRestriction.LevelLetterCocycles.SecondComparisonInCoordinates
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitVectorOfUnitFor
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalTheoremOfInputs

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecordCaseA

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.Per.DdREqDcris

theorem record_caseA : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (K LL : FinExt l), CaseA K LL →
    Formalism.MainNotions.TruncatedSeriesCountingBounds.DdREqDcris ((D.loc l).PD K) ↥LL.1 := by
  intro D l _ K LL _ hb V _ _ _ _ _ ρ _ _ _ hc
  exact map_Dcris_eq_DdR l (D.loc l) (D.locA l) (D.locT l) K LL hb V ρ hc

end GlobalTheory.Per.DdREqDcris
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitGenExists

section

@[expose] public section

noncomputable section

namespace GlobalTheory.WachUnit

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

theorem unitGen_exists : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), ∃ e, Formalism.MainNotions.WachCoordinates.Br.UnitGen ((HW l).W K s LL h) e := by
  intro D HW F l _ K s LL h
  obtain ⟨e, -, -, -, -, hN, -, hφ, hγ, hfree⟩ := GlobalTheory.WachUnit.unitVector D HW F l K s LL h
  exact ⟨e, hN, hφ, hγ, hfree⟩

end GlobalTheory.WachUnit
end
end
end

-- Source module: Formalism.SharpRestriction.LevelLetterCocycles.LocalCorollaryConstant

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.N.Ln03

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br

def localCorollaryConstant : ℝ := Classical.choose corollary_local_exists_constant

theorem local_corollary_of_de_rham (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (CR E1 E2 : ℝ) (hE1 : E1 = 800) (hE2 : localCorollaryConstant ≤ E2)
    (hDdR : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l), CaseA K LL →
      Formalism.MainNotions.TruncatedSeriesCountingBounds.DdREqDcris ((D.loc l).PD K) ↥LL.1)
    (h9 : Formalism.MainNotions.LocalSituation.adm9 D HW F) (hFont : Formalism.MainNotions.InvariantsGenerators.LitFont D HW F)
    (hUG : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (h : CaseA K LL), 5 ≤ l →
      ∃ e, UnitGen ((HW l).W K 1 LL h.2.2) e) :
    Stmt D HW F Cm CR E1 E2 := by
  have h := Classical.choose_spec corollary_local_exists_constant
  intro hA
  subst hE1
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16⟩ := hA
  obtain ⟨t1, c2, pr2, l3⟩ := a1
  have hP3 : Formalism.MainNotions.DeltaInvariantLattices.P3 D HW F Cm := fun l _ K s LL hg => (t1 l K s LL hg).2.2.1
  have hP4 : Formalism.MainNotions.DeltaInvariantLattices.P4 D HW F Cm := fun l _ K s LL hg => (t1 l K s LL hg).2.2.2.1
  have hP5 : Formalism.MainNotions.DeltaInvariantLattices.P5 D HW F := fun l _ K s LL hg => (t1 l K s LL hg).2.2.2.2.1
  have hP6 : Formalism.MainNotions.DeltaInvariantLattices.P6 D HW F := fun l _ K s LL hg => (t1 l K s LL hg).2.2.2.2.2.1
  have hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F := fun l _ K s LL hg => (t1 l K s LL hg).2.2.2.2.2.2.2.2.1
  have hP2a : Formalism.MainNotions.DeltaInvariantLattices.Pr2a D HW F := fun l _ K s LL hg => (pr2 l K s LL hg).1
  have r := h D HW F Cm CR hP3 hP4 hP5 hP6 hP9 hP2a l3 a3 a4 a7 a8 a9 a10 a12 a14 hDdR h9 hFont hUG
  exact ⟨r.1, r.2 E2 hE2⟩

end Formalism.MainNotions.N.Ln03
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TheoremECorollaryAClosingAllData

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.ThmECorA

open Formalism.BasicNotions.Loc

theorem closing (hBK : GlobalTheory.Published.BlochKatoLocal) (hTD : Formalism.GaloisCohomology.LocalTateDualityK)
    (hEC : Formalism.GaloisCohomology.LocalEulerCharK) :
    ∃ C₀ : ℝ, ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
      WachCoordinates.Conclusion1 D 800 ∧ ∀ C₂ : ℝ, C₀ ≤ C₂ → WachCoordinates.Conclusion2 D C₂ := by
  refine ⟨Formalism.MainNotions.N.Ln03.localCorollaryConstant, fun D HW F Cm => ?_⟩
  have hDdR := fun (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (h : CaseA K LL) =>
    GlobalTheory.Per.DdREqDcris.record_caseA D l K LL h
  have h9 := GlobalTheory.Decompl.fontaine_and_decompletion D HW F
  have hFont := GlobalTheory.T.fontaine_fullFaithful_exact_psi D HW F
  have hUG : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (h : CaseA K LL), 5 ≤ l →
      ∃ e, Formalism.MainNotions.WachCoordinates.Br.UnitGen ((HW l).W K 1 LL h.2.2) e :=
    fun l _ K LL h _ => GlobalTheory.WachUnit.unitGen_exists D HW F l K 1 LL h.2.2
  have hA := GlobalTheory.T.localLifting_theoremE_hypotheses_admitted hBK hTD hEC D HW F Cm
  refine ⟨(Formalism.MainNotions.N.Ln03.local_corollary_of_de_rham D HW F Cm 10 800 _ rfl le_rfl hDdR h9 hFont hUG hA).1, fun C₂ hC₂ => ?_⟩
  exact (Formalism.MainNotions.N.Ln03.local_corollary_of_de_rham D HW F Cm 10 800 C₂ rfl hC₂ hDdR h9 hFont hUG hA).2

end GlobalTheory.ThmECorA
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TheoremECorollaryAClosingAllDataStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

theorem _root_.GlobalTheory.T.theoremE_corollaryA_closing_all_data : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∃ C₀ : ℝ, ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), WachCoordinates.Conclusion1 D 800 ∧ ∀ C₂ : ℝ, C₀ ≤ C₂ → WachCoordinates.Conclusion2 D C₂ := by
  first | exact @GlobalTheory.ThmECorA.closing | exact GlobalTheory.ThmECorA.closing | (intros; apply GlobalTheory.ThmECorA.closing <;> assumption)
end
end
