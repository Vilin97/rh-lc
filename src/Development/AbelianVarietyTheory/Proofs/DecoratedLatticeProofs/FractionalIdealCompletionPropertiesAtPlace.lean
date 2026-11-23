module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LineLatAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacuaStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealCompletionLocallyPrincipal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InverseDifferentCompletionIffCharacterDual
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemScaledLatticeCompletionIffPolarisationInverseStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSpanSingletonMulIdealCompletionIff
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MulFractionalIdealCompletionSubsetIffMemQuotientStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodIdealZpowCompletionAdeleConjIff
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitIdealCompletionAtPlaceEqIntegralAdelesAtPlac

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealCompletionLocallyPrincipalStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.fractionalIdealCompletion_locally_principal : ∀ (D : D7) (v : Pl D) (𝔞 : FI D), 𝔞 ≠ 0 → ∃ x : D.host.E, x ≠ 0 ∧ ∀ s, s ∈ idV 𝔞 v ↔ incA D x⁻¹ * s ∈ intAt D (· = v) ∧ s ∈ idAt D (· = v) := by
  first | exact @GlobalTheory.IdVGen.idV_gen | exact GlobalTheory.IdVGen.idV_gen | (intros; apply GlobalTheory.IdVGen.idV_gen <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealLocallyPrincipalAdelic

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.FinPl.idV_principal_at : ∀ (D : D7) (v : Pl D) (𝔞 : FI D), 𝔞 ≠ 0 → ∃ g ∈ idV 𝔞 v, ∃ g' ∈ idAt D (· = v), (∀ s ∈ idAt D (· = v), g' * g * s = s) ∧ ∀ s, s ∈ idV 𝔞 v ↔ s ∈ idAt D (· = v) ∧ g' * s ∈ intAt D (· = v) := by
  intro D v 𝔞 h𝔞
  obtain ⟨x, hx0, hx⟩ := GlobalTheory.T.fractionalIdealCompletion_locally_principal D v 𝔞 h𝔞
  obtain ⟨ε, hεε, -, hεint, hεid, -⟩ := (GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (· = v)).1
  have hεI : ε ∈ idAt D (· = v) := hεint.1
  have hxx : incA D x⁻¹ * incA D x = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hx0, map_one]
  refine ⟨incA D x * ε, ?_, incA D x⁻¹ * ε, Ideal.mul_mem_left _ _ hεI, ?_, ?_⟩
  · rw [hx]
    refine ⟨?_, Ideal.mul_mem_left _ _ hεI⟩
    rw [← mul_assoc, hxx, one_mul]; exact hεint
  · intro s hs
    have : incA D x⁻¹ * ε * (incA D x * ε) = ε * ε := by
      calc incA D x⁻¹ * ε * (incA D x * ε) = (incA D x⁻¹ * incA D x) * (ε * ε) := by ring
        _ = ε * ε := by rw [hxx, one_mul]
    rw [this, hεε]; exact (hεid s).1 hs
  · intro s
    rw [hx]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h2, ?_⟩
      rw [mul_assoc, (hεid s).1 h2]; exact h1
    · rintro ⟨h2, h1⟩
      refine ⟨?_, h2⟩
      rw [mul_assoc, (hεid s).1 h2] at h1; exact h1
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealLocallyPrincipalAdelicStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.fractionalIdeal_locallyPrincipal_adelic : ∀ (D : D7) (v : Pl D) (𝔞 : FI D), 𝔞 ≠ 0 → ∃ g ∈ idV 𝔞 v, ∃ g' ∈ idAt D (· = v), (∀ s ∈ idAt D (· = v), g' * g * s = s) ∧ ∀ s, s ∈ idV 𝔞 v ↔ s ∈ idAt D (· = v) ∧ g' * s ∈ intAt D (· = v) := by
  first | exact @GlobalTheory.FinPl.idV_principal_at | exact GlobalTheory.FinPl.idV_principal_at | (intros; apply GlobalTheory.FinPl.idV_principal_at <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InverseDifferentCompletionIffCharacterDualStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.inverseDifferentCompletion_iff_characterDual : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (v : Pl D), ∀ s ∈ idAt D (· = v), s ∈ idV (dI D) v ↔ ∀ o ∈ intAt D (· = v), psiE ψ (s * o) = 1 := by
  first | exact @GlobalTheory.SeeSaw.DiffDual.idV_dI_iff | exact GlobalTheory.SeeSaw.DiffDual.idV_dI_iff | (intros; apply GlobalTheory.SeeSaw.DiffDual.idV_dI_iff <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSpanSingletonMulIdealCompletionIffStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.mem_spanSingleton_mul_idealCompletion_iff : ∀ (D : D7) (v : Pl D) (𝔞 : FI D) (x : D.host.E), x ≠ 0 → ∀ s, s ∈ idV (FractionalIdeal.spanSingleton _ x * 𝔞) v ↔ incA D x⁻¹ * s ∈ idV 𝔞 v ∧ s ∈ idAt D (· = v) := by
  first | exact @GlobalTheory.SeeSaw.idV_spanSingleton_mul_iff | exact GlobalTheory.SeeSaw.idV_spanSingleton_mul_iff | (intros; apply GlobalTheory.SeeSaw.idV_spanSingleton_mul_iff <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodIdealZpowCompletionAdeleConjIffStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.periodIdealZpow_completion_adeleConj_iff : ∀ (D : D7) (v : Pl D) (n : ℤ) (s : AE D), s ∈ idV (D.host.AA ^ n) v ↔ cA D s ∈ idV (D.host.AAbar ^ n) v := by
  first | exact @GlobalTheory.SeeSaw.idV_AA_zpow_conj | exact GlobalTheory.SeeSaw.idV_AA_zpow_conj | (intros; apply GlobalTheory.SeeSaw.idV_AA_zpow_conj <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitIdealCompletionAtPlaceEqIntegralAdelesAtPlacStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.unitIdealCompletionAtPlace_eq_integralAdelesAtPlace : ∀ (D : D7) (v : Pl D) (a : AE D), a ∈ idV (1 : FI D) v ↔ a ∈ intAt D (· = v) := by
  first | exact @GlobalTheory.SeeSaw.idV_one_eq_intAt | exact GlobalTheory.SeeSaw.idV_one_eq_intAt | (intros; apply GlobalTheory.SeeSaw.idV_one_eq_intAt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealCompletionPropertiesAtPlace

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw

theorem idV_props : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ v : Pl D, (∀ a, a ∈ idV (1 : FI D) v ↔ a ∈ intAt D (· = v)) ∧ (∀ 𝔞 𝔟 : FI D, 𝔞 ≠ 0 → 𝔟 ≠ 0 → ∀ s ∈ idAt D (· = v), (∀ a ∈ idV 𝔞 v, s * a ∈ idV 𝔟 v) ↔ s ∈ idV (𝔟 * 𝔞⁻¹) v) ∧ (∀ (𝔞 : FI D) (x : D.host.E), x ≠ 0 → ∀ s, s ∈ idV (FractionalIdeal.spanSingleton _ x * 𝔞) v ↔ incA D x⁻¹ * s ∈ idV 𝔞 v ∧ s ∈ idAt D (· = v)) ∧ (∀ n : ℤ, ∀ s, s ∈ idV (D.host.AA ^ n) v ↔ cA D s ∈ idV (D.host.AAbar ^ n) v) ∧ (∀ s ∈ idAt D (· = v), s ∈ idV (dI D) v ↔ ∀ o ∈ intAt D (· = v), psiE ψ (s * o) = 1) ∧ (∀ 𝔞 : FI D, 𝔞 ≠ 0 → ∃ g ∈ idV 𝔞 v, ∃ g' ∈ idAt D (· = v), (∀ s ∈ idAt D (· = v), g' * g * s = s) ∧ ∀ s, s ∈ idV 𝔞 v ↔ s ∈ idAt D (· = v) ∧ g' * s ∈ intAt D (· = v)) ∧ ∀ (S : HSp D) (L : Lat S) (y : Fin S.rank → AE D), y ∈ latA S L (· = v) ↔ (∀ i, y i ∈ idAt D (· = v)) ∧ ∀ s ∈ idV D.host.AA⁻¹ v, s • y ∈ latV S L (· = v) := fun D ψ hψ v =>
  ⟨GlobalTheory.T.unitIdealCompletionAtPlace_eq_integralAdelesAtPlace D v, GlobalTheory.T.mul_fractionalIdealCompletion_subset_iff_mem_quotient D v, GlobalTheory.T.mem_spanSingleton_mul_idealCompletion_iff D v, fun n s => GlobalTheory.T.periodIdealZpow_completion_adeleConj_iff D v n s,
    GlobalTheory.T.inverseDifferentCompletion_iff_characterDual D ψ hψ v, GlobalTheory.T.fractionalIdeal_locallyPrincipal_adelic D v, GlobalTheory.T.mem_scaledLatticeCompletion_iff_polarisationInverse D v⟩

end GlobalTheory.SeeSaw

end
end
end
