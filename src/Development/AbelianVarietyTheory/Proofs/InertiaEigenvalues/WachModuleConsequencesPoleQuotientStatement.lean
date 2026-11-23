module

public import Formalism.SharpRestriction.LevelLetterCocycles.GammaSemisimpleLocalOfConsequences
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
public import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeHodgeTateJumpsFinite
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
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GammaEigenvalueOnWachLatticeQPowerQuotient
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProdGammaSubJumpUnitsAnnihilatesQuotient
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleInverseQuotientFreeFiniteCrystalline

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeHodgeTateJumpsFiniteStatement

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices


theorem _root_.GlobalTheory.T.crystallineLattice_hodgeTateJumps_finite : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → (Jumps (PD := (D.loc l).PD K) T).Finite := by
  first | exact @GlobalTheory.NL.JumpsFinite.jumps_finite | exact GlobalTheory.NL.JumpsFinite.jumps_finite | (intros; apply GlobalTheory.NL.JumpsFinite.jumps_finite <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GammaEigenvalueOnWachLatticeQPowerQuotientStatement

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gamma_eigenvalue_on_wachLattice_qPower_quotient : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ y : ℕ, 1 ≤ y → ∀ a ∈ Jumps (PD := (D.loc l).PD K) T, ∀ j : ℕ, 1 ≤ j → j ≤ y → ∃ x ∈ invN W T (W.Q ^ y), x ∉ W.N T ∧ W.γ T x - (((uU W ^ (-(a + j)) : (↥(OL LL))ˣ) : ↥(OL LL))) • x ∈ W.N T := by
  first | exact @GlobalTheory.NL.IntegralScalarUnits.occ | exact GlobalTheory.NL.IntegralScalarUnits.occ | (intros; apply GlobalTheory.NL.IntegralScalarUnits.occ <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProdGammaSubJumpUnitsAnnihilatesQuotientStatement

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_gamma_sub_jump_units_annihilates_quotient : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ y : ℕ, 1 ≤ y → ∀ Fs : Finset (↥(OL LL))ˣ, (∀ a ∈ Jumps (PD := (D.loc l).PD K) T, ∀ j : ℕ, 1 ≤ j → j ≤ y → uU W ^ (-(a + j)) ∈ Fs) → ∀ x ∈ invN W T (W.Q ^ y), Polynomial.aeval (W.γ T) (∏ c ∈ Fs, ((Polynomial.X : Polynomial ↥(OL LL)) - Polynomial.C (Units.val c))) x ∈ W.N T := by
  first | exact @GlobalTheory.NL.KillLevels.annihilate | exact GlobalTheory.NL.KillLevels.annihilate | (intros; apply GlobalTheory.NL.KillLevels.annihilate <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleInverseQuotientFreeFiniteCrystallineStatement

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachModule_inverseQuotient_free_finite_crystalline : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ y : ℕ, Module.Free ↥(OL LL) (quo W T (invN W T (W.Q ^ y)) (W.N T)) ∧ Module.Finite ↥(OL LL) (quo W T (invN W T (W.Q ^ y)) (W.N T)) := by
  first | exact @GlobalTheory.NL.QuoFree.quo_free_finite | exact GlobalTheory.NL.QuoFree.quo_free_finite | (intros; apply GlobalTheory.NL.QuoFree.quo_free_finite <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleConsequencesPoleQuotient

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.WachModulePoleQuotient



theorem wachModule_consequences_poleQuotient : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), gammaSemisimpleQuotientGlobal D HW F := by
  intro D HW F Cm
  unfold gammaSemisimpleQuotientGlobal gammaSemisimpleLocal GammaSemisimpleQuotient
  intro l _ K s LL h T hT y hy
  classical
  have hfr := GlobalTheory.T.wachModule_inverseQuotient_free_finite_crystalline D HW F l K s LL h T hT y
  have hJ := GlobalTheory.T.crystallineLattice_hodgeTateJumps_finite D HW l K s LL h T hT
  let Fs : Finset (↥(OL LL))ˣ := (hJ.toFinset ×ˢ Finset.Icc 1 y).image
    (fun p : ℤ × ℕ => uU ((HW l).W K s LL h) ^ (-(p.1 + (p.2 : ℤ))))
  have hmem : ∀ c, c ∈ Fs ↔ ∃ a ∈ Jumps (PD := (D.loc l).PD K) T, ∃ j : ℕ, 1 ≤ j ∧ j ≤ y ∧
      c = uU ((HW l).W K s LL h) ^ (-(a + j)) := by
    intro c
    simp only [Fs, Finset.mem_image, Finset.mem_product, Set.Finite.mem_toFinset, Finset.mem_Icc,
      Prod.exists]
    constructor
    · rintro ⟨a, j, ⟨ha, h1, h2⟩, rfl⟩
      exact ⟨a, ha, j, h1, h2, rfl⟩
    · rintro ⟨a, ha, j, h1, h2, rfl⟩
      exact ⟨a, j, ⟨ha, h1, h2⟩, rfl⟩
  refine ⟨hfr.1, hfr.2, Fs, ?_, ?_, ?_⟩
  · ext c
    exact hmem c
  · intro x hx
    exact GlobalTheory.T.prod_gamma_sub_jump_units_annihilates_quotient D HW F Cm l K s LL h T hT y hy Fs
      (fun a ha j h1 h2 => (hmem _).2 ⟨a, ha, j, h1, h2, rfl⟩) x hx
  · intro c hc
    obtain ⟨a, ha, j, h1, h2, rfl⟩ := (hmem c).1 hc
    obtain ⟨x, hx, hxN, hγ⟩ := GlobalTheory.T.gamma_eigenvalue_on_wachLattice_qPower_quotient D HW F Cm l K s LL h T hT y hy a ha j h1 h2
    exact ⟨x, hx, hxN, hγ⟩

end GlobalTheory.NL.WachModulePoleQuotient
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleConsequencesPoleQuotientStatement

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

theorem _root_.GlobalTheory.T.gammaSemisimpleQuotientD_statement : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), gammaSemisimpleQuotientGlobal D HW F := by
  first | exact @GlobalTheory.NL.WachModulePoleQuotient.wachModule_consequences_poleQuotient | exact GlobalTheory.NL.WachModulePoleQuotient.wachModule_consequences_poleQuotient | (intros; apply GlobalTheory.NL.WachModulePoleQuotient.wachModule_consequences_poleQuotient <;> assumption)
end
end
