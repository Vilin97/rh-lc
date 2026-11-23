module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRepSuppSplit
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisOSumSmul
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAlgebraicStdCharHalfSymplecticRealPartZeroStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPointActsOnVacuumByAlgebraicScalarStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RationalTranslateAlgebraicCombination
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SupportSplitAlgebraicCombination
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumValueAlgebraicCongruence
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsRatRealAlgebraicCombinationTwist

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
namespace GlobalTheory.MovedAlgRat
theorem rat_real_algebraic_combination_of_moved : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X → ∀ (t : T), ∀ γ ∈ Formalism.L2.Theta.GQ A, ∀ a ∈ GinfC A, ∀ γ' ∈ Formalism.L2.Theta.GQ WW, ∀ a' ∈ GinfC WW,
      γ * a ∈ GfC A → γ' * a' ∈ GfC WW →
      ∃ (n : ℕ) (c : Fin n → ℂ) (w : Fin n → WO (GlobalTheory.Grid.neg A) WW), (∀ p, IsAlgebraic ℚ (c p)) ∧
        (∀ p, (w p).map (infPart D) = 0) ∧
        X.ω t (γ * a, γ' * a') X.vac = ∑ p, c p • heisO W.ψ (GlobalTheory.Grid.neg A) WW (w p) X.vac := by
  intro D T _ L μ₀ sc G W i j A A' WW X hP hI hL hX t γ hγ a ha γ' hγ' a' ha' hfin hfin'
  obtain ⟨C, hC, hCe⟩ := GlobalTheory.T.realPoint_acts_on_vacuum_by_algebraicScalar hX t γ hγ a ha γ' hγ' a' ha' hfin hfin'
  have hR : GlobalTheory.MovedAlg.IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t (γ, γ') X.vac) :=
    _root_.GlobalTheory.T.rationally_moved_vector_algebraic hP hI hL hX t γ hγ a ha γ' hγ' a' ha' hfin hfin'
  have e : X.ω t (γ * a, γ' * a') X.vac = C • X.ω t (γ, γ') X.vac := by
    have hm : ((γ * a, γ' * a') : GA D A × GA D WW) = (γ, γ') * (a, a') := rfl
    rw [hm, map_mul, Module.End.mul_apply, hCe, map_smul]
  rw [e]
  exact GlobalTheory.MovedAlg.IsAlgComb.smul hC hR
end GlobalTheory.MovedAlgRat
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

theorem _root_.GlobalTheory.T.exists_rat_real_algebraic_combination_twist : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X → ∀ (t : T), ∀ γ ∈ Formalism.L2.Theta.GQ A, ∀ a ∈ GinfC A, ∀ γ' ∈ Formalism.L2.Theta.GQ WW, ∀ a' ∈ GinfC WW,
      γ * a ∈ GfC A → γ' * a' ∈ GfC WW →
      ∃ (n : ℕ) (c : Fin n → ℂ) (w : Fin n → WO (GlobalTheory.Grid.neg A) WW), (∀ p, IsAlgebraic ℚ (c p)) ∧
        (∀ p, (w p).map (infPart D) = 0) ∧
        X.ω t (γ * a, γ' * a') X.vac = ∑ p, c p • heisO W.ψ (GlobalTheory.Grid.neg A) WW (w p) X.vac := by
  first | exact @_root_.GlobalTheory.MovedAlgRat.rat_real_algebraic_combination_of_moved | exact _root_.GlobalTheory.MovedAlgRat.rat_real_algebraic_combination_of_moved | (intros; apply _root_.GlobalTheory.MovedAlgRat.rat_real_algebraic_combination_of_moved <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.VacuumVectorAtLevelMemFockAlgebraic

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section
namespace GlobalTheory.LevelVac
variable {D : D7}


theorem level_vacuum_vector_algebraic : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X → ∀ (t : T), ∃ N : ℕ, 0 < N ∧ ∀ k ∈ GfC A, ∀ k' ∈ GfC WW, GlobalTheory.Member.FinCong A N k →
      GlobalTheory.Member.FinCong WW N k' → ∃ ζ : ℂ, IsAlgebraic ℚ ζ ∧ X.ω t (k, k') X.vac = ζ • X.vac := by
  intro D T _ L μ₀ sc G W i j A A' WW X _ _ _ hX t
  have hI := hX.is
  obtain ⟨N, hN, h⟩ := exists_level_fix (S := GlobalTheory.Grid.neg A) (T := WW) (om := (X.ω t).toSgn true) (hI.weil t)
    (sS := fun τ => -X.rA.s τ) (fun τ => GlobalTheory.Grid.isCartanInv_sgn true A τ (hI.rigA.2.2 τ).1)
    (fun τ => (hI.rigW.2.2 τ).1) (GlobalTheory.RowTest.isSelfDualC_neg' hI.rigA.1) hI.rigW.1 hI.rigA.2.1 hI.rigW.2.1 hI.isVac
  refine ⟨N, hN, fun k hk k' hk' hc hc' => ⟨1, isAlgebraic_one, ?_⟩⟩
  rw [one_smul]
  exact h ((GlobalTheory.Grid.ofSgn true A).symm k) hk k' hk' hc hc'
end GlobalTheory.LevelVac
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

theorem _root_.GlobalTheory.T.vacuum_vector_at_level_mem_fockAlgebraic : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X → ∀ (t : T), ∃ N : ℕ, 0 < N ∧ ∀ k ∈ GfC A, ∀ k' ∈ GfC WW, GlobalTheory.Member.FinCong A N k →
      GlobalTheory.Member.FinCong WW N k' → ∃ ζ : ℂ, IsAlgebraic ℚ ζ ∧ X.ω t (k, k') X.vac = ζ • X.vac := by
  first | exact @_root_.GlobalTheory.LevelVac.level_vacuum_vector_algebraic | exact _root_.GlobalTheory.LevelVac.level_vacuum_vector_algebraic | (intros; apply _root_.GlobalTheory.LevelVac.level_vacuum_vector_algebraic <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.MovedTranslateEqAlgebraicCombination

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section
namespace GlobalTheory.MovedAlg
theorem moved_translate_eq_algebraic_combination : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∀ (t : T), ∀ x ∈ GfC A, ∀ h ∈ GfC WW, ∀ u : WO (GlobalTheory.Grid.neg A) WW, u.map (infPart D) = 0 →
      ∃ (n : ℕ) (c : Fin n → ℂ) (w : Fin n → WO (GlobalTheory.Grid.neg A) WW), (∀ p, IsAlgebraic ℚ (c p)) ∧
        (∀ p, (w p).map (infPart D) = 0) ∧
        X.ω t (x, h) (heisO W.ψ (GlobalTheory.Grid.neg A) WW u X.vac) = ∑ p, c p • heisO W.ψ (GlobalTheory.Grid.neg A) WW (w p) X.vac := by
  intro D T _ L μ₀ sc G W i j A A' WW X hP hI hL hX t x hx h hh u hu
  have hψ : ∀ u v : WO (GlobalTheory.Grid.neg A) WW, u.map (infPart D) = 0 → v.map (infPart D) = 0 →
      IsAlgebraic ℚ (W.ψ (symplOH (GlobalTheory.Grid.neg A) WW u v)) := fun u v hu hv =>
    GlobalTheory.T.isAlgebraic_stdChar_halfSymplectic_realPart_zero hX.is.isVac.1 _ _ u v hu hv
  obtain ⟨N, hN, hlev⟩ := _root_.GlobalTheory.T.vacuum_vector_at_level_mem_fockAlgebraic hP hI hL hX t
  obtain ⟨γ, hγ, a, ha, s, hs, k, hk, hx', hkc, hss⟩ := GlobalTheory.UnRep.Space.exists_rep_suppSplit D A N hN x
  obtain ⟨γ', hγ', a', ha', s', hs', k', hk', hh', hkc', hss'⟩ := GlobalTheory.UnRep.Space.exists_rep_suppSplit D WW N hN h
  have hga : γ * a ∈ GfC A := by
    have e : γ * a = x * k⁻¹ * s⁻¹ := by rw [hx']; group
    rw [e]
    exact mul_mem (mul_mem hx (inv_mem hk)) (inv_mem hs)
  have hga' : γ' * a' ∈ GfC WW := by
    have e : γ' * a' = h * k'⁻¹ * s'⁻¹ := by rw [hh']; group
    rw [e]
    exact mul_mem (mul_mem hh (inv_mem hk')) (inv_mem hs')
  have hpair : ((x, h) : GA D A × GA D WW) = (γ * a, γ' * a') * ((s, s') * (k, k')) := by
    rw [hx', hh']
    simp only [Prod.mk_mul_mk, mul_assoc]
  obtain ⟨ζ, hζ, hkv⟩ := hlev k hk k' hk' hkc hkc'
  have h1 : IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t (s, s') X.vac) :=
    _root_.GlobalTheory.T.moved_support_theta_algebraic hP hI hL hX t N hN s hs s' hs' hss hss'
  have h2 : IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t ((s, s') * (k, k')) X.vac) := by
    rw [map_mul, Module.End.mul_apply, hkv, map_smul]
    exact h1.smul hζ
  have h3 : IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t (γ * a, γ' * a') X.vac) :=
    _root_.GlobalTheory.T.exists_rat_real_algebraic_combination_twist hP hI hL hX t γ hγ a ha γ' hγ' a' ha' hga hga'
  have h4 : IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t (x, h) X.vac) := by
    rw [hpair, map_mul, Module.End.mul_apply]
    exact om_algComb hX hψ t _ _ h3 h2
  have h5 : IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (heisO W.ψ (GlobalTheory.Grid.neg A) WW u X.vac) :=
    ⟨1, fun _ => 1, fun _ => u, fun _ => isAlgebraic_one, fun _ => hu, by simp⟩
  exact om_algComb hX hψ t x h h4 h5
end GlobalTheory.MovedAlg
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

theorem _root_.GlobalTheory.T.twisted_moved_translate_algebraic : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∀ (t : T), ∀ x ∈ GfC A, ∀ h ∈ GfC WW, ∀ u : WO (GlobalTheory.Grid.neg A) WW, u.map (infPart D) = 0 →
      ∃ (n : ℕ) (c : Fin n → ℂ) (w : Fin n → WO (GlobalTheory.Grid.neg A) WW), (∀ p, IsAlgebraic ℚ (c p)) ∧
        (∀ p, (w p).map (infPart D) = 0) ∧
        X.ω t (x, h) (heisO W.ψ (GlobalTheory.Grid.neg A) WW u X.vac) = ∑ p, c p • heisO W.ψ (GlobalTheory.Grid.neg A) WW (w p) X.vac := by
  first | exact @_root_.GlobalTheory.MovedAlg.moved_translate_eq_algebraic_combination | exact _root_.GlobalTheory.MovedAlg.moved_translate_eq_algebraic_combination | (intros; apply _root_.GlobalTheory.MovedAlg.moved_translate_eq_algebraic_combination <;> assumption)
end
end
end
