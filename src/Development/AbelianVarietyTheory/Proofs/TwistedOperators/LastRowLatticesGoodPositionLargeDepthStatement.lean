module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsTameFinitePlaceHermitianAll
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselFlagCharacterPrimitiveRowTestMovedLatticeStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselLastVectorMemHomLatticeIffIntegralStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TiltSc
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeColumnsOffFiniteSet
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StaircaseLatticeIsotropicLineIdealIff
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealLineOfPeriodsOnLine
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridRowMovedLatticeSplitsBesselLargeDepthStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridRowMovedLatticeSplitsJacobiLargeDepthStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridRowZeroBasePointCarriesLatticeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualGridRowMovedLatticeLargeDepthStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiFlagCharPrimitiveMovedLatticeLargeDepthStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiToBesselCarriesFlagLinesRowPeriodSuccStatement
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LatNotSelfDual
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridStandardVacuumScalarEqProdLocalPlaces
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelCharactersUnramifiedOffLevelPlaces
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagGenDiag
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowBesZeroE
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastSeesawLineMapKeepsLatticesLargeDepthStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegLineLatticeAndBesselCoreLatticeSelfDualSplit
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PosNormLineSelfDualAndTopLatticeSplitsStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumBasePointMovesRowLatticesStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselToJacobiBasePointCarriesRowLatticeLines

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped nonZeroDivisors

namespace GlobalTheory.RowColsBF

open GlobalTheory.RowShape GlobalTheory.RowChain GlobalTheory.StairCols

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem tiltSc_odd {j : ℕ} (hj : Odd j) (p : Fin (D.R.m - 1 - j)) (hp : 2 * p.1 < D.R.m - 1 - j) :
    tiltSc D j p = (D.host.xi0 ^ p.1)⁻¹ := by
  rw [tiltSc, if_pos hj, if_pos hp]

theorem tiltSc_even {j : ℕ} (hj : ¬ Odd j) (p : Fin (D.R.m - 1 - j)) : tiltSc D j p = 1 := by
  rw [tiltSc, if_neg hj]

theorem besCol_eq (G : GridData L sc) (j σ : ℕ) (hj : j + 2 * σ + 2 = D.R.m) (i : Fin σ) (a : AE D) :
    GlobalTheory.FinPl.colMul (besDecAt G j σ hj).jX i a =
      fun k => (a * incA D (D.host.xi0 ^ i.1)) * incA D ((G.rowDec j (by omega)).a k (Fin.castLE (by omega) i)) := by
  funext k
  simp only [GlobalTheory.FinPl.colMul, HypDec.jX, besDecAt, diagDec, rowBes, besDec, HermitianOrthogonalExtensionData.iso, rat, Matrix.map_apply,
    Matrix.mul_diagonal, Matrix.submatrix_apply, lam, id_eq, map_mul]
  ring

theorem jacCol_eq (G : GridData L sc) (j σ : ℕ) (hj : j + 2 * σ + 2 = D.R.m) (i : Fin σ) (a : AE D) :
    GlobalTheory.FinPl.colMul (xZero (rowJac G (j + 1) (by omega) σ (by omega))) i a =
      fun k => a * incA D ((G.rowDec (j + 1) (by omega)).a k (Fin.castLE (by omega) i)) := rfl

theorem cols (G : GridData L sc) (j σ : ℕ) (hj : j + 2 * σ + 2 = D.R.m) (v : GlobalTheory.FinPl.Pl D) :
    GlobalTheory.FinPl.ColsAt (besDecAt G j σ hj) (xZero (rowJac G (j + 1) (by omega) σ (by omega)))
      (rowN G j) (rowN G (j + 1)) v := by
  intro i a ha
  have hjm : j < D.R.m := by omega
  have hjm' : j + 1 < D.R.m := by omega
  obtain ⟨k, hk⟩ := D.R.m_even
  have hev : ¬ Odd j := by
    rw [Nat.not_odd_iff_even]; exact ⟨k - σ - 1, by omega⟩
  have hod : Odd (j + 1) := ⟨k - σ - 1, by omega⟩
  rw [besCol_eq G j σ hj i a, jacCol_eq G j σ hj i a]
  have l1 : rowN G j = (G.rowDec j hjm).lat (G.Λ (.top j)) (rowId D j) := dif_pos hjm
  have l2 : rowN G (j + 1) = (G.rowDec (j + 1) hjm').lat (G.Λ (.top (j + 1))) (rowId D (j + 1)) := dif_pos hjm'
  have hpr : (Fin.castLE (by omega : σ ≤ D.R.m - 1 - j) i).rev ≠ Fin.castLE (by omega) i := fun e => by
    have := congrArg Fin.val e
    simp only [Fin.val_rev, Fin.val_castLE] at this
    omega
  have hqr : (Fin.castLE (by omega : σ ≤ D.R.m - 1 - (j + 1)) i).rev ≠ Fin.castLE (by omega) i := fun e => by
    have := congrArg Fin.val e
    simp only [Fin.val_rev, Fin.val_castLE] at this
    omega
  rw [GlobalTheory.FinPl.latV, l1, col_mem_iff (G.rowDec j hjm) _ hpr _ _ 1 {1}
    (fun x hx => by rw [Set.mem_singleton_iff.1 hx]; exact FractionalIdeal.one_mem_one _)
    (fun x hx => by
      obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hx
      exact ⟨1, rfl, o, (one_mul _).symm⟩) v]
  rw [GlobalTheory.FinPl.latA, l2, col_mem_iff (G.rowDec (j + 1) hjm') _ hqr _ _ D.host.AA {a | a ∈ D.host.AA} (fun x hx => hx)
    (fun x hx => ⟨x, hx, 1, by simp⟩) v]
  have e3 : D.host.AA * rowId D (j + 1) (Fin.castLE (by omega) i) =
      FractionalIdeal.spanSingleton _ (D.host.xi0 ^ i.1)⁻¹ * (1 * rowId D j (Fin.castLE (by omega) i)) := by
    rw [rowId, rowId, tiltSc_even hev, tiltSc_odd hod _ (by simp only [Fin.val_castLE]; omega),
      FractionalIdeal.spanSingleton_one, one_mul, one_mul, stairId, stairId]
    simp only [Fin.val_castLE]
    have h1 : D.R.m - 1 - j - i.1 = (D.R.m - 1 - (j + 1) - i.1) + 1 := by omega
    rw [h1, pow_succ]
    ring
  rw [e3, GlobalTheory.StairLine.mem_idV_inv_mul (pow_ne_zero _ (GlobalTheory.Unf.Inhab.cmHost_imaginaryGenerator_ne_zero D)), mul_comm a]

theorem colsAt_bf : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ j σ (hj : j + 2 * σ + 2 = D.R.m) v,
    GlobalTheory.FinPl.ColsAt (besDecAt ch.G j σ hj) (xZero (rowJac ch.G (j + 1) (by omega) σ (by omega)))
      (GlobalTheory.RowShape.rowN ch.G j) (GlobalTheory.RowShape.rowN ch.G (j + 1)) v :=
  ⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ => fun j σ hj v => cols ch.G j σ hj v⟩⟩

end GlobalTheory.RowColsBF
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselToJacobiBasePointCarriesRowLatticeLinesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.besselToJacobi_basePoint_carries_row_lattice_lines : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ j σ (hj : j + 2 * σ + 2 = D.R.m) v, GlobalTheory.FinPl.ColsAt (besDecAt ch.G j σ hj) (xZero (rowJac ch.G (j + 1) (by omega) σ (by omega)))
    (GlobalTheory.RowShape.rowN ch.G j) (GlobalTheory.RowShape.rowN ch.G (j + 1)) v := by
  first | exact @GlobalTheory.RowColsBF.colsAt_bf | exact GlobalTheory.RowColsBF.colsAt_bf | (intros; apply GlobalTheory.RowColsBF.colsAt_bf <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastRowCharsUnramifiedOffTensorPlaces

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LastRowUnram

theorem chars_unram : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ (t : T) (v : GlobalTheory.FinPl.Pl D), (∀ w ∈ locPl ch.G t, w.under (𝓞 D.host.F) ≠ v) → ∀ i, i < D.R.m →
    GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (ch.G.chrS (.mu t D.R.m i)) v ∧ GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (ch.G.chrT (.mu t D.R.m i)) v := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch _ _ => ?_⟩⟩
  intro t v hv i hi
  classical
  have hL : R.toLevCh.Is A.μ0 := hS.core.lev
  have hS0 := GlobalTheory.RowVacScalar.notMem_S0_of_no_place_above ch.G t hv
  have hQ : ∀ PP ∈ R.toLevCh.Q t, PP ∈ locPl ch.G t := fun PP h => by
    unfold locPl
    exact Finset.mem_union_right _ h
  have hmu : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (R.toLevCh.mu t (i + 1)) v := by
    refine GlobalTheory.SeeSaw.LevelTest.charUnramAt_of fun w hw => ?_
    show GlobalTheory.LFun.UnrAt (R.toLevCh.mu0 (i + 1) * R.toLevCh.xi t) w
    refine GlobalTheory.LFun.UnrAt.mul ?_ ?_
    · refine (GlobalTheory.LFun.unrAt_iff_of_chrEq (hL.mu0 ⟨i, hi⟩) w).2 ((R.toLevCh.C.isMu0 ⟨i, hi⟩).unr w fun k hk => ?_)
      refine hS0 (ch.G.pl.mem_S0_of_sum_eq.2 (Or.inr ((GlobalTheory.ChiGrid.S1_mem_OmF D).2 ?_)))
      have : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (w.under (𝓞 D.host.F)).asIdeal := by
        show algebraMap _ (𝓞 D.host.E) _ ∈ w.asIdeal
        rw [map_natCast]; exact hk
      rw [hw] at this
      fin_cases k
      · exact Or.inl this
      · exact Or.inr (Or.inl this)
    · refine (GlobalTheory.LFun.unrAt_iff_of_chrEq (hL.xi t) w).2 ?_
      by_contra hu
      rcases (hL.Q_ram t w).1 hu with h | ⟨P', hP', hc⟩
      · exact hv w (hQ w h) hw
      · exact hv P' (hQ P' hP') ((GlobalTheory.LevelPlaces.under_eq_of_isConjPl hc).trans hw)
  have key := GlobalTheory.RowVacScalar.attChr_charUnramAt hmu (GlobalTheory.RowVacScalar.eta_charUnramAt hL v)
  exact ⟨key _, key _⟩

end GlobalTheory.LastRowUnram
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastRowCharsUnramifiedOffTensorPlacesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.lastRowChars_unramified_off_tensorPlaces : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ (t : T) (v : GlobalTheory.FinPl.Pl D), (∀ w ∈ locPl ch.G t, w.under (𝓞 D.host.F) ≠ v) → ∀ i, i < D.R.m →
    GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (ch.G.chrS (.mu t D.R.m i)) v ∧ GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (ch.G.chrT (.mu t D.R.m i)) v := by
  first | exact @GlobalTheory.LastRowUnram.chars_unram | exact GlobalTheory.LastRowUnram.chars_unram | (intros; apply GlobalTheory.LastRowUnram.chars_unram <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegLineLatticeAndBesselCoreLatticeSelfDualSplitStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.negLineLattice_and_besselCoreLattice_selfDual_split : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ j σ, j + 2 * σ + 2 = D.R.m → IsSelfDualC _ (GlobalTheory.RowShape.lineL D j) ∧
    IsSelfDualC _ (GlobalTheory.RowShape.coreL ch.G j) ∧ ∀ v, GlobalTheory.FinPl.OrthAt (GlobalTheory.OrthSumExists.orthDecHsum D (ch.G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D))
      (GlobalTheory.RowShape.coreL ch.G j) (ch.G.Λ (.top j)) (GlobalTheory.RowShape.lineL D j) v := by
  first | exact @GlobalTheory.RowShape.coreL_selfDual_split | exact GlobalTheory.RowShape.coreL_selfDual_split | (intros; apply GlobalTheory.RowShape.coreL_selfDual_split <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastRowLatticesGoodPositionLargeDepth

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowShape



theorem shapeAt_big : Big fun ch => ShapeAt ch := by
  refine big_mono (fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch h => ?_)
    ((((((((((((((GlobalTheory.T.gridRow_zero_basePoint_carriesLattice).and GlobalTheory.T.vacuum_base_point_moves_row_lattices).and GlobalTheory.T.posNormLine_selfDual_and_topLattice_splits).and GlobalTheory.T.negLineLattice_and_besselCoreLattice_selfDual_split).and GlobalTheory.T.isSelfDual_gridRowMovedLattice_largeDepth).and GlobalTheory.T.gridRowMovedLattice_splits_bessel_largeDepth).and GlobalTheory.T.gridRowMovedLattice_splits_jacobi_largeDepth).and GlobalTheory.T.besselFlag_character_primitive_rowTest_movedLattice).and GlobalTheory.T.jacobiFlagChar_primitive_movedLattice_largeDepth).and
      GlobalTheory.T.besselToJacobi_basePoint_carries_row_lattice_lines).and GlobalTheory.T.jacobiToBessel_carries_flagLines_rowPeriod_succ).and GlobalTheory.T.besselLastVector_mem_homLattice_iff_integral).and GlobalTheory.T.lastSeesawLineMap_keeps_lattices_largeDepth).and GlobalTheory.T.lastRowChars_unramified_off_tensorPlaces)
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hmv0, hmvS⟩, htop⟩, hcore⟩, hsd⟩, hmB⟩, hmJ⟩, hpB⟩, hpJ⟩, hcBF⟩, hcFB⟩, hlast⟩, hkap⟩, hun⟩ := h
  have hmv : ∀ (t : T) (b : Pts ch.G), IsBase t ch.S.B b → ∀ j, j ≤ D.R.m → GlobalTheory.FinPl.Moves _ (b j) (ch.G.Λ (.grid D.R.m j)) (GlobalTheory.RowShape.rowN ch.G j) fun _ => True := fun t b hb j hj => by
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact hmv0 t b hb
    · exact hmvS t b hb j hj0 hj
  have hX : ∀ k, k ≤ D.R.m → IsSelfDualC (ch.G.V (.top k)) (ch.G.Λ (.top k)) := fun k hk =>
    (ch.G.isV (X := .top k) (by show k ≤ D.R.m; omega) (fun _ e => Node.noConfusion e)).sd
  refine ⟨GlobalTheory.RowShape.rowN ch.G, GlobalTheory.RowShape.coreL ch.G, GlobalTheory.RowShape.lineL D, GlobalTheory.RowShape.topL D, hmv, htop.1, htop.2,
    fun t M hM j σ hj vN v => ?_⟩
  obtain ⟨hLL, hN0, hO⟩ := hcore j σ hj
  refine ⟨hLL, hO v, ?_, ?_, ?_, ?_⟩
  · exact
      { tame := GlobalTheory.FinPl.TamePlaces.tame D v
        sdV := hsd j (by omega)
        sdV₀ := hN0
        sdW := hsd (j + 1) (by omega)
        sdW₀ := hX (j + 1) (by omega)
        monoV := hmB j σ hj v
        monoW := hmJ (j + 1) (by omega) σ (by omega) v
        prim := hpB j σ hj v
        cols := hcBF j σ hj v
        last := fun hσ a ha => hlast j σ hj v hσ a ha }
  · intro i hi hi'
    subst hi
    exact
      { tame := GlobalTheory.FinPl.TamePlaces.tame D v
        sdV := hsd i (by omega)
        sdV₀ := hX i (by omega)
        sdW := hsd (i + 1) (by omega)
        sdW₀ := hN0
        monoV := hmJ i (by omega) (σ + 1) (by omega) v
        monoW := hmB (i + 1) σ (by omega) v
        prim := hpJ i (by omega) (σ + 1) (by omega) v
        cols := hcFB i σ hi' v }
  · intro hσ w hw
    subst hσ
    exact hkap j (by omega) v w hw
  · exact fun hoff i hi => hun t v hoff i hi
end GlobalTheory.RowShape

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastRowLatticesGoodPositionLargeDepthStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.lastRowLatticesGoodPosition_large_depth : Big fun ch => ShapeAt ch := by
  first | exact @GlobalTheory.RowShape.shapeAt_big | exact GlobalTheory.RowShape.shapeAt_big | (intros; apply GlobalTheory.RowShape.shapeAt_big <;> assumption)
end
end
