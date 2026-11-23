module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RootOfUnityThetaTwist
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsDetRootFinPartOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsFinOf
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RepresentationAtEveryPlace
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealLineOfPeriodsOnLine
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealLineOfPeriodsOnLine
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RepresentationAtEveryPlaceStatement
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsColumnUnitVacuaFamilyMoved
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingJointDataTwistRatioAtDetRootsStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumBasePointUniqueAllTuples
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsDetRoot
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NormEmbeddingHostFormConstantEq
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryPointPrescribedLocalMatrices

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowLocBig

theorem exists_hasLoc_big : Big fun ch => ∀ t (j : ℕ) (hj : j ≤ _)
    (g : ∀ w : GlobalTheory.FunObj.locPl ch.G t, GL (Fin ((GlobalTheory.FunObj.locGrid ch.G t w.1).rank (_, j))) (GlobalTheory.FunObj.Kw w.1)),
    ∃ r, HasLoc t ch.S.B hj r g :=
  ⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s ch _ _ t _ hj g =>
    GlobalTheory.RowRep.exists_hasLoc s.core.lev ch.S.B t hj g⟩⟩

end GlobalTheory.RowLocBig
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryPointPrescribedLocalMatricesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_unitaryPoint_prescribed_localMatrices : Big fun ch => ∀ t (j : ℕ) (hj : j ≤ _) (g : ∀ w : GlobalTheory.FunObj.locPl ch.G t, GL (Fin ((GlobalTheory.FunObj.locGrid ch.G t w.1).rank (_, j))) (GlobalTheory.FunObj.Kw w.1)), ∃ r, HasLoc t ch.S.B hj r g := by
  first | exact @GlobalTheory.RowLocBig.exists_hasLoc_big | exact GlobalTheory.RowLocBig.exists_hasLoc_big | (intros; apply GlobalTheory.RowLocBig.exists_hasLoc_big <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsVacuumBasePointFamilyEveryTuple

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.RowBase

theorem exists_isBase : Big fun ch => ∀ t, ∃ b, IsBase t ch.S.B b := by
  refine GlobalTheory.RowReal.big_mono ?_ (Big.and GlobalTheory.T.representation_at_every_place GlobalTheory.T.exists_unitaryPoint_prescribed_localMatrices)
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch ⟨hrep, hloc⟩ t
  classical
  let β0 : CosFam ch.G t := fun _ _ => DoubleCoset.mk _ _ 1
  obtain ⟨b', hb'⟩ := (hrep 1 t).1 β0
  have H : ∀ j, ∃ x : GA D (ch.G.V (.grid D.R.m j)),
      (j ∈ idx D → ∃ δ, IsTilt ch.G j δ ∧ IsFinOf δ x) ∧ (j ∉ idx D → x = 1) := by
    intro j
    by_cases hj : j ∈ idx D
    · have hle : j ≤ D.R.m := by have := GlobalTheory.RowRep.idx_le hj; omega
      obtain ⟨δ, -, hδ, -⟩ := hb'.2 j hj hle
      obtain ⟨x, hx⟩ := GlobalTheory.RowRep.exists_isFinOf _ δ
      exact ⟨x, fun _ => ⟨δ, hδ, hx⟩, fun h => absurd hj h⟩
    · exact ⟨1, fun h => absurd h hj, fun _ => rfl⟩
  choose f hf using H
  obtain ⟨r, hr⟩ := hloc t 0 (Nat.zero_le _) (fun w => (stair (locGrid ch.G t w.1) (unifAt w.1) (cosExp ch.G w.1) 0)⁻¹)
  refine ⟨Function.update f 0 r, ?_, ?_, ?_⟩
  · rw [Function.update_self]; exact hr
  · intro j hj
    have h0 : j ≠ 0 := by have := GlobalTheory.RowRep.idx_le hj; omega
    rw [Function.update_of_ne h0]
    exact (hf j).1 hj
  · intro j h0 hj
    rw [Function.update_of_ne h0]
    exact (hf j).2 hj

end GlobalTheory.RowBase
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsVacuumBasePointFamilyEveryTupleStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_vacuumBasePointFamily_every_tuple : Big fun ch => ∀ t, ∃ b, IsBase t ch.S.B b := by
  first | exact @GlobalTheory.RowBase.exists_isBase | exact GlobalTheory.RowBase.exists_isBase | (intros; apply GlobalTheory.RowBase.exists_isBase <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.TwistCharacterMemTwistFiniteValueProductSubgroup

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.XiVals

theorem xi_mem : Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t : T) (x : (AE D)ˣ),
    Circle.toUnits (R.toLevCh.xi t x) ∈ xiVals R.toLevCh t :=
  ⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hS _ _ _ t x =>
    GlobalTheory.ColVac.xi_mem_xiVals hS.core.lev t x⟩⟩

end GlobalTheory.XiVals

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.TwistCharacterMemTwistFiniteValueProductSubgroupStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.twistCharacter_mem_twistFiniteValueProductSubgroup : Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t : T) (x : (AE D)ˣ), Circle.toUnits (R.toLevCh.xi t x) ∈ xiVals R.toLevCh t := by
  first | exact @GlobalTheory.XiVals.xi_mem | exact GlobalTheory.XiVals.xi_mem | (intros; apply GlobalTheory.XiVals.xi_mem <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumBasePointUniqueAllTuplesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.vacuumBasePoint_unique_all_tuples : Big fun ch => ∀ t t' b b', IsBase t ch.S.B b → IsBase t' ch.S.B b' → b = b' := by
  first | exact @GlobalTheory.RowBaseUniq.isBase_unique | exact GlobalTheory.RowBaseUniq.isBase_unique | (intros; apply GlobalTheory.RowBaseUniq.isBase_unique <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldedVacuaDifferByTwistValuesLargeDepth

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowVacTw

theorem circ_id (A B A' B' : Circle) : A'⁻¹ * B' = (A⁻¹ * B) * ((A' * A⁻¹)⁻¹ * (B' * B⁻¹)) := by
  apply Circle.ext
  have := Circle.coe_ne_zero A
  have := Circle.coe_ne_zero B
  have := Circle.coe_ne_zero A'
  have := Circle.coe_ne_zero B'
  simp only [Circle.coe_mul, Circle.coe_inv]
  field_simp



theorem vacTw : Big fun ch => VacTw ch := by
  obtain ⟨C, h⟩ := Big.and (Big.and GlobalTheory.T.exists_vacuumBasePointFamily_every_tuple GlobalTheory.T.vacuumBasePoint_unique_all_tuples) (Big.and GlobalTheory.T.twistCharacter_mem_twistFiniteValueProductSubgroup GlobalTheory.T.unfoldingJointData_twist_ratio_at_detRoots)
  refine ⟨C, fun ε CF hC => ?_⟩
  obtain ⟨x₀, h⟩ := h ε CF hC
  refine ⟨x₀, fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch hi ha => ?_⟩
  obtain ⟨⟨hex, hun⟩, hxv, hcon⟩ := h D large₂ he hx Γ Pl0 T A Ks R F s ch hi ha
  have hL := s.core.lev
  classical
  let xr : ∀ k, GA D (ch.G.V (.grid D.R.m k)) → (AE D)ˣ := fun k g => (GlobalTheory.RecDict.exists_isDetRoot D _ g).choose
  have hxr : ∀ k g, IsDetRoot _ g (xr k g) := fun k g => (GlobalTheory.RecDict.exists_isDetRoot D _ g).choose_spec
  let bb : T → Pts ch.G := fun t => (hex t).choose
  have hbb : ∀ t, IsBase t ch.S.B (bb t) := fun t => (hex t).choose_spec
  let w : T → ℕ → Circle := fun t j =>
    (R.toLevCh.xi t (xr j (bb t j)))⁻¹ * R.toLevCh.xi t (xr (j + 2) (bb t (j + 2)))
  refine ⟨hex, fun t j => Circle.toUnits (w t j), fun t j => ?_, ?_⟩
  · simp only [w, map_mul, map_inv]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hxv t _)) (hxv t _)
  intro t t' M M' hM hM' b b' hb hb' P p hp j hj hjm
  have e1 : b = bb t := hun t t b (bb t) hb (hbb t)
  have e2 : b' = bb t := hun t' t b' (bb t) hb' (hbb t)
  have e3 : bb t' = bb t := hun t' t _ _ (hbb t') (hbb t)
  subst e1 e2
  have hfin : ∀ k, ∃ y : (AE D)ˣ, finPart D (y : AE D) = 1 ∧ IsDetRoot _ (p k) y := fun k =>
    GlobalTheory.TwistFinPart.exists_isDetRoot_finPart_one _ (p k) (hp.1 k) _ (hxr k (p k))
  choose y hy1 hy using hfin
  have hx : ∀ k, IsDetRoot _ ((p * bb t) k) (y k * xr k (bb t k)) := fun k =>
    GlobalTheory.ExtCore.isDetRoot_mul _ _ _ _ _ (hy k) (hxr k (bb t k))
  have hm2 := D.R.two_le_m
  have hmi : D.R.m ∉ idx D := fun h' => by
    simp only [idx, List.mem_range'_1] at h'
    omega
  have hm : (p * bb t) D.R.m = 1 := by
    rw [Pi.mul_apply, hp.2 _ hmi, (hbb t).2.2 _ (by omega) hmi, one_mul]
  rw [hcon t t' M M' hM hM' P (p * bb t) _ hx hm j hj hjm, smul_smul]
  congr 1
  obtain ⟨n, hn0, hn⟩ := hL.xi_fin t
  obtain ⟨n', hn0', hn'⟩ := hL.xi_fin t'
  have h1 : ∀ k, R.toLevCh.xi t (y k) = 1 := fun k => GlobalTheory.TupRoot.eq_one_of_finPart (hL.xi t) hn0 hn _ (hy1 k)
  have h1' : ∀ k, R.toLevCh.xi t' (y k) = 1 := fun k => GlobalTheory.TupRoot.eq_one_of_finPart (hL.xi t') hn0' hn' _ (hy1 k)
  have hw : w t' j = w t j * (((R.toLevCh.xi t' * (R.toLevCh.xi t)⁻¹) (y j * xr j (bb t j)))⁻¹ *
      (R.toLevCh.xi t' * (R.toLevCh.xi t)⁻¹) (y (j + 2) * xr (j + 2) (bb t (j + 2)))) := by
    simp only [w, e3, MonoidHom.mul_apply, MonoidHom.inv_apply, map_mul, h1, h1', inv_one, one_mul]
    exact circ_id _ _ _ _
  show ((Circle.toUnits (w t' j) : ℂˣ) : ℂ) = ((Circle.toUnits (w t j) : ℂˣ) : ℂ) * _
  rw [hw, map_mul, Units.val_mul]
  rfl

end GlobalTheory.RowVacTw

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldedVacuaDifferByTwistValuesLargeDepthStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.unfoldedVacua_differ_by_twist_values_largeDepth : Big fun ch => VacTw ch := by
  first | exact @GlobalTheory.RowVacTw.vacTw | exact GlobalTheory.RowVacTw.vacTw | (intros; apply GlobalTheory.RowVacTw.vacTw <;> assumption)
end
end
