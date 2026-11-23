module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Development.AbelianVarietyTheory.Definitions.Divisors.InstCMHostS
public import Formalism.LocalToGlobal.IndefiniteReal.ConjSubConjSub
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseLevelVectorOfPrincipalLevelFixed
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodFixedVectorOfTypeOccurringInRows
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicIsometryMatchingFrames
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryMatchesParahoricLevels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SignAtBasePlaceEqEmbedding
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePlacesNotPairwiseConjugate
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockFrameConjugationIdentity
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarRowsLevelCharacterEqLiftsLevelCharacter
import Formalism.LocalToGlobal.IndefiniteReal.ConjSubConjSub

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseLevelVectorOfPrincipalLevelFixedStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

theorem _root_.GlobalTheory.T.exists_baseLevel_vector_of_principalLevel_fixed : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) {s : ℕ}, A.fam.Ok s → Core R F → (∀ χ ∈ A.X, chiIdem χ * lvlIdem F.P0 F.ψ0 ≠ 0) → ∀ {n : ℕ} (PY : principalLevelFrame.RowPsi (Yc D 0) n) (π : Formalism.L2.NG.FinTyp D.host.E n) (v : Formalism.AUTREP.GAf D.host.E n → ℂ), v ∈ π.S → v ≠ 0 → principalLevelFrame.IsTypeVec (PY.ψ ⁻¹' levS _ (R.βY 0) (R.dat0 R.triv)) (fun _ => 1) v → (∀ κ : G → Formalism.AUTREP.GAf D.host.E n, (∀ g, IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g) (PY.ψ (κ g))) → ∑ g, RealDat.eC (A := A) D.what₂.embLL g • Formalism.L2.NG.rt D.host.E n (κ g) v = v) → ∃ x ∈ π.S, x ≠ 0 ∧ principalLevelFrame.IsTypeVec (PY.ψ ⁻¹' levS _ (R.βY 0) (R.dat0 (R.levR F false))) (fun κ => levChi _ (R.βY 0) (R.dat0 (R.levR F false)) (PY.ψ κ)) x := by
  first | exact @GlobalTheory.BaseVec.exists_base_vec | exact GlobalTheory.BaseVec.exists_base_vec | (intros; apply GlobalTheory.BaseVec.exists_base_vec <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodFixedVectorOfTypeOccurringInRowsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

theorem _root_.GlobalTheory.T.exists_good_fixed_vector_of_type_occurring_in_rows : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) {s : ℕ}, A.fam.Ok s → Core R F → ∀ {n : ℕ} (PY : principalLevelFrame.RowPsi (Yc D 0) n) π, π ∈ principalLevelFrame.OccRows R.θ PY (R.MY 0) (fun b => (levS _ (R.βY 0) (R.dat0 (R.levR F b)))) (fun b => (levChi _ (R.βY 0) (R.dat0 (R.levR F b)))) (fun _ => R.e0) → ∃ v ∈ (principalLevelFrame.FinTyp.conjT π).S, v ≠ 0 ∧ principalLevelFrame.IsTypeVec (PY.ψ ⁻¹' levS _ (R.βY 0) (R.dat0 R.triv)) (fun _ => 1) v ∧ ∀ κ : G → Formalism.AUTREP.GAf D.host.E n, (∀ g, IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g) (PY.ψ (κ g))) → ∑ g, RealDat.eC (A := A) D.what₂.embLL g • Formalism.L2.NG.rt D.host.E n (κ g) v = v := by
  first | exact @GlobalTheory.OccRowVec.exists_vec_of_occRows | exact GlobalTheory.OccRowVec.exists_vec_of_occRows | (intros; apply GlobalTheory.OccRowVec.exists_vec_of_occRows <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelsStandardFramesConjugateStandardGroup

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

noncomputable section

namespace GlobalTheory.FrameMove

variable {D : D7}

theorem levChi_datY (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (r t : ℕ) (hr : r ≤ V.rank) (Pg : Finset (Pl D.host.E))
    (P : LevelP Pg r ℂ) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (κ : GA D V) :
    levChi V β (datY V.rank r t 0 hr Pg ∅ P χ ξ Frm.B) κ =
      ((ext1 P.H P.chi (rTup β (datY V.rank r t 0 hr Pg ∅ P χ ξ Frm.B) (finE V κ)) : ℂˣ) : ℂ) := by
  unfold levChi levFn
  simp [datY]
  rfl



theorem frame_move : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → ∀ (i : Fin D.R.m) {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (PY : principalLevelFrame.RowPsi (Yc D 0) n) (PW : principalLevelFrame.RowPsi (Wc D i) n), StdPsi hF PY → StdPsi hF PW → ∀ P : LevelP R.Pg D.R.r ℂ, ∃ h : Formalism.AUTREP.GAf D.host.E n, ∀ κ, PW.ψ κ ∈ levS _ (R.βW i) (R.datWp i P) → PY.ψ (h⁻¹ * κ * h) ∈ levS _ (R.βY 0) (R.dat0 P) ∧ levChi _ (R.βW i) (R.datWp i P) (PW.ψ κ) = levChi _ (R.βY 0) (R.dat0 P) (PY.ψ (h⁻¹ * κ * h)) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC i n hF PY PW hY hW P
  obtain ⟨c, hc⟩ := hC.lev.βY 0 (Fin.pos i)
  obtain ⟨c', hc'⟩ := hC.lev.βW i
  have hrk : (Yc D 0).rank = (Wc D i).rank := GlobalTheory.PartDims.rank_zeroth_component_eq.trans (GlobalTheory.PartDims.rank_weight_component_eq i).symm
  obtain ⟨j, Φ, hΦ⟩ := GlobalTheory.FinIsoExists.exists_isFinIso (Yc D 0) (Wc D i) (R.βY 0) (R.ΛY 0) _ (R.βW i) (R.ΛW i) _ R.Pg
    hrk hc hc' (GlobalTheory.TypePlaces.not_isConjPl R.C.P R.Pg hC.lev.Pg)
  obtain ⟨h, hh⟩ := GlobalTheory.KapIsot.frames_inner (Yc D 0) (Wc D i) hF PY PW hY hW
    (by rw [GlobalTheory.PartDims.rank_zeroth_component_eq]; exact GlobalTheory.KapIsot.odd_r D.R) _ _ _ j Φ hΦ
  refine ⟨h, fun κ hκ => ?_⟩
  have hx := hh (h⁻¹ * κ * h)
  rw [show h * (h⁻¹ * κ * h) * h⁻¹ = κ by group] at hx
  obtain ⟨l1, l2⟩ := GlobalTheory.LevTrans.levtrans (Yc D 0) (Wc D i) (R.βY 0) (R.βW i) D.R.r D.R.t (r_le_Y 0) (r_le_rank_Wc i) R.Pg R.chi
    (fun _ _ => 1) j Φ hΦ ⟨PY.ψ (h⁻¹ * κ * h), PY.into _⟩
  rw [hx] at l1 l2
  obtain ⟨hp, hH⟩ := mem_lev.1 hκ.2
  have hpY := l1.2 hp
  have hrt : rTup (R.βW i) (R.datWp i P) (finE (Wc D i) (PW.ψ κ)) =
      rTup (R.βY 0) (R.dat0 P) (finE (Yc D 0) (PY.ψ (h⁻¹ * κ * h))) := l2 hpY
  refine ⟨?_, ?_⟩
  · show PY.ψ (h⁻¹ * κ * h) ∈
      (GfC (Yc D 0) ⊓ (lev D.sp.cm (Yc D 0).gram (R.βY 0) (R.dat0 P)).comap (finE (Yc D 0)) : Subgroup _)
    refine Subgroup.mem_inf.2 ⟨PY.into _, ?_⟩
    show finE (Yc D 0) (PY.ψ (h⁻¹ * κ * h)) ∈ lev D.sp.cm (Yc D 0).gram (R.βY 0) (R.dat0 P)
    refine mem_lev.2 ⟨hpY, ?_⟩
    rw [← hrt]
    exact hH
  · have e1 : levChi (Wc D i) (R.βW i) (R.datWp i P) (PW.ψ κ) =
        ((ext1 P.H P.chi (rTup (R.βW i) (R.datWp i P) (finE (Wc D i) (PW.ψ κ))) : ℂˣ) : ℂ) :=
      levChi_datY (Wc D i) (R.βW i) D.R.r D.R.t (r_le_rank_Wc i) R.Pg P (fun _ _ => 1) (fun _ => 1) (PW.ψ κ)
    have e2 : levChi (Yc D 0) (R.βY 0) (R.dat0 P) (PY.ψ (h⁻¹ * κ * h)) =
        ((ext1 P.H P.chi (rTup (R.βY 0) (R.dat0 P) (finE (Yc D 0) (PY.ψ (h⁻¹ * κ * h)))) : ℂˣ) : ℂ) :=
      levChi_datY (Yc D 0) (R.βY 0) D.R.r D.R.t (r_le_Y 0) R.Pg P R.chi (fun _ => 1) (PY.ψ (h⁻¹ * κ * h))
    rw [e1, e2, hrt]

end GlobalTheory.FrameMove

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelsStandardFramesConjugateStandardGroupStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

theorem _root_.GlobalTheory.T.levels_standardFrames_conjugate_standardGroup : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → ∀ (i : Fin D.R.m) {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (PY : principalLevelFrame.RowPsi (Yc D 0) n) (PW : principalLevelFrame.RowPsi (Wc D i) n), StdPsi hF PY → StdPsi hF PW → ∀ P : LevelP R.Pg D.R.r ℂ, ∃ h : Formalism.AUTREP.GAf D.host.E n, ∀ κ, PW.ψ κ ∈ levS _ (R.βW i) (R.datWp i P) → PY.ψ (h⁻¹ * κ * h) ∈ levS _ (R.βY 0) (R.dat0 P) ∧ levChi _ (R.βW i) (R.datWp i P) (PW.ψ κ) = levChi _ (R.βY 0) (R.dat0 P) (PY.ψ (h⁻¹ * κ * h)) := by
  first | exact @GlobalTheory.FrameMove.frame_move | exact GlobalTheory.FrameMove.frame_move | (intros; apply GlobalTheory.FrameMove.frame_move <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarRowsLevelCharacterEqLiftsLevelCharacterStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

theorem _root_.GlobalTheory.T.star_rows_level_character_eq_lifts_level_character : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (b : Bool) (g : GA D (Yc D 0)), star (levChi _ (R.βY 0) (R.dat0 (R.levR F b)) g) = levChi _ (R.βY 0) (R.dat0 (R.levL F b (sg0 D A))) g := by
  first | exact @GlobalTheory.ChiStarLev.star_levChi_levR | exact GlobalTheory.ChiStarLev.star_levChi_levR | (intros; apply GlobalTheory.ChiStarLev.star_levChi_levR <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowTypeExistsBaseLevelVector

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

noncomputable section

namespace GlobalTheory.RowTypeVec

theorem vec_of_rows : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) {s : ℕ}, A.fam.Ok s → Core R F → (∀ χ ∈ A.X, chiIdem χ * lvlIdem F.P0 F.ψ0 ≠ 0) → ∀ {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (PY : principalLevelFrame.RowPsi (Yc D 0) n) (PW : ∀ i, principalLevelFrame.RowPsi (Wc D i) n), StdPsi hF PY → (∀ i, StdPsi hF (PW i)) → ∀ π, π ∈ principalLevelFrame.OccRows R.θ PY (R.MY 0) (fun b => (levS _ (R.βY 0) (R.dat0 (R.levR F b)))) (fun b => (levChi _ (R.βY 0) (R.dat0 (R.levR F b)))) (fun _ => R.e0) → ∀ i, ∃ x ∈ π.S, x ≠ 0 ∧ principalLevelFrame.IsTypeVec ((PW i).ψ ⁻¹' (levS _ (R.βW i) (R.datWp i (R.levL F false (sg0 D A))))) (fun κ => (levChi _ (R.βW i) (R.datWp i (R.levL F false (sg0 D A)))) ((PW i).ψ κ)) x := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F s hOk hC hgen n hF PY PW hPY hPW π hπ i
  obtain ⟨v, hvS, hv0, hvT, hvG⟩ := GlobalTheory.T.exists_good_fixed_vector_of_type_occurring_in_rows R F hOk hC PY π hπ
  obtain ⟨x, hxS, hx0, hxT⟩ := GlobalTheory.T.exists_baseLevel_vector_of_principalLevel_fixed R F hOk hC hgen PY (principalLevelFrame.FinTyp.conjT π) v hvS hv0 hvT hvG
  set y : Formalism.AUTREP.GAf D.host.E n → ℂ := fun g => star (x g) with hy
  have hyS : y ∈ π.S := hxS
  have hy0 : y ≠ 0 := by
    intro h
    apply hx0
    funext g
    have := congrFun h g
    simpa [hy] using this
  have hyT : principalLevelFrame.IsTypeVec (PY.ψ ⁻¹' levS _ (R.βY 0) (R.dat0 (R.levL F false (sg0 D A))))
      (fun κ => levChi _ (R.βY 0) (R.dat0 (R.levL F false (sg0 D A))) (PY.ψ κ)) y := by
    intro κ hκ
    have e := hxT κ hκ
    funext g
    have eg := congrFun e g
    simp only [principalLevelFrame.rt_apply, Pi.smul_apply, smul_eq_mul] at eg
    simp only [hy, principalLevelFrame.rt_apply, Pi.smul_apply, smul_eq_mul, eg, star_mul', GlobalTheory.T.star_rows_level_character_eq_lifts_level_character R F false]
  obtain ⟨h, hh⟩ := GlobalTheory.T.levels_standardFrames_conjugate_standardGroup R F hC i hF PY (PW i) hPY (hPW i) (R.levL F false (sg0 D A))
  refine ⟨Formalism.L2.NG.rt D.host.E n h y, π.stable h y hyS, ?_, ?_⟩
  · intro h0
    apply hy0
    have := congrArg (Formalism.L2.NG.rt D.host.E n h⁻¹) h0
    rwa [principalLevelFrame.rt_rt, inv_mul_cancel, principalLevelFrame.rt_one, map_zero] at this
  · intro κ hκ
    obtain ⟨h1, h2⟩ := hh κ hκ
    have e : κ * h = h * (h⁻¹ * κ * h) := by group
    show Formalism.L2.NG.rt D.host.E n κ (Formalism.L2.NG.rt D.host.E n h y) = _
    rw [principalLevelFrame.rt_rt, e, ← principalLevelFrame.rt_rt, hyT _ h1, map_smul]
    exact congrArg (· • Formalism.L2.NG.rt D.host.E n h y) h2.symm

end GlobalTheory.RowTypeVec

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowTypeExistsBaseLevelVectorStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

theorem _root_.GlobalTheory.T.rowType_exists_baseLevel_vector : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) {s : ℕ}, A.fam.Ok s → Core R F → (∀ χ ∈ A.X, chiIdem χ * lvlIdem F.P0 F.ψ0 ≠ 0) → ∀ {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (PY : principalLevelFrame.RowPsi (Yc D 0) n) (PW : ∀ i, principalLevelFrame.RowPsi (Wc D i) n), StdPsi hF PY → (∀ i, StdPsi hF (PW i)) → ∀ π, π ∈ principalLevelFrame.OccRows R.θ PY (R.MY 0) (fun b => (levS _ (R.βY 0) (R.dat0 (R.levR F b)))) (fun b => (levChi _ (R.βY 0) (R.dat0 (R.levR F b)))) (fun _ => R.e0) → ∀ i, ∃ x ∈ π.S, x ≠ 0 ∧ principalLevelFrame.IsTypeVec ((PW i).ψ ⁻¹' (levS _ (R.βW i) (R.datWp i (R.levL F false (sg0 D A))))) (fun κ => (levChi _ (R.βW i) (R.datWp i (R.levL F false (sg0 D A)))) ((PW i).ψ κ)) x := by
  first | exact @GlobalTheory.RowTypeVec.vec_of_rows | exact GlobalTheory.RowTypeVec.vec_of_rows | (intros; apply GlobalTheory.RowTypeVec.vec_of_rows <;> assumption)
end
end
