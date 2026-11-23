module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsChainPols
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PathConvergenceDownChain
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedThetaFirstOccurrenceFiniteSwappedPair
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedThetaTowerFirstOccurrenceExists

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.GivenPathRepresentationFinite

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FlipStart

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem restrictPol_comp (P : PolE G) {X Y : Node} (p : Path T X Y) : ∀ {Z : Node} (q : Path T Y Z),
    restrictPol P (p.comp q) = Path.Fam.append (restrictPol P p) (restrictPol P q)
  | _, .nil => rfl
  | _, .snoc a q => by
    show (restrictPol P (p.comp q), polOf P a) = (Path.Fam.append (restrictPol P p) (restrictPol P q), polOf P a)
    rw [restrictPol_comp P p q]

theorem zip_append {S S' S'' : Arrow T → Type} (φ : ∀ a, S a → S' a → S'' a) {X Y : Node} {p : Path T X Y} (d : p.Fam S)
    (d' : p.Fam S') : ∀ {Z : Node} (q : Path T Y Z) (e : q.Fam S) (e' : q.Fam S'),
    Path.Fam.zip φ (d.append e) (d'.append e') = (Path.Fam.zip φ d d').append (Path.Fam.zip φ e e')
  | _, .nil, _, _ => rfl
  | _, .snoc a q, e, e' => by
    show (Path.Fam.zip φ (d.append e.1) (d'.append e'.1), φ a e.2 e'.2) =
      ((Path.Fam.zip φ d d').append (Path.Fam.zip φ e.1 e'.1), φ a e.2 e'.2)
    rw [zip_append φ d d' q e.1 e'.1]

theorem zip_rowFam {S S' S'' : Arrow T → Type} (φ : ∀ a, S a → S' a → S'' a) (j : ℕ) : ∀ n (f : ∀ i : Fin n, S (.right i j))
    (g : ∀ i : Fin n, S' (.right i j)), Path.Fam.zip φ (rowFam j n f) (rowFam j n g) = rowFam j n fun i => φ _ (f i) (g i)
  | 0, _, _ => rfl
  | n + 1, f, g => by
    show (Path.Fam.zip φ (rowFam j n fun i => f i.castSucc) (rowFam j n fun i => g i.castSucc), φ _ (f (Fin.last n)) (g (Fin.last n))) =
      (rowFam j n fun i => φ _ (f i.castSucc) (g i.castSucc), φ _ (f (Fin.last n)) (g (Fin.last n)))
    rw [zip_rowFam φ j n]

theorem zip_downFam {S S' S'' : Arrow T → Type} (φ : ∀ a, S a → S' a → S'' a) (t : T) (i : ℕ) : ∀ n (f : ∀ j : Fin n, S (.down t i j))
    (g : ∀ j : Fin n, S' (.down t i j)), Path.Fam.zip φ (downFam t i n f) (downFam t i n g) = downFam t i n fun j => φ _ (f j) (g j)
  | 0, _, _ => rfl
  | n + 1, f, g => by
    show Path.Fam.zip φ (Path.Fam.append (p := Path.one (.down t i n)) ((), f (Fin.last n)) (downFam t i n fun j => f j.castSucc))
        (Path.Fam.append (p := Path.one (.down t i n)) ((), g (Fin.last n)) (downFam t i n fun j => g j.castSucc)) =
      Path.Fam.append (p := Path.one (.down t i n)) ((), φ _ (f (Fin.last n)) (g (Fin.last n)))
        (downFam t i n fun j => φ _ (f j.castSucc) (g j.castSucc))
    refine (zip_append φ (p := Path.one (.down t i n)) (((), f (Fin.last n)) : (Path.one (.down t i n)).Fam S)
      (((), g (Fin.last n)) : (Path.one (.down t i n)).Fam S') (downPath t i n) (downFam t i n fun j => f j.castSucc)
      (downFam t i n fun j => g j.castSucc)).trans ?_
    rw [zip_downFam φ t i n]
    rfl

theorem restrictPol_rowPath (P : PolE G) (j : ℕ) : ∀ n, restrictPol P (rowPath T j n) = rowFam j n fun i => polOf P (.right i j)
  | 0 => rfl
  | n + 1 => by
    show (restrictPol P (rowPath T j n), polOf P (.right n j)) = (rowFam j n fun i => polOf P (.right (i.castSucc : Fin (n + 1)) j), _)
    rw [restrictPol_rowPath P j n]
    rfl

theorem restrictPol_downPath (P : PolE G) (t : T) (i : ℕ) : ∀ n,
    restrictPol P (downPath t i n) = downFam t i n fun j => polOf P (.down t i j)
  | 0 => rfl
  | n + 1 => by
    show restrictPol P ((Path.one (.down t i n)).comp (downPath t i n)) = _
    rw [restrictPol_comp, restrictPol_downPath P t i n]
    rfl

theorem tensE_single (W : G.Weil) {X Y : Node} (p : Path T X Y) (P : PolE G) (d : PureT G p) (c : ℂ) :
    tensE W p (Finsupp.single P 1) (Finsupp.single d c) =
      Finsupp.single (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d (restrictPol P p)) c := by
  unfold tensE tensT
  rw [Finsupp.mapDomain_single, Finsupp.sum_single_index, Finsupp.sum_single_index, one_mul]
  · simp
  · simp

theorem zip_given (W : G.Weil) (t : T) (ρ : G.RealVec) (q : ∀ j : ℕ, PolF D (G.V (.grid 0 (j + 1))).rank (G.V (.grid 0 j)).rank)
    (f : ∀ j : Fin D.R.m, Sch G (.down t 0 j)) (Φ : G.Datum) :
    Path.Fam.zip (fun a (g : Sch G a) Q => W.fock a.pair g Q) (givenFin W t f Φ) (restrictPol (gPol ρ q) (givenPath t D.R.m)) =
      Path.Fam.append (colPure W t f fun j => q j) (rowDatum W ρ Φ) := by
  unfold givenFin givenPath
  rw [restrictPol_comp, zip_append, restrictPol_downPath, restrictPol_rowPath, zip_downFam, zip_rowFam]
  congr 1
  unfold rowDatum
  congr 1
  funext i
  show W.fock (.chi i 0) (W.cosVec i (Φ i)) (if h : (i : ℕ) < D.R.m then ρ ⟨i, h⟩ else 0) = W.datum ρ Φ i
  rw [dite_eq_left i.2]
  rfl

end GlobalTheory.FlipStart


end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.FlipSequenceStartColumn

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.FlipStart.Col
variable {D : D7}
variable {T : Type} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
end GlobalTheory.FlipStart.Col
open GlobalTheory.FlipStart GlobalTheory.FlipStart.Col in
theorem GlobalTheory.FlipStart.flipSequence_start_column : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t : T) (f : ∀ j : Fin D.R.m, Sch ch.G (.down t 0 j)) (q : ∀ j : ℕ, PolF D (ch.G.V (.grid 0 (j + 1))).rank (ch.G.V (.grid 0 j)).rank), GlobalTheory.FlipStart.ChainVecs ch t f → GlobalTheory.FlipStart.ChainPols ch q → ∀ M : Vol ch.G, M.Is t → ∀ y : (R.HX t).H, PathConv ch.W M (downPath t 0 D.R.m) (GlobalTheory.FlipStart.colPure ch.W t f fun j => q j) (formTop ch t y) ∧ liftP ch.W M (downPath t 0 D.R.m) (GlobalTheory.FlipStart.colPure ch.W t f fun j => q j) (formTop ch t y) = ch.cv.lift t y := by
  intro _ _
  refine ⟨0, fun _ _ _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  intro t f q hf hq M hM y
  have h := col_top hch.weil s.core.chain s.core.models hq hM y D.R.m rfl (fun j => ch.W.fock (.mu t 0 j) (f j) (q j))
    (fun j => ⟨fun h => ⟨f j, (hf j).1 h, rfl⟩, fun h => ⟨f j, (hf j).2 h, rfl⟩⟩) (formTop ch t y)
    (by unfold formTop; exact cast_fun_heq _ _)
  exact ⟨h.1, eq_of_heq h.2⟩
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.flipSequence_column_succ : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t : T) (f : ∀ j : Fin D.R.m, Sch ch.G (.down t 0 j)) (q : ∀ j : ℕ, PolF D (ch.G.V (.grid 0 (j + 1))).rank (ch.G.V (.grid 0 j)).rank), GlobalTheory.FlipStart.ChainVecs ch t f → GlobalTheory.FlipStart.ChainPols ch q → ∀ M : Vol ch.G, M.Is t → ∀ y : (R.HX t).H, PathConv ch.W M (downPath t 0 D.R.m) (GlobalTheory.FlipStart.colPure ch.W t f fun j => q j) (formTop ch t y) ∧ liftP ch.W M (downPath t 0 D.R.m) (GlobalTheory.FlipStart.colPure ch.W t f fun j => q j) (formTop ch t y) = ch.cv.lift t y := by
  first | exact @_root_.GlobalTheory.FlipStart.flipSequence_start_column | exact _root_.GlobalTheory.FlipStart.flipSequence_start_column | (intros; apply _root_.GlobalTheory.FlipStart.flipSequence_start_column <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.FlipSequenceStartCondition

section

@[expose] public section

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.FlipStart
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}
end GlobalTheory.FlipStart
open GlobalTheory.FlipStart in
theorem GlobalTheory.FlipStart.flipSequence_start_condition : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∃ Pg : GlobalTheory.FlipRun.PolE ch.G →₀ ℂ, ∀ t : T, ∃ z : ℂˣ, z ∈ GlobalTheory.RowClaim.xiVals R.toLevCh t ∧ ∀ Φ : ch.G.Datum, ∃ τg : TotT ch.G (GlobalTheory.FunObj.givenPath t D.R.m), GlobalTheory.FlipRun.RepFin ch.S.B ch.rm t (GlobalTheory.FunObj.givenPath t D.R.m) τg (fun w => (givenStage t w ch.S.B Φ).tensor) ∧ ∀ M : Vol ch.G, M.Is t → ∀ y, TotConv ch.W M _ (GlobalTheory.FlipRun.tensE ch.W _ Pg τg) (GlobalTheory.RowClaim.formTop ch t y) ∧ thetaChi ch.W ch.M ch.ρ Φ (ch.cv.lift t y) = (z : ℂ)⁻¹ • liftT ch.W M _ (GlobalTheory.FlipRun.tensE ch.W _ Pg τg) (GlobalTheory.RowClaim.formTop ch t y) := by
  intro hP hC
  obtain ⟨a, h⟩ := ((_root_.GlobalTheory.T.flipSequence_column_succ hP hC).and (_root_.GlobalTheory.T.twisted_theta_tower_first_occurrence_exists hP hC)).and (_root_.GlobalTheory.T.twisted_theta_first_occurrence_finite_swapped_pair hP)
  refine ⟨a, fun ε CF hCF => ?_⟩
  obtain ⟨x, h⟩ := h ε CF hCF
  refine ⟨x, fun D large₂ e hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch i j => ?_⟩
  obtain ⟨⟨hcol, hrow⟩, hfin⟩ := h D large₂ e hx Γ Pl0 T A Ks R F s ch i j
  obtain ⟨q, hq⟩ := exists_chainPols ch
  refine ⟨Finsupp.single (gPol ch.ρ q) 1, fun t => ?_⟩
  obtain ⟨f, hf⟩ := exists_chainVecs ch t
  obtain ⟨z, hz, hrep⟩ := hfin t f hf
  refine ⟨z, hz, fun Φ => ⟨Finsupp.single (givenFin ch.W t f Φ) (z : ℂ), hrep Φ, fun M hM y => ?_⟩⟩
  obtain ⟨hc1, hc2⟩ := hcol t f q hf hq M hM y
  obtain ⟨hr1, hr2⟩ := hrow t Φ M hM y
  rw [tensE_single]
  refine ⟨fun d hd => ?_, ?_⟩
  · have hd' := Finsupp.support_single_subset hd
    rw [Finset.mem_singleton] at hd'
    subst hd'
    rw [zip_given]
    refine (pathConv_comp ch.W M _ _ _ _ _).2 ⟨hc1, ?_⟩
    rw [hc2]
    exact hr1
  · rw [liftT_single, zip_given]
    unfold givenPath
    rw [pathLift_comp, hc2, ← hr2, smul_smul, inv_mul_cancel₀ (Units.ne_zero z), one_smul]
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.flipSequence_initial_term : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∃ Pg : GlobalTheory.FlipRun.PolE ch.G →₀ ℂ, ∀ t : T, ∃ z : ℂˣ, z ∈ GlobalTheory.RowClaim.xiVals R.toLevCh t ∧ ∀ Φ : ch.G.Datum, ∃ τg : TotT ch.G (GlobalTheory.FunObj.givenPath t D.R.m), GlobalTheory.FlipRun.RepFin ch.S.B ch.rm t (GlobalTheory.FunObj.givenPath t D.R.m) τg (fun w => (givenStage t w ch.S.B Φ).tensor) ∧ ∀ M : Vol ch.G, M.Is t → ∀ y, TotConv ch.W M _ (GlobalTheory.FlipRun.tensE ch.W _ Pg τg) (GlobalTheory.RowClaim.formTop ch t y) ∧ thetaChi ch.W ch.M ch.ρ Φ (ch.cv.lift t y) = (z : ℂ)⁻¹ • liftT ch.W M _ (GlobalTheory.FlipRun.tensE ch.W _ Pg τg) (GlobalTheory.RowClaim.formTop ch t y) := by
  first | exact @_root_.GlobalTheory.FlipStart.flipSequence_start_condition | exact _root_.GlobalTheory.FlipStart.flipSequence_start_condition | (intros; apply _root_.GlobalTheory.FlipStart.flipSequence_start_condition <;> assumption)
end
end
end
