module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OfRoots
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniquePlace
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegerPointsCoverRealPointsRootCoordinatesStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RatCoordCont
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreimageReindexScaleComplexLe
public import Formalism.LocalRingCardinality.DataHost
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTieOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ParametersTermRelations
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TermTieOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RatCoordConjEqStCoord
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopBPin
import Mathlib.CategoryTheory.Countable
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.FormAll
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopBPin
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreimageReindexScaleComplexLeStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.measure_preimage_reindex_scale_complex_le : ∀ (ι ι' κ κ' : Type) [Fintype ι] [Fintype ι'] [Fintype κ] [Fintype κ'] (e : ι ≃ ι') (f : κ ≃ κ') (ρ c : ℝ) (d : κ → ℕ), 1 ≤ ρ → c ≤ 1 → ∀ A : Set (ι → κ → ℂ), MeasurableSet A → (MeasureTheory.Measure.pi fun _ : ι' => MeasureTheory.Measure.pi fun _ : κ' => ENNReal.ofReal c • (MeasureTheory.volume : MeasureTheory.Measure ℂ)) ((fun (x : ι' → κ' → ℂ) (i : ι) (q : κ) => ((ρ : ℂ) ^ d q)⁻¹ * x (e i) (f q)) ⁻¹' A) ≤ MeasureTheory.volume A * ENNReal.ofReal (ρ ^ (2 * Fintype.card ι * ∑ q, d q)) := by
  first | exact @GlobalTheory.CoordScale.measure_preimage_reindex_scale_le | exact GlobalTheory.CoordScale.measure_preimage_reindex_scale_le | (intros; apply GlobalTheory.CoordScale.measure_preimage_reindex_scale_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemRootsPointMatrixIffSameBlock

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RootsBijection

open Formalism.L2.SG.RealObj in
theorem fwd {K : Type*} [Zero K] : ∀ (bs : List (K × ℕ)) (i j a b : ℕ), Formalism.MainNotions.S.ptEntry bs i a ≠ 0 →
    Formalism.MainNotions.S.ptEntry bs j b ≠ 0 → a < b → j < i → blkOf bs a = blkOf bs b
  | [], _, _, _, _, h, _, _, _ => by simp [Formalism.MainNotions.S.ptEntry] at h
  | (t, s) :: bs, i, j, a, b, h1, h2, hab, hji => by
    rw [Formalism.MainNotions.S.ptEntry] at h1 h2
    by_cases ha : a < s
    · by_cases hb : b < s
      · simp [blkOf, ha, hb]
      · exfalso
        rw [if_neg (show ¬ (j < s ∧ b < s) by omega)] at h2
        by_cases hj : s ≤ j
        · rw [if_neg (show ¬ (s ≤ i ∧ s ≤ a) by omega)] at h1
          by_cases hi : i < s
          · omega
          · rw [if_neg (show ¬ (i < s ∧ a < s) by omega)] at h1; exact h1 rfl
        · rw [if_neg (show ¬ (s ≤ j ∧ s ≤ b) by omega)] at h2; exact h2 rfl
    · have hb : ¬ b < s := by omega
      rw [if_neg (show ¬ (i < s ∧ a < s) by omega)] at h1
      rw [if_neg (show ¬ (j < s ∧ b < s) by omega)] at h2
      by_cases hi : s ≤ i
      · by_cases hj : s ≤ j
        · rw [if_pos ⟨hi, by omega⟩] at h1
          rw [if_pos ⟨hj, by omega⟩] at h2
          have := fwd bs (i - s) (j - s) (a - s) (b - s) h1 h2 (by omega) (by omega)
          simp [blkOf, ha, hb, this]
        · rw [if_neg (show ¬ (s ≤ j ∧ s ≤ b) by omega)] at h2; exact absurd rfl h2
      · rw [if_neg (show ¬ (s ≤ i ∧ s ≤ a) by omega)] at h1; exact absurd rfl h1

open Formalism.L2.SG.RealObj in
theorem bwd {K : Type*} [Zero K] : ∀ (bs : List (K × ℕ)), (∀ p ∈ bs, p.1 ≠ 0) → ∀ (a b : ℕ), a < b →
    b < (bs.map Prod.snd).sum → blkOf bs a = blkOf bs b →
    ∃ i j, j < i ∧ i < (bs.map Prod.snd).sum ∧ Formalism.MainNotions.S.ptEntry bs i a ≠ 0 ∧ Formalism.MainNotions.S.ptEntry bs j b ≠ 0
  | [], _, _, _, _, hb, _ => by simp at hb
  | (t, s) :: bs, hnz, a, b, hab, hbs, hbl => by
    have ht : t ≠ 0 := hnz (t, s) (by simp)
    simp only [List.map_cons, List.sum_cons] at hbs ⊢
    by_cases ha : a < s
    · have hb : b < s := by
        by_contra hb
        simp [blkOf, ha, hb] at hbl
      refine ⟨s - 1 - a, s - 1 - b, by omega, by omega, ?_, ?_⟩
      · rw [Formalism.MainNotions.S.ptEntry, if_pos ⟨by omega, ha⟩, if_pos (by omega)]; exact ht
      · rw [Formalism.MainNotions.S.ptEntry, if_pos ⟨by omega, hb⟩, if_pos (by omega)]; exact ht
    · have hb : ¬ b < s := by omega
      have hbl' : blkOf bs (a - s) = blkOf bs (b - s) := by
        simpa [blkOf, ha, hb] using hbl
      have htail :
          ∃ i j, j < i ∧ i < (bs.map Prod.snd).sum ∧
            Formalism.MainNotions.S.ptEntry bs i (a - s) ≠ 0 ∧
            Formalism.MainNotions.S.ptEntry bs j (b - s) ≠ 0 :=
        bwd bs (fun p hp => hnz p (List.mem_cons_of_mem _ hp)) (a - s) (b - s)
          (by omega) (by omega) hbl'
      rcases htail with ⟨i, j, hji, his, hi, hj⟩
      refine ⟨i + s, j + s, Nat.add_lt_add_right hji s, by omega, ?_, ?_⟩
      · simpa [Formalism.MainNotions.S.ptEntry, ha, Nat.le_of_not_gt ha] using hi
      · simpa [Formalism.MainNotions.S.ptEntry, hb, Nat.le_of_not_gt hb] using hj

end GlobalTheory.RootsBijection

theorem GlobalTheory.roots_ptMat_iff : ∀ (K : Type) [Field K] (n : ℕ) (w : Point K n) (a b : Fin n),
    (a, b) ∈ GlobalTheory.LoopV.roots (ptMat w) ↔ a < b ∧ Formalism.L2.SG.RealObj.blkOf w.1 a.1 = Formalism.L2.SG.RealObj.blkOf w.1 b.1 := by
  intro K _ n w a b
  unfold GlobalTheory.LoopV.roots
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  simp only [ptMat]
  constructor
  · rintro ⟨hab, i, j, hji, hi, hj⟩
    exact ⟨hab, GlobalTheory.RootsBijection.fwd w.1 i.1 j.1 a.1 b.1 hi hj hab hji⟩
  · rintro ⟨hab, hbl⟩
    obtain ⟨i, j, hji, hin, hi, hj⟩ := GlobalTheory.RootsBijection.bwd w.1 (fun p hp => (w.2.1 p hp).1) a.1 b.1 hab
      (by rw [w.2.2]; exact b.2) hbl
    rw [w.2.2] at hin
    exact ⟨hab, ⟨i, hin⟩, ⟨j, by omega⟩, hji, hi, hj⟩
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemRootsPointMatrixIffSameBlockStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.mem_roots_point_matrix_iff_same_block : ∀ (K : Type) [Field K] (n : ℕ) (w : Point K n) (a b : Fin n), (a, b) ∈ GlobalTheory.LoopV.roots (ptMat w) ↔ a < b ∧ Formalism.L2.SG.RealObj.blkOf w.1 a.1 = Formalism.L2.SG.RealObj.blkOf w.1 b.1 := by
  first | exact @GlobalTheory.roots_ptMat_iff | exact GlobalTheory.roots_ptMat_iff | (intros; apply GlobalTheory.roots_ptMat_iff <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabiliserHaarRootCoordinatesLeLebesgue

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory

namespace GlobalTheory.LoopVol

theorem pinned_ratCoord_le : ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (γw sf : X.B.I.Ginf) (μw : MeasureTheory.Measure X.B.I.Ginf), IsHaarOnSet X.B.I (Formalism.L2.SG.RealObj.StInf X u u' γw) μw → μw.map (Formalism.L2.SG.RealObj.stCoord X u' w γw) = Formalism.L2.SG.RealObj.muStab X w → D.host.ka / (X.B.g : ℝ) / Real.pi ≤ 1 → ∀ A : Set (D.what₂.Tau → GlobalTheory.LoopV.roots (ptMat w) → ℂ), MeasurableSet A → (μw.map (fun y => sf * y * sf⁻¹)) (GlobalTheory.LoopVol.ratCoord X u' w γw sf ⁻¹' A) ≤ MeasureTheory.volume A * ENNReal.ofReal (D.host.rdE ^ (2 * D.R.f * (D.R.rS + 1) ^ 3)) := by
  intro D X u u' w γw sf μw _hH hmap hc A hA
  classical

  let ι : GlobalTheory.LoopV.roots (ptMat w) ≃ Formalism.L2.SG.RealObj.FreeE w :=
    Equiv.subtypeEquivRight (fun p => GlobalTheory.T.mem_roots_point_matrix_iff_same_block D.host.E (D.R.rS + 1) w p.1 p.2)
  let d : GlobalTheory.LoopV.roots (ptMat w) → ℕ := fun q => q.1.2.1 - q.1.1.1
  let S : (NumberField.InfinitePlace X.B.I.F → Formalism.L2.SG.RealObj.FreeE w → ℂ) → (D.what₂.Tau → GlobalTheory.LoopV.roots (ptMat w) → ℂ) :=
    fun x τ q => (((D.host.rdE : ℝ) : ℂ) ^ d q)⁻¹ * x (X.pl.symm τ) (ι q)
  have hS : Continuous S := by
    refine continuous_pi fun τ => continuous_pi fun q => continuous_const.mul ?_
    exact (continuous_apply _).comp (continuous_apply _)
  have hΦ : Continuous (fun y : X.B.I.Ginf => sf * y * sf⁻¹) :=
    (continuous_const.mul continuous_id).mul continuous_const
  have hst := Formalism.L2.SG.Pf.LoopBPin.stCoord_cont (X := X) u' w γw
  have hrat := ratCoord_cont X u' w γw sf
  have hpre : (fun y : X.B.I.Ginf => sf * y * sf⁻¹) ⁻¹' (ratCoord X u' w γw sf ⁻¹' A) =
      Formalism.L2.SG.RealObj.stCoord X u' w γw ⁻¹' (S ⁻¹' A) := by
    ext y
    simp only [Set.mem_preimage]
    have : ratCoord X u' w γw sf (sf * y * sf⁻¹) = S (Formalism.L2.SG.RealObj.stCoord X u' w γw y) := by
      funext τ q
      exact ratCoord_conj_eq_stCoord D X u' w γw sf y τ q (ι q) rfl
    rw [this]
  have hB : MeasurableSet (S ⁻¹' A) := hS.measurable hA
  rw [Measure.map_apply hΦ.measurable (hrat.measurable hA), hpre,
    ← Measure.map_apply hst.measurable hB, hmap]
  have hrd : 1 ≤ D.host.rdE := GlobalTheory.RealPlaces.one_le_rdE (D := D)
  have key := GlobalTheory.T.measure_preimage_reindex_scale_complex_le D.what₂.Tau (NumberField.InfinitePlace X.B.I.F) (GlobalTheory.LoopV.roots (ptMat w)) (Formalism.L2.SG.RealObj.FreeE w)
    X.pl.symm ι D.host.rdE (D.host.ka / (X.B.g : ℝ) / Real.pi) d hrd hc A hA
  refine le_trans key ?_
  gcongr
  · rw [D.what₂.card_Tau]
  · have hsum : ∑ q : GlobalTheory.LoopV.roots (ptMat w), d q ≤ (D.R.rS + 1) ^ 3 := by
      calc ∑ q : GlobalTheory.LoopV.roots (ptMat w), d q ≤ ∑ _q : GlobalTheory.LoopV.roots (ptMat w), (D.R.rS + 1) :=
            Finset.sum_le_sum fun q _ => by
              have := q.1.2.2; simp only [d]; omega
        _ = Fintype.card (GlobalTheory.LoopV.roots (ptMat w)) * (D.R.rS + 1) := by simp
        _ ≤ (D.R.rS + 1) ^ 2 * (D.R.rS + 1) := by
            gcongr
            calc Fintype.card (GlobalTheory.LoopV.roots (ptMat w)) ≤ Fintype.card (Fin (D.R.rS + 1) × Fin (D.R.rS + 1)) :=
                  Fintype.card_subtype_le _
              _ = (D.R.rS + 1) ^ 2 := by simp [sq]
        _ = (D.R.rS + 1) ^ 3 := by ring
    exact hsum

end GlobalTheory.LoopVol
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabiliserHaarRootCoordinatesLeLebesgueStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.stabiliserHaar_rootCoordinates_le_lebesgue : ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (γw sf : X.B.I.Ginf) (μw : MeasureTheory.Measure X.B.I.Ginf), IsHaarOnSet X.B.I (Formalism.L2.SG.RealObj.StInf X u u' γw) μw → μw.map (Formalism.L2.SG.RealObj.stCoord X u' w γw) = Formalism.L2.SG.RealObj.muStab X w → D.host.ka / (X.B.g : ℝ) / Real.pi ≤ 1 → ∀ A : Set (D.what₂.Tau → GlobalTheory.LoopV.roots (ptMat w) → ℂ), MeasurableSet A → (μw.map (fun y => sf * y * sf⁻¹)) (GlobalTheory.LoopVol.ratCoord X u' w γw sf ⁻¹' A) ≤ MeasureTheory.volume A * ENNReal.ofReal (D.host.rdE ^ (2 * D.R.f * (D.R.rS + 1) ^ 3)) := by
  first | exact @GlobalTheory.LoopVol.pinned_ratCoord_le | exact GlobalTheory.LoopVol.pinned_ratCoord_le | (intros; apply GlobalTheory.LoopVol.pinned_ratCoord_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabiliserCovolumeLeRootCoordinateCover

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open MeasureTheory in
theorem GlobalTheory.LoopVol.packing_pinned {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word} (s : TT Y u u')
    {γw g g' : X.B.I.Ginf} {μw : Measure X.B.I.Ginf} (hg : g ∈ X.SinfU u) (hg' : g' ∈ X.SinfU u')
    (hdec : s.pt.1 = g * γw * g'⁻¹) (hH : IsHaarOnSet X.B.I (Formalism.L2.SG.RealObj.StInf X u u' γw) μw)
    {K B : Set X.B.I.Ginf} (hK : Formalism.L2.SG.LoopTerm.IsFundR s K) (hB : MeasurableSet B)
    (hcov : ∀ r ∈ Formalism.L2.SG.TermOp.Vanish.Rset s, ∃ q ∈ Formalism.L2.SG.TermOp.ROinf s, q * r ∈ B) :
    (μw.map fun y => g * y * g⁻¹) K ≤ (μw.map fun y => g * y * g⁻¹) B := by
  obtain ⟨-, -, hconc, hinvw⟩ := hH
  obtain ⟨hKm, hKu⟩ := hK
  haveI := Formalism.L2.SG.TermOp.Vanish.ROsub_countable X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin
  set Γ := Formalism.L2.SG.TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin with hΓ
  set μR := μw.map fun y => g * y * g⁻¹ with hμR
  have hcm : Measurable fun y : X.B.I.Ginf => g * y * g⁻¹ :=
    ((continuous_const.mul continuous_id).mul continuous_const).measurable
  have hRm : MeasurableSet (Formalism.L2.SG.TermOp.Vanish.Rset s) :=
    (Formalism.L2.SG.Pf.rClosedC_holds D X Y u u' s).measurableSet
  have hRc : μR (Formalism.L2.SG.TermOp.Vanish.Rset s)ᶜ = 0 := by
    rw [hμR, Measure.map_apply hcm hRm.compl]
    apply measure_mono_null _ hconc
    intro y hy
    exact fun hySt => hy (Formalism.L2.SG.LoopTerm.stInf_conj hg hg' hdec hySt)
  have hinv : ∀ q ∈ Γ, μR.map (fun x => q * x) = μR := by
    intro q hq
    have hq' := Formalism.L2.SG.LoopTerm.stInf_conj_inv hg hg' hdec (Formalism.L2.SG.Pf.LoopBPin.roinf_sub_rset s hq)
    rw [hμR, Measure.map_map (measurable_const_mul q) hcm]
    have e : (fun x => q * x) ∘ (fun y => g * y * g⁻¹) =
        (fun y => g * y * g⁻¹) ∘ (fun y => (g⁻¹ * q * g) * y) := by
      funext y; simp only [Function.comp]; group
    rw [e, ← Measure.map_map hcm (measurable_const_mul _), hinvw _ hq']
  have hpre : ∀ q ∈ Γ, ∀ C, MeasurableSet C → μR ((fun x => q * x) ⁻¹' C) = μR C := by
    intro q hq C hC
    rw [← Measure.map_apply (measurable_const_mul q) hC, hinv q hq]
  have h1 : μR K ≤ ∑' q : Γ, μR (K ∩ (fun x => (q : X.B.I.Ginf) * x) ⁻¹' B) := by
    calc μR K = μR (K ∩ Formalism.L2.SG.TermOp.Vanish.Rset s) := (measure_inter_conull hRc).symm
      _ ≤ μR (⋃ q : Γ, K ∩ (fun x => (q : X.B.I.Ginf) * x) ⁻¹' B) := by
          refine measure_mono fun r hr => ?_
          obtain ⟨q, hq, hqr⟩ := hcov r hr.2
          exact Set.mem_iUnion.2 ⟨⟨q, hq⟩, hr.1, hqr⟩
      _ ≤ _ := measure_iUnion_le _
  have h2 : ∀ q : Γ, μR (K ∩ (fun x => (q : X.B.I.Ginf) * x) ⁻¹' B) =
      μR (B ∩ (fun x => ((q⁻¹ : Γ) : X.B.I.Ginf) * x) ⁻¹' K) := by
    intro q
    have hC : MeasurableSet (B ∩ (fun x => ((q⁻¹ : Γ) : X.B.I.Ginf) * x) ⁻¹' K) :=
      hB.inter (hKm.preimage (measurable_const_mul _))
    rw [← hpre q q.2 _ hC]
    congr 1
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Subgroup.coe_inv, inv_mul_cancel_left]
    exact and_comm
  have h3 := Formalism.L2.SG.Pf.FormAllPf.decomp μR (Formalism.L2.SG.TermOp.Vanish.Rset s) hRc Γ B K hB hKm hKu
  have h4 : ∑' q : Γ, μR (K ∩ (fun x => (q : X.B.I.Ginf) * x) ⁻¹' B) = μR B := by
    rw [h3]
    simp_rw [h2]
    exact (Equiv.inv Γ).tsum_eq (fun q => μR (B ∩ (fun x => (q : X.B.I.Ginf) * x) ⁻¹' K))
  exact h1.trans_eq h4

theorem GlobalTheory.LoopVol.ka_div_le_one {D : D7} (X : HidaSetting D) {u u' : D.what₂.Word} (hSt : Formalism.MainNotions.S.Cnt.Stand D u u') :
    D.host.ka / (X.B.g : ℝ) / Real.pi ≤ 1 := by
  have hrd := GlobalTheory.RealPlaces.one_le_rdE D
  have hg0 := hSt.2.2.2.2.2.2.2.1.two_le
  have hg1 := hSt.2.2.2.2.2.2.2.2.1.two_le
  have h0 : (2 : ℝ) ≤ (D.host.g 0 : ℝ) := by exact_mod_cast hg0
  have h1 : (2 : ℝ) ≤ (D.host.g 1 : ℝ) := by exact_mod_cast hg1
  have hgR : (4 : ℝ) ≤ (X.B.g : ℝ) := by rw [X.g_eq]; push_cast; nlinarith
  have e : D.host.ka / (X.B.g : ℝ) / Real.pi = 2 / (D.host.rdE * X.B.g) := by
    rw [show D.host.ka = Real.pi / (D.host.rdE / 2) from rfl]
    have : (0 : ℝ) < D.host.rdE := by linarith
    have : (0 : ℝ) < (X.B.g : ℝ) := by linarith
    field_simp
  rw [e, div_le_one (by positivity)]
  nlinarith

theorem GlobalTheory.LoopVol.covolume_le_cover : ∀ Cg cb Cu cT CT C0 A : ℝ, ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (W : WittDat X) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl : ℝ), Formalism.MainNotions.S.Cnt.Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A → ∀ s : TT Y u u', s.relevant → s.G ≠ 0 → ∀ (w : Point D.host.E (D.R.rS + 1)) (μR : MeasureTheory.Measure X.B.I.Ginf) (K : Set X.B.I.Ginf), s.toTerm.atPt w → Formalism.L2.SG.VolPin.IsPinnedR s w μR → Formalism.L2.SG.LoopTerm.IsFundR s K → ∀ (L U : Formalism.MainNotions.S.Cnt.GramM D), IsLoUni L → IsUpUni U → ZhatOM (ZhatL (lf D (FlagOfWord W u)) (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame)) = L * ptMat w * U → ∀ Ω : Set (D.what₂.Tau → GlobalTheory.LoopV.roots (ptMat w) → ℂ), MeasurableSet Ω → (∀ c : D.what₂.Tau → GlobalTheory.LoopV.roots (ptMat w) → ℂ, ∃ n ∈ NLam (Formalism.HermitianLatticesTheory.gmap (W.δ u) s.lam) (lf D (FlagOfWord W u)) ∩ NLam (Formalism.HermitianLatticesTheory.gmap (W.δ u) s.lam) (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame), ∃ a : Formalism.MainNotions.S.Cnt.GramM D, (∀ j : Fin (D.R.rS + 1), n (frame (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame) j) = ∑ i : Fin (D.R.rS + 1), ((-1) ^ (i.val + j.val) * a i j) • frame (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame) i) ∧ (fun τ (q : GlobalTheory.LoopV.roots (ptMat w)) => ((U * a * U⁻¹).map (embS D τ) * GlobalTheory.LoopV.ofRoots (GlobalTheory.LoopV.roots (ptMat w)) (c τ) : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ) q.1.1 q.1.2) ∈ Ω) → μR K ≤ MeasureTheory.volume Ω * ENNReal.ofReal (D.host.rdE ^ (2 * D.R.f * (D.R.rS + 1) ^ 3)) := by
  intro Cg cb Cu cT CT C0 A D X Y W large₂ u u' C' Cl hH s hrel hG w μR K hat hPin hK L U hL hU hZ Ω hΩ hcov
  obtain ⟨γw, sf, s', μw, hrep, hsf, hs', hdec, hμwH, hμwS, rfl⟩ := hPin
  obtain ⟨T, hT, hTc⟩ := GlobalTheory.T.integerPoints_cover_realPoints_rootCoordinates Cg cb Cu cT CT C0 A D X Y W large₂ u u' C' Cl hH s hrel hG w γw sf s' hat hrep hsf hs' hdec
    L U hL hU hZ Ω hcov
  have hTΩ : MeasurableSet (T ⁻¹' Ω) := hT.measurable hΩ
  have hBm : MeasurableSet (GlobalTheory.LoopVol.ratCoord X u' w γw sf ⁻¹' (T ⁻¹' Ω)) :=
    (GlobalTheory.LoopVol.ratCoord_cont X u' w γw sf).measurable hTΩ
  have hka := GlobalTheory.LoopVol.ka_div_le_one X hH.2.1
  calc (μw.map fun y => sf * y * sf⁻¹) K
      ≤ (μw.map fun y => sf * y * sf⁻¹) (GlobalTheory.LoopVol.ratCoord X u' w γw sf ⁻¹' (T ⁻¹' Ω)) :=
        GlobalTheory.LoopVol.packing_pinned s hsf hs' hdec hμwH hK hBm hTc
    _ ≤ MeasureTheory.volume (T ⁻¹' Ω) * ENNReal.ofReal (D.host.rdE ^ (2 * D.R.f * (D.R.rS + 1) ^ 3)) :=
        GlobalTheory.T.stabiliserHaar_rootCoordinates_le_lebesgue D X u u' w γw sf μw hμwH hμwS hka _ hTΩ
    _ = MeasureTheory.volume Ω * ENNReal.ofReal (D.host.rdE ^ (2 * D.R.f * (D.R.rS + 1) ^ 3)) := by
        rw [hT.measure_preimage hΩ.nullMeasurableSet]

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabiliserCovolumeLeRootCoordinateCoverStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.stabiliserCovolume_le_rootCoordinateCover : ∀ Cg cb Cu cT CT C0 A : ℝ, ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (W : WittDat X) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl : ℝ), Formalism.MainNotions.S.Cnt.Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A → ∀ s : TT Y u u', s.relevant → s.G ≠ 0 → ∀ (w : Point D.host.E (D.R.rS + 1)) (μR : MeasureTheory.Measure X.B.I.Ginf) (K : Set X.B.I.Ginf), s.toTerm.atPt w → Formalism.L2.SG.VolPin.IsPinnedR s w μR → Formalism.L2.SG.LoopTerm.IsFundR s K → ∀ (L U : Formalism.MainNotions.S.Cnt.GramM D), IsLoUni L → IsUpUni U → ZhatOM (ZhatL (lf D (FlagOfWord W u)) (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame)) = L * ptMat w * U → ∀ Ω : Set (D.what₂.Tau → GlobalTheory.LoopV.roots (ptMat w) → ℂ), MeasurableSet Ω → (∀ c : D.what₂.Tau → GlobalTheory.LoopV.roots (ptMat w) → ℂ, ∃ n ∈ NLam (Formalism.HermitianLatticesTheory.gmap (W.δ u) s.lam) (lf D (FlagOfWord W u)) ∩ NLam (Formalism.HermitianLatticesTheory.gmap (W.δ u) s.lam) (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame), ∃ a : Formalism.MainNotions.S.Cnt.GramM D, (∀ j : Fin (D.R.rS + 1), n (frame (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame) j) = ∑ i : Fin (D.R.rS + 1), ((-1) ^ (i.val + j.val) * a i j) • frame (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame) i) ∧ (fun τ (q : GlobalTheory.LoopV.roots (ptMat w)) => ((U * a * U⁻¹).map (embS D τ) * GlobalTheory.LoopV.ofRoots (GlobalTheory.LoopV.roots (ptMat w)) (c τ) : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ) q.1.1 q.1.2) ∈ Ω) → μR K ≤ MeasureTheory.volume Ω * ENNReal.ofReal (D.host.rdE ^ (2 * D.R.f * (D.R.rS + 1) ^ 3)) := by
  first | exact @GlobalTheory.LoopVol.covolume_le_cover | exact GlobalTheory.LoopVol.covolume_le_cover | (intros; apply GlobalTheory.LoopVol.covolume_le_cover <;> assumption)
end
end
