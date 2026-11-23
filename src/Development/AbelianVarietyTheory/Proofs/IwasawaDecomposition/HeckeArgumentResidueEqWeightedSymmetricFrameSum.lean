module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneSubEwMem
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.LevelCuspCharacters
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagDualVectorPairingSymmetricFrameModPlace
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.IndefiniteReal.AutomorphicEvaluation
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OtherInstanceCharacterEqPsiSymmetricArgument
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.KppRedW
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.KppFwdPf
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnipotentDualVectorPairingSymmetricFrameModPlace
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Std.Tactic.BVDecide.Normalize.BitVec

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagDualVectorPairingSymmetricFrameModPlaceStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.flagDualVector_pairing_symmetricFrame_mod_place : ∀ (D : D7) (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (k : Fin 2), ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal → ∀ (a : Fin D.R.rS) (j : Fin D.R.r), hA X.B.I (X.f0 a) (GlobalTheory.Mem.SymFrame.symVec X w j) - (if j = GlobalTheory.Mem.SymChar.Resid.posE D a then 1 else 0) ∈ GlobalTheory.Mem.SymChar.wInt X w := by
  first | exact @GlobalTheory.Mem.SymChar.hA_symVec_sub_ite_mem_wInt | exact GlobalTheory.Mem.SymChar.hA_symVec_sub_ite_mem_wInt | (intros; apply GlobalTheory.Mem.SymChar.hA_symVec_sub_ite_mem_wInt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMemPlaceIdealSpanOfNeOne

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SymChar.EwZero

variable {D : D7}


open Formalism.L2.SG.Pf.KppRedW Formalism.L2.SG.Pf.AllRowsRedKerA Formalism.L2.SG.Pf.RowDictPf in
theorem Wq_le_wInt (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) :
    Wq X.B.I (wB X w) ≤ GlobalTheory.Mem.SymChar.wInt X w := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨a, ha, rfl⟩
  refine Submodule.subset_span ⟨a, ⟨RingOfIntegers.mapRingEquiv X.ιE a, ha, by simp⟩, rfl⟩


open Formalism.L2.SG.Pf.KppRedW Formalism.L2.SG.Pf.AllRowsRedKerA Formalism.L2.SG.Pf.RowDictPf in
theorem Lq_le_wLf (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) :
    Lq X.B.I (wB X w) ≤ wLf X w := by
  show Formalism.MainNotions.S.lamAf (F := X.B.I.F) (wLat0 X.B.I (wB X w)) ≤ Formalism.MainNotions.S.lamAf (F := X.B.I.F) (wLat X w)
  rw [wLat_eq]

theorem ew_mem_wInt (D : D7) (X : HidaSetting D) (kv : Σ k : Fin 2, D.nd.PlG k)
    (hw : ¬ GlobalTheory.Mem.SymFrame.EwAt X (D.naut.plGw kv.1 kv.2)) :
    X.ew ∈ GlobalTheory.Mem.SymChar.wInt X (D.naut.plGw kv.1 kv.2) := by
  obtain ⟨ob, h1, -⟩ := Formalism.L2.SG.Pf.KppFwdPf.ew_res X kv
  cases ob with
  | false =>
    simp only [Bool.false_eq_true, if_false, sub_zero] at h1
    exact Wq_le_wInt X _ h1
  | true =>
    simp only [if_true] at h1
    exfalso
    apply hw
    intro y hy
    have h2 : 1 - X.ew ∈ Formalism.L2.SG.Pf.KppRedW.Wq X.B.I (Formalism.L2.SG.Pf.RowDictPf.wB X (D.naut.plGw kv.1 kv.2)) := by
      have := neg_mem h1
      rwa [neg_sub] at this
    exact Lq_le_wLf X _ (Formalism.L2.SG.Pf.KppRedW.Wq_smul h2 hy)

end GlobalTheory.Mem.SymChar.EwZero
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMemPlaceIdealSpanOfNeOneStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.idempotent_mem_placeIdealSpan_of_ne_one : ∀ (D : D7) (X : HidaSetting D) (kv : Σ k : Fin 2, D.nd.PlG k), ¬ GlobalTheory.Mem.SymFrame.EwAt X (D.naut.plGw kv.1 kv.2) → X.ew ∈ GlobalTheory.Mem.SymChar.wInt X (D.naut.plGw kv.1 kv.2) := by
  first | exact @GlobalTheory.Mem.SymChar.EwZero.ew_mem_wInt | exact GlobalTheory.Mem.SymChar.EwZero.ew_mem_wInt | (intros; apply GlobalTheory.Mem.SymChar.EwZero.ew_mem_wInt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymmetricFrameWeightedEdgeSumReindex

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SymChar.EdgeReindex

theorem sum_edge {Q : Type} [AddCommMonoid Q] {r t : ℕ} (ht : t < r) (P : Fin r → Prop) [DecidablePred P]
    (hP : ∀ j, P j ↔ j.val = t) (f : Fin r → Q) : (∑ j, if P j then f j else 0) = f ⟨t, ht⟩ := by
  rw [Finset.sum_eq_single ⟨t, ht⟩]
  · rw [if_pos ((hP _).2 rfl)]
  · intro b _ hb
    rw [if_neg]
    intro h
    exact hb (Fin.ext ((hP b).1 h))
  · simp

def extF {Q : Type} [AddCommGroup Q] {r : ℕ} (F : Fin r → Fin r → Q) (a b : ℕ) : Q :=
  if h : a < r ∧ b < r then F ⟨a, h.1⟩ ⟨b, h.2⟩ else 0

def termAt {Q : Type} [AddCommGroup Q] (ρ k : ℕ) (s : Bool) {r : ℕ} (F : Fin r → Fin r → Q) (n : ℕ) : Q :=
  if n < ρ then extF F n (if n + 1 < ρ then n + 1 else ρ + k)
  else if n + 1 < ρ + k then (if s then extF F n (n + 1) else 0) else 0

theorem inner_eq {Q : Type} [AddCommGroup Q] (ρ k r : ℕ) (hr : r = k + 2 * ρ + 1) (s : Bool)
    (F : Fin r → Fin r → Q) (i : Fin r) :
    (∑ j : Fin r, if symEdge ρ k i j then GlobalTheory.Mem.SymChar.wtA ρ k s i j • F i j else 0) =
      termAt ρ k s F i.1 := by
  have hi := i.2
  unfold termAt
  by_cases h1 : i.1 < ρ
  · by_cases h2 : i.1 + 1 < ρ
    · rw [sum_edge (t := i.1 + 1) (by omega) _ (fun j => by
        simp only [symEdge]; constructor <;> intro h <;> omega)]
      rw [if_pos h1, if_pos h2, extF, dite_eq_left ⟨i.2, by omega⟩]
      simp only [GlobalTheory.Mem.SymChar.wtA, if_pos h1, one_smul]
    · rw [sum_edge (t := ρ + k) (by omega) _ (fun j => by
        simp only [symEdge]; constructor <;> intro h <;> omega)]
      rw [if_pos h1, if_neg h2, extF, dite_eq_left ⟨i.2, by omega⟩]
      simp only [GlobalTheory.Mem.SymChar.wtA, if_pos h1, one_smul]
  · by_cases h2 : i.1 + 1 < ρ + k
    · rw [sum_edge (t := i.1 + 1) (by omega) _ (fun j => by
        simp only [symEdge]; constructor <;> intro h <;> omega)]
      rw [if_neg h1, if_pos h2]
      simp only [GlobalTheory.Mem.SymChar.wtA, if_neg h1, if_pos h2]
      cases s
      · simp
      · rw [extF, dite_eq_left ⟨i.2, by omega⟩]
        simp
    · rw [if_neg h1, if_neg h2]
      refine Finset.sum_eq_zero fun j _ => ?_
      simp only [GlobalTheory.Mem.SymChar.wtA, if_neg h1, if_neg h2, zero_smul, ite_self]

theorem sum_symEdge_wtA : ∀ (Q : Type) [AddCommGroup Q] (ρ k r : ℕ) (hr : r = k + 2 * ρ + 1) (s : Bool) (F : Fin r → Fin r → Q), (∑ i : Fin r, ∑ j : Fin r, if symEdge ρ k i j then GlobalTheory.Mem.SymChar.wtA ρ k s i j • F i j else 0) = (∑ a : Fin ρ, F ⟨a.1, by have := a.2; omega⟩ ⟨if a.1 + 1 < ρ then a.1 + 1 else ρ + k, by have := a.2; split_ifs <;> omega⟩) + ∑ i : Fin k, if h : i.1 + 1 < k then (if s then F ⟨ρ + i.1, by omega⟩ ⟨ρ + i.1 + 1, by omega⟩ else 0) else 0 := by
  intro Q _ ρ k r hr s F
  rw [Finset.sum_congr rfl (fun i _ => inner_eq ρ k r hr s F i)]
  rw [Fin.sum_univ_eq_sum_range (fun n => termAt ρ k s F n) r]
  have e : Finset.range r = Finset.range (ρ + (k + (ρ + 1))) := congrArg Finset.range (by omega)
  rw [e, Finset.sum_range_add, Finset.sum_range_add]
  have h3 : (∑ x ∈ Finset.range (ρ + 1), termAt ρ k s F (ρ + (k + x))) = 0 := by
    refine Finset.sum_eq_zero fun x _ => ?_
    unfold termAt
    rw [if_neg (by omega), if_neg (by omega)]
  rw [h3, add_zero]
  congr 1
  · rw [← Fin.sum_univ_eq_sum_range (fun n => termAt ρ k s F n) ρ]
    refine Finset.sum_congr rfl fun a _ => ?_
    have ha := a.2
    unfold termAt extF
    rw [if_pos ha, dite_eq_left ⟨by omega, by split_ifs <;> omega⟩]
  · rw [← Fin.sum_univ_eq_sum_range (fun n => termAt ρ k s F (ρ + n)) k]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi := i.2
    by_cases h : i.1 + 1 < k
    · rw [dite_eq_left h]
      unfold termAt
      rw [if_neg (by omega), if_pos (by omega)]
      cases s
      · rfl
      · simp only [if_true]
        unfold extF
        rw [dite_eq_left ⟨by omega, by omega⟩]
    · rw [dite_eq_right h]
      unfold termAt
      rw [if_neg (by omega), if_neg (by omega)]

end GlobalTheory.Mem.SymChar.EdgeReindex
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymmetricFrameWeightedEdgeSumReindexStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.symmetricFrame_weightedEdgeSum_reindex : ∀ (Q : Type) [AddCommGroup Q] (ρ k r : ℕ) (hr : r = k + 2 * ρ + 1) (s : Bool) (F : Fin r → Fin r → Q), (∑ i : Fin r, ∑ j : Fin r, if symEdge ρ k i j then GlobalTheory.Mem.SymChar.wtA ρ k s i j • F i j else 0) = (∑ a : Fin ρ, F ⟨a.1, by have := a.2; omega⟩ ⟨if a.1 + 1 < ρ then a.1 + 1 else ρ + k, by have := a.2; split_ifs <;> omega⟩) + ∑ i : Fin k, if h : i.1 + 1 < k then (if s then F ⟨ρ + i.1, by omega⟩ ⟨ρ + i.1 + 1, by omega⟩ else 0) else 0 := by
  first | exact @GlobalTheory.Mem.SymChar.EdgeReindex.sum_symEdge_wtA | exact GlobalTheory.Mem.SymChar.EdgeReindex.sum_symEdge_wtA | (intros; apply GlobalTheory.Mem.SymChar.EdgeReindex.sum_symEdge_wtA <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnipotentDualVectorPairingSymmetricFrameModPlaceStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.unipotentDualVector_pairing_symmetricFrame_mod_place : ∀ (D : D7) (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (k : Fin 2), ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal → GlobalTheory.Mem.SymFrame.EwAt X w → 1 - X.ew ∈ GlobalTheory.Mem.SymChar.wInt X w → ∀ (i : Fin D.R.k) (j : Fin D.R.r), hA X.B.I (X.bwd i) (GlobalTheory.Mem.SymFrame.symVec X w j) - (if j = GlobalTheory.Mem.SymChar.Resid.posB D i then 1 else 0) ∈ GlobalTheory.Mem.SymChar.wInt X w := by
  first | exact @GlobalTheory.Mem.SymChar.Resid.hA_bwd_symVec | exact GlobalTheory.Mem.SymChar.Resid.hA_bwd_symVec | (intros; apply GlobalTheory.Mem.SymChar.Resid.hA_bwd_symVec <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeArgumentResidueEqWeightedSymmetricFrameSum

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SymChar


open GlobalTheory.Mem.SymChar.Resid in
theorem resid_at_w : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal) → ∀ (kv : Σ k : Fin 2, D.nd.PlG k), ∀ k ∈ X.B.I.Kset, ∀ N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)), GlobalTheory.Mem.SymFrame.IsMatIn X (D.naut.plGw kv.1 kv.2) (GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2)) k N → GlobalTheory.Mem.SymChar.ModW X (D.naut.plGw kv.1 kv.2) (GlobalTheory.Mem.SymChar.argS X k) (∑ i, ∑ j, if symEdge D.R.rS D.R.k i j then ((GlobalTheory.Mem.SymChar.wtA D.R.rS D.R.k (GlobalTheory.Mem.SymChar.side X (D.naut.plGw kv.1 kv.2)) i j : ℤ) : ZMod (D.host.g kv.1)) * N i j else 0) := by
  intro D X _h _hE hgw kv k hk N hN
  classical
  have hg : ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal := hgw kv
  haveI : NeZero (D.host.g kv.1) := ⟨(D.host.g_prime kv.1).ne_zero⟩
  set w := D.naut.plGw kv.1 kv.2 with hwdef
  let S : AddSubgroup (X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) := (wInt X w).toAddSubgroup
  let mk := QuotientAddGroup.mk' S
  have hmk : ∀ a b, a - b ∈ wInt X w → mk a = mk b := fun a b hab =>
    (QuotientAddGroup.eq_iff_sub_mem).2 hab
  let f0 : ℤ →+ (X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) ⧸ S :=
    mk.comp (Int.castAddHom (X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F))
  have hf0 : f0 (D.host.g kv.1 : ℤ) = 0 := by
    show mk ((((D.host.g kv.1 : ℕ) : ℤ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)) = 0
    rw [Int.cast_natCast]
    exact (QuotientAddGroup.eq_zero_iff _).2 (natCast_g_mem X kv.1 hg)
  let φ : ZMod (D.host.g kv.1) →+ (X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) ⧸ S :=
    ZMod.lift (D.host.g kv.1) ⟨f0, hf0⟩
  have hφ : ∀ t : ZMod (D.host.g kv.1), φ t = mk ((t.val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) := by
    intro t
    conv_lhs => rw [← ZMod.natCast_zmod_val t, ← Int.cast_natCast]
    rw [ZMod.lift_coe]
    show mk _ = mk _
    congr 1
    simp
  suffices hs : mk (argS X k) = φ (∑ i, ∑ j, if symEdge D.R.rS D.R.k i j then
      ((wtA D.R.rS D.R.k (side X w) i j : ℤ) : ZMod (D.host.g kv.1)) * N i j else 0) by
    unfold ModW
    rw [hφ] at hs
    exact (QuotientAddGroup.eq_iff_sub_mem).1 hs
  have hsum : φ (∑ i, ∑ j, if symEdge D.R.rS D.R.k i j then
      ((wtA D.R.rS D.R.k (side X w) i j : ℤ) : ZMod (D.host.g kv.1)) * N i j else 0) =
      ∑ i, ∑ j, if symEdge D.R.rS D.R.k i j then wtA D.R.rS D.R.k (side X w) i j • φ (N i j) else 0 := by

    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_

    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs
    · rw [← zsmul_eq_mul, map_zsmul]
    · exact map_zero φ
  rw [hsum, GlobalTheory.T.symmetricFrame_weightedEdgeSum_reindex _ D.R.rS D.R.k D.R.r (rank_eq D) (side X w) (fun i j => φ (N i j))]
  unfold argS

  rw [map_add (f := _), map_sum, map_sum]
  congr 1
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [hφ]
    apply hmk
    have := dual_row X w hN (X.vectorsInLattice.1 a).2 (posE D a) (GlobalTheory.T.flagDualVector_pairing_symmetricFrame_mod_place D X w kv.1 hg a) (posN D a)
    rw [symVec_posN] at this
    exact this
  · refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : i.1 + 1 < D.R.k
    · rw [dite_eq_left hi, dite_eq_left hi]
      by_cases hw : SymFrame.EwAt X w
      · have hs : side X w = true := by simp [side, hw]
        rw [if_pos hs, hφ]
        apply hmk
        have h1 := one_sub_ew_mem X kv.1 hg hw
        have := dual_row X w hN (X.vectorsInLattice.2.2 i).2 (posB D i) (GlobalTheory.T.unipotentDualVector_pairing_symmetricFrame_mod_place D X w kv.1 hg hw h1 i)
          (posB D ⟨i.1 + 1, hi⟩)
        rw [symVec_posB X w hw] at this
        have e1 : (posB D ⟨i.1 + 1, hi⟩) = ⟨D.R.rS + i.1 + 1, by have := rank_eq D; omega⟩ :=
          Fin.ext (by simp only [posB]; omega)
        rw [e1] at this
        exact this
      · have hs : side X w = false := by simp [side, hw]
        rw [if_neg (by simp [hs])]
        rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
        have hew := GlobalTheory.T.idempotent_mem_placeIdealSpan_of_ne_one D X kv hw
        have hbw : X.B.I.fmat k *ᵥ X.bw ⟨i.1 + 1, hi⟩ ∈ X.B.I.Lf :=
          Formalism.L2.SG.Pf.unitaryCongruence.K_mv X.B.I hk (X.vectorsInLattice.2.2 _).1
        have hint := Formalism.L2.SG.Pf.unitaryCongruence.hA_int X.B.I (X.vectorsInLattice.2.2 i).2 hbw
        have e : hA X.B.I (X.bwd i) (X.B.I.fmat k *ᵥ X.bw ⟨i.1 + 1, hi⟩) =
            hA X.B.I (X.bwd i) (X.B.I.fmat k *ᵥ X.bw ⟨i.1 + 1, hi⟩) * X.ew := by
          conv_lhs => rw [X.bwd_w i]
          rw [Formalism.L2.SG.Pf.unitaryCongruence.hA_smul_left, Formalism.L2.SG.Pf.unitaryCongruence.sigA_sigA, mul_comm]
        show hA X.B.I (X.bwd i) (X.B.I.fmat k *ᵥ X.bw ⟨i.1 + 1, hi⟩) ∈ wInt X w
        rw [e]
        exact (wInt X w).smul_mem (⟨_, hint⟩ : Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) hew
    · rw [dite_eq_right hi, dite_eq_right hi, map_zero]

end GlobalTheory.Mem.SymChar
end
end
end
