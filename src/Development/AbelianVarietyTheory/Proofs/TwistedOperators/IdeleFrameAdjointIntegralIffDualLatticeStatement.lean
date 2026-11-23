module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RedMFrMapAdjZero
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCharacterEmbeddingCompat
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeLatticeVacuumTransport
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RevPosRevPos
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThPDatumEq
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatLConjIIffHform

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatAStdLIff

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftLevel




noncomputable section

namespace GlobalTheory.TensColRead

variable {D : D7}

def embInf (D : D7) : Ainf D.host.F ⊗[D.host.F] D.host.E →ₗ[D.host.F] AE D :=
  TensorProduct.map (LinearMap.inl D.host.F (Ainf D.host.F) (Af D.host.F)) LinearMap.id

theorem embInf_add_emb (w : AE D) :
    embInf D (Formalism.L2.Theta.infPart D w) + GlobalTheory.TensLatMove.emb D (Formalism.L2.Theta.finPart D w) = w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb =>
    rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _)]
    conv_rhs => rw [← ha, ← hb]
    abel
  | tmul a e =>
    have e1 : embInf D (Formalism.L2.Theta.infPart D (a ⊗ₜ[D.host.F] e)) =
        (pairA D.host.F (fstA D.host.F a) 0) ⊗ₜ[D.host.F] e := rfl
    have e2 : GlobalTheory.TensLatMove.emb D (Formalism.L2.Theta.finPart D (a ⊗ₜ[D.host.F] e)) =
        (pairA D.host.F 0 (sndA D.host.F a)) ⊗ₜ[D.host.F] e := rfl
    rw [e1, e2, ← TensorProduct.add_tmul]
    congr 1
    exact Prod.ext (add_zero _) (zero_add _)

theorem emb_finPart (w : AE D) (h : Formalism.L2.Theta.infPart D w = 0) :
    GlobalTheory.TensLatMove.emb D (Formalism.L2.Theta.finPart D w) = w := by
  have := embInf_add_emb w
  rwa [h, map_zero, zero_add] at this

theorem col_iff {S T : HSp D} (L : Lt D.host.E T.rank) (x : WO S T) (k : Fin S.rank) :
    (fun c => Formalism.L2.Theta.finPart D (x c k)) ∈ hatV L ↔
      (fun c => toEAf D (x c k)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) L :=
  GlobalTheory.LevSplit.latHat_iff L _

def colHom (S T : HSp D) (k : Fin S.rank) : WO S T →+ (Fin T.rank → AfE D) where
  toFun x := fun c => Formalism.L2.Theta.finPart D (x c k)
  map_zero' := by funext c; simp
  map_add' x y := by funext c; simp

theorem toAf_single_mem (n : ℕ) (k : Fin n) : toAf (Pi.single k (1 : D.host.E)) ∈ hatV (stdL D.host.E n) :=
  AddSubgroup.subset_closure ⟨1, GlobalTheory.TensLatMove.intAf_one, Pi.single k 1,
    Submodule.subset_span ⟨k, rfl⟩, rfl⟩

theorem mem_hatA_stdL_iff : ∀ (D : D7) (S T : HSp D) (L : Lt D.host.E T.rank) (x : WO S T), IsFinPt x → (x ∈ hatA S T (tens (stdL D.host.E S.rank) L) ↔ ∀ k : Fin S.rank, (fun c => toEAf D (x c k)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) L) := by
  intro D S T L x hx
  constructor
  · intro hmem k
    rw [← col_iff]
    have hle : hatA S T (tens (stdL D.host.E S.rank) L) ≤ (hatV L).comap (colHom S T k) := by
      rw [hatA, AddSubgroup.closure_le]
      rintro _ ⟨α, hα, y, hy, rfl⟩
      exact AddSubgroup.subset_closure ⟨α, hα, y k, (GlobalTheory.SW.TensLat.mem_tens_stdL L y).1 hy k, rfl⟩
    exact hle hmem
  · intro h
    have hu : ∀ k, (fun c => Formalism.L2.Theta.finPart D (x c k)) ∈ hatV L := fun k => (col_iff L x k).2 (h k)
    have e : x = ∑ k, GlobalTheory.TensLatMove.outer S T (toAf (Pi.single k 1)) (fun c => Formalism.L2.Theta.finPart D (x c k)) := by
      ext c k'
      have hc : Formalism.L2.Theta.infPart D (x c k') = 0 := by
        have := congrFun (congrFun hx c) k'
        simpa using this
      rw [Matrix.sum_apply]
      simp only [GlobalTheory.TensLatMove.outer, Matrix.of_apply, toAf]

      rw [← map_sum, Finset.sum_eq_single k']
      · rw [Pi.single_eq_same, ← Algebra.TensorProduct.one_def, mul_one]
        exact (emb_finPart _ hc).symm
      · intro j _ hj
        rw [Pi.single_eq_of_ne (Ne.symm hj), TensorProduct.tmul_zero, mul_zero]
      · intro h'; exact absurd (Finset.mem_univ k') h'
    rw [e]
    exact sum_mem fun k _ => GlobalTheory.TensLatMove.outer_mem S T _ L _ (toAf_single_mem _ k) _ (hu k)

end GlobalTheory.TensColRead

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdeleFrameAdjointIntegralIffDualLattice

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftLevel

namespace GlobalTheory.DualRed

theorem adjA_entry : ∀ (D : D7) (S T : HSp D), S.gram = 1 → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (x : WO S T) (k : Fin S.rank) (j : Fin T.rank), adjA S T βS βT 1 x k j = Formalism.UG.hform (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) (T.gram.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F))) (fun c => toEAf D (x c k)) (fun c => βT.1 c j) := by
  intro D S T hS βS βT x k j
  have hE : toEAf D = GlobalTheory.LevSplit.finSw D := rfl
  unfold adjA frMapAdj
  rw [hS, inv_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, map_one, one_smul, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul, Matrix.map_mul]
  unfold Formalism.UG.hform
  simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, hE, GlobalTheory.LevSplit.finSw_cA,
    GlobalTheory.LevSplit.finSw_incA, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem adj_int_iff : ∀ (D : D7) (S T : HSp D), S.gram = 1 → ∀ (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βT ΛT → ∀ (J : Ideal (𝓞 D.host.E)), Squarefree J → ∀ x : WO S T, IsFinPt x → ((IsIntM (adjA S T βS βT 1 x) ∧ ∀ PP : Formalism.L2.DIV.Pl D.host.E, J ≤ PP.asIdeal → redM PP (adjA S T βS βT 1 x) = 0) ↔ x ∈ hatA S T (tens (stdL D.host.E S.rank) (conjI J • ΛT))) := by
  intro D S T hS ΛT hsd βS βT hfr J hJ x hx
  have hJ0 : J ≠ ⊥ := by
    rw [← Submodule.zero_eq_bot]
    exact hJ.ne_zero
  rw [GlobalTheory.TensColRead.mem_hatA_stdL_iff D S T _ x hx]
  simp only [GlobalTheory.FrameIdeal.mem_hatL_conjI_iff_hform D T ΛT hsd βT hfr J hJ0, ← adjA_entry D S T hS βS βT x]
  unfold IsIntM redM
  constructor
  · rintro ⟨hint, hred⟩ k j
    refine ⟨⟨_, hint k j⟩, GlobalTheory.LiftLevel.mem_idS hJ fun PP hPP => ?_, rfl⟩
    have h0 := congrFun (congrFun (hred PP hPP) k) j
    simpa only [Matrix.zero_apply, Pi.zero_apply, dif_pos (hint k j)] using h0
  · intro h
    have hint : ∀ k j, adjA S T βS βT 1 x k j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
      intro k j
      obtain ⟨s, -, hs⟩ := h k j
      rw [← hs]
      exact s.2
    refine ⟨hint, fun PP hPP => ?_⟩
    funext k j
    obtain ⟨s, hsI, hs⟩ := h k j
    have hse : (⟨adjA S T βS βT 1 x k j, hint k j⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = s := Subtype.ext hs.symm
    simp only [Matrix.zero_apply, Pi.zero_apply, dif_pos (hint k j), hse]
    exact GlobalTheory.LiftLevel.resS_eq_zero hPP hsI

end GlobalTheory.DualRed
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdeleFrameAdjointIntegralIffDualLatticeStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftLevel


theorem _root_.GlobalTheory.T.ideleFrameAdjoint_integral_iff_dualLattice : ∀ (D : D7) (S T : HSp D), S.gram = 1 → ∀ (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βT ΛT → ∀ (J : Ideal (𝓞 D.host.E)), Squarefree J → ∀ x : WO S T, IsFinPt x → ((IsIntM (adjA S T βS βT 1 x) ∧ ∀ PP : Formalism.L2.DIV.Pl D.host.E, J ≤ PP.asIdeal → redM PP (adjA S T βS βT 1 x) = 0) ↔ x ∈ hatA S T (tens (stdL D.host.E S.rank) (conjI J • ΛT))) := by
  first | exact @GlobalTheory.DualRed.adj_int_iff | exact GlobalTheory.DualRed.adj_int_iff | (intros; apply GlobalTheory.DualRed.adj_int_iff <;> assumption)
end
end
