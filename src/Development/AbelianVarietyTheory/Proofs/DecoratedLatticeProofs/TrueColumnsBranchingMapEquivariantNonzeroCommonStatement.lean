module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueColumnsBranchingMapEquivariantNonzeroCommon
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PinColL

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trueColumns_branchingMap_equivariant_nonzero_common : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (hN : B.R.N B.R.m = (B.R.N B.R.m - 1) + 1), (∀ τ, Formalism.L2.Col.Br.Interlace hN (Formalism.L2.Forms.lamT (D := (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)) u B.R.m τ) (sgT (D := (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)) u τ)) ∧ BrEqv hN _ _ (Formalism.L2.Forms.lamT (D := (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)) u B.R.m) (sgT (D := (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)) u) (lowOf I l Z u) ∧ (∃ Φ ∈ ValC _ (Formalism.L2.Forms.lamT (D := (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)) u B.R.m), lowOf I l Z u Φ ≠ 0) ∧ ∀ (a : I.ι) z c (y : FrN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) (B.R.N B.R.m - 1)), (I.per l u a).lowerMap z c ⟨y.1, y.2⟩ = lowOf I l Z u (fun y' => z c ⟨y'.1, y'.2⟩) y := by
  first | exact @GlobalTheory.TrueBranch.branching_true_columns | exact GlobalTheory.TrueBranch.branching_true_columns | (intros; apply GlobalTheory.TrueBranch.branching_true_columns <;> assumption)
