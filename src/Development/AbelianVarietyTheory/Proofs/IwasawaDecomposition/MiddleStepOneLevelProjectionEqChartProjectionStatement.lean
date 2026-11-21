module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MiddleStepOneLevelProjectionEqChartProjection
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmulLk

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.middleStep_oneLevel_projection_eq_chart_projection : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)) (F : ∀ u, FormsTiedSym (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u i (h1 : 1 ≤ i) (h2 : i + 1 ≤ (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.m) v (c : ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).mem u).C.cls i), (∀ (z : Formalism.L2.Forms.Ld (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) u i (le_of_succ_m h2) c) (z' : LdG (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) i (le_of_succ_m h2) (clsCrd (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) u i (le_of_succ_m h2) c)), z'.1 = z.1 → ((F u).lvC i h1 h2).pr v c z' = ((F u).lv i (le_of_succ_m h2)).pr v c z) ∧ ∀ (z : Formalism.L2.Forms.Lk (F u).atT i (le_of_succ_m h2) v c) (z' : LkG (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) i (le_of_succ_m h2) (PvG (F u).atT.res v) (clsCrd (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) u i (le_of_succ_m h2) c)), z'.1 = z.1 → ((F u).lvC i h1 h2).prk v c z' = ((F u).lv i (le_of_succ_m h2)).prk v c z := by
  first | exact @GlobalTheory.Mem.Col2.HAt.pr_lvC_eq_lv | exact GlobalTheory.Mem.Col2.HAt.pr_lvC_eq_lv | (intros; apply GlobalTheory.Mem.Col2.HAt.pr_lvC_eq_lv <;> assumption)
