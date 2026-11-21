module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EvaluationMapTrueChainFormsToForms
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LowerTieTwAt

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evaluationMap_trueChain_forms_to_forms : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (u : B.Word) (a : I.ι), (∀ φ ∈ ((I.tw l l0 Z).fm u a).Fi B.R.m, GlobalTheory.PerQ.PtT (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) u a φ ∈ ((I.tw l l0 Z).fm u a).ptC) ∧ ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).fm u).SgInterlace := by
  first | exact @GlobalTheory.PerQ.ptT_forms_built | exact GlobalTheory.PerQ.ptT_forms_built | (intros; apply GlobalTheory.PerQ.ptT_forms_built <;> assumption)
