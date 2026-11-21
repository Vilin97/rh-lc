module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TrueColumnsRowSharpBounds
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MoveStep
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EFirstGeOfULastNonpos
public import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built GlobalTheory.LvT.Built.TrueLaws
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trueColumns_row_sharp_bounds : ∀ (B : GlobalTheory.Mem.Base) (X : PreX B.toPre) (I : TC B X), I.Ok → I.JetsIn → GlobalTheory.LvT.WtSign.BaseSigns B → ∀ (l : I.Laws) (l0 : I.Law0 l) (Z : TC.Later B (I.cols l)) (Dx : DivX (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)) (u : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.Word), Formalism.MainNotions.product_first_zeroth_parts.Conclusion5Sharp (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) u ∧ ∀ w : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.places.Pl, (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.places.resChar w = ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).mem u).A.T → ∀ μ, Formalism.MainNotions.LocalQuadraticParts.UsedT (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) μ → μ ≠ (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.mu0 → (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.places.resChar w ∉ Dx.Qp μ → ∀ x ∈ LT.Nlam (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) u w, Formalism.MainNotions.WeilJacquetShalikaLaw.ColGeTw (I.tw l l0 Z) u μ w x (-(((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.m : ℝ) * EatT (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) u w)) := by
  first | exact @GlobalTheory.LvT.Built.TrueCols.row_true | exact GlobalTheory.LvT.Built.TrueCols.row_true | (intros; apply GlobalTheory.LvT.Built.TrueCols.row_true <;> assumption)
