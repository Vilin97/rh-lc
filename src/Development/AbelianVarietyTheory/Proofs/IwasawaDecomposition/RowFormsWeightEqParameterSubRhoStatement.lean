module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFormsWeightEqParameterSubRho
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EWtApply
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UfGLRatHom
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryOfIsON

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowForms_weight_eq_parameter_sub_rho : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι), ∀ τ (i : Fin ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.N (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.m - 1)), (((I.fm l u a).sg τ).w i : ℚ) = Formalism.L2.Forms.sgHC (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).hcW u τ) i - rhoVec ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.N (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.m - 1) i := by
  first | exact @GlobalTheory.Mem.Col2.TC.fm_sg_eq | exact GlobalTheory.Mem.Col2.TC.fm_sg_eq | (intros; apply GlobalTheory.Mem.Col2.TC.fm_sg_eq <;> assumption)
