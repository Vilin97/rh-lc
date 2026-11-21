module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHermitianDownMoveAtLevelPrimePlace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmulLk
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MiddleStepOneLevelProjectionEqChartProjectionStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostPrimesOverLevelPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicRelationClassesCoordinatesStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicConjugateCharacterStandardFormsStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelFunctionalEqOfClassesRelatedAtPlaceStatement

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hermitianDownMove_at_levelPrime_place : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)) (F : ∀ u, FormsTiedSym (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u i v (c : ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).mem u).C.cls i) (g : Module.Dual (((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).mem u).A.Fv v) (((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).fm u).lk i v c)), ∃ γ, i ≤ (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.m → g ≠ 0 → DnCl (F u).atT (F u).lv i v c g γ ∧ AdOf H u i c (((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).fm u).dn i v c g) γ v := by
  first | exact @GlobalTheory.Mem.Col2.HAt.dn_move_exists | exact GlobalTheory.Mem.Col2.HAt.dn_move_exists | (intros; apply GlobalTheory.Mem.Col2.HAt.dn_move_exists <;> assumption)
