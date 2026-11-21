module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnLevelOfStepZeroFormsLevelTrueColumns
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Formalism.LocalToGlobal.HermitianForms.TiedTwJSym

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnLevel_of_stepZeroFormsLevel_trueColumns : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch : ℕ → Type} {chOf : ∀ i, ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).mem u).C.cls i → Ch i} (F : FormsTiedSym (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) u Ch chOf), I.StdF l Z u F →
  ∃ L : ColLevel (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.g ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).mem u).C ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).mem u).A ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).clsLat u),
    SameCar (rank_eq_first_level (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R) L.Lb (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.Lb
      L.Uloc (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.Uloc
      L.U (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.U
      (fun c => (L.y c).1) (fun c => ((F.cls 0 (Nat.zero_le _) (Or.inl rfl)).y c).1)
      (fun c s => (L.stabI c s).1) (fun c s => ((F.cls 0 (Nat.zero_le _) (Or.inl rfl)).stabI c s).1) ∧
    F.gl.sp = L.splitG ∧ ∀ i v h, F.glev0.fr i v h = reGL (rank_eq_first_level (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R) _ (L.frG i v h) := by
  first | exact @GlobalTheory.Mem.LevZero.colLevel_of_forms | exact GlobalTheory.Mem.LevZero.colLevel_of_forms | (intros; apply GlobalTheory.Mem.LevZero.colLevel_of_forms <;> assumption)
