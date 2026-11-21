module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedTupleReadingLevelCharacter
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RdLevOn

@[expose] public section

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.UG GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TypeLev Matrix Formalism.L2.Forms GlobalTheory.SeeSaw.TwLev
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedTuple_reading_level_character : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l))
    (a : I.ι) {bad : Set (HeightOneSpectrum (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F))}
    (S : StepLevel (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E (sigD (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)) (gramP (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)) 1 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.f bad)
    {y lat st}, I.ReadsP a S.Lb S.U S.chi y lat st → ∀ (_c : (I.stX a).Cl) (ξ : ∀ PP : Pl (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E, (kP PP)ˣ →* ℂˣ),
    (∀ PP ∈ I.Q a, ∀ x, ((ξ PP x : ℂˣ) : ℂ) =
      B.embLL ((Formalism.L2.DIV.resChar (I.tup a : Formalism.L2.DIV.Chr B.fields.F B.fields.E B.fields.K) PP x : B.LLˣ) : B.LL)) →
    RdLevOn (E := B.fields.E) B.sp.cm (RatAt (I.Q a)) S.U S.chi (rowTyG I.Ch I.Ps) B.embLL (I.Q a)
      (fun _ => blockTri (blk2 B.R.r)) (fun P => (ξ P.1).comp (blkDet (blk2 B.R.r) 1)) := by
  first | exact @GlobalTheory.SeeSaw.TwLev.rdLevOn_reads_tw | exact GlobalTheory.SeeSaw.TwLev.rdLevOn_reads_tw | (intros; apply GlobalTheory.SeeSaw.TwLev.rdLevOn_reads_tw <;> assumption)
