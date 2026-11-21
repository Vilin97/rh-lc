module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NonemptyColCh
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EmbeddingAtLocalFactor
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData ValuativeRel
set_option maxHeartbeats 1000000
noncomputable section
namespace GlobalTheory.Fam.TopLocFac
theorem isLocFac_xiStd_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {hT : GatTies (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {Gi : Formalism.MainNotions.G.Inst (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) L} {Gl : Formalism.MainNotions.G.LatInst (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {cX : ExtraC} {ex : Extra (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ n : Fin a.n,
   GlobalTheory.LocMod.IsLocFac (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (a.pl n).1 ((a.G n).cg ((a.G n).s + 1)) (_root_.GlobalTheory.Fam.TopLoc.standardXi a n) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha ht n
  have hid := ((ha.tie (fun t => (nonempty_rowCh (D := _root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) _ _ u a.g ht.pinX.std t).some) fun t => (nonempty_colCh (D := _root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) u _).some).2.idem n).1
  obtain ⟨hs, hX, -⟩ := hW.tr.ok.spaces
  have hsd : ∀ j, j ≤ B.R.m → IsSelfDualC _ (a.g.x j).L := fun j hj => by
    have e : ((a.g.x j).L : Set (Fin ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X j).rank → (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E)) = intVec (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) _ :=
      Set.ext (ht.pinX.xs j hj).2.2
    have h1 := GlobalTheory.AdForm.VacStd.coe_latFrame_of_eq ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X j) hs _ (hX j)
    have h2 : GlobalTheory.PlaceModel.latFrame ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X j) = (a.g.x j).L := SetLike.coe_injective (h1.trans e.symm)
    rw [← h2]
    exact GlobalTheory.PlaceModel.isSelfDualC_latFrame _
  have hm : (a.G n).s + 1 + 1 = B.R.m := (a.G n).hs
  exact ⟨(a.G n).k, _, _, _, _, ofSplit (a.G n).q, _, _, _, _, _, _, (a.G n).FX ((a.G n).s + 1) le_rfl, (a.G n).FM, _,
    (GlobalTheory.QTw.GeoInhab.int_dense (a.G n).q hid).2, hid,
    GlobalTheory.StdHomAt.int_iff_up_mem_stdHom _ _ (a.G n).q (a.G n).unit _ _ _ _ _ _ _ _ (hsd _ (by omega)) (hsd _ hm.le)
      (ht.pinX.xs _ (by omega)).2.2 (ht.pinX.xs _ hm.le).2.2 ((a.G n).latX _ _) (a.G n).latM,
    GlobalTheory.LastTwoSteps.xiTop_mem_SB _ (GlobalTheory.StepData.Chain.ofType_regular _ _ _ _ _) (a.G n).S.cond (a.G n).unitVol (by simp) _,
    (a.G n).cg_top, fun _ => rfl⟩
end GlobalTheory.Fam.TopLocFac
end
end
