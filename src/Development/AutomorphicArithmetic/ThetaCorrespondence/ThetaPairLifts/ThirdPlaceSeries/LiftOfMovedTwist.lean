module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadPackageTwistHeq
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MMvDstA
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open GlobalTheory.Mem.R3.Tr
namespace GlobalTheory.HeightCounting.Up.LiTw
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
section Gen
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
end Gen
variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} {x : St P} {N : TwNew (Dof x)}
private theorem cfOf_stTw (m : Moved (oTw x N)) (hc : m.Copy) (hh : m.Coh)
    (r : ReadPk m (sideTw x N)) (hp : r.Pin) :
    (N.cf (cfOf x) : CharFrame (Dof (stTw x N m hc hh r hp))) =
      cfOf (stTw x N m hc hh r hp) := by
  with_unfolding_all
    unfold TwNew.cf cfOf TC.cf
    rfl

private theorem castFrame_row {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7}
    {cf cf' : CharFrame D} {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r}
    (e : cf = cf') (a : HeightCountingBaseData hL D cf rep) :
    (Eq.ndrec (motive := fun c => HeightCountingBaseData hL D c rep) a e).A.row = a.A.row := by
  cases e
  rfl

def liftOfMovedTwist {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (l : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x) (m : Moved (oTw x N)) (hc : m.Copy) (hh : m.Coh) (r : ReadPk m (sideTw x N))
    (hp : r.Pin) (e : HEq (repOf r.Y) (repOf x.r.Y)) (mt : InMt r.Y (cfOf (stTw x N m hc hh r hp)) w.I.xi (QOf P)) (rat : InRat r.Y m.z.cG) :
    _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL (stTw x N m hc hh r hp) where
  a := by
    with_unfolding_all
      exact Eq.ndrec
        (motive := fun cf => HeightCountingBaseData hL (Dof (stTw x N m hc hh r hp)) cf (repOf r.Y))
        (_root_.UpperTheory.One.M.stageAOfSwitch trivial N l.a (repOf r.Y) e)
        (cfOf_stTw m hc hh r hp)
  Pq := (by with_unfolding_all exact (l.Pq :))
  Pq_over := (by with_unfolding_all exact (l.Pq_over :))
  sel := (by with_unfolding_all exact (l.sel :))
  mt := (by with_unfolding_all exact (mt :))
  rat := (by with_unfolding_all exact (rat :))
  cusp := by
    rw [castFrame_row]
    with_unfolding_all exact cusp N l.cusp
theorem li_copy_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x) (N : TwNew (Dof x)) (m : Moved (oTw x N)) (hm : m.z = datTw x N) (hc : m.Copy) (hh : m.Coh) (r : ReadPk m (sideTw x N)) (hp : r.Pin), HEq (repOf r.Y) (repOf x.r.Y) → (∀ μ h i y, HEq (r.Y.IL.jMt μ h i y).1 (x.r.Y.IL.jMt μ h i y).1) → (∀ i y, HEq (r.Y.mj.eW i y) (x.r.Y.mj.eW i y)) → ∃ l' : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL (stTw x N m hc hh r hp), HEq l'.a.A.row (N.row l.a.A.row) ∧ HEq l'.Pq l.Pq ∧ HEq l'.rat.S (N.rat l.rat.S) ∧ HEq l'.rat.In.Sb l.rat.In.Sb ∧ HEq l'.rat.In.hL l.rat.In.hL ∧ HEq l'.rat.In.eig l.rat.In.eig ∧ HEq l'.rat.In.θ l.rat.In.θ := by
  intro hL K B f T w P x l N m hm hc hh r hp e H1 H2
  cases m
  dsimp only at hm
  subst hm
  have G1 : ∀ μ h i y, (x.r.Y.IL.jMt μ h i y).1 = jMtB (N := N) ((by with_unfolding_all exact (r.Y :))) μ h i y := fun μ h i y =>
    eq_of_heq ((by with_unfolding_all exact ((HEq.symm (H1 ((μ)) ((h)) ((i)) ((y)))) : _)))
  have G2 : ∀ i y, x.r.Y.mj.eW i y = eWB (N := N) ((by with_unfolding_all exact (r.Y :))) i y := fun i y =>
    eq_of_heq ((by with_unfolding_all exact ((HEq.symm (H2 ((i)) ((y)))) : _)))
  have mt : InMt r.Y (cfOf (stTw x N _ hc hh r hp)) w.I.xi (QOf P) := by
    with_unfolding_all
      exact Eq.ndrec (motive := fun cf => InMt r.Y cf w.I.xi (QOf P))
        (inMt (N := N) r.Y G1 l.mt) (cfOf_stTw _ hc hh r hp)
  refine ⟨liftOfMovedTwist l _ hc hh r hp e mt ?_, ?_⟩
  · with_unfolding_all exact inRat (N := N) r.Y G2 l.rat
  · constructor
    · unfold liftOfMovedTwist
      rw [castFrame_row]
      with_unfolding_all exact HEq.refl (N.row l.a.A.row)
    · with_unfolding_all
        exact ⟨HEq.refl l.Pq, HEq.refl (N.rat l.rat.S), HEq.refl l.rat.In.Sb,
          HEq.refl l.rat.In.hL, HEq.refl l.rat.In.eig, HEq.refl l.rat.In.θ⟩
end GlobalTheory.HeightCounting.Up.LiTw
end
end
