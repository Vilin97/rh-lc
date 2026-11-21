module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefAEqOfHeq

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl
namespace GlobalTheory.Mem.R3.Rw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt}

set_option maxHeartbeats 2000000 in

set_option maxHeartbeats 2000000 in

set_option maxHeartbeats 2000000 in

variable {hX : B.fields.Ok} {Wt W₁ : Set B.places.Pl}

set_option maxHeartbeats 4000000 in

theorem ExtModel.sign_at_base_place_eq_embedding (z : Dat (w.st Z) w.I hX T Wt) :
    sg0 (w.st Z).toD7 (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A = (w.st Z).toD7.what₂.embLL :=
  if_pos z.R.hv0

set_option maxHeartbeats 4000000 in

set_option maxHeartbeats 4000000 in

set_option maxHeartbeats 4000000 in

end GlobalTheory.Mem.R3.Rw
end
