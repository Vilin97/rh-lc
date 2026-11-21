import Formalism.LocalToGlobal.Columns.TiedCH
import Formalism.LocalToGlobal.Columns.TiedCG
import Formalism.LocalToGlobal.HermitianForms.RankEqFirstLevel

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.Col.CF

open Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def crdN (D : ColRec) (i : ℕ) (hi : i ≤ D.R.m) : (D.sp.X i).V ≃ₗ[D.host.E] (Fin (D.R.N i) → D.host.E) :=
  (D.sp.X i).frame.equivFun.trans (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankN D i hi)).symm)

def crdP (D : ColRec) : D.sp.X'.V ≃ₗ[D.host.E] (Fin (D.R.N D.R.m - 1) → D.host.E) :=
  D.sp.X'.frame.equivFun.trans (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankP D)).symm)

set_option maxHeartbeats 4000000 in

end Formalism.L2.Col.CF

end
