import Formalism.LocalToGlobal.ProjectiveLattices.EtArch
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAtData
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAtDataPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAtPf

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Torus

open ReciprocityTheory.ChartRestriction.G.I2

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def thRat (X : PT E) (s : (Fin 1 → Vsp X.dim) → ℂ) (a : Fin X.r → Vsp X.dim) : ℝ :=
  ∏ j, Real.sqrt (X.ptN2 1 s fun _ => a j) / Real.sqrt (X.l2 1 s)

variable (E) in

variable (E) in

variable (E) in

variable (E) in

variable (E) in

end Torus

variable {D : D7} {T : Top D} (h : LawsP T)

end Formalism.L2.Pj
