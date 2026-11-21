import Mathlib
import GroundTheory.AutomorphicForms.GL2Classical.Adelic
import GroundTheory.AutomorphicForms.GL2Classical.ConstantTerm
import GroundTheory.AutomorphicForms.GL2Classical.Smooth
import GroundTheory.AutomorphicForms.HarishChandraCentre
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.SmoothKZ
import GroundTheory.AutomorphicForms.GL2Classical.CuspConverse
import GroundTheory.AutomorphicForms.GL2Classical.GrowthReduction
import GroundTheory.AutomorphicForms.GL2Classical.KFinite
import GroundTheory.AutomorphicForms.HeckeAlgebraLevel

open NumberField IsDedekindDomain Matrix CongruenceSubgroup
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups ModularForm

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

open AdelicGLn AutomorphicForm

set_option linter.unusedSectionVars false

variable (p q : ℕ) [NeZero p] [NeZero q]

instance : NeZero (p * q) := ⟨Nat.mul_ne_zero (NeZero.ne p) (NeZero.ne q)⟩

variable [Fact p.Prime]

variable [Fact q.Prime] (N : ℕ) [NeZero N]

variable {k : ℤ}

end GL2Classical

end

end GroundTheory.Automorphic
