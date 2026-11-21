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
import GroundTheory.AutomorphicForms.GL2Classical.HeckeCommute
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.Unimodular
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Uniform
import GroundTheory.AutomorphicForms.Satake
import GroundTheory.AutomorphicForms.MacdonaldWhittakerHecke
import GroundTheory.AutomorphicForms.StrongApproximationSLDense
import GroundTheory.GlobalFields.LocalAtPlace
import GroundTheory.AutomorphicForms.HeckeIrreducible
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsDecay

open NumberField Matrix CongruenceSubgroup ModularForm Complex Filter
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups ModularForm Real InnerProductSpace Manifold NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

open AdelicGLn AutomorphicForm

set_option linter.unusedSectionVars false

variable {N : ℕ} [NeZero N] {k : ℤ}

variable (k) in

theorem posIdele_fst_rat (r : ℝ) (hr : 0 < r) :
    ((Reduction.posIdele (K := ℚ) r hr : Global.IdeleGroup ℚ) : 𝔸[ℚ]).1 =
      Global.RationalIdeles.realEquiv.symm r := by
  apply Global.RationalIdeles.realEquiv.injective
  rw [RingEquiv.apply_symm_apply, Global.RationalIdeles.realEquiv_apply]
  have := Reduction.infiniteProj_posIdele (K := ℚ) r hr default
  rw [← Global.IdeleGroup.coe_infiniteProj, this]
  simp [Global.posRealToUnits, Global.posRealElem, Global.RationalIdeles.isReal_infinitePlace]
  exact RingEquiv.apply_symm_apply (InfinitePlace.Completion.ringEquivRealOfIsReal _) r

end GL2Classical

end

end GroundTheory.Automorphic
