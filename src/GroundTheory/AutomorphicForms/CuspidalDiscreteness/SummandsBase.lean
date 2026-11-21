module

public import Mathlib
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsDecay
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.Smoothing
public import GroundTheory.AutomorphicForms.GKModules.Garding

@[expose] public section

open MeasureTheory Set Filter Topology Function

namespace GroundTheory.Automorphic

noncomputable section

namespace BanachRep

variable {G G' : Type*} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G']
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def comp (π : BanachRep G E) (f : G' →* G) (hf : Continuous f) : BanachRep G' E where
  toHom := π.toHom.comp f
  continuous_orbit' v := (π.continuous_orbit v).comp hf

end BanachRep

namespace CuspidalSpectrum

open AutomorphicForm

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}


def archP : archGroup K n →* Reduction.normOneGL (K := K) (n := n) :=
  (archProj K n).comp (archGroup K n).subtype

@[simp] theorem archimedeanProjection_apply (a : archGroup K n) : archP K n a = archProj K n (a : ArchUnits K n) := rfl

theorem continuous_archP : Continuous (archP K n) :=
  continuous_archProj.comp continuous_subtype_val

variable (μ : Measure (Reduction.normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]

end CuspidalSpectrum

end

end GroundTheory.Automorphic
