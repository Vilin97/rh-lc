import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BrgStdR
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EventuallyCongOne
import Formalism.LocalToGlobal.Columns.BaseLemmas
import Formalism.LocalToGlobal.Columns.RowFormsLemmas
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcParameterEAddHalfShiftLeBSucc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoefDualPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Col Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
open GlobalTheory.Mem GlobalTheory.Mem.Col2
open scoped TensorProduct

namespace GlobalTheory.Mem.R3.StdModel

section Gen

variable {X : Fields} {n : ℕ} (σ : X.K →+* ℂ)

variable [NeZero n]

variable {σ} {a : ℕ} {H Γ W : Type} [AddCommGroup W] [Module ℂ W]
  {mat : H → GL (Fin a) (X.E ⊗[X.F] Formalism.L2.Herm.Af X.F)} {rat : Γ → GL (Fin a) X.E → Prop} {ρ : Γ → W → W}
  {ι : Type} {lam : X.Tau → DomWeight n} {rho : GL (Fin n) X.E →* Module.End X.K (VV X.K lam)}

end Gen

section Rec

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem gram_V (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (hI : I.Ok) (i : Fin X.toD7.R.m) : (Vc X.toD7 i).gram = 1 := by
  obtain ⟨hs, -, -, -, -, hV⟩ := hI.spaces
  have h1 := hV ((i : ℕ) + 1)
  have hn : X.B.sp.Vneg ((i : ℕ) + 1) = false := X.B.V_pos _ (by omega) i.2
  rw [hn] at h1
  change (X.B.sp.V ((i : ℕ) + 1)).gram = 1
  rw [h1]
  refine Matrix.ext fun a b => (Formalism.BasicNotions.Examples₂.stdSpace_gram_apply hs _ _ _ _ a b).trans ?_
  simp [Matrix.one_apply, Formalism.BasicNotions.Examples₂.sgn]

variable (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL))
  (tr : TrI X.B px)

set_option maxHeartbeats 4000000 in

open Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Indef in
set_option maxHeartbeats 4000000 in

end Rec

end GlobalTheory.Mem.R3.StdModel

end
