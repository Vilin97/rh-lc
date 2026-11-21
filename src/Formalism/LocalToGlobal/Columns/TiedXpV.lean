module

public import Formalism.LocalToGlobal.Columns.TiedXp
public import Formalism.LocalToGlobal.Columns.TiedVal
public import Formalism.LocalToGlobal.Columns.TiedValRat
public import Formalism.LocalToGlobal.Columns.TiedValLatG
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkMapInitMinor
public import Formalism.LocalToGlobal.Columns.BaseLemmas

@[expose] public section

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem xp_half (R : Ranks) : R.m * (R.t + 1) / 2 = R.m * ((R.t + 1) / 2) := by
  obtain ⟨b, hb⟩ := R.t_odd
  have h : R.t + 1 = 2 * (b + 1) := by omega
  rw [h, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2), Nat.mul_left_comm, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]

theorem xp_sgTrue_eq {R : Ranks} (S : RowPar R) : S.sgTrue = shW S.sg ((R.m * (R.t + 1) / 2 : ℕ) : ℤ) := by
  unfold RowPar.sgTrue shiftW shW
  congr 1
  funext i
  rw [xp_half]
  push_cast
  ring

section Gen

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))} (σ₀ : X.K →+* ℂ)
  (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x)) (lam : X.Tau → DomWeight n)
  (Lf : DecoSet X.E n ST SG → Submodule (𝓞 X.E) (Sp X.E n)) (Λ : LevFam X.E X.K n SG)

end Gen

section GenP

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (ΛM : LevFam X.E X.K (R.N R.m - 1) Pr.vGs)

variable (hc : CMData X.F X.E) (hX : X.Ok) (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x))
  (hS : DecoPtSurj hc (R.N R.m - 1) (∅ : Finset (Pl X.E)) Pr.vGs)

namespace XpV

end XpV




end GenP

section Rec

variable {d : ColDat} (a : ColArgs d)

theorem sgT_eq (u : d.what₂.Word) : CF.sgT (D := d.colRec a) u = d.W.sgTrue :=
  funext fun τ => (xp_sgTrue_eq (d.W.row τ)).symm

variable (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurjP d) (u : d.what₂.Word)

end Rec

end Formalism.L2.Col
