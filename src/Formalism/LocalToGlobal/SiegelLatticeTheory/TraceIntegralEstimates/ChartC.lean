module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.StCoordVCoef
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.ChartLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RootPatterns
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ChartC
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FormTransp
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan

@[expose] public section

noncomputable section

open scoped Matrix Classical
open MeasureTheory Finset NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj
  Formalism.L2.SG.LocWSOf

namespace Formalism.L2.S.Pv.Chart

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} {θ : ℝ} (C : Formalism.L2.SG.LocWSOf.Choice X θ) (u u' : D.what₂.Word)
  (w : Point D.host.E (D.R.rS + 1)) (γ : X.B.I.Ginf) (τ : D.what₂.Tau)

include C

theorem place_chart (hrep : IsPtRep X u u' w γ) :
    ∃ ψ : (rootPat (ptLoc D τ w) → ℂ) → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS,
      (∀ y, Matrix.of (ψ y) ∈ Formalism.MainNotions.S.Rset D.R.k D.R.rS (Formalism.L2.SG.RealFrameCoordinates.g0 C γ τ) ∧
        rootCoords D.R.k D.R.rS (zB X (C.Qi τ) u' τ) (ptLoc D τ w) (ψ y) = y) ∧
      ∀ x, Matrix.of x ∈ Formalism.MainNotions.S.Rset D.R.k D.R.rS (Formalism.L2.SG.RealFrameCoordinates.g0 C γ τ) →
        ψ (rootCoords D.R.k D.R.rS (zB X (C.Qi τ) u' τ) (ptLoc D τ w) x) = x := by
  obtain ⟨hzW, hTz⟩ := Formalism.L2.SG.Pf.zTr C u τ
  obtain ⟨hzW', hTz'⟩ := Formalism.L2.SG.Pf.zTr C u' τ
  have hT : ∀ u0 : D.what₂.Word, 0 < Tr D u0 := fun u0 => by
    unfold Tr
    exact Nat.cast_pos.2 (D.mem u0).A.T_prime.pos
  have hk : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hg0 : Formalism.L2.SG.RealFrameCoordinates.g0 C γ τ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) :=
    Formalism.L2.SG.Pf.LTL.trG_mem _ _ _ (C.isT τ).2.1 (C.isT τ).2.2.1 _
  exact locChart D.R.k D.R.rS hk _ _ hzW (by rw [hTz]; exact hT u) hzW' (by rw [hTz']; exact hT u') (ptLoc D τ w) _
    hg0 (Formalism.L2.SG.RealFrameCoordinates.zhat_conjugator_eq_point C u u' w γ hrep τ)

theorem stCoordV_inj (hrep : IsPtRep X u u' w γ) {y₁ y₂ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))}
    (h₁ : y₁ ∈ Formalism.L2.SG.NGPin.StV X u u' γ (vOf X τ)) (h₂ : y₂ ∈ Formalism.L2.SG.NGPin.StV X u u' γ (vOf X τ))
    (h : Formalism.L2.SG.NGPin.stCoordV X u' w γ (vOf X τ) y₁ = Formalism.L2.SG.NGPin.stCoordV X u' w γ (vOf X τ) y₂) :
    y₁ = y₂ := by
  obtain ⟨ψ, -, hψ⟩ := place_chart C u u' w γ τ hrep
  have hcomp :
      Formalism.L2.SG.NGPin.stCoordV X u' w γ (vOf X τ) =
        (MeasurableEquiv.piCongrLeft (fun _ : Formalism.L2.SG.RealObj.FreeE w => ℂ) (Formalism.L2.SG.RootPatterns.idxF τ w)) ∘
          rootCoords D.R.k D.R.rS (zB X (C.Qi τ) u' τ) (ptLoc D τ w) ∘ Formalism.L2.SG.RealConjugatorData.cMr C γ τ := by
    funext y q
    have ha : q.1.1.1 < D.R.rS := by have := q.2.1; have := q.1.2.isLt; omega
    have hpc : ∀ x : ↥(rootPat (ptLoc D τ w)) → ℂ,
        MeasurableEquiv.piCongrLeft (fun _ : Formalism.L2.SG.RealObj.FreeE w => ℂ) (Formalism.L2.SG.RootPatterns.idxF τ w) x q = x ((Formalism.L2.SG.RootPatterns.idxF τ w).symm q) :=
      fun x => by simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
    simp only [Function.comp_apply]
    rw [hpc, Formalism.L2.SG.RealFrameCoordinates.stCoordV_eq C u' w γ τ y q]
    unfold rootCoords flagMat
    rw [dite_eq_left (show ((Formalism.L2.SG.RootPatterns.idxF τ w).symm q).1.1.val < D.R.rS from ha), ← Formalism.L2.SG.RealConjugatorData.cMr_eq]
    rfl
  rw [hcomp] at h
  have h' := (MeasurableEquiv.piCongrLeft (fun _ : FreeE w => ℂ) (Formalism.L2.SG.RootPatterns.idxF τ w)).injective h
  have m₁ := (Formalism.L2.SG.RealConjugatorData.stV_iff C γ τ u u' y₁).1 h₁
  have m₂ := (Formalism.L2.SG.RealConjugatorData.stV_iff C γ τ u u' y₂).1 h₂
  have e := congrArg ψ h'
  simp only [Function.comp_apply] at e
  rw [hψ (Formalism.L2.SG.RealConjugatorData.cMr C γ τ y₁) m₁, hψ (Formalism.L2.SG.RealConjugatorData.cMr C γ τ y₂) m₂] at e
  exact (Formalism.L2.SG.RealConjugatorData.cMr_closedEmb C γ τ).injective e

theorem stCoordV_surj (hrep : IsPtRep X u u' w γ) (x : FreeE w → ℂ) :
    ∃ y ∈ Formalism.L2.SG.NGPin.StV X u u' γ (vOf X τ), Formalism.L2.SG.NGPin.stCoordV X u' w γ (vOf X τ) y = x := by
  obtain ⟨ψ, hψ, -⟩ := place_chart C u u' w γ τ hrep
  set e := MeasurableEquiv.piCongrLeft (fun _ : FreeE w => ℂ) (Formalism.L2.SG.RootPatterns.idxF τ w)
  obtain ⟨hm, hc⟩ := hψ (e.symm x)
  have hrange (m : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)
      (hm : Matrix.of m ∈ Formalism.MainNotions.S.Rset D.R.k D.R.rS (Formalism.L2.SG.RealFrameCoordinates.g0 C γ τ)) :
      m ∈ Set.range (Formalism.L2.SG.RealConjugatorData.cMr C γ τ) := by
    obtain ⟨hQiQ, hQQi, hH, _⟩ := C.isT τ
    have hmU : (Matrix.of m)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * Matrix.of m = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := hm.1.1
    have hgi0 : (uMat (γ (vOf X τ))⁻¹)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * uMat (γ (vOf X τ))⁻¹ =
        Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := ((γ (vOf X τ))⁻¹).2
    rw [Formalism.L2.SG.RealConjugatorData.uMat_inv'] at hgi0
    set g := uMat (γ (vOf X τ))
    have hg : gᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * g = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := (γ (vOf X τ)).2
    have hgi : (g⁻¹)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * g⁻¹ = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := hgi0
    have hQi : (C.Qi τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * C.Qi τ = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := by
      rw [← hH]
      calc (C.Qi τ)ᴴ * ((C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * C.Q τ) * C.Qi τ
          = (C.Q τ * C.Qi τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Q τ * C.Qi τ) := by
            simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = _ := by rw [hQQi, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
    set M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ := g * C.Q τ * Matrix.of m * C.Qi τ * g⁻¹ with hM
    have hMU : Mᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * M = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := by
      calc Mᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * M
          = (g⁻¹)ᴴ * ((C.Qi τ)ᴴ * ((Matrix.of m)ᴴ * ((C.Q τ)ᴴ *
              (gᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * g) * C.Q τ) * Matrix.of m) * C.Qi τ) * g⁻¹ := by
            rw [hM]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = _ := by rw [hg, hH, hmU, hQi, hgi]
    have h2 : g⁻¹ * g = 1 := Formalism.L2.SG.RealConjugatorData.uMat_inv_mul _
    refine ⟨Formalism.L2.SG.RealConjugatorData.toUJn M hMU, ?_⟩
    show C.Qi τ * g⁻¹ * M * (g * C.Q τ) = Matrix.of m
    rw [hM]
    calc C.Qi τ * g⁻¹ * (g * C.Q τ * Matrix.of m * C.Qi τ * g⁻¹) * (g * C.Q τ)
        = (C.Qi τ * (g⁻¹ * g) * C.Q τ) * Matrix.of m * (C.Qi τ * (g⁻¹ * g) * C.Q τ) := by
          simp only [Matrix.mul_assoc]
      _ = Matrix.of m := by rw [h2, Matrix.mul_one, hQiQ, Matrix.one_mul, Matrix.mul_one]
  obtain ⟨y, hy⟩ := hrange _ hm
  refine ⟨y, (Formalism.L2.SG.RealConjugatorData.stV_iff C γ τ u u' y).2 (by rw [hy]; exact hm), ?_⟩
  have hcomp :
      Formalism.L2.SG.NGPin.stCoordV X u' w γ (vOf X τ) =
        (MeasurableEquiv.piCongrLeft (fun _ : Formalism.L2.SG.RealObj.FreeE w => ℂ) (Formalism.L2.SG.RootPatterns.idxF τ w)) ∘
          rootCoords D.R.k D.R.rS (zB X (C.Qi τ) u' τ) (ptLoc D τ w) ∘ Formalism.L2.SG.RealConjugatorData.cMr C γ τ := by
    funext y q
    have ha : q.1.1.1 < D.R.rS := by have := q.2.1; have := q.1.2.isLt; omega
    have hpc : ∀ x : ↥(rootPat (ptLoc D τ w)) → ℂ,
        MeasurableEquiv.piCongrLeft (fun _ : Formalism.L2.SG.RealObj.FreeE w => ℂ) (Formalism.L2.SG.RootPatterns.idxF τ w) x q = x ((Formalism.L2.SG.RootPatterns.idxF τ w).symm q) :=
      fun x => by simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
    simp only [Function.comp_apply]
    rw [hpc, Formalism.L2.SG.RealFrameCoordinates.stCoordV_eq C u' w γ τ y q]
    unfold rootCoords flagMat
    rw [dite_eq_left (show ((Formalism.L2.SG.RootPatterns.idxF τ w).symm q).1.1.val < D.R.rS from ha), ← Formalism.L2.SG.RealConjugatorData.cMr_eq]
    rfl
  rw [hcomp]
  simp only [Function.comp_apply]
  rw [hy, hc, e.apply_symm_apply]

theorem stCoordV_meas : Measurable (Formalism.L2.SG.NGPin.stCoordV X u' w γ (vOf X τ)) := by
  have hcomp :
      Formalism.L2.SG.NGPin.stCoordV X u' w γ (vOf X τ) =
        (MeasurableEquiv.piCongrLeft (fun _ : Formalism.L2.SG.RealObj.FreeE w => ℂ) (Formalism.L2.SG.RootPatterns.idxF τ w)) ∘
          rootCoords D.R.k D.R.rS (zB X (C.Qi τ) u' τ) (ptLoc D τ w) ∘ Formalism.L2.SG.RealConjugatorData.cMr C γ τ := by
    funext y q
    have ha : q.1.1.1 < D.R.rS := by have := q.2.1; have := q.1.2.isLt; omega
    have hpc : ∀ x : ↥(rootPat (ptLoc D τ w)) → ℂ,
        MeasurableEquiv.piCongrLeft (fun _ : Formalism.L2.SG.RealObj.FreeE w => ℂ) (Formalism.L2.SG.RootPatterns.idxF τ w) x q = x ((Formalism.L2.SG.RootPatterns.idxF τ w).symm q) :=
      fun x => by simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
    simp only [Function.comp_apply]
    rw [hpc, Formalism.L2.SG.RealFrameCoordinates.stCoordV_eq C u' w γ τ y q]
    unfold rootCoords flagMat
    rw [dite_eq_left (show ((Formalism.L2.SG.RootPatterns.idxF τ w).symm q).1.1.val < D.R.rS from ha), ← Formalism.L2.SG.RealConjugatorData.cMr_eq]
    rfl
  rw [hcomp]
  exact (MeasurableEquiv.measurable _).comp ((Formalism.L2.SG.RootPatterns.rootCoords_cont _ _ _ _).measurable.comp
    (Formalism.L2.SG.RealConjugatorData.cMr_measEmb C γ τ).measurable)

end Formalism.L2.S.Pv.Chart

end

