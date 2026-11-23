module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.LocCntUG
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.AlgGUT
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.ThetaGC
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryGramLifts.ScaleB
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.CompOfMemR
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.GSteps
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.HeadMapCj
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.SelfDualLatticesOneOrbit
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.ThetaMbe0GOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.HatZSecondProjTranspose
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.StepSplitHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryGramLifts.SecondProjConjApply
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryGramLifts.StepLiftG
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumA
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.SecondProjConjAlgebra
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryGramLifts.GamConIff
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.AlgGUNS

section

@[expose] public section

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

namespace Formalism.L2.SG.LocalCountModules.AlgGSplit

def AlgGAllNS : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (g : SplitG M.L), M.split = some g →
  ∀ (r : ℕ) (T T' : F), (∃ u v : 𝒪[F], (u : F) * T = 1 ∧ (v : F) * T' = 1) →
    (∃ c : 𝒪[F], T - T' = (g.q : F) ^ 2 * c) →
  ∀ (Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) M.R),
    Z₁.map M.R.subtype = HermSp.ZZplusOf M Zh₁ T T' → Z₂.map M.R.subtype = HermSp.ZZplusOf M Zh₂ T T' →
    IsUnit Zh₁.det → IsUnit Zh₂.det →
    Zh₁.det * (Zh₂.submatrix Fin.castSucc Fin.castSucc).det =
      Zh₂.det * (Zh₁.submatrix Fin.castSucc Fin.castSucc).det →
    IsUnit (Zh₁.det * M.L.cj Zh₁.det - algebraMap F E (T * T') *
      ((Zh₁.submatrix Fin.castSucc Fin.castSucc).det * M.L.cj (Zh₁.submatrix Fin.castSucc Fin.castSucc).det)) →
    IsUnit (Zh₂.det * M.L.cj Zh₂.det - algebraMap F E (T * T') *
      ((Zh₂.submatrix Fin.castSucc Fin.castSucc).det * M.L.cj (Zh₂.submatrix Fin.castSucc Fin.castSucc).det)) →
    T ∈ 𝒪[F] → IsUnit (Z₁.map M.R.subtype).det → IsUnit (Z₂.map M.R.subtype).det →
    IsUnit (HermSp.ZZplusOf M (Zh₁.map M.L.cj) T T').det → IsUnit (HermSp.ZZplusOf M (Zh₂.map M.L.cj) T T').det →
    Nat.card (ThetaGC M.L.O (M.L.cj : E →+* E) (algebraMap F E (g.q : F))
        (algebraMap F E ((g.q : F)⁻¹)) Zh₁ Zh₂ (algebraMap F E T) (algebraMap F E T')) =
      Nat.card (IsoMbe Z₁ Z₂)

theorem algGAllNS_of (h0 : StepSplit) (h1 : FirstIsometryForward) (h2 : FirstIsometryBackward) (h3 : FirstIsometryUniqueness)
    (h4 : StepDu) (h5 : StepDuU) : AlgGAllNS := by
  intro F _ _ _ E _ _ _ _ M g hs r T T' hT hq Zh₁ Zh₂ Z₁ Z₂ e₁ e₂ u₁ u₂ hrel hG₁ hG₂ hT0 hd₁ hd₂ hσ₁ hσ₂
  obtain ⟨c, hc⟩ := hq
  have hT'0 : T' ∈ 𝒪[F] := by
    have : T' = T - (g.q : F) ^ 2 * c := by rw [← hc]; ring
    rw [this]
    exact sub_mem hT0 (mul_mem (pow_mem g.q.2 2) c.2)
  have hq : ∃ c : 𝒪[F], T - T' = (g.q : F) ^ 2 * c := ⟨c, hc⟩
  let TT : M.R := ⟨g.e.symm (T, T'), mem_R_of hs _ ⟨T, hT0⟩ ⟨T', hT'0⟩ (g.q * c) (by simp)
    (by push_cast; rw [hc]; ring)⟩
  have hTT : g.e (TT : E) = (T, T') := by simp [TT]
  let Zs₁ : Matrix (Fin (r + 1)) (Fin (r + 1)) M.R :=
    Matrix.of fun a b => ⟨_, zsig_mem hs T T' c hc Zh₁ Z₁ e₁ a b⟩
  have eZs₁ : Zs₁.map M.R.subtype = HermSp.ZZplusOf M (Zh₁.map M.L.cj) T T' := by ext a b; rfl
  let Zs₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) M.R :=
    Matrix.of fun a b => ⟨_, zsig_mem hs T T' c hc Zh₂ Z₂ e₂ a b⟩
  have eZs₂ : Zs₂.map M.R.subtype = HermSp.ZZplusOf M (Zh₂.map M.L.cj) T T' := by ext a b; rfl
  let Zσ₁ : M.Mat (r + 1) := ⟨Zs₁, by rw [eZs₁]; exact hσ₁⟩
  let Zσ₂ : M.Mat (r + 1) := ⟨Zs₂, by rw [eZs₂]; exact hσ₂⟩
  have eσ₁ : Zσ₁.Z.map M.R.subtype = HermSp.ZZplusOf M (Zh₁.map M.L.cj) T T' := eZs₁
  have eσ₂ : Zσ₂.Z.map M.R.subtype = HermSp.ZZplusOf M (Zh₂.map M.L.cj) T T' := eZs₂
  let Y₁ : M.Mat (r + 1) := ⟨Z₁, hd₁⟩
  let Y₂ : M.Mat (r + 1) := ⟨Z₂, hd₂⟩
  have H₁ : GHyp M g T T' TT Zh₁ Y₁ Zσ₁ := ⟨hT, hq, hTT, e₁, eσ₁, u₁, hG₁⟩
  have H₂ : GHyp M g T T' TT Zh₂ Y₂ Zσ₂ := ⟨hT, hq, hTT, e₂, eσ₂, u₂, hG₂⟩
  have H₁' := gHyp_cj H₁
  have H₂' := gHyp_cj H₂
  have hrel' := kapEq_cj (M := M) hrel
  show _ = Nat.card (IsoMbe Y₁.Z Y₂.Z)
  rw [h0 F E M g hs r T T' TT Zh₁ Zh₂ Y₁ Y₂ Zσ₁ Zσ₂ H₁ H₂ hrel]
  refine Nat.card_congr
    { toFun := fun p => Classical.choose (h1 F E M g hs r T T' TT Zh₁ Zh₂ Y₁ Y₂ Zσ₁ Zσ₂ H₁ H₂ hrel p.1.1
          p.2.1 p.2.2.2.1)
      invFun := fun γ =>
        ⟨(Classical.choose (h2 F E M g hs r T T' TT Zh₁ Zh₂ Y₁ Y₂ Zσ₁ Zσ₂ H₁ H₂ hrel γ),
          Classical.choose (h2 F E M g hs r T T' TT _ _ Zσ₁ Zσ₂ Y₁ Y₂ H₁' H₂' hrel'
            (Classical.choose (h4 F E M g hs r T T' TT Zh₁ Zh₂ Y₁ Y₂ Zσ₁ Zσ₂ H₁ H₂ hrel γ)))), by
          have s1 := Classical.choose_spec (h2 F E M g hs r T T' TT Zh₁ Zh₂ Y₁ Y₂ Zσ₁ Zσ₂ H₁ H₂ hrel γ)
          have s4 := Classical.choose_spec (h4 F E M g hs r T T' TT Zh₁ Zh₂ Y₁ Y₂ Zσ₁ Zσ₂ H₁ H₂ hrel γ)
          have s2 := Classical.choose_spec (h2 F E M g hs r T T' TT _ _ Zσ₁ Zσ₂ Y₁ Y₂ H₁' H₂' hrel'
            (Classical.choose (h4 F E M g hs r T T' TT Zh₁ Zh₂ Y₁ Y₂ Zσ₁ Zσ₂ H₁ H₂ hrel γ)))
          exact ⟨s1.1, s2.1, s1.2.1, s2.2.1, s4 _ _ s1.2.2 s2.2.2⟩⟩
      left_inv := fun p => by
        have sf := Classical.choose_spec (h1 F E M g hs r T T' TT Zh₁ Zh₂ Y₁ Y₂ Zσ₁ Zσ₂ H₁ H₂ hrel p.1.1
          p.2.1 p.2.2.2.1)
        set γ := Classical.choose (h1 F E M g hs r T T' TT Zh₁ Zh₂ Y₁ Y₂ Zσ₁ Zσ₂ H₁ H₂ hrel p.1.1
          p.2.1 p.2.2.2.1)
        have s1 := Classical.choose_spec (h2 F E M g hs r T T' TT Zh₁ Zh₂ Y₁ Y₂ Zσ₁ Zσ₂ H₁ H₂ hrel γ)
        have s4 := Classical.choose_spec (h4 F E M g hs r T T' TT Zh₁ Zh₂ Y₁ Y₂ Zσ₁ Zσ₂ H₁ H₂ hrel γ)
        have s2 := Classical.choose_spec (h2 F E M g hs r T T' TT _ _ Zσ₁ Zσ₂ Y₁ Y₂ H₁' H₂' hrel'
            (Classical.choose (h4 F E M g hs r T T' TT Zh₁ Zh₂ Y₁ Y₂ Zσ₁ Zσ₂ H₁ H₂ hrel γ)))
        have e1 := ind_det hs γ _ _ s1.2.2 sf
        apply Subtype.ext
        refine Prod.ext e1 ?_
        refine h5 F E M g hs r T T' TT Zh₁ Zh₂ Y₁ Y₂ Zσ₁ Zσ₂ H₁ H₂ hrel p.1.1 _ _ ?_ p.2.2.2.2.2
        rw [← e1]
        exact s4 _ _ s1.2.2 s2.2.2
      right_inv := fun γ => by
        have s1 := Classical.choose_spec (h2 F E M g hs r T T' TT Zh₁ Zh₂ Y₁ Y₂ Zσ₁ Zσ₂ H₁ H₂ hrel γ)
        refine h3 F E M g hs r T T' TT Zh₁ Zh₂ Y₁ Y₂ Zσ₁ Zσ₂ H₁ H₂ hrel _ _ _
          (Classical.choose_spec (h1 F E M g hs r T T' TT Zh₁ Zh₂ Y₁ Y₂ Zσ₁ Zσ₂ H₁ H₂ hrel _ s1.1 s1.2.1))
          s1.2.2 }

theorem algGAllNS_holds : AlgGAllNS :=
  algGAllNS_of stepSplit_holds firstIso_forward_holds firstIso_backward_holds firstIso_uniqueness_holds (stepDu_of_lift stepLiftG) stepDuU

end Formalism.L2.SG.LocalCountModules.AlgGSplit
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryGramLifts.CardThetaGCScale

section

@[expose] public section

noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

section ScaleA7

variable {E : Type} [CommRing E] {O : Subring E} {cj : E →+* E} {qi : E} {r : ℕ} {T T' α : E} (q : E)

theorem gamTup_scale (h : ScHyp O cj qi T T' α) (hq : q * qi = 1) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (Y Y' Y'' : Ix r → O) :
    ((Submodule.Quotient.mk (scPhi h Y) : DDg O cj qi (Zh * dlast r α) T T'),
      (Submodule.Quotient.mk (scPhi h Y'') : DDg O cj qi (Zh * dlast r α) T T'),
      (((scPhi h Y (Sum.inl (Fin.last r)) : O) : E),
        lamStarC cj (Zh * dlast r α) (fun b => ((scPhi h Y (Sum.inl b) : O) : E) + q * (scPhi h Y (Sum.inr b) : O))),
      (lamC (Zh * dlast r α) (fun a => ((scPhi h Y' (Sum.inl a) : O) : E)),
        ((scPhi h Y' (Sum.inl (Fin.last r)) : O) : E) + q * (scPhi h Y' (Sum.inr (Fin.last r)) : O))) =
    scTr h Zh ((Submodule.Quotient.mk Y : DDg O cj qi Zh T T'), (Submodule.Quotient.mk Y'' : DDg O cj qi Zh T T'),
      ((Y (Sum.inl (Fin.last r)) : E), lamStarC cj Zh (fun b => (Y (Sum.inl b) : E) + q * Y (Sum.inr b))),
      (lamC Zh (fun a => (Y' (Sum.inl a) : E)), (Y' (Sum.inl (Fin.last r)) : E) + q * Y' (Sum.inr (Fin.last r)))) := by
  have hc : (fun b => ((scPhi h Y (Sum.inl b) : O) : E) + q * (scPhi h Y (Sum.inr b) : O)) =
      fun b => cj (if b = Fin.last r then α else 1) * ((Y (Sum.inl b) : E) + q * Y (Sum.inr b)) :=
    funext (phi_comb h q hq Y)
  have hl : (fun a => ((scPhi h Y' (Sum.inl a) : O) : E)) = fun a => (Y' (Sum.inl a) : E) := funext (phi_inl h Y')
  have hz := phi_comb h q hq Y' (Fin.last r)
  simp only [if_true] at hz
  simp only [scTr, scBar_mk, psiD, Prod.mk.injEq]
  refine ⟨trivial, trivial, ⟨phi_inl h Y _, ?_⟩, ?_, hz⟩
  · rw [hc, lamStarC_scale h Zh]
  · rw [hl, lamC_scale h Zh]

theorem gamRC_scale (h : ScHyp O cj qi T T' α) (hq : q * qi = 1) (hqO : q ∈ O)
    (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    GamRC O cj q qi (Zh * dlast r α) T T' = scTr h Zh '' GamRC O cj q qi Zh T T' := by
  ext p
  constructor
  · rintro ⟨Y, Y', Y'', c1, c2, c3, rfl⟩
    have hc := (gamCon_iff q h hqO ((scPhi h).symm Y) ((scPhi h).symm Y') ((scPhi h).symm Y'')).2
    simp only [LinearEquiv.apply_symm_apply] at hc
    obtain ⟨d1, d2, d3⟩ := hc ⟨c1, c2, c3⟩
    refine ⟨_, ⟨(scPhi h).symm Y, (scPhi h).symm Y', (scPhi h).symm Y'', d1, d2, d3, rfl⟩, ?_⟩
    rw [← gamTup_scale q h hq]
    simp only [LinearEquiv.apply_symm_apply]
  · rintro ⟨_, ⟨Y, Y', Y'', c1, c2, c3, rfl⟩, rfl⟩
    obtain ⟨d1, d2, d3⟩ := (gamCon_iff q h hqO Y Y' Y'').1 ⟨c1, c2, c3⟩
    exact ⟨scPhi h Y, scPhi h Y', scPhi h Y'', d1, d2, d3, (gamTup_scale q h hq Zh Y Y' Y'').symm⟩

theorem scBar_symm_mk (h : ScHyp O cj qi T T' α) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (Y : Ix r → O) :
    (scBar h Zh).symm (Submodule.Quotient.mk Y) = Submodule.Quotient.mk ((scPhi h).symm Y) := by
  rw [LinearEquiv.symm_apply_eq, scBar_mk, LinearEquiv.apply_symm_apply]

def scConj (h : ScHyp O cj qi T T' α) (Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    (DDg O cj qi Zh₁ T T' ≃ₗ[O] DDg O cj qi Zh₂ T T') ≃
      (DDg O cj qi (Zh₁ * dlast r α) T T' ≃ₗ[O] DDg O cj qi (Zh₂ * dlast r α) T T') where
  toFun θ := (scBar h Zh₁).symm.trans (θ.trans (scBar h Zh₂))
  invFun θ' := (scBar h Zh₁).trans (θ'.trans (scBar h Zh₂).symm)
  left_inv θ := by ext x; simp
  right_inv θ' := by ext x; simp

theorem thetaGC_scale_iff (h : ScHyp O cj qi T T' α) (hq : q * qi = 1) (hqO : q ∈ O)
    (Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (θ : DDg O cj qi Zh₁ T T' ≃ₗ[O] DDg O cj qi Zh₂ T T') :
    θ ∈ ThetaGC O cj q qi Zh₁ Zh₂ T T' ↔
      scConj h Zh₁ Zh₂ θ ∈ ThetaGC O cj q qi (Zh₁ * dlast r α) (Zh₂ * dlast r α) T T' := by
  have hθ' : ∀ Y : Ix r → O, scConj h Zh₁ Zh₂ θ (Submodule.Quotient.mk (scPhi h Y)) =
      scBar h Zh₂ (θ (Submodule.Quotient.mk Y)) := by
    intro Y
    show scBar h Zh₂ (θ ((scBar h Zh₁).symm (Submodule.Quotient.mk (scPhi h Y)))) = _
    rw [scBar_symm_mk, LinearEquiv.symm_apply_apply]
  have hcomm : (fun p => (scConj h Zh₁ Zh₂ θ p.1, scConj h Zh₁ Zh₂ θ p.2.1, p.2.2.1, p.2.2.2)) ∘ scTr h Zh₁ =
      scTr h Zh₂ ∘ (fun p => (θ p.1, θ p.2.1, p.2.2.1, p.2.2.2)) := by
    funext p
    simp only [Function.comp_apply, scTr]
    show (scBar h Zh₂ (θ ((scBar h Zh₁).symm (scBar h Zh₁ p.1))),
      scBar h Zh₂ (θ ((scBar h Zh₁).symm (scBar h Zh₁ p.2.1))), _) = _
    simp only [LinearEquiv.symm_apply_apply]
  unfold ThetaGC
  simp only [Set.mem_setOf_eq]
  rw [gamRC_scale q h hq hqO Zh₁, gamRC_scale q h hq hqO Zh₂, Set.image_image]
  rw [show (fun p => (scConj h Zh₁ Zh₂ θ (scTr h Zh₁ p).1, scConj h Zh₁ Zh₂ θ (scTr h Zh₁ p).2.1,
      (scTr h Zh₁ p).2.2.1, (scTr h Zh₁ p).2.2.2)) = scTr h Zh₂ ∘ (fun p => (θ p.1, θ p.2.1, p.2.2.1, p.2.2.2)) from
      hcomm, Set.image_comp, (Set.image_injective.2 (scTr_inj h Zh₂)).eq_iff]
  refine and_congr ?_ Iff.rfl
  constructor
  · intro hF Y W Y₂ W₂ hY hW
    have eY : θ (Submodule.Quotient.mk ((scPhi h).symm Y)) = Submodule.Quotient.mk ((scPhi h).symm Y₂) := by
      rw [← scBar_symm_mk h Zh₁, ← scBar_symm_mk h Zh₂, LinearEquiv.eq_symm_apply]; exact hY
    have eW : θ (Submodule.Quotient.mk ((scPhi h).symm W)) = Submodule.Quotient.mk ((scPhi h).symm W₂) := by
      rw [← scBar_symm_mk h Zh₁, ← scBar_symm_mk h Zh₂, LinearEquiv.eq_symm_apply]; exact hW
    have := hF _ _ _ _ eY eW
    rw [← formG_scale h Zh₂, ← formG_scale h Zh₁] at this
    simpa only [LinearEquiv.apply_symm_apply] using this
  · intro hF Y W Y₂ W₂ hY hW
    have eY : scConj h Zh₁ Zh₂ θ (Submodule.Quotient.mk (scPhi h Y)) = Submodule.Quotient.mk (scPhi h Y₂) := by
      rw [hθ', hY, scBar_mk]
    have eW : scConj h Zh₁ Zh₂ θ (Submodule.Quotient.mk (scPhi h W)) = Submodule.Quotient.mk (scPhi h W₂) := by
      rw [hθ', hW, scBar_mk]
    have := hF _ _ _ _ eY eW
    rwa [formG_scale h Zh₂, formG_scale h Zh₁] at this

theorem card_thetaGC_scale (h : ScHyp O cj qi T T' α) (hq : q * qi = 1) (hqO : q ∈ O)
    (Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    Nat.card (ThetaGC O cj q qi (Zh₁ * dlast r α) (Zh₂ * dlast r α) T T') = Nat.card (ThetaGC O cj q qi Zh₁ Zh₂ T T') :=
  (Nat.card_congr ((scConj h Zh₁ Zh₂).subtypeEquiv (thetaGC_scale_iff q h hq hqO Zh₁ Zh₂))).symm

end ScaleA7

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryGramLifts.ScaleFinal

section

@[expose] public section

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

def AlgGAllT : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (g : SplitG M.L), M.split = some g →
  ∀ (r : ℕ) (T T' : F), (∃ u v : 𝒪[F], (u : F) * T = 1 ∧ (v : F) * T' = 1) →
    (∃ c : 𝒪[F], T - T' = (g.q : F) ^ 2 * c) →
  ∀ (Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) M.R),
    Z₁.map M.R.subtype = HermSp.ZZplusOf M Zh₁ T T' → Z₂.map M.R.subtype = HermSp.ZZplusOf M Zh₂ T T' →
    IsUnit Zh₁.det → IsUnit Zh₂.det →
    Zh₁.det * (Zh₂.submatrix Fin.castSucc Fin.castSucc).det =
      Zh₂.det * (Zh₁.submatrix Fin.castSucc Fin.castSucc).det →
    IsUnit (Zh₁.det * M.L.cj Zh₁.det - algebraMap F E (T * T') *
      ((Zh₁.submatrix Fin.castSucc Fin.castSucc).det * M.L.cj (Zh₁.submatrix Fin.castSucc Fin.castSucc).det)) →
    IsUnit (Zh₂.det * M.L.cj Zh₂.det - algebraMap F E (T * T') *
      ((Zh₂.submatrix Fin.castSucc Fin.castSucc).det * M.L.cj (Zh₂.submatrix Fin.castSucc Fin.castSucc).det)) →
    T ∈ 𝒪[F] →
    Nat.card (ThetaGC M.L.O (M.L.cj : E →+* E) (algebraMap F E (g.q : F))
        (algebraMap F E ((g.q : F)⁻¹)) Zh₁ Zh₂ (algebraMap F E T) (algebraMap F E T')) =
      Nat.card (IsoMbe Z₁ Z₂)

section Fin

variable {E : Type} [CommRing E] {r : ℕ}

theorem det_dlast (α : E) : (dlast r α).det = α := by
  rw [dlast, Matrix.det_diagonal, Finset.prod_eq_single (Fin.last r)]
  · simp
  · intro b _ hb; simp [hb]
  · simp

theorem head_dlast (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (α : E) :
    (Zh * dlast r α).submatrix Fin.castSucc Fin.castSucc = Zh.submatrix Fin.castSucc Fin.castSucc := by
  ext a b
  simp [dlast, Matrix.mul_diagonal, Fin.castSucc_ne_last]

end Fin

theorem algGAllT_holds : AlgGAllT := by
  intro F _ _ _ E _ _ _ _ M g hs r T T' hT hq Zh₁ Zh₂ Z₁ Z₂ e₁ e₂ u₁ u₂ hrel hG₁ hG₂ hT0
  obtain ⟨α, hα, hαO, hβO, Z₁', Z₂', e₁', e₂', d₁, d₂, s₁, s₂, hcard⟩ :=
    Formalism.L2.SG.LocalCountModules.AlgGSplit.scaleChoice_holds F E M g hs r T T' hT hq hT0 Zh₁ Zh₂ Z₁ Z₂ e₁ e₂ u₁ u₂ hrel
  have hαu : IsUnit α := ⟨⟨α, M.L.cj α, hα, by rw [mul_comm]; exact hα⟩, rfl⟩
  have hcj : ∀ x : E, (M.L.cj : E →+* E) ((M.L.cj : E →+* E) x) = x := M.L.cj_cj
  have hH : ScHyp M.L.O (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) (algebraMap F E T) (algebraMap F E T') α :=
    { cjcj := hcj
      cjO := fun x hx => cj_mem_O M.L hx
      qic := AlgEquiv.commutes _ _
      Tc := AlgEquiv.commutes _ _
      T'c := AlgEquiv.commutes _ _
      αO := hαO
      αn := hα
      βO := hβO }
  have hqq : algebraMap F E (g.q : F) * algebraMap F E ((g.q : F)⁻¹) = 1 := by
    rw [← map_mul, mul_inv_cancel₀ (q_ne g), map_one]
  have hqO : algebraMap F E (g.q : F) ∈ M.L.O :=
    mem_O_of_comp g _ (by rw [AlgEquiv.commutes]; exact g.q.2) (by rw [AlgEquiv.commutes]; exact g.q.2)
  have hdet : ∀ Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E, (Zh * dlast r α).det = Zh.det * α := fun Zh => by
    rw [Matrix.det_mul, det_dlast]
  have hN : ∀ Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E,
      (Zh * dlast r α).det * M.L.cj (Zh * dlast r α).det = Zh.det * M.L.cj Zh.det := fun Zh => by
    rw [hdet, map_mul]; linear_combination (Zh.det * M.L.cj Zh.det) * hα
  have key := Formalism.L2.SG.LocalCountModules.AlgGSplit.algGAllNS_holds F E M g hs r T T' hT hq (Zh₁ * dlast r α) (Zh₂ * dlast r α) Z₁' Z₂'
    e₁' e₂' (by rw [hdet]; exact u₁.mul hαu) (by rw [hdet]; exact u₂.mul hαu)
    (by rw [hdet, hdet, head_dlast, head_dlast]; linear_combination α * hrel)
    (by rw [hN, head_dlast]; exact hG₁) (by rw [hN, head_dlast]; exact hG₂) hT0 d₁ d₂ s₁ s₂
  rw [card_thetaGC_scale _ hH hqq hqO, hcard] at key
  exact key

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.LocCntUGHolds

section

@[expose] public section

namespace Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG

theorem algGUT_holds : AlgGUT := by
  intro F _ _ _ E _ _ _ _ M g hg r T T' hT hq Zh₁ Zh₂ Z₁ Z₂ e₁ e₂ u₁ u₂ _ _ hrel hG₁ hG₂ hT0
  exact Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork.algGAllT_holds F E M g hg r T T' hT hq Zh₁ Zh₂ Z₁ Z₂ e₁ e₂ u₁ u₂ hrel hG₁ hG₂ hT0

theorem locCntUG_holds : Formalism.L2.SG.LocalCountModules.LocCntUG.LocCntUG := locCntUG_of_algGUT algGUT_holds

end Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.LocalCountConclusions.LocCntUG

section

@[expose] public section

namespace Formalism.L2.SG.LocalCountModules

theorem localCountUnitGlobal_holds : Formalism.L2.SG.LocalCountModules.LocCntUG.LocCntUG := Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG.locCntUG_holds

end Formalism.L2.SG.LocalCountModules
end
end
