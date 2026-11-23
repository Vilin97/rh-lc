module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomTripleBasisChangeFactorMemFieldStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomTripleWeilMoveRightTranslateStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSupportedUnitariesMovingBottomTriples
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdLatEq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulCutSubOneEntry
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHomLatticeIffFrameStabilizerActMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchrodingerIntertwinerSchwartzBruhatIsTheta
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionSchrodingerModelFiniteIdempotent
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHomLatticeIffFrameStabilizerActMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchrodingerIntertwinerSchwartzBruhatIsTheta
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSupportedUnitariesMovingBottomTriplesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_supported_unitaries_moving_bottomTriples : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (i j : Fin D.R.m)
    (A A' WW : HSp D) (X Y : Tri T A A' WW), IsBottomTri W i j X → IsBottomTri W i j Y → ∀ t : T,
    ∃ (g : GA D A) (g' : GA D A') (h : GA D WW) (x x' y : (AE D)ˣ),
      (Formalism.L2.Theta.SuppAt (Y.e t) A g ∧ Formalism.IndefR.Lev.finE A g ∈ Formalism.L2.DIV.St Y.rA.β ∧
        Formalism.L2.Theta.IsDetAt (Y.e t) A g x) ∧
      (Formalism.L2.Theta.SuppAt (Y.e t) A' g' ∧ Formalism.IndefR.Lev.finE A' g' ∈ Formalism.L2.DIV.St Y.rA'.β ∧
        Formalism.L2.Theta.IsDetAt (Y.e t) A' g' x') ∧
      (Formalism.L2.Theta.SuppAt (Y.e t) WW h ∧ Formalism.IndefR.Lev.finE WW h ∈ Formalism.L2.DIV.St Y.rW.β ∧
        Formalism.L2.Theta.IsDetAt (Y.e t) WW h y) ∧
      (∀ u : WO A WW, IsHalf (Y.e t) u → frMapO A WW Y.rA.β Y.rW.β (actO A WW g h u) = frMapO A WW X.rA.β X.rW.β u) ∧
      ∀ u : WO A' WW, IsHalf (cA D (Y.e t)) u →
        frMapAdj A' WW Y.rA'.β Y.rW.β (actO A' WW g' h u) = frMapAdj A' WW X.rA'.β X.rW.β u := by
  first | exact @GlobalTheory.BotUnitMove.move_elts | exact GlobalTheory.BotUnitMove.move_elts | (intros; apply GlobalTheory.BotUnitMove.move_elts <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardPairFirstMemberMovedDatumSplittingScale

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotFrames

theorem stdFst_actO {D : D7} {A WW : HSp D} (ν : (AE D)ˣ →* Circle) (e : AE D) (I : Ideal (𝓞 D.host.E))
    (βA βA' : GL (Fin A.rank) (Lev.EAf D)) (βW βW' : GL (Fin WW.rank) (Lev.EAf D)) (g : GA D A) (h : GA D WW)
    (hfr : ∀ u : WO A WW, IsHalf e u → frMapO A WW βA' βW' (actO A WW g h u) = frMapO A WW βA βW u) (u : WO A WW) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst ν e I A WW βA' βW' (actO A WW g h u) = GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst ν e I A WW βA βW u := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst
  by_cases hu : IsHalf e u
  · rw [hfr u hu]
    have hu' : IsHalf e (actO A WW g h u) := (GlobalTheory.SchrMove.isHalf_actO_iff g h u).2 hu
    by_cases hr : IsIntM (frMapO A WW βA βW u) ∧
        ∀ i j, A.rank ≤ i.1 → GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (frMapO A WW βA βW u i j)
    · rw [if_pos ⟨hu', hr⟩, if_pos ⟨hu, hr⟩]
    · rw [if_neg fun hh => hr hh.2, if_neg fun hh => hr hh.2]
  · rw [if_neg fun hh => hu ((GlobalTheory.SchrMove.isHalf_actO_iff g h u).1 hh.1), if_neg fun hh => hu hh.1]

theorem move_fst : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (i j : Fin D.R.m)
    (A A' WW : HSp D) (X Y : Tri T A A' WW), IsBottomTri W i j X → IsBottomTri W i j Y → ∀ (t : T) (g : GA D A) (h : GA D WW) (x y : (AE D)ˣ),
    Formalism.L2.Theta.SuppAt (Y.e t) A g → Formalism.IndefR.Lev.finE A g ∈ Formalism.L2.DIV.St Y.rA.β → Formalism.L2.Theta.IsDetAt (Y.e t) A g x →
    Formalism.L2.Theta.SuppAt (Y.e t) WW h → Formalism.IndefR.Lev.finE WW h ∈ Formalism.L2.DIV.St Y.rW.β → Formalism.L2.Theta.IsDetAt (Y.e t) WW h y →
    (∀ u : WO A WW, IsHalf (Y.e t) u → frMapO A WW Y.rA.β Y.rW.β (actO A WW g h u) = frMapO A WW X.rA.β X.rW.β u) →
    IsThetaAt W.ψ (symplO (GlobalTheory.Grid.neg A) WW) (heisO W.ψ (GlobalTheory.Grid.neg A) WW) (Y.e t)
      (latO (GlobalTheory.Grid.neg A) WW X.rA.Λ X.rW.Λ fun _ => True) 1 Y.vac
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j) (Y.e t) (Y.ideal (locPl G) t) A WW
        X.rA.β X.rW.β)
      (((splitFacO (GlobalTheory.BotFrames.botBeta G i j) (GlobalTheory.BotFrames.botBeta G i j / GlobalTheory.BotFrames.botAlpha L i j t) x y : Circle) : ℂ) •
        Y.ω t (g⁻¹, h⁻¹) (Y.f t)) := by
  intro D T L sc G W i j A A' WW X Y hX hY t g h x y hsg hstg hdg hsh hsth hdh hfr
  classical
  have hI := hY.is
  have hW : IsWeilDatumO W.ψ (GlobalTheory.Grid.neg A) WW (GlobalTheory.BotFrames.botBeta G i j)
      (GlobalTheory.BotFrames.botBeta G i j / GlobalTheory.BotFrames.botAlpha L i j t) ((Y.ω t).toSgn true) := hI.weil t
  have hSA : IsSelfDualC (GlobalTheory.Grid.neg A) Y.rA.Λ := GlobalTheory.RowTest.isSelfDualC_neg' hI.rigA.1
  have hSW : IsSelfDualC WW Y.rW.Λ := hI.rigW.1
  let g' : GA D (GlobalTheory.Grid.neg A) := (GlobalTheory.Grid.ofSgn true A).symm g
  have hL : ∀ u, u ∈ (latO (GlobalTheory.Grid.neg A) WW (Y.rA.Λ : Set (Fin A.rank → D.host.E)) (Y.rW.Λ : Set (Fin WW.rank → D.host.E)) fun _ => True) ↔
      actO (GlobalTheory.Grid.neg A) WW g' h u ∈ (latO (GlobalTheory.Grid.neg A) WW (Y.rA.Λ : Set (Fin A.rank → D.host.E)) (Y.rW.Λ : Set (Fin WW.rank → D.host.E)) fun _ => True) :=
    GlobalTheory.StabLatInv.mem_latO_iff_actO_mem D (GlobalTheory.Grid.neg A) WW Y.rA.Λ Y.rW.Λ Y.rA.β Y.rW.β hSA hSW hI.rigA.2.1 hI.rigW.2.1
      g' h hstg hsth
  have hvθ := hI.isVac.2.theta
  have hvL := hI.isVac.2.lat
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum (hI.idem t)
  have hec := (hI.idem t).2
  have h0 : (Y.ω t).toSgn true (g', h) Y.vac =
      ((splitFacO (GlobalTheory.BotFrames.botBeta G i j) (GlobalTheory.BotFrames.botBeta G i j / GlobalTheory.BotFrames.botAlpha L i j t) x y : Circle) : ℂ) • Y.vac := by
    obtain ⟨ι, P, es, h1, h2, he⟩ := ho
    rw [he] at hec hsg hsh hdg hdh
    have h3 : ∀ a ∈ P, ∀ b ∈ P, es a * cA D (es b) = 0 := fun a ha b hb => by
      rw [← GlobalTheory.PlaceModelSum.mul_sum_orth h1 h2 ha, ← GlobalTheory.PlaceModelSum.mul_sum_orth h1 h2 hb, RingHom.map_mul,
        mul_mul_mul_comm, hec, mul_zero]
    exact GlobalTheory.WeilSplit.om_latVac_sum hW hSA hSW hvθ hvL es P h1 h2 h3 g' h hsg hsh hL x y hdg hdh
  rw [← isStd_lat_eq hY.std hX.std, ← isStd_lat_eq hY.stdW hX.stdW]
  obtain ⟨⟨T₀, hT₀⟩, hall⟩ := hI.fst t
  refine ⟨⟨T₀, hT₀⟩, fun T' hT' => ?_⟩
  have hth := GlobalTheory.SchrTheta.isTheta_placeModel D W.ψ hW.std (GlobalTheory.Grid.neg A) WW Y.rA.Λ Y.rW.Λ hSA hSW (Y.e t) ho.idem
    ho.infPart_eq Y.vac hvθ T' hT'
  have hc : ((splitFacO (GlobalTheory.BotFrames.botBeta G i j) (GlobalTheory.BotFrames.botBeta G i j / GlobalTheory.BotFrames.botAlpha L i j t) x y : Circle) : ℂ) ≠ 0 :=
    Circle.coe_ne_zero _
  have pm := GlobalTheory.SchrMove.isPlaceModel_move hW hL hT' hth hc h0
  have hf := hall _ pm
  have hΦ : (fun u => GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j) (Y.e t)
      (Y.ideal (locPl G) t) A WW Y.rA.β Y.rW.β (actO (GlobalTheory.Grid.neg A) WW g' h u)) =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j) (Y.e t)
      (Y.ideal (locPl G) t) A WW X.rA.β X.rW.β :=
    funext fun u => stdFst_actO _ _ _ X.rA.β Y.rA.β X.rW.β Y.rW.β g h hfr u
  have e1 : Y.ω t (g⁻¹, h⁻¹) = (Y.ω t).toSgn true (g'⁻¹, h⁻¹) := rfl
  have hf' : Y.f t = ((splitFacO (GlobalTheory.BotFrames.botBeta G i j) (GlobalTheory.BotFrames.botBeta G i j / GlobalTheory.BotFrames.botAlpha L i j t) x y : Circle) : ℂ)⁻¹ •
      (Y.ω t).toSgn true (g', h) (T' (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j) (Y.e t)
      (Y.ideal (locPl G) t) A WW X.rA.β X.rW.β)) := by
    rw [hf, ← hΦ]; rfl
  rw [e1, hf', map_smul, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel,
    Prod.mk_one_one, map_one, Module.End.one_apply, smul_smul, mul_inv_cancel₀ hc, one_smul]

end GlobalTheory.BotFrames

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardPairFirstMemberMovedDatumSplittingScaleStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.standardPairFirstMember_movedDatum_splittingScale : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (i j : Fin D.R.m)
    (A A' WW : HSp D) (X Y : Tri T A A' WW), IsBottomTri W i j X → IsBottomTri W i j Y → ∀ (t : T) (g : GA D A) (h : GA D WW) (x y : (AE D)ˣ),
    Formalism.L2.Theta.SuppAt (Y.e t) A g → Formalism.IndefR.Lev.finE A g ∈ Formalism.L2.DIV.St Y.rA.β → Formalism.L2.Theta.IsDetAt (Y.e t) A g x →
    Formalism.L2.Theta.SuppAt (Y.e t) WW h → Formalism.IndefR.Lev.finE WW h ∈ Formalism.L2.DIV.St Y.rW.β → Formalism.L2.Theta.IsDetAt (Y.e t) WW h y →
    (∀ u : WO A WW, IsHalf (Y.e t) u → frMapO A WW Y.rA.β Y.rW.β (actO A WW g h u) = frMapO A WW X.rA.β X.rW.β u) →
    IsThetaAt W.ψ (symplO (GlobalTheory.Grid.neg A) WW) (heisO W.ψ (GlobalTheory.Grid.neg A) WW) (Y.e t)
      (latO (GlobalTheory.Grid.neg A) WW X.rA.Λ X.rW.Λ fun _ => True) 1 Y.vac
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j) (Y.e t) (Y.ideal (locPl G) t) A WW
        X.rA.β X.rW.β)
      (((splitFacO (GlobalTheory.BotFrames.botBeta G i j) (GlobalTheory.BotFrames.botBeta G i j / GlobalTheory.BotFrames.botAlpha L i j t) x y : Circle) : ℂ) •
        Y.ω t (g⁻¹, h⁻¹) (Y.f t)) := by
  first | exact @GlobalTheory.BotFrames.move_fst | exact GlobalTheory.BotFrames.move_fst | (intros; apply GlobalTheory.BotFrames.move_fst <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardPairSecondEqMovedBottomDatum

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BotFrames

theorem isThetaAt_stdSnd_move : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (i j : Fin D.R.m)
    (A A' WW : HSp D) (X Y : Tri T A A' WW), IsBottomTri W i j X → IsBottomTri W i j Y → ∀ (t : T) (g' : GA D A') (h : GA D WW) (x' y : (AE D)ˣ),
    Formalism.L2.Theta.SuppAt (Y.e t) A' g' → Formalism.IndefR.Lev.finE A' g' ∈ Formalism.L2.DIV.St Y.rA'.β →
    Formalism.L2.Theta.IsDetAt (Y.e t) A' g' x' →
    Formalism.L2.Theta.SuppAt (Y.e t) WW h → Formalism.IndefR.Lev.finE WW h ∈ Formalism.L2.DIV.St Y.rW.β → Formalism.L2.Theta.IsDetAt (Y.e t) WW h y →
    (∀ u : WO A' WW, IsHalf (cA D (Y.e t)) u →
      frMapAdj A' WW Y.rA'.β Y.rW.β (actO A' WW g' h u) = frMapAdj A' WW X.rA'.β X.rW.β u) →
    IsThetaAt W.ψ (symplO A' WW) (heisO W.ψ A' WW) (cA D (Y.e t))
      (latO A' WW X.rA'.Λ X.rW.Λ fun _ => True) 1 Y.vac'
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j) (Y.e t) (Y.ideal (locPl G) t)
        A.rank A' WW X.rA'.β X.rW.β)
      (((splitFacO (GlobalTheory.BotFrames.botAlpha L i j t) (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j) x' y : Circle)
        : ℂ) • Y.ω' t (g'⁻¹, h⁻¹) (Y.f' t)) := by
  intro D T L sc G W i j A A' WW X Y hX hY t g' h x' y hS1 hSt1 hD1 hS2 hSt2 hD2 hfr
  have hi := hY.is
  have hW : IsWeilDatumO W.ψ A' WW (botAlpha L i j t) (botAlpha L i j t / botBeta G i j) (Y.ω' t) :=
    (GlobalTheory.Grid.isWeil_false _ _ _ _ _ _).1 (hi.weil' t)
  have hSA : IsSelfDualC A' Y.rA'.Λ := hi.rigA'.1
  have hSW : IsSelfDualC WW Y.rW.Λ := hi.rigW.1
  have hFA : Formalism.L2.DIV.IsFrame Y.rA'.β Y.rA'.Λ := hi.rigA'.2.1
  have hFW : Formalism.L2.DIV.IsFrame Y.rW.β Y.rW.Λ := hi.rigW.2.1
  have eA : X.rA'.Λ = Y.rA'.Λ := isStd_lat_eq hX.std' hY.std'
  have eW : X.rW.Λ = Y.rW.Λ := isStd_lat_eq hX.stdW hY.stdW
  rw [eA, eW]
  have hL := GlobalTheory.StabLatInv.mem_latO_iff_actO_mem D A' WW Y.rA'.Λ Y.rW.Λ Y.rA'.β Y.rW.β hSA hSW hFA hFW g' h hSt1 hSt2
  have hvac := hi.isVac'
  have hIS := hi.idem t
  obtain ⟨ι, P, es, hsp, horth, hsum⟩ := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum hIS
  have hc0 : Y.e t * cA D (Y.e t) = 0 := hIS.2
  have hes : ∀ k ∈ P, es k * Y.e t = es k := by
    intro k hk
    rw [hsum, Finset.mul_sum, Finset.sum_eq_single_of_mem k hk (fun b hb hne => horth k hk b hb hne)]
    exact (hsp k hk).1
  have hecs : ∀ a ∈ P, ∀ b ∈ P, es a * cA D (es b) = 0 := by
    intro a ha b hb
    have h2 : cA D (es b) * cA D (Y.e t) = cA D (es b) := by rw [← map_mul, hes b hb]
    rw [← hes a ha, ← h2]
    calc es a * Y.e t * (cA D (es b) * cA D (Y.e t)) = es a * cA D (es b) * (Y.e t * cA D (Y.e t)) := by ring
      _ = 0 := by rw [hc0, mul_zero]
  have h0 : Y.ω' t (g', h) Y.vac' =
      ((splitFacO (botAlpha L i j t) (botAlpha L i j t / botBeta G i j) x' y : Circle) : ℂ) • Y.vac' := by
    rw [hsum] at hS1 hS2 hD1 hD2
    exact GlobalTheory.WeilSplit.om_latVac_sum hW hSA hSW hvac.2.theta hvac.2.lat es P hsp horth hecs g' h hS1 hS2 hL x' y hD1 hD2
  have hos := (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum hIS).conj
  have hc : ((splitFacO (botAlpha L i j t) (botAlpha L i j t / botBeta G i j) x' y : Circle) : ℂ) ≠ 0 :=
    Circle.coe_ne_zero _
  have hΦ : (LinearMap.funLeft ℂ ℂ (actO A' WW g' h))
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd (botAlpha L i j t / botBeta G i j) (Y.e t) (Y.ideal (locPl G) t) A.rank A' WW Y.rA'.β Y.rW.β) =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd (botAlpha L i j t / botBeta G i j) (Y.e t) (Y.ideal (locPl G) t) A.rank A' WW X.rA'.β X.rW.β := by
    funext u
    rw [LinearMap.funLeft_apply]
    unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd
    by_cases hu : IsHalf (cA D (Y.e t)) u
    · have hd : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord A' WW Y.rA'.β Y.rW.β (actO A' WW g' h u) =
          GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord A' WW X.rA'.β X.rW.β u := by
        unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord
        rw [hfr u hu]
      rw [hd, GlobalTheory.SchrMove.isHalf_actO_iff]
    · rw [if_neg, if_neg]
      · exact fun hh => hu hh.1
      · exact fun hh => hu ((GlobalTheory.SchrMove.isHalf_actO_iff g' h u).1 hh.1)
  obtain ⟨⟨T₀, hT₀⟩, hall⟩ := hi.snd t
  refine ⟨⟨T₀, hT₀⟩, fun T' hT' => ?_⟩
  have th1 := GlobalTheory.SchrTheta.isTheta_placeModel D W.ψ hW.std A' WW Y.rA'.Λ Y.rW.Λ hSA hSW (cA D (Y.e t)) hos.idem
    hos.infPart_eq Y.vac' hvac.2.theta T' hT'
  have pm := GlobalTheory.SchrMove.isPlaceModel_move hW hL hT' th1 hc h0
  have hf' := hall _ pm
  have omm : ∀ p q (F : WO A' WW → ℂ), Y.ω' t p (Y.ω' t q F) = Y.ω' t (p * q) F := fun p q F => by
    rw [map_mul]; rfl
  show _ = T' _
  rw [← hΦ, hf']
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, map_smul, smul_smul, mul_inv_cancel₀ hc, one_smul]
  rw [omm, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel, Prod.mk_one_one, map_one]
  rfl

end GlobalTheory.BotFrames
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardPairSecondEqMovedBottomDatumStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.standard_pair_second_eq_moved_bottom_datum : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (i j : Fin D.R.m)
    (A A' WW : HSp D) (X Y : Tri T A A' WW), IsBottomTri W i j X → IsBottomTri W i j Y → ∀ (t : T) (g' : GA D A') (h : GA D WW) (x' y : (AE D)ˣ),
    Formalism.L2.Theta.SuppAt (Y.e t) A' g' → Formalism.IndefR.Lev.finE A' g' ∈ Formalism.L2.DIV.St Y.rA'.β →
    Formalism.L2.Theta.IsDetAt (Y.e t) A' g' x' →
    Formalism.L2.Theta.SuppAt (Y.e t) WW h → Formalism.IndefR.Lev.finE WW h ∈ Formalism.L2.DIV.St Y.rW.β → Formalism.L2.Theta.IsDetAt (Y.e t) WW h y →
    (∀ u : WO A' WW, IsHalf (cA D (Y.e t)) u →
      frMapAdj A' WW Y.rA'.β Y.rW.β (actO A' WW g' h u) = frMapAdj A' WW X.rA'.β X.rW.β u) →
    IsThetaAt W.ψ (symplO A' WW) (heisO W.ψ A' WW) (cA D (Y.e t))
      (latO A' WW X.rA'.Λ X.rW.Λ fun _ => True) 1 Y.vac'
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j) (Y.e t) (Y.ideal (locPl G) t)
        A.rank A' WW X.rA'.β X.rW.β)
      (((splitFacO (GlobalTheory.BotFrames.botAlpha L i j t) (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j) x' y : Circle)
        : ℂ) • Y.ω' t (g'⁻¹, h⁻¹) (Y.f' t)) := by
  first | exact @GlobalTheory.BotFrames.isThetaAt_stdSnd_move | exact GlobalTheory.BotFrames.isThetaAt_stdSnd_move | (intros; apply GlobalTheory.BotFrames.isThetaAt_stdSnd_move <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDefiniteBottomTripleTransferredFrames

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotFrames

theorem frames_transfer : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (S : GridChoice W Set.univ),
    IsStdChar D W.ψ (-1) → ∀ μ₀ : T, L.Is μ₀ → NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
    (X Y : Tri T A A' WW), IsBottomTri W i j X → IsBottomTri W i j Y →
    ∃ Y₁ : Tri T A A' WW, IsBottomTri W i j Y₁ ∧ Y₁.rA = X.rA ∧ Y₁.rA' = X.rA' ∧ Y₁.rW = X.rW ∧
      ∀ c : T → ℂ, Y.IsConst W.ψ W.θ c → ∃ u : T → D.what₂.LLˣ, Y₁.IsConst W.ψ W.θ fun t => D.what₂.embLL (u t) * c t := by
  intro D T L sc G W S _ μ₀ hL hN i j A A' WW X Y hX hY
  choose g g' h x x' y hE using fun t => GlobalTheory.T.exists_supported_unitaries_moving_bottomTriples W i j A A' WW X Y hX hY t
  have hC := fun t => GlobalTheory.T.definite_bottom_triple_basis_change_factor_mem_field W S μ₀ hL hN i j A A' WW Y hY t (g t) (g' t) (h t) (x t) (x' t) (y t)
    (hE t).1.1 (hE t).1.2.1 (hE t).1.2.2 (hE t).2.1.1 (hE t).2.1.2.1 (hE t).2.1.2.2 (hE t).2.2.1.1 (hE t).2.2.1.2.1
    (hE t).2.2.1.2.2
  choose z hz using hC
  have κne : ∀ t, ((splitFacO (GlobalTheory.BotFrames.botBeta G i j) (GlobalTheory.BotFrames.botBeta G i j / GlobalTheory.BotFrames.botAlpha L i j t)
      (x t) (y t) : Circle) : ℂ) ≠ 0 := fun t => Circle.coe_ne_zero _
  have κne' : ∀ t, ((splitFacO (GlobalTheory.BotFrames.botAlpha L i j t) (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j)
      (x' t) (y t) : Circle) : ℂ) ≠ 0 := fun t => Circle.coe_ne_zero _
  have sA := GlobalTheory.BotFrames.isStd_s_eq hX.std hY.std
  have sA' := GlobalTheory.BotFrames.isStd_s_eq hX.std' hY.std'
  have sW := GlobalTheory.BotFrames.isStd_s_eq hX.stdW hY.stdW
  have lA := GlobalTheory.BotFrames.isStd_lat_eq hX.std hY.std
  have lA' := GlobalTheory.BotFrames.isStd_lat_eq hX.std' hY.std'
  have lW := GlobalTheory.BotFrames.isStd_lat_eq hX.stdW hY.stdW
  refine ⟨GlobalTheory.BotFrames.reRig Y X.rA X.rA' X.rW
    (fun t => ((splitFacO (GlobalTheory.BotFrames.botBeta G i j) (GlobalTheory.BotFrames.botBeta G i j / GlobalTheory.BotFrames.botAlpha L i j t)
      (x t) (y t) : Circle) : ℂ) • Y.ω t ((g t)⁻¹, (h t)⁻¹) (Y.f t))
    (fun t => ((splitFacO (GlobalTheory.BotFrames.botAlpha L i j t) (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j)
      (x' t) (y t) : Circle) : ℂ) • Y.ω' t ((g' t)⁻¹, (h t)⁻¹) (Y.f' t)),
    ⟨hY.rank, hY.rank', hX.std, hX.std', hX.stdW, ?_⟩, rfl, rfl, rfl, fun c hc => ?_⟩
  · have hi := hY.is
    refine ⟨hi.rank, hX.is.rigA, hX.is.rigA', hX.is.rigW, hi.weil, hi.weil', ?_, ?_, hi.idem, hi.expo,
      fun t => GlobalTheory.T.standardPairFirstMember_movedDatum_splittingScale W i j A A' WW X Y hX hY t (g t) (h t) (x t) (y t) (hE t).1.1 (hE t).1.2.1 (hE t).1.2.2 (hE t).2.2.1.1
        (hE t).2.2.1.2.1 (hE t).2.2.1.2.2 (hE t).2.2.2.1,
      fun t => GlobalTheory.T.standard_pair_second_eq_moved_bottom_datum W i j A A' WW X Y hX hY t (g' t) (h t) (x' t) (y t) (hE t).2.1.1 (hE t).2.1.2.1 (hE t).2.1.2.2
        (hE t).2.2.1.1 (hE t).2.2.1.2.1 (hE t).2.2.1.2.2 (hE t).2.2.2.2, hi.meas, hi.meas'⟩
    · show IsVacO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.Λ X.rW.Λ Y.vac
      rw [sA, sW, lA, lW]
      exact hi.isVac
    · show IsVacO W.ψ W.θ A' WW X.rA'.s X.rW.s X.rA'.Λ X.rW.Λ Y.vac'
      rw [sA', sW, lA', lW]
      exact hi.isVac'
  · refine ⟨fun t => (z t)⁻¹, ?_⟩
    have hD := GlobalTheory.T.definiteBottomTriple_weilMove_rightTranslate W i j A A' WW X Y hX hY g g' h _ _ κne κne' (fun t => ⟨(hE t).1.1, (hE t).1.2.1⟩)
      (fun t => ⟨(hE t).2.1.1, (hE t).2.1.2.1⟩) (fun t => ⟨(hE t).2.2.1.1, (hE t).2.2.1.2.1⟩) c hc
    convert hD using 2 with t
    rw [map_units_inv, hz t, inv_div]

end GlobalTheory.BotFrames

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDefiniteBottomTripleTransferredFramesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_definiteBottomTriple_transferred_frames : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (S : GridChoice W Set.univ),
    IsStdChar D W.ψ (-1) → ∀ μ₀ : T, L.Is μ₀ → NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
    (X Y : Tri T A A' WW), IsBottomTri W i j X → IsBottomTri W i j Y →
    ∃ Y₁ : Tri T A A' WW, IsBottomTri W i j Y₁ ∧ Y₁.rA = X.rA ∧ Y₁.rA' = X.rA' ∧ Y₁.rW = X.rW ∧
      ∀ c : T → ℂ, Y.IsConst W.ψ W.θ c → ∃ u : T → D.what₂.LLˣ, Y₁.IsConst W.ψ W.θ fun t => D.what₂.embLL (u t) * c t := by
  first | exact @GlobalTheory.BotFrames.frames_transfer | exact GlobalTheory.BotFrames.frames_transfer | (intros; apply GlobalTheory.BotFrames.frames_transfer <;> assumption)
end
end
