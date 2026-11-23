module

public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.TwoLevelLogarithm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLatPIffMulVec
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIsometryOfSabMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransp
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ContinuousRmulPair
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTranspOfMovesAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTransporterMovesFrameReadsInverse
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransporterMovesAllFramesOfDenseOpenStatement
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.UniformSpace.Uniformizable
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PairUnfoldPfA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientDomain
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ActLevIffLevelActionOver
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NumericalConsequencesOfPins
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegers
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ActLevFullLevelGroupFramedPoints
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLevelComponentTransportCompStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransportIdentityOfMemComponentGroupStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelActionMulAndFaithfulFiniteGroupStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelComponentTransportReadsCuspFormsConstMulStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniqueUpToTargetGroup
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTransporterMovesFrameReadsInverseStatement

section

@[expose] public section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn

theorem _root_.GlobalTheory.T.exists_transporter_moves_frame_reads_inverse : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)), ∃ ψ : ∀ k : (uAt r v i).Comp, LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] latQ p r i v k, ∀ (γ : LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l) (k : (uAt r v i).Comp) (x : Frame ((uAt r v i).X k).Ψ D.R.r) (hx : x ∈ ((uAt r v i).X k).dom), ∃ (k' : (uAt r v i).Comp) (a : GL (Fin D.R.r) D.host.E) (hm : GlobalTheory.LevelCusp.IsMatch ((uAt r v i).X k) ((uAt r v i).X k') a), ReadsInv p r i v ψ γ k k' a ∧ MovesAt p r i v γ k k' a hm x hx := by
  first | exact @GlobalTheory.ShareOn.exists_movesAt_readsInv | exact GlobalTheory.ShareOn.exists_movesAt_readsInv | (intros; apply GlobalTheory.ShareOn.exists_movesAt_readsInv <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelChangeTransportersAllComponents

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn

namespace GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_transp_all : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)), ∃ ψ : ∀ k : (uAt r v i).Comp, LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] latQ p r i v k, ∀ (γ : LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l) (k : (uAt r v i).Comp), ∃ (k' : (uAt r v i).Comp) (a : GL (Fin D.R.r) D.host.E), IsTransp p r i v ψ γ k k' a := by
  intro D L hT Gi Gl Kc Y cX ex Csz p hp r h hr i v
  obtain ⟨ψ, h1⟩ := GlobalTheory.T.exists_transporter_moves_frame_reads_inverse p hp r h hr i v
  refine ⟨ψ, fun γ k => ?_⟩
  let V := Frame ((uAt r v i).X k).Ψ D.R.r
  let Dk : Set V := ((uAt r v i).X k).dom
  have hDo : IsOpen Dk := FourierCoefficientDomain.isOpen_dom _
  have hDn : Dk.Nonempty := (GlobalTheory.frames_isConnected D.host.E D.R.r ((uAt r v i).X k)).nonempty
  let ι := Σ k' : (uAt r v i).Comp, {a : GL (Fin D.R.r) D.host.E //
    ∃ hm : GlobalTheory.LevelCusp.IsMatch ((uAt r v i).X k) ((uAt r v i).X k') a, ReadsInv p r i v ψ γ k k' a}
  let S : ι → Set V := fun c => {x | ∃ hx : x ∈ Dk, MovesAt p r i v γ k c.1 c.2.1 c.2.2.1 x hx}
  haveI : Countable ι := inferInstance
  obtain ⟨x₀, hx₀⟩ := hDn
  haveI : Nonempty ι := by
    obtain ⟨k', a, hm, hR, -⟩ := h1 γ k x₀ hx₀
    exact ⟨⟨k', a, hm, hR⟩⟩
  haveI : Nonempty Dk := ⟨⟨x₀, hx₀⟩⟩
  haveI : LocallyCompactSpace Dk := hDo.locallyCompactSpace
  let T : ι → Set Dk := fun c => Subtype.val ⁻¹' closure (S c)
  have hTc : ∀ c, IsClosed (T c) := fun c => isClosed_closure.preimage continuous_subtype_val
  have hTu : ⋃ c, T c = Set.univ := by
    refine Set.eq_univ_of_forall fun y => ?_
    obtain ⟨k', a, hm, hR, hM⟩ := h1 γ k y.1 y.2
    exact Set.mem_iUnion.2 ⟨⟨k', a, hm, hR⟩, subset_closure ⟨y.2, hM⟩⟩
  obtain ⟨c, hc⟩ := nonempty_interior_of_iUnion_of_closed hTc hTu
  obtain ⟨k', a, hm, hR⟩ := c
  refine ⟨k', a, isTransp_of_movesAt hm ?_ hR⟩
  refine GlobalTheory.T.transporter_moves_all_frames_of_dense_open p hp r h hr i v γ k k' a hm (Subtype.val '' interior (T ⟨k', a, hm, hR⟩))
    (hDo.isOpenMap_subtype_val _ isOpen_interior) (hc.image _) ?_ ?_
  · rintro _ ⟨y, -, rfl⟩
    exact y.2
  · rintro _ ⟨y, hy, rfl⟩
    have hy' : y ∈ T ⟨k', a, hm, hR⟩ := interior_subset hy
    exact hy'

end GlobalTheory.ShareOn

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelChangeTransportersAllComponentsStatement

section

@[expose] public section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn

theorem _root_.GlobalTheory.T.exists_levelChange_transporters_all_components : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)), ∃ ψ : ∀ k : (uAt r v i).Comp, LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] latQ p r i v k, ∀ (γ : LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l) (k : (uAt r v i).Comp), ∃ (k' : (uAt r v i).Comp) (a : GL (Fin D.R.r) D.host.E), IsTransp p r i v ψ γ k k' a := by
  first | exact @GlobalTheory.ShareOn.exists_transp_all | exact GlobalTheory.ShareOn.exists_transp_all | (intros; apply GlobalTheory.ShareOn.exists_transp_all <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdentityTransportsComponentToItself

section

@[expose] public section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn
set_option autoImplicit false

noncomputable section
namespace GlobalTheory.ShareOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem lact_one_self {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Ψ : Finset (E →+* ℂ)}
    (y : Frame Ψ r) : lact (1 : GL (Fin r) E) y = y := by
  funext τ
  show ((↑(1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ : Matrix (Fin r) (Fin r) ℂ) = y τ
  rw [Units.val_one, Matrix.map_one _ (map_zero τ.1) (map_one τ.1), Matrix.one_mul]; rfl

theorem isTransp_one : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (ψ : ∀ k : (uAt r v i).Comp, LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] latQ p r i v k) (k : (uAt r v i).Comp), IsTransp p r i v ψ 1 k k 1 := by
  intro D L hT Gi Gl Kc Y cX ex Csz p hm r h ho i v ψ k
  have hl := h.laws v
  obtain ⟨-, hA, -, -, -, -, hj⟩ := GlobalTheory.PinNum.numerics_of_pins D (r.used v).full.Q hl.p.pins
  obtain ⟨hpq, hr, -⟩ := hj ((i : ℕ) + 1) ⟨by omega, by omega⟩
  have hL := GlobalTheory.FullLevelAction.actLev_levFull D (r.used v).full.Q ((i : ℕ) + 1) (by rw [hpq]; exact hr) hA
  refine ⟨GlobalTheory.LevelCusp.isMatch_of_isUStab _ ⟨fun x y => by simp, fun x => by simp⟩, fun x hx => ?_, fun w => ?_⟩
  · have e : castFrame (rfl : ((uAt r v i).X k).Ψ = ((uAt r v i).X k).Ψ) (lact 1 x) = x := by
      rw [lact_one_self]; rfl
    refine ⟨by rw [e]; exact hx, 1, ?_⟩
    have ey : (uAt r v i).un k ⟨castFrame (rfl : ((uAt r v i).X k).Ψ = ((uAt r v i).X k).Ψ) (lact 1 x), by rw [e]; exact hx⟩ =
        (uAt r v i).un k ⟨x, hx⟩ := congrArg _ (Subtype.ext e)
    have hf := hL.func 1 _ ((uAt r v i).un k ⟨x, hx⟩) ((uAt r v i).un k ⟨x, hx⟩)
      (mvLev ((r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c 1 ((uAt r v i).un k ⟨x, hx⟩))
      (hL.one _ _) (Formalism.L2.Pj.mvPt_spec hL.total 1 _)
    have hy : (uAt r v i).un k ⟨x, hx⟩ =
        mvLev ((r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c 1 ((uAt r v i).un k ⟨x, hx⟩) :=
      (GlobalTheory.LevelLawsCompare.frMap_id_iff _ _).1 hf
    rw [ey]
    exact (congrArg (FrBor 1 ((uAt r v i).un k ⟨x, hx⟩)) hy).mp (GlobalTheory.ShFam.Descent.frBor_one _)
  · have hw : Matrix.mulVec ((1 : GL (Fin D.R.r) D.host.E) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E)
        (w : Fin D.R.r → D.host.E) ∈ ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA.lattice₂ D ((uAt r v i).X k).Λ := by
      rw [Units.val_one, Matrix.one_mulVec]; exact w.2
    refine ⟨hw, ?_⟩
    calc Submodule.Quotient.mk ⟨_, hw⟩ = Submodule.Quotient.mk w :=
          congrArg _ (Subtype.ext (Matrix.one_mulVec _))
      _ = ψ k ((ψ k).symm (Submodule.Quotient.mk w)) := ((ψ k).apply_symm_apply _).symm
      _ = _ := rfl
end GlobalTheory.ShareOn

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdentityTransportsComponentToItselfStatement

section

@[expose] public section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn

theorem _root_.GlobalTheory.T.identity_transports_component_to_itself : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (ψ : ∀ k : (uAt r v i).Comp, LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] latQ p r i v k) (k : (uAt r v i).Comp), IsTransp p r i v ψ 1 k k 1 := by
  first | exact @GlobalTheory.ShareOn.isTransp_one | exact GlobalTheory.ShareOn.isTransp_one | (intros; apply GlobalTheory.ShareOn.isTransp_one <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniqueUpToTargetGroupStatement

section

@[expose] public section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn

theorem _root_.GlobalTheory.T.unique_up_to_target_group : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (ψ : ∀ k : (uAt r v i).Comp, LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] latQ p r i v k) (γ : LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l) (k k₁ k₂ : (uAt r v i).Comp) (a₁ a₂ : GL (Fin D.R.r) D.host.E), IsTransp p r i v ψ γ k k₁ a₁ → IsTransp p r i v ψ γ k k₂ a₂ → k₁ = k₂ ∧ a₁ * a₂⁻¹ ∈ ((uAt r v i).X k₁).Γ := by
  first | exact @GlobalTheory.ShareOn.IsTransp.uniq | exact GlobalTheory.ShareOn.IsTransp.uniq | (intros; apply GlobalTheory.ShareOn.IsTransp.uniq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelGroupTransportUniformisationComponent

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn

namespace GlobalTheory.ShareOn

theorem exists_transport : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)), ∃ (act : p.P.Gp → (uAt r v i).Comp → (uAt r v i).Comp) (tr : p.P.Gp → (uAt r v i).Comp → GL (Fin D.R.r) D.host.E),
    (∀ k, act 1 k = k) ∧ (∀ g g' k, act (g * g') k = act g (act g' k)) ∧
    (∀ g k, GlobalTheory.LevelCusp.IsMatch ((uAt r v i).X k) ((uAt r v i).X (act g k)) (tr g k)) ∧
    (∀ g k γ, γ ∈ ((uAt r v i).X k).Γ ↔ tr g k * γ * (tr g k)⁻¹ ∈ ((uAt r v i).X (act g k)).Γ) ∧
    (∀ g g' k, tr (g * g') k * (tr g (act g' k) * tr g' k)⁻¹ ∈ ((uAt r v i).X (act (g * g') k)).Γ) ∧
    (∀ g k, act g k = k → tr g k ∈ ((uAt r v i).X k).Γ → g = 1) ∧
    (∃ a : p.P.Gp → (uAt r v i).Comp → ℂˣ, ∀ (F : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i)) (g : p.P.Gp)
      (k : (uAt r v i).Comp) (x : Frame ((uAt r v i).X k).Ψ D.R.r), x ∈ ((uAt r v i).X k).dom →
      ∀ (h2 : ((uAt r v i).X k).Ψ = ((uAt r v i).X (act g k)).Ψ),
        rdU (uAt r v i) (actLev (Xo := p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c (levFull (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l)
            (r.lev i g⁻¹) F.1) k x =
          (a g k : ℂ) * rdU (uAt r v i) F.1 (act g k) (castFrame h2 (lact (tr g k) x))) ∧
    ∀ Lf : (uAt r v i).Comp → Submodule (𝓞 D.host.E) (Fin D.R.r → D.host.E), (∀ k, Lf k = lattice₂ D ((uAt r v i).X k).Λ) →
      ∃ φ : ∀ k, LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E]
          (Lf k ⧸ (p.T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (Lf k)))),
        ∀ (k : (uAt r v i).Comp) (g : p.P.Gp), act g k = k → ∃ n : ℤ, ∀ w : Lf k,
          ∃ hw : Matrix.mulVec (tr g k : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) w ∈ Lf k,
            Submodule.Quotient.mk (p := p.T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (Lf k))) ⟨_, hw⟩ =
              φ k ((r.lev i g ^ n) ((φ k).symm (Submodule.Quotient.mk w))) := by
  intro D L hT Gi Gl Kc Y cX ex Csz p hp r h hr i v
  obtain ⟨ψ, hex⟩ := GlobalTheory.T.exists_levelChange_transporters_all_components p hp r h hr i v
  have uniq := GlobalTheory.T.unique_up_to_target_group p hp r h hr i v ψ
  have one := GlobalTheory.T.identity_transports_component_to_itself p hp r h hr i v ψ
  have comp := GlobalTheory.T.isLevelComponentTransport_comp p hp r h hr i v ψ
  have gam := GlobalTheory.T.isTransport_identity_of_mem_componentGroup p hp r h hr i v ψ
  obtain ⟨lmul, linj⟩ := GlobalTheory.T.levelAction_mul_and_faithful_finiteGroup p hp r h hr i
  have c8 := GlobalTheory.T.levelComponentTransport_reads_cuspForms_const_mul p hp r h hr i v ψ
  choose act tr htr using fun (g : p.P.Gp) k => hex (r.lev i g⁻¹) k
  have lev1 : r.lev i 1 = 1 := by
    have e := lmul 1 1
    rw [mul_one] at e
    exact (mul_eq_left.1 e.symm)
  have levinv : ∀ g, r.lev i g⁻¹ = (r.lev i g)⁻¹ := fun g =>
    eq_inv_of_mul_eq_one_left (by rw [← lmul, inv_mul_cancel, lev1])
  have levmul : ∀ g g', r.lev i (g * g')⁻¹ = r.lev i g'⁻¹ * r.lev i g⁻¹ := fun g g' => by
    rw [mul_inv_rev, lmul]
  have hco : ∀ g g' k, IsTransp p r i v ψ (r.lev i (g * g')⁻¹) k (act g (act g' k)) (tr g (act g' k) * tr g' k) :=
    fun g g' k => by
      rw [levmul]
      exact comp _ _ _ _ _ _ _ (htr g' k) (htr g (act g' k))
  refine ⟨act, tr, fun k => ?_, fun g g' k => ?_, fun g k => (htr g k).1, fun g k γ => ?_, fun g g' k => ?_,
    fun g k hk hΓ => ?_, ⟨fun g k => (c8 _ _ _ _ (htr g k)).choose, fun F g k x hx h2 =>
      (c8 _ _ _ _ (htr g k)).choose_spec F x hx h2⟩, fun Lf hLf => ?_⟩
  · have e := htr 1 k
    rw [inv_one, lev1] at e
    exact (uniq _ _ _ _ _ _ e (one k)).1
  · exact (uniq _ _ _ _ _ _ (htr (g * g') k) (hco g g' k)).1
  · constructor
    · intro hγ
      have e1 := comp _ _ _ _ _ _ _ (gam k γ hγ) (htr g k)
      rw [one_mul] at e1
      have := (uniq _ _ _ _ _ _ e1 (htr g k)).2
      simpa [mul_assoc] using this
    · intro hγ
      obtain ⟨k'', b, hb⟩ := hex (r.lev i g⁻¹)⁻¹ (act g k)
      have e1 := comp _ _ _ _ _ _ _ (htr g k) hb
      rw [mul_inv_cancel] at e1
      obtain ⟨hk'', hb1⟩ := uniq _ _ _ _ _ _ e1 (one k)
      rw [hk''] at hb hb1
      have e2 := comp _ _ _ _ _ _ _ (gam _ _ hγ) hb
      have e3 := comp _ _ _ _ _ _ _ (htr g k) e2
      rw [one_mul, mul_inv_cancel] at e3
      have hb2 := (uniq _ _ _ _ _ _ e3 (one k)).2
      rw [inv_one, mul_one] at hb1 hb2
      have key : γ = (b * tr g k)⁻¹ * (b * (tr g k * γ * (tr g k)⁻¹) * tr g k) := by group
      rw [key]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hb1) hb2
  · exact (uniq _ _ _ _ _ _ (htr (g * g') k) (hco g g' k)).2
  · have e1 := gam k (tr g k) hΓ
    have e2 := htr g k
    rw [hk] at e2
    have e3 := IsTransp.eq_of_eq e2 e1
    have : g⁻¹ = 1 := linj _ e3
    simpa using this
  · have keyg : ∀ g, (r.lev i g⁻¹).symm = r.lev i g ^ (1 : ℤ) := fun g => by
      rw [zpow_one, levinv]
      rfl
    obtain rfl : Lf = fun k => lattice₂ D ((uAt r v i).X k).Λ := funext hLf
    refine ⟨ψ, fun k g hk => ⟨1, fun w => ?_⟩⟩
    beta_reduce at w ⊢
    have e2 := htr g k
    rw [hk] at e2
    obtain ⟨-, -, hm⟩ := e2
    obtain ⟨hw, e⟩ := hm w
    refine ⟨hw, e.trans (congrArg (ψ k) (congrFun (congrArg DFunLike.coe (keyg g)) _))⟩

end GlobalTheory.ShareOn

end
end
end
