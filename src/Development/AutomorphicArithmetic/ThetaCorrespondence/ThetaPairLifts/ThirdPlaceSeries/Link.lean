module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TieTwRecOf
public import Formalism.LocalToGlobal.Divisibility.TupUsed
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BaseRankEqOfRealisation
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowSideDetermined
import Formalism.LocalToGlobal.IndefiniteForms.IndefUse
public import Formalism.LocalToGlobal.HilbertRowConditions.ColumnsFunctionAtSubspaces
public import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Mathlib.RingTheory.PicardGroup
import Formalism.SharpRestriction.GlobalSchurBounds.QuadraticLogDerivCongr
import Formalism.SharpRestriction.GlobalSchurBounds.TheoremThreeUnderScaleOfGeneral

-- Source module: Formalism.LocalToGlobal.NormalizedHeckeFactors.BaseRowsEqRecordRows

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Module

namespace Formalism.L2.N.ExtNRows3

open Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}

theorem finrank_Mj_eq_dW (P : RowSideFamily ex) (i : Fin D.R.m) :
    finrank ℂ (D.what₂.Mj ((i : ℕ) + 1)) = P.S0.dW i := by
  have th := P.tied.div.th
  have := Module.finrank_eq_card_basis (Module.Basis.mk (th.li i) (th.span i).ge)
  rw [this, Fintype.card_fin]
  rfl

section Pin

variable (P : RowSideFamily ex) (h : RowsHold0_3 P)


include h in
theorem wf0 : (P.A3.side3 P.P0 P.ψ0 P.Zs).WF := by
  obtain ⟨s, hs⟩ := h.famOk
  exact P.A3.side_well_formed hs _ _ _ h.zsSt h.zsBl h.famSep

include h in
theorem dW_eq_D (i : Fin D.R.m) : P.S0.dW i = P.S0.D := by
  obtain ⟨R0, hR0⟩ := h.rows0
  exact hR0 ▸ R0.dW_eq (wf0 P h) i

include h in
theorem Ep_decomp : iSupIndep P.S0.Ep ∧ (⨆ p, P.S0.Ep p) = ⊤ := by
  obtain ⟨R0, hR0⟩ := h.rows0
  exact hR0 ▸ R0.Ep_decomp (wf0 P h)



end Pin

theorem thetaP_surj (P : RowSideFamily ex) (h : RowsHold0_3 P)
    (hR : Formalism.L2.DIV.DivRows3 D P.A3 P.P0 P.ψ0 P.Ps P.ψs P.Zs P.S0 P.S1 ex.p0 P.C P.NuC P.I) (i : Fin D.R.m) (t : P.T)
    (hl : Function.Surjective (lPrj D P.A3.A P.P0 P.ψ0 (P.A3.fam3.toSub2 P.Zs) i t).mulVec) :
    Function.Surjective (D.what₂.thetaP (P.I.tup t) ((i : ℕ) + 1)) := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← P.tied.div.th.span i, Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  obtain ⟨R0, hR0⟩ := h.rows0
  have hb : Function.Bijective (P.S0.θ i t).mulVec := hR0 ▸ R0.l1c.2.1 i t
  obtain ⟨z, hz⟩ := hb.2 (Pi.single k 1)
  obtain ⟨x, hx⟩ := hl z
  refine ⟨_, (hR.thTheta i t x).trans ?_⟩
  refine congrArg (P.I.jW i) ?_
  exact (congrArg _ hx).trans hz

theorem adjoint_injective {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] (A : V →ₗ[ℂ] W) (hA : Function.Surjective A) :
    Function.Injective (LinearMap.adjoint A) := by
  refine (injective_iff_map_eq_zero (LinearMap.adjoint A)).2 fun z hz => ?_
  obtain ⟨v, hv⟩ := hA z
  have h1 := LinearMap.adjoint_inner_left A v z
  rw [hz, inner_zero_left, hv] at h1
  exact inner_self_eq_zero.mp h1.symm

end Formalism.L2.N.ExtNRows3

end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BaseRowsEqRecordRows

section

@[expose] public section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Module
namespace Formalism.L2.N.ExtNRows3
open Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}
section Pin
variable (T : _root_.Formalism.L2.TiedDataSKAlt ex) (P : RowSideFamily ex) (hp : _root_.Formalism.L2.Rows.RowSideDeterminedAlt T P) (hL : RowsHoldLam3 P) (h : RowsHold0_3 P)
include hp hL h in
open Classical in
theorem base_rows_eq_record_rows_alt : P.S0.D = D.what₂.D0 := by
  obtain ⟨cOf, -, -, h3⟩ := hL
  have e1 := sum_finrank P.S0.Ep (Ep_decomp P h).1 (Ep_decomp P h).2
  rw [Module.finrank_fin_fun] at e1
  have e2 : ∑ c, ∑ σ ∈ Finset.univ.filter (fun σ => cOf σ = c), D.what₂.nRows0 σ = ∑ σ, D.what₂.nRows0 σ :=
    Finset.sum_fiberwise _ _ _
  have e3 : ∑ σ, D.what₂.nRows0 σ = D.what₂.D0 := by
    unfold Rows.Data.nRows0
    rw [← Fintype.card_sigma, Fintype.card_congr (Equiv.sigmaFiberEquiv D.what₂.ft0), Fintype.card_fin]
  rw [← e1, ← e3, ← e2]
  exact Finset.sum_congr rfl fun c _ => (h3 c).symm
include hp hL h in
theorem finrank_Mj_eq_D0 : ∀ j, 1 ≤ j → j ≤ D.R.m → finrank ℂ (D.what₂.Mj j) = D.what₂.D0 := by
  intro j h1 h2
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have := finrank_Mj_eq_dW P ⟨k, by omega⟩
  rw [dW_eq_D P h, _root_.Formalism.L2.N.ExtNRows3.base_rows_eq_record_rows_alt T P hp hL h] at this
  exact this
end Pin
theorem thetaT_injective_and_finrank_Zj_eq_D0_of_surjective (T : _root_.Formalism.L2.TiedDataSKAlt ex) (P : RowSideFamily ex) (hp : _root_.Formalism.L2.Rows.RowSideDeterminedAlt T P) (hL : RowsHoldLam3 P) (h : RowsHold0_3 P)
    (hR : Formalism.L2.DIV.DivRows3 D P.A3 P.P0 P.ψ0 P.Ps P.ψs P.Zs P.S0 P.S1 ex.p0 P.C P.NuC P.I) (i : Fin D.R.m) (t : P.T)
    (hl : Function.Surjective (lPrj D P.A3.A P.P0 P.ψ0 (P.A3.fam3.toSub2 P.Zs) i t).mulVec) :
    Function.Injective (D.what₂.thetaT (P.I.tup t) ((i : ℕ) + 1)) ∧
      finrank ℂ (D.what₂.Zj (P.I.tup t) ((i : ℕ) + 1)) = D.what₂.D0 := by
  have hi : Function.Injective (D.what₂.thetaT (P.I.tup t) ((i : ℕ) + 1)) :=
    adjoint_injective _ (thetaP_surj P h hR i t hl)
  refine ⟨hi, ?_⟩
  unfold Rows.Data.Zj
  rw [LinearMap.finrank_range_of_inj hi]
  exact _root_.Formalism.L2.N.ExtNRows3.finrank_Mj_eq_D0 T P hp hL h _ (Nat.succ_le_succ (Nat.zero_le _)) i.2
end Formalism.L2.N.ExtNRows3
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RankZeroOfRowConditions

section

@[expose] public section



section
noncomputable section
namespace Formalism.L2.N.RankZeroOfLevelThree
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Module
open Formalism.L2.N.ExtNRows3 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows
theorem rank_zero_of_row_conditions_alt {eps : ℝ} (Fm : FamP eps) (x0 : ℝ)
    (T : ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, _root_.Formalism.L2.TiedDataSKAlt (Fm.ex x hx i))
    (P : ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, RowSideFamily (Fm.ex x hx i))
    (hp : ∀ x (hx : Fm.x1 < x) (h0 : x0 ≤ x) (i : Fm.Ix x), _root_.Formalism.L2.Rows.RowSideDeterminedAlt (T x hx h0 i) (P x hx h0 i))
    (hL : ∀ x (hx : Fm.x1 < x) (h0 : x0 ≤ x) (i : Fm.Ix x), RowsHoldLam3 (P x hx h0 i))
    (hR : ∀ x (hx : Fm.x1 < x) (h0 : x0 ≤ x) (i : Fm.Ix x), Formalism.L2.DIV.DivRows3 (Fm.D x i) (P x hx h0 i).A3 (P x hx h0 i).P0
      (P x hx h0 i).ψ0 (P x hx h0 i).Ps (P x hx h0 i).ψs (P x hx h0 i).Zs (P x hx h0 i).S0 (P x hx h0 i).S1 (Fm.ex x hx i).p0
      (P x hx h0 i).C (P x hx h0 i).NuC (P x hx h0 i).I)
    (h : ∀ x (hx : Fm.x1 < x) (h0 : x0 ≤ x) (i : Fm.Ix x), RowsHold0_3 (P x hx h0 i))
    (ht : ∀ x (hx : Fm.x1 < x) (h0 : x0 ≤ x) (i : Fm.Ix x), ∃ t : (P x hx h0 i).T,
      (P x hx h0 i).I.tup t = (Fm.D x i).what₂.mu0 ∧
      ∀ k : Fin (Fm.D x i).R.m, Function.Surjective (lPrj (Fm.D x i) (P x hx h0 i).A3.A (P x hx h0 i).P0
        (P x hx h0 i).ψ0 ((P x hx h0 i).A3.fam3.toSub2 (P x hx h0 i).Zs) k t).mulVec) :
    SmallLevelRankEq Fm := by
  refine ⟨max x0 (Fm.x1 + 1), fun x hxx i j hj => ?_⟩
  have hx1 : Fm.x1 < x := lt_of_lt_of_le (lt_add_one _) (le_trans (le_max_right _ _) hxx)
  have h0 : x0 ≤ x := le_trans (le_max_left _ _) hxx
  obtain ⟨t, htup, hsurj⟩ := ht x hx1 h0 i
  have hj' := Finset.mem_Icc.1 hj
  obtain ⟨k, rfl⟩ : ∃ k : Fin (Fm.D x i).R.m, j = (k : ℕ) + 1 := ⟨⟨j - 1, by omega⟩, by simp; omega⟩
  have key := (_root_.Formalism.L2.N.ExtNRows3.thetaT_injective_and_finrank_Zj_eq_D0_of_surjective (T x hx1 h0 i) (P x hx1 h0 i) (hp x hx1 h0 i) (hL x hx1 h0 i) (h x hx1 h0 i) (hR x hx1 h0 i) k t (hsurj k)).2
  rw [htup] at key
  exact key
end Formalism.L2.N.RankZeroOfLevelThree
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Link

section

@[expose] public section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT Formalism.L2.Top3 Formalism.L2.Top4

theorem GlobalTheory.Top.link_alt_alt_alt : ∀ (𝒜 : FamClass)
    (sel : _root_.Formalism.L2.TwistSelection 𝒜)
    (selS : _root_.Formalism.L2.Top4.SelectionSpectralCondition 𝒜 sel)
    (selP : _root_.Formalism.L2.Top4.BaseLevelTiedChoiceAlt 𝒜 sel)
    (selDH : _root_.Formalism.L2.Top3.SelectionDefiniteHeightCondition 𝒜 sel)
    (selC : _root_.Formalism.L2.Top4.ColumnChoiceCompatibleSelection 𝒜 sel selP)
    (selB : _root_.Formalism.L2.Top4.SelectionBundle 𝒜 sel selS selP selDH selC)
    (hPA : _root_.Formalism.L2.Top4.AllRealisationsPrimitive sel (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB))
    (hLamP : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.Rows.RowsHoldLam3 (selP Fm hc x hx h i).1)
    (hDivG : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.DIV.DivRows3G (selP Fm hc x hx h i).1)
    (zL : Closed (D3 3 𝒜) fun Fm _ => ∀ hc : D3 3 𝒜 Fm, ∃ xr : ℝ, ∀ x (hx : Fm.x1 < x) (h : (sel Fm (d3_a hc)).1 ≤ x), xr ≤ x →
      ∀ (i : Fm.Ix x) (k : Fin (Fm.D x i).R.m),
        Function.Surjective (Formalism.L2.DIV.lPrj (Fm.D x i) (selP Fm (d3_a hc) x hx h i).1.A3.A (selP Fm (d3_a hc) x hx h i).1.P0
          (selP Fm (d3_a hc) x hx h i).1.ψ0 ((selP Fm (d3_a hc) x hx h i).1.A3.fam3.toSub2 (selP Fm (d3_a hc) x hx h i).1.Zs) k
          (selP Fm (d3_a hc) x hx h i).1.A3.A.μ0).mulVec), Closed (D3 3 𝒜) fun Fm _ => SmallLevelRankEq Fm := by
  intro 𝒜 sel selS selP selDH selC selB hPA hLamP hDivG zL
  have hDivR : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.DIV.DivRows3 (Fm.D x i) (selP Fm hc x hx h i).1.A3 (selP Fm hc x hx h i).1.P0 (selP Fm hc x hx h i).1.ψ0 (selP Fm hc x hx h i).1.Ps
        (selP Fm hc x hx h i).1.ψs (selP Fm hc x hx h i).1.Zs (selP Fm hc x hx h i).1.S0 (selP Fm hc x hx h i).1.S1 (Fm.ex x hx i).p0 (selP Fm hc x hx h i).1.C (selP Fm hc x hx h i).1.NuC (selP Fm hc x hx h i).1.I :=
    fun Fm hc x hx h i => (hDivG Fm hc x hx h i).toRows (_root_.Formalism.IndefR.LevelRealisationRankEquality.tup_all_used_of_realisation (selB Fm hc x hx h i).Q)
  have hZ : Closed (D3 3 𝒜) fun Fm _ => SmallLevelRankEq Fm :=
    closed_of_mem (zL.imp fun Fm _ _ h hc => by
      obtain ⟨xr, h⟩ := h hc
      exact _root_.Formalism.L2.N.RankZeroOfLevelThree.rank_zero_of_row_conditions_alt Fm (max (sel Fm (d3_a hc)).1 xr)
        (fun x hx h0 i => ((sel Fm (d3_a hc)).2 x hx (le_trans (le_max_left _ _) h0) i).T)
        (fun x hx h0 i => (selP Fm (d3_a hc) x hx (le_trans (le_max_left _ _) h0) i).1)
        (fun x hx h0 i => (selP Fm (d3_a hc) x hx (le_trans (le_max_left _ _) h0) i).2)
        (fun x hx h0 i => hLamP Fm (d3_a hc) x hx (le_trans (le_max_left _ _) h0) i)
        (fun x hx h0 i => hDivR Fm (d3_a hc) x hx (le_trans (le_max_left _ _) h0) i)
        (fun x hx h0 i => _root_.Formalism.L2.Top4.selP_condition_zero_of_primAll hPA Fm (d3_a hc) x hx (le_trans (le_max_left _ _) h0) i)
        (fun x hx h0 i => ⟨_, (selP Fm (d3_a hc) x hx (le_trans (le_max_left _ _) h0) i).1.tied.div.tup.mu0,
          h x hx (le_trans (le_max_left _ _) h0) (le_trans (le_max_right _ _) h0) i⟩))
  exact hZ
end
end
end
end
