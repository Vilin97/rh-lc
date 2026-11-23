module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NodeAgree
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainIntertwinersRowZeroUnitVacua
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainStepCharactersEqGridRowZeroRanks
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsColIntertwiner
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDownArrowRealIntertwinerWithAdjoint
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
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGridCosetDataEqWeilCosetVectors
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsVacOfNodeAgree
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsVacTrueOfAgree
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNonzeroRealIntertwinerGridArrow
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsVacX
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWRepOfNegSp
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeilRowArrow
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridRowArrowExistsCommonRealIntertwinerStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDownArrowRealIntertwinerWithAdjointStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_downArrow_realIntertwiner_with_adjoint : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ i, i < D.R.m → ∀ (ω : GlobalTheory.Grid.WRep (G.P (i + 1)).V (G.P i).V) (f : WO (G.P (i + 1)).V (G.P i).V → ℂ), GlobalTheory.Grid.IsWeil R.ψ true (G.P (i + 1)).V (G.P i).V (G.chi (D.R.m - i)) (G.chi (D.R.m - i)) ω → GlobalTheory.Grid.IsVac R.ψ R.θ true (G.P (i + 1)) (G.P i) f → ∃ (It : GlobalTheory.Grid.Pol (G.P (i + 1)) (G.P i) →ₗ[ℂ] SmT (G.P (i + 1)).M →ₗ[ℂ] SmT (G.P i).M) (U : GlobalTheory.Grid.Pol (G.P (i + 1)) (G.P i) →ₗ⋆[ℂ] SmT (G.P i).M →ₗ[ℂ] SmT (G.P (i + 1)).M), GlobalTheory.Grid.IsIntw R.θ (G.P i).M (G.P (i + 1)).M ω.swap (GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) f) It ∧ (⟨ω, f, It⟩ : GlobalTheory.Grid.ArrT (G.P (i + 1)) (G.P i)).IsAdj U := by
  first | exact @GlobalTheory.DownArrow.down_intertwiner_adj | exact GlobalTheory.DownArrow.down_intertwiner_adj | (intros; apply GlobalTheory.DownArrow.down_intertwiner_adj <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGridCosetDataEqWeilCosetVectorsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_gridCosetData_eq_weilCosetVectors : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ i, i < D.R.m → ∀ f : WO (G.V (i + 1) 0).V (G.V i 0).V → ℂ, HEq f (W.vac i) → ∃ v : G.toGridSp.Cos R i → (WO (G.V (i + 1) 0).V (G.V i 0).V → ℂ), (∀ c, GlobalTheory.Grid.IsCosetVec R.ψ true (G.V (i + 1) 0) (G.V i 0) G.idem (G.lvl R) c f (v c)) ∧ (∀ c, ∃ κ, HEq (v c) (W.cosVec i κ)) ∧ ∀ κ, ∃ c, HEq (v c) (W.cosVec i κ) := by
  first | exact @GlobalTheory.GridJoin.exists_cosData_agree | exact GlobalTheory.GridJoin.exists_cosData_agree | (intros; apply GlobalTheory.GridJoin.exists_cosData_agree <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsVacThRows

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.GridJoin

theorem isVacO_transport {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) :
    ∀ (S S' S₀ S₀' : HSp D) (a : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
      (a' : D.what₂.Tau → Matrix (Fin S'.rank) (Fin S'.rank) ℂ)
      (a₀ : D.what₂.Tau → Matrix (Fin S₀.rank) (Fin S₀.rank) ℂ)
      (a₀' : D.what₂.Tau → Matrix (Fin S₀'.rank) (Fin S₀'.rank) ℂ)
      (Λ : Set (Fin S.rank → D.host.E)) (Λ' : Set (Fin S'.rank → D.host.E))
      (Λ₀ : Set (Fin S₀.rank → D.host.E)) (Λ₀' : Set (Fin S₀'.rank → D.host.E)),
      S = S₀ → S' = S₀' → HEq a a₀ → HEq a' a₀' → HEq Λ Λ₀ → HEq Λ' Λ₀' →
      (∃ f, IsVacO ψ θ S₀ S₀' a₀ a₀' Λ₀ Λ₀' f) → ∃ f, IsVacO ψ θ S S' a a' Λ Λ' f := by
  rintro S S' _ _ a a' a₀ a₀' Λ Λ' Λ₀ Λ₀' rfl rfl h1 h2 h3 h4 h
  cases eq_of_heq h1; cases eq_of_heq h2; cases eq_of_heq h3; cases eq_of_heq h4
  exact h

theorem heq_coe_lat {D : D7} {V V' : HSp D} (h : V = V') {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin V'.rank → D.host.E)} (hΛ : HEq Λ Λ') :
    HEq (Λ : Set (Fin V.rank → D.host.E)) (Λ' : Set (Fin V'.rank → D.host.E)) := by
  subst h; cases eq_of_heq hΛ; rfl

theorem exists_isVac_th_rows : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ i j, i + 1 ≤ D.R.m → j < D.R.m → ∃ f : WO (G.nV i j).V (G.nV i (j + 1)).V → ℂ, GlobalTheory.Grid.IsVac R.ψ R.θ false (G.nV i j) (G.nV i (j + 1)) f := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc _ _ _ F hR _ G' W hW G _ _ hS _ i j hi hj
  obtain ⟨f, hf⟩ := GlobalTheory.FunObj.exists_isVac W hR.lev (p := .mu A.μ0 (i + 1) j) ⟨hi, by omega⟩
  have a := hS.vert (i + 1) j hi hj.le
  have b := hS.vert (i + 1) (j + 1) hi hj
  rw [← hW.ψ, ← hW.θ]
  exact isVacO_transport W.ψ W.θ _ _ _ _ _ _ _ _ _ _ _ _ a.sp b.sp a.cart b.cart
    (heq_coe_lat a.sp a.lat) (heq_coe_lat b.sp b.lat) ⟨f, hf⟩

end GlobalTheory.GridJoin
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsWeilOfEq

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GridJoin

theorem exists_isWeil_of_eq {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S S' T' Tg : HSp D} (hS : S = S') (hT : Tg = T')
    {χS χT : (AE D)ˣ →* Circle} (ω' : GlobalTheory.Grid.WRep S' T') (h : IsWeilDatumO ψ S' T' χS χT ω') :
    ∃ ω : GlobalTheory.Grid.WRep S Tg, GlobalTheory.Grid.IsWeil ψ false S Tg χS χT ω ∧ HEq ω ω' := by
  subst hS hT
  exact ⟨ω', h, HEq.rfl⟩

theorem omCol_of_weil : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ (t : T) j, j < D.R.m → ∃ ω : GlobalTheory.Grid.WRep (G.Xp j).V (G.nX j).V, GlobalTheory.Grid.IsWeil R.ψ false (G.Xp j).V (G.nX j).V (R.toLevCh.mu t (j + 1)) (R.toLevCh.mu t (j + 1)) ω ∧ HEq ω (W.om (.top t j)) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc _ _ _ F _ _ G' W hW G _ _ hSp _ t j hj
  have hS : (G.Xp j).V = G'.V (.top j) := (hSp.top j hj.le).sp
  have hT : (G.nX j).V = G'.V (.top (j + 1)) := (hSp.top (j + 1) hj).sp
  have hω := W.om_is (.top t j) (show j + 1 ≤ D.R.m from hj)
  have hr : ∀ k, k ≤ D.R.m → Even (G'.V (.top k)).rank := fun k hk => by
    have := (G'.isV (X := .top k) hk (fun _ h => by cases h)).rank
    rw [this]; exact even_rankX D k
  have eS : G'.chrS (.top t j) = R.toLevCh.mu t (j + 1) := by
    simp [GlobalTheory.ChiGrid.GridData.chrS, Formalism.IndefR.Lift.attChr, GlobalTheory.ChiGrid.GridData.chr, Nat.not_odd_iff_even.2 (hr j hj.le)]
  have eT : G'.chrT (.top t j) = R.toLevCh.mu t (j + 1) := by
    simp [GlobalTheory.ChiGrid.GridData.chrT, Formalism.IndefR.Lift.attChr, GlobalTheory.ChiGrid.GridData.chr, Nat.not_odd_iff_even.2 (hr (j + 1) hj)]
  rw [eS, eT, hW.ψ] at hω
  exact exists_isWeil_of_eq hS hT _ hω

end GlobalTheory.GridJoin
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNonzeroRealIntertwinerGridArrowStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_nonzero_real_intertwiner_grid_arrow : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ i j, i < D.R.m → j ≤ D.R.m → ∀ (ω : GlobalTheory.Grid.WRep (G.V (i + 1) j).V (G.V i j).V) (f : WO (G.V (i + 1) j).V (G.V i j).V → ℂ), GlobalTheory.Grid.IsWeil R.ψ true (G.V (i + 1) j).V (G.V i j).V (G.chiAt (D.R.m - i) (rkV D (i + 1) j)) (G.chiAt (D.R.m - i) (rkV D i j)) ω → GlobalTheory.Grid.IsVac R.ψ R.θ true (G.V (i + 1) j) (G.V i j) f → ∃ It : GlobalTheory.Grid.Pol (G.V (i + 1) j) (G.V i j) →ₗ[ℂ] SmT (G.V i j).M →ₗ[ℂ] SmT (G.V (i + 1) j).M, IsItW R.θ (G.V (i + 1) j).M (G.V i j).M ω (GlobalTheory.Grid.fock R.ψ R.θ true (G.V (i + 1) j) (G.V i j) f) It := by
  first | exact @GlobalTheory.GridJoin.ArrX.exists_intertwiner | exact GlobalTheory.GridJoin.ArrX.exists_intertwiner | (intros; apply GlobalTheory.GridJoin.ArrX.exists_intertwiner <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWrepOfEq

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GridJoin


open GlobalTheory.Grid GlobalTheory.ChiGrid in
theorem exists_wrep_of_eq {D : D7} {S T S' T' : HSp D} (hS : S = S') (hT : T = T') (ψ : AddChar (AF D.host.F) ℂ)
    (χ χ' : (AE D)ˣ →* Circle) (om : GA D (negSp S') × GA D T' →* Module.End ℂ (WO (negSp S') T' → ℂ))
    (h : IsWeilDatumO ψ (negSp S') T' χ χ' om) :
    ∃ ω : WRep S T, IsWeil ψ true S T χ χ' ω ∧ HEq (ω.toSgn true) om := by
  subst hS hT
  let ω : WRep S T := om.comp ((ofSgn true S).symm.toMonoidHom.prodMap (MonoidHom.id _))
  have e : ω.toSgn true = om := MonoidHom.ext fun x => rfl
  refine ⟨ω, ?_, heq_of_eq e⟩
  unfold IsWeil
  rw [e]
  exact h

theorem core_arrows_weil : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ i, i < D.R.m → ∃ ω : GlobalTheory.Grid.WRep (G.P (i + 1)).V (G.P i).V, GlobalTheory.Grid.IsWeil R.ψ true (G.P (i + 1)).V (G.P i).V (G.chi (D.R.m - i)) (G.chi (D.R.m - i)) ω ∧ HEq (ω.toSgn true) (W.om (.core i)) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc _ _ _ F _ _ G' W hW G _ _ hSp _ i hi
  have h1 : 1 ≤ D.R.m - i := by omega
  have h2 : D.R.m - i ≤ D.R.m := Nat.sub_le _ _
  have hom := W.om_is (.core i) (show (i + 1) ≤ D.R.m by omega)
  rw [(G'.chr_core (by omega : i + 1 ≤ D.R.m)).1, (G'.chr_core (by omega : i + 1 ≤ D.R.m)).2, hW.ψ,
    ← hSp.chi _ h1 h2] at hom
  exact exists_wrep_of_eq (hSp.core (i + 1) (by omega)).sp (hSp.core i (by omega)).sp _ _ _ _ hom

end GlobalTheory.GridJoin
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTestGridArrowsVacuaIntertwiners

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GridJoin

theorem exists_arrows : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∃ X ωT vacT ItT ωC vacC ItC dn ItU vC, (withArr G X ωT vacT ItT ωC vacC ItC dn ItU vC).IsArrows ∧ (withArr G X ωT vacT ItT ωC vacC ItC dn ItU vC).IsData ∧ ArrAgree (withArr G X ωT vacT ItT ωC vacC ItC dn ItU vC) W := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc hDC hHC hH hS F hR hsc G' W hW G hsp hch hag hcos
  have wX := GlobalTheory.GridJoin.exists_omX_of_agree hDC hHC hH hR hsc W hW G hsp hch hag hcos
  have vX := GlobalTheory.GridJoin.exists_vacX hDC hHC hH hR hsc W hW G hsp hch hag hcos
  have iX := GlobalTheory.T.exists_nonzero_real_intertwiner_grid_arrow hDC hHC hH hS hR hsc W hW G hsp hch hag hcos
  have wT := GlobalTheory.JoinArrows.exists_weil_rowArrow hDC hHC hH hR hsc W hW G hsp hch hag hcos
  have vT := GlobalTheory.GridJoin.exists_isVac_th_rows hDC hHC hH hR hsc W hW G hsp hch hag hcos
  have iT := GlobalTheory.T.gridRowArrow_exists_common_realIntertwiner hDC hHC hH hS hR hsc W hW G hsp hch hag hcos
  have wC := GlobalTheory.GridJoin.omCol_of_weil hDC hHC hH hR hsc W hW G hsp hch hag hcos
  have vC := GlobalTheory.GridJoin.exists_isVac_col hDC hHC hH hR hsc W hW G hsp hch hag hcos
  have iC := GlobalTheory.GridJoin.ColIt.exists_col_intertwiner hDC hHC hH hR hsc W hW G hsp hch hag hcos
  have wD := GlobalTheory.GridJoin.core_arrows_weil hDC hHC hH hR hsc W hW G hsp hch hag hcos
  have vD := GlobalTheory.GridJoin.exists_isVac_down hDC hHC hH hR hsc W hW G hsp hch hag hcos
  have iD := GlobalTheory.T.exists_downArrow_realIntertwiner_with_adjoint hDC hHC hH hR hsc W hW G hsp hch hag hcos
  have r0w := GlobalTheory.GridJoin.testGridRowZeroArrows_weil_vacua_agree hDC hHC hH hR hsc W hW G hsp hch hag hcos
  have r0i := GlobalTheory.GridJoin.RowArrows.chainIntertwiners_rowZero_unitVacua hDC hHC hH hR hsc W hW G hsp hch hag hcos
  have dT := GlobalTheory.T.exists_gridCosetData_eq_weilCosetVectors hDC hHC hH hR hsc W hW G hsp hch hag hcos
  have hXa : ∀ i j, ∃ a : GlobalTheory.Grid.ArrS (G.V (i + 1) j) (G.V i j), i < D.R.m → j ≤ D.R.m →
      a.Is R.ψ R.θ true (G.chiAt (D.R.m - i) (rkV D (i + 1) j)) (G.chiAt (D.R.m - i) (rkV D i j)) ∧
      HEq (a.ω.toSgn true) (W.om (.chi i j)) ∧ (j = 0 → HEq a.vac (W.vac i)) := by
    intro i j
    by_cases h : i < D.R.m ∧ j ≤ D.R.m
    · obtain ⟨ω, hω, hωa⟩ := wX i j h.1 h.2
      obtain ⟨f, hf, hf0⟩ := vX i j h.1 h.2
      obtain ⟨It, hIt⟩ := iX i j h.1 h.2 ω f hω hf
      exact ⟨⟨ω, f, It⟩, fun _ _ => ⟨⟨hω, hf, hIt⟩, hωa, hf0⟩⟩
    · exact ⟨⟨1, 0, 0⟩, fun a b => absurd ⟨a, b⟩ h⟩
  choose X hX using hXa
  have hTa : ∀ i j, ∃ (ω : T → GlobalTheory.Grid.WRep (G.nV i j).V (G.nV i (j + 1)).V) (f : WO (G.nV i j).V (G.nV i (j + 1)).V → ℂ)
      (It : GlobalTheory.Grid.Pol (G.nV i j) (G.nV i (j + 1)) →ₗ[ℂ] SmT (G.nV i (j + 1)).M →ₗ[ℂ] SmT (G.nV i j).M),
      i + 1 ≤ D.R.m → j < D.R.m → ∀ t, (⟨ω t, f, It⟩ : GlobalTheory.Grid.ArrS (G.nV i j) (G.nV i (j + 1))).Is R.ψ R.θ false
        (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D (i + 1) j)) (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D (i + 1) (j + 1))) ∧
        HEq (ω t) (W.om (.mu t (i + 1) j)) := by
    intro i j
    by_cases h : i + 1 ≤ D.R.m ∧ j < D.R.m
    · choose ω hω hωa using fun t => wT t i j h.1 h.2
      obtain ⟨f, hf⟩ := vT i j h.1 h.2
      obtain ⟨It, hIt⟩ := iT i j h.1 h.2 ω f hω hf
      exact ⟨ω, f, It, fun _ _ t => ⟨⟨hω t, hf, hIt t⟩, hωa t⟩⟩
    · exact ⟨fun _ => 1, 0, 0, fun a b => absurd ⟨a, b⟩ h⟩
  choose ωT vacT ItT hT using hTa
  have hCa : ∀ j, ∃ (ω : T → GlobalTheory.Grid.WRep (G.Xp j).V (G.nX j).V) (f : WO (G.Xp j).V (G.nX j).V → ℂ)
      (It : GlobalTheory.Grid.Pol (G.Xp j) (G.nX j) →ₗ[ℂ] SmT (G.Xp j).M →ₗ[ℂ] SmT (G.nX j).M),
      j < D.R.m → ∀ t, (⟨ω t, f, It⟩ : GlobalTheory.Grid.ArrT (G.Xp j) (G.Xp (j + 1))).Is R.ψ R.θ false
        (R.toLevCh.mu t (j + 1)) (R.toLevCh.mu t (j + 1)) ∧ HEq (ω t) (W.om (.top t j)) := by
    intro j
    by_cases h : j < D.R.m
    · choose ω hω hωa using fun t => wC t j h
      obtain ⟨f, hf⟩ := vC j h
      obtain ⟨It, hIt⟩ := iC j h ω f hω hf
      exact ⟨ω, f, It, fun _ t => ⟨⟨hω t, hf, hIt t⟩, hωa t⟩⟩
    · exact ⟨fun _ => 1, 0, 0, fun a => absurd a h⟩
  choose ωC vacC ItC hC using hCa
  have hDa : ∀ i, ∃ (a : GlobalTheory.Grid.ArrT (G.P (i + 1)) (G.P i))
      (U : GlobalTheory.Grid.Pol (G.P (i + 1)) (G.P i) →ₗ⋆[ℂ] SmT (G.P i).M →ₗ[ℂ] SmT (G.P (i + 1)).M), i < D.R.m →
      a.Is R.ψ R.θ true (G.chi (D.R.m - i)) (G.chi (D.R.m - i)) ∧ a.IsAdj U ∧ HEq (a.ω.toSgn true) (W.om (.core i)) := by
    intro i
    by_cases h : i < D.R.m
    · obtain ⟨ω, hω, hωa⟩ := wD i h
      obtain ⟨f, hf⟩ := vD i h
      obtain ⟨It, U, hIt, hU⟩ := iD i h ω f hω hf
      exact ⟨⟨ω, f, It⟩, U, fun _ => ⟨⟨hω, hf, hIt⟩, hU, hωa⟩⟩
    · exact ⟨⟨1, 0, 0⟩, 0, fun a => absurd a h⟩
  choose dn ItU hD using hDa
  have hVa : ∀ i, ∃ v : G.toGridSp.Cos R i → (WO (G.V (i + 1) 0).V (G.V i 0).V → ℂ), i < D.R.m →
      (∀ c, GlobalTheory.Grid.IsCosetVec R.ψ true (G.V (i + 1) 0) (G.V i 0) G.idem (G.lvl R) c (X i 0).vac (v c)) ∧
      (∀ c, ∃ κ, HEq (v c) (W.cosVec i κ)) ∧ ∀ κ, ∃ c, HEq (v c) (W.cosVec i κ) := by
    intro i
    by_cases h : i < D.R.m
    · obtain ⟨v, hv⟩ := dT i h (X i 0).vac ((hX i 0 h (Nat.zero_le _)).2.2 rfl)
      exact ⟨v, fun _ => hv⟩
    · exact ⟨fun _ _ => 0, fun h' => absurd h' h⟩
  choose vCo hvC using hVa
  refine ⟨X, fun t i j => ωT i j t, vacT, ItT, fun t j => ωC j t, vacC, ItC, dn, ItU, vCo,
    ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact fun i j hi hj => (hX i j hi hj).1
  · intro t i j hi hj
    cases i with
    | zero => exact ⟨(r0w t j hj).1, (r0w t j hj).2.1, r0i t j hj⟩
    | succ i => exact (hT i j hi hj t).1
  · exact fun t j hj => (hC j hj t).1
  · exact fun i hi => (hD i hi).1
  · exact fun i hi => (hD i hi).2.1
  · exact fun i hi c => (hvC i hi).1 c
  · exact fun i j hi hj => (hX i j hi hj).2.1
  · intro t i j hi hj
    cases i with
    | zero => exact (r0w t j hj).2.2
    | succ i => exact (hT i j hi hj t).2
  · exact fun t j hj => (hC j hj t).2
  · exact fun i hi => (hD i hi).2.2
  · exact fun i hi => (hX i 0 hi (Nat.zero_le _)).2.2 rfl
  · exact fun i hi => (hvC i hi).2

end GlobalTheory.GridJoin

end
end
end
