module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsComplexificationOfDefiniteGroupFormsStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ISupIndepFiniteTypeComponentsThetaLiftForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHermPosChainRealEndSpaceTuple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFiniteTypesIsotypicPartsSpanOrthogonal
public import Formalism.LocalToGlobal.IndefiniteReal.LinIndepOfOrth
import Formalism.LocalToGlobal.IndefiniteReal.LinksExistW
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Formalism.LocalToGlobal.IndefiniteReal.CompZeroOfOrth
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelChainOverTopSpaces
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLiftSpacesOverDefiniteFormsStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowBasisFromReferenceTupleQuotientStatement
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteRepresentativesRowFiniteTypes

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

noncomputable section

namespace GlobalTheory.RowTypeReps



theorem reps_exist : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Inputs D → Pins R F cG → Holds R F → ∀ (y : Hd R.toRealDat), ∃ (Φ : Type) (rep : Φ → Formalism.L2.NG.FinTyp D.host.E D.R.r), Reps y F.lv2 rep := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hI hP _ y
  have hB := hP.char.base
  have h0 := hB.models.ν0
  have hD : ∀ b, principalLevelFrame.IsotDecomp R.θ y.PY (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b)))
      (levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b))) R.e0 R.ν0 R.fd0 := by
    intro b
    obtain ⟨h1, h2⟩ := GlobalTheory.FinTypesRows.isotL_span_orth D (Yc D 0) _ R.θ (R.MY 0) y.PY y.hF (R.βY 0)
      (R.dat0 (R.toRealDat.levR F.lv2 b)) R.e0 _ _ hI (D.sp.Y_sig _) hB.models.inf y.stdPsi.1 h0.1.1 h0.2
      (GlobalTheory.Mem.R3.IsotIndep.gaL_finSum _ _ _ _ _)
    exact ⟨h1.symm, h2⟩

  have hp : ∀ b, PeterssonHilbertSpace.IsHermPos (Mult.goodPart R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b)))
      (levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b))) R.e0) (Mult.ipM (R.MY 0) R.ν0 R.fd0) := by
    intro b
    have h1 := hermPos_mono (GlobalTheory.HilbertLevels.herm_lev hI hB.models.inf (D.sp.Y_sig _) (R.MY 0) (R.βY 0)
      (R.dat0 (R.toRealDat.levR F.lv2 b)) h0.1.1 h0.2) (Submodule.map_mono (Mult.goodPart_le R.θ (R.MY 0) _ _ R.e0))
    have h2 := h1.map_equiv (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _).symm
    convert h2 using 1
    · ext x
      rw [Submodule.mem_map_equiv, LinearEquiv.symm_symm, Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]
    · funext x x'
      simp only [ipMT, LinearEquiv.symm_symm, LinearEquiv.symm_apply_apply]
  haveI := principalLevelFrame.finite_FTR R.θ y.PY (R.MY 0) (fun b => levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b)))
    (fun b => levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b))) (fun _ => R.e0) (fun _ => R.ν0) (fun _ => R.fd0) hD hp
  refine ⟨principalLevelFrame.FTR R.θ y.PY (R.MY 0) (fun b => levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b)))
    (fun b => levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b))) (fun _ => R.e0), principalLevelFrame.rowRepR R.θ,
    ⟨inferInstance, fun π => principalLevelFrame.rowRepR_occ R.θ π, fun π π' h => principalLevelFrame.rowRepR_inj R.θ π π' h, ?_⟩⟩
  intro ρ hρ
  exact ⟨Quotient.mk _ ⟨ρ, hρ⟩, Formalism.L2.Col.finTypRep_mk_iso ⟨ρ, hρ⟩⟩

end GlobalTheory.RowTypeReps
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteRepresentativesRowFiniteTypesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

theorem _root_.GlobalTheory.T.exists_finite_representatives_rowFiniteTypes : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Inputs D → Pins R F cG → Holds R F → ∀ (y : Hd R.toRealDat), ∃ (Φ : Type) (rep : Φ → Formalism.L2.NG.FinTyp D.host.E D.R.r), Reps y F.lv2 rep := by
  first | exact @GlobalTheory.RowTypeReps.reps_exist | exact GlobalTheory.RowTypeReps.reps_exist | (intros; apply GlobalTheory.RowTypeReps.reps_exist <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelChainOverTopSpacesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

theorem _root_.GlobalTheory.T.exists_levelChain_over_top_spaces : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Inputs D → Pins R F cG → Holds R F → ∀ (y : Hd R.toRealDat), ∀ (Φ : Type) (rep : Φ → Formalism.L2.NG.FinTyp D.host.E D.R.r), Reps y F.lv2 rep → ∀ (b : Bool) (m : D.what₂.Tup → Mat1 D.what₂.LL G) (s : D.what₂.Tup → Sp1 D.what₂.O (D.what₂.embLL.comp D.what₂.OtoLL) G) (tA : ∀ μ, Tie1 D.what₂.embLL (m μ) (s μ)) (hA : ∀ t, m (y.tup t) = rMat A3.A (levP F.lv2 b).1 (levP F.lv2 b).2 t), ∃ c : ChD D.what₂.Tup Φ D.R.m fun μ => (s μ).A, Nonempty (ChT y F.lv2 b rep (Top := fun μ => (s μ).A) (fun t x => ((tA (y.tup t)).cast (hA t)).j x) c) := by
  first | exact @GlobalTheory.Mem.R3.Rw.ChainLevel.chain_exists | exact GlobalTheory.Mem.R3.Rw.ChainLevel.chain_exists | (intros; apply GlobalTheory.Mem.R3.Rw.ChainLevel.chain_exists <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowLiftReadingDefiniteFormCoordinates

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.Mem.R3.Rw.PkRead



theorem exists_pkT : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), (∀ o : D.what₂.O, ∃ k : Ks, algebraMap Ks D.what₂.LL k = D.what₂.OtoLL o) → Inputs D → Pins R F cG → Holds R F → ∀ (y : Hd R.toRealDat), ∀ (mA : Bool → D.what₂.Tup → Mat1 D.what₂.LL G) (mL : D.what₂.Tup → ℕ → Mat1 D.what₂.LL G), (∀ b μ, (mA b μ).Laws D.what₂.embLL (idemOf A3.A.X)) → (∀ μ j, (mL μ j).Laws D.what₂.embLL (idemOf A3.A.X)) → (∀ b t, mA b (y.tup t) = rMat A3.A (levP F.lv2 b).1 (levP F.lv2 b).2 t) → (∀ (i : Fin D.R.m) t, mL (y.tup t) ((i : ℕ) + 1) = lMat A3.A F.lv2.P0 F.lv2.ψ0 i t) → ∃ p : PkD D G, p.mL = mL ∧ Nonempty (PkT F y mA p) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hO hI hP hH y mA mL hA hL hAe hLe
  obtain ⟨Φ, rep, hrep⟩ := GlobalTheory.T.exists_finite_representatives_rowFiniteTypes D G Pl0 I0 T A3 Ks R F cG hI hP hH y
  have hstar : ∀ x, D.what₂.embLL (star x) = starRingEnd ℂ (D.what₂.embLL x) := D.starLL_cx
  have hint : ∀ z, IsIntegral ℤ (D.what₂.OtoLL z) := D.O_int
  choose sA tA using fun b μ =>
    GlobalTheory.T.exists_complexification_of_definiteGroupForms' D.what₂.LL D.what₂.O D.what₂.OtoLL D.what₂.embLL G (mA b μ) (idemOf A3.A.X) hstar hint (hA b μ)
  choose sL tL using fun μ j =>
    GlobalTheory.T.exists_complexification_of_definiteGroupForms' D.what₂.LL D.what₂.O D.what₂.OtoLL D.what₂.embLL G (mL μ j) (idemOf A3.A.X) hstar hint (hL μ j)
  let tA' : ∀ b μ, Tie1 D.what₂.embLL (mA b μ) (sA b μ) := fun b μ => (tA b μ).some
  let tL' : ∀ μ j, Tie1 D.what₂.embLL (mL μ j) (sL μ j) := fun μ j => (tL μ j).some
  choose c hc using fun b =>
    GlobalTheory.T.exists_levelChain_over_top_spaces D G Pl0 I0 T A3 Ks R F cG hI hP hH y Φ rep hrep b (mA b) (sA b) (tA' b) (hAe b)
  obtain ⟨l, hl⟩ := GlobalTheory.T.exists_lift_spaces_over_definite_forms D G Pl0 I0 T A3 Ks R F cG hO hI hP hH y Φ rep hrep mL sL tL' hLe
  let chT := fun b => (hc b).some
  obtain ⟨nR, cR, Xo, hrr⟩ := GlobalTheory.T.exists_rowBasis_from_referenceTuple_quotient D G Pl0 I0 T A3 Ks R F cG hP hH y true (c true).EE (chT true).jE
    (chT true).jE_inj (chT true).jE_range
  haveI : Finite Φ := hrep.fin
  letI : Fintype Φ := Fintype.ofFinite Φ
  classical

  have hθ : IsInfFam R.θ := hP.char.base.models.inf
  have hfin : FiniteDimensional ℂ (Mult.Mult R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 true)))
      (levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 true)))) :=
    hI.hc (Yc D 0) (D.sp.Y_sig _) _ R.θ (R.MY 0) _ _ hθ (hI.lev (Yc D 0) (R.βY 0) _).2
  set Dall := Module.finrank ℂ (Mult.Mult R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 true)))
      (levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 true)))) with hDall
  have hn : Dall = 0 → (c true).n = 0 := by
    intro h0
    have hM : Mult.Mult R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 true)))
        (levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 true))) = ⊥ :=
      Submodule.finrank_eq_zero.1 h0
    have hE : (y.C F.lv2).EEc true = ⊥ := by
      show (Mult.goodPart R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 true)))
        (levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 true))) R.e0).map _ = ⊥
      rw [eq_bot_iff.2 ((Mult.goodPart_le _ _ _ _ _).trans hM.le)]
      exact Submodule.map_bot _
    have hr := (chT true).jE_range
    rw [hE] at hr
    have h1 := LinearMap.finrank_range_of_inj (chT true).jE_inj
    rw [hr, finrank_bot] at h1
    have h2 := Module.finrank_eq_card_basis (c true).bs.toBasis
    rw [← h1, Fintype.card_fin] at h2
    exact h2.symm
  let dp : ℝ := if Dall = 0 then 0 else 1 - ((c true).n : ℝ) / Dall
  have hdelp : dp ≤ 1 := by
    simp only [dp]
    split_ifs
    · norm_num
    · have : (0 : ℝ) ≤ ((c true).n : ℝ) / Dall := by positivity
      linarith
  have hD : (((c true).n : ℕ) : ℝ) = (1 - dp) * Dall := by
    simp only [dp]
    split_ifs with h
    · rw [hn h, h]; simp
    · have : (Dall : ℝ) ≠ 0 := by exact_mod_cast h
      field_simp
      ring
  refine ⟨{ Φ := Φ, sA := sA, mL := mL, sL := sL, tL := tL', ch := c, lf := l, Dall := Dall, delp := dp, delp_le_one := hdelp, D_eq := hD, nR := nR, cR := cR, Xo := Xo }, rfl, ⟨?_⟩⟩
  exact { rep := rep, reps := hrep, tA := tA', lawsA := hA, lawsL := hL, hA := hAe, hL := hLe, ch := chT, lf := hl.some, dall := rfl, rr := hrr }

end GlobalTheory.Mem.R3.Rw.PkRead
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowLiftReadingDefiniteFormCoordinatesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

theorem _root_.GlobalTheory.T.exists_rowLiftReading_definiteFormCoordinates : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), (∀ o : D.what₂.O, ∃ k : Ks, algebraMap Ks D.what₂.LL k = D.what₂.OtoLL o) → Inputs D → Pins R F cG → Holds R F → ∀ (y : Hd R.toRealDat), ∀ (mA : Bool → D.what₂.Tup → Mat1 D.what₂.LL G) (mL : D.what₂.Tup → ℕ → Mat1 D.what₂.LL G), (∀ b μ, (mA b μ).Laws D.what₂.embLL (idemOf A3.A.X)) → (∀ μ j, (mL μ j).Laws D.what₂.embLL (idemOf A3.A.X)) → (∀ b t, mA b (y.tup t) = rMat A3.A (levP F.lv2 b).1 (levP F.lv2 b).2 t) → (∀ (i : Fin D.R.m) t, mL (y.tup t) ((i : ℕ) + 1) = lMat A3.A F.lv2.P0 F.lv2.ψ0 i t) → ∃ p : PkD D G, p.mL = mL ∧ Nonempty (PkT F y mA p) := by
  first | exact @GlobalTheory.Mem.R3.Rw.PkRead.exists_pkT | exact GlobalTheory.Mem.R3.Rw.PkRead.exists_pkT | (intros; apply GlobalTheory.Mem.R3.Rw.PkRead.exists_pkT <;> assumption)
end
end
