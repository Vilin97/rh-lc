module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassPresExtMemExtBijIsom
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanRangeMulVec
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HilbertInnerRowFormsEqLevelClassSumStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowLevelFormsSpanDefiniteMultiplicitySpace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchurOrthogonalityDimPairingEqInnerStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanLiftFormsBaseLevelEqHilbertImageStatement
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HilbertInnerLiftFormsEqBaseLevelHermitian

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
noncomputable section
namespace GlobalTheory.Mem.R3

theorem liftForm_inner_eq_hform : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → ∀ (i : Fin D.R.m) (t : T) (x y : Fin (lDim D A F.P0 F.ψ0 i t) → D.what₂.LL), (((RealDat.nP F false)⁻¹ : ℝ) : ℂ) * ⟪R.jV i t (liftForm A F.P0 F.ψ0 i t x), R.jV i t (liftForm A F.P0 F.ψ0 i t y)⟫_ℂ = D.what₂.embLL (Formalism.DivisionValues.hform (lH D A F.P0 F.ψ0 i t) x y) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hB i t x y
  have h1 : ∀ f g : (A.MtCSD i t).Forms, ⟪R.jV i t f, R.jV i t g⟫_ℂ = D.what₂.embLL ((A.MtCSD i t).csum f g) := by
    intro f g
    refine ((hB.models.HV i t).2.2 _ _).trans ?_
    refine (congrArg₂ _ (hB.models.jV i t f) (hB.models.jV i t g)).trans ?_
    exact (GlobalTheory.classPres_extMem_extBij_isom _ _ _ _ _ _ _ _ _ _ (R.B.L i t).pres).2.2 f g
  have h2 := GlobalTheory.Mem.LiftForms.csum_lvlForm (A.fam.L i t).S (A.fam.L i t).r (A.fam.lvlA F.P0 F.ψ0).P (A.fam.lvlA F.P0 F.ψ0).ψ x y
  have h3 : ⟪R.jV i t (liftForm A F.P0 F.ψ0 i t x), R.jV i t (liftForm A F.P0 F.ψ0 i t y)⟫_ℂ =
      D.what₂.embLL ((Nat.card (A.fam.lvlA F.P0 F.ψ0).P : D.what₂.LL) * Formalism.DivisionValues.hform (lH D A F.P0 F.ψ0 i t) x y) :=
    (h1 (liftForm A F.P0 F.ψ0 i t x) (liftForm A F.P0 F.ψ0 i t y)).trans (congrArg D.what₂.embLL h2)
  have hP : RealDat.nP F false = (Nat.card F.P0 : ℝ) := rfl
  have hc : (Nat.card F.P0 : ℂ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := F.P0)).ne'
  rw [h3, map_mul, map_natCast, hP, ← mul_assoc]
  change ((((Nat.card F.P0 : ℝ))⁻¹ : ℝ) : ℂ) * (Nat.card F.P0 : ℂ) * _ = _
  rw [Complex.ofReal_inv, Complex.ofReal_natCast, inv_mul_cancel₀ hc, one_mul]

end GlobalTheory.Mem.R3
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HilbertInnerLiftFormsEqBaseLevelHermitianStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

theorem _root_.GlobalTheory.T.hilbert_inner_liftForms_eq_base_level_hermitian : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → ∀ (i : Fin D.R.m) (t : T) (x y : Fin (lDim D A F.P0 F.ψ0 i t) → D.what₂.LL), (((RealDat.nP F false)⁻¹ : ℝ) : ℂ) * ⟪R.jV i t (liftForm A F.P0 F.ψ0 i t x), R.jV i t (liftForm A F.P0 F.ψ0 i t y)⟫_ℂ = D.what₂.embLL (Formalism.DivisionValues.hform (lH D A F.P0 F.ψ0 i t) x y) := by
  first | exact @GlobalTheory.Mem.R3.liftForm_inner_eq_hform | exact GlobalTheory.Mem.R3.liftForm_inner_eq_hform | (intros; apply GlobalTheory.Mem.R3.liftForm_inner_eq_hform <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowLevelFormsSpanDefiniteMultiplicitySpaceStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

theorem _root_.GlobalTheory.T.rowLevelForms_span_definiteMultiplicitySpace : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → Seed.PrIso R.MX R.cX R.prX → A.fam.Ok 1 → TopMultH R → ∀ (b : Bool) (t : T), Submodule.span ℂ (Set.range fun x => R.cX.toMap R.prX ((R.HX t).e (R.jX t (rowForm A (F.lvl b).P (F.lvl b).ψ t x)))) = Mult.MultT R.θ R.MX (levS _ R.βX (datXP R t (R.levR F b))) (levChi _ R.βX (datXP R t (R.levR F b))) := by
  first | exact @GlobalTheory.TopSpan.topSpan | exact GlobalTheory.TopSpan.topSpan | (intros; apply GlobalTheory.TopSpan.topSpan <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassSumsEqPairingsTopChainLifts

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.TopNorm

theorem ipVia_self {H N : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [AddCommGroup N] [Module ℂ N]
    (e : H →ₗ[ℂ] N) (he : Function.Injective e) (u v : H) : ipVia e (e u) (e v) = ⟪u, v⟫_ℂ := by
  unfold ipVia
  split_ifs with h
  · have h1 : h.1.choose = u := he h.1.choose_spec
    have h2 : h.2.choose = v := he h.2.choose_spec
    rw [h1, h2]
  · exact absurd ⟨⟨u, rfl⟩, ⟨v, rfl⟩⟩ h



theorem classSums_topNorm : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : TopMultH R) (hinj : ∀ i t, Function.Injective (R.extV i t)), R.BaseW F → Seed.PrIso R.MX R.cX R.prX → A.fam.Ok 1 → let C := toChainReal R F tupT hm hTop; let L := toLiftReal R F tupT hm hTop hinj; ∀ μ : D.what₂.Tup, (let a := fun x => R.cX.toMap R.prX ((R.HX (tupT μ)).e (R.jX (tupT μ) (rowForm A F.P1 F.ψ1 (tupT μ) x))); Submodule.span ℂ (Set.range a) = C.CCXP true μ ∧ ∀ x y, C.ipXP true μ (a x) (a y) = D.what₂.embLL (Formalism.DivisionValues.hform (rH D A F.P1 F.ψ1 (tupT μ)) x y)) ∧ (let a := fun x => R.cX.toMap R.prX ((R.HX (tupT μ)).e (R.jX (tupT μ) (rowForm A F.P0 F.ψ0 (tupT μ) x))); Submodule.span ℂ (Set.range a) = C.CCXP false μ ∧ ∀ x y, C.ipXP false μ (a x) (a y) = D.what₂.embLL (Formalism.DivisionValues.hform (rH D A F.P0 F.ψ0 (tupT μ)) x y)) ∧ ∀ i : Fin D.R.m, (let a := fun x => R.extV i (tupT μ) (R.jV i (tupT μ) (liftForm A F.P0 F.ψ0 i (tupT μ) x)); Submodule.span ℂ (Set.range a) = L.Amt μ i ∧ ∀ x y, L.ipA μ i (a x) (a y) = D.what₂.embLL (Formalism.DivisionValues.hform (lH D A F.P0 F.ψ0 i (tupT μ)) x y)) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F tupT hm hTop hinj hB hPr hOk C L μ
  refine ⟨⟨GlobalTheory.T.rowLevelForms_span_definiteMultiplicitySpace D G Pl0 T A Ks R F hB hPr hOk hTop true (tupT μ), fun x y => ?_⟩,
    ⟨GlobalTheory.T.rowLevelForms_span_definiteMultiplicitySpace D G Pl0 T A Ks R F hB hPr hOk hTop false (tupT μ), fun x y => ?_⟩,
    fun i => ⟨GlobalTheory.T.span_liftForms_baseLevel_eq_hilbertImage D G Pl0 T A Ks R F hB hOk hinj i (tupT μ), fun x y => ?_⟩⟩
  · have h1 := GlobalTheory.T.schur_orthogonality_dim_pairing_eq_inner D G Pl0 T A Ks R F hB hPr (tupT μ) (R.jX (tupT μ) (rowForm A F.P1 F.ψ1 (tupT μ) x))
      (R.jX (tupT μ) (rowForm A F.P1 F.ψ1 (tupT μ) y))
    have h3 := GlobalTheory.T.hilbert_inner_rowForms_eq_level_class_sum D G Pl0 T A Ks R F hB true (tupT μ) x y
    have e1 : ((((∏ τ, (Module.finrank ℂ (R.MX.H τ) : ℝ)) / (1 : ℝ) : ℝ) : ℂ)) =
        (((∏ τ, (Module.finrank ℂ (R.MX.H τ) : ℝ)) : ℝ) : ℂ) :=
      congrArg (fun r : ℝ => (r : ℂ)) (div_one (∏ τ, (Module.finrank ℂ (R.MX.H τ) : ℝ)))
    refine Eq.trans ?_ h3
    show (((RealDat.nP F true)⁻¹ : ℝ) : ℂ) * ((((∏ τ, (Module.finrank ℂ (R.MX.H τ) : ℝ)) / (1 : ℝ) : ℝ) : ℂ) *
        ipMT R.MX (R.νX (tupT μ)) (R.fdX (tupT μ))
          (R.cX.toMap R.prX ((R.HX (tupT μ)).e (R.jX (tupT μ) (rowForm A F.P1 F.ψ1 (tupT μ) x))))
          (R.cX.toMap R.prX ((R.HX (tupT μ)).e (R.jX (tupT μ) (rowForm A F.P1 F.ψ1 (tupT μ) y))))) = _
    exact congrArg (fun z : ℂ => (((RealDat.nP F true)⁻¹ : ℝ) : ℂ) * z) ((congrArg (· * _) e1).trans h1)
  · have h1 := GlobalTheory.T.schur_orthogonality_dim_pairing_eq_inner D G Pl0 T A Ks R F hB hPr (tupT μ) (R.jX (tupT μ) (rowForm A F.P0 F.ψ0 (tupT μ) x))
      (R.jX (tupT μ) (rowForm A F.P0 F.ψ0 (tupT μ) y))
    have h3 := GlobalTheory.T.hilbert_inner_rowForms_eq_level_class_sum D G Pl0 T A Ks R F hB false (tupT μ) x y
    have e1 : ((((∏ τ, (Module.finrank ℂ (R.MX.H τ) : ℝ)) / (1 : ℝ) : ℝ) : ℂ)) =
        (((∏ τ, (Module.finrank ℂ (R.MX.H τ) : ℝ)) : ℝ) : ℂ) :=
      congrArg (fun r : ℝ => (r : ℂ)) (div_one (∏ τ, (Module.finrank ℂ (R.MX.H τ) : ℝ)))
    refine Eq.trans ?_ h3
    show (((RealDat.nP F false)⁻¹ : ℝ) : ℂ) * ((((∏ τ, (Module.finrank ℂ (R.MX.H τ) : ℝ)) / (1 : ℝ) : ℝ) : ℂ) *
        ipMT R.MX (R.νX (tupT μ)) (R.fdX (tupT μ))
          (R.cX.toMap R.prX ((R.HX (tupT μ)).e (R.jX (tupT μ) (rowForm A F.P0 F.ψ0 (tupT μ) x))))
          (R.cX.toMap R.prX ((R.HX (tupT μ)).e (R.jX (tupT μ) (rowForm A F.P0 F.ψ0 (tupT μ) y))))) = _
    exact congrArg (fun z : ℂ => (((RealDat.nP F false)⁻¹ : ℝ) : ℂ) * z) ((congrArg (· * _) e1).trans h1)
  · have h5 := GlobalTheory.T.hilbert_inner_liftForms_eq_base_level_hermitian D G Pl0 T A Ks R F hB i (tupT μ) x y
    refine Eq.trans ?_ h5
    show (((RealDat.nP F false)⁻¹ : ℝ) : ℂ) * ipVia (R.extV i (tupT μ))
      (R.extV i (tupT μ) (R.jV i (tupT μ) (liftForm A F.P0 F.ψ0 i (tupT μ) x)))
      (R.extV i (tupT μ) (R.jV i (tupT μ) (liftForm A F.P0 F.ψ0 i (tupT μ) y))) = _
    exact congrArg (fun z : ℂ => (((RealDat.nP F false)⁻¹ : ℝ) : ℂ) * z) (ipVia_self _ (hinj i (tupT μ)) _ _)

end GlobalTheory.TopNorm

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassSumsEqPairingsTopChainLiftsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

theorem _root_.GlobalTheory.T.classSums_eq_pairings_topChain_lifts : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : TopMultH R) (hinj : ∀ i t, Function.Injective (R.extV i t)), R.BaseW F → Seed.PrIso R.MX R.cX R.prX → A.fam.Ok 1 → let C := toChainReal R F tupT hm hTop; let L := toLiftReal R F tupT hm hTop hinj; ∀ μ : D.what₂.Tup, (let a := fun x => R.cX.toMap R.prX ((R.HX (tupT μ)).e (R.jX (tupT μ) (rowForm A F.P1 F.ψ1 (tupT μ) x))); Submodule.span ℂ (Set.range a) = C.CCXP true μ ∧ ∀ x y, C.ipXP true μ (a x) (a y) = D.what₂.embLL (Formalism.DivisionValues.hform (rH D A F.P1 F.ψ1 (tupT μ)) x y)) ∧ (let a := fun x => R.cX.toMap R.prX ((R.HX (tupT μ)).e (R.jX (tupT μ) (rowForm A F.P0 F.ψ0 (tupT μ) x))); Submodule.span ℂ (Set.range a) = C.CCXP false μ ∧ ∀ x y, C.ipXP false μ (a x) (a y) = D.what₂.embLL (Formalism.DivisionValues.hform (rH D A F.P0 F.ψ0 (tupT μ)) x y)) ∧ ∀ i : Fin D.R.m, (let a := fun x => R.extV i (tupT μ) (R.jV i (tupT μ) (liftForm A F.P0 F.ψ0 i (tupT μ) x)); Submodule.span ℂ (Set.range a) = L.Amt μ i ∧ ∀ x y, L.ipA μ i (a x) (a y) = D.what₂.embLL (Formalism.DivisionValues.hform (lH D A F.P0 F.ψ0 i (tupT μ)) x y)) := by
  first | exact @GlobalTheory.TopNorm.classSums_topNorm | exact GlobalTheory.TopNorm.classSums_topNorm | (intros; apply GlobalTheory.TopNorm.classSums_topNorm <;> assumption)
end
end
