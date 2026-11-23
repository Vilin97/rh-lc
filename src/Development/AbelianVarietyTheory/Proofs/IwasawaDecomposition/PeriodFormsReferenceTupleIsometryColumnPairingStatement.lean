module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralFormsHermLatticeGoodAndComplexBasisStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InnerEqOfNormSq
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MinkowskiBoundComapLattice
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClassSumPairingOfIsFormsOf
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkMapInitMinor
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
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClassSumPairingFormsLat
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodRelationPreservesLevelFormLatticeNormStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFormMetricEqClassSumMetricStatement
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormAtSqIntegralFormEqClassSumMetric

section

@[expose] public section

noncomputable section

namespace GlobalTheory.Mem.Df

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df
open scoped Matrix ComplexOrder

attribute [local instance] GlobalTheory.Mem.Col2.starE

theorem map_conj_bVV {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (φ : K →+* ℂ)
    (i : VVIdx lam) :
    MvPolynomial.map ((starRingEnd ℂ).comp φ) (bVV K lam i : VV K lam).1 = MvPolynomial.map φ (bVV K lam i : VV K lam).1 := by
  obtain ⟨Q, hQ⟩ := bVVfun_int K lam i
  rw [bVV_coe, hQ, MvPolynomial.map_map, MvPolynomial.map_map]
  rw [RingHom.ext_int (((starRingEnd ℂ).comp φ).comp (Int.castRingHom K)) (φ.comp (Int.castRingHom K))]

theorem map_smul_pol {K : Type} [Field K] {σ : Type} (φ : K →+* ℂ) (r : K) (p : MvPolynomial σ K) :
    MvPolynomial.map φ (r • p) = φ r • MvPolynomial.map φ p := by
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C]

theorem pairB_conj_map {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (φ : K →+* ℂ)
    (y : VV K lam) :
    pairB lam (MvPolynomial.map (starRingEnd ℂ) (MvPolynomial.map φ y.1)) (MvPolynomial.map φ y.1) =
      star (fun i => φ ((bVV K lam).repr y i)) ⬝ᵥ (GlobalTheory.TestLat.Compare.gramB K lam).map φ *ᵥ (fun i => φ ((bVV K lam).repr y i)) := by
  have hy : y.1 = ∑ i, (bVV K lam).repr y i • (bVV K lam i : VV K lam).1 := by
    conv_lhs => rw [← (bVV K lam).sum_repr y]
    rw [Submodule.coe_sum]
    rfl
  rw [MvPolynomial.map_map, hy]

  simp only [map_sum, map_smul_pol, map_conj_bVV, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
  ← GlobalTheory.PeriodOnStep.map_pairB, dotProduct, Matrix.mulVec, Matrix.map_apply, GlobalTheory.TestLat.Compare.gramB, Matrix.of_apply, pairBK_apply,
  Pi.star_apply, RingHom.comp_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [starRingEnd_apply]
  ring

theorem herm_mk {K : Type} [Field K] {ι : Type} [Fintype ι] (M : Matrix ι ι K) (φ : K →+* ℂ) (hM : (M.map φ).PosDef)
    (a : ι → K) :
    star (fun i => (InfinitePlace.mk φ).embedding (a i)) ⬝ᵥ M.map (InfinitePlace.mk φ).embedding *ᵥ
        (fun i => (InfinitePlace.mk φ).embedding (a i)) =
      star (fun i => φ (a i)) ⬝ᵥ M.map φ *ᵥ (fun i => φ (a i)) := by
  rcases InfinitePlace.embedding_mk_eq φ with h | h
  · rw [h]
  · rw [h]
    have hr := hM.posSemidef.dotProduct_mulVec_nonneg (fun i => φ (a i))
    have hc : starRingEnd ℂ (star (fun i => φ (a i)) ⬝ᵥ M.map φ *ᵥ (fun i => φ (a i))) =
        star (fun i => φ (a i)) ⬝ᵥ M.map φ *ᵥ (fun i => φ (a i)) :=
      Complex.conj_eq_iff_im.2 (Complex.nonneg_iff.1 hr).2.symm
    rw [← hc]

    simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply, ComplexEmbedding.conjugate_coe_eq, map_sum,
    map_mul, starRingEnd_apply, star_star]

theorem normAt_sq_eq_cSum {B : Base} {X : PreX B.toPre} (I : TC B X) (hX : B.fields.Ok) (a : I.ι) (x : (MtHL I hX a).V) :
    ((Formalism.HermitianLatticesTheory.normAt (MtHL I hX a).b (MtHL I hX a).X (InfinitePlace.mk B.embLL) x ^ 2 : ℝ) : ℂ) =
      cSum I hX a (toCx I hX a x) (toCx I hX a x) := by
  have h0 := (GlobalTheory.PeriodOnStep.isFormsOf_MtildeH B.wts I.Ch I.sel (I.tup a) I.Ps hX).2 (InfinitePlace.mk B.embLL)
  refine (h0 (x : (MtildeH B.wts I.Ch hX I.sel (I.tup a) I.Ps).V)).trans ?_
  rw [cSum_apply]
  unfold GSD.ipAt
  refine Finset.sum_congr rfl fun c _ => ?_
  unfold cTerm
  rw [GSD.wt_eq]
  congr 1
  rw [GlobalTheory.PeriodClassSum.pairAt_eq, GlobalTheory.PeriodClassSum.row_gramV]
  exact (herm_mk _ _ (GlobalTheory.PeriodClassSum.gramB_posDef _ _) _).trans (pairB_conj_map _ _ _).symm

end GlobalTheory.Mem.Df
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormAtSqIntegralFormEqClassSumMetricStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df
attribute [local instance] GlobalTheory.Mem.Col2.starE

theorem _root_.GlobalTheory.T.normAt_sq_integralForm_eq_classSumMetric : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (hX : B.fields.Ok) (a : I.ι) (x : (MtHL I hX a).V), ((Formalism.HermitianLatticesTheory.normAt (MtHL I hX a).b (MtHL I hX a).X (InfinitePlace.mk B.embLL) x ^ 2 : ℝ) : ℂ) = cSum I hX a (toCx I hX a x) (toCx I hX a x) := by
  first | exact @GlobalTheory.Mem.Df.normAt_sq_eq_cSum | exact GlobalTheory.Mem.Df.normAt_sq_eq_cSum | (intros; apply GlobalTheory.Mem.Df.normAt_sq_eq_cSum <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodFormsReferenceTupleIsometryColumnPairing

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.St

attribute [local instance] GlobalTheory.Mem.Col2.starE



theorem eMt0_isometry : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), K.Over B.toPre → Forced K B T →
    pinAnd HasPk K B f T w → ∀ (P : Pre2 K w) (x : St P) (hη : ∀ j v, 1 ≤ j → j ≤ B.R.m → x.o.η j v = P.q.eta j v), ∀ u F G, inner ℂ ((w.D x.o.Z).eMt u F) ((w.D x.o.Z).eMt u G) = TC.ipMt w.I w.l u w.I.mu0 F G := by
  intro K B f T w hO hF hP P x hη u F G
  show inner ℂ (P.q.e.e0 u F) (P.q.e.e0 u G) = _
  have hN : ∀ m : (Df.MtHL w.I P.hX w.I.mu0).V, Formalism.HermitianLatticesTheory.normAt (Df.MtHL w.I P.hX w.I.mu0).b (Df.MtHL w.I P.hX w.I.mu0).X
      (InfinitePlace.mk B.embLL) m = ‖P.q.per.e w.I.mu0 (Df.toCx w.I P.hX w.I.mu0 m)‖ :=
    GlobalTheory.T.periodRelation_preserves_levelForm_lattice_norm (w.st P.Z₀) w.I P.hX P.z.Xg P.z.tr w.I.mu0 (P.q.t.tA true w.I.mu0) (P.q.per.e w.I.mu0) (P.q.per.crd w.I.mu0)
  have hin : ∀ y y' : Df.MtCx w.I w.I.mu0, inner ℂ (P.q.per.e w.I.mu0 y) (P.q.per.e w.I.mu0 y') = Df.cSum w.I P.hX w.I.mu0 y y' := by
    intro y y'
    obtain ⟨-, ⟨j, hj⟩, -, hsp⟩ := GlobalTheory.T.integralFormsHermLattice_good_and_complexBasis w.I P.hX w.I.mu0
    obtain ⟨k, hk⟩ := Df.exists_embLL_im_ne (B := B) P.hX
    have hspan : Submodule.span ℂ (Set.range j) = ⊤ := by
      rw [eq_top_iff, ← hsp]
      exact Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨_, hj _⟩)
    exact Df.inner_eq_of_norm_sq B.embLL j hspan k hk (P.q.per.e w.I.mu0).toLinearMap (Df.cSum w.I P.hX w.I.mu0) (fun m => by
      rw [hj, LinearEquiv.coe_toLinearMap, ← hN m, GlobalTheory.T.normAt_sq_integralForm_eq_classSumMetric w.I P.hX w.I.mu0 m]) y y'
  have key : ∀ F : ((w.D x.o.Z).mem u).P.Mt,
      Df.SameForm w.I w.l u w.I.mu0 ((P.q.per.e w.I.mu0).symm (P.q.e.e0 u F)) F := fun F => by
    have h := P.q.per.ref u ((P.q.per.e w.I.mu0).symm (P.q.e.e0 u F))
    erw [LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply] at h
    exact h
  have h1 : ∀ F : ((w.D x.o.Z).mem u).P.Mt, P.q.e.e0 u F = P.q.per.e w.I.mu0 ((P.q.per.e w.I.mu0).symm (P.q.e.e0 u F)) :=
    fun F => ((P.q.per.e w.I.mu0).apply_symm_apply _).symm
  rw [h1 F, h1 G]
  exact (hin _ _).trans (GlobalTheory.T.rowFormMetric_eq_classSumMetric w.I w.ok w.pins w.l P.hX x.o.Z u w.I.mu0 F G _ _ (key F) (key G)).symm

end GlobalTheory.Mem.R3.Rw.St

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodFormsReferenceTupleIsometryColumnPairingStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

theorem _root_.GlobalTheory.T.periodForms_referenceTuple_isometry_column_pairing : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), K.Over B.toPre → Forced K B T →
    pinAnd HasPk K B f T w → ∀ (P : Pre2 K w) (x : St P) (hη : ∀ j v, 1 ≤ j → j ≤ B.R.m → x.o.η j v = P.q.eta j v), ∀ u F G, inner ℂ ((w.D x.o.Z).eMt u F) ((w.D x.o.Z).eMt u G) = TC.ipMt w.I w.l u w.I.mu0 F G := by
  first | exact @GlobalTheory.Mem.R3.Rw.St.eMt0_isometry | exact GlobalTheory.Mem.R3.Rw.St.eMt0_isometry | (intros; apply GlobalTheory.Mem.R3.Rw.St.eMt0_isometry <;> assumption)
end
end
