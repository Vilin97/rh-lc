module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AsIdealSpMapClosedPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommonRestrIsoTens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormRatiosGenerateAtFlagSpaceGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivLeSubMulDiv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeparatesOnSmoothOfPair
public import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
public import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
public import Mathlib.LinearAlgebra.Matrix.Block
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointEigenbasisBaseChange
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsCombAtGMulVec
public import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
public import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPf
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameBorelGroupoidProperties
import Mathlib.Algebra.Order.Star.Int
import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings

-- Source module: Development.AbelianVarietyTheory.Proofs.GenericRegularity.EqOfUnitriangularOfEqLowerMul

section

@[expose] public section

namespace GlobalTheory.UnitriangularLowerMulEq

open Matrix

theorem eq_of_unitriangular_of_eq_lower_mul {S : Type} [inst : CommRing S] {n : ℕ}
    (A A' L : Matrix (Fin n) (Fin n) S)
    (hA : ∀ (i j : Fin n), j < i → A i j = (0 : S)) (hA1 : ∀ (i : Fin n), A i i = (1 : S))
    (hA' : ∀ (i j : Fin n), j < i → A' i j = (0 : S)) (hA'1 : ∀ (i : Fin n), A' i i = (1 : S))
    (hL : ∀ (i j : Fin n), i < j → L i j = (0 : S)) (h : A' = L * A) : A' = A := by
  classical
  have hAb : A.BlockTriangular id := fun i j hji => hA i j hji
  have hA'b : A'.BlockTriangular id := fun i j hji => hA' i j hji
  have hdet : A.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hAb]
    simp [hA1]
  have hu : IsUnit A.det := by rw [hdet]; exact isUnit_one
  have hLeq : L = A' * A⁻¹ := by
    rw [h, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
  have : Invertible A := A.invertibleOfIsUnitDet hu
  have hLb : L.BlockTriangular id := hLeq ▸ hA'b.mul (Matrix.blockTriangular_inv_of_blockTriangular hAb)
  have hoff : ∀ i j, i ≠ j → L i j = 0 := fun i j hij =>
    (lt_or_gt_of_ne hij).elim (hL i j) fun hji => hLb hji
  have hdiag : ∀ i, L i i = 1 := by
    intro i
    have hii := congrFun (congrFun h i) i
    rw [Matrix.mul_apply, Finset.sum_eq_single i (fun k _ hki => by rw [hoff i k (Ne.symm hki), zero_mul])
      (by simp), hA1, mul_one, hA'1] at hii
    exact hii.symm
  have hL1 : L = 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [hdiag]
    · simp [hoff i j hij, Matrix.one_apply_ne hij]
  rw [h, hL1, Matrix.one_mul]

end GlobalTheory.UnitriangularLowerMulEq
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GenericRegularity.CompEmbEqOfFrBor

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField Topology ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

namespace GlobalTheory.Reg.GenericFlagInj

theorem unitri_eq_of_lower {S : Type} [CommRing S] {n : ℕ} (A A' L : Matrix (Fin n) (Fin n) S)
    (hA : ∀ i j, j < i → A i j = 0) (hAd : ∀ i, A i i = 1)
    (hA' : ∀ i j, j < i → A' i j = 0) (hAd' : ∀ i, A' i i = 1)
    (hL : ∀ i j, i < j → L i j = 0) (e : A' = L * A) : A' = A := by
  first
  | exact @_root_.GlobalTheory.UnitriangularLowerMulEq.eq_of_unitriangular_of_eq_lower_mul
  | exact _root_.GlobalTheory.UnitriangularLowerMulEq.eq_of_unitriangular_of_eq_lower_mul
  | (apply _root_.GlobalTheory.UnitriangularLowerMulEq.eq_of_unitriangular_of_eq_lower_mul <;> assumption)
  | (intros; apply _root_.GlobalTheory.UnitriangularLowerMulEq.eq_of_unitriangular_of_eq_lower_mul <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UnitriangularLowerMulEq.eq_of_unitriangular_of_eq_lower_mul <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UnitriangularLowerMulEq.eq_of_unitriangular_of_eq_lower_mul ..)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem genPt_inj {Z Z' : Comp Xo c} (h : genPt Z = genPt Z') : Z = Z' := by
  have g : ∀ W : Comp Xo c, IsGenericPoint (genPt W) (W : Set (Xo.XF c)) := fun W =>
    W.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ W.2)
  exact Subtype.ext (by rw [← (g Z).def, ← (g Z').def, h])

theorem genSp_strK (Z : Comp Xo c) : genSp Z ≫ strK = spMap (algebraMap c.F (kap Z)) := by
  symm
  show Spec.map (CommRingCat.ofHom (Spec.preimage (genSp Z ≫ strK)).hom) = _
  rw [CommRingCat.ofHom_hom, Spec.map_preimage]

theorem genSp_eq {T : Type} [CommRing T] [Algebra c.F T] {Z Z' : Comp Xo c} (ψ : kap Z →ₐ[c.F] T)
    (ψ' : kap Z' →ₐ[c.F] T) (h : spMap ψ.toRingHom ≫ xGen Z = spMap ψ'.toRingHom ≫ xGen Z') :
    spMap ψ.toRingHom ≫ genSp Z = spMap ψ'.toRingHom ≫ genSp Z' := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc]
    exact h
  · have e := genSp_strK Z
    have e' := genSp_strK Z'
    rw [Category.assoc, Category.assoc]
    erw [e, e']
    rw [spMap_comp_ring, spMap_comp_ring]
    congr 1
    ext r
    exact (ψ.commutes r).trans (ψ'.commutes r).symm

theorem comp_eq {T : Type} [CommRing T] [Nontrivial T] [Algebra c.F T] {Z Z' : Comp Xo c} (ψ : kap Z →ₐ[c.F] T)
    (ψ' : kap Z' →ₐ[c.F] T) (h : spMap ψ.toRingHom ≫ xGen Z = spMap ψ'.toRingHom ≫ xGen Z') : Z = Z' := by
  obtain ⟨p⟩ : Nonempty (Sp T) := inferInstanceAs (Nonempty (PrimeSpectrum T))
  have e := congrArg (fun f : Sp T ⟶ Xo.XF c => f p) (genSp_eq ψ ψ' h)
  simp only [Scheme.Hom.comp_apply, genSp] at e
  apply genPt_inj
  exact (Scheme.fromSpecResidueField_apply _ _).symm.trans (e.trans (Scheme.fromSpecResidueField_apply _ _))

theorem emb_eq {T : Type} [CommRing T] [Algebra c.F T] {Z : Comp Xo c} (ψ ψ' : kap Z →ₐ[c.F] T)
    (h : spMap ψ.toRingHom ≫ xGen Z = spMap ψ'.toRingHom ≫ xGen Z) : ψ = ψ' := by
  have e := genSp_eq ψ ψ' h
  haveI : Mono (genSp Z) := by unfold genSp; infer_instance
  have e2 : spMap ψ.toRingHom = spMap ψ'.toRingHom := (cancel_mono (genSp Z)).1 e
  have e3 := congrArg CommRingCat.Hom.hom (Spec.map_injective e2)
  exact AlgHom.coe_ringHom_injective e3

noncomputable def resKap {T : Type} [CommRing T] [Algebra c.F T] {Z : Comp Xo c} (φ : Om Z →ₐ[c.F] T) : kap Z →ₐ[c.F] T :=
  { φ.toRingHom.comp (algebraMap (kap Z) (Om Z)) with
    commutes' := fun r => by
      have := φ.commutes r
      rw [gfp_tower] at this
      exact this }

theorem x_eq {T : Type} [CommRing T] [Algebra c.F T] (h : GenFrEx Xo c) {Z : Comp Xo c} (φ : Om Z →ₐ[c.F] T)
    {y : FrPt Xo c T} (hy : FrMap φ (genFr h Z) y) : y.x = spMap (resKap φ).toRingHom ≫ xGen Z := by
  rw [hy.1, (isGenFr_genFr h Z).1, ← Category.assoc, spMap_comp_ring]
  rfl

theorem eq_of_frBor {T : Type} [CommRing T] [Nontrivial T] [Algebra c.F T] (h : GenFrEx Xo c) (Z Z' : Comp Xo c)
    (φ : Om Z →ₐ[c.F] T) (φ' : Om Z' →ₐ[c.F] T) (y y' : FrPt Xo c T) (t : Ix Dw → Tˣ)
    (hy : FrMap φ (genFr h Z) y) (hy' : FrMap φ' (genFr h Z') y') (hb : FrBor t y y') : Z = Z' ∧ HEq φ φ' := by
  have hx := x_eq h φ hy
  have hx' := x_eq h φ' hy'
  have hxx := hx.symm.trans (hb.1.symm.trans hx')
  obtain rfl : Z = Z' := comp_eq _ _ hxx
  refine ⟨rfl, heq_of_eq ?_⟩
  have hψ : resKap φ = resKap φ' := emb_eq _ _ hxx
  obtain ⟨y₀, hy₀, hc⟩ := (isGenFr_genFr h Z).2
  have pull : ∀ (χ : Om Z →ₐ[c.F] T) (w : FrPt Xo c T), FrMap χ (genFr h Z) w → ∀ τ i,
      IsCombAt w.x (fun j => spMap (dualMap (resKap χ).toRingHom) ≫ y₀.u τ j) (fun j => χ (genCoef Z τ i j))
        (w.u τ i) := by
    intro χ w hw τ i
    refine isCombAt_pull χ.toRingHom hw.1 (fun j => ?_) (hw.2.1 τ i) (hc τ i)
    rw [← Category.assoc, spMap_comp_ring, ← dualMap_comp]
    rfl
  have hcoef : ∀ τ i j, φ' (genCoef Z τ i j) = φ (genCoef Z τ i j) := by
    intro τ
    choose cf hd hz hcf using hb.2.1 τ
    have hyx : y.x = spMap (resKap φ).toRingHom ≫ y₀.x := by rw [hx, hy₀]
    have key := unitri_eq_of_lower (Matrix.of fun i j => φ (genCoef Z τ i j))
      (Matrix.of fun i j => φ' (genCoef Z τ i j)) (Matrix.of cf)
      (fun i j hij => by simp [genCoef, not_lt.2 hij.le, hij.ne'])
      (fun i => by simp [genCoef])
      (fun i j hij => by simp [genCoef, not_lt.2 hij.le, hij.ne'])
      (fun i => by simp [genCoef]) (fun i j hij => hz i j hij) ?_
    · intro i j
      exact congrFun (congrFun key i) j
    · ext i j
      have h1 := pull φ' y' hy' τ i
      rw [← hψ, hb.1] at h1
      have h2 := GlobalTheory.TangentLinear.isCombAt_mulVec E H Dw l Xo T y.x
        (fun j => spMap (dualMap (resKap φ).toRingHom) ≫ y₀.u τ j)
        (fun j => hyx ▸ GlobalTheory.Frames.FramedBaseChange.tan_bc (resKap φ).toRingHom (y₀.tan τ j)) (y.u τ)
        (Matrix.of fun j i => φ (genCoef Z τ i j)) (cf i) (y'.u τ i) (pull φ y hy τ) (hcf i)
      have ht : IsTanAt y.x (y'.u τ i) := hb.1 ▸ y'.tan τ i
      rw [hyx] at h1 h2 ht
      have h3 := (GlobalTheory.Frames.eigenbasis_baseChange E H Dw l Xo c _ T (resKap φ) y₀ τ _ ht (y'.eig τ i)).unique h1 h2
      have h4 := congrFun h3 j
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply] at h4
      simp only [Matrix.mul_apply, Matrix.of_apply]
      rw [h4]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  apply AlgHom.coe_ringHom_injective
  refine IsLocalization.ringHom_ext (nonZeroDivisors (MvPolynomial (FlagVar Dw) (kap Z))) ?_
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun v => ?_)
  · exact AlgHom.congr_fun hψ r
  · obtain ⟨τ, ⟨i, j⟩, hij⟩ := v
    have := hcoef τ i j
    simp only [genCoef, dif_pos (show i < j from hij)] at this
    exact this.symm

end GlobalTheory.Reg.GenericFlagInj
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPositivityPrincipalisationDeep

section

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SepCusp

section Geometry

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn exOf secZ)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Vanishing.H0
open GlobalTheory.CompHt (genVal genPoint)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem eq_of_ptY_eq {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (h : GenFrEx Xo c) (Z : Comp Xo c)
    {K : Type} [Field K] [Algebra c.F K] (φ φ' : Om Z →ₐ[c.F] K)
    (e : spMap φ.toRingHom ≫ X.ptY (genFr h Z) = spMap φ'.toRingHom ≫ X.ptY (genFr h Z)) : φ = φ' := by
  obtain ⟨y, hy⟩ := GlobalTheory.FlagMod.exists_frMap φ (genFr h Z)
  obtain ⟨y', hy'⟩ := GlobalTheory.FlagMod.exists_frMap φ' (genFr h Z)
  rw [X.ptY_frMap hy, X.ptY_frMap hy'] at e
  obtain ⟨k, hz⟩ := GlobalTheory.FlagMod.exists_chart_of_isLocalRing X.F.cover (X.ptY y)
  obtain ⟨Q, hQ⟩ := X.top.exists_chartFr (GlobalTheory.FlagMod.frX_snd y) (X.lies_ptY y).1 k hz
  obtain ⟨t, ht⟩ := hQ.exists_frBor (X.lies_ptY y)
  obtain ⟨t', ht'⟩ := hQ.exists_frBor (e ▸ X.lies_ptY y')
  obtain ⟨-, g1, g2, -⟩ := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c K
  exact eq_of_heq (GlobalTheory.Reg.GenericFlagInj.eq_of_frBor h Z Z φ φ' y y' _ hy hy' (g1 _ _ _ _ _ (g2 _ _ _ ht) ht')).2

theorem exists_val_cuspSec {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c) {r : ℕ}
    (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (la : AllWt.Weight Dw) (h : GenFrEx Xo c) (w : Sp (Om Z) ⟶ Y₀ X Z)
    (hw : w ≫ inc₀ X Z = X.ptY (genFr h Z)) (hU : ⊤ ≤ w ⁻¹ᵁ U₀ X Z) (i : (L₀ X Z la).ι)
    (hi : ⊤ ≤ w ⁻¹ᵁ (L₀ X Z la).U i) :
    ∃ T : Om Z, T ≠ 0 ∧ ∀ g : Cusp Z U la, H0.val w i hU hi (cuspSec X Z U la g) = T * genVal Z g.1 := by
  have e₁ : w ≫ inc₀ X Z = X.pt (genFr h Z) ≫ X.inc := by rw [X.pt_inc]; exact hw
  have hO₂ : ⊤ ≤ (w ≫ inc₀ X Z) ⁻¹ᵁ flagOpen X := hU
  have hk₂ : ⊤ ≤ (w ≫ inc₀ X Z) ⁻¹ᵁ X.F.U (i PUnit.unit) :=
    (le_iff_ptOf_mem _ _).2 (mem_pull.1 ((le_iff_ptOf_mem _ _).1 hi))
  have hk₁ : ⊤ ≤ (X.pt (genFr h Z) ≫ X.inc) ⁻¹ᵁ X.F.U (i PUnit.unit) := e₁ ▸ hk₂
  obtain ⟨Q, t, hQ, ht⟩ := X.exists_chartFr_frBor (genFr h Z) (i PUnit.unit) hk₁
  have hQ₂ : X.F.ChartFr (i PUnit.unit) (w ≫ inc₀ X Z) hk₂ Q := chartFr_congr e₁.symm hQ
  refine ⟨((∏ ix, t ix ^ exOf Dw la 0 ix : (Om Z)ˣ) : Om Z)⁻¹, inv_ne_zero (Units.ne_zero _), fun g => ?_⟩
  have v₈ := evR_eq_val_secOf ⟨g.1, cusp_le_secZ Z U la g.2⟩ hO₂ hQ₂ ht
  have v₅ : H0.val w i hU hi (cuspSec X Z U la g) = H0.val (B := X.LL (exOf Dw la 0))
      (w ≫ inc₀ X Z) (i PUnit.unit) hO₂ hk₂ (secOf X _ ⟨g.1, cusp_le_secZ Z U la g.2⟩) :=
    H0.val_pull (inc₀ X Z) le_rfl w i hU hi hO₂ hk₂ _
  have v₆ : genVal Z g.1 = evR Xo c g.1 (genFr h Z) := rfl
  rw [v₅, v₆, v₈, inv_mul_cancel_left₀ (Units.ne_zero _)]

theorem val_eq_stalk {k K : Type} [CommRing k] [Field K] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {B : LB Y} {O : Y.Opens}
    (x : Sp K ⟶ Y) (i : B.ι) (hO : ⊤ ≤ x ⁻¹ᵁ O) (hi : ⊤ ≤ x ⁻¹ᵁ B.U i) (hy : ptOf x ∈ O) (hj : ptOf x ∈ B.U i)
    (f : H0 p B O) :
    H0.val x i hO hi f = (Scheme.stalkClosedPointTo (R := CommRingCat.of K) x).hom (germ i (ptOf x) hy hj f) := by
  rw [H0.val_apply, H0.germ_apply]
  exact (stalkClosedPointTo_ger x _ _ _ (memInf hy hj)).symm

theorem gapGe_std (Dw : Datum H) : GapGe 1 (GlobalTheory.CompHt.stdWt (Psi H) (Dw.p + Dw.q) : AllWt.Weight Dw) := by
  intro τ k hk
  simp only [gap, dif_pos hk, GlobalTheory.CompHt.stdWt]
  push_cast
  omega

theorem gapGe_sub_std (m : ℕ) (b : AllWt.Weight Dw) (h : GapGe (m : ℤ) b) :
    GapGe 0 (b - m • (GlobalTheory.CompHt.stdWt (Psi H) (Dw.p + Dw.q) : AllWt.Weight Dw)) := by
  intro τ k hk
  have h1 := h τ k hk
  simp only [gap, dif_pos hk, Pi.sub_apply, Pi.smul_apply, GlobalTheory.CompHt.stdWt] at h1 ⊢
  rw [nsmul_eq_mul, nsmul_eq_mul]
  push_cast
  linarith

theorem cls_nsmul {Y : Scheme.{0}} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) (n : ℕ) (a : Λ) :
    cls (B (n • a)) (C.isLB (n • a)) = n • cls (B a) (C.isLB a) :=
  map_nsmul (AddMonoidHom.mk' (fun a => cls (B a) (C.isLB a)) (cls_common_add C)) n a

end Geometry

theorem exists_fg_complexPoint (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [CharZero K] [Countable K]
    (hfg : (⊤ : IntermediateField K Ω).FG) (L : IntermediateField K Ω) (hL : L = ⊤) :
    ∃ (σ : K →+* ℂ) (A B : Subalgebra K Ω), A.FG ∧ B.FG ∧ B ≤ A ∧ (∀ b ∈ B, b ∈ L) ∧
      IntermediateField.adjoin K (A : Set Ω) = ⊤ ∧ (∀ b ∈ B, b ≠ 0 → ∃ x : A →+* ℂ,
        (∀ k : K, x (algebraMap K A k) = σ k) ∧ (∀ hb : b ∈ A, x ⟨b, hb⟩ ≠ 0) ∧
          ∀ y : A →+* ℂ, (∀ k : K, y (algebraMap K A k) = σ k) → (∀ a : A, (a : Ω) ∈ B → y a = x a) → y = x) := by
  have : Countable Ω := TwoPoint.countable_of_fg _ _ hfg
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  obtain ⟨i⟩ := TwoPoint.nonempty_ringHom_complex Ω
  obtain ⟨s, hs⟩ := hfg
  let A : Subalgebra K Ω := Algebra.adjoin K (s : Set Ω)
  exact ⟨i.comp (algebraMap _ _), A, A, ⟨s, rfl⟩, ⟨s, rfl⟩, le_rfl, fun b _ => hL ▸ IntermediateField.mem_top,
    eq_top_iff.2 (hs ▸ IntermediateField.adjoin.mono _ _ _ Algebra.subset_adjoin), fun b _ hb =>
    ⟨i.comp A.val.toRingHom, fun _ => rfl, fun _ => (map_ne_zero i).2 hb, fun y _ h => RingHom.ext fun a => h a a.2⟩⟩

open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp GlobalTheory.DegVal GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal NNReal

theorem gapGe_sub_kap {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} (u : GlobalTheory.AllWt.Weight Dw) (hu : ∀ τ (a b : Fin (Dw.p + Dw.q)), (b : ℕ) = a + 1 →
      (((dimFlag Dw + 3) ^ 2 + 2 * (Dw.p + Dw.q) : ℕ) : ℤ) ≤ u τ a - u τ b) :
    GlobalTheory.HSApp.GapGe (((FlagTan.dimFlag Dw + 2).choose 2 : ℕ) : ℤ) (u - FlagTan.kap Dw) := by
  intro τ k hk
  have h₁ := hu τ ⟨k, by omega⟩ ⟨k + 1, hk⟩ rfl
  have h₂ := GlobalTheory.HSApp.gap_kap_le (Dw := Dw) τ hk
  have h₃ := GlobalTheory.CompHS.gap_eq (u τ) (i := ⟨k, by omega⟩) (j := ⟨k + 1, hk⟩) rfl
  have h₄ : (FlagTan.dimFlag Dw + 2).choose 2 ≤ (FlagTan.dimFlag Dw + 3) ^ 2 :=
    (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (by omega) 2)
  have h₅ : (((FlagTan.dimFlag Dw + 2).choose 2 : ℕ) : ℤ) ≤ ((FlagTan.dimFlag Dw + 3) ^ 2 : ℕ) := by
    exact_mod_cast h₄
  rw [GlobalTheory.CompHS.dimFlag_eq] at h₁
  rw [Pi.sub_apply, GlobalTheory.HSApp.gap_sub]
  dsimp only at h₃
  push_cast at h₁ h₂ h₅ ⊢
  linarith


end GlobalTheory.SepCusp
end
end
end
