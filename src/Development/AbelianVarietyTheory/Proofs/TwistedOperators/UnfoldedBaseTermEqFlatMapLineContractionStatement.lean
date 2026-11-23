module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.QuasiOfFam
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaIntegrandLocallyUniformMajorant
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinatesOfThetaFunctionAreThetaFunctions
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldedTermBasePointEqFlatMapPairing
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilMixedCoordinatesContinuousBoundedSupNorm
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalFullRankBesselBasePoint
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiActionUnipotentLaws
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergIntegralFourierBesselBasePointEqPairin
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralFundamentalDomainEqIteratedDecomp
import Formalism.LocalToGlobal.IndefiniteReal.PHeisFC
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Dynamics.Ergodic.Action.Regular
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
import Mathlib.Tactic.ReduceModChar
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Monotonicity.Lemmas

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelBasePointMulMemRationalMatrices

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.Asc.HeisL

variable {D : D7}

theorem mixedModelBasePointWithLast_mul {σ : ℕ} (B : BesL D σ) (S : HSp D) (b : Mx D (σ + 1) S.rank) :
    xLast B.d (vecB B.o B.ζ) ⬝ b = B.d.incX S (Matrix.of fun i j => b (Fin.castSucc i) j) +
      B.d.inc0 S ((B.o.resT S).symm (0, zEll B.L (σ + 1) B.ζ ⬝ b)) := by
  rw [HypDec.incX_apply, HypDec.wittDecomp_inclAnisotropicHom_apply, OrthDec.resT_symm_apply, Matrix.mul_zero, zero_add, GlobalTheory.Unf.FB.zEll_mul_eq,
    Matrix.mul_vecMulVec, Matrix.mul_vecMulVec, OrthDec.jB, ← ratV_mulVec]
  ext k j
  simp [Matrix.mul_apply, Fin.sum_univ_castSucc, xLast, vecMulVec_apply, vecB]

theorem symplOH_x0L {σ : ℕ} (B : BesL D σ) (S : HSp D) (b b' : Mx D (σ + 1) S.rank) :
    symplOH S B.V (xLast B.d (vecB B.o B.ζ) ⬝ b) (xLast B.d (vecB B.o B.ζ) ⬝ b') =
      symplOH S B.L (zEll B.L (σ + 1) B.ζ ⬝ b) (zEll B.L (σ + 1) B.ζ ⬝ b') := by
  rw [mixedModelBasePointWithLast_mul, mixedModelBasePointWithLast_mul]
  simp only [GlobalTheory.OrientedHeis.symplOH_add_left, GlobalTheory.OrientedHeis.symplOH_add_right, HypDec.symplOH_incX_incX,
    HypDec.wittDecomp_sympl_inclIsotropic_inclAnisotropic, HypDec.wittDecomp_sympl_inclAnisotropic_inclAnisotropic, zero_add]
  rw [symplOH_skew S B.V (B.d.incX S _) (B.d.inc0 S _), HypDec.wittDecomp_sympl_inclIsotropic_inclAnisotropic, neg_zero, zero_add,
    OrthDec.symplOH_resT, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, symplOH_zero_left, zero_add]

theorem zlL_mem_ratMx {σ : ℕ} (B : BesL D σ) : zEll B.L (σ + 1) B.ζ ∈ ratMx D B.L.rank (σ + 1) := by
  refine ⟨vecMulVec B.ζ (fun i : Fin (σ + 1) => if i.1 + 1 = σ + 1 then (1 : D.host.E) else 0), ?_⟩
  refine Matrix.ext fun k i => ?_
  change incA D (B.ζ k * (if i.1 + 1 = σ + 1 then (1 : D.host.E) else 0)) =
    incA D (B.ζ k) * (if i.1 + 1 = σ + 1 then (1 : AE D) else 0)
  split_ifs
  · rw [mul_one, mul_one]
  · rw [mul_zero, mul_zero, map_zero]

theorem mixedModelBasePoint_mul_mem_rationalMatrices {σ : ℕ} (B : BesL D σ) (S : HSp D) {γ : Mx D (σ + 1) S.rank} (hγ : γ ∈ ratMx D (σ + 1) S.rank) :
    xLast B.d (vecB B.o B.ζ) ⬝ γ ∈ ratMx D B.V.rank S.rank := by
  rw [mixedModelBasePointWithLast_mul]
  obtain ⟨g, rfl⟩ := hγ
  refine add_mem (ratMx_mul (rat_mem _) ⟨Matrix.of fun i j => g (Fin.castSucc i) j, rfl⟩)
    (ratMx_mul (rat_mem _) ?_)
  rw [OrthDec.resT_symm_apply, Matrix.mul_zero, zero_add]
  exact ratMx_mul (rat_mem _) (ratMx_mul (zlL_mem_ratMx B) (rat_mem _))

end GlobalTheory.Asc.HeisL

namespace GlobalTheory.Asc

open GlobalTheory.Asc.HeisL GlobalTheory.Unf.FB



theorem heis_baseL : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : HSp D) (B : BesL D σ) (vB : VolM D (σ + 1) S.rank) (vT : VolM D σ S.rank) (vL : VolM D B.L.rank S.rank) (f : WO S B.V → ℂ) (y : WO S B.L → ℂ), GlobalTheory.Unf.FB.Quasi ψ S B.V f → GlobalTheory.Unf.FB.Quasi ψ S B.L y → (∫ b in vB.𝓕, f (xLast B.d (vecB B.o B.ζ) ⬝ b) * star (y (zEll B.L (σ + 1) B.ζ ⬝ b)) ∂vB.μ = contractT B.o S vL.μ vL.𝓕 (B.d.mixT S ψ vT.μ vT.𝓕 f 0) y 0) ∧ ∫⁻ v in vL.𝓕, ‖B.d.mixT S ψ vT.μ vT.𝓕 f 0 ((B.o.resT S).symm (0, v))‖ₑ ∂vL.μ ≤ ∫⁻ b in vB.𝓕, ‖f (xLast B.d (vecB B.o B.ζ) ⬝ b)‖ₑ ∂vB.μ := by
  intro D ψ hψ σ S B vB vT vL f y hf hy
  have hψn : ∀ a, ‖ψ a‖ = 1 := hψ.1.2.1
  have hL1 : B.L.rank = 1 := B.line.1
  let i₀ : Fin B.L.rank := ⟨0, by omega⟩
  have h1 : ∀ i : Fin B.L.rank, i = i₀ := fun i => Fin.ext (by have := i.2; simp only [i₀]; omega)
  have h0 : B.ζ i₀ ≠ 0 := by
    intro h
    apply B.line.2
    have : B.ζ = 0 := funext fun i => by rw [h1 i, h]; rfl
    rw [this]; simp
  set e := splitLine (σ := σ) (n := S.rank) B.L B.ζ i₀ h1 h0 with he_def
  obtain ⟨he, hes⟩ := continuous_splitLine (σ := σ) (n := S.rank) B.L B.ζ i₀ h1 h0
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := lattice_Mx D (σ + 1) S.rank
  obtain ⟨j1, j2, j3, j4, j5, -⟩ := lattice_Mx D σ S.rank
  obtain ⟨k1, k2, k3, k4, k5, -⟩ := lattice_Mx D B.L.rank S.rank
  haveI : BorelSpace (Mx D (σ + 1) S.rank) := ⟨rfl⟩
  haveI : BorelSpace (Mx D σ S.rank) := ⟨rfl⟩
  haveI : BorelSpace (Mx D B.L.rank S.rank) := ⟨rfl⟩
  haveI : Countable (ratMx D (σ + 1) S.rank) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI := vT.covol.1
  haveI := vL.covol.1
  haveI := vB.covol.1

  have hx : ∀ b : Mx D (σ + 1) S.rank, xLast B.d (vecB B.o B.ζ) ⬝ b = B.d.incX S (e b).1 + B.d.inc0 S ((B.o.resT S).symm (0, (e b).2)) := fun b => mixedModelBasePointWithLast_mul B S b

  set P := vT.μ.prod vL.μ with hP
  let me : Mx D (σ + 1) S.rank ≃ᵐ Mx D σ S.rank × Mx D B.L.rank S.rank :=
    { toEquiv := e.toEquiv
      measurable_toFun := he.measurable
      measurable_invFun := hes.measurable }
  have hmp : MeasurePreserving me (P.map e.symm) P := MeasurePreserving.symm me.symm ⟨me.symm.measurable, rfl⟩
  have hmp' : MeasurePreserving e (P.map e.symm) P := hmp
  have hν : (P.map e.symm).IsAddHaarMeasure := AddEquiv.isAddHaarMeasure_map P e.symm hes (by simpa using he)
  have hPF : IsAddFundamentalDomain ((ratMx D σ S.rank).prod (ratMx D B.L.rank S.rank)) (vT.𝓕 ×ˢ vL.𝓕) P :=
    GlobalTheory.CoordUnfold.isAddFundamentalDomain_prod vT.covol.2.1 vL.covol.2.1
  have hF' : IsAddFundamentalDomain (ratMx D (σ + 1) S.rank) (e ⁻¹' (vT.𝓕 ×ˢ vL.𝓕)) (P.map e.symm) := by
    let g : (ratMx D σ S.rank).prod (ratMx D B.L.rank S.rank) → ratMx D (σ + 1) S.rank :=
      fun p => ⟨e.symm p, splitLine_symm_mem B.L B.ζ i₀ h1 h0 p.2⟩
    have hg : Function.Bijective g := by
      constructor
      · intro a b hab
        exact Subtype.ext (e.symm.injective (congrArg Subtype.val hab))
      · intro x
        exact ⟨⟨e x, splitLine_mem B.L B.ζ i₀ h1 h0 x.2⟩, Subtype.ext (by simp [g])⟩
    refine hPF.preimage_of_equiv hmp'.quasiMeasurePreserving hg ?_
    intro p x
    simp [g, AddSubgroup.vadd_def]
  have hv : (P.map e.symm) (e ⁻¹' (vT.𝓕 ×ˢ vL.𝓕)) = 1 := by
    refine (hmp.measure_preimage_equiv _).trans ?_
    rw [Measure.prod_prod, vT.covol.2.2, vL.covol.2.2, one_mul]
  have hcov : IsCovolOne (ratMx D (σ + 1) S.rank) (P.map e.symm) (e ⁻¹' (vT.𝓕 ×ˢ vL.𝓕)) := ⟨hν, hF', hv⟩
  have hμeq : P.map e.symm = vB.μ := covolOne_measure_eq vB.covol hcov

  have hfx : ∀ γ ∈ ratMx D (σ + 1) S.rank, ∀ b,
      f (xLast B.d (vecB B.o B.ζ) ⬝ (γ + b)) = ψ (-(symplOH S B.V (xLast B.d (vecB B.o B.ζ) ⬝ γ) (xLast B.d (vecB B.o B.ζ) ⬝ b))) * f (xLast B.d (vecB B.o B.ζ) ⬝ b) := by
    intro γ hγ b
    obtain ⟨δ, hδ⟩ := mixedModelBasePoint_mul_mem_rationalMatrices B S hγ
    have e1 := hf.1 δ (xLast B.d (vecB B.o B.ζ) ⬝ b)
    rw [show ratW B.V S δ = xLast B.d (vecB B.o B.ζ) ⬝ γ from hδ] at e1
    rw [Matrix.mul_add, e1]
  have hyz : ∀ γ ∈ ratMx D (σ + 1) S.rank, ∀ b,
      y (zEll B.L (σ + 1) B.ζ ⬝ (γ + b)) = ψ (-(symplOH S B.L (zEll B.L (σ + 1) B.ζ ⬝ γ) (zEll B.L (σ + 1) B.ζ ⬝ b))) * y (zEll B.L (σ + 1) B.ζ ⬝ b) := by
    intro γ hγ b
    obtain ⟨δ, hδ⟩ := ratMx_mul (zlL_mem_ratMx B) hγ
    have e1 := hy.1 δ (zEll B.L (σ + 1) B.ζ ⬝ b)
    rw [show ratW B.L S δ = zEll B.L (σ + 1) B.ζ ⬝ γ from hδ] at e1
    rw [Matrix.mul_add, e1]
  have hunit : ∀ a, ψ a * star (ψ a) = 1 := fun a => by
    rw [← starRingEnd_apply, RCLike.mul_conj, hψn]; simp
  set s := vT.𝓕 ×ˢ vL.𝓕 with hs
  set G : Mx D (σ + 1) S.rank → ℂ := fun b => f (xLast B.d (vecB B.o B.ζ) ⬝ b) * star (y (zEll B.L (σ + 1) B.ζ ⬝ b)) with hG
  have hGper : ∀ γ ∈ ratMx D (σ + 1) S.rank, ∀ b, G (γ + b) = G b := by
    intro γ hγ b
    simp only [hG]
    rw [hfx γ hγ b, hyz γ hγ b, symplOH_x0L, star_mul]
    calc ψ (-symplOH S B.L (zEll B.L (σ + 1) B.ζ ⬝ γ) (zEll B.L (σ + 1) B.ζ ⬝ b)) * f (xLast B.d (vecB B.o B.ζ) ⬝ b) *
          (star (y (zEll B.L (σ + 1) B.ζ ⬝ b)) * star (ψ (-symplOH S B.L (zEll B.L (σ + 1) B.ζ ⬝ γ) (zEll B.L (σ + 1) B.ζ ⬝ b))))
        = (ψ (-symplOH S B.L (zEll B.L (σ + 1) B.ζ ⬝ γ) (zEll B.L (σ + 1) B.ζ ⬝ b)) * star (ψ (-symplOH S B.L (zEll B.L (σ + 1) B.ζ ⬝ γ) (zEll B.L (σ + 1) B.ζ ⬝ b)))) *
          (f (xLast B.d (vecB B.o B.ζ) ⬝ b) * star (y (zEll B.L (σ + 1) B.ζ ⬝ b))) := by ring
      _ = _ := by rw [hunit, one_mul]
  have hx0c : Continuous fun b : Mx D (σ + 1) S.rank => xLast B.d (vecB B.o B.ζ) ⬝ b := continuous_const.matrix_mul continuous_id
  have hzlc : Continuous fun b : Mx D (σ + 1) S.rank => zEll B.L (σ + 1) B.ζ ⬝ b := continuous_const.matrix_mul continuous_id
  have hGc : Continuous G := (hf.2.comp hx0c).mul (continuous_star.comp (hy.2.comp hzlc))
  set H : Mx D σ S.rank × Mx D B.L.rank S.rank → ℂ :=
    fun p => f (B.d.incX S p.1 + B.d.inc0 S ((B.o.resT S).symm (0, p.2))) * star (y p.2) with hH
  have hGH : ∀ p, G (e.symm p) = H p := by
    intro p
    simp only [hG, hH]
    rw [hx (e.symm p), AddEquiv.apply_symm_apply]
    congr 3
    exact congrArg Prod.snd (e.apply_symm_apply p)
  have hmix : ∀ w₀, B.d.mixT S ψ vT.μ vT.𝓕 f 0 w₀ = ∫ ξ in vT.𝓕, f (B.d.incX S ξ + B.d.inc0 S w₀) ∂vT.μ := by
    intro w₀
    change ∫ ξ in vT.𝓕, heisO ψ S B.V (B.d.incX S ξ) (heisO ψ S B.V (B.d.incAdj S 0)
      (heisO ψ S B.V (B.d.inc0 S w₀) f)) 0 ∂vT.μ = _
    congr 1
    funext ξ
    rw [HypDec.integrandT_eq, map_zero, symplOH_zero_right, AddChar.map_zero_eq_one, one_mul, add_zero]
  have hGi : IntegrableOn G (e ⁻¹' s) (P.map e.symm) := covolOne_integrableOn hcov G hGc hGper
  have hHi : Integrable H ((vT.μ.restrict vT.𝓕).prod (vL.μ.restrict vL.𝓕)) := by
    rw [Measure.prod_restrict]
    have h2 := (hmp.integrableOn_comp_preimage me.measurableEmbedding (f := H) (s := s)).1 (by
      have : H ∘ me = G := funext fun b => by
        rw [Function.comp_apply, ← hGH]
        exact congrArg G (e.symm_apply_apply b)
      rw [this]; exact hGi)
    exact h2
  refine ⟨?_, ?_⟩
  · calc ∫ b in vB.𝓕, f (xLast B.d (vecB B.o B.ζ) ⬝ b) * star (y (zEll B.L (σ + 1) B.ζ ⬝ b)) ∂vB.μ = ∫ b in vB.𝓕, G b ∂vB.μ := rfl
      _ = ∫ b in e ⁻¹' s, G b ∂(P.map e.symm) := (covolOne_integral_eq vB.covol hcov G hGper).symm
      _ = ∫ p in s, H p ∂P := by
        have h3 := hmp.setIntegral_preimage_emb me.measurableEmbedding H s
        rw [← h3]
        refine congrArg (fun F : Mx D (σ + 1) S.rank → ℂ => ∫ b in e ⁻¹' s, F b ∂(P.map e.symm)) (funext fun b => ?_)
        rw [← hGH]
        exact (congrArg G (e.symm_apply_apply b)).symm
      _ = ∫ v in vL.𝓕, ∫ ξ in vT.𝓕, H (ξ, v) ∂vT.μ ∂vL.μ := by
        rw [hP, ← Measure.prod_restrict]
        exact integral_prod_symm H hHi
      _ = _ := by
        change _ = ∫ v in vL.𝓕, B.d.mixT S ψ vT.μ vT.𝓕 f 0 ((B.o.resT S).symm (0, v)) * star (y v) ∂vL.μ
        congr 1
        funext v
        rw [hmix, ← integral_mul_const]
  · have hψe : ∀ a, ‖ψ a‖ₑ = 1 := fun a => by rw [← ofReal_norm_eq_enorm, hψn, ENNReal.ofReal_one]
    set K : Mx D σ S.rank × Mx D B.L.rank S.rank → ENNReal :=
      fun p => ‖f (B.d.incX S p.1 + B.d.inc0 S ((B.o.resT S).symm (0, p.2)))‖ₑ with hK
    have hKc : Continuous K := by
      refine (hf.2.comp ?_).enorm
      simp only [HypDec.incX_apply, HypDec.wittDecomp_inclAnisotropicHom_apply, OrthDec.resT_symm_apply]
      exact (continuous_const.matrix_mul continuous_fst).add (continuous_const.matrix_mul
        (continuous_const.add (continuous_const.matrix_mul continuous_snd)))
    have hKe : ∀ b, K (e b) = ‖f (xLast B.d (vecB B.o B.ζ) ⬝ b)‖ₑ := fun b => by rw [hK, hx b]
    have hper' : ∀ (γ : ratMx D (σ + 1) S.rank) (b : Mx D (σ + 1) S.rank),
        ‖f (xLast B.d (vecB B.o B.ζ) ⬝ (γ +ᵥ b))‖ₑ = ‖f (xLast B.d (vecB B.o B.ζ) ⬝ b)‖ₑ := by
      intro γ b
      rw [AddSubgroup.vadd_def, vadd_eq_add, hfx γ γ.2 b, enorm_mul, hψe, one_mul]
    have hF'' : IsAddFundamentalDomain (ratMx D (σ + 1) S.rank) (e ⁻¹' s) vB.μ := hμeq ▸ hF'
    calc ∫⁻ v in vL.𝓕, ‖B.d.mixT S ψ vT.μ vT.𝓕 f 0 ((B.o.resT S).symm (0, v))‖ₑ ∂vL.μ
        ≤ ∫⁻ v in vL.𝓕, ∫⁻ ξ in vT.𝓕, K (ξ, v) ∂vT.μ ∂vL.μ := by
          refine lintegral_mono fun v => ?_
          rw [hmix]
          exact enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ p in s, K p ∂P := by
        rw [hP, ← Measure.prod_restrict, lintegral_prod_symm _ hKc.measurable.aemeasurable]
      _ = ∫⁻ b in e ⁻¹' s, K (e b) ∂(P.map e.symm) :=
        (hmp'.setLIntegral_comp_preimage_emb me.measurableEmbedding K s).symm
      _ = ∫⁻ b in e ⁻¹' s, ‖f (xLast B.d (vecB B.o B.ζ) ⬝ b)‖ₑ ∂vB.μ := by
        rw [hμeq]; congr 1; funext b; exact hKe b
      _ = ∫⁻ b in vB.𝓕, ‖f (xLast B.d (vecB B.o B.ζ) ⬝ b)‖ₑ ∂vB.μ := hF''.setLIntegral_eq vB.covol.2.1 _ hper'

end GlobalTheory.Asc

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldedBaseTermEqFlatMapLineContraction

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

open GlobalTheory.Unf.FB GlobalTheory.FlatBase

namespace GlobalTheory.Asc.FlatBaseL

theorem fl_base_eq_contract : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (s : StFB ψ J B) (vb : VolM D (σ + 1) J.W₀.rank) (vL : VolM D B.L.rank J.W₀.rank) (y : WO J.W₀ B.L → ℂ) (Ψ : WO J.W B.V → ℂ), GlobalTheory.Unf.FB.Quasi ψ J.W₀ B.L y → IsThetaFunO ψ J.W B.V Ψ → fl ψ J.d B.V s.vS vb s.vU (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) (xLast B.d (vecB B.o B.ζ)) Ψ = contractT B.o J.W₀ vL.μ vL.𝓕 (flFB s Ψ) y 0 ∧ ∀ M : ℝ, (∀ w, ‖y w‖ ≤ M) → ‖contractT B.o J.W₀ vL.μ vL.𝓕 (flFB s Ψ) y 0‖ₑ ≤ ENNReal.ofReal M * ∫⁻ u, ∫⁻ b in vb.𝓕, ‖J.d.mixS B.V ψ s.vS.μ s.vS.𝓕 Ψ (xLast B.d (vecB B.o B.ζ) ⬝ u.1.1) (xLast B.d (vecB B.o B.ζ) ⬝ b)‖ₑ ∂vb.μ ∂s.vU.ν := by
  intro D ψ σ J B s vb vL y Ψ hy hΨ
  have hstd : IsStdChar D ψ (-1) := s.weil.std
  have hchar := hstd.1
  obtain ⟨-, ⟨My, hMy, -⟩, -, -, -, hlaw0⟩ := GlobalTheory.Unf.FB.ThLawsL.th_laws D ψ hstd σ J B y hy
  have hlaw : ∀ b, ∀ u ∈ UX D (σ + 1), star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) (J.d.nB b * J.d.levi u) y 0) * star (psiFlag ψ J.d (J.d.nB b * J.d.levi u)) = star (psiUni ψ u) * star (y (zEll B.L (σ + 1) B.ζ ⬝ b)) := hlaw0
  have hnorm : ∀ u : UX D (σ + 1), ‖psiUni ψ u.1‖ = 1 := fun u => hchar.2.1 _
  have hfl : ∀ u : UX D (σ + 1), (∫ b in vb.𝓕, flFun ψ J.d B.V s.vS (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) (xLast B.d (vecB B.o B.ζ)) Ψ u b ∂vb.μ) =
      star (psiUni ψ u.1) * ∫ v in vL.𝓕, evalAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xLast B.d (vecB B.o B.ζ) ⬝ u.1.1) 0
        ((B.o.resT J.W₀).symm (0, v)) * star (y v) ∂vL.μ := by
    intro u
    have hf : Quasi ψ J.W₀ B.V (J.d.mixS B.V ψ s.vS.μ s.vS.𝓕 Ψ (xLast B.d (vecB B.o B.ζ) ⬝ u.1.1)) := by
      have h := (GlobalTheory.MixValues.mixed_values D ψ hstd).1 J.W J.W₀ B.V (σ + 1) J.d s.vS.μ s.vS.𝓕 s.vS.covol Ψ hΨ (xLast B.d (vecB B.o B.ζ) ⬝ u.1.1)
      exact ⟨h.quasi, h.cont⟩
    have hh := (GlobalTheory.Asc.heis_baseL D ψ hstd σ J.W₀ B vb s.vT vL _ y hf hy).1
    calc (∫ b in vb.𝓕, flFun ψ J.d B.V s.vS (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) (xLast B.d (vecB B.o B.ζ)) Ψ u b ∂vb.μ)
        = ∫ b in vb.𝓕, star (psiUni ψ u.1) * (J.d.mixS B.V ψ s.vS.μ s.vS.𝓕 Ψ (xLast B.d (vecB B.o B.ζ) ⬝ u.1.1) (xLast B.d (vecB B.o B.ζ) ⬝ b) *
            star (y (zEll B.L (σ + 1) B.ζ ⬝ b))) ∂vb.μ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
          simp only [flFun]
          rw [hlaw b u.1 u.2]
          simp only [I195MixedCoordinates_f1b992d3c44b213cc9f27f15.source, HypDec.mixS,
            HypDec.extX, HypDec.extY, HypDec.ext0, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
          ring
      _ = _ := by
          rw [integral_const_mul]
          exact congrArg (star (psiUni ψ u.1) * ·) hh
  have hLeft : fl ψ J.d B.V s.vS vb s.vU (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) (xLast B.d (vecB B.o B.ζ)) Ψ = ∫ u, star (psiUni ψ u.1) *
      ∫ v in vL.𝓕, evalAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xLast B.d (vecB B.o B.ζ) ⬝ u.1.1) 0
        ((B.o.resT J.W₀).symm (0, v)) * star (y v) ∂vL.μ ∂s.vU.ν := by
    unfold fl
    exact integral_congr_ae (Filter.Eventually.of_forall hfl)
  obtain ⟨x, hxo, hx⟩ := GlobalTheory.Asc.FBx.exists_rat_eq_xLast D σ B
  obtain ⟨M, hMi, hMb⟩ := GlobalTheory.Unf.flatFun_majorant D ψ J.W J.W₀ B.V B.V₀ (σ + 1) σ J.d B.d s.vS s.vT s.χV s.χW s.om s.weil s.vU x
    hxo.1 Ψ hΨ {1} isCompact_singleton
  have hom1 : s.om 1 Ψ = Ψ := by rw [map_one]; rfl
  have hbound : ∀ (u : UX D (σ + 1)) (v : WO J.W₀ B.L),
      ‖flatFun ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (xLast B.d (vecB B.o B.ζ)) 0 Ψ ((B.o.resT J.W₀).symm (0, v)) u * star (y v)‖ ≤
        M u * My := by
    intro u v
    have h := hMb 1 (Set.mem_singleton 1) 0 ((B.o.resT J.W₀).symm (0, v)) u
    rw [hx, hom1] at h
    rw [norm_mul, norm_star]
    exact mul_le_mul h (hMy v) (norm_nonneg _) ((norm_nonneg _).trans h)
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have : BorelSpace (UX D (σ + 1)) := ⟨rfl⟩
  have : BorelSpace (WO J.W₀ B.L) := ⟨rfl⟩
  have : SecondCountableTopology (WO J.W₀ B.L) := (lattice_Mx D B.L.rank J.W₀.rank).2.2.1
  have hE : Continuous fun p : UX D (σ + 1) × WO J.W₀ B.L =>
      evalAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xLast B.d (vecB B.o B.ζ) ⬝ p.1.1.1) 0 ((B.o.resT J.W₀).symm (0, p.2)) := by
    have hmc := (GlobalTheory.MixCont.mixed_coords_continuous D ψ J.W J.W₀ B.V B.V₀ (σ + 1) σ J.d B.d s.vS s.vT s.χV s.χW s.om s.weil Ψ hΨ).2
    have hc : Continuous fun p : UX D (σ + 1) × WO J.W₀ B.L => (p.1.1.1 : Mx D (σ + 1) (σ + 1)) :=
      (Units.continuous_val.comp continuous_subtype_val).comp continuous_fst
    have hin : Continuous fun p : UX D (σ + 1) × WO J.W₀ B.L =>
        ((1 : GA D J.W × GA D B.V), xLast B.d (vecB B.o B.ζ) ⬝ p.1.1.1, (0 : Mx D J.W₀.rank σ), (B.o.resT J.W₀).symm (0, p.2)) :=
      continuous_const.prodMk ((continuous_const.matrix_mul hc).prodMk (continuous_const.prodMk
        ((B.o.continuous_resT_symm J.W₀).comp (continuous_const.prodMk continuous_snd))))
    have h := hmc.comp hin
    simpa only [Function.comp_def, hom1] using h
  have hK : Continuous (Function.uncurry fun (u : UX D (σ + 1)) (v : WO J.W₀ B.L) =>
      flatFun ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (xLast B.d (vecB B.o B.ζ)) 0 Ψ ((B.o.resT J.W₀).symm (0, v)) u * star (y v)) :=
    ((continuous_star.comp ((continuous_psiUni hchar.1 (σ + 1)).comp continuous_fst)).mul hE).mul
      (continuous_star.comp (hy.2.comp continuous_snd))
  haveI : IsFiniteMeasure (vL.μ.restrict vL.𝓕) := isFiniteMeasure_restrict.2 (by rw [vL.covol.2.2]; simp)
  have hswap := integral_swap_of_majorant s.vU.ν (vL.μ.restrict vL.𝓕) (fun u v =>
      flatFun ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (xLast B.d (vecB B.o B.ζ)) 0 Ψ ((B.o.resT J.W₀).symm (0, v)) u * star (y v))
    hK.stronglyMeasurable M hMi My hbound
  have h1 : fl ψ J.d B.V s.vS vb s.vU (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) (xLast B.d (vecB B.o B.ζ)) Ψ = contractT B.o J.W₀ vL.μ vL.𝓕 (flFB s Ψ) y 0 := by
    rw [hLeft]
    calc (∫ u, star (psiUni ψ u.1) * ∫ v in vL.𝓕, evalAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xLast B.d (vecB B.o B.ζ) ⬝ u.1.1) 0
            ((B.o.resT J.W₀).symm (0, v)) * star (y v) ∂vL.μ ∂s.vU.ν)
        = ∫ u, ∫ v in vL.𝓕, flatFun ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (xLast B.d (vecB B.o B.ζ)) 0 Ψ ((B.o.resT J.W₀).symm (0, v)) u *
            star (y v) ∂vL.μ ∂s.vU.ν := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
          dsimp only
          rw [← integral_const_mul]
          refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
          simp only [flatFun]
          ring
      _ = ∫ v in vL.𝓕, ∫ u, flatFun ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (xLast B.d (vecB B.o B.ζ)) 0 Ψ ((B.o.resT J.W₀).symm (0, v)) u *
            star (y v) ∂s.vU.ν ∂vL.μ := hswap
      _ = ∫ v in vL.𝓕, (∫ u, flatFun ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (xLast B.d (vecB B.o B.ζ)) 0 Ψ ((B.o.resT J.W₀).symm (0, v)) u
            ∂s.vU.ν) * star (y v) ∂vL.μ :=
          integral_congr_ae (Filter.Eventually.of_forall fun v => integral_mul_const _ _)
      _ = contractT B.o J.W₀ vL.μ vL.𝓕 (flFB s Ψ) y 0 := rfl
  refine ⟨h1, fun Mb hMb' => ?_⟩
  rw [← h1]
  unfold fl
  calc ‖∫ u, ∫ b in vb.𝓕, flFun ψ J.d B.V s.vS (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) (xLast B.d (vecB B.o B.ζ)) Ψ u b ∂vb.μ ∂s.vU.ν‖ₑ
      ≤ ∫⁻ u, ‖∫ b in vb.𝓕, flFun ψ J.d B.V s.vS (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) (xLast B.d (vecB B.o B.ζ)) Ψ u b ∂vb.μ‖ₑ ∂s.vU.ν :=
        enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ u, ∫⁻ b in vb.𝓕, ‖flFun ψ J.d B.V s.vS (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) (xLast B.d (vecB B.o B.ζ)) Ψ u b‖ₑ ∂vb.μ ∂s.vU.ν :=
        lintegral_mono fun u => enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ u, ∫⁻ b in vb.𝓕, ENNReal.ofReal Mb *
          ‖J.d.mixS B.V ψ s.vS.μ s.vS.𝓕 Ψ (xLast B.d (vecB B.o B.ζ) ⬝ u.1.1) (xLast B.d (vecB B.o B.ζ) ⬝ b)‖ₑ ∂vb.μ ∂s.vU.ν := by
        refine lintegral_mono fun u => lintegral_mono fun b => ?_
        simp only [flFun]
        rw [enorm_mul]
        gcongr
        · rw [hlaw b u.1 u.2, ← ofReal_norm, norm_mul, norm_star, norm_star, hnorm u, one_mul]
          exact ENNReal.ofReal_le_ofReal (hMb' _)
        · simp only [I195MixedCoordinates_f1b992d3c44b213cc9f27f15.source, HypDec.mixS,
            HypDec.extX, HypDec.extY, HypDec.ext0, AddMonoidHom.coe_mk, ZeroHom.coe_mk, le_refl]
    _ = _ := (lintegral_congr fun u => lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).trans
        (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top)

end GlobalTheory.Asc.FlatBaseL

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldedBaseTermEqFlatMapLineContractionStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

theorem _root_.GlobalTheory.T.unfoldedBaseTerm_eq_flatMap_lineContraction : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (s : StFB ψ J B) (vb : VolM D (σ + 1) J.W₀.rank) (vL : VolM D B.L.rank J.W₀.rank) (y : WO J.W₀ B.L → ℂ) (Ψ : WO J.W B.V → ℂ), GlobalTheory.Unf.FB.Quasi ψ J.W₀ B.L y → IsThetaFunO ψ J.W B.V Ψ → fl ψ J.d B.V s.vS vb s.vU (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) (xLast B.d (vecB B.o B.ζ)) Ψ = contractT B.o J.W₀ vL.μ vL.𝓕 (flFB s Ψ) y 0 ∧ ∀ M : ℝ, (∀ w, ‖y w‖ ≤ M) → ‖contractT B.o J.W₀ vL.μ vL.𝓕 (flFB s Ψ) y 0‖ₑ ≤ ENNReal.ofReal M * ∫⁻ u, ∫⁻ b in vb.𝓕, ‖J.d.mixS B.V ψ s.vS.μ s.vS.𝓕 Ψ (xLast B.d (vecB B.o B.ζ) ⬝ u.1.1) (xLast B.d (vecB B.o B.ζ) ⬝ b)‖ₑ ∂vb.μ ∂s.vU.ν := by
  first | exact @GlobalTheory.Asc.FlatBaseL.fl_base_eq_contract | exact GlobalTheory.Asc.FlatBaseL.fl_base_eq_contract | (intros; apply GlobalTheory.Asc.FlatBaseL.fl_base_eq_contract <;> assumption)
end
end
