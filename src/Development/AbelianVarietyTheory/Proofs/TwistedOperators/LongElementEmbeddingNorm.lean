module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDecompSmulLatticeEmbeddingStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryEmbeddingContinuousMulRational
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
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StabiliserEqCentraliserCartan
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharInfinityEqCoeffMulHalfNormPow
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormSqUnitaryEmbeddingOrthogonal

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SepPer

theorem norm_sq_unitaryEmbedding_add : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (A : Fr Y) (B : Fr V), Adapted d A B → ∀ (x : GA D Y) (τ : D.what₂.Tau) (y : Fin Y.rank → D.host.E) (u : D.host.E), nrm θ B (stabilizerEmbedding d x) τ (frameMat V Y d.ι *ᵥ y + u • zv d) ^ 2 = nrm θ A x τ y ^ 2 + ‖tauE D τ u‖ ^ 2 := by
  intro D θ hθ Y V d A B hAd x τ y u
  let φ : AF D.host.F ⊗[D.host.F] D.host.E →+* ℂ :=
    (θ τ).comp (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom
  have hinc : ∀ e, φ (incA D e) = tauE D τ e := by
    intro e
    have := (hθ τ).1 e
    simpa [φ, incA, inclR] using this
  have hcmp : ∀ {W : HSp D} (g : GA D W), cmp θ τ g = (matHom W g).1.map φ := by
    intro W g; rfl
  have hinv : (stabilizerEmbedding d x)⁻¹ = stabilizerEmbedding d x⁻¹ :=
    (map_inv (MonoidHom.mk' (stabilizerEmbedding d) (GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_mul d)) x).symm
  set P := (frameMat V Y d.ι).map (tauE D τ) with hP
  set Q := (GlobalTheory.UnitaryEmbeddingProperties.qM d).map (tauE D τ) with hQ
  have key : cmp θ τ (stabilizerEmbedding d x)⁻¹ = GlobalTheory.UnitaryEmbeddingProperties.ex P Q (cmp θ τ x⁻¹) := by
    rw [hinv, hcmp, hcmp, GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_matrix_formula, GlobalTheory.UnitaryEmbeddingProperties.ex_map, Matrix.map_map, Matrix.map_map]
    have hf : (⇑φ ∘ ⇑(incA D)) = ⇑(tauE D τ) := funext hinc
    rw [hf]
  have hQP : Q * P = 1 := GlobalTheory.UnitaryEmbeddingProperties.qM_mul_map (tauE D τ) d
  have hQz0 : GlobalTheory.UnitaryEmbeddingProperties.qM d *ᵥ zv d = 0 := by
    have hp := d.perp
    have h0 : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat V Y d.ι) * V.gram) *ᵥ zv d = 0 := by
      funext i
      have := congr_fun (congr_fun hp i) 0
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, zv] using this
    rw [GlobalTheory.UnitaryEmbeddingProperties.qM, ← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]
  have hQz : Q *ᵥ (fun i => tauE D τ (zv d i)) = 0 := by
    funext i
    have := congr_fun hQz0 i
    rw [hQ]
    change ((GlobalTheory.UnitaryEmbeddingProperties.qM d).map (tauE D τ) *ᵥ (⇑(tauE D τ) ∘ zv d)) i = 0
    rw [← RingHom.map_mulVec, this]
    exact map_zero _
  have hvec : (fun i => tauE D τ ((frameMat V Y d.ι *ᵥ y + u • zv d) i)) =
      P *ᵥ (fun i => tauE D τ (y i)) + tauE D τ u • fun i => tauE D τ (zv d i) := by
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add (f := _), map_mul, hP, RingHom.map_mulVec]
    rfl
  have hex : ∀ (h : Matrix (Fin Y.rank) (Fin Y.rank) ℂ) (w : Fin Y.rank → ℂ) (a : ℂ),
      GlobalTheory.UnitaryEmbeddingProperties.ex P Q h *ᵥ (P *ᵥ w + a • fun i => tauE D τ (zv d i)) =
        P *ᵥ (h *ᵥ w) + a • fun i => tauE D τ (zv d i) := by
    intro h w a
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec, GlobalTheory.UnitaryEmbeddingProperties.ex_mul_P P Q hQP,
      ← Matrix.mulVec_mulVec]
    congr 2
    rw [GlobalTheory.UnitaryEmbeddingProperties.ex, Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hQz,
      Matrix.mulVec_zero, add_zero]
  unfold nrm
  rw [key, hvec, hex]
  exact hAd τ _ _

end GlobalTheory.SepPer
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormSqUnitaryEmbeddingOrthogonalStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.norm_sq_unitaryEmbedding_orthogonal : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (A : Fr Y) (B : Fr V), Adapted d A B → ∀ (x : GA D Y) (τ : D.what₂.Tau) (y : Fin Y.rank → D.host.E) (u : D.host.E), nrm θ B (stabilizerEmbedding d x) τ (frameMat V Y d.ι *ᵥ y + u • zv d) ^ 2 = nrm θ A x τ y ^ 2 + ‖tauE D τ u‖ ^ 2 := by
  first | exact @GlobalTheory.SepPer.norm_sq_unitaryEmbedding_add | exact GlobalTheory.SepPer.norm_sq_unitaryEmbedding_add | (intros; apply GlobalTheory.SepPer.norm_sq_unitaryEmbedding_add <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneLeNormRationalTranslate

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SepPer.MajDom

theorem re_form_le {n : ℕ} (G fr : Matrix (Fin n) (Fin n) ℂ) (ε : Fin n → Bool)
    (h : frᴴ * Formalism.REAL.Jm ε * fr = G) (v : Fin n → ℂ) :
    (star v ⬝ᵥ (G *ᵥ v)).re ≤ ∑ i, ‖(fr *ᵥ v) i‖ ^ 2 := by
  subst h
  have e : star v ⬝ᵥ ((frᴴ * Formalism.REAL.Jm ε * fr) *ᵥ v) =
      star (fr *ᵥ v) ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ (fr *ᵥ v)) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec]
  have hd : ∀ w : Fin n → ℂ, Formalism.REAL.Jm ε *ᵥ w = fun i => (if ε i = true then (1 : ℂ) else -1) * w i := by
    intro w; funext i; exact Matrix.mulVec_diagonal _ _ _
  rw [e, hd, dotProduct, Complex.re_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hw : star (fr *ᵥ v) i * ((if ε i = true then (1 : ℂ) else -1) * (fr *ᵥ v) i) =
      (if ε i = true then (1 : ℂ) else -1) * ((‖(fr *ᵥ v) i‖ : ℂ) ^ 2) := by
    rw [← Complex.conj_mul', Pi.star_apply, Complex.star_def]
    ring
  rw [hw]
  split_ifs
  · simp only [one_mul]
    norm_cast
  · have : (-((‖(fr *ᵥ v) i‖ : ℂ) ^ 2)).re = -(‖(fr *ᵥ v) i‖ ^ 2) := by norm_cast
    rw [neg_one_mul, this]
    nlinarith [sq_nonneg ‖(fr *ᵥ v) i‖]

theorem form_isom {n : ℕ} (G P : Matrix (Fin n) (Fin n) ℂ) (hP : Pᴴ * G * P = G) (u : Fin n → ℂ) :
    star (P *ᵥ u) ⬝ᵥ (G *ᵥ (P *ᵥ u)) = star u ⬝ᵥ (G *ᵥ u) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hP]

end GlobalTheory.SepPer.MajDom

namespace GlobalTheory.SepPer.MajDom

variable {D : D7}

theorem tauE_sig (τ : D.what₂.Tau) (a : D.host.E) :
    tauE D τ (D.sp.cm.sig a) = starRingEnd ℂ (tauE D τ a) :=
  D.sp.cm.cmUnram.2.1 _ a

theorem cmp_mulVec (θ : InfFam D) (hθ : IsInfFam θ) {V : HSp D} (γ : GA D V) (z₀ z : Fin V.rank → D.host.E)
    (h : mt V γ *ᵥ ratV z₀ = ratV z) (τ : D.what₂.Tau) :
    cmp θ τ γ *ᵥ (fun i => tauE D τ (z₀ i)) = fun i => tauE D τ (z i) := by
  let φ : AE D →+* ℂ := (θ τ).comp (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom
  have hφ : ∀ e : D.host.E, φ (incA D e) = tauE D τ e := by
    intro e
    show θ τ (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) (1 ⊗ₜ e)) = _
    rw [Algebra.TensorProduct.map_tmul, map_one]
    exact (hθ τ).1 e
  have hc : cmp θ τ γ = (mt V γ).map φ := rfl
  have e1 : (⇑φ ∘ ratV z₀) = fun j => tauE D τ (z₀ j) := funext fun j => hφ (z₀ j)
  funext i
  have := congrArg (fun w => φ (w i)) h
  simp only [RingHom.map_mulVec] at this
  rw [e1] at this
  rw [hc, this]
  exact hφ (z i)

theorem form_zv {Y V : HSp D} (d : HermitianOrthogonalExtensionData Y V 1 1) (τ : D.what₂.Tau) :
    star (fun i => tauE D τ (zv d i)) ⬝ᵥ (gramAt D V τ *ᵥ fun i => tauE D τ (zv d i)) = 1 := by
  have hg := congrArg (fun M => tauE D τ (M 0 0)) d.gram

  simp only [antiDiagonalSignGramMatrix, Formalism.UG.cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul,
  tauE_sig] at hg
  simp only [dotProduct, Matrix.mulVec, gramAt, Matrix.map_apply, Pi.star_apply, Complex.star_def, Finset.mul_sum, zv]
  refine Eq.trans ?_ (hg.trans (by simp))
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_assoc]
  congr 1
  exact (tauE_sig τ _).symm

end GlobalTheory.SepPer.MajDom

namespace GlobalTheory.SepPer.MajDom

theorem one_le_nrm : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (B : Fr V) (x : GA D Y)
    (γ : GA D V) (z : Fin V.rank → D.host.E), γ ∈ GQ V → mt V γ *ᵥ ratV (zv d) = ratV z →
    ∀ τ, 1 ≤ nrm θ B (stabilizerEmbedding d x) τ z := by
  intro D θ hθ Y V d B x γ z _ hmt τ
  set G := gramAt D V τ
  set u₀ : Fin V.rank → ℂ := fun i => tauE D τ (zv d i) with hu₀
  set P := cmp θ τ (stabilizerEmbedding d x)⁻¹ * cmp θ τ γ with hP
  have hv : cmp θ τ (stabilizerEmbedding d x)⁻¹ *ᵥ (fun i => tauE D τ (z i)) = P *ᵥ u₀ := by
    rw [← cmp_mulVec θ hθ γ (zv d) z hmt τ, Matrix.mulVec_mulVec]
  have hPG : Pᴴ * G * P = G := by
    have h1 := GlobalTheory.Doubling.infMat_isometry hθ τ (stabilizerEmbedding d x)⁻¹
    have h2 := GlobalTheory.Doubling.infMat_isometry hθ τ γ
    calc Pᴴ * G * P = (cmp θ τ γ)ᴴ * ((cmp θ τ (stabilizerEmbedding d x)⁻¹)ᴴ * G * cmp θ τ (stabilizerEmbedding d x)⁻¹) * cmp θ τ γ := by
          rw [hP, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = G := by rw [h1, h2]
  have hform : star (P *ᵥ u₀) ⬝ᵥ (G *ᵥ (P *ᵥ u₀)) = 1 := by
    rw [form_isom G P hPG u₀]
    exact form_zv d τ
  have key := re_form_le G (B.fr τ) (B.ε τ) (B.fr_gram τ) (P *ᵥ u₀)
  rw [hform, Complex.one_re] at key
  unfold nrm eu
  rw [hv]
  calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    _ ≤ _ := Real.sqrt_le_sqrt key

end GlobalTheory.SepPer.MajDom
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneLeNormRationalTranslateStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.one_le_norm_rational_translate : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (B : Fr V) (x : GA D Y) (γ : GA D V) (z : Fin V.rank → D.host.E), γ ∈ GQ V → mt V γ *ᵥ ratV (zv d) = ratV z → ∀ τ, 1 ≤ nrm θ B (stabilizerEmbedding d x) τ z := by
  first | exact @GlobalTheory.SepPer.MajDom.one_le_nrm | exact GlobalTheory.SepPer.MajDom.one_le_nrm | (intros; apply GlobalTheory.SepPer.MajDom.one_le_nrm <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.SqrtAbsNormLeProdNormCmTypeEmbeddings

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CMNorm

theorem sqrt_absNorm_le_prod_tauE : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (u : 𝓞 D.host.E), u ∈ 𝔪 → u ≠ 0 → Real.sqrt (Ideal.absNorm 𝔪) ≤ ∏ τ, ‖tauE D τ (u : D.host.E)‖ := by
  intro D 𝔪 u hu hu0
  have hnorm : ∏ τ, ‖tauE D τ (u : D.host.E)‖ ^ 2 = |((Algebra.norm ℚ (u : D.host.E) : ℚ) : ℝ)| := by
    rw [← Rat.cast_abs, ← NumberField.InfinitePlace.prod_eq_abs_norm]
    refine (Fintype.prod_bijective _ (GlobalTheory.LevelSeries.mk_tauE_bij D) _ _ (fun τ => ?_))
    rw [NumberField.InfinitePlace.mult, if_neg (GlobalTheory.LevelSeries.mk_tauE_complex D τ)]
    rfl
  have hspan : Ideal.span {u} ≤ 𝔪 := (Ideal.span_singleton_le_iff_mem _).2 hu
  have hne : Ideal.absNorm (Ideal.span {u}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hu0
  have hdvd := Ideal.absNorm_dvd_absNorm_of_le hspan
  have hle : Ideal.absNorm 𝔪 ≤ Ideal.absNorm (Ideal.span {u}) := Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdvd
  have habs : ((Ideal.absNorm (Ideal.span {u}) : ℕ) : ℝ) = |((Algebra.norm ℚ (u : D.host.E) : ℚ) : ℝ)| := by
    rw [Ideal.absNorm_span_singleton]
    rw [← Algebra.coe_norm_int]
    push_cast
    simp
  have hle' : ((Ideal.absNorm 𝔪 : ℕ) : ℝ) ≤ (∏ τ, ‖tauE D τ (u : D.host.E)‖) ^ 2 := by
    rw [← Finset.prod_pow, hnorm, ← habs]; exact_mod_cast hle
  calc Real.sqrt (Ideal.absNorm 𝔪) ≤ Real.sqrt ((∏ τ, ‖tauE D τ (u : D.host.E)‖) ^ 2) := Real.sqrt_le_sqrt hle'
    _ = ∏ τ, ‖tauE D τ (u : D.host.E)‖ := Real.sqrt_sq (Finset.prod_nonneg fun τ _ => norm_nonneg _)

end GlobalTheory.CMNorm
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.SqrtAbsNormLeProdNormCmTypeEmbeddingsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.sqrt_absNorm_le_prod_norm_cmTypeEmbeddings : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (u : 𝓞 D.host.E), u ∈ 𝔪 → u ≠ 0 → Real.sqrt (Ideal.absNorm 𝔪) ≤ ∏ τ, ‖tauE D τ (u : D.host.E)‖ := by
  first | exact @GlobalTheory.CMNorm.sqrt_absNorm_le_prod_tauE | exact GlobalTheory.CMNorm.sqrt_absNorm_le_prod_tauE | (intros; apply GlobalTheory.CMNorm.sqrt_absNorm_le_prod_tauE <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.LongElementEmbeddingNorm

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SepPer.LongSum

theorem long_sum : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (A : Fr Y) (B : Fr V), Adapted d A B → ∀ (Λ : Lat Y) (x : GA D Y) (s : ℝ), IsSelfDualC Y Λ → 0 ≤ s → s ≤ 1 → Long θ A Λ x s → Long θ B (d.lat Λ fun _ => 1) (stabilizerEmbedding d x) s ∧ (∀ τ, nrm θ B (stabilizerEmbedding d x) τ (zv d) = 1) ∧ ∀ (γ : GA D V) z, γ ∈ GQ V → mt V γ *ᵥ ratV (zv d) = ratV z → ∀ τ, 1 ≤ nrm θ B (stabilizerEmbedding d x) τ z := by
  intro D θ hθ Y V d A B hAd Λ x s _ hs0 hs1 hL
  have hzero : ∀ τ, nrm θ A x τ 0 = 0 := fun τ => by
    have e : (fun i => tauE D τ ((0 : Fin Y.rank → D.host.E) i)) = 0 := by funext i; simp
    unfold nrm
    rw [e, mulVec_zero, mulVec_zero]
    simp [eu]
  have hz : ∀ τ (u : D.host.E), nrm θ B (stabilizerEmbedding d x) τ (u • zv d) = ‖tauE D τ u‖ := fun τ u => by
    have h := GlobalTheory.T.norm_sq_unitaryEmbedding_orthogonal D θ hθ Y V d A B hAd x τ 0 u
    rw [mulVec_zero, zero_add, hzero] at h
    have h2 : nrm θ B (stabilizerEmbedding d x) τ (u • zv d) ^ 2 = ‖tauE D τ u‖ ^ 2 := by rw [h]; ring
    have h0 : 0 ≤ nrm θ B (stabilizerEmbedding d x) τ (u • zv d) := Real.sqrt_nonneg _
    exact (pow_left_inj₀ h0 (norm_nonneg _) two_ne_zero).1 h2
  have hge : ∀ τ y (u : D.host.E), nrm θ A x τ y ≤ nrm θ B (stabilizerEmbedding d x) τ (frameMat V Y d.ι *ᵥ y + u • zv d) := fun τ y u => by
    have h := GlobalTheory.T.norm_sq_unitaryEmbedding_orthogonal D θ hθ Y V d A B hAd x τ y u
    have h0 : 0 ≤ nrm θ B (stabilizerEmbedding d x) τ (frameMat V Y d.ι *ᵥ y + u • zv d) := Real.sqrt_nonneg _
    have h1 : 0 ≤ nrm θ A x τ y := Real.sqrt_nonneg _
    nlinarith [sq_nonneg ‖tauE D τ u‖]
  refine ⟨?_, fun τ => ?_, fun γ z hγ hz' τ => GlobalTheory.T.one_le_norm_rational_translate D θ hθ Y V d B x γ z hγ hz' τ⟩
  · intro 𝔪 h𝔪 w hw hw0
    obtain ⟨y, hy, u, hu, rfl⟩ := GlobalTheory.T.exists_decomp_smul_lattice_embedding D Y V d Λ x 𝔪 w hw
    by_cases hy0 : y = 0
    · subst hy0
      rw [mulVec_zero, zero_add] at hw0 ⊢
      have hu0 : u ≠ 0 := by
        rintro rfl; exact hw0 (by simp)
      have e : ∏ τ, nrm θ B (stabilizerEmbedding d x) τ ((u : D.host.E) • zv d) = ∏ τ, ‖tauE D τ (u : D.host.E)‖ :=
        Finset.prod_congr rfl fun τ _ => hz τ _
      rw [e]
      refine le_trans ?_ (GlobalTheory.T.sqrt_absNorm_le_prod_norm_cmTypeEmbeddings D 𝔪 u hu hu0)
      have h1 : s ^ Fintype.card D.what₂.Tau ≤ 1 := pow_le_one₀ hs0 hs1
      have h2 : 0 ≤ Real.sqrt (Ideal.absNorm 𝔪) := Real.sqrt_nonneg _
      nlinarith
    · refine le_trans (hL 𝔪 h𝔪 y hy hy0) ?_
      exact Finset.prod_le_prod₀ (fun τ _ => Real.sqrt_nonneg _) fun τ _ => hge τ y u
  · have h := hz τ 1
    rw [one_smul, map_one, norm_one] at h
    exact h

end GlobalTheory.SepPer.LongSum

end
end
end
