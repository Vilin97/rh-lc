module

public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.HermitianMetricLogNormFormulaStatement
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.LogNormsExtDegreeAdelic
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.SumEmbeddingsBaseChangeStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GramDetNeZeroLocalBasisCofiniteStatement
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCMFrame
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EllPullExistsOAct
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCmEllipticCurveIntegersWithPeriodStatement
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HomExtDvrOfCardTorsion
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaUniformisationComplexAbelianVarieties
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardTorsionPointsUnconditional
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCmEllipticCurveWithPeriodStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CurveZNeZeroStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameFunctionCmHeightStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameFunctionCmNumberFieldStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsTransitionMatrixGramStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocalBasisGramDetLogNormStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PureTypeLatticesOrthogonalStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmPackPureFrameOpenStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsCmPeriodEmbeddingStatement
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChowlaSelbergPeriod

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem exists_curve0_hasPeriod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [NeZero H.d]
    (χ : DirichletCharacter ℂ H.d), IsKroneckerChar χ → ∀ ρ : ℂ, ρ ^ 2 = -(H.d : ℂ) →
    ∃ (Z : Curve0 H ρ) (x : ℝ), Z.z ≠ 0 ∧ Z.C.HasPeriod x ∧
      (x : ℂ) = (Real.eulerMascheroniConstant + Real.log (2 * Real.pi / √H.d) : ℝ) -
        deriv χ.LFunction 1 / χ.LFunction 1 := by
  intro E _ _ _ H _ χ hχ ρ hρ
  have hL := GlobalTheory.abelianSchemeLaws_all.1
  have hU := GlobalTheory.thetaUnifAV_closed
  have hX := GlobalTheory.CM.homExtDvr_of_card_torsion GlobalTheory.UU.TorsionCount.card_torsion_points_unconditional
  obtain ⟨M, _, ω, C, x, hω, hpr, hper, hx⟩ := GlobalTheory.T.exists_cmEllipticCurve_integers_with_period GlobalTheory.T.exists_cmEllipticCurve_withPeriod hU hL hX E H χ hχ ρ hρ
  obtain ⟨C', π, c'⟩ := exists_ellMap hL.polBaseChange E H _ ω C ℂ ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M))
  obtain ⟨u, hu⟩ := PureType.exists_isThetaUnif hU C'.P
  obtain ⟨c, hc, hΛ⟩ := hpr C'.P π c'.2.1 u
  obtain ⟨Hm, χ', Ef, h1, h2, h3⟩ := id hu
  obtain ⟨w, hw, -⟩ := h2 C'.v (C'.basis.1 0)
  have hd := C'.dim
  let Z : Curve0 H ρ := ⟨M, ω, C, hω, C', π, c', u, hu, c, hc, hΛ, w ⟨0, by omega⟩ / c, by
    convert hw using 1
    funext j
    rw [mul_div_cancel₀ _ hc]
    congr 1
    apply Fin.ext
    have := j.2
    simp only
    omega⟩
  exact ⟨Z, x, GlobalTheory.T.curve_z_ne_zero E H ρ Z, hper, hx⟩

end GlobalTheory.CompanionTheory.Ar.Fl
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChowlaSelbergPeriodStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.chowla_selberg_period : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [NeZero H.d] (χ : DirichletCharacter ℂ H.d), IsKroneckerChar χ → ∀ ρ : ℂ, ρ ^ 2 = -(H.d : ℂ) → ∃ (Z : Curve0 H ρ) (x : ℝ), Z.z ≠ 0 ∧ Z.C.HasPeriod x ∧ (x : ℂ) = (Real.eulerMascheroniConstant + Real.log (2 * Real.pi / √H.d) : ℝ) - deriv χ.LFunction 1 / χ.LFunction 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.exists_curve0_hasPeriod | exact GlobalTheory.CompanionTheory.Ar.Fl.exists_curve0_hasPeriod | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.exists_curve0_hasPeriod <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameFunctionCmValue

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl.ConstAlg

theorem finite_fieldRange {E : Type} [Field E] [NumberField E] (τ : E →+* ℂ) :
    FiniteDimensional ℚ τ.toRatAlgHom.fieldRange :=
  (AlgEquiv.ofInjectiveField τ.toRatAlgHom).toLinearEquiv.finiteDimensional

theorem const_algebraic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H)
    (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty)
    (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c)
    (e : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (ρ : ℂ), IsTypeFn H D.p D.q ty → τ (H.rt : E) = H.rt0 →
    (∀ P (y : Sp ℂ ⟶ Xo.XF c), IsPeriod (FU.Di i) ty P → under y = FU.u i P →
      y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → Set.range y ⊆ U) →
    IsLineFn U τ φ → LinearIndependent (𝓞 E) e → IsConstMul U τ φ FU i e ρ →
    ∃ (k : IntermediateField ℚ ℂ) (_ : FiniteDimensional ℚ k) (r : k), c.F ≤ k ∧ (∀ b, (Z b).M ≤ k) ∧ r ≠ 0 ∧
      (r : ℂ) * (Z true).z ^ D.p = ρ * (Z false).z ^ D.q := by
  intro E _ _ _ H D l Xo c g ty FU i Z U τ φ e ρ hty hrt hmem hline he hconst
  obtain ⟨P, hP, x, hx, X, v, w, hk, hloc, hfr⟩ :=
    GlobalTheory.T.exists_cm_period_embedding E H D l Xo c g ty FU i Z τ ⟨2, Nat.prime_two⟩ τ.toRatAlgHom.fieldRange (finite_fieldRange τ) hty hrt
  have hcard : Fintype.card (Fin D.p ⊕ Fin D.q) = (FU.Di i).p + (FU.Di i).q := by
    simp [(FU.sig i).1, (FU.sig i).2]
  obtain ⟨T, hT, -, hdet, -⟩ := GlobalTheory.T.exists_transition_matrix_gram E H (FU.Di i) _ x e hcard he
  have hT0 : T.det ≠ 0 := hdet hloc.1
  have horth : ∀ a b, sesq (FU.Di i) (x (.inl a)) (x (.inr b)) = 0 := fun a b =>
    (GlobalTheory.T.pure_type_lattices_orthogonal E H (FU.Di i) g ty P hP _ _ (hx.1 a) (hx.2 b)).1
  have hG0 := (GlobalTheory.T.local_basis_gram_det_log_norm E H (FU.Di i) D.p D.q x ⟨2, Nat.prime_two⟩ hloc horth).1
  obtain ⟨hfm, hval⟩ := GlobalTheory.T.cm_pack_pure_frame_open E H D l Xo c g ty FU i Z P hP X x hx U τ φ e ρ T v w hty hrt hmem hline he
    hconst hloc.1 hT hfr
  have hφ : φ X.K X.y v w ≠ 0 := hline.ne X.K X.β X.y v w hfm
  have hmemK : ∀ t : E, τ t ∈ X.K := fun t => hk (τ.toRatAlgHom.mem_fieldRange.2 ⟨t, rfl⟩)
  set G := gramE (FU.Di i) (x ∘ Sum.inr) with hGdef
  let a : X.K := ⟨τ T.det, hmemK _⟩
  let b : X.K := ⟨τ G.det, hmemK _⟩
  have ha : a ≠ 0 := fun h => hT0 ((map_eq_zero τ).1 (congrArg Subtype.val h))
  have hb : b ≠ 0 := fun h => hG0 ((map_eq_zero τ).1 (congrArg Subtype.val h))
  have hbC : τ G.det ≠ 0 := (map_ne_zero τ).2 hG0
  refine ⟨X.K, inferInstance, φ X.K X.y v w * a / b, X.hc, X.hM, div_ne_zero (mul_ne_zero hφ ha) hb, ?_⟩
  have hcoe : ((φ X.K X.y v w * a / b : X.K) : ℂ) = ((φ X.K X.y v w : X.K) : ℂ) * τ T.det / τ G.det := rfl
  rw [hcoe]
  field_simp
  linear_combination hval

end GlobalTheory.CompanionTheory.Ar.Fl.ConstAlg
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameFunctionCmValueStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.frame_function_cm_value : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) (e : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (ρ : ℂ), IsTypeFn H D.p D.q ty → τ (H.rt : E) = H.rt0 → (∀ P (y : Sp ℂ ⟶ Xo.XF c), IsPeriod (FU.Di i) ty P → under y = FU.u i P → y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → Set.range y ⊆ U) → IsLineFn U τ φ → LinearIndependent (𝓞 E) e → IsConstMul U τ φ FU i e ρ → ∃ (k : IntermediateField ℚ ℂ) (_ : FiniteDimensional ℚ k) (r : k), c.F ≤ k ∧ (∀ b, (Z b).M ≤ k) ∧ r ≠ 0 ∧ (r : ℂ) * (Z true).z ^ D.p = ρ * (Z false).z ^ D.q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.ConstAlg.const_algebraic | exact GlobalTheory.CompanionTheory.Ar.Fl.ConstAlg.const_algebraic | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.ConstAlg.const_algebraic <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatDegreeHolds

section

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fl

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM

theorem flatDegree_mean_ext {M k : Type} [Field M] [NumberField M] [Field k] [NumberField k] (f : M →+* k)
    (F : (M →+* ℂ) → ℝ) :
    (∑ s : k →+* ℂ, F (s.comp f)) / Module.finrank ℚ k = (∑ s, F s) / Module.finrank ℚ M := by
  have h := GlobalTheory.T.sum_embeddings_base_change M k ℂ f F
  have hM : (Module.finrank ℚ M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  have hk : (Module.finrank ℚ k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  rw [div_eq_div_iff hk hM]
  linear_combination h

theorem flatDegree_sum_conj {E A : Type} [Field E] [NumberField E] [IsCMField E] [Field A] [CharZero A]
    (F : A → ℝ) (t : E) :
    ∑ j : E →+* A, F (j (IsCMField.complexConj E t)) = ∑ j : E →+* A, F (j t) := by
  let c : E →+* E := RingHomClass.toRingHom (IsCMField.complexConj E)
  let σ : (E →+* A) ≃ (E →+* A) :=
    { toFun := fun j => j.comp c
      invFun := fun j => j.comp c
      left_inv := fun j => RingHom.ext fun x => congrArg j (IsCMField.complexConj_apply_apply E x)
      right_inv := fun j => RingHom.ext fun x => congrArg j (IsCMField.complexConj_apply_apply E x) }
  exact Equiv.sum_comp σ (fun j => F (j t))

theorem flatDegree_logOm_re (E : Type) [Field E] [NumberField E] {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d) {x : ℝ}
    (hx : (x : ℂ) = (Real.eulerMascheroniConstant + Real.log (2 * Real.pi / √d) : ℝ) -
      deriv χ.LFunction 1 / χ.LFunction 1) :
    (logOm E χ).re = x - Real.log (rootDiscr E) + Real.log (Real.sqrt d) := by
  have hrd : 0 < rootDiscr E := by
    rw [NumberField.rootDiscr_def]
    apply Real.rpow_pos_of_pos
    exact_mod_cast abs_pos.mpr (NumberField.discr_ne_zero E)
  have hd : 0 < √(d : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d))
  have hL : deriv χ.LFunction 1 / χ.LFunction 1 =
      ((Real.eulerMascheroniConstant + Real.log (2 * Real.pi / √d) : ℝ) : ℂ) - x := by
    rw [hx]; ring
  unfold GlobalTheory.CM.logOm
  rw [hL]
  simp only [Complex.sub_re, Complex.ofReal_re]
  rw [Real.log_div (by positivity) hrd.ne', Real.log_div (by positivity) hd.ne']
  ring

theorem flatDegree : FlatDegree := by
  unfold FlatDegree
  intro E _ _ _ H D l Xo c g ty FU i U τ φ _ N _ χ hχ hty hrt hflat hN
  obtain ⟨mem, line, ⟨e, ρ, hli, hcm⟩⟩ := hflat
  obtain ⟨hNinf, hNfin⟩ := hN
  have hsq : ∀ b : Bool, sgnRt H b ^ 2 = -(H.d : ℂ) := by
    intro b
    cases b <;> simp [sgnRt, neg_sq, H.sqrt_neg_disc_sq]
  choose Z x hz hper hxv using fun b => GlobalTheory.T.chowla_selberg_period E H χ hχ (sgnRt H b) (hsq b)
  have hx : x false = x true := Complex.ofReal_injective ((hxv false).trans (hxv true).symm)
  haveI := (Z true).nf
  haveI := (Z false).nf
  obtain ⟨n₁, hn₁, hm₁⟩ := hper true
  obtain ⟨n₀, hn₀, hm₀⟩ := hper false
  obtain ⟨k, hkfd, r, hc, hM, hr0, hrz⟩ :=
    GlobalTheory.T.frame_function_cm_value E H D l Xo c g ty FU i Z U τ φ e ρ hty hrt mem line hli hcm
  haveI := hkfd
  haveI : NumberField k := ⟨⟩
  choose t ht1 ht2 ht3 using fun ℓ : Nat.Primes =>
    GlobalTheory.T.frame_function_cm_height E H D l Xo c g ty FU i Z U τ φ e ρ k hc hM r ℓ hty hrt mem line hli hcm hr0 hrz
  have hgram := GlobalTheory.T.gram_det_ne_zero_local_basis_cofinite E H (FU.Di i) (Fin D.p ⊕ Fin D.q) e
    (by rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, (FU.sig i).1, (FU.sig i).2]) hli
  have hrt2 : ((H.rt : E)) ^ 2 = -(H.d : E) := by
    have h := congrArg (algebraMap (NumberField.RingOfIntegers E) E) H.rt_sq
    rw [map_pow, map_neg, map_natCast] at h
    exact h
  have hmean₁ := flatDegree_mean_ext (IntermediateField.inclusion (hM true)).toRingHom
    (fun σ => Real.log (n₁ σ))
  have hmean₀ := flatDegree_mean_ext (IntermediateField.inclusion (hM false)).toRingHom
    (fun σ => Real.log (n₀ σ))
  have hfinite : {ℓ : Nat.Primes | ∃ j : E →+* ℂ_[ℓ], Real.log ‖j (t ℓ)‖ ≠ 0}.Finite := by
    apply hgram.2.subset
    intro ℓ hℓ hloc
    obtain ⟨j, hj⟩ := hℓ
    exact hj (ht2 ℓ hloc j)
  have key := GlobalTheory.T.hermitian_metric_log_norm_formula (↥k) E (RingHom.comp (IntermediateField.inclusion hc : ↥c.F →+* ↥k) (GlobalTheory.CompanionTheory.Ar.Fl.tauE c τ))
    (N.ext (IntermediateField.inclusion hc).toRingHom) r (GlobalTheory.CompanionTheory.Ar.Fl.gramE (FU.Di i) e).det
    (H.rt : E) D.p D.q H.d
    (fun s => n₁ (s.comp (IntermediateField.inclusion (hM true)).toRingHom))
    (fun s => n₀ (s.comp (IntermediateField.inclusion (hM false)).toRingHom))
    (x true) t (fun ℓ => IsCMField.complexConj E (t ℓ))
    hr0 hgram.1 (Nat.Prime.pos H.d_prime) hrt2
    (by rw [neg_div, hmean₁, ← hm₁]; rfl)
    (by rw [neg_div, hmean₀, ← hx, ← hm₀]; rfl)
    (fun s => GlobalTheory.T.frame_function_cm_number_field E H D l Xo c g ty FU i Z U τ φ e ρ k hc hM r s
      (n₁ (s.comp (IntermediateField.inclusion (hM true)).toRingHom))
      (n₀ (s.comp (IntermediateField.inclusion (hM false)).toRingHom))
      (N.inf (s.comp (IntermediateField.inclusion hc).toRingHom))
      hty hrt mem line hli hcm hr0 hrz
      (hn₁ _).1 (hn₀ _).1 (((hn₁ _).2 _).mpr rfl) (((hn₀ _).2 _).mpr rfl)
      (hNinf _))
    (fun ℓ => flatDegree_sum_conj (fun z : ℂ_[ℓ] => Real.log ‖z‖) (t ℓ))
    (fun ℓ j => ht1 ℓ j) hfinite
    (fun ℓ j => ht3 ℓ j _ (hNfin ℓ (j.comp (IntermediateField.inclusion hc).toRingHom)))
  obtain ⟨hAd, hdeg⟩ := key
  obtain ⟨hdeg', hAd'⟩ := GlobalTheory.CompanionTheory.Ar.Fl.logNorms_ext_deg_isAdelic (↥c.F) (↥k)
    (IntermediateField.inclusion hc).toRingHom N
  refine ⟨hAd'.mp hAd, ?_⟩
  rw [← hdeg', hdeg, flatDegree_logOm_re E χ (hxv true)]

end GlobalTheory.CompanionTheory.Ar.Fl
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatDegreeHoldsStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.FlatDegree_holds : GlobalTheory.CompanionTheory.Ar.Fl.FlatDegree := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.flatDegree | exact GlobalTheory.CompanionTheory.Ar.Fl.flatDegree | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.flatDegree <;> assumption)
end
end
