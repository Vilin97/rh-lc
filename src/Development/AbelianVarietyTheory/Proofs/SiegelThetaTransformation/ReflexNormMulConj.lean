module

public import Development.AbelianVarietyTheory.BlockTheory.JetGauges.ThetaSpanAdjoint
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsTorusOfPeriodHermitian
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.ReflexNormIndexIdeal
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsCoeEqSpanDetOfIntVecLe
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.GroupWithZero.Torsion
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulMemOfMemSpan
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.NeBotOfNorm
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.FirstCoordinateAdmissible
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DetIdealSelfDualLatticeAndInterStandard
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Formalism.LocalToGlobal.ProjectiveLattices.JFDFree
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulMemOfMemSpan
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs

-- Source module: Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MultAddMultConjugate

section

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LatticeBetaCompare

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal GlobalTheory.GenusLatCompare
open scoped nonZeroDivisors Pointwise

section Index

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

def detSpan (M : Submodule (𝓞 E) (Fin n → E)) : Submodule (𝓞 E) E := Submodule.span (𝓞 E) (detSet M)

omit [NumberField E] in
theorem detSet_eq (M : Submodule (𝓞 E) (Fin n → E)) :
    detSet M = {d | ∃ v : Fin n → Fin n → E, (∀ i, v i ∈ M) ∧ d = (Matrix.of v).det} := by
  ext d
  refine exists_congr fun v => and_congr_right fun _ => ?_
  rw [← Matrix.det_transpose (Matrix.of v)]
  rfl


theorem isUnit_detSpan (Λ : Lat E n) : IsUnit (detSpan Λ.L) := by
  obtain ⟨J, -, h0, -, hJ, -⟩ := GlobalTheory.TensorLat.exists_coe_eq_span_det (le_refl Λ.L) Λ.fg Λ.span_top
  rw [detSpan, detSet_eq, ← hJ]
  refine IsUnit.of_mul_eq_one ((J⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) ?_
  rw [← FractionalIdeal.coe_mul, mul_inv_cancel₀ h0, FractionalIdeal.coe_one]

end Index

section Push

variable {E F : Type} [Field E] [Field F] (φ : E →+* F)

theorem span_image_span (S : Set E) :
    Submodule.span (𝓞 F) (φ '' (Submodule.span (𝓞 E) S : Set E)) = Submodule.span (𝓞 F) (φ '' S) := by
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono (Set.image_mono Submodule.subset_span))
  rintro _ ⟨x, hx, rfl⟩
  induction hx using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul b x _ hx =>
    have : φ (b • x) = RingOfIntegers.mapRingHom φ b • φ x := by
      change φ ((b : E) * x) = _
      rw [map_mul]; rfl
    rw [this]; exact Submodule.smul_mem _ _ hx

def extend : Submodule (𝓞 E) E →* Submodule (𝓞 F) F where
  toFun M := Submodule.span (𝓞 F) (φ '' M)
  map_one' := by rw [Submodule.one_eq_span, span_image_span, Set.image_singleton, map_one, Submodule.one_eq_span]
  map_mul' M N := by
    rw [Submodule.mul_eq_span_mul_set, span_image_span, Set.image_mul, Submodule.span_mul_span]

def coeI (E : Type) [Field E] : Ideal (𝓞 E) →* Submodule (𝓞 E) E where
  toFun := IsLocalization.coeSubmodule E
  map_one' := by rw [Ideal.one_eq_top, IsLocalization.coeSubmodule_top]
  map_mul' := IsLocalization.coeSubmodule_mul E

theorem smul_eq_coeI_mul (𝔞 : Ideal (𝓞 E)) (N : Submodule (𝓞 E) E) : 𝔞 • N = coeI E 𝔞 * N := by
  refine le_antisymm (Submodule.smul_le.2 fun a ha x hx => ?_) (Submodule.mul_le.2 ?_)
  · rw [Algebra.smul_def]
    exact Submodule.mul_mem_mul ⟨a, ha, rfl⟩ hx
  · rintro _ ⟨a, ha, rfl⟩ x hx
    exact (Algebra.smul_def a x) ▸ Submodule.smul_mem_smul ha hx

theorem span_image_ideal (𝔞 : Ideal (𝓞 E)) :
    Submodule.span (𝓞 F) (φ.comp (algebraMap (𝓞 E) E) '' (𝔞 : Set (𝓞 E))) =
      coeI F (𝔞.map (RingOfIntegers.mapRingHom φ)) := by
  change _ = IsLocalization.coeSubmodule F (Ideal.span _)
  rw [IsLocalization.coeSubmodule_span, Set.image_image]
  rfl

theorem extend_coeI (𝔞 : Ideal (𝓞 E)) :
    extend φ (coeI E 𝔞) = coeI F (𝔞.map (RingOfIntegers.mapRingHom φ)) := by
  rw [← span_image_ideal]
  change Submodule.span (𝓞 F) (φ '' (algebraMap (𝓞 E) E '' (𝔞 : Set (𝓞 E)))) = _
  rw [Set.image_image]
  rfl

theorem span_eq_coeI_iff [NumberField F] (β : F) (I : Ideal (𝓞 F)) :
    Submodule.span (𝓞 F) {β} = coeI F I ↔ ∃ b : 𝓞 F, (b : F) = β ∧ Ideal.span {b} = I := by
  constructor
  · intro h
    obtain ⟨b, -, rfl⟩ : β ∈ coeI F I := h ▸ Submodule.mem_span_singleton_self β
    refine ⟨b, rfl, IsFractionRing.coeSubmodule_injective (𝓞 F) F ?_⟩
    rw [IsLocalization.coeSubmodule_span_singleton]
    exact h
  · rintro ⟨b, rfl, rfl⟩
    exact (IsLocalization.coeSubmodule_span_singleton F b).symm

end Push

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
variable {H : Host E} (Dw : Datum H) {l : Level H} (c : Coeff l)

theorem idealAt_eq (M : Submodule (𝓞 E) (Fin n → E)) (τ : E →+* ℂ) :
    idealAt c M τ = extend (embF c τ) (detSpan M) := (span_image_span _ _).symm

theorem coeI_reflexIdeal (𝔞 : Ideal (𝓞 E)) : coeI c.F (reflexIdeal Dw c 𝔞) =
    ∏ τ : E →+* ℂ, coeI c.F (𝔞.map (RingOfIntegers.mapRingHom (embF c τ))) ^ Dw.mult τ := by
  simp only [reflexIdeal, map_prod, map_pow]

variable {Dw c} in
theorem isBe_ne_zero {𝔞 : Ideal (𝓞 E)} (h0 : 𝔞 ≠ ⊥) {β : c.F} (h : IsBe Dw c 𝔞 β) : β ≠ 0 := by
  rintro rfl
  have := h.2 c.F.val.toRingHom
  rw [map_zero, norm_zero, zero_pow two_ne_zero] at this
  exact pow_ne_zero _ (Nat.cast_ne_zero.2 (Ideal.absNorm_eq_zero_iff.not.2 h0)) this.symm


variable {Dw c} in
theorem isBe_unique {𝔞 : Ideal (𝓞 E)} (h0 : 𝔞 ≠ ⊥) {β β' : c.F} (h : IsBe Dw c 𝔞 β) (h' : IsBe Dw c 𝔞 β') :
    ∃ ζ : c.F, IsOfFinOrder ζ ∧ β' = ζ * β := by
  have hβ := isBe_ne_zero h0 h
  obtain ⟨⟨b, rfl, hb⟩, ha⟩ := h
  obtain ⟨⟨b', rfl, hb'⟩, ha'⟩ := h'
  obtain ⟨u, rfl⟩ : ∃ u, u * b = b' := Ideal.mem_span_singleton'.1 (by
    rw [hb, ← hb']; exact Ideal.mem_span_singleton_self _)
  refine ⟨u, isOfFinOrder_iff_pow_eq_one.2 ?_, rfl⟩
  obtain ⟨m, hm, h⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one c.F ℂ u.isIntegral_coe fun s => by
    have h1 := (ha' s).trans (ha s).symm
    have h2 : ‖s b‖ ≠ 0 := by simpa using hβ
    rw [pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero] at h1
    change ‖s ((u : c.F) * b)‖ = _ at h1
    rw [map_mul, norm_mul] at h1
    exact mul_right_cancel₀ h2 (h1.trans (one_mul _).symm)
  exact ⟨m, hm, h⟩

theorem mult_add_mult_conjugate (τ : E →+* ℂ) :
    Dw.mult τ + Dw.mult (ComplexEmbedding.conjugate τ) = Dw.p + Dw.q := by
  apply GlobalTheory.PeriodTorus.mult_add_mult_conj <;> assumption

theorem norm_reflexNorm (γ : E) (s : c.F →+* ℂ) :
    ‖s (reflexNorm Dw c γ)‖ ^ 2 = |(Algebra.norm ℚ γ : ℝ)| ^ (Dw.p + Dw.q) := by
  have h1 : ∀ σ : E →+* ℂ, ‖s (embF c (ComplexEmbedding.conjugate σ) γ)‖ = ‖s (embF c σ γ)‖ := fun σ => by
    have e : embF c (ComplexEmbedding.conjugate σ) γ = embF c σ (IsCMField.complexConj E γ) :=
      Subtype.ext (IsCMField.complexEmbedding_complexConj E σ γ).symm
    have := IsCMField.complexEmbedding_complexConj E (s.comp (embF c σ)) γ
    rw [e]
    exact (congrArg norm this).trans (Complex.norm_conj _)
  have h2 : ∏ σ : E →+* ℂ, ‖s (embF c σ γ)‖ ^ Dw.mult σ =
      ∏ σ : E →+* ℂ, ‖s (embF c σ γ)‖ ^ Dw.mult (ComplexEmbedding.conjugate σ) := by
    rw [← Equiv.prod_comp (ComplexEmbedding.involutive_conjugate E).toPerm]
    simp only [Function.Involutive.coe_toPerm, h1]
  have h3 : |(Algebra.norm ℚ γ : ℝ)| = ∏ σ : E →+* ℂ, ‖s (embF c σ γ)‖ := by
    have hb : Function.Bijective fun σ : E →+* ℂ => s.comp (embF c σ) :=
      Finite.injective_iff_bijective.1 fun σ τ h => RingHom.ext fun x =>
        congrArg Subtype.val (s.injective (DFunLike.congr_fun h x))
    rw [← norm_prod, Fintype.prod_bijective _ hb (fun σ => s (embF c σ γ)) (fun σ => σ γ) fun _ => rfl,
      Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ) (fun σ : E →+* ℂ => σ γ) (fun σ : E →ₐ[ℚ] ℂ => σ γ) fun _ => rfl,
      ← Algebra.norm_eq_prod_embeddings]
    simp
  rw [reflexNorm, map_prod, norm_prod, h3, sq]
  simp only [map_pow, norm_pow]
  nth_rewrite 2 [h2]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_pow]
  exact Finset.prod_congr rfl fun σ _ => by rw [← pow_add, mult_add_mult_conjugate]

theorem isBe_principal (γ : 𝓞 E) : IsBe Dw c (Ideal.span {γ}) (reflexNorm Dw c (γ : E)) := by
  refine ⟨⟨∏ σ : E →+* ℂ, RingOfIntegers.mapRingHom (embF c σ) γ ^ Dw.mult σ, ?_, ?_⟩, fun s => ?_⟩
  · change algebraMap (𝓞 c.F) c.F _ = _
    simp only [map_prod, map_pow]
    rfl
  · simp only [reflexIdeal, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_pow,
      Ideal.prod_span_singleton]
  · rw [norm_reflexNorm, Ideal.absNorm_span_singleton, ← Algebra.coe_norm_int, Nat.cast_natAbs]
    simp

theorem reflexIdeal_mul (𝔞 𝔟 : Ideal (𝓞 E)) :
    reflexIdeal Dw c (𝔞 * 𝔟) = reflexIdeal Dw c 𝔞 * reflexIdeal Dw c 𝔟 := by
  simp only [reflexIdeal, Ideal.map_mul, mul_pow, Finset.prod_mul_distrib]

theorem reflexIdeal_pow (𝔞 : Ideal (𝓞 E)) (h : ℕ) : reflexIdeal Dw c (𝔞 ^ h) = reflexIdeal Dw c 𝔞 ^ h := by
  simp only [reflexIdeal, Ideal.map_pow, ← Finset.prod_pow, ← pow_mul, mul_comm h]

variable {Dw c}

theorem isBe_mul {𝔞 𝔟 : Ideal (𝓞 E)} {α β : c.F} (h : IsBe Dw c 𝔞 α) (h' : IsBe Dw c 𝔟 β) :
    IsBe Dw c (𝔞 * 𝔟) (α * β) := by
  obtain ⟨⟨a, rfl, ha⟩, h⟩ := h
  obtain ⟨⟨b, rfl, hb⟩, h'⟩ := h'
  refine ⟨⟨a * b, rfl, ?_⟩, fun s => ?_⟩
  · rw [reflexIdeal_mul, ← ha, ← hb, Ideal.span_singleton_mul_span_singleton]
  · rw [map_mul, norm_mul, mul_pow, h, h', map_mul, Nat.cast_mul, mul_pow]

theorem isBe_pow {𝔞 : Ideal (𝓞 E)} {α : c.F} (h : IsBe Dw c 𝔞 α) (k : ℕ) : IsBe Dw c (𝔞 ^ k) (α ^ k) := by
  induction k with
  | zero => simpa using isBe_top Dw c
  | succ k ih => rw [pow_succ, pow_succ]; exact isBe_mul ih h

theorem isBe_of_pow {𝔞 : Ideal (𝓞 E)} {ψ : c.F} {k : ℕ} (hk : 0 < k) (h : IsBe Dw c (𝔞 ^ k) (ψ ^ k)) :
    IsBe Dw c 𝔞 ψ := by
  obtain ⟨⟨b, hb, hI⟩, h⟩ := h
  have hψ : IsIntegral ℤ ψ := IsIntegral.of_pow hk (hb ▸ b.isIntegral_coe)
  obtain ⟨b₀, rfl⟩ : ∃ b₀ : 𝓞 c.F, (b₀ : c.F) = ψ := ⟨⟨ψ, hψ⟩, rfl⟩
  refine ⟨⟨b₀, rfl, ?_⟩, fun s => ?_⟩
  · have e : b = b₀ ^ k := RingOfIntegers.ext hb
    rw [e, ← Ideal.span_singleton_pow, reflexIdeal_pow] at hI
    exact pow_left_injective hk.ne' hI
  · have := h s
    rw [map_pow, norm_pow, map_pow, Nat.cast_pow, ← pow_mul, ← pow_mul, mul_comm k, mul_comm k, pow_mul,
      pow_mul] at this
    exact (pow_left_inj₀ (by positivity) (by positivity) hk.ne').1 this

variable (Dw c)

end GlobalTheory.LatticeBetaCompare
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DetIdealSelfDualLatticeAndInterStandardStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

theorem _root_.GlobalTheory.T.detIdeal_selfDual_lattice_and_inter_standard : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (Λ : GenLat E n), Λ.Unimod → ∃ J : Ideal (𝓞 E), J ≠ ⊥ ∧ Ideal.absNorm J = (Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index ∧ Submodule.span (𝓞 E) (detSet Λ.Ln) = J • Submodule.span (𝓞 E) (detSet Λ.La) ∧ Submodule.span (𝓞 E) (detSet Λ.Ln) = Submodule.map (Algebra.linearMap (𝓞 E) E) (conjI J) ∧ ∀ h : Matrix (Fin n) (Fin n) E, Submodule.span (𝓞 E) (detSet (actLat h Λ).La) = Submodule.map (LinearMap.mulLeft (𝓞 E) h.det) (Submodule.span (𝓞 E) (detSet Λ.La)) := by
  first | exact @GlobalTheory.DetIdeal.detIdeal_selfDual | exact GlobalTheory.DetIdeal.detIdeal_selfDual | (intros; apply GlobalTheory.DetIdeal.detIdeal_selfDual <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ReflexNormMulConj

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

noncomputable section

namespace GlobalTheory.BetaChange

open GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal GlobalTheory.LatticeBetaCompare GlobalTheory.SW.Nbr
open scoped nonZeroDivisors

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem form_adj (h : Matrix (Fin n) (Fin n) E) (v w : Fin n → E) :
    ∑ j, IsCMField.complexConj E (v j) * h.mulVec w j =
      ∑ j, IsCMField.complexConj E ((adjM h).mulVec v j) * w j := by

  simp only [Matrix.mulVec, dotProduct, adjM, Matrix.of_apply, map_sum, map_mul,
  IsCMField.complexConj_apply_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem unimod_act {h : Matrix (Fin n) (Fin n) E} (hu : IsUnitaryM h) {Λ : GenLat E n} (hΛ : Λ.Unimod) :
    (actLat h Λ).Unimod := by
  have h1 : adjM h * h = 1 := hu
  have h2 : h * adjM h = 1 := mul_eq_one_comm.1 h1
  intro v
  have e : v ∈ (actLat h Λ).La ↔ (adjM h).mulVec v ∈ Λ.La := by
    constructor
    · rintro ⟨u, hu, rfl⟩
      change (adjM h).mulVec (h.mulVec u) ∈ _
      rwa [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
    · intro hv
      refine ⟨_, hv, ?_⟩
      change h.mulVec _ = _
      rw [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
  rw [e, hΛ]
  constructor
  · rintro hv _ ⟨u, hu, rfl⟩
    exact (form_adj h v u).symm ▸ hv u hu
  · intro hv w hw
    rw [← form_adj]
    exact hv _ ⟨w, hw, rfl⟩

variable {H : Host E} (Dw : Datum H) {l : Geo.Tor.Level H} (c : Coeff l)

theorem reflexNorm_mul_conj (g : 𝓞 E) :
    reflexNorm Dw c ((g * co g : 𝓞 E) : E) = ((Ideal.absNorm (Ideal.span {g}) ^ (Dw.p + Dw.q) : ℕ) : c.F) := by
  have h := (isBe_principal Dw c g).2 c.F.val.toRingHom
  apply c.F.val.toRingHom.injective
  rw [map_natCast]
  have e : c.F.val.toRingHom (reflexNorm Dw c ((g * co g : 𝓞 E) : E)) =
      c.F.val.toRingHom (reflexNorm Dw c (g : E)) * conj (c.F.val.toRingHom (reflexNorm Dw c (g : E))) := by
    simp only [reflexNorm, map_prod, map_pow, ← Finset.prod_mul_distrib, ← mul_pow]
    refine Finset.prod_congr rfl fun σ _ => ?_
    congr 1
    change σ ((g : E) * IsCMField.complexConj E (g : E)) = σ g * conj (σ g)
    rw [map_mul, IsCMField.complexEmbedding_complexConj]
  rw [e, Complex.mul_conj', ← Complex.ofReal_pow, h]
  push_cast
  rfl

theorem isBe_mul_conj (J : Ideal (𝓞 E)) (hJ : J ≠ ⊥) :
    IsBe Dw c (J * conjI J) ((Ideal.absNorm J ^ (Dw.p + Dw.q) : ℕ) : c.F) := by
  let I₀ : (Ideal (𝓞 E))⁰ := ⟨J, mem_nonZeroDivisors_of_ne_zero hJ⟩
  obtain ⟨k, hk, e⟩ := (isOfFinOrder_of_finite (ClassGroup.mk0 I₀)).exists_pow_eq_one
  rw [← map_pow] at e
  obtain ⟨g, hg⟩ : (J ^ k).IsPrincipal := (ClassGroup.mk0_eq_one_iff (I₀ ^ k).2).1 e
  change J ^ k = Ideal.span {g} at hg
  refine isBe_of_pow hk ?_
  have e1 : (J * conjI J) ^ k = Ideal.span {g * co g} := by
    rw [mul_pow, conjI_eq, ← Ideal.map_pow, hg, Ideal.map_span, Set.image_singleton,
      Ideal.span_singleton_mul_span_singleton]
  have e2 : ((Ideal.absNorm J ^ (Dw.p + Dw.q) : ℕ) : c.F) ^ k = reflexNorm Dw c ((g * co g : 𝓞 E) : E) := by
    rw [reflexNorm_mul_conj, ← hg, map_pow, ← Nat.cast_pow, ← pow_mul, ← pow_mul, mul_comm k]
  rw [e1, e2]
  exact isBe_principal Dw c _

theorem isBe_of_isBeta {Λ : GenLat E n} (hΛ : Λ.Unimod) {b : c.F} (hb : IsBeta Dw c Λ b) {J : Ideal (𝓞 E)}
    (hN : Ideal.absNorm J = (Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index)
    (hJ : detSpan Λ.Ln = J • detSpan Λ.La) : IsBe Dw c J b := by
  have hu0 : IsUnit (detSpan Λ.La) :=
    isUnit_detSpan (GenusLatCompare.latEquiv.symm ⟨Λ, GenusLatCompare.isLat_of_unimod Λ hΛ⟩)
  have hu : IsUnit (∏ τ : E →+* ℂ, idealAt c Λ.La τ ^ Dw.mult τ) :=
    IsUnit.prod_iff.2 fun τ _ => by rw [idealAt_eq]; exact (hu0.map _).pow _
  obtain ⟨-, h1, h2⟩ := hb
  refine ⟨?_, fun s => by rw [hN]; exact h2 s⟩
  have e : ∀ τ, idealAt c Λ.Ln τ =
      coeI c.F (J.map (RingOfIntegers.mapRingHom (embF c τ))) * idealAt c Λ.La τ := fun τ => by
    rw [idealAt_eq, idealAt_eq, hJ, smul_eq_coeI_mul, map_mul, extend_coeI]
  rw [← span_eq_coeI_iff, coeI_reflexIdeal]
  rw [BetaIs] at h1
  simp only [e, mul_pow, Finset.prod_mul_distrib] at h1
  exact hu.mul_left_inj.1 h1

omit [IsCMField E] in
theorem map_mulLeft_eq (x : E) (M : Submodule (𝓞 E) E) :
    Submodule.map (LinearMap.mulLeft (𝓞 E) x) M = Submodule.span (𝓞 E) {x} * M := by
  ext y
  rw [Submodule.mem_span_singleton_mul]
  rfl

omit [IsCMField E] in
theorem coeI_span (u : 𝓞 E) : coeI E (Ideal.span {u}) = Submodule.span (𝓞 E) {(u : E)} :=
  IsLocalization.coeSubmodule_span_singleton E u

theorem beta_sq_compare : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (c : Coeff l), ∀ (n : ℕ) (Λ : GenLat E n) (h : Matrix (Fin n) (Fin n) E) (b b' : c.F), Λ.Unimod → IsUnitaryM h → IsBeta Dw c Λ b → IsBeta Dw c (actLat h Λ) b' → ∃ m : ℕ, 0 < m ∧ (b ^ 2 * ((((actLat h Λ).Ln.toAddSubgroup.addSubgroupOf (actLat h Λ).La.toAddSubgroup).index ^ (Dw.p + Dw.q) : ℕ) : c.F)) ^ m = (b' ^ 2 * ((((Λ).Ln.toAddSubgroup.addSubgroupOf (Λ).La.toAddSubgroup).index ^ (Dw.p + Dw.q) : ℕ) : c.F) * ∏ τ : E →+* ℂ, embF c τ h.det ^ Dw.mult τ) ^ m := by
  intro E _ _ _ H Dw l c n Λ h b b' hΛ hu hb hb'
  have hΛ' := unimod_act hu hΛ
  obtain ⟨J, hJ0, hN, hJ1, hJ2, hdet⟩ := GlobalTheory.T.detIdeal_selfDual_lattice_and_inter_standard E n Λ hΛ
  obtain ⟨J', hJ0', hN', hJ1', hJ2', -⟩ := GlobalTheory.T.detIdeal_selfDual_lattice_and_inter_standard E n _ hΛ'
  have hB := isBe_of_isBeta Dw c hΛ hb hN hJ1
  have hB' := isBe_of_isBeta Dw c hΛ' hb' hN' hJ1'
  obtain ⟨u, v, hv, huv⟩ := IsFractionRing.div_surjective (A := 𝓞 E) h.det
  have hv0 : v ≠ 0 := nonZeroDivisors.ne_zero hv
  have hvE : (v : E) ≠ 0 := by simpa using hv0
  have huv' : (u : E) = h.det * (v : E) := by
    rw [← huv]; exact (div_mul_cancel₀ _ hvE).symm
  have k1 : coeI E (conjI J) = coeI E J * detSpan Λ.La := by
    rw [← smul_eq_coeI_mul]; exact hJ2.symm.trans hJ1
  have k2 : coeI E (conjI J') = coeI E J' * (Submodule.span (𝓞 E) {h.det} * detSpan Λ.La) := by
    rw [← smul_eq_coeI_mul, ← map_mulLeft_eq]
    exact (hJ2'.symm.trans hJ1').trans (by rw [hdet]; rfl)
  have key : conjI J' * J * Ideal.span {v} = conjI J * J' * Ideal.span {u} := by
    apply IsFractionRing.coeSubmodule_injective (𝓞 E) E
    change coeI E _ = coeI E _
    simp only [map_mul, k1, k2, coeI_span]
    rw [huv', ← Set.singleton_mul_singleton, ← Submodule.span_mul_span]
    ring
  have a1 := isBe_mul (isBe_mul (isBe_pow hB 2) (isBe_mul_conj Dw c J' hJ0')) (isBe_principal Dw c v)
  have a2 := isBe_mul (isBe_mul (isBe_pow hB' 2) (isBe_mul_conj Dw c J hJ0)) (isBe_principal Dw c u)
  have e : J' ^ 2 * (J * conjI J) * Ideal.span {u} = J ^ 2 * (J' * conjI J') * Ideal.span {v} := by
    calc _ = J * J' * (conjI J * J' * Ideal.span {u}) := by ring
      _ = _ := by rw [← key]; ring
  rw [e] at a2
  have hc : conjI J' ≠ ⊥ := fun h0 => hJ0' (by
    rw [← conjI_conjI J', h0, conjI_eq, Ideal.map_bot])
  have hs : Ideal.span {v} ≠ (⊥ : Ideal (𝓞 E)) := by simpa using hv0
  obtain ⟨z, hz, ez⟩ := isBe_unique
    (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hJ0) (mul_ne_zero hJ0' hc)) hs) a2 a1
  obtain ⟨m, hm, hzm⟩ := hz.exists_pow_eq_one
  have hψ : reflexNorm Dw c (v : E) ≠ 0 := isBe_ne_zero hs (isBe_principal Dw c v)
  have hψu : reflexNorm Dw c (u : E) = (∏ τ : E →+* ℂ, embF c τ h.det ^ Dw.mult τ) * reflexNorm Dw c (v : E) := by
    simp only [huv', reflexNorm, map_mul, mul_pow, Finset.prod_mul_distrib]
  rw [hψu, ← _root_.mul_assoc, ← _root_.mul_assoc, hN, hN'] at ez
  have ez' := mul_right_cancel₀ hψ ez
  refine ⟨m, hm, ?_⟩
  rw [ez', _root_.mul_assoc z, mul_pow z, hzm, _root_.one_mul]

end GlobalTheory.BetaChange
end
end
end
