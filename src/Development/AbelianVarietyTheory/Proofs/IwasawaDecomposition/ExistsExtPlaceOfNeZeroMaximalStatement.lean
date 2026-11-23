module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import ReciprocityTheory.GaloisValuations.GlobalB
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.FiniteType
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringLiftOfSpecialFibre
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.TypeStar
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRatA
import Mathlib.RingTheory.Valuation.LocalSubring
import ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRatA

-- Source module: Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyExt

section

@[expose] public section

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.TrueGeo
namespace GlobalTheory.TrueGeoModel
variable {F : Type} [Field F] [NumberField F]

theorem nonempty_ext (v : HeightOneSpectrum (𝓞 F)) : Nonempty (Ext v) := by
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  let K := v.adicCompletion F
  have h1 : ‖FinitePlace.embedding v (algebraMap (𝓞 F) F a)‖ < 1 := (FinitePlace.norm_lt_one_iff_mem F v a).2 ha
  have h0 : FinitePlace.embedding v (algebraMap (𝓞 F) F a) ≠ 0 := by
    simpa using ha0
  letI : NontriviallyNormedField K := NontriviallyNormedField.ofNormNeOne ⟨_, h0, h1.ne⟩
  let L := AlgebraicClosure K
  letI : Algebra F L := ((algebraMap K L).comp (FinitePlace.embedding v)).toAlgebra
  let j : AlgebraicClosure F →ₐ[F] L := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let N := spectralMulAlgNorm K L
  let w : AbsoluteValue (AlgebraicClosure F) ℝ :=
    (MulRingNorm.mulRingNormEquivAbsoluteValue N.toMulRingNorm).comp (f := j.toRingHom) j.injective
  have hw (x) : w x = spectralNorm K L (j x) := rfl
  have hn (x y) : w (x + y) ≤ max (w x) (w y) := by
    rw [hw, hw, hw, map_add (f := _)]; exact isNonarchimedean_spectralNorm _ _
  refine ⟨⟨w, fun x => ?_, ⟨⟨⟨⟨⟨{x | w x ≤ 1}, ?_⟩, by simp⟩, ?_, by simp⟩, ?_⟩, ?_⟩, fun _ => Iff.rfl⟩⟩
  · rw [hw, j.commutes, ← FinitePlace.norm_embedding]
    exact spectralNorm_extends _
  · intro x y hx hy
    simp only [Set.mem_setOf_eq, map_mul] at *
    exact mul_le_one₀ hx (w.nonneg _) hy
  · intro x y hx hy
    exact (hn x y).trans (max_le hx hy)
  · intro x hx
    simpa using hx
  · intro x
    rcases le_total (w x) 1 with h | h
    · exact .inl h
    · refine .inr ?_
      change w x⁻¹ ≤ 1
      rw [map_inv₀]; exact inv_le_one_of_one_le₀ h

end GlobalTheory.TrueGeoModel
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClosedPointGeometricFibresFinite

section

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.ExtConj
variable {F : Type} [Field F] [NumberField F]

theorem valuation_lt_one_iff {v : HeightOneSpectrum (𝓞 F)} (e : Ext v) (y : AlgebraicClosure F) :
    e.O.valuation y < 1 ↔ e.w y < 1 := by
  rw [ReciprocityTheory.Gal.valuation_lt_one_iff', e.mem_O, e.mem_O, map_inv₀]
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · have h0 : 0 < e.w y := e.w.pos hy
    simp only [hy, false_or, not_le, one_lt_inv₀ h0]
    exact ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩

theorem lies_over {v : HeightOneSpectrum (𝓞 F)} (e : Ext v) (x : 𝓞 F) :
    e.O.valuation (algebraMap F (AlgebraicClosure F) (x : F)) < 1 ↔ x ∈ v.asIdeal := by
  rw [valuation_lt_one_iff, e.w_alg, ← FinitePlace.norm_embedding]
  exact FinitePlace.norm_lt_one_iff_mem F v x

theorem conj (v : HeightOneSpectrum (𝓞 F)) (e e' : Ext v) :
    ∃ g : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F, ∀ x, e'.w x = e.w (g x) := by
  obtain ⟨g, hg⟩ := ReciprocityTheory.Gal.exists_smul_eq_of_over (lies_over e) (lies_over e')
  refine ⟨g⁻¹, ?_⟩
  let u : AbsoluteValue (AlgebraicClosure F) ℝ :=
    e.w.comp (f := (g⁻¹ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F).toRingEquiv.toRingHom) (g⁻¹).injective
  have hu (x) : u x = e.w (g⁻¹ x) := rfl
  have he : u.IsEquiv e'.w := AbsoluteValue.isEquiv_iff_lt_one_iff.2 fun x => by
    rw [hu, ← valuation_lt_one_iff, ← valuation_lt_one_iff, ← hg, ReciprocityTheory.Gal.smul_valuation_lt_one_iff]
  obtain ⟨c, hc, hce⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.1 he
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  have h1 : e'.w (algebraMap F _ (a : F)) < 1 := (valuation_lt_one_iff e' _).1 ((lies_over e' a).2 ha)
  have h0 : 0 < e'.w (algebraMap F _ (a : F)) := e'.w.pos (by simpa using ha0)
  have h2 : u (algebraMap F _ (a : F)) = e'.w (algebraMap F _ (a : F)) := by
    rw [hu, AlgEquiv.commutes, e.w_alg, e'.w_alg]
  have h3 := congrFun hce (algebraMap F _ (a : F))
  simp only [h2] at h3
  have hc1 : c = 1 := by
    have h4 := congrArg Real.log h3
    rw [Real.log_rpow h0] at h4
    have := (Real.log_neg h0 h1).ne
    exact mul_right_cancel₀ this (by rw [h4, one_mul])
  intro x
  rw [← hu, ← hce, hc1]
  simp

theorem factor {K : Type} [Field K] {X : Scheme.{0}} (y : Sp K ⟶ X) (x : X) (h : below y = x) :
    ∃ ψ : X.residueField x ⟶ CommRingCat.of K, Spec.map ψ ≫ X.fromSpecResidueField x = y := by
  subst h
  exact ⟨_, Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K X y⟩

theorem below_comp {K : Type} [Field K] {X : Scheme.{0}} (x : X) (ψ : X.residueField x ⟶ CommRingCat.of K) :
    below (K := K) (Spec.map ψ ≫ X.fromSpecResidueField x) = x :=
  (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply x _)

theorem closed_point_geometric_fibres_finite {k K : Type} [Field k] [Field K] [Algebra k K] [IsAlgClosed K] {X : Scheme.{0}} (s : X ⟶ Sp k)
    [LocallyOfFiniteType s] (x : X) (hx : IsClosed ({x} : Set X)) :
    Nonempty {y : {y : Sp K ⟶ X // y ≫ s = spMap (algebraMap k K)} // below y.1 = x} ∧
      Finite {y : {y : Sp K ⟶ X // y ≫ s = spMap (algebraMap k K)} // below y.1 = x} := by
  have := isClosed_singleton_iff_isClosedImmersion.1 hx
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (X.fromSpecResidueField x ≫ s)
  have hfin : IsFinite (Spec.map φ) := by
    rw [hφ]
    exact isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.2 inferInstance
  letI : Algebra k (X.residueField x) := φ.hom.toAlgebra
  haveI : Module.Finite k (X.residueField x) := (IsFinite.SpecMap_iff φ).1 hfin
  have hP (ψ : X.residueField x →ₐ[k] K) :
      (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ X.fromSpecResidueField x) ≫ s = spMap (algebraMap k K) := by
    have h : φ ≫ CommRingCat.ofHom ψ.toRingHom = CommRingCat.ofHom (algebraMap k K) :=
      CommRingCat.hom_ext ψ.comp_algebraMap
    rw [Category.assoc, ← hφ, ← Spec.map_comp]
    exact congrArg Spec.map h
  let P : (X.residueField x →ₐ[k] K) → {y : {y : Sp K ⟶ X // y ≫ s = spMap (algebraMap k K)} // below y.1 = x} :=
    fun ψ => ⟨⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ X.fromSpecResidueField x, hP ψ⟩,
      below_comp x _⟩
  refine ⟨⟨P IsAlgClosed.lift⟩, Finite.of_surjective P ?_⟩
  rintro ⟨⟨y, hy⟩, hyx⟩
  obtain ⟨ψ, h⟩ := factor y x hyx
  have h2 : Spec.map (φ ≫ ψ) = Spec.map (CommRingCat.ofHom (algebraMap k K)) := by
    rw [Spec.map_comp, hφ, ← Category.assoc, h]
    exact hy
  have h3 := Spec.map_injective h2
  exact ⟨⟨ψ.hom, fun a => congrArg (fun t => t.hom a) h3⟩, Subtype.ext (Subtype.ext h)⟩

theorem pts (Y : Var F) (x : Y.X) (hx : IsClosed ({x} : Set Y.X)) :
    Nonempty {y : AlgPt Y // below y.1 = x} ∧ Finite {y : AlgPt Y // below y.1 = x} :=
  closed_point_geometric_fibres_finite Y.str x hx

theorem main : ∀ (F : Type) [Field F] [NumberField F] , (∀ v : HeightOneSpectrum (𝓞 F), Nonempty (Ext v)) ∧ (∀ Y : Var F, ∀ x : Y.X, IsClosed ({x} : Set Y.X) → Nonempty {y : AlgPt Y // below y.1 = x} ∧ Finite {y : AlgPt Y // below y.1 = x}) ∧ ∀ (v : HeightOneSpectrum (𝓞 F)) (e e' : Ext v), ∃ g : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F, ∀ x, e'.w x = e.w (g x) :=
  fun _ _ _ => ⟨GlobalTheory.TrueGeoModel.nonempty_ext, pts, conj⟩

end GlobalTheory.TrueGeo.ExtConj
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHorizontalPrimeLeOfIsMaximal

section

@[expose] public section

namespace GlobalTheory

theorem exists_intCast_mem_of_isMaximal (R : Type*) [CommRing R] [Algebra.FiniteType ℤ R]
    (m : Ideal R) [m.IsMaximal] : ∃ p : ℤ, p ≠ 0 ∧ algebraMap ℤ R p ∈ m := by
  let := Ideal.Quotient.field m
  have := ReciprocityTheory.AnForm.R.IntegerToRational.isJacobsonRing_int
  have : Module.Finite ℤ (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℤ _
  by_contra h
  push Not at h
  have hinj : Function.Injective (algebraMap ℤ (R ⧸ m)) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra ha0
    apply h a ha0
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simpa using ha
  have hF : IsField ℤ :=
    (Algebra.IsIntegral.isField_iff_isField hinj).mpr (Field.toIsField (R ⧸ m))
  exact Int.not_isField hF

theorem exists_horizontal_prime_le_of_isMaximal :
    ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra.FiniteType ℤ R] [CharZero R] (𝔪 : Ideal R),
      𝔪.IsMaximal → ∀ g : R, g ≠ 0 → ∃ q : Ideal R, q.IsPrime ∧ q ≤ 𝔪 ∧ g ∉ q ∧
        CharZero (R ⧸ q) ∧ Algebra.IsAlgebraic ℤ (R ⧸ q) := by
  intro R _ _ _ _ m hm g hg
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  obtain ⟨p₀, hp₀, hp₀m⟩ := exists_intCast_mem_of_isMaximal R m
  obtain ⟨p, hp⟩ := (IsPrincipalIdealRing.principal (m.comap (algebraMap ℤ R))).principal
  have hp' : m.comap (algebraMap ℤ R) = Ideal.span {p} := hp
  have hp0 : p ≠ 0 := by
    rintro rfl
    have : p₀ ∈ m.comap (algebraMap ℤ R) := hp₀m
    rw [hp'] at this
    exact hp₀ (by simpa using this)
  have hpprime : Prime p := by
    rw [← Ideal.span_singleton_prime hp0, ← hp']
    infer_instance
  have hpm : algebraMap ℤ R p ∈ m := by
    have : p ∈ m.comap (algebraMap ℤ R) := hp' ▸ Ideal.mem_span_singleton_self p
    exact this
  set x : R := algebraMap ℤ R p * g with hx
  have hx0 : x ≠ 0 := mul_ne_zero (by simpa using hp0) hg
  obtain ⟨q, ⟨hqp, hqm, hxq⟩, hmax⟩ := set_has_maximal_iff_noetherian.mpr
    (inferInstance : IsNoetherian R R) {q : Ideal R | q.IsPrime ∧ q ≤ m ∧ x ∉ q}
    ⟨⊥, Ideal.isPrime_bot, bot_le, by simpa using hx0⟩
  change Ideal R at q
  have hpq : algebraMap ℤ R p ∉ q := fun h => hxq (q.mul_mem_right _ h)
  have hinj : Function.Injective (algebraMap ℤ (R ⧸ q)) := by
    have hq' : (q.comap (algebraMap ℤ R)).IsPrime := inferInstance
    have hbot : q.comap (algebraMap ℤ R) = ⊥ := by
      by_contra hne
      have hM : (q.comap (algebraMap ℤ R)).IsMaximal := IsPrime.to_maximal_ideal hne
      have := hM.eq_of_le (Ideal.IsPrime.ne_top inferInstance) (Ideal.comap_mono (f := algebraMap ℤ R) hqm)
      apply hpq
      have h2 : p ∈ q.comap (algebraMap ℤ R) := this ▸ hpm
      exact h2
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    have : a ∈ q.comap (algebraMap ℤ R) := by
      rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem]
      simpa using ha
    rwa [hbot, Ideal.mem_bot] at this
  have hsurj := Ideal.Quotient.mk_surjective (I := q)
  refine ⟨q, hqp, hqm, fun h => hxq (q.mul_mem_left _ h), charZero_of_injective_algebraMap hinj, ?_⟩
  have hm' : (m.map (Ideal.Quotient.mk q)).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le hsurj (by simpa using hqm)
  have hcm : (m.map (Ideal.Quotient.mk q)).comap (Ideal.Quotient.mk q) = m := by
    rw [Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact sup_eq_left.mpr hqm
  have h1 : (m.map (Ideal.Quotient.mk q)).height ≤ 1 := by
    refine height_le_one_of_forall_mem _ (f := Ideal.Quotient.mk q x)
      (by simpa [Ideal.Quotient.eq_zero_iff_mem] using hxq) ?_
    intro P hP hP0 hPm
    by_contra hxP
    refine hmax (P.comap (Ideal.Quotient.mk q)) ⟨inferInstance, ?_, hxP⟩ ?_
    · exact hcm ▸ Ideal.comap_mono hPm
    · refine lt_of_le_of_ne ?_ ?_
      · intro a ha
        rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr ha]
        exact P.zero_mem
      · intro e
        apply hP0
        rw [eq_bot_iff]
        intro b hb
        obtain ⟨a, rfl⟩ := hsurj b
        have : a ∈ q := e ▸ hb
        exact Ideal.Quotient.eq_zero_iff_mem.mpr this
  have : Algebra.QuasiFiniteAt ℤ (m.map (Ideal.Quotient.mk q)) :=
    quasiFiniteAt_of_height_le_one _ h1 p (fun e => hp0 (hinj (by simpa using e)))
      (Ideal.mem_map_of_mem _ hpm)
  have : FaithfulSMul ℤ (R ⧸ q) := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  exact isAlgebraic_of_quasiFiniteAt ℤ (R ⧸ q) (m.map (Ideal.Quotient.mk q))

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExtPlaceOfNeZeroMaximal

section

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
open Pointwise

namespace GlobalTheory.TrueGeo.HorizRing

variable {F : Type} [Field F] [NumberField F]

theorem exists_embed (B : Type) [CommRing B] [IsDomain B] [Algebra (𝓞 F) B] [CharZero B] [Algebra.IsAlgebraic ℤ B] :
    ∃ ψ : B →ₐ[𝓞 F] AlgebraicClosure F, Function.Injective ψ := by
  have hinj : Function.Injective (algebraMap (𝓞 F) B) := by
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_
    change Ideal.comap (algebraMap ℤ (𝓞 F)) (RingHom.ker (algebraMap (𝓞 F) B)) = ⊥
    rw [RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
    exact RingHom.injective_int _
  haveI : Algebra.IsAlgebraic (𝓞 F) B :=
    Algebra.IsAlgebraic.extendScalars (R := ℤ) (RingHom.injective_int _)
  haveI : Module.IsTorsionFree (𝓞 F) B := Module.isTorsionFree_iff_algebraMap_injective.2 hinj
  haveI : Module.IsTorsionFree (𝓞 F) (AlgebraicClosure F) := by
    rw [Module.isTorsionFree_iff_algebraMap_injective, IsScalarTower.algebraMap_eq (𝓞 F) F (AlgebraicClosure F)]
    exact (algebraMap F _).injective.comp (IsFractionRing.injective (𝓞 F) F)
  let ψ : B →ₐ[𝓞 F] AlgebraicClosure F := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨ψ, ?_⟩
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra h0
  refine Ideal.comap_ne_bot_of_algebraic_mem (R := ℤ) (I := RingHom.ker ψ.toRingHom) h0 hx
    (Algebra.IsAlgebraic.isAlgebraic x) ?_
  change Ideal.comap (algebraMap ℤ B) (RingHom.ker ψ.toRingHom) = ⊥
  rw [RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
  exact RingHom.injective_int _

theorem comap_ne_bot {R : Type} [CommRing R] [Algebra (𝓞 F) R] [Algebra.FiniteType (𝓞 F) R] (𝔪 : Ideal R)
    [h : 𝔪.IsMaximal] : 𝔪.comap (algebraMap (𝓞 F) R) ≠ ⊥ := by
  intro h0
  letI := Ideal.Quotient.field 𝔪
  haveI := ReciprocityTheory.AnForm.R.IntegerToRational.isJacobsonRing_int
  haveI : IsJacobsonRing (𝓞 F) := isJacobsonRing_of_isIntegral (R := ℤ)
  haveI : Module.Finite (𝓞 F) (R ⧸ 𝔪) := finite_of_finite_type_of_isJacobsonRing _ _
  have hinj : Function.Injective (algebraMap (𝓞 F) (R ⧸ 𝔪)) := by
    rw [RingHom.injective_iff_ker_eq_bot, IsScalarTower.algebraMap_eq (𝓞 F) R (R ⧸ 𝔪), ← RingHom.comap_ker,
      Ideal.Quotient.algebraMap_eq, Ideal.mk_ker, h0]
  exact RingOfIntegers.not_isField F
    ((Algebra.IsIntegral.isField_iff_isField hinj).2 (Field.toIsField _))

theorem exists_valuationSubring {R K : Type} [CommRing R] [Field K] (ψ : R →+* K) (𝔪 : Ideal R) [h : 𝔪.IsMaximal]
    (hk : RingHom.ker ψ ≤ 𝔪) : ∃ A : ValuationSubring K, (∀ x, ψ x ∈ A) ∧ ∀ x, A.valuation (ψ x) < 1 ↔ x ∈ 𝔪 := by
  have hs := ψ.rangeRestrict_surjective
  have hc : (𝔪.map ψ.rangeRestrict).comap ψ.rangeRestrict = 𝔪 := by
    rw [Ideal.comap_map_of_surjective _ hs, sup_eq_left, ← RingHom.ker_eq_comap_bot, RingHom.ker_rangeRestrict]
    exact hk
  have hne : 𝔪.map ψ.rangeRestrict ≠ ⊤ := fun ht => h.ne_top (by rw [← hc, ht, Ideal.comap_top])
  obtain ⟨A, hA, hI⟩ := Ideal.image_subset_nonunits_valuationSubring (A := ψ.range) _ hne
  have hm : ∀ x, ψ x ∈ A := fun x => hA ⟨x, rfl⟩
  refine ⟨A, hm, ?_⟩
  let φ : R →+* A := ψ.codRestrict A hm
  have hle : 𝔪 ≤ (IsLocalRing.maximalIdeal A).comap φ := fun x hx => by
    rw [Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff]
    exact hI ⟨_, Ideal.mem_map_of_mem _ hx, rfl⟩
  have he := h.eq_of_le (Ideal.comap_ne_top φ (IsLocalRing.maximalIdeal.isMaximal A).ne_top) hle
  intro x
  rw [he, Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff]
  rfl

theorem main : ∀ (F : Type) [Field F] [NumberField F] (R : Type) [CommRing R] [IsDomain R] [Algebra (𝓞 F) R] [Algebra.FiniteType (𝓞 F) R] [CharZero R] (𝔪 : Ideal R), 𝔪.IsMaximal → ∀ g : R, g ≠ 0 → ∃ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (φ : R →+* e.O), (∀ a : 𝓞 F, ((φ (algebraMap (𝓞 F) R a) : e.O) : AlgebraicClosure F) = algebraMap F (AlgebraicClosure F) (algebraMap (𝓞 F) F a)) ∧ (IsLocalRing.maximalIdeal e.O).comap φ = 𝔪 ∧ φ g ≠ 0 := by
  intro F _ _ R _ _ _ _ _ 𝔪 h𝔪 g hg
  haveI : Algebra.FiniteType ℤ R := Algebra.FiniteType.trans (S := 𝓞 F) inferInstance inferInstance
  obtain ⟨q, hq, hqm, hgq, hc, ha⟩ := GlobalTheory.exists_horizontal_prime_le_of_isMaximal R 𝔪 h𝔪 g hg
  obtain ⟨ψ₀, hψ₀⟩ := @exists_embed F _ _ (R ⧸ q) _ _ _ hc (by convert ha <;> first | rfl | exact Subsingleton.elim _ _)
  let ψ : R →ₐ[𝓞 F] AlgebraicClosure F := ψ₀.comp (Ideal.Quotient.mkₐ (𝓞 F) q)
  have hker : ∀ x, ψ x = 0 ↔ x ∈ q := fun x => by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← map_eq_zero_iff ψ₀ hψ₀]
    rfl
  have hψ (a : 𝓞 F) : ψ (algebraMap (𝓞 F) R a) = algebraMap F (AlgebraicClosure F) (algebraMap (𝓞 F) F a) := by
    rw [ψ.commutes, ← IsScalarTower.algebraMap_apply]
  obtain ⟨A, hA, hAm⟩ := exists_valuationSubring ψ.toRingHom 𝔪 (fun x hx => hqm ((hker x).1 hx))
  let v : HeightOneSpectrum (𝓞 F) := ⟨𝔪.comap (algebraMap (𝓞 F) R), inferInstance, comap_ne_bot 𝔪⟩
  obtain ⟨e⟩ := (ExtConj.main F).1 v
  have hov (x : 𝓞 F) : A.valuation (algebraMap F (AlgebraicClosure F) (x : F)) < 1 ↔ x ∈ v.asIdeal := by
    have := hAm (algebraMap (𝓞 F) R x)
    rwa [show ψ.toRingHom (algebraMap (𝓞 F) R x) = _ from hψ x] at this
  obtain ⟨σ, hσ⟩ := ReciprocityTheory.Gal.exists_smul_eq_of_over hov (ExtConj.lies_over e)
  have hm (x : R) : σ (ψ x) ∈ e.O := by
    rw [← hσ]
    exact ValuationSubring.smul_mem_pointwise_smul σ _ A (hA x)
  let φ : R →+* e.O := (σ.toRingEquiv.toRingHom.comp ψ.toRingHom).codRestrict e.O hm
  have hφ (x : R) : (φ x : AlgebraicClosure F) = σ (ψ x) := rfl
  refine ⟨v, e, φ, fun a => ?_, ?_, fun h0 => hgq ?_⟩
  · rw [hφ, hψ, σ.commutes]
  · ext x
    rw [Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff, hφ, ← hAm]
    have := ReciprocityTheory.Gal.smul_valuation_lt_one_iff σ A (σ (ψ x))
    rw [hσ] at this
    rw [this]
    simp
  · have := hφ g
    rw [h0] at this
    exact (hker g).1 (by simpa using this.symm)

end GlobalTheory.TrueGeo.HorizRing
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExtPlaceOfNeZeroMaximalStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

theorem _root_.GlobalTheory.T.exists_ext_place_of_ne_zero_maximal : ∀ (F : Type) [Field F] [NumberField F] (R : Type) [CommRing R] [IsDomain R] [Algebra (𝓞 F) R] [Algebra.FiniteType (𝓞 F) R] [CharZero R] (𝔪 : Ideal R), 𝔪.IsMaximal → ∀ g : R, g ≠ 0 → ∃ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (φ : R →+* e.O), (∀ a : 𝓞 F, ((φ (algebraMap (𝓞 F) R a) : e.O) : AlgebraicClosure F) = algebraMap F (AlgebraicClosure F) (algebraMap (𝓞 F) F a)) ∧ (IsLocalRing.maximalIdeal e.O).comap φ = 𝔪 ∧ φ g ≠ 0 := by
  first | exact @GlobalTheory.TrueGeo.HorizRing.main | exact GlobalTheory.TrueGeo.HorizRing.main | (intros; apply GlobalTheory.TrueGeo.HorizRing.main <;> assumption)
end
end
