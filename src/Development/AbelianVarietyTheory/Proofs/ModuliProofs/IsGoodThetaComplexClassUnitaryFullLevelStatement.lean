module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TypeFnPeriodExistModuliNonempty
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPeriodDomainParam
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPeriodsComplexPELObjectStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FiniteMarkedDataInGenus
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GoodThetaClassOfLatticeFamiliesStatement
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EqZeroOfSumEmbeddingMul
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsPELObjectOfPrimitivePeriodMapUniformised
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PelObjectClassPrimAndIsoClosed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TransportThetaLevelUniformisationCoordinates
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsTypeFnOfRank

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem exists_isTypeFn_of_rank : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ), Nonempty ((Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) → ∃ ty : Fin g → (E →+* ℂ), IsTypeFn H D.p D.q ty := by
  intro E _ _ _ H D g ⟨e⟩
  obtain ⟨g', ty, h, -, P, -, hinj, hdisc, hspan, -⟩ := GlobalTheory.PeriodExists.exists_typeFn_period H D
  let L : Submodule ℤ (Fin g' → ℂ) := LinearMap.range P.toIntLinearMap
  have : DiscreteTopology L := hdisc
  have : IsZLattice ℝ L := ⟨by
    have : (L : Set (Fin g' → ℂ)) = Set.range P := by ext; simp [L]
    rw [this]; exact hspan⟩
  have h1 := ZLattice.rank ℝ L
  have h2 : Module.finrank ℤ L = 2 * g := by
    rw [← (e.trans (LinearEquiv.ofInjective P.toIntLinearMap hinj)).finrank_eq]
    simp
  have h3 : Module.finrank ℝ (Fin g' → ℂ) = 2 * g' := by
    rw [Module.finrank_pi_fintype]; simp [mul_comm]
  obtain rfl : g' = g := by omega
  exact ⟨ty, h⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.ImAdjointOfSpan

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.ConjBound

open GlobalTheory.EigenNorm

variable {g : ℕ}

theorem im_adjoint_of_span (Hm : Matrix (Fin g) (Fin g) ℂ) (t u : Fin g → ℂ) (S : Set (Fin g → ℂ))
    (hS : Submodule.span ℝ S = ⊤)
    (h : ∀ z ∈ S, ∀ w ∈ S, (hermForm Hm (t * z) w).im = (hermForm Hm z (u * w)).im) (z w : Fin g → ℂ) :
    (hermForm Hm (t * z) w).im = (hermForm Hm z (u * w)).im := by
  have hz : z ∈ Submodule.span ℝ S := hS ▸ Submodule.mem_top
  have hw : w ∈ Submodule.span ℝ S := hS ▸ Submodule.mem_top
  have hr : ∀ (r : ℝ) (v : Fin g → ℂ), r • v = (r : ℂ) • v := fun r v => by
    funext i; simp
  induction hz, hw using Submodule.span_induction₂ with
  | mem_mem z w hz hw => exact h z hz w hw
  | zero_left w _ => simp [hermForm]
  | zero_right z _ => simp [hermForm]
  | add_left z z' w _ _ _ h1 h2 =>
    rw [mul_add, hermForm_add_left, hermForm_add_left, Complex.add_im, Complex.add_im, h1, h2]
  | add_right z w w' _ _ _ h1 h2 =>
    rw [mul_add, hermForm_add_right, hermForm_add_right, Complex.add_im, Complex.add_im, h1, h2]
  | smul_left r z w _ _ h1 =>
    rw [hr, mul_smul_comm, hermForm_smul_left, hermForm_smul_left, Complex.im_ofReal_mul, Complex.im_ofReal_mul, h1]
  | smul_right r z w _ _ h1 =>
    rw [hr, mul_smul_comm, hermForm_smul_right, hermForm_smul_right, Complex.conj_ofReal, Complex.im_ofReal_mul,
      Complex.im_ofReal_mul, h1]

theorem hermForm_eq_sum (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    hermForm Hm z w = ∑ i, ∑ j, z i * Hm i j * starRingEnd ℂ (w j) := by
  simp [hermForm, dotProduct, Matrix.mulVec, Finset.mul_sum, _root_.mul_assoc]

theorem entry_comm (Hm : Matrix (Fin g) (Fin g) ℂ) (t : Fin g → ℂ)
    (h : ∀ z w, (hermForm Hm (t * z) w).im = (hermForm Hm z (star t * w)).im) (i j : Fin g) :
    t i * Hm i j = Hm i j * t j := by
  have key : ∀ s : ℂ, (s * (t i * Hm i j)).im = (s * (Hm i j * t j)).im := fun s => by
    have := h (Pi.single i s) (Pi.single j 1)
    rw [hermForm_eq_sum, hermForm_eq_sum] at this
    simp only [Pi.mul_apply, Pi.single_apply, Pi.star_apply, mul_ite, mul_zero, _root_.mul_one, ite_mul, zero_mul,
      apply_ite (starRingEnd ℂ), map_zero, map_one, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      RCLike.star_def, Complex.conj_conj] at this
    convert this using 2 <;> ring
  have h1 := key 1
  have h2 := key Complex.I
  rw [_root_.one_mul, _root_.one_mul] at h1
  rw [Complex.I_mul_im, Complex.I_mul_im] at h2
  exact Complex.ext h2 h1

theorem re_lt_of_comm (Hm : Matrix (Fin g) (Fin g) ℂ) (t : Fin g → ℂ) (κ : ℝ)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re)
    (hc : ∀ i j, t i * Hm i j = Hm i j * t j) (ht : ∀ i, ‖t i‖ ^ 2 < κ) (y : Fin g → ℂ) (hy : y ≠ 0) :
    (hermForm Hm (t * y) (t * y)).re < κ * (hermForm Hm y y).re := by
  let s : Fin g → ℂ := fun i => (Real.sqrt (κ - ‖t i‖ ^ 2) : ℝ)
  have hs0 : ∀ i, s i ≠ 0 := fun i => by
    have : 0 < Real.sqrt (κ - ‖t i‖ ^ 2) := Real.sqrt_pos.2 (sub_pos.2 (ht i))
    exact Complex.ofReal_ne_zero.2 this.ne'
  have hsy : s * y ≠ 0 := fun h0 => hy (by
    funext i
    have := congrFun h0 i
    simpa [hs0 i] using this)
  have hss : ∀ i, s i * starRingEnd ℂ (s i) + t i * starRingEnd ℂ (t i) = κ := fun i => by
    rw [Complex.mul_conj', Complex.mul_conj']
    have : ‖s i‖ ^ 2 = κ - ‖t i‖ ^ 2 := by
      simp only [s, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      exact Real.sq_sqrt (sub_pos.2 (ht i)).le
    rw [← Complex.ofReal_pow, this]
    push_cast; ring
  have hsum : hermForm Hm (s * y) (s * y) + hermForm Hm (t * y) (t * y) = κ * hermForm Hm y y := by
    simp only [hermForm_eq_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases h0 : Hm i j = 0
    · simp [h0]
    · have hij : t i = t j := by
        have := hc i j
        rw [mul_comm] at this
        exact mul_left_cancel₀ h0 this
      have hsij : s i = s j := by simp only [s, hij]
      simp only [Pi.mul_apply, map_mul, hij, hsij, ← hss j]
      ring
  have h1 := hpos _ hsy
  have h2 := congrArg Complex.re hsum
  rw [Complex.add_re, Complex.re_ofReal_mul] at h2
  linarith

theorem exists_action_lt :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Q : D.La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (a : 𝓞 E) (κ : ℕ), (∀ (c : 𝓞 E) x i, Q (c • x) i = ty i (c : E) * Q x i) → (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = D.EF x y) → (∀ τ : E →+* ℂ, ‖τ (a : E)‖ ^ 2 < κ) → ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q x) = Q (a • x)) ∧ ∀ y, y ≠ 0 → (hermForm Hm (F y) (F y)).re < κ * (hermForm Hm y y).re := by
  intro E _ _ _ H D g ty Q Hm a κ hlin ⟨_, _, hspan, _, hpos, him⟩ hκ
  let t : Fin g → ℂ := fun i => ty i (a : E)
  have h1 : ∀ x, t * Q x = Q (a • x) := fun x => funext fun i => (hlin a x i).symm
  have h2 : ∀ x, star t * Q x = Q (H.bar a • x) := fun x => funext fun i => by
    rw [hlin, H.bar_eq, IsCMField.complexEmbedding_complexConj]; rfl
  refine ⟨LinearMap.mulLeft ℂ t, h1, fun y hy => ?_⟩
  refine re_lt_of_comm Hm t κ hpos (entry_comm Hm t (im_adjoint_of_span Hm t (star t) _ hspan ?_))
    (fun i => hκ (ty i)) y hy
  rintro _ ⟨x, rfl⟩ _ ⟨x', rfl⟩
  rw [h1, h2, him, him, D.adj]

end GlobalTheory.ConjBound
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsPELObjectOfPrimitivePeriodMapUniformisedStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.isPELObject_of_primitive_periodMap_uniformised : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (em : o →+* ℂ) (w w' : J) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (ρ : o) (ty : Fin g → (E →+* ℂ)) (t : TObj g k J b (spMap em)) (D' : Datum H) (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν : ℕ → ℤ) (Q : D'.La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), 1 ≤ D.p + D.q → a w = H.w0 → em ρ = H.rt0 → IsTypeFn H D.p D.q ty → (D'.p = D.p ∧ D'.q = D.q ∧ (∀ n m : ℕ, 0 < n → 0 < m → ∀ x, ∃ y, f (n * m) x = f n x + n • y) ∧ (∀ n : ℕ, 0 < n → (∀ x, (∃ y, f n x = n • y) ↔ ∃ y, x = n • y) ∧ ∀ x', ∃ x y, x' = f n x + n • y) ∧ ∀ n : ℕ, 0 < n → ∀ x x', (n : ℤ) ∣ D'.EF (f n x) (f n x') - ν n * D.EF x x') → em (b.ζ : o) = Complex.exp (-(2 * Real.pi * Complex.I) * (ν k : ℂ) / k) → IsPeriod D' ty Q → (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = D'.EF x y) → (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH Hm χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ (Q).range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = Q x → χ' l = (-1) ^ D'.EF x ((fun j x => a j • x) w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((k : ℕ) : ℂ)⁻¹ • Q ((fun i => f k (bas (Pi.single i 1))) i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q x) = Q ((fun j x => a j • x) j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀) → t.Prim w w' → PELClass D a bas ρ em t := by
  first | exact @GlobalTheory.PeriodObject.pelClass_of_period | exact GlobalTheory.PeriodObject.pelClass_of_period | (intros; apply GlobalTheory.PeriodObject.pelClass_of_period <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsGoodThetaComplexClassUnitaryFullLevel

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.PelGood

theorem exists_domain {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D D' : Datum H) {g : ℕ}
    (ty : Fin g → (E →+* ℂ)) (hty : IsTypeFn H D.p D.q ty) (hp : D'.p = D.p) (hq : D'.q = D.q) :
    ∃ (B : Set (Fin D.dim → ℂ)) (P : (Fin D.dim → ℂ) → (D'.La →+ (Fin g → ℂ))), IsOpen B ∧ Convex ℝ B ∧
      IsHolPeriods D' ty B P ∧ ∀ P', IsPeriod D' ty P' →
        ∃! b, b ∈ B ∧ ∃ h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ a, P' a = h (P b a) := by
  have hd : D.dim = D'.dim := by rw [Datum.dim, Datum.dim, hp, hq]
  rw [hd]
  exact exists_period_domain_param E H D' g ty (by rw [hp, hq]; exact hty)

theorem isPeriod_comp {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D D' : Datum H} {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} {Q : D.La →+ (Fin g → ℂ)} (hQ : IsPeriod D ty Q) (e : D.La ≃ₗ[𝓞 E] D'.La)
    (he : ∀ x y, D'.EF (e x) (e y) = D.EF x y) :
    IsPeriod D' ty (Q.comp e.symm.toAddEquiv.toAddMonoidHom) := by
  obtain ⟨h1, h2, h3, h4, Hm, h5, h6, h7⟩ := hQ
  have hr : Set.range (Q.comp e.symm.toAddEquiv.toAddMonoidHom) = Set.range Q :=
    e.symm.surjective.range_comp Q
  have hr' : (Q.comp e.symm.toAddEquiv.toAddMonoidHom).range = Q.range :=
    SetLike.ext' hr
  refine ⟨fun a x i => ?_, h2.comp e.symm.injective, by rw [hr']; exact h3, by rw [hr]; exact h4, Hm, h5, h6,
    fun x y => ?_⟩
  · change Q (e.symm (a • x)) i = _ * Q (e.symm x) i
    rw [map_smul, h1]
  · change (hermForm Hm (Q (e.symm x)) (Q (e.symm y))).im = _
    rw [h7, ← he, e.apply_symm_apply, e.apply_symm_apply]

theorem exp_eq_zpow (k : ℕ) (hk : 0 < k) (m ν s : ℤ) (h : (k : ℤ) ∣ m - ν * s) :
    Complex.exp (-(2 * Real.pi * Complex.I) * (m : ℂ) / (k : ℂ)) =
      Complex.exp (-(2 * Real.pi * Complex.I) * (ν : ℂ) / k) ^ s := by
  obtain ⟨c, hc⟩ := h
  have hm : m = ν * s + k * c := by linarith
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [← Complex.exp_int_mul, Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-c, ?_⟩
  rw [hm]
  push_cast
  field_simp
  ring

theorem goodClass_pelClass : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) [Finite J] (a : J → 𝓞 E) (w w' : J) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La), 1 ≤ D.p + D.q → IsSympBasis D bas → a w = H.w0 → a w' = H.bar H.w0 → Subring.closure (Set.range a) = ⊤ → ∃ (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ), ∀ n : ℕ, n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ N' : ℕ, N' = n ^ j → ∀ (o : Type) [CommRing o] (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (ρ : o), em ρ = H.rt0 → GoodClass em (PELClass (b := b) D a bas ρ em) Mat κ w w' D.dim := by
  intro L1 L2 hΘ hU E _ _ _ H D g J _ a w w' bas hpq hbas hw hw' _
  obtain ⟨ty, hty⟩ := exists_isTypeFn_of_rank E H D g ⟨bas⟩
  obtain ⟨κ, hκ⟩ : ∃ κ : ℕ, ∀ (j : J) (τ : E →+* ℂ), ‖τ (a j : E)‖ ^ 2 < κ := by
    obtain ⟨M, hM⟩ := (Set.finite_range (fun x : J × (E →+* ℂ) => ‖x.2 (a x.1 : E)‖ ^ 2)).bddAbove
    obtain ⟨κ, hκ⟩ := exists_nat_gt M
    exact ⟨κ, fun j τ => (hM ⟨(j, τ), rfl⟩).trans_lt hκ⟩
  let Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ :=
    fun j i' i => bas.symm (a j • bas (Pi.single i 1)) i'
  have hMat : ∀ j i, a j • bas (Pi.single i 1) = ∑ i', Mat j i' i • bas (Pi.single i' 1) := by
    intro j i
    apply bas.symm.injective

    rw [map_sum]
    simp only [map_smul, LinearEquiv.symm_apply_apply]
    ext i₀
    simp [Mat, Finset.sum_apply, Pi.single_apply]
  refine ⟨Mat, κ, fun n hn hodd => ?_⟩
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.T.goodThetaClass_of_lattice_families L1 L2 hΘ hU g J Mat κ n w w' hn hodd
  refine ⟨j₀, fun j hj N' hN o _ b em ρ hρ => ?_⟩
  have hk : 0 < N' ^ 2 := by rw [hN]; exact pow_pos (pow_pos hn.pos _) _
  obtain ⟨r, Di, fi, νi, hfam, hall⟩ := MarkedGenus.finite_marked_data_in_genus E H D (N' ^ 2) (em (b.ζ : o)) hk
  choose B P hBo hBc hBh hBu using fun i => exists_domain D (Di i) ty hty (hfam i).1.1 (hfam i).1.2.1
  have hH : ∀ i bb, ∃ Hm : Matrix (Fin g) (Fin g) ℂ, bb ∈ B i →
      (Function.Injective (P i bb) ∧ DiscreteTopology (P i bb).range ∧ Submodule.span ℝ (Set.range (P i bb)) = ⊤ ∧
        Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧
        ∀ x y, (hermForm Hm (P i bb x) (P i bb y)).im = (Di i).EF x y) := by
    intro i bb
    by_cases hb : bb ∈ B i
    · obtain ⟨-, h2, h3, h4, Hm, h5⟩ := (hBh i).1 bb hb
      exact ⟨Hm, fun _ => ⟨h2, h3, h4, h5⟩⟩
    · exact ⟨0, fun h => (hb h).elim⟩
  choose Hm hHm using hH
  refine hj₀ j hj N' hN o b em _ D.dim r (fun i => (Di i).La) (fun i => (Di i).EF)
    (fun i i₁ => fi i (N' ^ 2) (bas (Pi.single i₁ 1))) (fun i j x => a j • x) B P Hm
    (fun t t' ht hm => (pelClass_prim_and_iso E H D o g _ J b em w w' a bas ρ t ht).2 t' hm)
    (fun t ht => (pelClass_prim_and_iso E H D o g _ J b em w w' a bas ρ t ht).1 hw hw') (fun i => ?_) (fun t ht => ?_)
  · refine ⟨(Di i).unimod, hBo i, (hBc i).isPreconnected, (hBh i).2, fun x => ?_, fun x y => ?_, fun i₁ i₂ => ?_,
      fun j₁ i₁ => ⟨0, ?_⟩, fun bb hb => ⟨hHm i bb hb, fun j₁ => ?_⟩, fun bb hb z hz hh => ?_, fun bb hb t hu hp => ?_⟩
    · rw [← add_smul, hw, hw', HostModel.cmHost_bar_halfIntegerGenerator, add_sub_cancel, one_smul]
    · rw [hw, hw', (Di i).adj]
    · rw [(hfam i).2]
      apply exp_eq_zpow _ hk
      rw [← hbas]
      exact (hfam i).1.2.2.2.2 _ hk _ _

    · rw [smul_zero, add_zero, ← map_smul, hMat, map_sum]
      simp only [map_zsmul]
    · exact ConjBound.exists_action_lt E H (Di i) g ty (P i bb) (Hm i bb) (a j₁) κ ((hBh i).1 bb hb).1 (hHm i bb hb)
        (hκ j₁)
    · exact (hBu i _ ((hBh i).1 z hz)).unique ⟨hb, hh⟩ ⟨hz, LinearEquiv.refl _ _, fun _ => rfl⟩
    · exact GlobalTheory.T.isPELObject_of_primitive_periodMap_uniformised L1 L2 hΘ hU E H D o g _ J b em w w' a bas ρ ty t (Di i) (fi i) (νi i) (P i bb) (Hm i bb)
        hpq hw hρ hty (hfam i).1 (hfam i).2 ((hBh i).1 bb hb) (hHm i bb hb) hu hp
  · obtain ⟨D', f, ν, Q, Hm', hgen, hζ, hper, hpol, hu⟩ :=
      GlobalTheory.T.exists_periods_complexPELObject L1 L2 hΘ hU E H D o g _ J b em w w' a bas ρ ty t hw hw' hρ hty ht
    obtain ⟨i, e, he, hef⟩ := hall D' f ν hgen hζ
    obtain ⟨bb, ⟨hb, h, hh⟩, -⟩ := hBu i _ (isPeriod_comp hper e he)
    refine ⟨i, bb, hb, ?_⟩
    refine UnifTransport.transport_uniformisation o g (N' ^ 2) J b em w w' t D'.La D'.EF
      (fun i₁ => f (N' ^ 2) (bas (Pi.single i₁ 1))) (fun j x => a j • x) Q Hm' (Di i).La (Di i).EF
      (fun i₁ => fi i (N' ^ 2) (bas (Pi.single i₁ 1))) (fun j x => a j • x) (P i bb) (Hm i bb) e.toAddEquiv h.symm
      hpol (hHm i bb hb) (fun x => ?_) he (fun j x => e.map_smul _ _) (fun i₁ => hef _) hu
    rw [LinearEquiv.eq_symm_apply, ← hh]
    exact congrArg Q (e.symm_apply_apply x)

end GlobalTheory.PelGood
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsGoodThetaComplexClassUnitaryFullLevelStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.isGoodThetaComplexClass_unitaryFullLevel : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) [Finite J] (a : J → 𝓞 E) (w w' : J) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La), 1 ≤ D.p + D.q → IsSympBasis D bas → a w = H.w0 → a w' = H.bar H.w0 → Subring.closure (Set.range a) = ⊤ → ∃ (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ), ∀ n : ℕ, n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ N' : ℕ, N' = n ^ j → ∀ (o : Type) [CommRing o] (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (ρ : o), em ρ = H.rt0 → GoodClass em (PELClass (b := b) D a bas ρ em) Mat κ w w' D.dim := by
  first | exact @GlobalTheory.PelGood.goodClass_pelClass | exact GlobalTheory.PelGood.goodClass_pelClass | (intros; apply GlobalTheory.PelGood.goodClass_pelClass <;> assumption)
end
end
