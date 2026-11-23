module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonDenominatorConjLocalCoordsLatticeStatement
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationMulLeOneOfTraceApproxIdempotentIntegral
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInverseDifferentMaxValuationStatement
public import Mathlib.Algebra.Module.Lattice.Full
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Mathlib.Order.Int.LeastGreatest
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeInverseGramLocalBasisIntegralStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationAlgHomEqOfInertPrimeStatement
public import Formalism.SatakeDualWeyl.StatementG
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationAlgebraMapEqOfInertPlace
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HermitianFormFiniteZerosOnLineCmExt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegerDenominatorNotMemOfValuationLeOne

section

@[expose] public section

open NumberField IsDedekindDomain
open scoped Matrix

namespace GlobalTheory.IntegralDenom

theorem exists_denom_not_mem : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (a : E), w.valuation E a ≤ 1 → ∃ s : 𝓞 E, s ∉ w.asIdeal ∧ ∃ r : 𝓞 E, (s : E) * a = r := by
  intro E _ _ w a ha
  exact GlobalTheory.InvDiffLocal.exists_not_mem_mul_mem w a ha

end GlobalTheory.IntegralDenom
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegerDenominatorNotMemOfValuationLeOneStatement

section

@[expose] public section

open NumberField IsDedekindDomain
open scoped Matrix

theorem _root_.GlobalTheory.T.exists_integer_denominator_not_mem_of_valuation_le_one : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (a : E), w.valuation E a ≤ 1 → ∃ s : 𝓞 E, s ∉ w.asIdeal ∧ ∃ r : 𝓞 E, (s : E) * a = r := by
  first | exact @GlobalTheory.IntegralDenom.exists_denom_not_mem | exact GlobalTheory.IntegralDenom.exists_denom_not_mem | (intros; apply GlobalTheory.IntegralDenom.exists_denom_not_mem <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalBasisAtPrimeOfIsLattice

section

@[expose] public section

open NumberField IsDedekindDomain
open scoped Matrix

namespace GlobalTheory

theorem exists_valuation_bound_of_fg {E : Type} [Field E] [NumberField E]
    (w : HeightOneSpectrum (𝓞 E)) {n : ℕ} {L : Submodule (𝓞 E) (Fin n → E)} (hL : L.FG) :
    ∃ C : WithZero (Multiplicative ℤ), ∀ x ∈ L, ∀ i, w.valuation E (x i) ≤ C := by
  classical
  obtain ⟨s, rfl⟩ := hL
  refine ⟨(s ×ˢ (Finset.univ : Finset (Fin n))).sup fun p => w.valuation E (p.1 p.2), ?_⟩
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    intro i
    exact Finset.le_sup (f := fun p : (Fin n → E) × Fin n => w.valuation E (p.1 p.2))
      (b := (x, i)) (Finset.mem_product.2 ⟨hx, Finset.mem_univ _⟩)
  | zero => intro i; simp
  | add x y _ _ hx hy => intro i; exact Valuation.map_add_le _ (hx i) (hy i)
  | smul a x _ hx =>
    intro i
    rw [Pi.smul_apply, Algebra.smul_def, map_mul]
    exact (mul_le_of_le_one_left' (w.valuation_le_one a)).trans (hx i)

theorem valuation_det_le_pow_of_entry_le {E : Type} [Field E] [NumberField E]
    (w : HeightOneSpectrum (𝓞 E)) {n : ℕ} (X : Matrix (Fin n) (Fin n) E)
    {C : WithZero (Multiplicative ℤ)} (h : ∀ i j, w.valuation E (X i j) ≤ C) :
    w.valuation E X.det ≤ C ^ n := by
  rw [Matrix.det_apply']
  refine Valuation.map_sum_le _ fun σ _ => ?_
  rw [map_mul, map_prod]
  have h1 : w.valuation E ((Equiv.Perm.sign σ : ℤ) : E) ≤ 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  refine (mul_le_of_le_one_left' h1).trans ?_
  calc ∏ i, w.valuation E (X (σ i) i) ≤ ∏ _i : Fin n, C :=
        Finset.prod_le_prod' fun i _ => h _ _
    _ = C ^ n := by simp

theorem exists_det_ne_zero_col_mem_of_span_eq_top {E : Type} [Field E] {n : ℕ}
    {S : Set (Fin n → E)} (hS : Submodule.span E S = ⊤) :
    ∃ X : Matrix (Fin n) (Fin n) E, X.det ≠ 0 ∧ ∀ j, (fun i => X i j) ∈ S := by
  classical
  obtain ⟨t, htS, hspan, hli⟩ := exists_linearIndependent E S
  rw [hS] at hspan
  let b : Module.Basis t E (Fin n → E) := Module.Basis.mk hli (by simp [hspan])
  have hfin : Finite t := Module.Finite.finite_basis b
  have := Fintype.ofFinite t
  have hc : Fintype.card t = n := by
    rw [← Module.finrank_eq_card_basis b]; simp
  let e : t ≃ Fin n := Fintype.equivFinOfCardEq hc
  let b' := b.reindex e
  refine ⟨Matrix.of fun i j => b' j i, ?_, fun j => ?_⟩
  · have hli' : LinearIndependent E (Matrix.of fun i j => b' j i).col := b'.linearIndependent
    have := Matrix.linearIndependent_cols_iff_isUnit.1 hli'
    exact ((Matrix.isUnit_iff_isUnit_det _).1 this).ne_zero
  · have : (fun i => (Matrix.of fun i j => b' j i) i j) = (e.symm j : Fin n → E) := by
      funext i; simp [b', b]
    rw [this]
    exact htS (e.symm j).2

theorem exists_local_basis_of_isLattice (E : Type) [Field E] [NumberField E]
    (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E))
    (hL : L.IsFullLattice E) :
    ∃ X : Matrix (Fin n) (Fin n) E, IsUnit X.det ∧ (∀ j, (fun i => X i j) ∈ L) ∧
      ∀ x ∈ L, ∀ i, w.valuation E ((X⁻¹ *ᵥ x) i) ≤ 1 := by
  classical
  obtain ⟨C, hC⟩ := exists_valuation_bound_of_fg w hL.fg
  obtain ⟨X₀, hX₀, hX₀L⟩ := exists_det_ne_zero_col_mem_of_span_eq_top hL.span_eq_top
  have hbd : ∀ X : Matrix (Fin n) (Fin n) E, (∀ j, (fun i => X i j) ∈ L) →
      w.valuation E X.det ≤ C ^ n := fun X hX =>
    valuation_det_le_pow_of_entry_le w X fun i j => hC _ (hX j) i
  obtain ⟨m, ⟨X, hX, hXL, rfl⟩, hmax⟩ := Int.exists_greatest_of_bdd
    (P := fun m => ∃ X : Matrix (Fin n) (Fin n) E, X.det ≠ 0 ∧ (∀ j, (fun i => X i j) ∈ L) ∧
      WithZero.log (w.valuation E X.det) = m)
    ⟨WithZero.log (C ^ n), by
      rintro _ ⟨X, hX, hXL, rfl⟩
      have h0 : w.valuation E X.det ≠ 0 := by simpa using hX
      have h1 := hbd X hXL
      have h2 : C ^ n ≠ 0 := fun h => h0 (le_antisymm (h ▸ h1) zero_le')
      exact (WithZero.log_le_log h0 h2).2 h1⟩
    ⟨_, X₀, hX₀, hX₀L, rfl⟩
  have h0 : w.valuation E X.det ≠ 0 := by simpa using hX
  refine ⟨X, hX.isUnit, hXL, fun x hx i => ?_⟩
  have hcr : X.det * (X⁻¹ *ᵥ x) i = (X.updateCol i x).det := by
    have := congrFun (Matrix.det_smul_inv_mulVec_eq_cramer X x hX.isUnit) i
    simpa [Matrix.cramer_apply] using this
  have hle : w.valuation E (X.updateCol i x).det ≤ w.valuation E X.det := by
    by_cases hY : (X.updateCol i x).det = 0
    · simp [hY]
    · have h1 : w.valuation E (X.updateCol i x).det ≠ 0 := by simpa using hY
      refine (WithZero.log_le_log h1 h0).1 (hmax _ ⟨_, hY, fun j => ?_, rfl⟩)
      by_cases hj : j = i
      · subst hj
        simpa using hx
      · simpa [Matrix.updateCol_ne hj] using hXL j
  rw [← hcr, map_mul] at hle
  have hpos : 0 < w.valuation E X.det := zero_lt_iff.2 h0
  exact (mul_le_iff_le_one_right hpos).1 hle

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationAlgebraMapEqOfInertPlaceStatement

section

@[expose] public section

open NumberField IsDedekindDomain
open scoped Matrix

theorem _root_.GlobalTheory.T.valuation_algebraMap_eq_of_inertPlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → ∀ x : F, w.valuation E (algebraMap F E x) = v.valuation F x := by
  first | exact @GlobalTheory.InertValRestr.valuation_algebraMap_of_isInertAt | exact GlobalTheory.InertValRestr.valuation_algebraMap_of_isInertAt | (intros; apply GlobalTheory.InertValRestr.valuation_algebraMap_of_isInertAt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianDetEqUnitMulNormAtInert

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.SkewDetParity

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem val_sigma (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    (h : Formalism.UG.IsInertAt F E v w) (x : E) : w.valuation E (σ x) = w.valuation E x :=
  GlobalTheory.T.valuation_algHom_eq_of_inertPrime F E σ v w h x

theorem val_algebraMap (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    (h : Formalism.UG.IsInertAt F E v w) (x : F) : w.valuation E (algebraMap F E x) = v.valuation F x :=
  GlobalTheory.T.valuation_algebraMap_eq_of_inertPlace F E v w h x

theorem exists_max_dual (w : HeightOneSpectrum (𝓞 E)) : ∃ e : E, e ≠ 0 ∧
    (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * e))) ∧
    ∀ f : E, (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * f))) → w.valuation E f ≤ w.valuation E e :=
  GlobalTheory.T.exists_inverseDifferent_max_valuation E w

theorem exists_local_basis (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E))
    (hL : L.IsFullLattice E) : ∃ X : Matrix (Fin n) (Fin n) E, IsUnit X.det ∧ (∀ j, (fun i => X i j) ∈ L) ∧
    ∀ x ∈ L, ∀ i, w.valuation E ((X⁻¹ *ᵥ x) i) ≤ 1 :=
  GlobalTheory.exists_local_basis_of_isLattice E w n L hL

theorem exists_den (w : HeightOneSpectrum (𝓞 E)) (a : E) (ha : w.valuation E a ≤ 1) :
    ∃ s : 𝓞 E, s ∉ w.asIdeal ∧ ∃ r : 𝓞 E, (s : E) * a = r :=
  GlobalTheory.T.exists_integer_denominator_not_mem_of_valuation_le_one E w a ha

theorem exists_common_den (σ : E →ₐ[F] E) (w : HeightOneSpectrum (𝓞 E))
    (hσ : ∀ x, w.valuation E (σ x) = w.valuation E x)
    (hden : ∀ a : E, w.valuation E a ≤ 1 → ∃ s : 𝓞 E, s ∉ w.asIdeal ∧ ∃ r : 𝓞 E, (s : E) * a = r)
    (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.FG) (X : Matrix (Fin n) (Fin n) E)
    (hX : ∀ x ∈ L, ∀ i, w.valuation E ((X⁻¹ *ᵥ x) i) ≤ 1) :
    ∃ s : 𝓞 E, s ∉ w.asIdeal ∧ ∀ x ∈ L, ∀ i, ∃ r : 𝓞 E, (s : E) * σ ((X⁻¹ *ᵥ x) i) = r :=
  GlobalTheory.T.exists_common_denominator_conj_localCoords_lattice F E σ w hσ hden n L hL X hX

theorem dual_bound (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E))
    (w : HeightOneSpectrum (𝓞 E))
    (hdual : ∀ y, y ∈ L ↔ ∀ x ∈ L, ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * form σ J y x)))
    (X : Matrix (Fin n) (Fin n) E) (hX : IsUnit X.det) (hG : IsUnit (Xᵀ * J * X.map σ).det)
    (hXc : ∀ x ∈ L, ∀ i, w.valuation E ((X⁻¹ *ᵥ x) i) ≤ 1)
    (s : 𝓞 E) (hs : s ∉ w.asIdeal) (hsr : ∀ x ∈ L, ∀ i, ∃ r : 𝓞 E, (s : E) * σ ((X⁻¹ *ᵥ x) i) = r)
    (e : E) (he : ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * e))) :
    ∀ i k, w.valuation E (e * (Xᵀ * J * X.map σ)⁻¹ i k) ≤ 1 :=
  GlobalTheory.T.selfDualLattice_inverseGram_localBasis_integral F E σ n J L w hdual X hX hG hXc s hs hsr e he

theorem val_det_le (w : HeightOneSpectrum (𝓞 E)) {n : ℕ} (M : Matrix (Fin n) (Fin n) E)
    (c : WithZero (Multiplicative ℤ)) (h : ∀ i j, w.valuation E (M i j) ≤ c) :
    w.valuation E M.det ≤ c ^ n := by
  rw [Matrix.det_apply]
  refine Valuation.map_sum_le _ fun p _ => ?_
  have hp : w.valuation E (∏ i, M (p i) i) ≤ c ^ n := by
    rw [map_prod]
    calc ∏ i, w.valuation E (M (p i) i) ≤ ∏ _i : Fin n, c := Finset.prod_le_prod' fun i _ => h _ _
      _ = c ^ n := by simp
  rcases Int.units_eq_one_or (Equiv.Perm.sign p) with h1 | h1 <;> rw [h1]
  · rwa [one_smul]
  · rwa [Units.neg_smul, one_smul, Valuation.map_neg]

end GlobalTheory.SkewDetParity

namespace GlobalTheory.SkewDetParity

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem form_cols (σ : E →ₐ[F] E) {n : ℕ} (J X : Matrix (Fin n) (Fin n) E) (i j : Fin n) :
    (Xᵀ * J * X.map σ) i j = form σ J (fun k => X k i) (fun k => X k j) := by
  simp only [form, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, dotProduct, Matrix.mulVec,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem parity_at (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    (hin : Formalism.UG.IsInertAt F E v w) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E))
    (hL : L.IsFullLattice E)
    (hdual : ∀ y, y ∈ L ↔ ∀ x ∈ L, ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * form σ J y x)))
    (hn : Even n) (hJ : J.det ≠ 0) : ∃ a : E, a ≠ 0 ∧ w.valuation E J.det = w.valuation E a ^ 2 := by
  obtain ⟨e, he0, heD, hemax⟩ := exists_max_dual w
  obtain ⟨X, hXu, hXL, hXc⟩ := exists_local_basis w n L hL
  obtain ⟨s, hs, hsr⟩ := exists_common_den σ w (val_sigma σ v w hin) (exists_den w) n L hL.fg X hXc
  have hσdet : σ X.det = (X.map σ).det := by
    rw [AlgHom.map_det]; rfl
  have hdetG : (Xᵀ * J * X.map σ).det = X.det * J.det * σ X.det := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hσdet]
  have hX0 : X.det ≠ 0 := hXu.ne_zero
  have hσX0 : σ X.det ≠ 0 := by
    intro h0; apply hX0; exact (map_eq_zero_iff σ σ.toRingHom.injective).1 h0
  have hG0 : (Xᵀ * J * X.map σ).det ≠ 0 := by
    rw [hdetG]; exact mul_ne_zero (mul_ne_zero hX0 hJ) hσX0
  have hGu : IsUnit (Xᵀ * J * X.map σ).det := isUnit_iff_ne_zero.2 hG0
  have hGij : ∀ i j, w.valuation E ((Xᵀ * J * X.map σ) i j) ≤ w.valuation E e := fun i j => by
    rw [form_cols]
    exact hemax _ fun o => (hdual _).1 (hXL i) _ (hXL j) o
  have hup := val_det_le w _ _ hGij
  have hinv := dual_bound σ n J L w hdual X hXu hGu hXc s hs hsr e heD
  have hlow := val_det_le w (e • (Xᵀ * J * X.map σ)⁻¹) 1 (fun i k => by
    simpa [Matrix.smul_apply] using hinv i k)
  rw [one_pow, Matrix.det_smul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', Fintype.card_fin, map_mul,
    map_pow, map_inv₀] at hlow
  have hvG0 : w.valuation E (Xᵀ * J * X.map σ).det ≠ 0 := (Valuation.ne_zero_iff _).2 hG0
  have hlow' : w.valuation E e ^ n ≤ w.valuation E (Xᵀ * J * X.map σ).det := by
    first
      | rwa [mul_inv_le_iff₀ hvG0, one_mul] at hlow
      | rwa [mul_inv_le_iff₀ (zero_lt_iff.2 hvG0), one_mul] at hlow
  have hEq : w.valuation E (Xᵀ * J * X.map σ).det = w.valuation E e ^ n := le_antisymm hup hlow'
  rw [hdetG, map_mul, map_mul, val_sigma σ v w hin] at hEq
  obtain ⟨m, rfl⟩ := hn
  refine ⟨e ^ m / X.det, div_ne_zero (pow_ne_zero _ he0) hX0, ?_⟩
  have hvX0 : w.valuation E X.det ≠ 0 := (Valuation.ne_zero_iff _).2 hX0
  rw [map_div₀, map_pow, div_pow, ← pow_mul, mul_two, ← hEq]
  field_simp

theorem sigma_sigma (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2 τ, h.2.2.2 τ, star_star]

theorem det_eq_unit_mul_norm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (n r s : ℕ) (W : Spc F E n), W.IsSkew σ B r s → Even n →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → IsField (Fv F v ⊗[F] E) →
    ∃ (y : Fv F v ⊗[F] E) (u : Fv F v), Valued.v u = 1 ∧
      (1 : Fv F v) ⊗ₜ[F] W.J.det = algebraMap (Fv F v) (Fv F v ⊗[F] E) u *
        (y * Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ y) := by
  intro F E _ _ _ _ _ σ B hB n r s W hW hn v w hin _
  by_cases hJ : W.J.det = 0
  · exact ⟨0, 1, map_one _, by simp [hJ]⟩
  obtain ⟨a, ha0, hva⟩ := parity_at σ v w hin n W.J W.L hW.lat hW.dual hn hJ
  have hmap : W.J.map σ = -W.Jᵀ := by
    ext i j
    simp only [Matrix.map_apply, Matrix.neg_apply, Matrix.transpose_apply]
    rw [← hW.skew j i]
  have hfix : σ W.J.det = W.J.det := by
    rw [AlgHom.map_det]
    change (W.J.map σ).det = _
    rw [hmap, Matrix.det_neg, Matrix.det_transpose, Fintype.card_fin, hn.neg_one_pow, one_mul]
  obtain ⟨c, hc⟩ := GlobalTheory.HermLineZeros.exists_of_fixed hB.cm _ hfix
  have hfixN : σ (a * σ a) = a * σ a := by
    rw [map_mul, sigma_sigma σ hB.cm, mul_comm]
  obtain ⟨β, hβ⟩ := GlobalTheory.HermLineZeros.exists_of_fixed hB.cm _ hfixN
  have hσa0 : σ a ≠ 0 := by
    intro h0; apply ha0; exact (map_eq_zero_iff σ σ.toRingHom.injective).1 h0
  have hβ0 : β ≠ 0 := by
    intro h0; rw [h0, map_zero] at hβ; exact mul_ne_zero ha0 hσa0 hβ.symm
  refine ⟨(1 : Fv F v) ⊗ₜ[F] a, algebraMap F (Fv F v) (c / β), ?_, ?_⟩
  · rw [show Valued.v (algebraMap F (Fv F v) (c / β)) = v.valuation F (c / β) from
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (c / β), ← val_algebraMap v w hin, map_div₀, map_div₀, hc, hβ,
      map_mul, val_sigma σ v w hin, hva, sq]
    have : w.valuation E a ≠ 0 := (Valuation.ne_zero_iff _).2 ha0
    exact div_self (mul_ne_zero this this)
  · have key : (algebraMap F (Fv F v) (c / β)) ⊗ₜ[F] (algebraMap F E β) = (1 : Fv F v) ⊗ₜ[F] W.J.det := by
      rw [Algebra.algebraMap_eq_smul_one (c / β), TensorProduct.smul_tmul, Algebra.smul_def, ← map_mul,
        div_mul_cancel₀ _ hβ0, hc]
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← hβ,
      Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← key]
    simp

end GlobalTheory.SkewDetParity
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianDetEqUnitMulNormAtInertStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.skewHermitian_det_eq_unit_mul_norm_at_inert : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (n r s : ℕ) (W : Spc F E n), W.IsSkew σ B r s → Even n →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → IsField (Fv F v ⊗[F] E) →
    ∃ (y : Fv F v ⊗[F] E) (u : Fv F v), Valued.v u = 1 ∧
      (1 : Fv F v) ⊗ₜ[F] W.J.det = algebraMap (Fv F v) (Fv F v ⊗[F] E) u *
        (y * Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ y) := by
  first | exact @GlobalTheory.SkewDetParity.det_eq_unit_mul_norm | exact GlobalTheory.SkewDetParity.det_eq_unit_mul_norm | (intros; apply GlobalTheory.SkewDetParity.det_eq_unit_mul_norm <;> assumption)
end
end
