module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormDivLocalEmbeddingCloseToOneStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsParahoricTypeVectorAtConjugatePlace
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuedMapEqOfContinuousCompletionIsoExtending

section

@[expose] public section

open NumberField IsDedekindDomain

namespace GlobalTheory.CompletionIsom


open WithZero in
theorem valuation_eq_of_lt_one_iff {K : Type} [Field K] (v v' : Valuation K (WithZero (Multiplicative ℤ)))
    (h : ∀ y, v y < 1 ↔ v' y < 1) (π : K) (hπ : v π = exp (-1)) (y₀ : K) (hy₀ : v' y₀ = exp (-1)) :
    ∀ y, v' y = v y := by
  have hπ0 : π ≠ 0 := by rintro rfl; rw [map_zero] at hπ; exact exp_ne_zero hπ.symm
  have hy0 : y₀ ≠ 0 := by rintro rfl; rw [map_zero] at hy₀; exact exp_ne_zero hy₀.symm
  have hexp : ∀ (w : Valuation K (WithZero (Multiplicative ℤ))) (x : K), x ≠ 0 → ∃ a : ℤ, w x = exp a :=
    fun w x hx => ⟨_, (exp_log ((Valuation.ne_zero_iff w).2 hx)).symm⟩
  have hker : ∀ z, v z = 1 → v' z = 1 := by
    intro z hz
    have hz0 : z ≠ 0 := by rintro rfl; rw [map_zero] at hz; exact zero_ne_one hz
    obtain ⟨a, ha⟩ := hexp v' z hz0
    rcases lt_trichotomy a 0 with h1 | h1 | h1
    · have := (h z).2 (by rw [ha, ← exp_zero, exp_lt_exp]; exact h1)
      rw [hz] at this; exact absurd this (lt_irrefl _)
    · rw [ha, h1, exp_zero]
    · have := (h z⁻¹).2 (by rw [map_inv₀, ha, ← exp_neg, ← exp_zero, exp_lt_exp]; omega)
      rw [map_inv₀, hz, inv_one] at this; exact absurd this (lt_irrefl _)
  obtain ⟨e, he⟩ := hexp v' π hπ0
  obtain ⟨b, hb⟩ := hexp v y₀ hy0
  have he1 : e < 0 := by
    have := (h π).1 (by rw [hπ, ← exp_zero, exp_lt_exp]; omega)
    rwa [he, ← exp_zero, exp_lt_exp] at this
  have hb1 : b < 0 := by
    have := (h y₀).2 (by rw [hy₀, ← exp_zero, exp_lt_exp]; omega)
    rwa [hb, ← exp_zero, exp_lt_exp] at this
  have he2 : -1 ≤ e := by
    by_contra hc
    have := (h (π * y₀⁻¹)).2 (by
      rw [map_mul, map_inv₀, he, hy₀, ← exp_neg, ← exp_add, ← exp_zero, exp_lt_exp]; omega)
    rw [map_mul, map_inv₀, hπ, hb, ← exp_neg, ← exp_add, ← exp_zero, exp_lt_exp] at this
    omega
  have hπ' : v' π = exp (-1) := by rw [he]; congr 1; omega
  intro y
  by_cases hy : y = 0
  · rw [hy, map_zero, map_zero]
  obtain ⟨a, ha⟩ := hexp v y hy
  have hz := hker (y * π ^ a) (by
    rw [map_mul, map_zpow₀, ha, hπ, ← exp_zsmul, ← exp_add, ← exp_zero]; congr 1; simp)
  rw [map_mul, map_zpow₀, hπ', ← exp_zsmul] at hz
  rw [ha, eq_inv_of_mul_eq_one_left hz, ← exp_neg]
  congr 1; simp

theorem valued_v_map : ∀ (E E' : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E']
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))
    (w' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E'))
    (i : w.adicCompletion E ≃+* w'.adicCompletion E'), Continuous i →
    (∀ x : E, i (algebraMap E _ x) = algebraMap E' _ (algebraMap E E' x)) →
    ∀ y : w.adicCompletion E, Valued.v (i y) = Valued.v y := by
  intro E E' _ _ _ _ _ w w' i hi _ y
  have := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion E w
  have ho : IsOpenMap i :=
    AddMonoidHom.isOpenMap_of_sigmaCompact i.toAddEquiv.toAddMonoidHom i.surjective hi
  have hi' : Continuous i.symm := i.toEquiv.continuous_symm_iff.2 ho
  obtain ⟨π, hπ⟩ := w.valuedAdicCompletion_surjective E (WithZero.exp (-1))
  obtain ⟨ϖ, hϖ⟩ := w'.valuedAdicCompletion_surjective E' (WithZero.exp (-1))
  refine valuation_eq_of_lt_one_iff (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
    ((Valued.v : Valuation (w'.adicCompletion E') (WithZero (Multiplicative ℤ))).comap i.toRingHom)
    (fun x => ⟨fun hx => GlobalTheory.ConjParahoric.val_lt_one_map i.toRingHom hi hx, fun hx => ?_⟩) π hπ (i.symm ϖ) ?_ y
  · have := GlobalTheory.ConjParahoric.val_lt_one_map i.symm.toRingHom hi' hx
    simpa using this
  · simpa using hϖ

end GlobalTheory.CompletionIsom
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuedMapEqOfContinuousCompletionIsoExtendingStatement

section

@[expose] public section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.valued_map_eq_of_continuous_completionIso_extending : ∀ (E E' : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E'] (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) (w' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E')) (i : w.adicCompletion E ≃+* w'.adicCompletion E'), Continuous i → (∀ x : E, i (algebraMap E _ x) = algebraMap E' _ (algebraMap E E' x)) → ∀ y : w.adicCompletion E, Valued.v (i y) = Valued.v y := by
  first | exact @GlobalTheory.CompletionIsom.valued_v_map | exact GlobalTheory.CompletionIsom.valued_v_map | (intros; apply GlobalTheory.CompletionIsom.valued_v_map <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormCloseToComponentLocalDegreeOne

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.NormCompat.LocalDegOne

theorem valued_algebraMap_eq {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (k : K) :
    Valued.v (algebraMap K (v.adicCompletion K) k) = v.valuation K k :=
  IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v k

theorem mul_sub_one_le {R : Type} [CommRing R] (v : Valuation R (WithZero (Multiplicative ℤ))) (a b : R) (M : ℕ)
    (ha : v (a - 1) ≤ WithZero.exp (-(M : ℤ))) (hb : v (b - 1) ≤ WithZero.exp (-(M : ℤ))) :
    v (a * b - 1) ≤ WithZero.exp (-(M : ℤ)) := by
  have e : a * b - 1 = (a - 1) * (b - 1) + ((a - 1) + (b - 1)) := by ring
  have h1 : WithZero.exp (-(M : ℤ)) ≤ 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega
  rw [e]
  refine (v.map_add _ _).trans (max_le ?_ ((v.map_add _ _).trans (max_le ha hb)))
  rw [v.map_mul]
  calc v (a - 1) * v (b - 1) ≤ WithZero.exp (-(M : ℤ)) * 1 := mul_le_mul' ha (hb.trans h1)
    _ = _ := mul_one _

theorem norm_div_close_to_one : ∀ (E E' : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E'] (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) (w' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E')) (i : w.adicCompletion E ≃+* w'.adicCompletion E'), Continuous i → (∀ x : E, i (algebraMap E _ x) = algebraMap E' _ (algebraMap E E' x)) → ∀ M : ℕ, ∃ M' : ℕ, ∀ (c : E) (z : E'), c ≠ 0 → (∀ w'' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E'), w''.asIdeal.comap (algebraMap (NumberField.RingOfIntegers E) (NumberField.RingOfIntegers E')) = w.asIdeal → w'' ≠ w' → w''.valuation E' (z - 1) ≤ WithZero.exp (-(M' : ℤ))) → w'.valuation E' (z / algebraMap E E' c - 1) ≤ WithZero.exp (-(M' : ℤ)) → w.valuation E (Algebra.norm E z / c - 1) ≤ WithZero.exp (-(M : ℤ)) := by
  intro E E' _ _ _ _ _ w w' i hi hcomp M
  set σ : E' →+* w.adicCompletion E := (i.symm : w'.adicCompletion E' →+* w.adicCompletion E).comp (algebraMap E' (w'.adicCompletion E')) with hσ
  have hσE : ∀ x : E, σ (algebraMap E E' x) = algebraMap E _ x := fun x => by
    simp only [hσ, RingHom.comp_apply, RingEquiv.coe_toRingHom, ← hcomp x, RingEquiv.symm_apply_apply]
  have hσv : ∀ x : E', Valued.v (σ x) = w'.valuation E' x := fun x => by
    rw [← GlobalTheory.T.valued_map_eq_of_continuous_completionIso_extending E E' w w' i hi hcomp (σ x)]
    simp only [hσ, RingHom.comp_apply, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
    exact valued_algebraMap_eq w' x
  obtain ⟨M₁, hM₁⟩ := GlobalTheory.T.norm_div_localEmbedding_close_to_one E E' w w' σ hσE hσv M
  refine ⟨max (max M M₁) 1, fun c z hc hz hzw => ?_⟩
  have hle : ∀ k, k ≤ max (max M M₁) 1 → WithZero.exp (-((max (max M M₁) 1 : ℕ) : ℤ)) ≤ WithZero.exp (-(k : ℤ)) := fun k hk => by
    rw [WithZero.exp_le_exp]; omega
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_div, zero_sub, Valuation.map_neg, Valuation.map_one] at hzw
    have := hzw.trans (hle 1 (le_max_right _ _))
    rw [← WithZero.exp_zero, WithZero.exp_le_exp] at this
    omega
  have hF := hM₁ z hz0 fun w'' h1 h2 => (hz w'' h1 h2).trans (hle M₁ (by omega))
  have hσz : σ z ≠ 0 := (map_ne_zero σ).2 hz0
  have hcE : algebraMap E (w.adicCompletion E) c ≠ 0 := (map_ne_zero _).2 hc
  have h2 : Valued.v (σ z / algebraMap E (w.adicCompletion E) c - 1) ≤ WithZero.exp (-(M : ℤ)) := by
    have e : σ z / algebraMap E (w.adicCompletion E) c - 1 = σ (z / algebraMap E E' c - 1) := by
      rw [map_sub, map_div₀, hσE, map_one]
    rw [e, hσv]
    exact hzw.trans (hle M (by omega))
  rw [← valued_algebraMap_eq, map_sub, map_div₀, map_one]
  have e2 : algebraMap E (w.adicCompletion E) (Algebra.norm E z) / algebraMap E (w.adicCompletion E) c =
      (algebraMap E (w.adicCompletion E) (Algebra.norm E z) / σ z) * (σ z / algebraMap E (w.adicCompletion E) c) := by
    field_simp
  rw [e2]
  exact mul_sub_one_le Valued.v _ _ M hF h2

end GlobalTheory.NormCompat.LocalDegOne
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormCloseToComponentLocalDegreeOneStatement

section

@[expose] public section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.norm_close_to_component_localDegreeOne : ∀ (E E' : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E'] (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) (w' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E')) (i : w.adicCompletion E ≃+* w'.adicCompletion E'), Continuous i → (∀ x : E, i (algebraMap E _ x) = algebraMap E' _ (algebraMap E E' x)) → ∀ M : ℕ, ∃ M' : ℕ, ∀ (c : E) (z : E'), c ≠ 0 → (∀ w'' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E'), w''.asIdeal.comap (algebraMap (NumberField.RingOfIntegers E) (NumberField.RingOfIntegers E')) = w.asIdeal → w'' ≠ w' → w''.valuation E' (z - 1) ≤ WithZero.exp (-(M' : ℤ))) → w'.valuation E' (z / algebraMap E E' c - 1) ≤ WithZero.exp (-(M' : ℤ)) → w.valuation E (Algebra.norm E z / c - 1) ≤ WithZero.exp (-(M : ℤ)) := by
  first | exact @GlobalTheory.NormCompat.LocalDegOne.norm_div_close_to_one | exact GlobalTheory.NormCompat.LocalDegOne.norm_div_close_to_one | (intros; apply GlobalTheory.NormCompat.LocalDegOne.norm_div_close_to_one <;> assumption)
end
end
