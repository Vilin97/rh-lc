module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.AevalElimEqRenameLinearSubstitution
public import Mathlib.Algebra.Polynomial.Degree.Defs
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.TypeStar
public import Mathlib.Topology.Algebra.MvPolynomial
public import ReciprocityTheory.SemistableReduction.LagrangeIdealLiftsFact
import ReciprocityTheory.SemistableReduction.SphereTorusA
public import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.SemistableReduction.GaussAbsMulOfMonomialOrder
import ReciprocityTheory.SemistableReduction.LagrangeIdealLiftsFact
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
public import Mathlib.NumberTheory.NumberField.ProductFormula

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatDegreeLeAndCoeffProdPow

section

@[expose] public section

universe u_1 u_2

namespace GlobalTheory.ProductDegreeCoefficient

open Polynomial

theorem natDegree_le_and_coeff_prod_pow {B : Type u_1} [CommRing B] {T : Type u_2}
    (s : Finset T) (p : T → Polynomial B) (e : T → ℕ)
    (h : ∀ t : T, (p t).natDegree ≤ 1) :
    (∏ t ∈ s, p t ^ e t).natDegree ≤ ∑ t ∈ s, e t ∧
      (∏ t ∈ s, p t ^ e t).coeff (∑ t ∈ s, e t) = ∏ t ∈ s, (p t).coeff 1 ^ e t := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    obtain ⟨ih1, ih2⟩ := ih
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha]
    have h1 : (p a ^ e a).natDegree ≤ e a := by
      have := Polynomial.natDegree_pow_le_of_le (e a) (h a)
      simpa using this
    have h2 : (p a ^ e a).coeff (e a) = (p a).coeff 1 ^ e a := by
      have := Polynomial.coeff_pow_of_natDegree_le (m := e a) (h a)
      simpa using this
    refine ⟨Polynomial.natDegree_mul_le_of_le h1 ih1, ?_⟩
    rw [Polynomial.coeff_mul_add_eq_of_natDegree_le h1 ih1, h2, ih2]

end GlobalTheory.ProductDegreeCoefficient
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ContinuousTorusPoint

section

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MeasureTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.Closed

section

variable {K : Type} [Field K] [NumberField K] {κ : Type} [Fintype κ]

theorem map_ne_zero_of_ne_zero {f : MvPolynomial κ K} (hf : f ≠ 0) (σ : K →+* ℂ) :
    MvPolynomial.map σ f ≠ 0 := fun h => hf ((MvPolynomial.map_injective σ σ.injective) (by rw [h, map_zero]))

end

theorem logHeight_le_torusHeight {K : Type} [Field K] [NumberField K] {B n : ℕ} (hn : 0 < n) (a : Fin B → ℕ)
    (f : MvPolynomial (Fin B × Fin n) K) (hf : f ≠ 0) (ha : IsMultiHomogeneous a f) :
    h0 f ≤ hTX5 f := by
  unfold h0 hTX5
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  refine add_le_add le_rfl (Finset.sum_le_sum fun σ _ => ?_)
  exact sphereLeTorus B n a _ hn (map_ne_zero_of_ne_zero hf σ) (isMultiHomogeneous_map_ring a f ha σ)

theorem continuous_torusPoint' {κ : Type} : Continuous (fun θ : κ → ℝ => torusPoint θ) := by
  unfold torusPoint
  exact continuous_pi fun i => Complex.continuous_exp.comp
    (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_apply i)))

theorem measurable_log_eval_torus {κ : Type} [Fintype κ] (f : MvPolynomial κ ℂ) :
    Measurable (fun θ : κ → ℝ => Real.log ‖MvPolynomial.eval (torusPoint θ) f‖) := (Real.measurable_log.comp (continuous_norm.comp ((MvPolynomial.continuous_eval f).comp continuous_torusPoint')).measurable)

theorem torusProb_map_comp {κ κ' : Type} [Fintype κ] [Fintype κ'] (e : κ → κ')
    (he : Function.Injective e) :
    Measure.map (fun θ : κ' → ℝ => θ ∘ e) (torusProb κ') = torusProb κ := by
  classical
  have hmeas : Measurable (fun θ : κ' → ℝ => θ ∘ e) :=
    Measurable.of_eval (fun a => measurable_pi_apply (e a))
  unfold torusProb
  symm
  refine Measure.pi_eq (fun s hs => ?_)
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs)]
  have hpre : (fun θ : κ' → ℝ => θ ∘ e) ⁻¹' Set.univ.pi s =
      Set.univ.pi (Function.extend e s (fun _ => Set.univ)) := by
    ext θ
    simp only [Set.mem_preimage, Set.mem_univ_pi, Function.comp_apply]
    constructor
    · intro h y
      by_cases hy : ∃ a, e a = y
      · obtain ⟨a, rfl⟩ := hy
        rw [he.extend_apply]
        exact h a
      · rw [Function.extend_apply' _ _ _ hy]
        trivial
    · intro h a
      have h1 := h (e a)
      rwa [he.extend_apply] at h1
  rw [hpre, Measure.pi_pi]
  set ν : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  have hν : ν Set.univ = 1 := by simp [ν]
  calc ∏ y, ν (Function.extend e s (fun _ => Set.univ) y)
      = ∏ y ∈ Finset.univ.image e, ν (Function.extend e s (fun _ => Set.univ) y) := by
        refine (Finset.prod_subset (Finset.subset_univ _) (fun y _ hy => ?_)).symm
        have hy' : ¬ ∃ a, e a = y := by simpa using hy
        rw [Function.extend_apply' _ _ _ hy', hν]
    _ = ∏ a, ν (s a) := by
        rw [Finset.prod_image (fun a _ b _ h => he h)]
        refine Finset.prod_congr rfl (fun a _ => ?_)
        rw [he.extend_apply]

theorem torusMean_rename {κ κ' : Type} [Fintype κ] [Fintype κ'] (e : κ → κ')
    (he : Function.Injective e) (f : MvPolynomial κ ℂ) :
    torusMean (MvPolynomial.rename e f) = torusMean f := by
  unfold torusMean
  simp_rw [MvPolynomial.eval_rename]
  rw [← torusProb_map_comp e he, MeasureTheory.integral_map]
  · rfl
  · exact (Measurable.of_eval fun i => measurable_pi_apply (e i)).aemeasurable
  · exact (measurable_log_eval_torus f).aestronglyMeasurable

theorem gaussAbs_rename_of_injective {K : Type} [Field K] [NumberField K] {κ κ' : Type} (e : κ → κ')
    (he : Function.Injective e) (w : FinitePlace K) (f : MvPolynomial κ K) :
    gaussAbs w (MvPolynomial.rename e f) = gaussAbs w f := by
  classical
  unfold gaussAbs
  rw [MvPolynomial.support_rename_of_injective he, Finset.sup_image]
  congr 1
  refine Finset.sup_congr rfl fun s _ => ?_
  simp only [Function.comp_apply, MvPolynomial.coeff_rename_mapDomain e he]

theorem hTX5_rename {K : Type} [Field K] [NumberField K] {κ κ' : Type} [Fintype κ] [Fintype κ']
    (e : κ → κ') (he : Function.Injective e) (f : MvPolynomial κ K) :
    hTX5 (MvPolynomial.rename e f) = hTX5 f := by
  unfold hTX5
  congr 2
  · exact finsum_congr fun w => by rw [gaussAbs_rename_of_injective e he w f]
  · refine Finset.sum_congr rfl fun σ _ => ?_
    rw [MvPolynomial.map_rename, torusMean_rename e he]

end ReciprocityTheory.ChartRestriction.G.T0
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.LogHeightLeTorusHeightSubst

section

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

section CoeffIn

variable {R : Type*} [CommRing R] {V : Type*} [DecidableEq V]

noncomputable def asPolyInVar (i : V) : MvPolynomial V R →ₐ[R] Polynomial (MvPolynomial V R) :=
  MvPolynomial.aeval fun v => if v = i then Polynomial.X else Polynomial.C (MvPolynomial.X v)

theorem coeffIn_eq_sum (i : V) (k : ℕ) (P : MvPolynomial V R) (S : Finset (V →₀ ℕ))
    (hS : P.support ⊆ S) :
    ReciprocityTheory.MultiplicativeHeights.coeffIn i k P =
      ∑ s ∈ S, if s i = k then MvPolynomial.monomial (s.erase i) (P.coeff s) else 0 := by
  unfold ReciprocityTheory.MultiplicativeHeights.coeffIn
  rw [Finset.sum_filter]
  apply Finset.sum_subset hS
  intro s _ hs
  rw [MvPolynomial.notMem_support_iff.mp hs]
  simp

theorem coeffIn_add_alt (i : V) (k : ℕ) (p q : MvPolynomial V R) :
    ReciprocityTheory.MultiplicativeHeights.coeffIn i k (p + q) = ReciprocityTheory.MultiplicativeHeights.coeffIn i k p + ReciprocityTheory.MultiplicativeHeights.coeffIn i k q := by
  classical
  rw [coeffIn_eq_sum i k _ _ MvPolynomial.support_add,
    coeffIn_eq_sum i k p (p.support ∪ q.support) Finset.subset_union_left,
    coeffIn_eq_sum i k q (p.support ∪ q.support) Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs <;> simp [MvPolynomial.coeff_add, map_add (f := _)]

theorem polyIn_monomial_of_eq_zero (i : V) (t : V →₀ ℕ) (ht : t i = 0) (a : R) :
    asPolyInVar i (MvPolynomial.monomial t a) = Polynomial.C (MvPolynomial.monomial t a) := by
  rw [asPolyInVar, MvPolynomial.aeval_monomial, MvPolynomial.monomial_eq, Polynomial.C_mul,
    Finsupp.prod, Finsupp.prod, map_prod, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]
  congr 1
  refine Finset.prod_congr rfl fun v hv => ?_
  have hvi : v ≠ i := by
    rintro rfl
    exact (Finsupp.mem_support_iff.mp hv) ht
  rw [if_neg hvi, map_pow]

theorem polyIn_monomial (i : V) (u : V →₀ ℕ) (a : R) :
    asPolyInVar i (MvPolynomial.monomial u a) =
      Polynomial.C (MvPolynomial.monomial (u.erase i) a) * Polynomial.X ^ (u i) := by
  have hu : u = Finsupp.single i (u i) + u.erase i := (Finsupp.single_add_erase i u).symm
  have e : MvPolynomial.monomial u a =
      MvPolynomial.monomial (Finsupp.single i (u i)) (1 : R) * MvPolynomial.monomial (u.erase i) a := by
    conv_lhs => rw [hu]
    rw [MvPolynomial.monomial_mul, one_mul]
  rw [e, map_mul, polyIn_monomial_of_eq_zero i (u.erase i) (by simp) a,
    ← MvPolynomial.X_pow_eq_monomial,
    map_pow, asPolyInVar, MvPolynomial.aeval_X, if_pos rfl, mul_comm]

theorem coeffIn_eq_polyIn_coeff (i : V) (k : ℕ) (P : MvPolynomial V R) :
    ReciprocityTheory.MultiplicativeHeights.coeffIn i k P = (asPolyInVar i P).coeff k := by
  classical
  refine MvPolynomial.induction_on' P (fun u a => ?_) (fun p q hp hq => ?_)
  · rw [coeffIn_eq_sum i k _ {u} MvPolynomial.support_monomial_subset, Finset.sum_singleton,
      MvPolynomial.coeff_monomial, if_pos rfl, polyIn_monomial, Polynomial.coeff_C_mul_X_pow]
    by_cases h : u i = k
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (Ne.symm h)]
  · rw [coeffIn_add_alt, map_add (f := _), Polynomial.coeff_add, hp, hq]

theorem coeffIn_map {S : Type*} [CommRing S] (φ : R →+* S) (hφ : Function.Injective φ) (i : V)
    (k : ℕ) (P : MvPolynomial V R) :
    ReciprocityTheory.MultiplicativeHeights.coeffIn i k (MvPolynomial.map φ P) =
      MvPolynomial.map φ (ReciprocityTheory.MultiplicativeHeights.coeffIn i k P) := by
  unfold ReciprocityTheory.MultiplicativeHeights.coeffIn

  rw [MvPolynomial.support_map_of_injective _ hφ, map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [MvPolynomial.map_monomial, MvPolynomial.coeff_map]

end CoeffIn

theorem gaussAbs_coeffIn_le {V : Type*} (w : FinitePlace K) (i : V) (k : ℕ)
    (P : MvPolynomial V K) :
    ReciprocityTheory.MultiplicativeHeights.gaussAbs w (ReciprocityTheory.MultiplicativeHeights.coeffIn i k P) ≤ ReciprocityTheory.MultiplicativeHeights.gaussAbs w P := by
  classical
  have h0 : 0 ≤ ReciprocityTheory.MultiplicativeHeights.gaussAbs w P := by unfold ReciprocityTheory.MultiplicativeHeights.gaussAbs; exact NNReal.coe_nonneg _
  refine ReciprocityTheory.MultiplicativeHeights.gauss_abs_le_of_coeff_le w _ h0 fun t => ?_
  unfold ReciprocityTheory.MultiplicativeHeights.coeffIn
  rw [MvPolynomial.coeff_sum]
  refine ReciprocityTheory.MultiplicativeHeights.finite_place_sum_le w _ _ h0 fun s _ => ?_
  rw [MvPolynomial.coeff_monomial]
  split_ifs
  · exact ReciprocityTheory.MultiplicativeHeights.coeff_le_gauss_abs w P s
  · rw [map_zero]; exact h0

theorem coeff_prod_pow_linear {B : Type*} [CommRing B] {T : Type*} (s : Finset T) (p : T → Polynomial B)
    (e : T → ℕ) (hp : ∀ t, (p t).natDegree ≤ 1) :
    (∏ t ∈ s, p t ^ e t).natDegree ≤ ∑ t ∈ s, e t ∧
      (∏ t ∈ s, p t ^ e t).coeff (∑ t ∈ s, e t) = ∏ t ∈ s, (p t).coeff 1 ^ e t := by
  first | exact GlobalTheory.ProductDegreeCoefficient.natDegree_le_and_coeff_prod_pow .. | (apply GlobalTheory.ProductDegreeCoefficient.natDegree_le_and_coeff_prod_pow <;> assumption) | (intros; apply GlobalTheory.ProductDegreeCoefficient.natDegree_le_and_coeff_prod_pow <;> assumption) | (apply @GlobalTheory.ProductDegreeCoefficient.natDegree_le_and_coeff_prod_pow <;> assumption) | (intros; apply @GlobalTheory.ProductDegreeCoefficient.natDegree_le_and_coeff_prod_pow <;> assumption) | (apply @GlobalTheory.ProductDegreeCoefficient.natDegree_le_and_coeff_prod_pow <;> first | assumption | infer_instance)

theorem polyIn_substitution_leading {D N : ℕ} (f : KTp K D N) (a : Fin (D + 1) → ℕ)
    (hmh : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous a f) :
    (asPolyInVar (Sum.inr 0) (bilinearSubstitution f)).natDegree ≤ ∑ b, a b ∧
      (asPolyInVar (Sum.inr 0) (bilinearSubstitution f)).coeff (∑ b, a b) =
        MvPolynomial.rename (fun t : TVar D N =>
          (Sum.inl (t.1.succ, t.2) : (Fin (D + 2) × Fin (N + 1)) ⊕ Fin (D + 2))) f := by
  classical
  set E := asPolyInVar (R := K) (V := (Fin (D + 2) × Fin (N + 1)) ⊕ Fin (D + 2)) (Sum.inr 0)
  let p : TVar D N → Polynomial (MvPolynomial ((Fin (D + 2) × Fin (N + 1)) ⊕ Fin (D + 2)) K) :=
    fun t => E (MvPolynomial.X (Sum.inr 0) * MvPolynomial.X (Sum.inl (t.1.succ, t.2)) -
      MvPolynomial.X (Sum.inr t.1.succ) * MvPolynomial.X (Sum.inl (0, t.2)))
  have hpt : ∀ t, p t = Polynomial.X * Polynomial.C (MvPolynomial.X (Sum.inl (t.1.succ, t.2))) -
      Polynomial.C (MvPolynomial.X (Sum.inr t.1.succ)) *
        Polynomial.C (MvPolynomial.X (Sum.inl (0, t.2))) := by
    intro t
    simp [p, E, asPolyInVar, Fin.succ_ne_zero]
  have hp1 : ∀ t, (p t).natDegree ≤ 1 := by
    intro t
    rw [hpt]
    refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · exact (Polynomial.natDegree_mul_le).trans (by simp)
    · exact (Polynomial.natDegree_mul_le).trans (by simp)
  have hpc : ∀ t, (p t).coeff 1 = MvPolynomial.X (Sum.inl (t.1.succ, t.2)) := by
    intro t
    rw [hpt]
    simp [Polynomial.coeff_C]
  have hEG : E (bilinearSubstitution f) = MvPolynomial.aeval p f := by
    unfold bilinearSubstitution
    rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  have hsum : ∀ s ∈ f.support, ∑ t, s t = ∑ b, a b := by
    intro s hs
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun b _ => hmh s hs b
  have hterm : ∀ s ∈ f.support,
      (MvPolynomial.aeval p (MvPolynomial.monomial s (f.coeff s))).natDegree ≤ ∑ b, a b ∧
        (MvPolynomial.aeval p (MvPolynomial.monomial s (f.coeff s))).coeff (∑ b, a b) =
          MvPolynomial.rename (fun t : TVar D N =>
            (Sum.inl (t.1.succ, t.2) : (Fin (D + 2) × Fin (N + 1)) ⊕ Fin (D + 2)))
            (MvPolynomial.monomial s (f.coeff s)) := by
    intro s hs
    obtain ⟨h1, h2⟩ := coeff_prod_pow_linear Finset.univ p s hp1
    rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
      Polynomial.algebraMap_apply, ← hsum s hs]
    refine ⟨(Polynomial.natDegree_C_mul_le _ _).trans h1, ?_⟩
    rw [Polynomial.coeff_C_mul, h2, MvPolynomial.rename_monomial, MvPolynomial.monomial_eq,
      MvPolynomial.algebraMap_eq]
    congr 1
    rw [Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
      Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    exact Finset.prod_congr rfl fun t _ => by rw [hpc]
  rw [hEG]
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  rw [MvPolynomial.aeval_sum, map_sum (MvPolynomial.rename _)]
  refine ⟨Polynomial.natDegree_sum_le_of_forall_le _ _ fun s hs => (hterm s hs).1, ?_⟩
  rw [Polynomial.finsetSum_coeff]
  exact Finset.sum_congr rfl fun s hs => (hterm s hs).2

theorem logHeight_le_torusHeight_subst {D N : ℕ} (f : KTp K D N) (hf : f ≠ 0) (a : Fin (D + 1) → ℕ)
    (hmh : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous a f) : ReciprocityTheory.MultiplicativeHeights.h0 f ≤ hTX5 (bilinearSubstitution f) := by
  classical
  set ρ : TVar D N → (Fin (D + 2) × Fin (N + 1)) ⊕ Fin (D + 2) := fun t => Sum.inl (t.1.succ, t.2)
  have hρ : Function.Injective ρ := by
    intro t t' h
    simp only [ρ, Sum.inl.injEq, Prod.mk.injEq, Fin.succ_inj] at h
    exact Prod.ext h.1 h.2
  obtain ⟨hdeg, htop⟩ := polyIn_substitution_leading f a hmh
  have hc : ReciprocityTheory.MultiplicativeHeights.coeffIn (Sum.inr 0) (∑ b, a b) (bilinearSubstitution f) = MvPolynomial.rename ρ f := by
    rw [coeffIn_eq_polyIn_coeff, htop]
  have hc' : ∀ k, ∑ b, a b < k → ReciprocityTheory.MultiplicativeHeights.coeffIn (Sum.inr 0) k (bilinearSubstitution f) = 0 := by
    intro k hk
    rw [coeffIn_eq_polyIn_coeff]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg hk)
  have hR0 : MvPolynomial.rename ρ f ≠ 0 := fun h0 =>
    hf (MvPolynomial.rename_injective ρ hρ (by rw [h0, map_zero]))
  have hG0 : bilinearSubstitution f ≠ 0 := by
    intro h0
    apply hR0
    rw [← hc, h0]
    unfold ReciprocityTheory.MultiplicativeHeights.coeffIn
    simp
  have h1 : ReciprocityTheory.MultiplicativeHeights.h0 f ≤ hTX5 f := logHeight_le_torusHeight (Nat.succ_pos N) a f hf hmh
  refine h1.trans ?_
  rw [← hTX5_rename ρ hρ f]
  unfold hTX5
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  refine add_le_add ?_ (Finset.sum_le_sum fun φ _ => ?_)
  · refine finsum_le_finsum' (ReciprocityTheory.MultiplicativeHeights.gauss_abs_log_support_finite _ hR0)
      (ReciprocityTheory.MultiplicativeHeights.gauss_abs_log_support_finite _ hG0) fun w => ?_
    refine Real.log_le_log (ReciprocityTheory.MultiplicativeHeights.gauss_abs_pos_of_ne_zero w _ hR0) ?_
    rw [← hc]
    exact gaussAbs_coeffIn_le w _ _ _
  · have hinj := MvPolynomial.map_injective φ φ.injective
      (σ := (Fin (D + 2) × Fin (N + 1)) ⊕ Fin (D + 2))
    have e1 : ReciprocityTheory.MultiplicativeHeights.coeffIn (Sum.inr 0) (∑ b, a b) (MvPolynomial.map φ (bilinearSubstitution f)) =
        MvPolynomial.map φ (MvPolynomial.rename ρ f) := by
      rw [coeffIn_map φ φ.injective, hc]
    have hne : ReciprocityTheory.MultiplicativeHeights.coeffIn (Sum.inr 0) (∑ b, a b) (MvPolynomial.map φ (bilinearSubstitution f)) ≠ 0 := by
      rw [e1]
      intro h0
      exact hR0 (hinj (by rw [h0, map_zero]))
    have := ReciprocityTheory.MultiplicativeHeights.Closed.torusCoeff _ (MvPolynomial.map φ (bilinearSubstitution f)) (Sum.inr 0) (∑ b, a b) hne
      (Or.inl fun k hk => by rw [coeffIn_map φ φ.injective, hc' k hk, map_zero])
    rwa [e1] at this

theorem gaussAbs_monomial {σ : Type*} (w : FinitePlace K) (s : σ →₀ ℕ) (κ : K) :
    ReciprocityTheory.MultiplicativeHeights.gaussAbs w (MvPolynomial.monomial s κ) = w κ := by
  classical
  apply le_antisymm
  · refine ReciprocityTheory.MultiplicativeHeights.gauss_abs_le_of_coeff_le w _ (apply_nonneg w κ) fun t => ?_
    rw [MvPolynomial.coeff_monomial]
    split_ifs
    · exact le_rfl
    · rw [map_zero]; exact apply_nonneg w κ
  · have := ReciprocityTheory.MultiplicativeHeights.coeff_le_gauss_abs w (MvPolynomial.monomial s κ) s
    rwa [MvPolynomial.coeff_monomial, if_pos rfl] at this

theorem sum_log_abs_eq_zero (κ : K) (hκ : κ ≠ 0) :
    ∑ᶠ w : FinitePlace K, Real.log (w κ) + ∑ φ : K →+* ℂ, Real.log ‖φ κ‖ = 0 := by
  have hmul : (Function.mulSupport fun w : FinitePlace K => w κ).Finite :=
    FinitePlace.hasFiniteMulSupport hκ
  have h1 : ∑ᶠ w : FinitePlace K, Real.log (w κ) = Real.log (∏ᶠ w : FinitePlace K, w κ) := by
    rw [finsum_eq_sum_of_support_subset (s := hmul.toFinset),
      finprod_eq_prod_of_mulSupport_subset (s := hmul.toFinset) _ (by simp),
      Real.log_prod (fun w _ => (FinitePlace.pos_iff.2 hκ).ne')]
    intro w hw
    simp only [Set.Finite.coe_toFinset, Function.mem_mulSupport]
    intro h1
    apply hw
    simp [h1]
  have h2 : ∑ φ : K →+* ℂ, Real.log ‖φ κ‖ = Real.log |Algebra.norm ℚ κ| := by
    rw [← Real.log_prod (fun φ _ => norm_ne_zero_iff.2 ((map_ne_zero φ).2 hκ))]
    congr 1
    have := congr_arg (‖·‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ κ)
    rw [norm_prod] at this
    rw [Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun φ => ‖φ κ‖) (fun φ => ‖φ κ‖)
      (fun _ => by simp [RingHom.equivRatAlgHom_apply]), ← this]
    rw [eq_ratCast, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
  rw [h1, h2, FinitePlace.prod_eq_inv_abs_norm hκ]
  push_cast
  rw [Real.log_inv, neg_add_cancel]

theorem hTX5_C_mul_X_pow_mul_pow {σ : Type} [Fintype σ] (κ : K) (hκ : κ ≠ 0) (v : σ) (a m : ℕ)
    (F1 : MvPolynomial σ K) (hF1 : F1 ≠ 0) :
    hTX5 (MvPolynomial.C κ * MvPolynomial.X v ^ a * F1 ^ m) = m * hTX5 F1 := by
  classical
  have hP : MvPolynomial.C κ * MvPolynomial.X v ^ a =
      MvPolynomial.monomial (Finsupp.single v a) κ := by
    rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.C_mul_monomial, mul_one]
  have hM0 : MvPolynomial.monomial (Finsupp.single v a) κ ≠ 0 := by
    rw [Ne, MvPolynomial.monomial_eq_zero]; exact hκ
  have hpow : ∀ k : ℕ, F1 ^ k ≠ 0 := fun k => pow_ne_zero k hF1
  have hgpow : ∀ (w : FinitePlace K) (k : ℕ),
      ReciprocityTheory.MultiplicativeHeights.gaussAbs w (F1 ^ k) = ReciprocityTheory.MultiplicativeHeights.gaussAbs w F1 ^ k := by
    intro w k
    induction k with
    | zero => rw [pow_zero, pow_zero, ← MvPolynomial.C_1, MvPolynomial.C_apply, gaussAbs_monomial,
        map_one]
    | succ k ih => rw [pow_succ, pow_succ, ReciprocityTheory.MultiplicativeHeights.gauss_abs_mul w _ _ (hpow k) hF1, ih]
  have hgauss : ∀ w : FinitePlace K,
      Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs w (MvPolynomial.C κ * MvPolynomial.X v ^ a * F1 ^ m)) =
        Real.log (w κ) + m * Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs w F1) := by
    intro w
    rw [hP, ReciprocityTheory.MultiplicativeHeights.gauss_abs_mul w _ _ hM0 (hpow m), gaussAbs_monomial, hgpow,
      Real.log_mul, Real.log_pow]
    · exact (FinitePlace.pos_iff.2 hκ).ne'
    · exact (pow_pos (ReciprocityTheory.MultiplicativeHeights.gauss_abs_pos_of_ne_zero w F1 hF1) m).ne'
  have hfinκ : (Function.support fun w : FinitePlace K => Real.log (w κ)).Finite := by
    have := ReciprocityTheory.MultiplicativeHeights.gauss_abs_log_support_finite (MvPolynomial.monomial (Finsupp.single v a) κ) hM0
    simpa only [gaussAbs_monomial] using this
  have hfinF := ReciprocityTheory.MultiplicativeHeights.gauss_abs_log_support_finite F1 hF1
  have hfinsum : ∑ᶠ w : FinitePlace K,
      Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs w (MvPolynomial.C κ * MvPolynomial.X v ^ a * F1 ^ m)) =
      ∑ᶠ w : FinitePlace K, Real.log (w κ) +
        m * ∑ᶠ w : FinitePlace K, Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs w F1) := by
    simp_rw [hgauss]
    rw [finsum_add_distrib hfinκ (hfinF.subset (Function.support_mul_subset_right _ _)),
      mul_finsum' _ _ hfinF]
  have TB := ReciprocityTheory.MultiplicativeHeights.Closed.torusMeanBasic
  have htor : ∀ φ : K →+* ℂ,
      ReciprocityTheory.MultiplicativeHeights.torusMean (MvPolynomial.map φ (MvPolynomial.C κ * MvPolynomial.X v ^ a * F1 ^ m)) =
        Real.log ‖φ κ‖ + m * ReciprocityTheory.MultiplicativeHeights.torusMean (MvPolynomial.map φ F1) := by
    intro φ
    have hinj := MvPolynomial.map_injective φ φ.injective (σ := σ)
    have hF1' : MvPolynomial.map φ F1 ≠ 0 := fun h => hF1 (hinj (by rw [h, map_zero]))
    have hpow' : ∀ k : ℕ, (MvPolynomial.map φ F1) ^ k ≠ 0 := fun k => pow_ne_zero k hF1'
    have hmon0 : MvPolynomial.monomial (Finsupp.single v a) (φ κ) ≠ 0 := by
      rw [Ne, MvPolynomial.monomial_eq_zero]; exact (map_ne_zero φ).2 hκ
    have hp : ∀ k : ℕ, ReciprocityTheory.MultiplicativeHeights.torusMean ((MvPolynomial.map φ F1) ^ k) =
        k * ReciprocityTheory.MultiplicativeHeights.torusMean (MvPolynomial.map φ F1) := by
      intro k
      induction k with
      | zero =>
        rw [pow_zero, ← MvPolynomial.C_1, MvPolynomial.C_apply, (TB σ).2.2]
        simp
      | succ k ih =>
        rw [pow_succ, (TB σ).2.1 _ _ (hpow' k) hF1', ih]
        push_cast
        ring
    rw [hP, map_mul, map_pow, MvPolynomial.map_monomial, (TB σ).2.1 _ _ hmon0 (hpow' m), (TB σ).2.2,
      hp]
  unfold hTX5
  rw [hfinsum]
  simp_rw [htor]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, mul_div_assoc']
  congr 1
  linear_combination sum_log_abs_eq_zero κ hκ

end ReciprocityTheory.ChartRestriction.G.T0
end
end
