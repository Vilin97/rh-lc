module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsTensorFiniteAdeleEquiv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdeleEquivOfLocal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseElementNegativeAtTwoEmbeddingsStatement
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
import GroundTheory.GlobalFields.LocalAtPlace
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdeleSqSubMulSq

section

@[expose] public section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing Polynomial

namespace GlobalTheory.AdelicQuadSol

theorem exists_sq_eq_of_approx {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (r b : v.adicCompletionIntegers K) (hb : b ^ 2 - r ∈ maximalIdeal (v.adicCompletionIntegers K))
    (hu : IsUnit (2 * b)) : ∃ s : v.adicCompletionIntegers K, s ^ 2 = r := by
  haveI := GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v
  have hm : (X ^ 2 - C r : (v.adicCompletionIntegers K)[X]).Monic := monic_X_pow_sub_C r two_ne_zero
  have hd : eval b (derivative (X ^ 2 - C r : (v.adicCompletionIntegers K)[X])) = 2 * b := by
    simp [one_add_one_eq_two]
  obtain ⟨s, hs, -⟩ := HenselianRing.is_henselian (I := maximalIdeal (v.adicCompletionIntegers K))
    (X ^ 2 - C r) hm b (by simpa using hb) (by rw [hd]; exact hu.map _)
  refine ⟨s, ?_⟩
  have h0 : s ^ 2 - r = 0 := by simpa using hs
  linear_combination h0

theorem local_integral : ∀ (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (δ a : K), Valued.v (algebraMap K (v.adicCompletion K) 2) = 1 → Valued.v (algebraMap K (v.adicCompletion K) δ) = 1 → Valued.v (algebraMap K (v.adicCompletion K) a) = 1 → ∃ x y : v.adicCompletion K, x ∈ v.adicCompletionIntegers K ∧ y ∈ v.adicCompletionIntegers K ∧ x ^ 2 - algebraMap K (v.adicCompletion K) δ * y ^ 2 = algebraMap K (v.adicCompletion K) a := by
  intro K _ _ v δ a h2 hδ ha
  set O := v.adicCompletionIntegers K
  let d : O := ⟨algebraMap K (v.adicCompletion K) δ, by rw [mem_adicCompletionIntegers, hδ]⟩
  let α : O := ⟨algebraMap K (v.adicCompletion K) a, by rw [mem_adicCompletionIntegers, ha]⟩
  have hdu : IsUnit d := adicCompletionIntegers.isUnit_iff_valued_eq_one.2 hδ
  have hαu : IsUnit α := adicCompletionIntegers.isUnit_iff_valued_eq_one.2 ha
  have h2u : IsUnit (2 : O) := by
    apply adicCompletionIntegers.isUnit_iff_valued_eq_one.2
    have e2 : ((2 : O) : v.adicCompletion K) = algebraMap K (v.adicCompletion K) 2 := by
      rw [map_ofNat]; rfl
    rw [e2]; exact h2
  letI := Fintype.ofFinite (ResidueField O)
  have h2k : (2 : ResidueField O) ≠ 0 := by
    have := (h2u.map (residue O)).ne_zero
    rwa [map_ofNat] at this
  have hchar : ringChar (ResidueField O) ≠ 2 := by
    intro h
    apply h2k
    have := ringChar.Nat.cast_ringChar (R := ResidueField O)
    rw [h] at this
    exact_mod_cast this
  have hodd := FiniteField.odd_card_of_char_ne_two hchar
  have hdk : residue O d ≠ 0 := (hdu.map (residue O)).ne_zero
  have hαk : residue O α ≠ 0 := (hαu.map (residue O)).ne_zero
  obtain ⟨s, t, hst⟩ := FiniteField.exists_root_sum_quadratic
    (f := (X ^ 2 : (ResidueField O)[X])) (g := C (-residue O d) * X ^ 2 + C (-residue O α))
    (by simp) (by compute_degree!) hodd
  obtain ⟨x0, rfl⟩ := residue_surjective s
  obtain ⟨y0, rfl⟩ := residue_surjective t
  have he : x0 ^ 2 - d * y0 ^ 2 - α ∈ maximalIdeal O := by
    rw [← residue_eq_zero_iff]
    simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X] at hst
    rw [map_sub, map_sub, map_mul, map_pow, map_pow]
    linear_combination hst
  by_cases hx : residue O x0 = 0
  · have hy : residue O y0 ≠ 0 := by
      intro hy
      apply hαk
      have := (residue_eq_zero_iff _).2 he
      rw [map_sub, map_sub, map_mul, map_pow, map_pow, hx, hy] at this
      linear_combination -this
    obtain ⟨e, he'⟩ := hdu
    set di : O := ((e⁻¹ : Oˣ) : O)
    have hdi : di * d = 1 := by rw [← he']; exact e.inv_mul
    obtain ⟨y, hy2⟩ := exists_sq_eq_of_approx v (di * (x0 ^ 2 - α)) y0
      (by
        have : y0 ^ 2 - di * (x0 ^ 2 - α) = -di * (x0 ^ 2 - d * y0 ^ 2 - α) := by
          linear_combination (-(y0 ^ 2)) * hdi
        rw [this]; exact Ideal.mul_mem_left _ _ he)
      (h2u.mul (by
        rw [← IsLocalRing.residue_ne_zero_iff_isUnit]; exact hy))
    refine ⟨(x0 : v.adicCompletion K), (y : v.adicCompletion K), x0.2, y.2, ?_⟩
    have hO : x0 ^ 2 - d * y ^ 2 = α := by
      rw [hy2]; linear_combination (-(x0 ^ 2 - α)) * hdi
    have := congrArg (fun z : O => (z : v.adicCompletion K)) hO
    simpa [d, α] using this
  · obtain ⟨x, hx2⟩ := exists_sq_eq_of_approx v (α + d * y0 ^ 2) x0
      (by
        have : x0 ^ 2 - (α + d * y0 ^ 2) = x0 ^ 2 - d * y0 ^ 2 - α := by ring
        rw [this]; exact he)
      (h2u.mul (by rw [← IsLocalRing.residue_ne_zero_iff_isUnit]; exact hx))
    refine ⟨(x : v.adicCompletion K), (y0 : v.adicCompletion K), x.2, y0.2, ?_⟩
    have hO : x ^ 2 - d * y0 ^ 2 = α := by rw [hx2]; ring
    have := congrArg (fun z : O => (z : v.adicCompletion K)) hO
    simpa [d, α] using this

theorem eventually_valued_eq_one {K : Type} [Field K] [NumberField K] {c : K} (hc : c ≠ 0) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      Valued.v (algebraMap K (v.adicCompletion K) c) = 1 := by
  filter_upwards [(algebraMap K (FiniteAdeleRing (𝓞 K) K) c).2,
    (algebraMap K (FiniteAdeleRing (𝓞 K) K) c⁻¹).2] with v h1 h2
  have h1' : Valued.v (algebraMap K (v.adicCompletion K) c) ≤ 1 := (mem_adicCompletionIntegers (𝓞 K) K v).1 h1
  have h2' : Valued.v (algebraMap K (v.adicCompletion K) c⁻¹) ≤ 1 := (mem_adicCompletionIntegers (𝓞 K) K v).1 h2
  rw [map_inv₀, map_inv₀] at h2'
  have h0 : Valued.v (algebraMap K (v.adicCompletion K) c) ≠ 0 := by
    rw [Ne, map_eq_zero, map_eq_zero]; exact hc
  exact le_antisymm h1' ((inv_le_one₀ (zero_lt_iff.2 h0)).1 h2')

theorem exists_finiteAdele_sq_sub_mul_sq : ∀ (K : Type) [Field K] [NumberField K] (δ a : K), δ ≠ 0 → a ≠ 0 → (∀ v : HeightOneSpectrum (𝓞 K), ∃ x y : v.adicCompletion K, x ^ 2 - algebraMap K (v.adicCompletion K) δ * y ^ 2 = algebraMap K (v.adicCompletion K) a) → ∃ x y : FiniteAdeleRing (𝓞 K) K, x ^ 2 - algebraMap K (FiniteAdeleRing (𝓞 K) K) δ * y ^ 2 = algebraMap K (FiniteAdeleRing (𝓞 K) K) a := by
  intro K _ _ δ a hδ ha hloc
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  have hev : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      Valued.v (algebraMap K (v.adicCompletion K) 2) = 1 ∧
      Valued.v (algebraMap K (v.adicCompletion K) δ) = 1 ∧
      Valued.v (algebraMap K (v.adicCompletion K) a) = 1 :=
    (eventually_valued_eq_one h2).and ((eventually_valued_eq_one hδ).and (eventually_valued_eq_one ha))
  classical
  let sol : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K × v.adicCompletion K := fun v =>
    if h : Valued.v (algebraMap K (v.adicCompletion K) 2) = 1 ∧
      Valued.v (algebraMap K (v.adicCompletion K) δ) = 1 ∧
      Valued.v (algebraMap K (v.adicCompletion K) a) = 1 then
      ((local_integral K v δ a h.1 h.2.1 h.2.2).choose, (local_integral K v δ a h.1 h.2.1 h.2.2).choose_spec.choose)
    else ((hloc v).choose, (hloc v).choose_spec.choose)
  have hsol : ∀ v, (sol v).1 ^ 2 - algebraMap K (v.adicCompletion K) δ * (sol v).2 ^ 2 =
      algebraMap K (v.adicCompletion K) a := by
    intro v
    simp only [sol]
    split_ifs with h
    · exact (local_integral K v δ a h.1 h.2.1 h.2.2).choose_spec.choose_spec.2.2
    · exact (hloc v).choose_spec.choose_spec
  have hint : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      (sol v).1 ∈ v.adicCompletionIntegers K ∧ (sol v).2 ∈ v.adicCompletionIntegers K := by
    filter_upwards [hev] with v h
    simp only [sol, dif_pos h]
    exact ⟨(local_integral K v δ a h.1 h.2.1 h.2.2).choose_spec.choose_spec.1,
      (local_integral K v δ a h.1 h.2.1 h.2.2).choose_spec.choose_spec.2.1⟩
  refine ⟨⟨fun v => (sol v).1, hint.mono fun _ h => h.1⟩, ⟨fun v => (sol v).2, hint.mono fun _ h => h.2⟩, ?_⟩
  refine FiniteAdeleRing.ext K fun v => ?_
  change (sol v).1 ^ 2 - algebraMap K (v.adicCompletion K) δ * (sol v).2 ^ 2 = algebraMap K (v.adicCompletion K) a
  exact hsol v

end GlobalTheory.AdelicQuadSol
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdeleSqSubMulSqStatement

section

@[expose] public section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.exists_finiteAdele_sq_sub_mul_sq_eq_of_local : ∀ (K : Type) [Field K] [NumberField K] (δ a : K), δ ≠ 0 → a ≠ 0 → (∀ v : HeightOneSpectrum (𝓞 K), ∃ x y : v.adicCompletion K, x ^ 2 - algebraMap K (v.adicCompletion K) δ * y ^ 2 = algebraMap K (v.adicCompletion K) a) → ∃ x y : FiniteAdeleRing (𝓞 K) K, x ^ 2 - algebraMap K (FiniteAdeleRing (𝓞 K) K) δ * y ^ 2 = algebraMap K (FiniteAdeleRing (𝓞 K) K) a := by
  first | (exact @GlobalTheory.AdelicQuadSol.exists_finiteAdele_sq_sub_mul_sq) | (exact GlobalTheory.AdelicQuadSol.exists_finiteAdele_sq_sub_mul_sq) | (intros; apply GlobalTheory.AdelicQuadSol.exists_finiteAdele_sq_sub_mul_sq  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealSubfieldNegativeTwoPlacesNormEverywher

section

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

open IsDedekindDomain

noncomputable section

namespace GlobalTheory.NormSign

theorem form_of_norm {K L : Type} [Field K] [NumberField K] [Field L] [Algebra K L]
    (hrank : Module.finrank K L = 2) (σ : L →+* L) (hσK : ∀ x : K, σ (algebraMap K L x) = algebraMap K L x)
    {t : L} {δ : K} (ht0 : t ≠ 0) (hσt : σ t = -t) (htt : t * t = algebraMap K L δ)
    (v : HeightOneSpectrum (𝓞 K)) {h : K} (h0 : h ≠ 0)
    (hz : ∃ z : v.adicCompletion K ⊗[K] L, Algebra.norm (v.adicCompletion K) z = algebraMap K (v.adicCompletion K) h) :
    ∃ x y : v.adicCompletion K, x ^ 2 - algebraMap K (v.adicCompletion K) δ * y ^ 2 =
      algebraMap K (v.adicCompletion K) h := by
  have hli : LinearIndependent K ![(1 : L), t] := by
    rw [LinearIndependent.pair_iff]
    intro s c hsc
    by_cases hc : c = 0
    · subst hc
      simp only [zero_smul, add_zero, smul_eq_zero, one_ne_zero, or_false] at hsc
      exact ⟨hsc, rfl⟩
    · exfalso
      have ht : t = algebraMap K L (-s / c) := by
        rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hsc
        have hc' : algebraMap K L c ≠ 0 := (map_ne_zero _).2 hc
        rw [map_div₀, map_neg, eq_div_iff hc']
        linear_combination hsc
      have h2 : σ t = t := by rw [ht, hσK]
      rw [hσt] at h2
      have : (2 : L) * t = 0 := by linear_combination -h2
      rcases mul_eq_zero.1 this with h | h
      · have h2' : (2 : L) = algebraMap K L 2 := (map_ofNat (algebraMap K L) 2).symm
        rw [h2'] at h
        exact two_ne_zero ((map_eq_zero _).1 h)
      · exact ht0 h
  let e : Module.Basis (Fin 2) K L := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hrank])
  have e0 : e 0 = 1 := by simp [e]
  have e1 : e 1 * e 1 = algebraMap K L δ := by simp [e, htt]
  have hu : IsUnit (algebraMap K (v.adicCompletion K) h) := (map_ne_zero _).2 h0 |>.isUnit
  haveI : FiniteDimensional K L := Module.finite_of_finrank_pos (by omega)
  have hm : hu.unit ∈ GlobalTheory.QuadSymbol.normGroup K L (v.adicCompletion K) := by
    rw [GlobalTheory.QuadSymbol.mem_normGroup_iff]
    obtain ⟨z, hz⟩ := hz
    exact ⟨z, by rw [hz]; rfl⟩
  obtain ⟨x, y, hxy⟩ := (GlobalTheory.QuadSymbol.mem_normGroup_iff_form e e0 e1).1 hm
  exact ⟨x, y, by rw [← hxy]; rfl⟩

theorem exists_toAfP (K : Type) [Field K] [NumberField K] (p : ℕ) :
    ∃ Φ : FiniteAdeleRing (𝓞 K) K →+* AfP p ⊗[ℚ] K, ∀ k : K, Φ (algebraMap K _ k) = 1 ⊗ₜ k := by
  obtain ⟨ι, hι, -⟩ := GlobalTheory.AdeleBaseChange.exists_tensor_finiteAdele_equiv ℚ K
  obtain ⟨e, -⟩ := GlobalTheory.NormLevelCompare.exists_adele_equiv
  let g : FiniteAdeleRing (𝓞 ℚ) ℚ →ₐ[ℚ] AfP p :=
    ((AfP.restr p).comp (e : FiniteAdeleRing (𝓞 ℚ) ℚ →+* FiniteAdeleRing ℤ ℚ)).toRatAlgHom
  let m : FiniteAdeleRing (𝓞 ℚ) ℚ ⊗[ℚ] K →ₐ[ℚ] AfP p ⊗[ℚ] K :=
    Algebra.TensorProduct.map g (AlgHom.id ℚ K)
  refine ⟨m.toRingHom.comp ι.symm.toRingHom, fun k => ?_⟩
  have : ι.symm (algebraMap K _ k) = 1 ⊗ₜ k := by rw [← hι, RingEquiv.symm_apply_apply]
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, this]
  simp [m]

theorem exists_neg_two_norm_away : ∀ (M : Type) [Field M] [NumberField M] (σ : M →+* M), σ ≠ RingHom.id M → (∀ (φ : M →+* ℂ) (x : M), φ (σ x) = (starRingEnd ℂ) (φ x)) → ∀ ε ε' : M →+* ℂ, ε ≠ ε' → ε ≠ ComplexEmbedding.conjugate ε' → ∀ (p : ℕ) [Fact p.Prime], ∃ a : M, a ≠ 0 ∧ σ a = a ∧ (ε a).re < 0 ∧ (ε' a).re < 0 ∧ (∀ φ : M →+* ℂ, φ ≠ ε → φ ≠ ComplexEmbedding.conjugate ε → φ ≠ ε' → φ ≠ ComplexEmbedding.conjugate ε' → 0 < (φ a).re) ∧ ∃ u : (AfP p ⊗[ℚ] M)ˣ, (u : AfP p ⊗[ℚ] M) * Algebra.TensorProduct.map (AlgHom.id ℚ (AfP p)) σ.toRatAlgHom u = 1 ⊗ₜ a := by
  intro M _ _ σ hσ hconj ε ε' hεε' hεc p _
  have hinv : ∀ x, σ (σ x) = x := by
    intro x
    obtain ⟨φ⟩ : Nonempty (M →+* ℂ) := inferInstance
    apply φ.injective
    rw [hconj, hconj, Complex.conj_conj]
  let σe : M ≃ₐ[ℚ] M :=
    { σ.toRatAlgHom with invFun := σ, left_inv := hinv, right_inv := hinv }
  have hσe : ∀ x, σe x = σ x := fun _ => rfl
  have hσe2 : σe ^ 2 = 1 := by
    ext x; rw [pow_two, AlgEquiv.mul_apply, hσe, hσe, hinv]; rfl
  have hσe1 : σe ≠ 1 := by
    intro h; apply hσ; ext x
    have := congrArg (fun f : M ≃ₐ[ℚ] M => f x) h
    simpa [hσe] using this
  have hσinv : σe⁻¹ = σe := inv_eq_of_mul_eq_one_right (by rw [← pow_two, hσe2])
  let K := IntermediateField.fixedField (Subgroup.zpowers σe)
  have hmem : ∀ x : M, x ∈ K ↔ σ x = x := by
    intro x
    rw [IntermediateField.mem_fixedField_iff]
    constructor
    · intro h; exact h σe (Subgroup.mem_zpowers σe)
    · intro h f hf
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hf
      clear hf
      induction k using Int.induction_on with
      | zero => simp
      | succ n ih => rw [_root_.zpow_add_one, AlgEquiv.mul_apply, hσe, h, ih]
      | pred n ih => rw [_root_.zpow_sub_one, AlgEquiv.mul_apply, hσinv, hσe, h, ih]
  have hrank : Module.finrank K M = 2 := by
    rw [IntermediateField.finrank_fixedField_eq_card, Nat.card_zpowers]
    exact orderOf_eq_prime hσe2 hσe1
  have hσK : ∀ x : K, σ (algebraMap K M x) = algebraMap K M x := fun x => (hmem _).1 x.2
  obtain ⟨h, h0, hε, hε', hpos, hloc⟩ := GlobalTheory.T.exists_base_element_negative_at_two_embeddings K M hrank σ hσ hσK hconj ε ε' hεε' hεc
  obtain ⟨s, hs⟩ : ∃ s, σ s ≠ s := by
    by_contra hc; push_neg at hc; exact hσ (RingHom.ext hc)
  set t := s - σ s with ht
  have hσt : σ t = -t := by rw [ht, map_sub, hinv]; ring
  have ht0 : t ≠ 0 := sub_ne_zero.2 (Ne.symm hs)
  have htK : t * t ∈ K := (hmem _).2 (by rw [map_mul, hσt]; ring)
  let δ : K := ⟨t * t, htK⟩
  have htt : t * t = algebraMap K M δ := rfl
  have hδ0 : δ ≠ 0 := by
    intro hd; apply ht0
    have : t * t = 0 := by rw [htt, hd, map_zero]
    exact mul_self_eq_zero.1 this
  have hform := fun v => form_of_norm hrank σ hσK ht0 hσt htt v h0 (hloc v)
  obtain ⟨x, y, hxy⟩ := GlobalTheory.T.exists_finiteAdele_sq_sub_mul_sq_eq_of_local K δ h hδ0 h0 hform
  obtain ⟨Φ, hΦ⟩ := exists_toAfP K p
  let j : AfP p ⊗[ℚ] K →ₐ[ℚ] AfP p ⊗[ℚ] M :=
    Algebra.TensorProduct.map (AlgHom.id ℚ (AfP p)) (IsScalarTower.toAlgHom ℚ K M)
  let S : AfP p ⊗[ℚ] M →ₐ[ℚ] AfP p ⊗[ℚ] M :=
    Algebra.TensorProduct.map (AlgHom.id ℚ (AfP p)) σ.toRatAlgHom
  have hSj' : ∀ w, S (j w) = j w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a k =>
      show a ⊗ₜ σ (algebraMap K M k) = a ⊗ₜ algebraMap K M k
      rw [hσK]
    | add w w' hw hw' => rw [map_add (f := _), map_add (f := _), hw, hw']
  set X := j (Φ x) with hX
  set Y := j (Φ y) with hY
  set T : AfP p ⊗[ℚ] M := 1 ⊗ₜ t with hT
  have hST : S T = -T := by simp [S, T, hσt, TensorProduct.tmul_neg]
  have hTT : T * T = j (Φ (algebraMap K _ δ)) := by
    rw [hΦ, hT, Algebra.TensorProduct.tmul_mul_tmul, mul_one, htt]; simp [j]
  have hkey : (X + Y * T) * S (X + Y * T) = 1 ⊗ₜ (algebraMap K M h) := by
    rw [map_add (f := _), map_mul, hX, hY, hSj', hSj', hST]
    have : (j (Φ x) + j (Φ y) * T) * (j (Φ x) + j (Φ y) * -T) =
        j (Φ (x ^ 2 - algebraMap K _ δ * y ^ 2)) := by
      rw [map_sub, map_mul, map_pow, map_pow, map_sub, map_mul, map_pow, map_pow, ← hTT]; ring
    rw [this, hxy, hΦ]; simp [j]
  have hunit : IsUnit (X + Y * T) := by
    have ha : IsUnit ((1 : AfP p) ⊗ₜ[ℚ] (algebraMap K M h)) :=
      ((map_ne_zero (algebraMap K M)).2 h0).isUnit.map
        (Algebra.TensorProduct.includeRight : M →ₐ[ℚ] AfP p ⊗[ℚ] M)
    rw [← hkey] at ha
    exact isUnit_of_mul_isUnit_left ha
  exact ⟨algebraMap K M h, (map_ne_zero _).2 h0, hσK h, hε, hε', hpos, hunit.unit, hkey⟩

end GlobalTheory.NormSign
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealSubfieldNegativeTwoPlacesNormEverywherStatement

section

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.exists_realSubfield_negative_twoPlaces_normEverywhere : ∀ (M : Type) [Field M] [NumberField M] (σ : M →+* M), σ ≠ RingHom.id M → (∀ (φ : M →+* ℂ) (x : M), φ (σ x) = (starRingEnd ℂ) (φ x)) → ∀ ε ε' : M →+* ℂ, ε ≠ ε' → ε ≠ ComplexEmbedding.conjugate ε' → ∀ (p : ℕ) [Fact p.Prime], ∃ a : M, a ≠ 0 ∧ σ a = a ∧ (ε a).re < 0 ∧ (ε' a).re < 0 ∧ (∀ φ : M →+* ℂ, φ ≠ ε → φ ≠ ComplexEmbedding.conjugate ε → φ ≠ ε' → φ ≠ ComplexEmbedding.conjugate ε' → 0 < (φ a).re) ∧ ∃ u : (AfP p ⊗[ℚ] M)ˣ, (u : AfP p ⊗[ℚ] M) * Algebra.TensorProduct.map (AlgHom.id ℚ (AfP p)) σ.toRatAlgHom u = 1 ⊗ₜ a := by
  first | (exact @GlobalTheory.NormSign.exists_neg_two_norm_away) | (exact GlobalTheory.NormSign.exists_neg_two_norm_away) | (intros; apply GlobalTheory.NormSign.exists_neg_two_norm_away <;> assumption)
end
end
