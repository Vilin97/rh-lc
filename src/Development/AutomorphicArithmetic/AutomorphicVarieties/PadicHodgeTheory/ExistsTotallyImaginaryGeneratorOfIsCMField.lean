module

public import Mathlib.NumberTheory.NumberField.CMField
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsRealSplitPrimitiveElementPadicFiniteExt
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsCMOfConj

section

@[expose] public section

theorem UpperTheory.Reformulated.B.Qh8.isCM_of_conj :
    ∀ (K : Type) [inst : Field K] [inst_1 : NumberField K]
    [NumberField.IsTotallyComplex K],
    (∀ (x : K), ∃ (y : K), ∀ (φ : K →+* ℂ), (φ : K → ℂ) y = (starRingEnd ℂ : ℂ → ℂ) ((φ : K → ℂ) x)) →
      NumberField.IsCMField K := by
  intro K _ _ _ h
  choose c hc using h
  let φ₀ : K →+* ℂ := Classical.choice (inferInstance : Nonempty _)
  obtain ⟨x, hx⟩ : ∃ x : K, starRingEnd ℂ (φ₀ x) ≠ φ₀ x := by
    by_contra hne
    apply NumberField.IsTotallyComplex.complexEmbedding_not_isReal φ₀
    rw [NumberField.ComplexEmbedding.isReal_iff]
    ext z
    rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
    by_contra hz
    exact hne ⟨z, hz⟩
  have hanti : ∀ (z : K) (φ : K →+* ℂ), starRingEnd ℂ (φ (z - c z)) = -φ (z - c z) := by
    intro z φ
    simp [hc]
  obtain ⟨d, hd0, hd⟩ : ∃ d : K, d ≠ 0 ∧ ∀ φ : K →+* ℂ, starRingEnd ℂ (φ d) = -φ d := by
    refine ⟨x - c x, fun h0 => hx ?_, hanti x⟩
    rw [← hc, ← sub_eq_zero.mp h0]
  have hli : LinearIndependent (NumberField.maximalRealSubfield K) ![(1 : K), d] := by
    rw [LinearIndependent.pair_iff]
    rintro ⟨s, hs⟩ ⟨t, ht⟩ hst
    have h1 : s * 1 + t * d = 0 := hst
    have h2 := congrArg φ₀ h1
    have h3 := congrArg (starRingEnd ℂ) h2
    have hs' : starRingEnd ℂ (φ₀ s) = φ₀ s := hs φ₀
    have ht' : starRingEnd ℂ (φ₀ t) = φ₀ t := ht φ₀
    simp only [map_add (f := _), map_mul, map_one, map_zero, hs', ht', hd] at h2 h3
    have hs0 : s = 0 := by
      apply φ₀.injective
      rw [map_zero]
      linear_combination (h2 + h3) / 2
    have ht0 : t = 0 := by
      rw [hs0, zero_mul, zero_add] at h1
      exact (mul_eq_zero.mp h1).resolve_right hd0
    exact ⟨Subtype.ext hs0, Subtype.ext ht0⟩
  have hsp : ⊤ ≤ Submodule.span (NumberField.maximalRealSubfield K)
      (Set.range ![(1 : K), d]) := by
    intro z _
    have ha : (z + c z) / 2 ∈ NumberField.maximalRealSubfield K := by
      intro φ
      change starRingEnd ℂ _ = _
      simp [hc, add_comm, map_ofNat]
    have hb : (z - c z) / (2 * d) ∈ NumberField.maximalRealSubfield K := by
      intro φ
      change starRingEnd ℂ _ = _
      rw [map_div₀, map_div₀, hanti, map_mul, map_mul, hd, map_ofNat, map_ofNat, mul_neg,
        neg_div_neg_eq]
    rw [Matrix.range_cons_cons_empty, Submodule.mem_span_pair]
    refine ⟨⟨_, ha⟩, ⟨_, hb⟩, ?_⟩
    change (z + c z) / 2 * 1 + (z - c z) / (2 * d) * d = z
    field_simp
    ring
  have hfin : Module.finrank (NumberField.maximalRealSubfield K) K = 2 := by
    rw [Module.finrank_eq_card_basis (Module.Basis.mk hli hsp), Fintype.card_fin]
  haveI : Algebra.IsQuadraticExtension (NumberField.maximalRealSubfield K) K :=
    { finrank_eq_two' := hfin }
  exact ⟨⟩
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsTotallyImaginaryGeneratorOfIsCMField

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc NumberField

private theorem isCM_of_conj (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K]
    (h : ∀ x : K, ∃ y : K, ∀ φ : K →+* ℂ, φ y = starRingEnd ℂ (φ x)) : IsCMField K :=
  _root_.UpperTheory.Reformulated.B.Qh8.isCM_of_conj K h

open Polynomial in
private theorem exists_sqrt (l : ℕ) [hl : Fact l.Prime] :
    ∃ d : ℚ_[l], d ^ 2 = 1 - 4 * (l : ℚ_[l]) := by
  have h3 : ‖((l : ℕ) : ℤ_[l])‖ < 1 := PadicInt.norm_natCast_lt_one_iff.2 dvd_rfl
  obtain ⟨z, hz, -⟩ := hensels_lemma (p := l) (R := ℤ_[l]) (F := X ^ 2 - X + C (l : ℤ_[l])) (a := 0) (by
    have e1 : aeval (0 : ℤ_[l]) (X ^ 2 - X + C (l : ℤ_[l]) : ℤ_[l][X]) = ((l : ℕ) : ℤ_[l]) := by
      simp
    have e2 : aeval (0 : ℤ_[l]) (derivative (X ^ 2 - X + C (l : ℤ_[l]) : ℤ_[l][X])) = -1 := by
      simp
    rw [e1, e2, norm_neg, norm_one, one_pow]
    exact h3)
  have h4 : z ^ 2 - z + (l : ℤ_[l]) = 0 := by simpa using hz
  have h5 : (z : ℚ_[l]) ^ 2 - z + (l : ℚ_[l]) = 0 := by
    have := congrArg (fun x : ℤ_[l] => (x : ℚ_[l])) h4
    simpa using this
  exact ⟨2 * z - 1, by linear_combination 4 * h5⟩

private theorem conj_of_sq (w : ℂ) (r : ℝ) (hr : r < 0) (h : w ^ 2 = r) : starRingEnd ℂ w = -w := by
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp [pow_two] at h1 h2
  have h3 : w.re = 0 := by
    by_contra h0
    have : w.im = 0 := by
      have : w.re * w.im = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left h0
    rw [this] at h1
    nlinarith [mul_self_nonneg w.re]
  apply Complex.ext <;> simp [h3]

open Polynomial in
private theorem conj_of_root (g : ℚ[X]) (hg : g ≠ 0) (hs : (g.map (algebraMap ℚ ℝ)).Splits) (w : ℂ)
    (h : aeval w g = 0) : starRingEnd ℂ w = w := by
  have h1 : g.map (algebraMap ℚ ℝ) ≠ 0 := Polynomial.map_ne_zero hg
  have h2 : w ∈ ((g.map (algebraMap ℚ ℝ)).map (algebraMap ℝ ℂ)).roots := by
    rw [mem_roots (Polynomial.map_ne_zero h1), IsRoot.def, eval_map_algebraMap, aeval_map_algebraMap]
    exact h
  rw [hs.roots_map] at h2
  obtain ⟨r, -, rfl⟩ := Multiset.mem_map.1 h2
  exact Complex.conj_ofReal r

theorem UpperTheory.exists_totally_imaginary_generator_of_isCMField :
    ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l), ∃ (M : Type) (_ : Field M) (_ : NumberField M) (_ : IsCMField M) (f : M →+* Om l), IntermediateField.adjoin ℚ_[l] (Set.range f) = K.1 ∧ ∃ (δ : M) (d : ℚ_[l]), δ ≠ 0 ∧ f δ = algebraMap ℚ_[l] (Om l) d ∧ ∀ φ : M →+* ℂ, starRingEnd ℂ (φ δ) = -φ δ := by
  intro l hl K
  obtain ⟨β, g, hgm, hgs, hβ, hK⟩ := UpperTheory.exists_real_split_primitive_element_padic_finite_ext l K
  obtain ⟨d, hd⟩ := exists_sqrt l
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl.out.one_lt.le
  set D : Om l := algebraMap ℚ_[l] (Om l) d with hD
  have hD2 : D ^ 2 = 1 - 4 * (l : Om l) := by
    rw [hD, ← map_pow, hd]; simp [map_ofNat]
  have hβi : IsIntegral ℚ β := ⟨g, hgm, hβ⟩
  have hDi : IsIntegral ℚ D := by
    apply IsIntegral.of_pow two_pos
    rw [hD2]
    have : (1 - 4 * (l : Om l)) = algebraMap ℚ (Om l) (1 - 4 * l) := by simp
    rw [this]
    exact isIntegral_algebraMap
  let M : IntermediateField ℚ (Om l) := IntermediateField.adjoin ℚ {β, D}
  have hfd : FiniteDimensional ℚ M := IntermediateField.finiteDimensional_adjoin (by
    rintro x (rfl | rfl)
    · exact hβi
    · exact hDi)
  have hNF : NumberField M := { to_charZero := inferInstance, to_finiteDimensional := hfd }
  let b : M := ⟨β, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let δ : M := ⟨D, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  have hδ2 : δ ^ 2 = 1 - 4 * (l : M) := by
    apply (algebraMap M (Om l)).injective
    rw [map_pow, map_sub, map_mul, map_one, map_ofNat, map_natCast]
    exact hD2
  have hb : Polynomial.aeval b g = 0 := by
    apply (algebraMap M (Om l)).injective
    rw [← Polynomial.aeval_algebraMap_apply, map_zero]
    exact hβ
  have hδφ2 : ∀ φ : M →+* ℂ, φ δ ^ 2 = ((1 - 4 * l : ℝ) : ℂ) := fun φ => by
    rw [← map_pow, hδ2]; simp [map_ofNat]
  have hδc : ∀ φ : M →+* ℂ, starRingEnd ℂ (φ δ) = -φ δ := fun φ =>
    conj_of_sq _ _ (by linarith) (hδφ2 φ)
  have hδ0 : ∀ φ : M →+* ℂ, φ δ ≠ 0 := fun φ h => by
    have := hδφ2 φ
    rw [h, zero_pow two_ne_zero] at this
    have : (1 - 4 * l : ℝ) = 0 := by exact_mod_cast this.symm
    linarith
  have hbc : ∀ φ : M →+* ℂ, starRingEnd ℂ (φ b) = φ b := fun φ => by
    refine conj_of_root g hgm.ne_zero hgs _ ?_
    have := Polynomial.aeval_algHom_apply φ.toRatAlgHom b g
    rw [hb, map_zero] at this
    exact this
  have htc : IsTotallyComplex M := ⟨fun w => by
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    intro h
    have h1 : starRingEnd ℂ (w.embedding δ) = w.embedding δ := RingHom.congr_fun h δ
    rw [hδc] at h1
    exact hδ0 w.embedding (by linear_combination (-1 / 2 : ℂ) * h1)⟩
  have hCM : IsCMField M := by
    refine isCM_of_conj _ ?_
    rintro ⟨x, hx⟩
    induction hx using IntermediateField.adjoin_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact ⟨b, fun φ => (hbc φ).symm⟩
      · exact ⟨-δ, fun φ => by rw [map_neg]; exact (hδc φ).symm⟩
    | algebraMap a =>
      refine ⟨algebraMap ℚ M a, fun φ => ?_⟩
      change φ (algebraMap ℚ M a) = starRingEnd ℂ (φ (algebraMap ℚ M a))
      simp
    | add x y hx hy ihx ihy =>
      obtain ⟨a, ha⟩ := ihx
      obtain ⟨b, hb⟩ := ihy
      refine ⟨a + b, fun φ => ?_⟩
      rw [map_add (f := _), ha, hb, ← map_add (f := _), ← map_add (f := _)]
      rfl
    | inv x hx ihx =>
      obtain ⟨a, ha⟩ := ihx
      refine ⟨a⁻¹, fun φ => ?_⟩
      rw [map_inv₀, ha, ← map_inv₀, ← map_inv₀]
      rfl
    | mul x y hx hy ihx ihy =>
      obtain ⟨a, ha⟩ := ihx
      obtain ⟨b, hb⟩ := ihy
      refine ⟨a * b, fun φ => ?_⟩
      rw [map_mul, ha, hb, ← map_mul, ← map_mul]
      rfl
  refine ⟨M, inferInstance, hNF, hCM, algebraMap M (Om l), ?_, δ, d, ?_, rfl, hδc⟩
  · apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨x, rfl⟩
      have hβK : β ∈ K.1 := hK ▸ IntermediateField.mem_adjoin_simple_self _ β
      have hle : M.toSubfield ≤ K.1.toSubfield := by
        rw [IntermediateField.adjoin_toSubfield, Subfield.closure_le]
        rintro y (⟨q, rfl⟩ | rfl | rfl)
        · simp
        · exact hβK
        · exact K.1.algebraMap_mem d
      exact hle x.2
    · rw [← hK, IntermediateField.adjoin_le_iff]
      rintro _ rfl
      exact IntermediateField.subset_adjoin _ _ ⟨b, rfl⟩
  · intro h
    have φ : M →+* ℂ := Classical.choice inferInstance
    exact hδ0 φ (by rw [h, map_zero])
end
end
