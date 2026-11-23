module

public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGDefs
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import ReciprocityTheory.NeutralLocalFields.HilbertClassField
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModCMPoint
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModFrobSer
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGBasic
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModKronPt
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModLatTau
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Finsupp.Pointwise
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.NeutralLocalFields.HilbertClassField
public import Mathlib.NumberTheory.NumberField.Norm
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModVanish
public import Mathlib.RingTheory.RootsOfUnity.Minpoly

-- Source module: ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQuadInt

section

@[expose] public section

noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField

namespace ReciprocityTheory.ChartRestriction.L1

theorem omegaK_eq (d : ℕ) : omegaK d = (1 + sqD d) / 2 := by
  unfold omegaK sqD
  rfl

theorem KQ_mem_iff (d : ℕ) (z : ℂ) : z ∈ KQ d ↔ ∃ u v : ℚ, z = u + v * sqD d := by
  constructor
  · intro hz
    have h1 : z ∈ (KQ d).toSubalgebra := hz
    clear hz
    unfold KQ at h1
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (sqD_isIntegral d).isAlgebraic] at h1
    induction h1 using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      exact ⟨0, 1, by simp [hx]⟩
    | algebraMap r => exact ⟨r, 0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨u, v, rfl⟩ := hx
      obtain ⟨u', v', rfl⟩ := hy
      exact ⟨u + u', v + v', by push_cast; ring⟩
    | mul x y _ _ hx hy =>
      obtain ⟨u, v, rfl⟩ := hx
      obtain ⟨u', v', rfl⟩ := hy
      refine ⟨u * u' - d * v * v', u * v' + v * u', ?_⟩
      have hs := sqD_sq d
      push_cast
      linear_combination (v * v') * hs
  · rintro ⟨u, v, rfl⟩
    have hs : sqD d ∈ KQ d := IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _)
    refine add_mem ?_ (mul_mem ?_ hs)
    · simp
    · simp

theorem ratInt_of_isIntegral {q : ℚ} (h : IsIntegral ℤ (q : ℂ)) : ∃ n : ℤ, q = n := by
  have h1 : IsIntegral ℤ q := by
    rw [← isIntegral_algHom_iff (algebraMap ℚ ℂ).toIntAlgHom (algebraMap ℚ ℂ).injective]
    simpa using h
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp h1
  exact ⟨n, by rw [← hn]; simp⟩

theorem conj_sqD (d : ℕ) : (starRingEnd ℂ) (sqD d) = - sqD d := by
  unfold sqD
  simp

theorem quadInt {d : ℕ} (hsf : Squarefree d) (hd : d % 4 = 3) (x : 𝓞 (KQ d)) :
    ∃ a b : ℤ, (((x : KQ d) : ℂ)) = a + b * omegaK d := by
  have hx : IsIntegral ℤ (((x : KQ d) : ℂ)) :=
    (NumberField.RingOfIntegers.isIntegral_coe x).map (IntermediateField.val (KQ d)).toRingHom.toIntAlgHom
  obtain ⟨u, v, huv⟩ := (KQ_mem_iff d _).mp (x : KQ d).2
  rw [huv] at hx
  have hc : IsIntegral ℤ ((starRingEnd ℂ) ((u : ℂ) + v * sqD d)) := hx.map (starRingEnd ℂ).toIntAlgHom
  rw [map_add (f := _), map_mul, conj_sqD, map_ratCast, map_ratCast] at hc
  have hs := sqD_sq d
  obtain ⟨A, hA⟩ := ratInt_of_isIntegral (q := 2 * u) (by
    have e : (((2 * u : ℚ)) : ℂ) = ((u : ℂ) + v * sqD d) + ((u : ℂ) + v * -sqD d) := by
      push_cast; ring
    rw [e]; exact hx.add hc)
  obtain ⟨N, hN⟩ := ratInt_of_isIntegral (q := u ^ 2 + d * v ^ 2) (by
    have e : (((u ^ 2 + d * v ^ 2 : ℚ)) : ℂ) = ((u : ℂ) + v * sqD d) * ((u : ℂ) + v * -sqD d) := by
      push_cast; linear_combination ((v : ℂ) ^ 2) * hs
    rw [e]; exact hx.mul hc)

  have hd0 : (d : ℤ) ≠ 0 := by omega
  obtain ⟨k, hk⟩ : ∃ k : ℤ, (d : ℚ) * (2 * v) = k := by
    set r : ℚ := (d : ℚ) * (2 * v) with hr
    have hr2 : r ^ 2 = ((d * (4 * N - A ^ 2) : ℤ) : ℚ) := by
      push_cast
      rw [← hN, ← hA]; ring
    have hden : r.den = 1 := by
      have := congrArg Rat.den hr2
      rw [Rat.den_pow, Rat.den_intCast] at this
      exact (Nat.pow_eq_one.mp this).resolve_right (by norm_num)
    exact ⟨r.num, (Rat.coe_int_num_of_den_eq_one hden).symm⟩
  have hk2 : k ^ 2 = d * (4 * N - A ^ 2) := by
    have : ((k ^ 2 : ℤ) : ℚ) = ((d * (4 * N - A ^ 2) : ℤ) : ℚ) := by
      push_cast
      rw [← hk, ← hN, ← hA]; ring
    exact_mod_cast this
  have hdk : (d : ℤ) ∣ k := by
    have hsq : Squarefree (d : ℤ) := Int.squarefree_natCast.mpr hsf
    exact (hsq.dvd_pow_iff_dvd (n := 2) (by norm_num)).mp ⟨_, hk2⟩
  obtain ⟨B, rfl⟩ := hdk
  have hB : 2 * v = B := by
    have : (d : ℚ) * (2 * v) = (d : ℚ) * B := by rw [hk]; push_cast; ring
    exact mul_left_cancel₀ (by exact_mod_cast hd0) this

  have h4 : A ^ 2 + (d : ℤ) * B ^ 2 = 4 * N := by
    have : ((A ^ 2 + (d : ℤ) * B ^ 2 : ℤ) : ℚ) = ((4 * N : ℤ) : ℚ) := by
      push_cast
      rw [← hN, ← hA, ← hB]; ring
    exact_mod_cast this
  obtain ⟨c, hc3⟩ : ∃ c : ℤ, (d : ℤ) = 4 * c + 3 := ⟨(d / 4 : ℕ), by omega⟩
  obtain ⟨a, ha | ha⟩ := Int.even_or_odd' A <;> obtain ⟨b, hb | hb⟩ := Int.even_or_odd' B
  · refine ⟨a - b, B, ?_⟩
    rw [omegaK_eq]
    have e1 : (u : ℂ) = ((A : ℚ) : ℂ) / 2 := by rw [← hA]; push_cast; ring
    have e2 : (v : ℂ) = ((B : ℚ) : ℂ) / 2 := by rw [← hB]; push_cast; ring
    rw [huv, e1, e2, ha, hb]; push_cast; ring
  · exfalso
    rw [ha, hb, hc3] at h4
    have : 4 * N = 4 * (a ^ 2 + 4 * c * b ^ 2 + 4 * c * b + c + 3 * b ^ 2 + 3 * b) + 3 := by
      rw [← h4]; ring
    omega
  · exfalso
    rw [ha, hb, hc3] at h4
    have : 4 * N = 4 * (a ^ 2 + a + 4 * c * b ^ 2 + 3 * b ^ 2) + 1 := by
      rw [← h4]; ring
    omega
  · refine ⟨a - b, B, ?_⟩
    rw [omegaK_eq]
    have e1 : (u : ℂ) = ((A : ℚ) : ℂ) / 2 := by rw [← hA]; push_cast; ring
    have e2 : (v : ℂ) = ((B : ℚ) : ℂ) / 2 := by rw [← hB]; push_cast; ring
    rw [huv, e1, e2, ha, hb]; push_cast; ring

end ReciprocityTheory.ChartRestriction.L1
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModPrincNorm

section

@[expose] public section

noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField

namespace ReciprocityTheory.ChartRestriction.L1

theorem sqD_indep {d : ℕ} (hd : 0 < d) (u v : ℚ) (h : (u : ℂ) + v * sqD d = 0) : u = 0 ∧ v = 0 := by
  have hs : Real.sqrt d ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hd)).ne'
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [sqD] at hre him
  exact ⟨hre, him.resolve_right (by
    intro h0
    apply hs
    simpa using h0)⟩

theorem sqK_li {d : ℕ} (hd : 0 < d) : LinearIndependent ℚ ![(1 : KQ d), sqK d] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  apply sqD_indep hd
  have := congrArg (fun z : KQ d => (z : ℂ)) h
  simpa [sqK, Algebra.smul_def] using this

theorem sqK_decomp {d : ℕ} (z : KQ d) (p q : ℚ) (h : (z : ℂ) = p + q * sqD d) :
    z = p • (1 : KQ d) + q • sqK d := by
  apply Subtype.ext
  simp [sqK, Algebra.smul_def, h]

theorem sqK_span {d : ℕ} : ⊤ ≤ Submodule.span ℚ (Set.range ![(1 : KQ d), sqK d]) := by
  intro z _
  obtain ⟨u, v, h⟩ := (KQ_mem_iff d z).1 z.2
  rw [sqK_decomp z u v h]
  refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))

def bKQ {d : ℕ} (hd : 0 < d) : Module.Basis (Fin 2) ℚ (KQ d) := Module.Basis.mk (sqK_li hd) sqK_span

theorem sqK_mul_self (d : ℕ) : sqK d * sqK d = -(d : KQ d) := by
  apply Subtype.ext
  have := sqD_sq d
  simp [sqK, ← this, sq]

theorem norm_KQ {d : ℕ} (hd : 0 < d) (z : KQ d) (p q : ℚ) (h : (z : ℂ) = p + q * sqD d) :
    Algebra.norm ℚ z = p ^ 2 + d * q ^ 2 := by
  have h0 : bKQ hd 0 = 1 := by simp [bKQ]
  have h1 : bKQ hd 1 = sqK d := by simp [bKQ]
  have hz := sqK_decomp z p q h
  have e0 : z * bKQ hd 0 = p • bKQ hd 0 + q • bKQ hd 1 := by
    rw [h0, h1, mul_one]; exact hz
  have e1 : z * bKQ hd 1 = (-(d : ℚ) * q) • bKQ hd 0 + p • bKQ hd 1 := by
    rw [h0, h1, hz, add_mul, smul_mul_assoc, smul_mul_assoc, sqK_mul_self, one_mul]
    simp only [Algebra.smul_def, mul_one]
    push_cast
    ring
  rw [Algebra.norm_eq_matrix_det (bKQ hd), Matrix.det_fin_two]
  simp only [Algebra.leftMulMatrix_eq_repr_mul, e0, e1, map_add (f := _), map_smul, Module.Basis.repr_self]
  simp
  ring

theorem absNorm_span {d : ℕ} (hsf : Squarefree d) (hd : d % 4 = 3) (x : 𝓞 (KQ d)) (a b : ℤ)
    (h : (((x : KQ d) : ℂ)) = a + b * omegaK d) :
    4 * (Ideal.absNorm (Ideal.span {x}) : ℤ) = 4 * a ^ 2 + 4 * a * b + b ^ 2 * (1 + d) := by
  have hd0 : 0 < d := by omega
  have hn := norm_KQ hd0 (x : KQ d) (a + b / 2) (b / 2) (by
    rw [h]; simp only [omegaK, sqD]; push_cast; ring)
  rw [← Algebra.coe_norm_int] at hn
  have hn' : 4 * Algebra.norm ℤ x = 4 * a ^ 2 + 4 * a * b + b ^ 2 * (1 + d) := by
    have : (4 : ℚ) * (Algebra.norm ℤ x : ℚ) = 4 * a ^ 2 + 4 * a * b + b ^ 2 * (1 + d) := by
      rw [hn]; ring
    exact_mod_cast this
  have hpos : 0 ≤ Algebra.norm ℤ x := by
    have : 0 ≤ 4 * Algebra.norm ℤ x := by
      rw [hn']
      have : 4 * a ^ 2 + 4 * a * b + b ^ 2 * (1 + (d : ℤ)) = (2 * a + b) ^ 2 + d * b ^ 2 := by ring
      rw [this]; positivity
    omega
  rw [Ideal.absNorm_span_singleton, Int.natAbs_of_nonneg hpos, hn']

theorem princ_form {d : ℕ} (hsf : Squarefree d) (hd : d % 4 = 3) (v : HeightOneSpectrum (𝓞 (KQ d)))
    (hv : ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩ = 1) :
    ∃ a b : ℤ, 4 * (Nat.card (𝓞 (KQ d) ⧸ v.asIdeal) : ℤ) = 4 * a ^ 2 + 4 * a * b + b ^ 2 * (1 + d) := by
  rw [ClassGroup.mk0_eq_one_iff] at hv
  obtain ⟨x, hx⟩ := hv.principal
  obtain ⟨a, b, hab⟩ := quadInt hsf hd x
  refine ⟨a, b, ?_⟩
  rw [← absNorm_span hsf hd x a b hab, Ideal.absNorm_apply, Submodule.cardQuot_apply, hx]

end ReciprocityTheory.ChartRestriction.L1
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModFrobCong

section

@[expose] public section

noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField

namespace ReciprocityTheory.ChartRestriction.L1

theorem natCard_mem {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {A : ValuationSubring Ω}
    {v : HeightOneSpectrum (𝓞 E)} (h : LiesAbove A v) :
    ((Nat.card (𝓞 E ⧸ v.asIdeal) : ℕ) : Ω) ∈ A.nonunits := by
  have hmem : ((Nat.card (𝓞 E ⧸ v.asIdeal) : ℕ) : 𝓞 E) ∈ v.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    rcases finite_or_infinite (𝓞 E ⧸ v.asIdeal) with hf | hf
    · have := Fintype.ofFinite (𝓞 E ⧸ v.asIdeal)
      rw [Nat.card_eq_fintype_card]
      exact Nat.cast_card_eq_zero _
    · rw [Nat.card_eq_zero_of_infinite, Nat.cast_zero]
  have h2 := (h _).mpr hmem
  simpa using h2

theorem frobCong {d : ℕ} {L : PeriodPair} (hsf : Squarefree d) (hd : d % 4 = 3) (hL : HasCMBy d L)
    (x : Om d) (hx : (x : ℂ) = jInv L) (A : ValuationSubring (Om d)) (v : HeightOneSpectrum (𝓞 (KQ d)))
    (hA : LiesAbove A v) (hp : (Nat.card (𝓞 (KQ d) ⧸ v.asIdeal)).Prime)
    (hv : ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩ = 1) :
    x ^ Nat.card (𝓞 (KQ d) ⧸ v.asIdeal) - x ∈ A.nonunits := by
  set N := Nat.card (𝓞 (KQ d) ⧸ v.asIdeal) with hN
  have hd0 : 0 < d := by omega
  obtain ⟨c, τ, hτ⟩ := latTau L
  have hj : jInv L = jT τ := jInv_eq_jT hτ
  obtain ⟨a, b, hab⟩ := princ_form hsf hd v hv
  obtain ⟨A', B', C', D', h1, h2, h3⟩ := cmPoint hd0 hL hτ a b
  have hG : Gm N τ = 0 := by
    apply Gm_vanish hp.pos τ A' B' C' D'
    · linarith
    · rw [← h1, h2]
      ring
  obtain ⟨r, hr, hrel⟩ := kronPt hp hG
  obtain ⟨r0, hr0m, hr0⟩ := one_sub_zeta_pow hp
  have hzint : IsIntegral ℤ (zetaC N) := (zetaC_isPrimitiveRoot hp.ne_zero).isIntegral hp.pos
  have hr0int : IsIntegral ℤ r0 := by
    have hle : Rm N ≤ (integralClosure ℤ ℂ).toSubring :=
      Subring.closure_le.mpr (Set.singleton_subset_iff.mpr hzint)
    exact hle hr0m
  obtain ⟨r', hr'c, hr'i⟩ := exists_Om d hr
  obtain ⟨r0', hr0'c, hr0'i⟩ := exists_Om d hr0int
  have hC : (((x ^ N - x) ^ (2 * N) : Om d) : ℂ) = (((N : Om d) * r0' * r' ^ N : Om d) : ℂ) := by
    push_cast
    rw [hr'c, hr0'c, hx, hj, pow_mul, hrel, mul_pow, hr0]
  have hEq : (x ^ N - x) ^ (2 * N) = (N : Om d) * r0' * r' ^ N := Subtype.ext hC
  have hNu := natCard_mem hA
  rw [ValuationSubring.mem_nonunits_iff] at hNu ⊢
  have hv1 : A.valuation r0' ≤ 1 := (A.valuation_le_one_iff _).mpr (mem_of_isIntegral A hr0'i)
  have hv2 : A.valuation r' ≤ 1 := (A.valuation_le_one_iff _).mpr (mem_of_isIntegral A hr'i)
  have hv3 : A.valuation ((x ^ N - x) ^ (2 * N)) < 1 := by
    rw [hEq, map_mul, map_mul, map_pow]
    exact mul_lt_one_of_lt_of_le (mul_lt_one_of_lt_of_le hNu hv1) (pow_le_one' hv2 _)
  by_contra hcon
  rw [map_pow] at hv3
  exact absurd hv3 (not_lt.mpr (one_le_pow_of_one_le' (not_lt.mp hcon) _))

end ReciprocityTheory.ChartRestriction.L1
end
end
end
