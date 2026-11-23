module

public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.TwistedSlicesSquareIntegrable
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
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
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AbsPowOneNotIsAlgRat
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.Basic.Real.Basic
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PStringStepD
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Algebra.Order.Star.Int
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PStringStepC

-- Source module: Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.NotIsUnitaryAbsPow

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.LFun GlobalTheory.CuspRep GlobalTheory.HeckeGal.Model

namespace GlobalTheory.Published.JacquetShalikaModel

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]


open NumberField IsDedekindDomain in
variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
omit [_root_.NumberField.IsTotallyComplex E] in
theorem _root_.GlobalTheory.Published.JacquetShalikaModel.infinite_places : Infinite (HeightOneSpectrum (𝓞 E)) := by
  classical
  by_contra h
  rw [not_infinite_iff_finite] at h
  have hfin : (Set.range fun P : HeightOneSpectrum (𝓞 E) =>
      Ideal.comap (algebraMap ℤ (𝓞 E)) P.asIdeal).Finite := Set.finite_range _
  apply Nat.infinite_setOf_prime
  have hinj : Set.InjOn (fun p : ℕ => Ideal.span {(p : ℤ)}) {p | p.Prime} := by
    intro p _ q _ hpq
    have := Ideal.span_singleton_eq_span_singleton.mp hpq
    rw [Int.associated_iff_natAbs] at this
    simpa using this
  refine Set.Finite.of_finite_image (hfin.subset ?_) hinj
  rintro _ ⟨p, hp, rfl⟩
  haveI hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  obtain ⟨Q, hQ, hlies⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) (Ideal.span {(p : ℤ)})
  have hcomap : Ideal.comap (algebraMap ℤ (𝓞 E)) Q = Ideal.span {(p : ℤ)} :=
    (hlies.over).symm
  have hne : Q ≠ ⊥ := by
    rintro rfl
    have hmem : (p : ℤ) ∈ Ideal.comap (algebraMap ℤ (𝓞 E)) (⊥ : Ideal (𝓞 E)) :=
      hcomap ▸ Ideal.subset_span rfl
    rw [Ideal.mem_comap, Ideal.mem_bot, map_natCast, Nat.cast_eq_zero] at hmem
    exact hp.ne_zero hmem
  exact ⟨⟨Q, hQ.isPrime, hne⟩, hcomap⟩

end GlobalTheory.Published.JacquetShalikaModel
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PStringStepA

section

@[expose] public section

namespace PositivityTheory.Rg.Rs.StrStepA

theorem adjacent (c₁ c₂ : ℝ) (d₁ d₂ : ℕ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (S : Set ℝ)
    (hS : ∀ x, x ∈ S ↔ (∃ i : ℕ, i < d₁ ∧ x = c₁ + ((d₁ : ℝ) - 1) / 2 - i) ∨
      ∃ j : ℕ, j < d₂ ∧ x = c₂ + ((d₂ : ℝ) - 1) / 2 - j)
    (hdisj : ∀ i j : ℕ, i < d₁ → j < d₂ → c₁ + ((d₁ : ℝ) - 1) / 2 - i ≠ c₂ + ((d₂ : ℝ) - 1) / 2 - j)
    (hint : ∀ x ∈ S, ∀ y ∈ S, ∃ n : ℤ, x - y = n)
    (hneg : ∀ x ∈ S, -x ∈ S) (hP : ∀ u ∈ S, 1 ≤ u → u - 1 ∈ S) (hc : c₁ < c₂) :
    c₂ - c₁ = ((d₁ : ℝ) + d₂) / 2 := by
  set e₁ : ℝ := ((d₁ : ℝ) - 1) / 2 with he₁
  set e₂ : ℝ := ((d₂ : ℝ) - 1) / 2 with he₂
  have hd₁' : (1 : ℝ) ≤ d₁ := by exact_mod_cast hd₁
  have hd₂' : (1 : ℝ) ≤ d₂ := by exact_mod_cast hd₂
  have he₁0 : 0 ≤ e₁ := by rw [he₁]; linarith
  have he₂0 : 0 ≤ e₂ := by rw [he₂]; linarith
  have hcast₁ : ((d₁ - 1 : ℕ) : ℝ) = d₁ - 1 := by rw [Nat.cast_sub hd₁]; simp
  have hcast₂ : ((d₂ - 1 : ℕ) : ℝ) = d₂ - 1 := by rw [Nat.cast_sub hd₂]; simp
  set B : ℝ := c₁ + e₁ with hBdef
  set C : ℝ := c₂ + e₂ - ((d₂ : ℝ) - 1) with hCdef
  have hB : B ∈ S := (hS _).2 (Or.inl ⟨0, hd₁, by simp [hBdef]⟩)
  have hC : C ∈ S := (hS _).2 (Or.inr ⟨d₂ - 1, by omega, by rw [hcast₂]⟩)
  have hmem : ∀ x ∈ S, x ≤ B ∨ C ≤ x := by
    intro x hx
    rcases (hS x).1 hx with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
    · left; have : (0 : ℝ) ≤ i := Nat.cast_nonneg i; linarith
    · right
      have h1 : j ≤ d₂ - 1 := by omega
      have h2 : (j : ℝ) ≤ ((d₂ - 1 : ℕ) : ℝ) := by exact_mod_cast h1
      rw [hcast₂] at h2; linarith
  obtain ⟨n, hn⟩ := hint _ hC _ hB
  rcases lt_trichotomy n 1 with h | h | h
  · exfalso
    have hn0 : n ≤ 0 := by omega
    have hn0' : (n : ℝ) ≤ 0 := by exact_mod_cast hn0
    by_cases hCA : c₁ - e₁ ≤ C
    · have hk : (((-n).toNat : ℕ) : ℤ) = -n := Int.toNat_of_nonneg (by omega)
      have hk' : (((-n).toNat : ℕ) : ℝ) = -(n : ℝ) := by exact_mod_cast hk
      have hkd : (-n).toNat < d₁ := by
        have : (((-n).toNat : ℕ) : ℝ) < d₁ := by rw [hk']; linarith
        exact_mod_cast this
      refine hdisj (-n).toNat (d₂ - 1) hkd (by omega) ?_
      rw [hk', hcast₂]; linarith
    · rw [not_le] at hCA
      have hJ0 : (0 : ℤ) ≤ n + d₁ + d₂ - 2 := by
        have : (0 : ℝ) ≤ (n : ℝ) + d₁ + d₂ - 2 := by linarith
        exact_mod_cast this
      have hJ1 : n + d₁ + d₂ - 2 < (d₂ : ℤ) := by
        have : (n : ℝ) + d₁ + d₂ - 2 < d₂ := by linarith
        exact_mod_cast this
      have hj : (((n + d₁ + d₂ - 2).toNat : ℕ) : ℤ) = n + d₁ + d₂ - 2 := Int.toNat_of_nonneg hJ0
      have hj' : (((n + d₁ + d₂ - 2).toNat : ℕ) : ℝ) = (n : ℝ) + d₁ + d₂ - 2 := by exact_mod_cast hj
      have hjd : (n + d₁ + d₂ - 2).toNat < d₂ := by omega
      refine hdisj (d₁ - 1) (n + d₁ + d₂ - 2).toNat (by omega) hjd ?_
      rw [hj', hcast₁]; linarith
  · subst h
    push_cast at hn
    linarith
  · exfalso
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (show (2 : ℤ) ≤ n by omega)
    have hC1 : C - 1 ∉ S := fun h1 => by rcases hmem _ h1 with h2 | h2 <;> linarith
    have hB1 : B + 1 ∉ S := fun h1 => by rcases hmem _ h1 with h2 | h2 <;> linarith
    have hClt : C < 1 := by
      by_contra h3; exact hC1 (hP _ hC (not_lt.1 h3))
    have hBgt : -1 < B := by
      by_contra h3; rw [not_lt] at h3
      have h4 := hneg _ (hP _ (hneg _ hB) (by linarith))
      exact hB1 (by convert h4 using 1; ring)
    linarith

end PositivityTheory.Rg.Rs.StrStepA
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.SdNormCpow

section

@[expose] public section

namespace PositivityTheory.Rg.Rs.StrStepA

theorem sd_norm_cpow (q : ℕ) (hq : 1 < q) (x : ℝ) : ‖(q : ℂ) ^ (-(x : ℂ))‖ = (q : ℝ) ^ (-x) := by
  rw [Complex.norm_natCast_cpow_of_pos (by omega)]
  simp

theorem step_down (q : ℕ) (hq : 1 < q) (B₀ : Multiset ℂ)
    (hB : ∀ β ∈ B₀, (q : ℝ) ^ (-(1 / 2) : ℝ) < ‖β‖ ∧ ‖β‖ < (q : ℝ) ^ (1 / 2 : ℝ)) {α : ℂ} (hα : α ∈ B₀)
    (S : Set ℝ) (hint : ∀ x ∈ S, ∀ y ∈ S, ∃ n : ℤ, x - y = n) (M : Multiset ℂ)
    (hM : ∀ z, z ∈ M ↔ ∃ x ∈ S, ∃ β ∈ B₀, z = β * (q : ℂ) ^ (-(x : ℂ)))
    (hgap : ∀ z : ℂ, ‖z‖ < (q : ℝ) ^ (-(1 / 2) : ℝ) → M.count z ≤ M.count ((q : ℂ) * z))
    {u : ℝ} (hu : u ∈ S) (hu1 : 1 ≤ u) : u - 1 ∈ S := by
  have hQ : (1 : ℝ) < q := by exact_mod_cast hq
  have hQ0 : (0 : ℝ) < q := by linarith
  set z : ℂ := α * (q : ℂ) ^ (-(u : ℂ)) with hz
  have hzM : z ∈ M := (hM z).2 ⟨u, hu, α, hα, rfl⟩
  have hnz : ‖z‖ = ‖α‖ * (q : ℝ) ^ (-u) := by rw [hz, norm_mul, sd_norm_cpow q hq]
  have hsmall : ‖z‖ < (q : ℝ) ^ (-(1 / 2) : ℝ) := by
    rw [hnz]
    have h1 : ‖α‖ * (q : ℝ) ^ (-u) < (q : ℝ) ^ (1 / 2 : ℝ) * (q : ℝ) ^ (-u) :=
      mul_lt_mul_of_pos_right (hB α hα).2 (Real.rpow_pos_of_pos hQ0 _)
    have h2 : (q : ℝ) ^ (1 / 2 : ℝ) * (q : ℝ) ^ (-u) = (q : ℝ) ^ (1 / 2 - u) := by
      rw [← Real.rpow_add hQ0]; ring_nf
    have h3 : (q : ℝ) ^ (1 / 2 - u) ≤ (q : ℝ) ^ (-(1 / 2) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hQ.le (by linarith)
    linarith
  have hc1 : 0 < M.count z := Multiset.count_pos.2 hzM
  have hc2 : 0 < M.count ((q : ℂ) * z) := lt_of_lt_of_le hc1 (hgap z hsmall)
  obtain ⟨x, hx, β, hβ, e⟩ := (hM _).1 (Multiset.count_pos.1 hc2)
  have en : (q : ℝ) * (‖α‖ * (q : ℝ) ^ (-u)) = ‖β‖ * (q : ℝ) ^ (-x) := by
    have h := congrArg norm e
    rw [norm_mul, hnz, norm_mul, sd_norm_cpow q hq, Complex.norm_natCast] at h
    exact h
  have hβn : ‖β‖ = ‖α‖ * (q : ℝ) ^ (1 - u + x) := by
    have e1 : (q : ℝ) ^ (1 - u + x) = q * (q : ℝ) ^ (-u) * (q : ℝ) ^ x := by
      rw [Real.rpow_add hQ0, Real.rpow_sub hQ0, Real.rpow_one, Real.rpow_neg hQ0.le]
      field_simp
    have hxx : (q : ℝ) ^ (-x) * (q : ℝ) ^ x = 1 := by rw [← Real.rpow_add hQ0]; simp
    calc ‖β‖ = ‖β‖ * (q : ℝ) ^ (-x) * (q : ℝ) ^ x := by rw [mul_assoc, hxx, mul_one]
      _ = q * (‖α‖ * (q : ℝ) ^ (-u)) * (q : ℝ) ^ x := by rw [en]
      _ = ‖α‖ * (q : ℝ) ^ (1 - u + x) := by rw [e1]; ring
  obtain ⟨n, hn⟩ := hint x hx u hu
  have hk : 1 - u + x = ((n + 1 : ℤ) : ℝ) := by push_cast; linarith
  rw [hk, Real.rpow_intCast] at hβn
  obtain ⟨hb1, hb2⟩ := hB β hβ
  obtain ⟨ha1, ha2⟩ := hB α hα
  have hpos : (0 : ℝ) < (q : ℝ) ^ (-(1 / 2) : ℝ) := Real.rpow_pos_of_pos hQ0 _
  have hhalf : (q : ℝ) ^ (-(1 / 2) : ℝ) * (q : ℝ) = (q : ℝ) ^ (1 / 2 : ℝ) := by
    have h := (Real.rpow_add hQ0 (-(1 / 2) : ℝ) 1).symm
    rw [Real.rpow_one] at h
    rw [h]; norm_num
  rcases lt_trichotomy (n + 1) 0 with hneg | hzero | hposn
  ·
    exfalso
    have hle : (q : ℝ) ^ (n + 1) ≤ (q : ℝ) ^ (-1 : ℤ) := zpow_le_zpow_right₀ hQ.le (by omega)
    have hzp : (0 : ℝ) < (q : ℝ) ^ (n + 1) := zpow_pos hQ0 _
    have : ‖β‖ < (q : ℝ) ^ (1 / 2 : ℝ) * (q : ℝ) ^ (-1 : ℤ) := by
      rw [hβn]
      calc ‖α‖ * (q : ℝ) ^ (n + 1) < (q : ℝ) ^ (1 / 2 : ℝ) * (q : ℝ) ^ (n + 1) := mul_lt_mul_of_pos_right ha2 hzp
        _ ≤ _ := mul_le_mul_of_nonneg_left hle (Real.rpow_pos_of_pos hQ0 _).le
    rw [← hhalf, zpow_neg_one, mul_assoc, mul_inv_cancel₀ hQ0.ne', mul_one] at this
    linarith
  · have hx' : x = u - 1 := by
      have : (n : ℝ) = -1 := by exact_mod_cast (by omega : n = -1)
      linarith
    rw [← hx']; exact hx
  · exfalso
    have hle : (q : ℝ) ^ (1 : ℤ) ≤ (q : ℝ) ^ (n + 1) := zpow_le_zpow_right₀ hQ.le (by omega)
    have : (q : ℝ) ^ (-(1 / 2) : ℝ) * (q : ℝ) ^ (1 : ℤ) < ‖β‖ := by
      rw [hβn]
      calc (q : ℝ) ^ (-(1 / 2) : ℝ) * (q : ℝ) ^ (1 : ℤ) ≤ (q : ℝ) ^ (-(1 / 2) : ℝ) * (q : ℝ) ^ (n + 1) :=
            mul_le_mul_of_nonneg_left hle hpos.le
        _ < ‖α‖ * (q : ℝ) ^ (n + 1) := mul_lt_mul_of_pos_right ha1 (zpow_pos hQ0 _)
    rw [zpow_one, hhalf] at this
    linarith

end PositivityTheory.Rg.Rs.StrStepA
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PStringStep

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec
open scoped ComplexConjugate

namespace PositivityTheory.Rg.Rs

theorem stringStep_of : GlobalTheory.Published.JacquetShalikaRigidity → GlobalTheory.Published.JacquetShalikaBound → InfInd2 → InfAsc →
    SatInd2 → SatAsc → SatHerm → Gap → StringStep := by
  intro hR hJ hInf hIA hSI hSA hSH hG E _ _ _ r s hr hs V V₁ V₂ z₁ z₂ hV hV₁ hV₂ hemb τ hτ hsum hre
    a₁ d₁ a₂ d₂ π₁ π₂ hu₁ hn₁ h₁ hu₂ hn₂ h₂

  have hr₁ : d₁ * a₁ = r := by obtain ⟨h, -⟩ := h₁; simpa using h
  have hs₂ : d₂ * a₂ = s := by obtain ⟨h, -⟩ := h₂; simpa using h
  have hd₁ : 0 < d₁ := Nat.pos_of_ne_zero fun h => by subst h; omega
  have hd₂ : 0 < d₂ := Nat.pos_of_ne_zero fun h => by subst h; omega
  have ha₁ : 1 ≤ a₁ := Nat.pos_of_ne_zero fun h => by subst h; omega
  have ha₂ : 1 ≤ a₂ := Nat.pos_of_ne_zero fun h => by subst h; omega

  have hexp := StrStepC.sat_expand hSI hSA hSH V V₁ V₂ z₁ z₂ hV hV₁ hV₂ hemb π₁ π₂ ha₁ ha₂ hu₁ hn₁ hu₂ hn₂ h₁ h₂
  have hp₀ := StrStepC.perm_of hR π₁ π₂ ha₁ ha₂ (fun i : Fin d₁ => z₁ - (s : ℂ) / 2 + (spehExp d₁ i : ℂ))
    (fun j : Fin d₂ => z₂ + (r : ℂ) / 2 + (spehExp d₂ j : ℂ))
    (hexp.mono fun w ⟨BV, B₁, B₂, _, h1, h2, e, hh⟩ => ⟨BV, B₁, B₂, h1, h2, e, hh⟩)

  rcases StrStepD.match_left ha₁ ha₂ π₁ π₂ hn₁ hn₂ _ _ hp₀ ⟨d₁ - 1, by omega⟩ with ⟨i', hi'⟩ | ⟨j, hj, hcls⟩
  · exfalso
    have h := congrArg Complex.re hi'
    have hi : ((d₁ - 1 : ℕ) : ℝ) = d₁ - 1 := by rw [Nat.cast_sub (by omega)]; simp
    simp only [spehExp, Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.conj_re, Complex.ofReal_re,
      Complex.div_ofNat_re, Complex.natCast_re, hi] at h
    have : (0 : ℝ) ≤ (i' : ℕ) := Nat.cast_nonneg _
    linarith
  have him : z₁.im = z₂.im := by
    have h := congrArg Complex.im hj
    simpa [spehExp, map_ofNat, Complex.div_ofNat_im] using h
  have hsim := congrArg Complex.im hsum
  simp only [Complex.add_im, Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero,
    Complex.zero_im] at hsim
  have h1im : z₁.im = 0 := by
    have : ((r : ℝ) + s) * z₁.im = 0 := by rw [← him] at hsim; linarith
    rcases mul_eq_zero.1 this with h | h
    · have : (0 : ℝ) < r := by exact_mod_cast hr
      have : (0 : ℝ) ≤ s := Nat.cast_nonneg _
      linarith
    · exact h
  have h2im : z₂.im = 0 := him ▸ h1im
  obtain ⟨ha, hh⟩ := Sigma.mk.inj_iff.1 hcls
  subst ha
  have hmk : CG.mk π₁ = CG.mk π₂ := eq_of_heq hh
  have hiso : π₁.Iso π₂ := Quotient.exact hmk
  subst hr₁ hs₂

  obtain ⟨c₁, hc₁d⟩ : ∃ c : ℝ, c = z₁.re - ((d₂ * a₁ : ℕ) : ℝ) / 2 := ⟨_, rfl⟩
  obtain ⟨c₂, hc₂d⟩ : ∃ c : ℝ, c = z₂.re + ((d₁ * a₁ : ℕ) : ℝ) / 2 := ⟨_, rfl⟩
  have hc₁ : ((c₁ : ℝ) : ℂ) = z₁ - ((d₂ * a₁ : ℕ) : ℂ) / 2 := by
    apply Complex.ext <;> simp [hc₁d, h1im]
  have hc₂ : ((c₂ : ℝ) : ℂ) = z₂ + ((d₁ * a₁ : ℕ) : ℂ) / 2 := by
    apply Complex.ext <;> simp [hc₂d, h2im]

  obtain ⟨m, hm, hnd, hint⟩ := hτ
  obtain ⟨m₁, m₂, hm₁, hm₂, hme⟩ := hInf E _ _ V V₁ V₂ z₁ z₂ hV hV₁ hV₂ hemb τ m hm
  obtain ⟨m₀, hm₀, hme₁⟩ := hIA E _ a₁ d₁ V₁ π₁ hV₁ h₁ τ m₁ hm₁
  obtain ⟨m₀', hm₀', hme₂⟩ := hIA E _ a₁ d₂ V₂ π₂ hV₂ h₂ τ m₂ hm₂
  have hm₀e : m₀' = m₀ := hm₀'.unique (hiso.hasInfChar hm₀)
  have hform : m = (∑ i : Fin d₁, m₀.map (· + (spehExp d₁ i : ℂ))).map (· + ((c₁ : ℝ) : ℂ)) +
      (∑ j : Fin d₂, m₀.map (· + (spehExp d₂ j : ℂ))).map (· + ((c₂ : ℝ) : ℂ)) := by
    rw [hme, hme₁, hme₂, hm₀e, hc₁, hc₂]
  have hne : m₀ ≠ 0 := by
    rintro rfl
    have h := hm.1
    rw [hform] at h
    simp at h
    linarith
  obtain ⟨hdisj, hintS⟩ := StrStepD.of_infChar m m₀ c₁ c₂ hform hne hnd hint

  have hexp' : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ BV B₁ B₂ : Multiset ℂˣ, SatV V w BV ∧
      (CG.mk π₁).HasSat w B₁ ∧ (CG.mk π₂).HasSat w B₂ ∧
      BV.map (fun b : ℂˣ => (b : ℂ)) =
        (∑ i : Fin d₁, B₁.map fun b : ℂˣ =>
          (b : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-((c₁ + spehExp d₁ i : ℝ) : ℂ))) +
          ∑ j : Fin d₂, B₂.map (fun b : ℂˣ =>
            (b : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-((c₂ + spehExp d₂ j : ℝ) : ℂ))) ∧
      BV.map (fun b => (star b)⁻¹) = BV ∧ B₁.map (fun b => (star b)⁻¹) = B₁ ∧
        B₂.map (fun b => (star b)⁻¹) = B₂ := by
    refine hexp.mono fun w ⟨BV, B₁, B₂, h0, h1, h2, e, hh⟩ => ⟨BV, B₁, B₂, h0, h1, h2, ?_, hh⟩
    rw [e]
    simp only [Complex.ofReal_add, hc₁, hc₂]
  have hp := StrStepC.perm_of hR π₁ π₂ ha₁ ha₁ (fun i : Fin d₁ => ((c₁ + spehExp d₁ i : ℝ) : ℂ))
    (fun j : Fin d₂ => ((c₂ + spehExp d₂ j : ℝ) : ℂ))
    (hexp'.mono fun w ⟨BV, B₁, B₂, _, h1, h2, e, hh⟩ => ⟨BV, B₁, B₂, h1, h2, e, hh⟩)
  have hneg : ∀ u ∈ StrStepD.strSet c₁ c₂ d₁ d₂, -u ∈ StrStepD.strSet c₁ c₂ d₁ d₂ := by
    intro u hu
    rcases StrStepD.mem_strSet.1 hu with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · rcases StrStepD.match_left ha₁ ha₁ π₁ π₂ hn₁ hn₂ _ _ hp i with ⟨i', e⟩ | ⟨j, e, -⟩
      · have h := congrArg Complex.re e
        simp only [Complex.ofReal_re, Complex.neg_re, Complex.conj_re] at h
        exact StrStepD.mem_strSet.2 (Or.inl ⟨i', by linarith⟩)
      · have h := congrArg Complex.re e
        simp only [Complex.ofReal_re, Complex.neg_re, Complex.conj_re] at h
        exact StrStepD.mem_strSet.2 (Or.inr ⟨j, by linarith⟩)
    · rcases StrStepD.match_right ha₁ ha₁ π₁ π₂ hn₁ hn₂ _ _ hp j with ⟨j', e⟩ | ⟨i, e, -⟩
      · have h := congrArg Complex.re e
        simp only [Complex.ofReal_re, Complex.neg_re, Complex.conj_re] at h
        exact StrStepD.mem_strSet.2 (Or.inr ⟨j', by linarith⟩)
      · have h := congrArg Complex.re e
        simp only [Complex.ofReal_re, Complex.neg_re, Complex.conj_re] at h
        exact StrStepD.mem_strSet.2 (Or.inl ⟨i, by linarith⟩)

  have := GlobalTheory.Published.JacquetShalikaModel.infinite_places (E := E)
  obtain ⟨w, BV, B₁, B₂, hBV, hs₁, hs₂, e, -⟩ := hexp'.exists
  have hB₂ : B₂ = B₁ := by
    rw [← hmk] at hs₂
    exact hs₂.unique hs₁
  rw [hB₂] at e
  have hq : 1 < Ideal.absNorm w.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm w
  have hM : ∀ z, z ∈ BV.map (fun b : ℂˣ => (b : ℂ)) ↔ ∃ x ∈ StrStepD.strSet c₁ c₂ d₁ d₂,
      ∃ β ∈ B₁.map (fun b : ℂˣ => (b : ℂ)), z = β * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-(x : ℂ)) := by
    intro z
    rw [e, ← StrStepD.mem_sat]
    simp only [Multiset.map_map, Function.comp_def, Complex.ofReal_add]
  have hgap : ∀ z : ℂ, ‖z‖ < (Ideal.absNorm w.asIdeal : ℝ) ^ (-(1 / 2) : ℝ) →
      (BV.map fun b : ℂˣ => (b : ℂ)).count z ≤
        (BV.map fun b : ℂˣ => (b : ℂ)).count ((Ideal.absNorm w.asIdeal : ℂ) * z) :=
    fun z hz => hG E _ V hV w BV hBV z hz
  have hbound : ∀ β ∈ B₁.map (fun b : ℂˣ => (b : ℂ)), (Ideal.absNorm w.asIdeal : ℝ) ^ (-(1 / 2) : ℝ) < ‖β‖ ∧
      ‖β‖ < (Ideal.absNorm w.asIdeal : ℝ) ^ (1 / 2 : ℝ) := by
    intro β hβ
    obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.1 hβ
    exact hJ E a₁ (CG.mk π₁) ((CG.isUnitary_mk π₁).2 hu₁) w B₁ hs₁ b hb
  obtain ⟨α, hα⟩ : ∃ α, α ∈ B₁.map (fun b : ℂˣ => (b : ℂ)) := by
    obtain ⟨b, hb⟩ := Multiset.card_pos_iff_exists_mem.1 (by rw [hs₁.card]; omega)
    exact ⟨_, Multiset.mem_map_of_mem _ hb⟩
  have hP : ∀ u ∈ StrStepD.strSet c₁ c₂ d₁ d₂, 1 ≤ u → u - 1 ∈ StrStepD.strSet c₁ c₂ d₁ d₂ :=
    fun u hu hu1 => StrStepA.step_down _ hq _ hbound hα _ hintS _ hM hgap hu hu1

  have hlin : (d₁ : ℝ) * c₁ + d₂ * c₂ = 0 := by
    have hsre := congrArg Complex.re hsum
    simp only [Complex.add_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im, h1im, h2im, mul_zero,
      sub_zero, Complex.zero_re] at hsre
    have ha : (0 : ℝ) < a₁ := by exact_mod_cast ha₁
    have : (a₁ : ℝ) * (d₁ * c₁ + d₂ * c₂) = 0 := by
      rw [hc₁d, hc₂d]
      push_cast at hsre ⊢
      linear_combination hsre
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact h
  have hc₁n : c₁ < 0 := by rw [hc₁d]; linarith
  have hc₂p : 0 < c₂ := by
    have : (0 : ℝ) < d₁ := by exact_mod_cast hd₁
    have : (0 : ℝ) < d₂ := by exact_mod_cast hd₂
    nlinarith
  have hadj := StrStepA.adjacent c₁ c₂ d₁ d₂ hd₁ hd₂ (StrStepD.strSet c₁ c₂ d₁ d₂) (fun x => Iff.rfl) hdisj hintS
    hneg hP (by linarith)
  have hc₁v : c₁ = -(d₂ : ℝ) / 2 := by
    have h : ((d₁ : ℝ) + d₂) * (c₁ + d₂ / 2) = 0 := by linear_combination hlin - (d₂ : ℝ) * hadj
    rcases mul_eq_zero.1 h with h | h
    · have : (0 : ℝ) < d₁ := by exact_mod_cast hd₁
      have : (0 : ℝ) ≤ d₂ := Nat.cast_nonneg _
      linarith
    · linarith
  have hc₂v : c₂ = (d₁ : ℝ) / 2 := by linarith
  push_cast at hc₁d hc₂d
  refine ⟨by rw [hmk], ?_, ?_⟩
  · apply Complex.ext
    · simp
      linarith
    · simp [h1im]
  · apply Complex.ext
    · simp
      linarith
    · simp [h2im]

end PositivityTheory.Rg.Rs

end
end
end
