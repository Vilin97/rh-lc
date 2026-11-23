module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DegOneIffSurjective
public import Mathlib.RingTheory.DedekindDomain.Basic
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
import Mathlib.Tactic.Linter.Style
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
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ResidueDegreeOneOfLinearMem

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRepsCoprimeOutsideModulus

section

@[expose] public section

namespace GlobalTheory


open IsDedekindDomain in
theorem exists_reps_coprime_outside_modulus : ∀ (A : Type) [CommRing A] [IsDedekindDomain A] (m : Ideal A) (a₀ b₀ : A), m ≠ ⊥ → ∃ a b : A, a - a₀ ∈ m ∧ b - b₀ ∈ m ∧ b ≠ 0 ∧ ∀ p : Ideal A, p.IsMaximal → ¬ m ≤ p → ¬ (a ∈ p ∧ b ∈ p) := by
  classical
  intro A _ _ m a₀ b₀ hm
  obtain ⟨b, hbm, hb0⟩ : ∃ b, b - b₀ ∈ m ∧ b ≠ 0 := by
    by_cases h : b₀ = 0
    · obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
      exact ⟨x, by simpa [h] using hx, hx0⟩
    · exact ⟨b₀, by simp, h⟩
  have hspan : Ideal.span {b} ≠ (0 : Ideal A) := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hb0
  have hfin : {v : HeightOneSpectrum A | v.asIdeal ∣ Ideal.span {b}}.Finite :=
    Ideal.finite_factors hspan
  let S := hfin.toFinset.filter (fun v => ¬ m ≤ v.asIdeal)
  let K : Ideal A := ⨅ v ∈ S, v.asIdeal
  have hK : m ⊔ K = ⊤ := by
    apply Ideal.sup_iInf_eq_top
    intro v hv
    have hv' : ¬ m ≤ v.asIdeal := (Finset.mem_filter.mp hv).2
    have hmax : v.asIdeal.IsMaximal := v.isMaximal
    by_contra hne
    rw [sup_comm] at hne
    have heq := hmax.eq_of_le hne le_sup_left
    exact hv' (heq ▸ le_sup_right)
  have h1 : (1 : A) ∈ m ⊔ K := by rw [hK]; exact Submodule.mem_top
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp h1
  refine ⟨a₀ * y + x, b, ?_, hbm, hb0, ?_⟩
  · have : a₀ * y + x - a₀ = x - a₀ * x := by
      have hy' : y = 1 - x := by rw [← hxy]; ring
      rw [hy']; ring
    rw [this]
    exact m.sub_mem hx (m.mul_mem_left a₀ hx)
  · rintro p hp hmp ⟨hap, hbp⟩
    have hp0 : p ≠ ⊥ := by
      rintro rfl
      exact hb0 ((Submodule.mem_bot A).mp hbp)
    let v : HeightOneSpectrum A := ⟨p, hp.isPrime, hp0⟩
    have hvS : v ∈ S := by
      refine Finset.mem_filter.mpr ⟨?_, hmp⟩
      rw [Set.Finite.mem_toFinset]
      show p ∣ Ideal.span {b}
      rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
      exact hbp
    have hKp : K ≤ p := iInf₂_le v hvS
    have hyp : y ∈ p := hKp hy
    have hxp : x ∈ p := by
      have := p.sub_mem hap (p.mul_mem_left a₀ hyp)
      simpa using this
    exact hp.ne_top ((Ideal.eq_top_iff_one p).mpr (hxy ▸ p.add_mem hxp hyp))

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCongrModPowResidueDegreeOneFactors

section

@[expose] public section

open NumberField IsDedekindDomain HeckeValGen GlobalTheory.HeckeSplit

namespace GlobalTheory

theorem exists_shift_mod_pow_degOne : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (θ : 𝓞 E) (D : 𝓞 F), (∀ y : 𝓞 E, ∃ u v : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) D * y = algebraMap (𝓞 F) (𝓞 E) u + algebraMap (𝓞 F) (𝓞 E) v * θ) → ∀ (m : Ideal (𝓞 F)), m ≠ ⊥ → m ≤ Ideal.span {D} → ∀ (y : 𝓞 E) (N : ℕ), ∃ k : 𝓞 E, k - algebraMap (𝓞 F) (𝓞 E) D * y ∈ Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (m ^ N) ∧ ∀ P : HeightOneSpectrum (𝓞 E), ¬ m ≤ P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) → k ∈ P.asIdeal → DegOne F P := by
  intro F E _ _ _ _ _ θ D hgen m hm hmD y N
  obtain ⟨u, v, huv⟩ := hgen y
  have hmN : m ^ N ≠ ⊥ := pow_ne_zero N hm
  obtain ⟨a, b, ha, hb, -, hcop⟩ := exists_reps_coprime_outside_modulus (𝓞 F) (m ^ N) u v hmN
  refine ⟨algebraMap (𝓞 F) (𝓞 E) a + algebraMap (𝓞 F) (𝓞 E) b * θ, ?_, ?_⟩
  · rw [huv]
    have e : algebraMap (𝓞 F) (𝓞 E) a + algebraMap (𝓞 F) (𝓞 E) b * θ -
        (algebraMap (𝓞 F) (𝓞 E) u + algebraMap (𝓞 F) (𝓞 E) v * θ) =
        algebraMap (𝓞 F) (𝓞 E) (a - u) + algebraMap (𝓞 F) (𝓞 E) (b - v) * θ := by
      simp only [map_sub]; ring
    rw [e]
    exact Ideal.add_mem _ (Ideal.mem_map_of_mem _ ha)
      (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hb))
  · intro P hmP hk
    have hPmax : P.asIdeal.IsMaximal := P.isMaximal
    have hpmax : (P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))).IsMaximal :=
      Ideal.isMaximal_under_of_isIntegral_of_isMaximal P.asIdeal
    have hmNp : ¬ m ^ N ≤ P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) := fun h =>
      hmP (hpmax.isPrime.le_of_pow_le h)
    have hD : algebraMap (𝓞 F) (𝓞 E) D ∉ P.asIdeal := by
      intro h
      apply hmP
      refine hmD.trans ?_
      rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
      exact h
    have hbP : algebraMap (𝓞 F) (𝓞 E) b ∉ P.asIdeal := by
      intro h
      apply hcop _ hpmax hmNp
      refine ⟨?_, Ideal.mem_comap.mpr h⟩
      rw [Ideal.mem_comap]
      have := P.asIdeal.sub_mem hk (P.asIdeal.mul_mem_right θ h)
      simpa using this
    exact residue_degree_one_of_linear_mem (𝓞 F) (𝓞 E) P.asIdeal θ D a b hpmax hgen hD hbP hk
end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCongrModPowResidueDegreeOneFactorsStatement

section

@[expose] public section

open NumberField IsDedekindDomain HeckeValGen GlobalTheory.HeckeSplit

theorem _root_.GlobalTheory.T.exists_congr_mod_pow_residueDegreeOne_factors : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (θ : 𝓞 E) (D : 𝓞 F), (∀ y : 𝓞 E, ∃ u v : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) D * y = algebraMap (𝓞 F) (𝓞 E) u + algebraMap (𝓞 F) (𝓞 E) v * θ) → ∀ (m : Ideal (𝓞 F)), m ≠ ⊥ → m ≤ Ideal.span {D} → ∀ (y : 𝓞 E) (N : ℕ), ∃ k : 𝓞 E, k - algebraMap (𝓞 F) (𝓞 E) D * y ∈ Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (m ^ N) ∧ ∀ P : HeightOneSpectrum (𝓞 E), ¬ m ≤ P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) → k ∈ P.asIdeal → DegOne F P := by
  first | exact @GlobalTheory.exists_shift_mod_pow_degOne | exact GlobalTheory.exists_shift_mod_pow_degOne | (intros; apply GlobalTheory.exists_shift_mod_pow_degOne <;> assumption)
end
end
