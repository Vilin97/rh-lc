module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegelZeroFront
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BalancedEntriesBoundedSiegelReducedStatement
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegelZeroFront
public import Mathlib.Algebra.Algebra.Spectrum.Basic
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.Complex.Norm

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TraceBoundedOfAevalMonicEqZero

section

@[expose] public section

open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RedTh

theorem trace_le_of_aeval_monic_eq_zero :
    ∀ (p : Polynomial ℤ), p.Monic → ∀ n : ℕ, ∃ K : ℝ, ∀ M : Matrix (Fin n) (Fin n) ℤ,
      Polynomial.aeval M p = 0 → ((M.trace : ℤ) : ℝ) ≤ K := by
  intro p hp n
  set pC : Polynomial ℂ := p.map (Int.castRingHom ℂ) with hpC
  have hpC0 : pC ≠ 0 := (hp.map (Int.castRingHom ℂ)).ne_zero
  set B : ℝ := ∑ x ∈ pC.roots.toFinset, ‖x‖ with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun x _ => norm_nonneg x
  refine ⟨n * B, fun M hM => ?_⟩
  set A : Matrix (Fin n) (Fin n) ℂ := M.map (Int.castRingHom ℂ) with hA
  have hAp : Polynomial.aeval A pC = 0 := by
    have e := Polynomial.aeval_algHom_apply ((Int.castRingHom ℂ).mapMatrix (m := Fin n)).toIntAlgHom M p
    rw [hM, map_zero] at e
    rw [hpC, show Int.castRingHom ℂ = algebraMap ℤ ℂ from rfl, Polynomial.aeval_map_algebraMap]
    exact e
  have htr : ((M.trace : ℤ) : ℂ) = A.trace := by
    simp [hA, Matrix.trace, Matrix.map_apply]
  have hroot : ∀ μ ∈ A.charpoly.roots, ‖μ‖ ≤ B := by
    intro μ hμ
    rcases isEmpty_or_nonempty (Fin n) with hn | hn
    · exfalso
      have hc := Polynomial.card_roots' A.charpoly
      rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_eq_zero] at hc
      have := Multiset.card_pos_iff_exists_mem.2 ⟨μ, hμ⟩
      omega
    have hsp : μ ∈ spectrum ℂ A :=
      Matrix.mem_spectrum_iff_isRoot_charpoly.2 (Polynomial.isRoot_of_mem_roots hμ)
    have h1 := spectrum.subset_polynomial_aeval A pC ⟨μ, hsp, rfl⟩
    rw [hAp, spectrum.zero_eq, Set.mem_singleton_iff] at h1
    have hmem : μ ∈ pC.roots.toFinset := by
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hpC0]; exact h1
    exact Finset.single_le_sum (f := fun x => ‖x‖) (fun x _ => norm_nonneg x) hmem
  have hsum : ‖A.trace‖ ≤ n * B := by
    rw [Matrix.trace_eq_sum_roots_charpoly]
    refine (norm_multiset_sum_le _).trans ?_
    refine (Multiset.sum_le_card_nsmul _ B (fun x hx => by obtain ⟨μ, hμ, rfl⟩ := Multiset.mem_map.1 hx; exact hroot μ hμ)).trans ?_
    rw [Multiset.card_map, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ hB0
    have := Polynomial.card_roots' A.charpoly
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at this
    exact_mod_cast this
  calc ((M.trace : ℤ) : ℝ) = (((M.trace : ℤ) : ℂ)).re := by simp
    _ ≤ ‖((M.trace : ℤ) : ℂ)‖ := Complex.re_le_norm _
    _ ≤ n * B := by rw [htr]; exact hsum

end GlobalTheory.RedTh
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TraceBoundedOfAevalMonicEqZeroStatement

section

@[expose] public section

open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.trace_bounded_of_aeval_monic_eq_zero : ∀ (p : Polynomial ℤ), p.Monic → ∀ n : ℕ, ∃ K : ℝ, ∀ M : Matrix (Fin n) (Fin n) ℤ, Polynomial.aeval M p = 0 → ((M.trace : ℤ) : ℝ) ≤ K := by
  first | exact @GlobalTheory.RedTh.trace_le_of_aeval_monic_eq_zero | exact GlobalTheory.RedTh.trace_le_of_aeval_monic_eq_zero | (intros; apply GlobalTheory.RedTh.trace_le_of_aeval_monic_eq_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteBalancedCmIntegersActionsSiegelReduced

section

@[expose] public section

open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RedTh

theorem finite_balanced_actions : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (n : ℕ),
    {ρ : 𝓞 E →+* Matrix (Fin n) (Fin n) ℤ | ∃ (d : Fin n → ℝ) (u : Matrix (Fin n) (Fin n) ℝ), IsSiegel d u ∧
      (∀ i, 0 < d i) ∧ ∀ c, ((ρ c).map (Int.cast : ℤ → ℝ))ᵀ * gram d u = gram d u *
        (ρ (H.bar c)).map (Int.cast : ℤ → ℝ)}.Finite := by
  intro E _ _ _ H n
  classical
  set S := {ρ : 𝓞 E →+* Matrix (Fin n) (Fin n) ℤ | ∃ (d : Fin n → ℝ) (u : Matrix (Fin n) (Fin n) ℝ), IsSiegel d u ∧
      (∀ i, 0 < d i) ∧ ∀ c, ((ρ c).map (Int.cast : ℤ → ℝ))ᵀ * gram d u = gram d u *
        (ρ (H.bar c)).map (Int.cast : ℤ → ℝ)} with hSdef

  have hK : ∀ c : 𝓞 E, ∃ K : ℝ, ∀ ρ : 𝓞 E →+* Matrix (Fin n) (Fin n) ℤ,
      (((ρ (H.bar c) * ρ c).trace : ℤ) : ℝ) ≤ K := by
    intro c
    obtain ⟨p, hpm, hp⟩ := Algebra.IsIntegral.isIntegral (R := ℤ) (H.bar c * c)
    obtain ⟨K, hK⟩ := GlobalTheory.T.trace_bounded_of_aeval_monic_eq_zero p hpm n
    refine ⟨K, fun ρ => ?_⟩
    apply hK
    have h0 : Polynomial.aeval (ρ.toIntAlgHom (H.bar c * c)) p = 0 := by
      rw [Polynomial.aeval_algHom_apply, Polynomial.aeval_def, hp, map_zero]
    simpa using h0
  choose K hK using hK

  have hC : ∀ c : 𝓞 E, ∃ N : ℤ, ∀ ρ ∈ S, ∀ i j, ρ c i j ∈ Set.Icc (-N) N := by
    intro c
    obtain ⟨C, hC⟩ := GlobalTheory.T.balanced_entries_bounded_siegelReduced n (K c)
    refine ⟨⌈C⌉, fun ρ hρ i j => ?_⟩
    obtain ⟨d, u, hs, hpos, hrel⟩ := hρ
    have h1 := hC (ρ c) (ρ (H.bar c)) d u hs hpos (hrel c) (hK c ρ) i j
    have h2 : ((|ρ c i j| : ℤ) : ℝ) ≤ ((⌈C⌉ : ℤ) : ℝ) := h1.trans (Int.le_ceil C)
    have h3 : |ρ c i j| ≤ ⌈C⌉ := by exact_mod_cast h2
    exact abs_le.mp h3
  choose N hN using hC
  let b := RingOfIntegers.basis E
  let F : (𝓞 E →+* Matrix (Fin n) (Fin n) ℤ) → (Module.Free.ChooseBasisIndex ℤ (𝓞 E) → Fin n → Fin n → ℤ) :=
    fun ρ l => ρ (b l)
  let T : Set (Module.Free.ChooseBasisIndex ℤ (𝓞 E) → Fin n → Fin n → ℤ) :=
    Set.pi Set.univ fun l => Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Set.Icc (-N (b l)) (N (b l))
  have hT : T.Finite :=
    Set.Finite.pi fun l => Set.Finite.pi fun _ => Set.Finite.pi fun _ => Set.finite_Icc _ _
  refine Set.Finite.of_injOn (f := F) (t := T) ?_ ?_ hT
  · intro ρ hρ l _ i _ j _
    exact hN (b l) ρ hρ i j
  · intro ρ₁ _ ρ₂ _ h
    have hl : ∀ l, ρ₁ (b l) = ρ₂ (b l) := fun l => congrFun h l
    have hlin : ρ₁.toAddMonoidHom.toIntLinearMap = ρ₂.toAddMonoidHom.toIntLinearMap :=
      b.ext fun l => by simpa using hl l
    ext1 x
    simpa using LinearMap.congr_fun hlin x

end GlobalTheory.RedTh
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteBalancedCmIntegersActionsSiegelReducedStatement

section

@[expose] public section

open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.finite_balanced_cmIntegers_actions_siegelReduced : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (n : ℕ), {ρ : 𝓞 E →+* Matrix (Fin n) (Fin n) ℤ | ∃ (d : Fin n → ℝ) (u : Matrix (Fin n) (Fin n) ℝ), IsSiegel d u ∧ (∀ i, 0 < d i) ∧ ∀ c, ((ρ c).map (Int.cast : ℤ → ℝ))ᵀ * gram d u = gram d u * (ρ (H.bar c)).map (Int.cast : ℤ → ℝ)}.Finite := by
  first | exact @GlobalTheory.RedTh.finite_balanced_actions | exact GlobalTheory.RedTh.finite_balanced_actions | (intros; apply GlobalTheory.RedTh.finite_balanced_actions <;> assumption)
end
end
