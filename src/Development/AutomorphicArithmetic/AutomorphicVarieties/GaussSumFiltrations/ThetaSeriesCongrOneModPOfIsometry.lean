module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPosGramQuadFormTotallyPositiveProperness
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.IntMatrixIsometryPrimeOrderLatticeStability
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.NormSumFreeOrbitsLeInvPrime
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.QExpansionLinearCombination
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ThetaSeriesHolomorphicQExpansionOfBoundedCoeff

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.LatticePeriodicFunctionRangeFinite

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries

theorem isSB_range_finite : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [DecidableEq κ] (N : ℕ)
    (Φ : (κ → F) → ℂ), 0 < N → IsSB N Φ → (Set.range Φ).Finite := by
  intro F _ _ κ _ _ N Φ hN hSB
  classical
  obtain ⟨hsupp, hper⟩ := hSB
  have memLL : ∀ y : κ → F, y ∈ LL F κ ↔ ∀ k, IsIntegral ℤ (y k) := by
    intro y
    simp [LL, AddSubgroup.mem_pi, mem_integralClosure_iff]
  have memaL : ∀ (c : F) (x : κ → F), x ∈ aL κ c ↔ ∃ y ∈ LL F κ, c • y = x := by
    intro c x
    simp [aL]
  have intB : ∀ c : Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℤ,
      IsIntegral ℤ (∑ i, c i • integralBasis F i) := by
    intro c
    have hmem : (∑ i, c i • integralBasis F i) ∈ Submodule.span ℤ (Set.range (integralBasis F)) :=
      (Submodule.mem_span_range_iff_exists_fun ℤ).mpr ⟨c, rfl⟩
    obtain ⟨a, ha⟩ := (mem_span_integralBasis F).mp hmem
    rw [← ha]
    exact RingOfIntegers.isIntegral_coe a
  have decomp : ∀ z : F, IsIntegral ℤ z →
      ∃ c : Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℤ, ∑ i, c i • integralBasis F i = z := by
    intro z hz
    have hmem : z ∈ Submodule.span ℤ (Set.range (integralBasis F)) :=
      (mem_span_integralBasis F).mpr ⟨⟨z, hz⟩, rfl⟩
    exact (Submodule.mem_span_range_iff_exists_fun ℤ).mp hmem
  have hNF : (N : F) ≠ 0 := by exact_mod_cast hN.ne'
  have hM : (0 : ℤ) < ((N * N : ℕ) : ℤ) := by positivity
  let g : (κ → Module.Free.ChooseBasisIndex ℤ (𝓞 F) → Fin (N * N)) → ℂ := fun r =>
    Φ (fun k => (N : F)⁻¹ * ∑ i, (((r k i : ℕ) : ℤ) • integralBasis F i))
  refine ((Set.finite_range g).insert 0).subset ?_
  rintro _ ⟨x, rfl⟩
  rw [Set.mem_insert_iff]
  by_cases h0 : Φ x = 0
  · exact Or.inl h0
  right
  obtain ⟨y, hy, rfl⟩ := (memaL _ x).mp (hsupp x h0)
  have hyi := (memLL y).mp hy
  choose c hc using fun k => decomp (y k) (hyi k)
  have hcast : ∀ k i, (((c k i % ((N * N : ℕ) : ℤ)).toNat : ℕ) : ℤ) = c k i % ((N * N : ℕ) : ℤ) :=
    fun k i => Int.toNat_of_nonneg (Int.emod_nonneg _ hM.ne')
  refine ⟨fun k i => ⟨(c k i % ((N * N : ℕ) : ℤ)).toNat, ?_⟩, ?_⟩
  · have h2 := Int.emod_lt_of_pos (c k i) hM
    have h3 := hcast k i
    omega
  · show Φ (fun k => (N : F)⁻¹ *
        ∑ i, ((((c k i % ((N * N : ℕ) : ℤ)).toNat : ℕ) : ℤ) • integralBasis F i)) = Φ ((N : F)⁻¹ • y)
    simp only [hcast]
    have hl : ((N : F)⁻¹ • y - fun k => (N : F)⁻¹ *
        ∑ i, ((c k i % ((N * N : ℕ) : ℤ)) • integralBasis F i)) ∈ aL κ (N : F) := by
      rw [memaL]
      refine ⟨fun k => ∑ i, (c k i / ((N * N : ℕ) : ℤ)) • integralBasis F i, ?_, ?_⟩
      · rw [memLL]
        intro k
        exact intB _
      · funext k
        simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        rw [← hc k, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        simp only [zsmul_eq_mul]
        have hdiv : ((c k i : ℤ) : F) = ((N : F) * N) * ((c k i / ((N * N : ℕ) : ℤ) : ℤ) : F) +
            ((c k i % ((N * N : ℕ) : ℤ) : ℤ) : F) := by
          exact_mod_cast (Int.mul_ediv_add_emod (c k i) ((N * N : ℕ) : ℤ)).symm
        have key : ∀ (cF rF qF : F), cF = ((N : F) * N) * qF + rF →
            (N : F) * (qF * integralBasis F i) =
              (N : F)⁻¹ * (cF * integralBasis F i) - (N : F)⁻¹ * (rF * integralBasis F i) := by
          intro cF rF qF h
          rw [h]
          field_simp
          ring
        exact key _ _ _ hdiv
    have hp := hper (fun k => (N : F)⁻¹ *
        ∑ i, ((c k i % ((N * N : ℕ) : ℤ)) • integralBasis F i)) _ hl
    rw [add_sub_cancel] at hp
    exact hp.symm

end GlobalTheory.HilbertThetaSeries

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

theorem _root_.GlobalTheory.T.lattice_periodic_function_range_finite : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [DecidableEq κ] (N : ℕ) (Φ : (κ → F) → ℂ), 0 < N → IsSB N Φ → (Set.range Φ).Finite := by
  first | exact @GlobalTheory.HilbertThetaSeries.isSB_range_finite | exact GlobalTheory.HilbertThetaSeries.isSB_range_finite | (intros; apply GlobalTheory.HilbertThetaSeries.isSB_range_finite <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ThetaSeriesCongrOneModPOfIsometry

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries

theorem th_congr_one : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ) (κ : Type) [Fintype κ] [DecidableEq κ] (G S : Matrix κ κ ℤ) (t : ℕ), LatD p G S t → ∀ Φ : (κ → F) → ℂ, Good ι S Φ → Small ι (p : ℝ)⁻¹ (th G Φ - 1) := by
  intro F _ _ _ p _ ι κ _ _ G S t hL Φ hΦ
  obtain ⟨⟨N, hN, hNp, hSB⟩, hinv, hbd, h0⟩ := hΦ
  have hp : p.Prime := Fact.out
  obtain ⟨hQ, hact, -, -⟩ := _root_.GlobalTheory.T.intMatrix_isometry_prime_order_lattice_stability F p hp κ G S t hL
  obtain ⟨hTP, -, hfin⟩ := _root_.GlobalTheory.T.evenPosGram_quadForm_totallyPositive_properness F κ G hL.pos
  obtain ⟨B, hB⟩ := ((_root_.GlobalTheory.T.lattice_periodic_function_range_finite F κ N Φ hN hSB).image (fun w => ‖w‖)).bddAbove
  have hB' : ∀ x, ‖Φ x‖ ≤ B := fun x => hB ⟨Φ x, ⟨x, rfl⟩, rfl⟩
  obtain ⟨-, -, -, hq⟩ := _root_.GlobalTheory.T.thetaSeries_holomorphic_qExpansion_of_bounded_coeff F κ G hL.pos ((N:F)⁻¹) Φ B hSB.1 hB'
  have hc := (_root_.GlobalTheory.T.qExpansion_linear_combination F _ _ _ _ (1:ℂ) hq hq).2.2.2
  have hq1 := (_root_.GlobalTheory.T.qExpansion_linear_combination F _ _ _ _ (1:ℂ) hq hc).2.2.1
  refine ⟨_, hq1, fun ξ => ?_⟩
  simp only [Pi.sub_apply]
  have hfs := hfin ((N:F)⁻¹) ξ
  rw [finsum_mem_eq_finite_toFinset_sum _ hfs]
  by_cases hξ : ξ = 0
  · subst hξ
    have hz : hfs.toFinset = {0} := by
      ext x
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Finset.mem_singleton]
      constructor
      · rintro ⟨-, hx⟩
        by_contra hne
        have h1 := hTP x hne
        rw [hx] at h1
        obtain ⟨v⟩ := (inferInstance : Nonempty (NumberField.InfinitePlace F))
        have h2 := h1 v
        simp [reAt] at h2
      · rintro rfl
        exact ⟨zero_mem _, by simp [QF, BF]⟩
    rw [hz, Finset.sum_singleton, if_pos rfl, map_sub, map_one]
    exact h0
  · rw [if_neg hξ, sub_zero]
    apply _root_.GlobalTheory.T.norm_sum_free_orbits_le_inv_prime p ι (κ → F) (fun x => S.map Int.cast *ᵥ x) hfs.toFinset Φ
    · intro x hx
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hx ⊢
      exact ⟨((hact x).2.2.2 _).2 hx.1, ((hQ x x).2).trans hx.2⟩
    · intro x _
      exact (hact x).1
    · intro x hx h
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hx
      apply hξ
      rw [← hx.2, (hact x).2.1 h]
      simp [QF, BF]
    · intro x _
      exact hinv x
    · intro x _
      exact hbd x

end GlobalTheory.HilbertThetaSeries

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

theorem _root_.GlobalTheory.T.thetaSeries_congr_one_mod_p_of_isometry : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ) (κ : Type) [Fintype κ] [DecidableEq κ] (G S : Matrix κ κ ℤ) (t : ℕ), LatD p G S t → ∀ Φ : (κ → F) → ℂ, Good ι S Φ → Small ι (p : ℝ)⁻¹ (th G Φ - 1) := by
  first | exact @GlobalTheory.HilbertThetaSeries.th_congr_one | exact GlobalTheory.HilbertThetaSeries.th_congr_one | (intros; apply GlobalTheory.HilbertThetaSeries.th_congr_one <;> assumption)
end
end
