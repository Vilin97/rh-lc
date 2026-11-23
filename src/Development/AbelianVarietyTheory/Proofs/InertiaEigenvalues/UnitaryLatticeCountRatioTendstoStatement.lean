module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
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
public import Mathlib.Data.Int.Interval
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FullLatticeSandwichBetweenIntegralElements
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualStableLatticeUnitOrbitsFiniteStatement
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Order.Filter.AtTopBot.Archimedean
public import Mathlib.Order.Filter.AtTopBot.Field
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Order.Field
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorusModIntegralUnitsStructureAndIntegralityStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorusOrbitLatticeCountBoundedByRhoStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UUEqSumOverTorusOrbitsStatement
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteAlgebraInvolutionRhoPowEqCardBox

section

@[expose] public section

open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma

theorem rho_pow_eq_card_box : ∀ (K : UQ) (B : InvAlg K) (a : K.O) (r : ℕ) (φ : B.T →* Multiplicative (Fin r → ℤ)) (c : Fin r → ℕ), Function.Surjective φ → (∀ t : B.T, φ t = 1 ↔ (t : B.Aˣ) ∈ intUnits K.O B.A) → (∀ (t : B.T) (k : ℕ), IsIntegral K.O ((((t : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * algebraMap K.O B.A a ^ k) ↔ ∀ i, |Multiplicative.toAdd (φ t) i| ≤ ((k * c i : ℕ) : ℤ)) → ∀ k : ℕ, B.rho (algebraMap K.O B.A a ^ k) = ∏ i, (2 * k * c i + 1) := by
  intro K B a r φ c hφ hker hint k
  have hK : (intUnits K.O B.A).subgroupOf B.T = φ.ker := by
    ext t
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hker]
  unfold InvAlg.rho
  rw [hK]
  let e := QuotientGroup.quotientKerEquivOfSurjective φ hφ
  have he : ∀ q : B.T ⧸ φ.ker, e q = φ (Quotient.out q) := by
    intro q
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  have h1 : Nat.card {q : B.T ⧸ φ.ker //
      IsIntegral K.O ((((Quotient.out q : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * algebraMap K.O B.A a ^ k : B.A)} =
      Nat.card {v : Fin r → ℤ // ∀ i, v i ∈ Set.Icc (-((k * c i : ℕ) : ℤ)) ((k * c i : ℕ) : ℤ)} := by
    apply Nat.card_congr
    refine (e.toEquiv.trans Multiplicative.toAdd).subtypeEquiv ?_
    intro q
    simp only [MulEquiv.toEquiv_eq_coe, Equiv.trans_apply, MulEquiv.coe_toEquiv, he, Set.mem_Icc, ← abs_le]
    exact hint _ k
  rw [h1, Nat.card_congr (Equiv.subtypePiEquivPi), Nat.card_pi]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h2 : Nat.card (Set.Icc (-((k * c i : ℕ) : ℤ)) ((k * c i : ℕ) : ℤ)) = 2 * k * c i + 1 := by
    rw [Nat.card_eq_card_toFinset, Set.toFinset_Icc, Int.card_Icc, show 2 * k * c i = 2 * (k * c i) by ring]
    omega
  exact h2

end GlobalTheory.UnitLemma
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteAlgebraInvolutionRhoPowEqCardBoxStatement

section

@[expose] public section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.finiteAlgebraInvolution_rho_pow_eq_card_box : ∀ (K : UQ) (B : InvAlg K) (a : K.O) (r : ℕ) (φ : B.T →* Multiplicative (Fin r → ℤ)) (c : Fin r → ℕ), Function.Surjective φ → (∀ t : B.T, φ t = 1 ↔ (t : B.Aˣ) ∈ intUnits K.O B.A) → (∀ (t : B.T) (k : ℕ), IsIntegral K.O ((((t : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * algebraMap K.O B.A a ^ k) ↔ ∀ i, |Multiplicative.toAdd (φ t) i| ≤ ((k * c i : ℕ) : ℤ)) → ∀ k : ℕ, B.rho (algebraMap K.O B.A a ^ k) = ∏ i, (2 * k * c i + 1) := by
  first | exact @GlobalTheory.UnitLemma.rho_pow_eq_card_box | exact GlobalTheory.UnitLemma.rho_pow_eq_card_box | (intros; apply GlobalTheory.UnitLemma.rho_pow_eq_card_box <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FullLatticeSandwichBetweenIntegralElementsStatement

section

@[expose] public section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.fullLattice_sandwich_between_integral_elements : ∀ (K : UQ) (B : InvAlg K), B.LieReg → ∀ a : K.O, K.Small a → ∀ L : Submodule K.O B.A, IsLat K.O K.E L → ∃ m : ℕ, ∀ n : ℕ, m ≤ n → (∀ y : B.A, IsIntegral K.O y → algebraMap K.O B.A a ^ n * y ∈ L) ∧ ∀ y ∈ L, IsIntegral K.O (algebraMap K.O B.A a ^ n * y) := by
  first | exact @GlobalTheory.UnitLemma.lattice_sandwich | exact GlobalTheory.UnitLemma.lattice_sandwich | (intros; apply GlobalTheory.UnitLemma.lattice_sandwich <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TendstoRatioBoxCountsProdOne

section

@[expose] public section

open Filter

namespace GlobalTheory

theorem ratio_box_counts_tendsto_one (r : ℕ) (c : Fin r → ℕ) (m : ℕ) :
    Filter.Tendsto (fun k : ℕ => ((∏ i, (2 * (k + m) * c i + 1) : ℕ) : ℝ) /
      ((∏ i, (2 * k * c i + 1) : ℕ) : ℝ)) Filter.atTop (nhds 1) := by
  have key : ∀ i, Tendsto (fun k : ℕ => ((2 * (k + m) * c i + 1 : ℕ) : ℝ) /
      ((2 * k * c i + 1 : ℕ) : ℝ)) atTop (nhds 1) := by
    intro i
    rcases Nat.eq_zero_or_pos (c i) with h | h
    · simp [h]
    · have hc : (0:ℝ) < c i := by exact_mod_cast h
      have hden : Tendsto (fun k : ℕ => ((2 * k * c i + 1 : ℕ) : ℝ)) atTop atTop := by
        push_cast
        apply tendsto_atTop_add_const_right
        exact (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0:ℝ) < 2)).atTop_mul_const hc
      have h0 : Tendsto (fun k : ℕ => (2 * m * c i : ℝ) / ((2 * k * c i + 1 : ℕ) : ℝ)) atTop (nhds 0) :=
        tendsto_const_nhds.div_atTop hden
      have h1 := (tendsto_const_nhds (x := (1:ℝ))).add h0
      rw [add_zero] at h1
      refine h1.congr (fun k => ?_)
      have hpos : ((2 * k * c i + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp
      push_cast
      ring
  have h := tendsto_finsetProd (Finset.univ : Finset (Fin r)) (fun i _ => key i)
  simp only [Finset.prod_const_one] at h
  refine h.congr (fun k => ?_)
  rw [Nat.cast_prod, Nat.cast_prod, Finset.prod_div_distrib]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TendstoRatioBoxCountsProdOneStatement

section

@[expose] public section

open Filter

theorem _root_.GlobalTheory.T.tendsto_ratio_box_counts_prod_one : ∀ (r : ℕ) (c : Fin r → ℕ) (m : ℕ), Filter.Tendsto (fun k : ℕ => ((∏ i, (2 * (k + m) * c i + 1) : ℕ) : ℝ) / ((∏ i, (2 * k * c i + 1) : ℕ) : ℝ)) Filter.atTop (nhds 1) := by
  first | exact @GlobalTheory.ratio_box_counts_tendsto_one | exact GlobalTheory.ratio_box_counts_tendsto_one | (intros; apply GlobalTheory.ratio_box_counts_tendsto_one <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryLatticeCountRatioTendsto

section

@[expose] public section

open GlobalTheory.UnitLemma Polynomial Filter Topology

namespace GlobalTheory.UnitLemma

theorem unitaryLimit : UnitaryLimit := by
  have L0 := GlobalTheory.T.selfDual_stable_lattice_unit_orbits_finite
  have S1 := GlobalTheory.T.fullLattice_sandwich_between_integral_elements
  have S2 := GlobalTheory.T.torus_orbit_lattice_count_bounded_by_rho
  have S3 := GlobalTheory.T.UU_eq_sum_over_torus_orbits
  have S4 := GlobalTheory.T.torus_mod_integralUnits_structure_and_integrality
  have S5 := GlobalTheory.T.finiteAlgebraInvolution_rho_pow_eq_card_box
  have S6 := GlobalTheory.T.tendsto_ratio_box_counts_prod_one

  intro K B hB a ha x hx
  classical
  obtain ⟨r, φ, c, hsurj, hker, hc, hint⟩ := S4 K B hB a ha
  have hrho : ∀ k : ℕ, B.rho (algebraMap K.O B.A a ^ k) = ∏ i, (2 * k * c i + 1) :=
    S5 K B a r φ c hsurj hker hint
  have hpos : ∀ j : ℕ, 0 < B.rho (algebraMap K.O B.A a ^ j) := fun j => by
    rw [hrho]; exact Finset.prod_pos fun i _ => by omega
  obtain ⟨hfin, hstab⟩ := L0 K B hB.2 x hx.1 hx.2
  choose m hm using fun o : Orb K.O B.T (B.X x) => S1 K B hB a ha _ (Quot.out o).2.1
  haveI := Fintype.ofFinite (Orb K.O B.T (B.X x))
  set M := Finset.univ.sup m with hMdef
  have hmM : ∀ o, m o ≤ M := fun o => Finset.le_sup (Finset.mem_univ o)
  have key := fun (k : ℕ) (hk : M ≤ k) (o : Orb K.O B.T (B.X x)) =>
    S2 K B _ (hstab _ (Quot.out o).2).1 (hstab _ (Quot.out o).2).2 a hpos M k hk
      (hm o M (hmM o)).1 (hm o M (hmM o)).2
  have hUU : ∀ k, M ≤ k → (B.UU x (algebraMap K.O B.A a ^ k) : ℝ) =
      ∑ o : Orb K.O B.T (B.X x), (Nat.card {L' : Submodule K.O B.A // (∃ t ∈ B.T, L' = mulLat K.O (t : B.A) (Quot.out o).1) ∧
        algebraMap K.O B.A a ^ k ∈ L'} : ℝ) := by
    intro k hk
    rw [S3 K B x _ hfin (fun o => (key k hk o).1), finsum_eq_sum_of_fintype]
    push_cast; rfl
  have hN : (B.N x : ℝ) = ∑ o : Orb K.O B.T (B.X x),
      (((stabLat K.O (Quot.out o).1 ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) : ℕ) : ℝ) := by
    unfold InvAlg.N orbSum
    rw [finsum_eq_sum_of_fintype]
    push_cast
    simp
  have hlo : ∀ k, M ≤ k → (B.N x : ℝ) * B.rho (algebraMap K.O B.A a ^ (k - M)) ≤ B.UU x (algebraMap K.O B.A a ^ k) := by
    intro k hk
    rw [hUU k hk, hN, Finset.sum_mul]
    refine Finset.sum_le_sum fun o _ => ?_
    exact_mod_cast (key k hk o).2.1
  have hhi : ∀ k, M ≤ k → (B.UU x (algebraMap K.O B.A a ^ k) : ℝ) ≤ (B.N x : ℝ) * B.rho (algebraMap K.O B.A a ^ (k + M)) := by
    intro k hk
    rw [hUU k hk, hN, Finset.sum_mul]
    refine Finset.sum_le_sum fun o _ => ?_
    exact_mod_cast (key k hk o).2.2
  have hposR : ∀ j, (0 : ℝ) < B.rho (algebraMap K.O B.A a ^ j) := fun j => by exact_mod_cast hpos j
  have hup : Tendsto (fun k : ℕ => (B.N x : ℝ) * B.rho (algebraMap K.O B.A a ^ (k + M)) / B.rho (algebraMap K.O B.A a ^ k)) atTop (𝓝 (B.N x : ℝ)) := by
    have := (S6 r c M).const_mul (B.N x : ℝ)
    rw [mul_one] at this
    refine this.congr fun k => ?_
    rw [hrho, hrho, mul_div_assoc]
  have hdown : Tendsto (fun k : ℕ => (B.N x : ℝ) * B.rho (algebraMap K.O B.A a ^ (k - M)) / B.rho (algebraMap K.O B.A a ^ k)) atTop (𝓝 (B.N x : ℝ)) := by
    have h1 := ((S6 r c M).inv₀ one_ne_zero).comp (tendsto_sub_atTop_nat M)
    have h2 := h1.const_mul (B.N x : ℝ)
    rw [inv_one, mul_one] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_ge_atTop M] with k hk
    simp only [Function.comp_apply, inv_div]
    rw [Nat.sub_add_cancel hk, hrho, hrho, mul_div_assoc]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hdown hup ?_ ?_
  · filter_upwards [eventually_ge_atTop M] with k hk
    exact div_le_div_of_nonneg_right (hlo k hk) (hposR k).le
  · filter_upwards [eventually_ge_atTop M] with k hk
    exact div_le_div_of_nonneg_right (hhi k hk) (hposR k).le

end GlobalTheory.UnitLemma
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryLatticeCountRatioTendstoStatement

section

@[expose] public section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.unitary_lattice_count_ratio_tendsto : UnitaryLimit := by
  first | exact @GlobalTheory.UnitLemma.unitaryLimit | exact GlobalTheory.UnitLemma.unitaryLimit | (intros; apply GlobalTheory.UnitLemma.unitaryLimit <;> assumption)
end
end
