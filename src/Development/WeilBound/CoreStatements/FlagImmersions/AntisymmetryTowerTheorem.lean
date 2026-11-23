module

public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
public import Mathlib.CategoryTheory.Category.Basic
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagDegreeWeightFormulaStatement
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagShiftTotalLinRootPowerStatement
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.PolarizationPolynomialCoeffBoundStatement
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.MvPolynomial.Funext
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.PolarizationPolynomialCoeffBoundStatement
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Tactic.Linter.Style

-- Source module: Development.WeilBound.CoreStatements.FlagImmersions.DegLApply

section

@[expose] public section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Top

noncomputable section

namespace RootFieldNumerics.Lin

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

def degL (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) : RP Ψ N →ₗ[ℝ] ℝ :=
  ((-1 : ℝ) ^ dimFl Ψ N) •
    ∑ σ : Ψ → Equiv.Perm (Fin N), (∏ τ, ((Equiv.Perm.sign (σ τ) : ℤ) : ℝ)) • lcoeff ℝ (permExp σ)

theorem degL_apply (F : RP Ψ N) : degL Ψ N F = degFl F := by
  simp only [degL, degFl, LinearMap.smul_apply, LinearMap.sum_apply, MvPolynomial.lcoeff_apply,
    smul_eq_mul]

def shL (j : ℕ) (τ : Ψ) : RP Ψ N →ₗ[ℝ] ℝ :=
  (degL Ψ N).comp (∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j),
    (pderiv (τ, i) : Derivation ℝ (RP Ψ N) (RP Ψ N)).toLinearMap)

theorem shL_apply (j : ℕ) (τ : Ψ) (F : RP Ψ N) : shL j τ F = Sh j τ F := by
  rw [shL, LinearMap.comp_apply, degL_apply, Sh]
  congr 1
  simp

def totL (τ : Ψ) : RP Ψ N →ₗ[ℝ] ℝ :=
  (degL Ψ N).comp (∑ i : Fin N, (pderiv (τ, i) : Derivation ℝ (RP Ψ N) (RP Ψ N)).toLinearMap)

theorem totL_apply (τ : Ψ) (F : RP Ψ N) : totL τ F = Tot τ F := by
  rw [totL, LinearMap.comp_apply, degL_apply, Tot]
  congr 1
  simp

end RootFieldNumerics.Lin
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.AntisymmetricPerturbationBound

section

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
open RootFieldNumerics

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem inv_linear_eval (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (l : MvPolynomial (Ψ × Fin N) ℝ)
    (hl : l ∈ GroundTheory.Heights₂.Heights.antisymInv Ψ N j) :
    ∃ a b : Ψ → ℝ, ∀ x : Ψ × Fin N → ℝ, eval x l =
      ∑ τ, (a τ - b τ) * ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), x (τ, i) +
        ∑ τ, b τ * ∑ i, x (τ, i) := by
  obtain ⟨h1, h2⟩ := hl
  rw [homogeneousSubmodule_one_eq_span_X] at h1
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 h1
  have hcoef : ∀ p, l.coeff (Finsupp.single p 1) = c p := by
    intro p
    rw [← hc, coeff_sum, Finset.sum_eq_single p]
    · simp
    · intro q _ hq
      rw [MvPolynomial.coeff_smul, coeff_X, if_neg, smul_zero]
      intro h
      exact hq (Finsupp.single_left_injective one_ne_zero h)
    · simp
  have hinv : ∀ τ (i k : Fin N), ((i : ℕ) < j ↔ (k : ℕ) < j) → c (τ, i) = c (τ, k) := by
    intro τ i k hik
    have hmem : Equiv.swap (τ, i) (τ, k) ∈ GroundTheory.Heights₂.Heights.antisymWeyl Ψ N j := by
      intro p
      rw [Equiv.swap_apply_def]
      split_ifs with e1 e2
      · subst e1
        exact ⟨rfl, hik.symm⟩
      · subst e2
        exact ⟨rfl, hik⟩
      · exact ⟨rfl, Iff.rfl⟩
    have h3 := coeff_rename_mapDomain _ (Equiv.swap (τ, i) (τ, k)).injective l (Finsupp.single (τ, i) 1)
    rw [h2 _ hmem, Finsupp.mapDomain_single, Equiv.swap_apply_left, hcoef, hcoef] at h3
    exact h3.symm
  have ha : ∀ τ, ∃ a : ℝ, ∀ i : Fin N, (i : ℕ) < j → c (τ, i) = a := by
    intro τ
    by_cases h : ∃ i : Fin N, (i : ℕ) < j
    · obtain ⟨i, hi⟩ := h
      exact ⟨c (τ, i), fun k hk => hinv τ k i (by simp [hi, hk])⟩
    · exact ⟨0, fun k hk => absurd ⟨k, hk⟩ h⟩
  have hb : ∀ τ, ∃ b : ℝ, ∀ i : Fin N, ¬ (i : ℕ) < j → c (τ, i) = b := by
    intro τ
    by_cases h : ∃ i : Fin N, ¬ (i : ℕ) < j
    · obtain ⟨i, hi⟩ := h
      exact ⟨c (τ, i), fun k hk => hinv τ k i (iff_of_false hk hi)⟩
    · exact ⟨0, fun k hk => absurd ⟨k, hk⟩ h⟩
  choose a ha using ha
  choose b hb using hb
  refine ⟨a, b, fun x => ?_⟩

  rw [← hc, map_sum, Fintype.sum_prod_type, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.sum_filter, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eval, eval_X]
  split_ifs with hi
  · rw [ha τ i hi]
    ring
  · rw [hb τ i hi]
    ring

theorem flagDeg_eq_delta (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : Ψ × Fin N → ℝ,
      flagDeg (fun τ i => x (τ, i) : Wt Ψ N) = c * eval x (GroundTheory.Heights₂.Heights.antisymDelta Ψ N) := by
  refine ⟨((dimFl Ψ N).factorial : ℝ) * ∏ _τ : Ψ, ∏ i : Fin N, ∏ k ∈ Finset.Ioi i, ((k : ℝ) - (i : ℝ))⁻¹, ?_, ?_⟩
  · refine mul_pos (by positivity) (Finset.prod_pos fun _ _ => Finset.prod_pos fun i _ =>
      Finset.prod_pos fun k hk => inv_pos.2 (sub_pos.2 ?_))
    exact_mod_cast (Finset.mem_Ioi.1 hk)
  · intro x
    rw [(GlobalTheory.T.flag_degree_weight_formula Ψ N _).1, mul_assoc]
    congr 1
    unfold GroundTheory.Heights₂.Heights.antisymDelta
    rw [map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_prod, ← Finset.prod_mul_distrib, ← Finset.prod_filter]
    refine Finset.prod_congr (by ext k; simp) fun k _ => ?_
    rw [map_sub, eval_X, eval_X, div_eq_inv_mul]

theorem cor_b_poly_functional : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (R : RP Ψ N →ₗ[ℝ] ℝ) (v ε : ℝ) (Pl l : MvPolynomial (Ψ × Fin N) ℝ), 0 < v → (∀ lam : Wt Ψ N, eval (fun x => lam x.1 x.2) Pl = R (linRoot lam ^ (dimFl Ψ N + 1))) → Pl.IsHomogeneous (dimFl Ψ N + 1) → l ∈ GroundTheory.Heights₂.Heights.antisymInv Ψ N j → (∀ m, |(Pl - GroundTheory.Heights₂.Heights.antisymDelta Ψ N * l).coeff m| ≤ ε) → ∃ α β : Ψ → ℝ, ∀ m : Ψ × Fin N →₀ ℕ, m.degree = dimFl Ψ N + 1 → |R (monomial m 1) + v * (∑ τ, (α τ - β τ) * Sh j τ (monomial m 1) + ∑ τ, β τ * Tot τ (monomial m 1))| ≤ ε := by
  intro Ψ _ _ N j R v ε Pl l hv hP _ hl hε
  obtain ⟨a, b, hab⟩ := inv_linear_eval Ψ N j l hl
  obtain ⟨c, hc0, hc⟩ := flagDeg_eq_delta Ψ N
  set K : ℝ := v * ((dimFl Ψ N : ℝ) + 1) * c with hK
  have hK0 : K ≠ 0 := by positivity
  refine ⟨fun τ => a τ / K, fun τ => b τ / K, fun m hm => ?_⟩
  let Φ : RP Ψ N →ₗ[ℝ] ℝ :=
    R + v • (∑ τ, (a τ / K - b τ / K) • Lin.shL j τ + ∑ τ, (b τ / K) • Lin.totL τ)
  have hΦ : ∀ F, Φ F = R F + v * (∑ τ, (a τ / K - b τ / K) * Sh j τ F + ∑ τ, b τ / K * Tot τ F) := by
    intro F
    simp only [Φ, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sum_apply, Lin.shL_apply,
      Lin.totL_apply, smul_eq_mul]
  obtain ⟨P', -, hP', -, hle⟩ := GlobalTheory.T.polarization_polynomial_coeff_bound (Ψ × Fin N) (dimFl Ψ N + 1) Φ
  have heq : P' = Pl - GroundTheory.Heights₂.Heights.antisymDelta Ψ N * l := by
    refine MvPolynomial.funext fun x => ?_
    have e1 : (-∑ y, C (x y) * X y : RP Ψ N) = linRoot (fun τ i => x (τ, i) : Wt Ψ N) := rfl
    have e2 := hP (fun τ i => x (τ, i))
    rw [hP', e1, hΦ, map_sub, map_mul, hab, ← e2]
    simp only [(GlobalTheory.T.flag_shift_total_lin_root_power Ψ N j _ _).1, (GlobalTheory.T.flag_shift_total_lin_root_power Ψ N j _ _).2, hc]
    rw [sub_eq_add_neg (eval x Pl)]
    congr 1
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun τ _ => ?_
    have hK' : v * ((dimFl Ψ N : ℝ) + 1) * c / K = 1 := div_self hK0
    generalize (∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), x (τ, i)) = s
    generalize (∑ i, x (τ, i)) = t
    generalize eval x (GroundTheory.Heights₂.Heights.antisymDelta Ψ N) = d
    linear_combination (-(d * ((a τ - b τ) * s + b τ * t))) * hK'
  have h := hle m hm
  rw [hΦ, heq] at h
  exact h.trans (hε m)

end GlobalTheory.CompanionTheory.Ar.Top
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.AntisymmetricPerturbationBoundStatement

section

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

theorem _root_.GlobalTheory.T.antisymmetric_perturbation_bound :
    ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (R : RP Ψ N →ₗ[ℝ] ℝ)
      (v ε : ℝ) (Pl l : MvPolynomial (Ψ × Fin N) ℝ),
      0 < v →
      (∀ lam : Wt Ψ N, eval (fun x => lam x.1 x.2) Pl = R (linRoot lam ^ (dimFl Ψ N + 1))) →
      Pl.IsHomogeneous (dimFl Ψ N + 1) →
      l ∈ GroundTheory.Heights₂.Heights.antisymInv Ψ N j →
      (∀ m, |AddMonoidAlgebra.coeff (Pl - GroundTheory.Heights₂.Heights.antisymDelta Ψ N * l) m| ≤ ε) →
      ∃ α β : Ψ → ℝ, ∀ m : Ψ × Fin N →₀ ℕ, m.degree = dimFl Ψ N + 1 →
        |R (monomial m 1) + v * (∑ τ, (α τ - β τ) * Sh j τ (monomial m 1) +
          ∑ τ, β τ * Tot τ (monomial m 1))| ≤ ε :=
  @GlobalTheory.CompanionTheory.Ar.Top.cor_b_poly_functional
end
end

-- Source module: Development.WeilBound.CoreStatements.FlagImmersions.AntisymmetryTowerTheorem

section

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

private theorem comp_swap_eq_swapWt {Ψ : Type} [DecidableEq Ψ] {N : ℕ} (x : Ψ × Fin N → ℝ) (τ : Ψ) (a b : Fin N) :
    x ∘ ⇑(Equiv.swap (τ, a) (τ, b)) = fun z : Ψ × Fin N => swapWt τ a b (fun s i => x (s, i)) z.1 z.2 := by
  funext z
  obtain ⟨s, i⟩ := z
  simp only [swapWt, Function.comp_apply, Equiv.swap_apply_def, Prod.mk.injEq]
  by_cases hs : s = τ
  · subst hs
    by_cases hia : i = a
    · subst hia
      simp
    · by_cases hib : i = b
      · subst hib
        simp [hia]
      · simp [hia, hib]
  · simp [hs]

private theorem inWall_and_dominant_of_eq_neighbors {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ} (hj0 : 1 ≤ j) (hjN : j < N)
    (τ : Ψ) (x : Ψ × Fin N → ℝ)
    (hx : x ∈ Metric.closedBall (fun y : Ψ × Fin N => -(1 / (4 * ((N : ℝ) + 1)) *
        (((y.2 : ℕ) : ℝ) - if y.1 = τ ∧ j ≤ (y.2 : ℕ) then 1 else 0))) (1 / (16 * ((N : ℝ) + 1))))
    (hxe : x (τ, ⟨j - 1, by omega⟩) = x (τ, ⟨j, hjN⟩)) :
    InWall j τ (1 / (8 * ((N : ℝ) + 1))) (fun s i => x (s, i)) ∧
      Dominant (Ψ := Ψ) (N := N) (fun s i => x (s, i)) := by
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = 1 / (4 * ((N : ℝ) + 1)) := ⟨_, rfl⟩
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have hδN : δ * ((N : ℝ) + 1) = 1 / 4 := by
    rw [hδ]
    field_simp
  have hr : 1 / (16 * ((N : ℝ) + 1)) = δ / 4 := by
    rw [hδ]
    field_simp
    ring
  have hc : 1 / (8 * ((N : ℝ) + 1)) = δ / 2 := by
    rw [hδ]
    field_simp
    ring
  rw [← hδ, hr] at hx
  rw [hc]
  have hb : ∀ (s : Ψ) (i : Fin N),
      |x (s, i) - -(δ * (((i : ℕ) : ℝ) - if s = τ ∧ j ≤ (i : ℕ) then 1 else 0))| ≤ δ / 4 := by
    intro s i
    have h1 := (dist_pi_le_iff (by linarith)).1 (Metric.mem_closedBall.1 hx) (s, i)
    rwa [Real.dist_eq] at h1
  have G : ∀ (s : Ψ) (a b : Fin N), (b : ℕ) = (a : ℕ) + 1 → ¬ (s = τ ∧ (b : ℕ) = j) →
      δ / 2 ≤ x (s, a) - x (s, b) := by
    intro s a b hab hn
    have hite : (if s = τ ∧ j ≤ (a : ℕ) then (1 : ℝ) else 0) = if s = τ ∧ j ≤ (b : ℕ) then 1 else 0 := by
      by_cases hs : s = τ
      · have hbj : (b : ℕ) ≠ j := fun h => hn ⟨hs, h⟩
        simp only [hs, true_and]
        split_ifs <;> first | rfl | (exfalso; omega)
      · simp [hs]
    have hbR : ((b : ℕ) : ℝ) = ((a : ℕ) : ℝ) + 1 := by exact_mod_cast hab
    have ha := abs_le.1 (hb s a)
    have hb2 := abs_le.1 (hb s b)
    rw [hite] at ha
    rw [hbR] at hb2
    linarith [ha.1, ha.2, hb2.1, hb2.2]
  have hcons : ∀ (s : Ψ) (a b : Fin N), (b : ℕ) = (a : ℕ) + 1 → x (s, b) ≤ x (s, a) := by
    intro s a b hab
    by_cases hs : s = τ ∧ (b : ℕ) = j
    · obtain ⟨rfl, hbj⟩ := hs
      have ha : a = ⟨j - 1, Nat.lt_of_le_of_lt (Nat.sub_le j 1) hjN⟩ := Fin.ext (show (a : ℕ) = j - 1 by omega)
      have hb' : b = ⟨j, hjN⟩ := Fin.ext hbj
      have e1 : x (s, b) = x (s, ⟨j, hjN⟩) := congrArg (fun i => x (s, i)) hb'
      have e2 : x (s, a) = x (s, ⟨j - 1, Nat.lt_of_le_of_lt (Nat.sub_le j 1) hjN⟩) :=
        congrArg (fun i => x (s, i)) ha
      rw [e1, e2]
      exact hxe.ge
    · have := G s a b hab hs
      linarith
  have hdom : ∀ (s : Ψ) (k : ℕ) (a b : Fin N), (b : ℕ) = (a : ℕ) + k → x (s, b) ≤ x (s, a) := by
    intro s k
    induction k with
    | zero =>
      intro a b h
      have : b = a := Fin.ext (by omega)
      rw [this]
    | succ k ih =>
      intro a b h
      have hbl := b.isLt
      have hc : (a : ℕ) + k < N := by omega
      exact le_trans (hcons s ⟨(a : ℕ) + k, hc⟩ b (show (b : ℕ) = (a : ℕ) + k + 1 by omega))
        (ih a ⟨(a : ℕ) + k, hc⟩ rfl)
  refine ⟨?_, ?_⟩
  · show _ ∧ _ ∧ _ ∧ _
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun s =>
        (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i => ?_
      show ‖x (s, i)‖ ≤ 1 / 2
      rw [Real.norm_eq_abs]
      have hiN : ((i : ℕ) : ℝ) ≤ N := by exact_mod_cast i.isLt.le
      have hI0 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) - (if s = τ ∧ j ≤ (i : ℕ) then 1 else 0) := by
        split_ifs with hh
        · have h1 : 1 ≤ (i : ℕ) := le_trans hj0 hh.2
          have h2 : (1 : ℝ) ≤ ((i : ℕ) : ℝ) := by exact_mod_cast h1
          linarith
        · simp
      have hI1 : ((i : ℕ) : ℝ) - (if s = τ ∧ j ≤ (i : ℕ) then 1 else 0) ≤ N := by
        split_ifs <;> linarith
      have hA := mul_nonneg hδpos.le hI0
      have hB := mul_le_mul_of_nonneg_left hI1 hδpos.le
      have h1 := abs_le.1 (hb s i)
      rw [abs_le]
      constructor <;> linarith [h1.1, h1.2]
    · simp only [gap, ent, dite_eq_left (show j - 1 < N by omega), dite_eq_left hjN]
      exact sub_eq_zero.2 hxe
    · intro τ' hτ'
      simp only [gap, ent, dite_eq_left (show j - 1 < N by omega), dite_eq_left hjN]
      exact G τ' ⟨j - 1, by omega⟩ ⟨j, hjN⟩ (show j = j - 1 + 1 by omega) (fun h => hτ' h.1)
    · intro s i hi hij
      simp only [ent, dite_eq_left (show i < N by omega), dite_eq_left hi]
      exact G s ⟨i, by omega⟩ ⟨i + 1, hi⟩ rfl (fun h => hij h.2)
  · intro s a b hab
    exact hdom s ((b : ℕ) - (a : ℕ)) a b (by have := Fin.le_iff_val_le_val.1 hab; omega)


open GroundTheory.Heights₂.Heights in
theorem antisymmetry_tower_theorem : GroundTheory.Heights₂.Heights.AntisymPerturbation.Statement → ∀ II : IntersectionSystem, ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (hh : RP Ψ N →ₗ[ℝ] ℝ), T.Proportional → T.ThmW II → T.I8 II hh → I9 (Ψ := Ψ) (N := N) hh → T.ThmB II hh := by
  intro hS II Ψ _ _ N T hh hprop hW h8 h9
  obtain ⟨hvol, -, -⟩ := hprop
  have hj0 : 1 ≤ T.j := T.j_pos
  have hjN : T.j < N := T.j_lt
  have hv : 0 < T.volT := by
    show 0 < ∑ c : T.Comp, T.vol c
    exact Finset.sum_pos (fun c _ => hvol c) Finset.univ_nonempty
  obtain ⟨h, hhom, hev, -, -⟩ := GlobalTheory.T.polarization_polynomial_coeff_bound (Ψ × Fin N) (dimFl Ψ N + 1) hh
  let x0 : Ψ → Ψ × Fin N → ℝ := fun τ y => -(1 / (4 * ((N : ℝ) + 1)) *
    (((y.2 : ℕ) : ℝ) - if y.1 = τ ∧ T.j ≤ (y.2 : ℕ) then 1 else 0))
  let K : Ψ → Set (Ψ × Fin N → ℝ) := fun τ =>
    diagHyperplane Ψ N τ ⟨T.j - 1, by omega⟩ ⟨T.j, hjN⟩ ∩ Metric.closedBall (x0 τ) (1 / (16 * ((N : ℝ) + 1)))
  have hK : ∀ τ : Ψ, IsCompact (K τ) ∧ K τ ⊆ diagHyperplane Ψ N τ ⟨T.j - 1, by omega⟩ ⟨T.j, hjN⟩ ∧
      (∃ O : Set (Ψ × Fin N → ℝ), IsOpen O ∧
        (O ∩ diagHyperplane Ψ N τ ⟨T.j - 1, by omega⟩ ⟨T.j, hjN⟩).Nonempty ∧
        O ∩ diagHyperplane Ψ N τ ⟨T.j - 1, by omega⟩ ⟨T.j, hjN⟩ ⊆ K τ) ∧
      ∀ x ∈ K τ, eval x h = 0 := by
    intro τ
    have hHc : IsClosed (diagHyperplane Ψ N τ ⟨T.j - 1, by omega⟩ ⟨T.j, hjN⟩) :=
      isClosed_eq (continuous_apply _) (continuous_apply _)
    refine ⟨(isCompact_closedBall _ _).inter_left hHc, Set.inter_subset_left,
      ⟨Metric.ball (x0 τ) (1 / (16 * ((N : ℝ) + 1))), Metric.isOpen_ball,
        ⟨x0 τ, Metric.mem_ball_self (by positivity), ?_⟩, ?_⟩, ?_⟩
    · show x0 τ (τ, ⟨T.j - 1, by omega⟩) = x0 τ (τ, ⟨T.j, hjN⟩)
      simp [x0, show ¬ T.j ≤ T.j - 1 by omega, Nat.cast_sub hj0]
    · rintro x ⟨hxO, hxH⟩
      exact ⟨hxH, Metric.ball_subset_closedBall hxO⟩
    · rintro x ⟨hxH, hxB⟩
      obtain ⟨-, hdom⟩ := inWall_and_dominant_of_eq_neighbors hj0 hjN τ x hxB hxH
      rw [hev x]
      exact h9.1 (fun s i => x (s, i)) hdom
        ⟨τ, ⟨T.j - 1, by omega⟩, ⟨T.j, hjN⟩, (show T.j = T.j - 1 + 1 by omega), hxH⟩
  obtain ⟨C0, hC⟩ := hS Ψ N T.j (by omega) hjN h K hK
  obtain ⟨CW, B₁, hB⟩ := hW (1 / (8 * ((N : ℝ) + 1))) (by positivity)
  unfold RootTower.ThmB
  refine ⟨C0 * CW, max B₁ 2, fun B hB₂ => ?_⟩
  have hB1 : B₁ ≤ B := le_trans (le_max_left _ _) hB₂
  have hB2 : 2 ≤ B := le_trans (le_max_right _ _) hB₂
  let L : RP Ψ N →ₗ[ℝ] ℝ :=
    ∑ c : T.Comp, ((T.M B c).PP II).comp (rename (some : Ψ × Fin N → Option (Ψ × Fin N))).toLinearMap
  have hL : ∀ F, L F = T.PPt II B F := by
    intro F
    simp [L, RootTower.PPt, RootTower.PPc, toA, LinearMap.sum_apply]
  obtain ⟨P, hPhom, hPev, -, -⟩ := GlobalTheory.T.polarization_polynomial_coeff_bound (Ψ × Fin N) (dimFl Ψ N + 1) L
  have hQev : ∀ x : Ψ × Fin N → ℝ, eval x (P - T.volT • h) =
      (L - T.volT • hh) ((-∑ z, MvPolynomial.C (x z) * X z) ^ (dimFl Ψ N + 1)) := by
    intro x
    rw [map_sub, MvPolynomial.smul_eval, hPev, hev]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
  have hQhom : (P - T.volT • h).IsHomogeneous (dimFl Ψ N + 1) :=
    (mem_homogeneousSubmodule _ _).1 (Submodule.sub_mem _ ((mem_homogeneousSubmodule _ _).2 hPhom)
      (Submodule.smul_mem _ _ ((mem_homogeneousSubmodule _ _).2 hhom)))
  have key : ∀ F, T.PPt II B F - T.volT * hh F = ∑ c, (T.PPc II B c F - T.vol c * hh F) := by
    intro F
    simp only [RootTower.PPt, RootTower.volT, Finset.sum_sub_distrib, Finset.sum_mul]
  have hanti : P - T.volT • h ∈ antisymSpace Ψ N T.j := by
    show _ ∧ _
    refine ⟨?_, ?_⟩
    · have hd : antisymDegree Ψ N + 1 = dimFl Ψ N + 1 := by
        simp only [antisymDegree, dimFl, Nat.choose_two_right]
      rw [hd]
      exact (mem_homogeneousSubmodule _ _).2 hQhom
    · rintro σ ⟨τ, a, b, hab, hj, rfl⟩
      have hbj : (b : ℕ) ≠ T.j := by omega
      apply MvPolynomial.funext
      intro x
      rw [eval_rename, map_neg, hQev, hQev, comp_swap_eq_swapWt x τ a b]
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hL]
      rw [key, key]
      have hsum := Finset.sum_congr rfl fun c (_ : c ∈ (Finset.univ : Finset T.Comp)) =>
        h8 B hB2 c τ a b hab hbj (fun s i => x (s, i))
      rw [Finset.sum_neg_distrib] at hsum
      exact hsum
  have hsmall : ∀ τ : Ψ, ∀ x ∈ K τ, |eval x P| ≤ CW * Real.log B / B := by
    rintro τ x ⟨hxH, hxB⟩
    obtain ⟨hwall, -⟩ := inWall_and_dominant_of_eq_neighbors hj0 hjN τ x hxB hxH
    rw [hPev x, hL]
    exact hB B hB1 τ (fun s i => x (s, i)) hwall
  obtain ⟨l, hl, hlc⟩ := hC P T.volT (CW * Real.log B / B) hanti hsmall
  obtain ⟨α, β, hαβ⟩ := GlobalTheory.T.antisymmetric_perturbation_bound Ψ N T.j (L - T.volT • hh) T.volT (C0 * (CW * Real.log B / B))
    (P - T.volT • h) l hv (fun lam => hQev _) hQhom hl hlc
  refine ⟨α, β, fun m hm => ?_⟩
  have h1 := hαβ m hm
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hL] at h1
  rw [show C0 * CW * Real.log B / B = C0 * (CW * Real.log B / B) by ring]
  refine (le_of_eq ?_).trans h1
  congr 1
  ring

end RootFieldNumerics
end
end
