module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinWronskianNeZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JInvariantEqualSl2OrbitStatement
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.ReduceModChar
public import Mathlib.RingTheory.RootsOfUnity.Complex
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JInvariantEqualSl2OrbitStatement
import Mathlib.Algebra.Order.Star.Int
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinWronskianNeZeroStatement

section

@[expose] public section

open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

theorem _root_.GlobalTheory.T.eisenstein_wronskian_ne_zero : ∀ τ : ℍ, 2 * E₄ τ * deriv (⇑E₆ ∘ ofComplex) τ - 3 * E₆ τ * deriv (⇑E₄ ∘ ofComplex) τ ≠ 0 := by
  first | exact @GlobalTheory.EisWronskian.wronskian_E₄_E₆_ne_zero | exact GlobalTheory.EisWronskian.wronskian_E₄_E₆_ne_zero | (intros; apply GlobalTheory.EisWronskian.wronskian_E₄_E₆_ne_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.EllipticPointsStabilizer

section

@[expose] public section

open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory.EllipticZero

lemma denom_mul_SL (g h : SL(2, ℤ)) (z : ℍ) :
    denom ((g * h : SL(2, ℤ)) : GL (Fin 2) ℝ) z
      = denom (g : GL (Fin 2) ℝ) ((h • z : ℍ) : ℂ) * denom (h : GL (Fin 2) ℝ) z := by
  have hd : 0 < ((h : GL (Fin 2) ℝ)).det.val := by simp
  have := denom_cocycle (g : GL (Fin 2) ℝ) (h : GL (Fin 2) ℝ) z.im_ne_zero
  rw [← coe_smul_of_det_pos hd, ← ModularGroup.sl_moeb] at this
  rw [← this, map_mul, map_mul]

lemma conj_fix (γ u : SL(2, ℤ)) (σ : ℍ) (hu : u • σ = σ) :
    (γ * u * γ⁻¹) • (γ • σ) = γ • σ ∧
      denom ((γ * u * γ⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) ((γ • σ : ℍ) : ℂ)
        = denom (u : GL (Fin 2) ℝ) σ := by
  refine ⟨by rw [mul_smul, mul_smul, inv_smul_smul, hu], ?_⟩
  have h1 := denom_mul_SL (γ * u * γ⁻¹) γ σ
  have h2 := denom_mul_SL γ u σ
  rw [inv_mul_cancel_right, h2, hu, mul_comm] at h1
  exact (mul_right_cancel₀ (denom_ne_zero _ _) h1).symm

lemma eq_zero_of_fix {k : ℤ} (f : ModularForm 𝒮ℒ k) (u : SL(2, ℤ)) (σ : ℍ) (hu : u • σ = σ)
    (hk : denom (u : GL (Fin 2) ℝ) σ ^ k ≠ 1) : f σ = 0 := by
  have h : f (u • σ) = denom u σ ^ k * f σ :=
    SlashInvariantForm.slash_action_eqn'' f (by simp) σ
  rw [hu] at h
  have : (denom (u : GL (Fin 2) ℝ) σ ^ k - 1) * f σ = 0 := by linear_combination -h
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hk)

lemma exists_four : ∃ (σ : ℍ) (u : SL(2, ℤ)), u • σ = σ ∧
    IsPrimitiveRoot (denom (u : GL (Fin 2) ℝ) σ) 4 := by
  refine ⟨UpperHalfPlane.I, ModularGroup.S, ?_, ?_⟩
  · rw [modular_S_smul]; ext1; simp
  · rw [ModularGroup.denom_S]; exact Complex.isPrimitiveRoot_I

lemma exists_six : ∃ (σ : ℍ) (u : SL(2, ℤ)), u • σ = σ ∧
    IsPrimitiveRoot (denom (u : GL (Fin 2) ℝ) σ) 6 := by
  have hp := Complex.isPrimitiveRoot_exp 6 (by norm_num)
  set μ := Complex.exp (2 * Real.pi * Complex.I / (6 : ℕ)) with hμ
  have him : 0 < μ.im := by
    have : μ = Complex.exp (((Real.pi / 3 : ℝ) : ℂ) * Complex.I) := by
      rw [hμ]; congr 1; push_cast; ring
    rw [this, Complex.exp_ofReal_mul_I_im, Real.sin_pi_div_three]
    positivity
  have h6 : μ ^ 6 = 1 := hp.pow_eq_one
  have h3 : μ ^ 3 - 1 ≠ 0 := sub_ne_zero.2 (hp.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num))
  have h1 : μ + 1 ≠ 0 := fun h => by
    have := congrArg Complex.im h
    simp at this
    exact him.ne' this
  have hq : μ ^ 2 - μ + 1 = 0 := by
    have : (μ ^ 3 - 1) * ((μ + 1) * (μ ^ 2 - μ + 1)) = 0 := by linear_combination h6
    exact (mul_eq_zero.1 ((mul_eq_zero.1 this).resolve_left h3)).resolve_left h1
  have h0 : μ ≠ 0 := hp.ne_zero (by norm_num)
  refine ⟨⟨μ, him⟩, ModularGroup.T * ModularGroup.S, ?_, ?_⟩
  · rw [mul_smul, modular_S_smul, modular_T_smul]
    ext1
    simp only [coe_vadd]
    push_cast
    field_simp
    linear_combination -hq
  · rw [denom_mul_SL, ModularGroup.denom_S]
    have : ∀ z : ℍ, denom ((ModularGroup.T : SL(2, ℤ)) : GL (Fin 2) ℝ) z = 1 := fun z => by
      rw [ModularGroup.denom_apply]; simp [ModularGroup.T]
    rw [this, one_mul]
    exact hp

theorem elliptic_of_zero : ∀ τ₀ : ℍ,
    (E₆ τ₀ = 0 → ∃ u : SL(2, ℤ), u • τ₀ = τ₀ ∧ IsPrimitiveRoot (denom (u : GL (Fin 2) ℝ) τ₀) 4) ∧
    (E₄ τ₀ = 0 → ∃ u : SL(2, ℤ), u • τ₀ = τ₀ ∧
      IsPrimitiveRoot (denom (u : GL (Fin 2) ℝ) τ₀) 6) := by
  intro τ₀
  constructor
  · intro h
    obtain ⟨σ, u, hu, hp⟩ := exists_four
    have h0 : E₆ σ = 0 := eq_zero_of_fix E₆ u σ hu (by
      rw [Ne, hp.zpow_eq_one_iff_dvd]; norm_num)
    obtain ⟨γ, rfl⟩ := GlobalTheory.T.j_invariant_equal_sl2_orbit τ₀ σ (by rw [h, h0]; ring)
    obtain ⟨h1, h2⟩ := conj_fix γ u σ hu
    exact ⟨_, h1, h2 ▸ hp⟩
  · intro h
    obtain ⟨σ, u, hu, hp⟩ := exists_six
    have h0 : E₄ σ = 0 := eq_zero_of_fix E₄ u σ hu (by
      rw [Ne, hp.zpow_eq_one_iff_dvd]; norm_num)
    obtain ⟨γ, rfl⟩ := GlobalTheory.T.j_invariant_equal_sl2_orbit τ₀ σ (by rw [h, h0]; ring)
    obtain ⟨h1, h2⟩ := conj_fix γ u σ hu
    exact ⟨_, h1, h2 ▸ hp⟩

end GlobalTheory.EllipticZero
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.EllipticPointsStabilizerStatement

section

@[expose] public section

open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

theorem _root_.GlobalTheory.T.elliptic_points_stabilizer : ∀ τ₀ : ℍ, (E₆ τ₀ = 0 → ∃ u : SL(2, ℤ), u • τ₀ = τ₀ ∧ IsPrimitiveRoot (denom (u : GL (Fin 2) ℝ) τ₀) 4) ∧ (E₄ τ₀ = 0 → ∃ u : SL(2, ℤ), u • τ₀ = τ₀ ∧ IsPrimitiveRoot (denom (u : GL (Fin 2) ℝ) τ₀) 6) := by
  first | exact @GlobalTheory.EllipticZero.elliptic_of_zero | exact GlobalTheory.EllipticZero.elliptic_of_zero | (intros; apply GlobalTheory.EllipticZero.elliptic_of_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLevelOneSimpleZeroFormAtPoint

section

@[expose] public section

open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory.LevelOneLocal

theorem tendsto_E {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) :
    Tendsto (ModularForm.E hk : ℍ → ℂ) atImInfty (𝓝 1) := by
  have h0 : valueAtInfty (ModularForm.E hk : ℍ → ℂ) = 1 := by
    rw [← qExpansion_coeff_zero one_pos
      (ModularFormClass.analyticAt_cuspFunction_zero (ModularForm.E hk) one_pos one_mem_strictPeriods_SL)
      (SlashInvariantFormClass.periodic_comp_ofComplex (ModularForm.E hk) one_mem_strictPeriods_SL)]
    exact EisensteinSeries.E_qExpansion_coeff_zero hk hk2
  obtain ⟨c, hc, h⟩ := ModularFormClass.exp_decay_sub_atImInfty' (ModularForm.E hk)
  rw [h0] at h
  have h2 : Tendsto (fun τ : ℍ ↦ Real.exp (-c * τ.im)) atImInfty (𝓝 0) := by
    refine Real.tendsto_exp_atBot.comp ?_
    exact Tendsto.const_mul_atTop_of_neg (by linarith) tendsto_comap
  simpa using (h.trans_tendsto h2).add_const 1

theorem tendsto_E₄ : Tendsto (E₄ : ℍ → ℂ) atImInfty (𝓝 1) := tendsto_E _ ⟨2, rfl⟩

theorem tendsto_E₆ : Tendsto (E₆ : ℍ → ℂ) atImInfty (𝓝 1) := tendsto_E _ ⟨3, rfl⟩

theorem cube_sub_sq_ne_zero (τ : ℍ) : E₄ τ ^ 3 - E₆ τ ^ 2 ≠ 0 := by
  intro h
  apply ModularForm.discriminant_ne_zero τ
  rw [ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq, h, zero_div]

theorem isMF_E₄ : IsMF ⊤ 4 (E₄ : ℍ → ℂ) := isMF_coe_top E₄

theorem isMF_E₆ : IsMF ⊤ 6 (E₆ : ℍ → ℂ) := isMF_coe_top E₆

theorem differentiableAt_comp {f : ℍ → ℂ} (hf : MDiff f) (τ : ℍ) :
    DifferentiableAt ℂ (f ∘ ofComplex) τ :=
  mdifferentiableAt_iff.mp (hf τ)

theorem deriv_comb (α β : ℂ) (τ : ℍ) :
    deriv ((α • (E₄ : ℍ → ℂ) ^ 3 - β • (E₆ : ℍ → ℂ) ^ 2) ∘ ofComplex) τ =
      α * (3 * E₄ τ ^ 2 * deriv (⇑E₄ ∘ ofComplex) τ) - β * (2 * E₆ τ * deriv (⇑E₆ ∘ ofComplex) τ) := by
  have h4 := (differentiableAt_comp isMF_E₄.2.1 τ).hasDerivAt
  have h6 := (differentiableAt_comp isMF_E₆.2.1 τ).hasDerivAt
  have h := ((h4.fun_pow 3).const_mul α).fun_sub ((h6.fun_pow 2).const_mul β)
  have e : (α • (E₄ : ℍ → ℂ) ^ 3 - β • (E₆ : ℍ → ℂ) ^ 2) ∘ ofComplex =
      fun x => α * (⇑E₄ ∘ ofComplex) x ^ 3 - β * (⇑E₆ ∘ ofComplex) x ^ 2 := by
    ext x; simp
  rw [e, h.deriv]
  simp

theorem exists_local_data : ∀ τ₀ : ℍ, ∃ (n : ℕ) (a b : ℤ) (E : ℍ → ℂ) (u : SL(2, ℤ)), u • τ₀ = τ₀ ∧ 0 < n ∧ IsPrimitiveRoot (denom (u : GL (Fin 2) ℝ) τ₀) n ∧ a < b ∧ Even (b - a) ∧ IsMF ⊤ b E ∧ (∀ τ : ℍ, E τ = 0 → deriv (E ∘ ofComplex) τ ≠ 0 ∧ ∃ γ : SL(2, ℤ), τ = γ • τ₀) ∧ (∃ c : ℂ, c ≠ 0 ∧ Tendsto E atImInfty (𝓝 c)) ∧ ∀ d : ℤ, 0 ≤ d → (n : ℤ) ∣ d → ∃ e : ℍ → ℂ, IsMF ⊤ (d + a) e ∧ e τ₀ ≠ 0 := by
  intro τ₀
  have hD := cube_sub_sq_ne_zero τ₀
  by_cases h6 : E₆ τ₀ = 0
  · obtain ⟨u, hu, hp⟩ := (GlobalTheory.T.elliptic_points_stabilizer τ₀).1 h6
    have h4 : E₄ τ₀ ≠ 0 := fun h => hD (by simp [h, h6])
    refine ⟨4, 0, 6, E₆, u, hu, by norm_num, hp, by norm_num, by decide, isMF_E₆, fun τ hτ => ⟨?_, ?_⟩,
      ⟨1, one_ne_zero, tendsto_E₆⟩, ?_⟩
    · intro h
      exact GlobalTheory.T.eisenstein_wronskian_ne_zero τ (by simp [h, hτ])
    · exact GlobalTheory.T.j_invariant_equal_sl2_orbit τ τ₀ (by simp [h6, hτ])
    · rintro d hd ⟨m, rfl⟩
      obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ m by push_cast at hd; omega)
      refine ⟨(E₄ : ℍ → ℂ) ^ m, ?_, by simpa using fun h => absurd h h4⟩
      have := isMF_E₄.pow m
      convert this using 1
      push_cast; ring
  by_cases h4 : E₄ τ₀ = 0
  · obtain ⟨u, hu, hp⟩ := (GlobalTheory.T.elliptic_points_stabilizer τ₀).2 h4
    refine ⟨6, 0, 4, E₄, u, hu, by norm_num, hp, by norm_num, by decide, isMF_E₄, fun τ hτ => ⟨?_, ?_⟩,
      ⟨1, one_ne_zero, tendsto_E₄⟩, ?_⟩
    · intro h
      exact GlobalTheory.T.eisenstein_wronskian_ne_zero τ (by simp [h, hτ])
    · exact GlobalTheory.T.j_invariant_equal_sl2_orbit τ τ₀ (by simp [h4, hτ])
    · rintro d hd ⟨m, rfl⟩
      obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ m by push_cast at hd; omega)
      refine ⟨(E₆ : ℍ → ℂ) ^ m, ?_, by simpa using fun h => absurd h h6⟩
      have := isMF_E₆.pow m
      convert this using 1
      push_cast; ring
  refine ⟨2, 4, 12, (E₆ τ₀ ^ 2) • (E₄ : ℍ → ℂ) ^ 3 - (E₄ τ₀ ^ 3) • (E₆ : ℍ → ℂ) ^ 2, -1, ?_, by norm_num, ?_,
    by norm_num, by decide, ?_, fun τ hτ => ?_, ⟨E₆ τ₀ ^ 2 - E₄ τ₀ ^ 3, fun h => hD (by linear_combination -h), ?_⟩,
    ?_⟩
  · rw [ModularGroup.SL_neg_smul, one_smul]
  · have : denom ((-1 : SL(2, ℤ)) : GL (Fin 2) ℝ) τ₀ = -1 := by simp [denom]
    rw [this]
    exact IsPrimitiveRoot.neg_one 0 (by norm_num)
  · exact ((isMF_E₄.pow 3).smul _).sub ((isMF_E₆.pow 2).smul _)
  · have hz : E₆ τ₀ ^ 2 * E₄ τ ^ 3 - E₄ τ₀ ^ 3 * E₆ τ ^ 2 = 0 := by simpa using hτ
    refine ⟨?_, GlobalTheory.T.j_invariant_equal_sl2_orbit τ τ₀ (by linear_combination hz)⟩
    have hDτ := cube_sub_sq_ne_zero τ
    have k4 : E₄ τ ≠ 0 := by
      intro h
      have : E₆ τ = 0 := by simpa [h, h4] using hz
      exact hDτ (by simp [h, this])
    rw [deriv_comb]
    intro h
    have hW := GlobalTheory.T.eisenstein_wronskian_ne_zero τ
    apply mul_ne_zero (mul_ne_zero (pow_ne_zero 2 h6) (pow_ne_zero 3 k4)) hW
    linear_combination (2 * E₄ τ * deriv (⇑E₆ ∘ ofComplex) τ) * hz - (E₄ τ * E₆ τ) * h
  · have := ((tendsto_E₄.pow 3).const_mul (E₆ τ₀ ^ 2)).sub ((tendsto_E₆.pow 2).const_mul (E₄ τ₀ ^ 3))
    simp only [one_pow, mul_one] at this
    exact this
  · rintro d hd ⟨m, rfl⟩
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ m by push_cast at hd; omega)
    rcases Nat.even_or_odd' m with ⟨p, rfl | rfl⟩
    · refine ⟨(E₄ : ℍ → ℂ) ^ (p + 1), ?_, by simpa using h4⟩
      have := isMF_E₄.pow (p + 1)
      convert this using 1
      push_cast; ring
    · refine ⟨(E₄ : ℍ → ℂ) ^ p * E₆, (isMF_E₄.pow p).mul isMF_E₆ (by push_cast; ring), ?_⟩
      exact mul_ne_zero (pow_ne_zero p h4) h6

end GlobalTheory.LevelOneLocal
end
end
