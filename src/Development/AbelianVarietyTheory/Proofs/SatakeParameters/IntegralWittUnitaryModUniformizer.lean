module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DvdPowZeroIff
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqZeroOfForallDvdPow
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HermitianIntegralVectorsPairingStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvMemDoubleCosetAndComm
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MulSelfEqOneIffOfLinearOrderedCommGroupWithZero
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Algebra.Order.Star.Int

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLimitDvdUniformizerPowCauchy

section

@[expose] public section

open Matrix Filter Topology

namespace GlobalTheory.Hk3.IntWittBase

open Formalism.UG GlobalTheory.Hk3.IntWitt

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem val_lt_exp_of_dvdPow_succ {ϖ x : L}
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    {N : ℕ} (hx : DvdPow ϖ (N + 1) x) : Valued.v x < WithZero.exp (-(N : ℤ)) := by
  obtain ⟨b, hb, hxb⟩ := hx
  rw [hxb, map_mul, map_pow, hϖ]
  calc (WithZero.exp (-1 : ℤ)) ^ (N + 1) * Valued.v b ≤ (WithZero.exp (-1 : ℤ)) ^ (N + 1) * 1 :=
        mul_le_mul' le_rfl hb
    _ = WithZero.exp (-((N + 1 : ℕ) : ℤ)) := by
        rw [mul_one, ← WithZero.exp_nsmul]; congr 1; push_cast; ring
    _ < WithZero.exp (-(N : ℤ)) := WithZero.exp_lt_exp.2 (by push_cast; omega)

theorem isClosed_dvdPow_sub {ϖ : L} (h0 : ϖ ≠ 0) (m : ℕ) (c : L) : IsClosed {x : L | DvdPow ϖ m (x - c)} := by
  have hp : ϖ ^ m ≠ 0 := pow_ne_zero _ h0
  have he : {x : L | DvdPow ϖ m (x - c)} =
      (fun x => (ϖ ^ m)⁻¹ * (x - c)) ⁻¹' ((Valued.v (R := L)).integer : Set L) := by
    ext x
    constructor
    · rintro ⟨b, hb, hxb⟩
      show Valued.v ((ϖ ^ m)⁻¹ * (x - c)) ≤ 1
      rw [hxb, inv_mul_cancel_left₀ hp]; exact hb
    · intro hx
      exact ⟨(ϖ ^ m)⁻¹ * (x - c), hx, by rw [mul_inv_cancel_left₀ hp]⟩
  rw [he]
  exact (Valued.isClosed_integer L).preimage (by fun_prop)

theorem exists_limit_dvdPow (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L)
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (a : ℕ → L) (ha : ∀ k, DvdPow ϖ (k + 1) (a (k + 1) - a k)) :
    ∃ b : L, ∀ k, DvdPow ϖ (k + 1) (b - a k) := by
  have h0 : ϖ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hϖ
    exact WithZero.zero_ne_coe hϖ
  have hint : ϖ ∈ intL L := by
    show Valued.v ϖ ≤ 1
    rw [hϖ]
    show WithZero.exp (-1 : ℤ) ≤ WithZero.exp 0
    exact WithZero.exp_le_exp.2 (by omega)
  have hstep : ∀ k m, k ≤ m → DvdPow ϖ (k + 1) (a m - a k) := by
    intro k m hkm
    induction m, hkm using Nat.le_induction with
    | base => rw [sub_self]; exact dvdPow_zero ϖ _
    | succ m hkm ih =>
      have := dvdPow_add (dvdPow_mono hint (Nat.succ_le_succ hkm) (ha m)) ih
      rwa [sub_add_sub_cancel] at this
  have hc : CauchySeq a := by
    rw [(Valued.hasBasis_uniformity L (WithZero (Multiplicative ℤ))).cauchySeq_iff]
    intro γ _
    have hγ : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ (0 : WithZero (Multiplicative ℤ)) := by
      simp
    obtain ⟨e, he⟩ : ∃ e, MonoidWithZeroHom.ValueGroup₀.embedding γ.1 = WithZero.exp e :=
      ⟨_, (WithZero.exp_log hγ).symm⟩
    refine ⟨(-e).toNat, fun m hm n hn => ?_⟩
    show Valued.v.restrict (a n - a m) < γ.1
    rw [Valuation.restrict_lt_iff_lt_embedding, he]
    have h1 := dvdPow_sub (hstep _ n hn) (hstep _ m hm)
    rw [sub_sub_sub_cancel_right] at h1
    refine (val_lt_exp_of_dvdPow_succ hϖ h1).trans_le (WithZero.exp_le_exp.2 ?_)
    have := Int.self_le_toNat (-e)
    omega
  obtain ⟨b, hb⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨b, fun k => ?_⟩
  exact (isClosed_dvdPow_sub h0 (k + 1) (a k)).mem_of_tendsto hb
    (eventually_atTop.2 ⟨k, fun m hm => hstep k m hm⟩)

end GlobalTheory.Hk3.IntWittBase
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLimitDvdUniformizerPowCauchyStatement

section

@[expose] public section

open Matrix

theorem _root_.GlobalTheory.T.exists_limit_dvdUniformizerPow_cauchy : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L),
    Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) →
    ∀ a : ℕ → L, (∀ k, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (k + 1) (a (k + 1) - a k)) →
    ∃ b : L, ∀ k, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (k + 1) (b - a k) := by
  first | exact @GlobalTheory.Hk3.IntWittBase.exists_limit_dvdPow | exact GlobalTheory.Hk3.IntWittBase.exists_limit_dvdPow | (intros; apply GlobalTheory.Hk3.IntWittBase.exists_limit_dvdPow <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryGroupNewtonLiftStep

section

@[expose] public section

open Matrix

noncomputable section

namespace GlobalTheory.Hk3.UnitaryNewton

open Formalism.UG GlobalTheory.Hk3.IntWitt GlobalTheory.Hk3.IntWittBase

variable {L : Type} [Field L]

theorem cT_smul' (σ : L →+* L) {n : ℕ} (s : L) (A : Matrix (Fin n) (Fin n) L) :
    cT σ (s • A) = σ s • cT σ A := by ext i j; simp [cT]

theorem cT_add' (σ : L →+* L) {n : ℕ} (A B : Matrix (Fin n) (Fin n) L) :
    cT σ (A + B) = cT σ A + cT σ B := by ext i j; simp [cT]

theorem cT_cT' {σ : L →+* L} (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (A : Matrix (Fin n) (Fin n) L) :
    cT σ (cT σ A) = A := by ext i j; simp [cT, hσ]

theorem newton_identity {n : ℕ} (s c : L) (hc : c + c = 1) (Gc g J X Xc E : Matrix (Fin n) (Fin n) L)
    (h1 : Gc * J * g = J + s • E) (h2 : J * X = -(c • E)) (h3 : Xc * J = -(c • E)) :
    (Gc + s • (Xc * Gc)) * J * (g + s • (g * X)) - J =
      (s * s) • (E * X + Xc * E + Xc * (Gc * J * g) * X) := by
  have e : (Gc + s • (Xc * Gc)) * J * (g + s • (g * X)) =
      Gc * J * g + s • (Gc * J * g * X) + s • (Xc * (Gc * J * g)) + (s * s) • (Xc * (Gc * J * g) * X) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc, smul_add]
    abel
  rw [e]
  nth_rewrite 1 [h1]; nth_rewrite 1 [h1]; nth_rewrite 1 [h1]
  rw [Matrix.add_mul, Matrix.mul_add, h2, h3, Matrix.smul_mul, Matrix.mul_smul]
  have hE : (c + c) • E = (1 : L) • E := by rw [hc]
  linear_combination (norm := module) (-s) • hE

end GlobalTheory.Hk3.UnitaryNewton

end

namespace GlobalTheory.Hk3.UnitaryNewton

open Formalism.UG GlobalTheory.Hk3.IntWitt GlobalTheory.Hk3.IntWittBase

theorem newton_step : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → ∀ (n : ℕ) (J : GL (Fin n) L), J ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) →
    (∀ i j, σ ((J : Matrix (Fin n) (Fin n) L) i j) = (J : Matrix (Fin n) (Fin n) L) j i) →
    ∀ (k : ℕ) (g : Matrix (Fin n) (Fin n) L), (∀ i j, g i j ∈ Formalism.UG.intL L) →
    (∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (k + 1)
      ((Formalism.UG.cT σ g * (J : Matrix (Fin n) (Fin n) L) * g - (J : Matrix (Fin n) (Fin n) L)) i j)) →
    ∃ g' : Matrix (Fin n) (Fin n) L, (∀ i j, g' i j ∈ Formalism.UG.intL L) ∧
      (∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (k + 1) (g' i j - g i j)) ∧
      ∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (k + 2)
        ((Formalism.UG.cT σ g' * (J : Matrix (Fin n) (Fin n) L) * g' - (J : Matrix (Fin n) (Fin n) L)) i j) := by
  intro L _ _ ϖ σ q hU hq n J hJ hJh k g hg hD
  have h2 : Valued.v (2 : L) = 1 := GlobalTheory.Hk3.Inh.v_two hU hq
  obtain ⟨hσσ, hσv, hσϖ, hϖv, -⟩ := hU
  set Jm : Matrix (Fin n) (Fin n) L := (J : Matrix (Fin n) (Fin n) L) with hJm
  set Ji : Matrix (Fin n) (Fin n) L := ((J⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hJidef
  have hJi : Ji * Jm = 1 := by rw [hJm, hJidef, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hJi' : Jm * Ji = 1 := by rw [hJm, hJidef, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  obtain ⟨g0, hg0⟩ := hJ
  have hJI : ∀ i j, Jm i j ∈ intL L := by
    intro i j; rw [hJm, ← hg0]; exact ((g0 : Matrix (Fin n) (Fin n) (intL L)) i j).2
  have hJiI : ∀ i j, Ji i j ∈ intL L := by
    intro i j; rw [hJidef, ← hg0, ← map_inv]
    exact (((g0⁻¹ : GL (Fin n) (intL L)) : Matrix (Fin n) (Fin n) (intL L)) i j).2
  have hJc : cT σ Jm = Jm := by ext i j; rw [cT_apply]; exact hJh j i
  have hJic : cT σ Ji = Ji := by
    have h : cT σ Ji * Jm = 1 := by rw [← hJc, ← cT_mul, hJi', cT_one]
    calc cT σ Ji = cT σ Ji * Jm * Ji := by rw [Matrix.mul_assoc, hJi', Matrix.mul_one]
      _ = Ji := by rw [h, Matrix.one_mul]
  unfold DvdPow at hD
  choose E hE hEeq using hD
  set s : L := ϖ ^ (k + 1) with hs
  have hϖ0 : ϖ ≠ 0 := by
    intro h0; rw [h0, map_zero] at hϖv; exact WithZero.zero_ne_coe hϖv
  have hϖI : ϖ ∈ intL L := by
    show Valued.v ϖ ≤ 1
    rw [hϖv]; exact_mod_cast (show (Multiplicative.ofAdd (-1 : ℤ)) ≤ 1 from by decide)
  have hs0 : s ≠ 0 := pow_ne_zero _ hϖ0
  have hσs : σ s = s := by rw [hs, map_pow, hσϖ]
  have hsI : s ∈ intL L := (intL L).pow_mem hϖI _
  set Em : Matrix (Fin n) (Fin n) L := Matrix.of E with hEm
  have hEmI : ∀ i j, Em i j ∈ intL L := hE
  have hDE : cT σ g * Jm * g = Jm + s • Em := by
    ext i j
    have := hEeq i j
    rw [Matrix.sub_apply] at this
    rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hEm, Matrix.of_apply, ← this]; ring
  have hEh : cT σ Em = Em := by
    have h := congrArg (cT σ) hDE
    rw [cT_mul, cT_mul, cT_cT' hσσ, hJc, cT_add', cT_smul', hσs, hJc, ← Matrix.mul_assoc, hDE] at h
    exact (smul_right_injective _ hs0 (add_left_cancel h)).symm
  have h20 : (2 : L) ≠ 0 := by intro h0; rw [h0, map_zero] at h2; exact zero_ne_one h2
  set c : L := (2 : L)⁻¹ with hcdef
  have hc : c + c = 1 := by rw [← two_mul, hcdef, mul_inv_cancel₀ h20]
  have hσc : σ c = c := by rw [hcdef, map_inv₀, map_ofNat]
  have hcI : c ∈ intL L := by
    show Valued.v c ≤ 1
    rw [hcdef, map_inv₀, h2, inv_one]
  set X : Matrix (Fin n) (Fin n) L := (-c) • (Ji * Em) with hX
  have hXI : ∀ i j, X i j ∈ intL L := by
    intro i j; rw [hX, Matrix.smul_apply, smul_eq_mul]
    exact mul_mem (neg_mem hcI) (int_mul hJiI hEmI i j)
  have hXc : cT σ X = (-c) • (Em * Ji) := by
    rw [hX, cT_smul', cT_mul, hEh, hJic, map_neg, hσc]
  have hJX : Jm * X = -(c • Em) := by
    rw [hX, Matrix.mul_smul, ← Matrix.mul_assoc, hJi', Matrix.one_mul, neg_smul]
  have hXJ : cT σ X * Jm = -(c • Em) := by
    rw [hXc, Matrix.smul_mul, Matrix.mul_assoc, hJi, Matrix.mul_one, neg_smul]
  refine ⟨g + s • (g * X), ?_, ?_, ?_⟩
  · intro i j
    rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    exact add_mem (hg i j) (mul_mem hsI (int_mul hg hXI i j))
  · intro i j
    refine ⟨(g * X) i j, int_mul hg hXI i j, ?_⟩
    rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]; ring
  · have hg'c : cT σ (g + s • (g * X)) = cT σ g + s • (cT σ X * cT σ g) := by
      rw [cT_add', cT_smul', hσs, cT_mul]
    have key := newton_identity s c hc (cT σ g) g Jm X (cT σ X) Em hDE hJX hXJ
    rw [hg'c, key]
    have hgc : ∀ i j, cT σ g i j ∈ intL L := int_cT hσv hg
    have hXcI : ∀ i j, cT σ X i j ∈ intL L := int_cT hσv hXI
    have hR : ∀ i j, (Em * X + cT σ X * Em + cT σ X * (cT σ g * Jm * g) * X) i j ∈ intL L := by
      intro i j
      rw [Matrix.add_apply, Matrix.add_apply]
      exact add_mem (add_mem (int_mul hEmI hXI i j) (int_mul hXcI hEmI i j))
        (int_mul (int_mul hXcI (int_mul (int_mul hgc hJI) hg)) hXI i j)
    intro i j
    refine ⟨ϖ ^ k * (Em * X + cT σ X * Em + cT σ X * (cT σ g * Jm * g) * X) i j,
      mul_mem ((intL L).pow_mem hϖI _) (hR i j), ?_⟩
    rw [Matrix.smul_apply, smul_eq_mul, hs]; ring

end GlobalTheory.Hk3.UnitaryNewton
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryGroupNewtonLiftStepStatement

section

@[expose] public section

open Matrix

theorem _root_.GlobalTheory.T.unitaryGroup_newton_lift_step : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → ∀ (n : ℕ) (J : GL (Fin n) L), J ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) →
    (∀ i j, σ ((J : Matrix (Fin n) (Fin n) L) i j) = (J : Matrix (Fin n) (Fin n) L) j i) →
    ∀ (k : ℕ) (g : Matrix (Fin n) (Fin n) L), (∀ i j, g i j ∈ Formalism.UG.intL L) →
    (∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (k + 1)
      ((Formalism.UG.cT σ g * (J : Matrix (Fin n) (Fin n) L) * g - (J : Matrix (Fin n) (Fin n) L)) i j)) →
    ∃ g' : Matrix (Fin n) (Fin n) L, (∀ i j, g' i j ∈ Formalism.UG.intL L) ∧
      (∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (k + 1) (g' i j - g i j)) ∧
      ∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (k + 2)
        ((Formalism.UG.cT σ g' * (J : Matrix (Fin n) (Fin n) L) * g' - (J : Matrix (Fin n) (Fin n) L)) i j) := by
  first | exact @GlobalTheory.Hk3.UnitaryNewton.newton_step | exact GlobalTheory.Hk3.UnitaryNewton.newton_step | (intros; apply GlobalTheory.Hk3.UnitaryNewton.newton_step <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralWittUnitaryModUniformizer

section

@[expose] public section

open Matrix

namespace GlobalTheory.Hk3.IntWittBase

open Formalism.UG GlobalTheory.Hk3.IntWitt

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem witt_mod_base : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → ∀ (n' : ℕ) (JT : GL (Fin n') L),
    JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ (ι : Type) [Fintype ι] (z z' : ι → Fin n' → L), (∀ i r, z i r ∈ Formalism.UG.intL L) → (∀ i r, z' i r ∈ Formalism.UG.intL L) →
    GlobalTheory.Hk3.IntWitt.IndepMod ϖ z → GlobalTheory.Hk3.IntWitt.IndepMod ϖ z' →
    (∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 (Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (z' i) (z' j) - Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (z i) (z j))) →
    ∃ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
      ∀ i r, GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 ((((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ z i) r - z' i r) := by
  intro L _ _ _ ϖ σ q hU hq n' JT hJ hJh ι _ z z' hz hz' hi hi' hgr
  classical
  obtain ⟨g₀, hg₀i, hg₀u, hg₀z⟩ := GlobalTheory.T.hermitian_integral_vectors_pairing L ϖ σ q hU hq n' JT hJ hJh ι z z' hz hz' hi hi' hgr
  have hstep := GlobalTheory.T.unitaryGroup_newton_lift_step L ϖ σ q hU hq n' JT hJ hJh
  obtain ⟨hσσ, hσv, hσϖ, hϖv, -, -, -⟩ := hU
  set J : Matrix (Fin n') (Fin n') L := (JT : Matrix (Fin n') (Fin n') L) with hJdef
  have hJi : ∀ i j, J i j ∈ intL L := by
    obtain ⟨k0, hk0⟩ := hJ
    intro i j; rw [hJdef, ← hk0]; exact ((k0 : Matrix (Fin n') (Fin n') (intL L)) i j).2

  let P : ℕ → Matrix (Fin n') (Fin n') L → Prop := fun k g =>
    (∀ i j, g i j ∈ intL L) ∧ ∀ i j, DvdPow ϖ (k + 1) ((cT σ g * J * g - J) i j)
  have hex : ∀ (k : ℕ) (g : Matrix (Fin n') (Fin n') L), ∃ g' : Matrix (Fin n') (Fin n') L,
      P k g → P (k + 1) g' ∧ ∀ i j, DvdPow ϖ (k + 1) (g' i j - g i j) := by
    intro k g
    by_cases hP : P k g
    · obtain ⟨g', h1, h2, h3⟩ := hstep k g hP.1 hP.2
      exact ⟨g', fun _ => ⟨⟨h1, h3⟩, h2⟩⟩
    · exact ⟨g, fun h => absurd h hP⟩
  choose F hF using hex
  let f : ℕ → Matrix (Fin n') (Fin n') L := fun k => Nat.rec g₀ (fun k g => F k g) k
  have hf0 : f 0 = g₀ := rfl
  have hfs : ∀ k, f (k + 1) = F k (f k) := fun k => rfl
  have hfP : ∀ k, P k (f k) := by
    intro k
    induction k with
    | zero => exact ⟨hg₀i, hg₀u⟩
    | succ k ih => rw [hfs]; exact (hF k (f k) ih).1
  have hclose : ∀ k i j, DvdPow ϖ (k + 1) (f (k + 1) i j - f k i j) := by
    intro k i j; rw [hfs]; exact (hF k (f k) (hfP k)).2 i j

  have hlim := fun i j => GlobalTheory.T.exists_limit_dvdUniformizerPow_cauchy L ϖ hϖv (fun k => f k i j) (fun k => hclose k i j)
  choose b hb using hlim
  let h : Matrix (Fin n') (Fin n') L := Matrix.of b
  have hhk : ∀ k i j, DvdPow ϖ (k + 1) ((h - f k) i j) := fun k i j => hb i j k
  have hϖi : ϖ ∈ intL L := by
    show Valued.v ϖ ≤ 1
    rw [hϖv]; exact WithZero.exp_le_exp.2 (by norm_num : (-1 : ℤ) ≤ 0)
  have hhi : ∀ i j, h i j ∈ intL L := by
    intro i j
    have e : h i j = (h - f 0) i j + f 0 i j := by simp
    rw [e]
    exact add_mem (dvdPow_zero_iff.1 (dvdPow_mono hϖi (Nat.zero_le 1) (hhk 0 i j))) ((hfP 0).1 i j)
  have hunit : cT σ h * J * h = J := by
    ext i j
    have hz0 : (cT σ h * J * h - J) i j = 0 := by
      refine eq_zero_of_forall_dvdPow hϖv fun k => ?_
      have e : cT σ h * J * h - J = (cT σ (h - f k) * J * h + cT σ (f k) * J * (h - f k)) +
          (cT σ (f k) * J * f k - J) := by
        rw [cT_sub]; simp only [sub_mul, mul_sub, Matrix.mul_assoc]; abel
      rw [e, Matrix.add_apply, Matrix.add_apply]
      refine dvdPow_add (dvdPow_add ?_ ?_) ((hfP k).2 i j)
      · exact mc_mul_right (mc_mul_right (mc_cT hσv hσϖ (hhk k)) hJi) hhi i j
      · rw [Matrix.mul_assoc]
        exact mc_mul_left (int_cT hσv (hfP k).1) (mc_mul_left hJi (hhk k)) i j
    rw [Matrix.sub_apply] at hz0
    exact sub_eq_zero.1 hz0

  set Ji : Matrix (Fin n') (Fin n') L := ((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) with hJidef
  have hJiJ : Ji * J = 1 := by rw [hJidef, hJdef, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hleft : (Ji * cT σ h * J) * h = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT σ h), hunit, hJiJ]
  have hright : h * (Ji * cT σ h * J) = 1 := mul_eq_one_comm.1 hleft
  let hG : GL (Fin n') L := ⟨h, Ji * cT σ h * J, hright, hleft⟩
  have hmem : hG ∈ UJ σ J := hunit
  refine ⟨⟨hG, hmem⟩, GlobalTheory.UnitarySwap.mem_GLint_of_unitary hσv hJ hmem hhi, fun i r => ?_⟩
  show DvdPow ϖ 1 ((h *ᵥ z i) r - z' i r)
  have e : (h *ᵥ z i) r - z' i r = ((h - g₀) *ᵥ z i) r + ((g₀ *ᵥ z i) r - z' i r) := by
    simp [Matrix.sub_mulVec]
  rw [e]
  refine dvdPow_add ?_ (hg₀z i r)
  simp only [Matrix.mulVec, dotProduct]
  refine dvdPow_sum _ _ fun s _ => ?_
  rw [mul_comm]
  exact dvdPow_mul_int (hhk 0 r s) (hz i s)

end GlobalTheory.Hk3.IntWittBase
end
end
