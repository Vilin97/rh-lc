module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqZeroOfCobOneEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveModPrimeEqQuasiLogarithmDefect
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
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsCounitDerivationCounitComp
import Mathlib.RingTheory.MvPowerSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDualTangentModEqEvalAdditive
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DUnitMemRangeOfMemKerIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsLie
import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveModPrimeEqQuasiLogarithmDefectStatement

section

@[expose] public section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.additive_mod_prime_eq_quasiLogarithm_defect : ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (b : G.A 1) (z : G.A 1 ⊗[O] G.A 1), cobOne O (G.A 1) b = (p : O) • z → ∃ (f : MvPowerSeries (Fin d) E) (s : MvPowerSeries (Fin d) O) (y : G.A 1), QL c.μ ⊤ f ∧ map (algebraMap O E) s = defect c.μ p f ∧ c.ev 1 s = b + (p : O) • y := by
  first | exact @GlobalTheory.QLog.additive_mod_p_is_defect | exact GlobalTheory.QLog.additive_mod_p_is_defect | (intros; apply GlobalTheory.QLog.additive_mod_p_is_defect <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualEqSmulOfForallDvd

section

@[expose] public section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

theorem dual_eq_smul_of_forall_dvd :
    ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (a : O), (∀ x : O, a * x = 0 → x = 0) →
      ∀ l : Module.Dual O M, (∀ w, a ∣ l w) → ∃ l' : Module.Dual O M, l = a • l' := by
  intro O M _ _ _ a ha l hl
  have cancel : ∀ x y : O, a * x = a * y → x = y := by
    intro x y hxy
    have := ha (x - y) (by rw [mul_sub, hxy, sub_self])
    exact sub_eq_zero.mp this
  let c : M → O := fun w => Classical.choose (hl w)
  have hc : ∀ w, l w = a * c w := fun w => Classical.choose_spec (hl w)
  refine ⟨{ toFun := c, map_add' := ?_, map_smul' := ?_ }, ?_⟩
  · intro x y
    apply cancel
    rw [mul_add, ← hc, ← hc, ← hc, map_add (f := _)]
  · intro r x
    apply cancel
    simp only [RingHom.id_apply, smul_eq_mul]
    rw [← hc, map_smul, hc, smul_eq_mul]
    ring
  · ext w
    simp only [LinearMap.smul_apply, LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul]
    exact hc w

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualEqSmulOfForallDvdStatement

section

@[expose] public section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.dual_eq_smul_of_forall_dvd' : ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (a : O), (∀ x : O, a * x = 0 → x = 0) → ∀ l : Module.Dual O M, (∀ w, a ∣ l w) → ∃ l' : Module.Dual O M, l = a • l' := by
  first | exact @GlobalTheory.dual_eq_smul_of_forall_dvd | exact GlobalTheory.dual_eq_smul_of_forall_dvd | (intros; apply GlobalTheory.dual_eq_smul_of_forall_dvd <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDualTangentModEqEvalAdditiveStatement

section

@[expose] public section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.cartierDual_tangent_mod_eq_eval_additive : ∀ (O A : Type) [CommRing O] [CommRing A] [Bialgebra O A] [Module.Finite O A] [Module.Projective O A] [Coalgebra.IsCocomm O A] (a : O) (u : Cot O (CartierDual O A) →ₗ[O] O ⧸ Ideal.span {a}), ∃ (b : A) (z : A ⊗[O] A), cobOne O A b = a • z ∧ ∀ φ : CartierDual O A, u (dUnit (R := O) φ) = Ideal.Quotient.mk _ (φ b) := by
  first | exact @GlobalTheory.cartierDual_tangent_mod | exact GlobalTheory.cartierDual_tangent_mod | (intros; apply GlobalTheory.cartierDual_tangent_mod <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualLieExistsAdditiveEvalModPrimePow

section

@[expose] public section

noncomputable section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

theorem PDivGroup.dual_lie_exists_eval_mod_pow : ∀ (p : ℕ) (O : Type) [CommRing O]
    (G : PDivGroup p O) (l : G.dual.Lie) (n : ℕ), ∃ (b : G.A n) (z : G.A n ⊗[O] G.A n),
    cobOne O (G.A n) b = (p : O) ^ n • z ∧ ∀ (w : G.dual.omega) (φ : CartierDual O (G.A n)),
    dUnit (R := O) φ = w.1 n → (p : O) ^ n ∣ l w - φ b := by
  intro p O _ G l n
  let I : Ideal O := Ideal.span {(p : O) ^ n}
  let N : Submodule O G.dual.omega := Ideal.span {(p : O)} ^ n • ⊤
  let m : G.dual.omega →ₗ[O] O ⧸ I := (Ideal.Quotient.mkₐ O I).toLinearMap ∘ₗ l
  have hN : N ≤ LinearMap.ker m := by
    intro x hx
    have hx' : x ∈ (Ideal.span {(p : O)} ^ n • ⊤ : Submodule O G.dual.omega) := hx
    rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists] at hx'
    obtain ⟨v, -, rfl⟩ := hx'
    rw [LinearMap.mem_ker]
    change Ideal.Quotient.mk I (l ((p : O) ^ n • v)) = 0
    rw [map_smul, smul_eq_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  let u : Cot O (CartierDual O (G.A n)) →ₗ[O] O ⧸ I :=
    N.liftQ m hN ∘ₗ (G.dual.omegaQuotEquiv n).symm.toLinearMap
  have hu : ∀ w : G.dual.omega, u (w.1 n) = Ideal.Quotient.mk I (l w) := by
    intro w
    have h := (G.dual.omegaQuotEquiv_mk n w)
    change N.liftQ m hN ((G.dual.omegaQuotEquiv n).symm (w.1 n)) = _
    rw [← h, LinearEquiv.symm_apply_apply]
    rfl
  obtain ⟨b, z, hb, hφ⟩ := GlobalTheory.T.cartierDual_tangent_mod_eq_eval_additive O (G.A n) ((p : O) ^ n) u
  refine ⟨b, z, hb, fun w φ hφw => ?_⟩
  have h1 := hφ φ
  rw [hφw, hu, Ideal.Quotient.eq] at h1
  exact Ideal.mem_span_singleton.1 h1

end GlobalTheory
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualLieExistsAdditiveEvalModPrimePowStatement

section

@[expose] public section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.dual_lie_exists_additive_eval_mod_prime_pow : ∀ (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (l : G.dual.Lie) (n : ℕ), ∃ (b : G.A n) (z : G.A n ⊗[O] G.A n), cobOne O (G.A n) b = (p : O) ^ n • z ∧ ∀ (w : G.dual.omega) (φ : CartierDual O (G.A n)), dUnit (R := O) φ = w.1 n → (p : O) ^ n ∣ l w - φ b := by
  first | exact @GlobalTheory.PDivGroup.dual_lie_exists_eval_mod_pow | exact GlobalTheory.PDivGroup.dual_lie_exists_eval_mod_pow | (intros; apply GlobalTheory.PDivGroup.dual_lie_exists_eval_mod_pow <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsLieStatement

section

@[expose] public section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.existsUnique_isLie_of_isFrame_of_QL : ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (f : MvPowerSeries (Fin d) E), QL c.μ ⊤ f → ∃! l : G.dual.Lie, c.IsLie f l := by
  first | exact @GlobalTheory.QLog.Chart.existsUnique_isLie | exact GlobalTheory.QLog.Chart.existsUnique_isLie | (intros; apply GlobalTheory.QLog.Chart.existsUnique_isLie <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieSurjModP

section

@[expose] public section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog

theorem lie_surj_mod_p : ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E] [Algebra O E],
    IsFrame p E (RingHom.id O) → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d),
    ∀ l : G.dual.Lie, ∃ (f : MvPowerSeries (Fin d) E) (l' l'' : G.dual.Lie),
      QL c.μ ⊤ f ∧ c.IsLie f l' ∧ l = l' + (p : O) • l'' := by
  intro p _ O E _ _ _ hF G d c l
  obtain ⟨b, z, hbz, hl⟩ := GlobalTheory.T.dual_lie_exists_additive_eval_mod_prime_pow p O G l 1
  rw [pow_one] at hbz
  obtain ⟨f, s, y, hf, hs, hy⟩ := GlobalTheory.T.additive_mod_prime_eq_quasiLogarithm_defect p O E hF G d c b z hbz
  obtain ⟨l', hl', -⟩ := GlobalTheory.T.existsUnique_isLie_of_isFrame_of_QL p O E hF G d c f hf
  have hdiv : ∀ w : G.dual.omega, (p : O) ∣ (l - l') w := by
    intro w
    obtain ⟨φ, hφ⟩ := AugCot.d_surjective _ (w.1 1)
    have h1 := hl w φ hφ
    have h2 := hl'.2 1 w φ s hφ (by rw [pow_one]; exact hs)
    rw [pow_one] at h1 h2
    rw [hy, map_add (f := _), map_smul, smul_eq_mul] at h2
    have h3 : (p : O) ∣ l' w - φ b := by
      have := dvd_add h2 (dvd_mul_right (p : O) (φ y))
      rwa [show l' w - (φ b + (p : O) * φ y) + (p : O) * φ y = l' w - φ b by ring] at this
    have := dvd_sub h1 h3
    rwa [show l w - φ b - (l' w - φ b) = (l - l') w by simp] at this
  obtain ⟨l'', hl''⟩ := GlobalTheory.T.dual_eq_smul_of_forall_dvd' O G.dual.omega (p : O) (fun x hx => hF.sat x hx) (l - l') hdiv
  exact ⟨f, l', l'', hf, hl', by rw [← hl'']; abel⟩

end GlobalTheory.QLog
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiLogarithmLieAddPSmul

section

@[expose] public section

set_option autoImplicit false

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.QLog

theorem exists_isLie_add_smul : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (E : Type) [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ l : G.dual.Lie, ∃ (f : MvPowerSeries (Fin d) E) (l' l'' : G.dual.Lie), QL c.μ ⊤ f ∧ c.IsLie f l' ∧ l = l' + (p : O) • l'' := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ G d c E _ _ hE l
  exact lie_surj_mod_p p O E hE G d c l

end GlobalTheory.QLog
end
end
