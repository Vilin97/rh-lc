module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvDer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffSubstEqZeroOfDegreeLt
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvDer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualPairingChartPartialDerivativeModMaxStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComulChartSubSubstMemPSmul

section

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer
open TensorProduct

namespace GlobalTheory

theorem comul_ev_sub_ev₂_subst_mem :
    ∀ (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (n : ℕ)
      (F : MvPowerSeries (Fin d) O), ∃ t : G.A n ⊗[O] G.A n,
        Coalgebra.comul (R := O) (c.ev n F) - c.ev₂ n (subst c.μ F) = (p : O) • t := by
  intro p O _ G d c n F
  have hμ : HasSubst c.μ := hasSubst_of_constantCoeff_zero c.isLaw.const
  let φ₁ : MvPowerSeries (Fin d) O →ₐ[O] G.A n ⊗[O] G.A n :=
    (Bialgebra.comulAlgHom O (G.A n)).comp (c.ev n)
  let φ₂ : MvPowerSeries (Fin d) O →ₐ[O] G.A n ⊗[O] G.A n := (c.ev₂ n).comp (substAlgHom hμ)
  have h1 : ∀ f, φ₁ f = Coalgebra.comul (R := O) (c.ev n f) := fun f => rfl
  have h2 : ∀ f, φ₂ f = c.ev₂ n (subst c.μ f) := fun f => by
    simp only [φ₂, AlgHom.comp_apply, coe_substAlgHom]
  have hpoly : φ₁.comp (MvPolynomial.coeToMvPowerSeries.algHom O) =
      φ₂.comp (MvPolynomial.coeToMvPowerSeries.algHom O) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    simp only [AlgHom.comp_apply, MvPolynomial.coeToMvPowerSeries.algHom_apply, MvPolynomial.coe_X,
      Algebra.algebraMap_self, MvPowerSeries.map_id, RingHom.id_apply]
    rw [h1, h2, (c.isEval n).1 i, subst_X hμ, c.comul]
  obtain ⟨N₁, hN₁⟩ := (c.isEval n).2 1
  obtain ⟨N₂, hN₂⟩ := (c.isEval₂ n).2 1
  set N := max N₁ N₂
  set P := trunc' O (Finsupp.equivFunOnFinite.symm fun _ => N) F
  set T := F - (P : MvPowerSeries (Fin d) O)
  have hT : ∀ α : Fin d →₀ ℕ, α.degree < N → coeff α T = 0 := by
    intro α hα
    simp only [T, P, map_sub, MvPolynomial.coeff_coe, coeff_trunc']
    rw [if_pos, sub_self]
    intro i
    show α i ≤ N
    exact le_of_lt (lt_of_le_of_lt (Finsupp.le_degree i α) hα)
  have hPe : φ₁ (P : MvPowerSeries (Fin d) O) = φ₂ (P : MvPowerSeries (Fin d) O) := by
    have := congrArg (fun ψ => ψ P) hpoly
    simpa [MvPolynomial.coeToMvPowerSeries.algHom_apply] using this
  obtain ⟨a, ha⟩ := hN₁ T fun α hα => hT α (lt_of_lt_of_le hα (le_max_left _ _))
  obtain ⟨b, hb⟩ := hN₂ (subst c.μ T) fun β hβ =>
    coeff_subst_eq_zero_of_degree_lt O (Fin d) (Fin d ⊕ Fin d) c.μ T N c.isLaw.const hT β
      (lt_of_lt_of_le hβ (le_max_right _ _))
  rw [pow_one] at ha hb
  refine ⟨Coalgebra.comul (R := O) a - b, ?_⟩
  have hF : F = (P : MvPowerSeries (Fin d) O) + T := by simp [T]
  rw [← h1, ← h2, hF, map_add (f := _), map_add (f := _), hPe, add_sub_add_left_eq_sub, h1, h2, ha, hb,
    ← Bialgebra.comulAlgHom_apply, map_mul, map_natCast, Bialgebra.comulAlgHom_apply,
    ← mul_sub, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComulChartSubSubstMemPSmulStatement

section

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer
open TensorProduct


theorem _root_.GlobalTheory.T.comul_chart_sub_subst_mem_p_smul : ∀ (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (n : ℕ) (F : MvPowerSeries (Fin d) O), ∃ t : G.A n ⊗[O] G.A n, Coalgebra.comul (R := O) (c.ev n F) - c.ev₂ n (subst c.μ F) = (p : O) • t := by
  first | exact @GlobalTheory.comul_ev_sub_ev₂_subst_mem | exact GlobalTheory.comul_ev_sub_ev₂_subst_mem | (intros; apply GlobalTheory.comul_ev_sub_ev₂_subst_mem <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CounitFormalChartEvSubConstantCoeffDvd

section

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer
open TensorProduct

namespace GlobalTheory.FrNil

theorem counit_ev_sub_constantCoeff (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ)
    (c : QLog.Chart G d) (n : ℕ) (F : MvPowerSeries (Fin d) O) :
    (p : O) ∣ Coalgebra.counit (R := O) (c.ev n F) - constantCoeff F := by
  obtain ⟨N, hN⟩ := (c.isEval n).2 1
  set P : MvPolynomial (Fin d) O := trunc' O (Finsupp.equivFunOnFinite.symm fun _ => N) F with hP

  have halg : ((Bialgebra.counitAlgHom O (G.A n)).comp
      ((c.ev n).comp (MvPolynomial.coeToMvPowerSeries.algHom O))) =
      MvPolynomial.aeval (fun _ => (0 : O)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.coe_comp, Function.comp_apply, MvPolynomial.coeToMvPowerSeries.algHom_apply,
      MvPolynomial.aeval_X, Algebra.algebraMap_self, RingHom.id_apply, MvPolynomial.coe_X,
      MvPowerSeries.map_id]
    rw [(c.isEval n).1 i]
    exact c.aug n i
  have hPc : Coalgebra.counit (R := O) (c.ev n (P : MvPowerSeries (Fin d) O)) = constantCoeff F := by
    have := congrArg (fun φ => φ P) halg
    simp only [AlgHom.coe_comp, Function.comp_apply, MvPolynomial.coeToMvPowerSeries.algHom_apply,
      Algebra.algebraMap_self, RingHom.id_apply, MvPowerSeries.map_id] at this
    rw [show Coalgebra.counit (R := O) (c.ev n (P : MvPowerSeries (Fin d) O)) =
      Bialgebra.counitAlgHom O (G.A n) (c.ev n (P : MvPowerSeries (Fin d) O)) from rfl, this]
    rw [MvPolynomial.aeval_zero', hP, ← coeff_zero_eq_constantCoeff_apply, Algebra.algebraMap_self,
      RingHom.id_apply, MvPolynomial.constantCoeff_eq, coeff_trunc', if_pos]
    intro i
    exact Nat.zero_le _
  have hT : ∀ α : Fin d →₀ ℕ, α.degree < N → coeff α (F - (P : MvPowerSeries (Fin d) O)) = 0 := by
    intro α hα
    rw [map_sub, MvPolynomial.coeff_coe, hP, coeff_trunc', if_pos, sub_self]
    intro i
    show α i ≤ N
    exact le_trans (Finsupp.le_degree i α) hα.le
  obtain ⟨a, ha⟩ := hN _ hT
  rw [pow_one] at ha
  have hsplit : c.ev n F = c.ev n (F - (P : MvPowerSeries (Fin d) O)) + c.ev n P := by
    rw [← map_add (f := _), sub_add_cancel]
  refine ⟨Coalgebra.counit (R := O) a, ?_⟩
  rw [hsplit, map_add (f := _), ha, hPc, add_sub_cancel_right]
  rw [show ((p : G.A n)) * a = (p : O) • a by rw [Algebra.smul_def, map_natCast], map_smul, smul_eq_mul]

end GlobalTheory.FrNil
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CounitFormalChartEvSubConstantCoeffDvdStatement

section

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer
open TensorProduct


theorem _root_.GlobalTheory.T.counit_formalChart_ev_sub_constantCoeff_dvd : ∀ (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (n : ℕ) (F : MvPowerSeries (Fin d) O), (p : O) ∣ Coalgebra.counit (R := O) (c.ev n F) - constantCoeff F := by
  first | exact @GlobalTheory.FrNil.counit_ev_sub_constantCoeff | exact GlobalTheory.FrNil.counit_ev_sub_constantCoeff | (intros; apply GlobalTheory.FrNil.counit_ev_sub_constantCoeff <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvPowOfConvSubConstantCoeffInvariantDerivation

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
  GlobalTheory.LawDer TensorProduct

namespace GlobalTheory.LawDer

theorem convPow_ev_sub_constantCoeff_iterate_mem : ∀ (p : ℕ) (O : Type) [CommRing O]
    (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (n : ℕ) (m : Ideal O), (p : O) ∈ m →
    ∀ (u : Fin d → O) (φ : G.dual.A n), (∀ F, φ (c.ev n F) - ∑ i, u i * lin F i ∈ m) →
    ∀ (k : ℕ) (F : MvPowerSeries (Fin d) O),
      (φ ^ k) (c.ev n F) - constantCoeff ((invDer c.μ u)^[k] F) ∈ m := by
  intro p O _ G d c n m hp u φ hφ k
  induction k with
  | zero =>
    intro F
    obtain ⟨a, ha⟩ := GlobalTheory.T.counit_formalChart_ev_sub_constantCoeff_dvd p O G d c n F
    rw [pow_zero, Function.iterate_zero, id, LinearMap.convOne_apply, Algebra.algebraMap_self,
      RingHom.id_apply, ha]
    exact m.mul_mem_right a hp
  | succ k ih =>
    intro F
    obtain ⟨t, ht⟩ := GlobalTheory.T.comul_chart_sub_subst_mem_p_smul p O G d c n F
    rw [pow_succ, LinearMap.convMul_apply, Function.iterate_succ_apply, sub_eq_iff_eq_add.1 ht,
      map_add, map_add, map_smul, map_smul]
    have h1 := GlobalTheory.T.dual_pairing_chart_partial_derivative_mod_max p O G d c n m hp u φ hφ (φ ^ k).ofConv (subst c.μ F)
    have h2 := ih (invDer c.μ u F)
    have h3 : (p : O) • LinearMap.mul' O O (TensorProduct.map (φ ^ k).ofConv φ.ofConv t) ∈ m := by
      rw [smul_eq_mul]; exact m.mul_mem_right _ hp
    have := m.add_mem (m.add_mem h1 h2) h3
    convert this using 1
    simp only [invDer]
    ring

end GlobalTheory.LawDer
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvPowOfConvSubConstantCoeffInvariantDerivationStatement

section

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

theorem _root_.GlobalTheory.T.convPow_ofConv_sub_constantCoeff_invariantDerivation : ∀ (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (n : ℕ) (m : Ideal O), (p : O) ∈ m → ∀ (u : Fin d → O) (φ : G.dual.A n), (∀ F, φ (c.ev n F) - ∑ i, u i * lin F i ∈ m) → ∀ (k : ℕ) (F : MvPowerSeries (Fin d) O), (φ ^ k) (c.ev n F) - constantCoeff ((invDer c.μ u)^[k] F) ∈ m := by
  first | exact @GlobalTheory.LawDer.convPow_ev_sub_constantCoeff_iterate_mem | exact GlobalTheory.LawDer.convPow_ev_sub_constantCoeff_iterate_mem | (intros; apply GlobalTheory.LawDer.convPow_ev_sub_constantCoeff_iterate_mem <;> assumption)
end
end
