module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KchMul
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.SectionEqZeroOfGenericFramedPointValues
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBaseFieldMultipleOfNthRootComplexificationStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntegerExponentSectionOfChartRegularStatement
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaFrameValueEqUnitSmoothConnectedBase
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Polynomial.Basic
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ContinuousAevalMvPolynomial
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KchMul
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.PeriodicSchwarzLemma
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniversalTripleFibreAtFramedPointStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaKeyRuleTriangularFrameChangeFourthPowerStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaKeyRuleValueAtThetaPoint
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniversalTripleFibresBaseChangeKeyDataStatement
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowEqUnitOfContinuousComplexRoot

section

@[expose] public section

open Polynomial

namespace GlobalTheory.ContRoot

open GlobalTheory.AffinePoints

theorem nonempty_algHom (B : Type) [CommRing B] [Nontrivial B] [Algebra ℂ B]
    [Algebra.FiniteType ℂ B] : Nonempty (B →ₐ[ℂ] ℂ) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal B
  let _ := Ideal.Quotient.field m
  have : Module.Finite ℂ (B ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℂ (B ⧸ m)
  exact ⟨(IsAlgClosed.lift : (B ⧸ m) →ₐ[ℂ] ℂ).comp (Ideal.Quotient.mkₐ ℂ m)⟩

theorem exists_monic_prime_dvd (B : Type) [CommRing B] [IsDomain B] [IsIntegrallyClosed B]
    {n : ℕ} (hn : 0 < n) (u : B) :
    ∃ P : B[X], P.Monic ∧ Prime P ∧ 0 < P.natDegree ∧ P ∣ X ^ n - C u := by
  let L := AlgebraicClosure (FractionRing B)
  have hinj : Function.Injective (algebraMap B L) := by
    rw [IsScalarTower.algebraMap_eq B (FractionRing B) L]
    exact (algebraMap (FractionRing B) L).injective.comp (IsFractionRing.injective B _)
  have : FaithfulSMul B L := (faithfulSMul_iff_algebraMap_injective B L).2 hinj
  obtain ⟨β, hβ⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap B L u) hn
  have h0 : aeval β (X ^ n - C u : B[X]) = 0 := by simp [hβ]
  have hint : IsIntegral B β := ⟨_, monic_X_pow_sub_C u hn.ne', h0⟩
  exact ⟨minpoly B β, minpoly.monic hint, minpoly.prime_of_isIntegrallyClosed hint,
    minpoly.natDegree_pos hint, minpoly.isIntegrallyClosed_dvd hint h0⟩

theorem exists_pow_eq_of_continuous_root : ∀ (B : Type) [CommRing B] [IsDomain B] [Algebra ℂ B] [Algebra.Smooth ℂ B] (n : ℕ) (u : Bˣ) (ρ : (B →ₐ[ℂ] ℂ) → ℂ), 0 < n → (∀ (m : ℕ) (V : Set (Fin m → ℂ)) (s : (Fin m → ℂ) → (B →ₐ[ℂ] ℂ)), IsOpen V → (∀ a : B, DifferentiableOn ℂ (fun p => s p a) V) → ContinuousOn (fun p => ρ (s p)) V) → (∀ ψ : B →ₐ[ℂ] ℂ, ρ ψ ^ n = ψ (u : B)) → ∃ b : B, b ^ n = u := by
  intro B _ _ _ _ n u ρ hn hc hρ
  have hρc : Continuous ρ := GlobalTheory.RootConst.continuous_of_holomorphic_families B ρ hc
  have := GlobalTheory.isIntegrallyClosed_of_smooth ℂ B
  obtain ⟨P, hm, hp, hd, hdvd⟩ := exists_monic_prime_dvd B hn (u : B)
  have hdom : IsDomain (AdjoinRoot P) := AdjoinRoot.isDomain_of_prime hp
  have hft : Algebra.FiniteType ℂ (AdjoinRoot P) :=
    Algebra.FiniteType.trans (S := B) inferInstance inferInstance
  have hconn := GlobalTheory.RootConst.preconnectedSpace_algHom (AdjoinRoot P)
  let φ : B →ₐ[ℂ] AdjoinRoot P := IsScalarTower.toAlgHom ℂ B (AdjoinRoot P)
  have hroot : AdjoinRoot.root P ^ n = φ u := by
    have h := (AdjoinRoot.mk_eq_zero (f := P)).2 hdvd
    rw [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, sub_eq_zero] at h
    exact h
  have hu : ∀ ψ : B →ₐ[ℂ] ℂ, ψ u ≠ 0 := fun ψ => (u.isUnit.map ψ).ne_zero
  have hρ0 : ∀ ψ, ρ ψ ≠ 0 := fun ψ h => hu ψ (by rw [← hρ, h, zero_pow hn.ne'])
  have hcont : Continuous fun χ : AdjoinRoot P →ₐ[ℂ] ℂ =>
      χ (AdjoinRoot.root P) / ρ (comap φ χ) :=
    (continuous_eval _).div (hρc.comp (continuous_comap φ)) fun _ => hρ0 _
  have hconst := GlobalTheory.RootConst.eq_of_pow_eq_one hcont hn fun χ => by
    rw [div_pow, ← map_pow, hroot, hρ, comap_apply]
    exact div_self (hu (comap φ χ))
  obtain ⟨ψ⟩ := nonempty_algHom B
  have key : ∀ z, (P.map (ψ : B →+* ℂ)).IsRoot z → ∃ χ : AdjoinRoot P →ₐ[ℂ] ℂ,
      comap φ χ = ψ ∧ χ (AdjoinRoot.root P) = z := by
    intro z hz
    have hz' : P.eval₂ (ψ : B →+* ℂ) z = 0 := by rw [← eval_map]; exact hz
    refine ⟨AdjoinRoot.liftAlgHom P ψ z hz', ?_, by simp⟩
    ext b
    simp [φ]
  have huniq : ∀ z w, (P.map (ψ : B →+* ℂ)).IsRoot z → (P.map (ψ : B →+* ℂ)).IsRoot w →
      z = w := by
    intro z w hz hw
    obtain ⟨χ, h1, h2⟩ := key z hz
    obtain ⟨χ', h1', h2'⟩ := key w hw
    have h := hconst χ χ'
    simp only [h1, h1', h2, h2'] at h
    exact (div_left_inj' (hρ0 ψ)).1 h
  have hsep : (P.map (ψ : B →+* ℂ)).Separable := by
    refine (separable_X_pow_sub_C (n := n) (ψ u) (Nat.cast_ne_zero.2 hn.ne') (hu ψ)).of_dvd ?_
    simpa using Polynomial.map_dvd (ψ : B →+* ℂ) hdvd
  have hne : P.map (ψ : B →+* ℂ) ≠ 0 := (hm.map _).ne_zero
  have hdeg : P.natDegree ≤ 1 := by
    rw [← hm.natDegree_map (ψ : B →+* ℂ),
      (IsAlgClosed.splits (P.map (ψ : B →+* ℂ))).natDegree_eq_card_roots,
      ← Multiset.toFinset_card_of_nodup (nodup_roots hsep)]
    refine Finset.card_le_one.2 fun a ha b hb => huniq a b ?_ ?_
    · exact (mem_roots hne).1 (Multiset.mem_toFinset.1 ha)
    · exact (mem_roots hne).1 (Multiset.mem_toFinset.1 hb)
  have h1 : P = X + C (P.coeff 0) := hm.eq_X_add_C (le_antisymm hdeg hd)
  refine ⟨-P.coeff 0, ?_⟩
  have h2 : P.eval (-P.coeff 0) = 0 := by
    rw [congrArg (eval (-P.coeff 0)) h1]; simp
  have h3 := eval_eq_zero_of_dvd_of_eval_eq_zero hdvd h2
  simpa [sub_eq_zero] using h3

end GlobalTheory.ContRoot
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowEqUnitOfContinuousComplexRootStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.FrameUnif GlobalTheory.Reg
open scoped Matrix TensorProduct

theorem _root_.GlobalTheory.T.exists_pow_eq_unit_of_continuous_complex_root : ∀ (B : Type) [CommRing B] [IsDomain B] [Algebra ℂ B] [Algebra.Smooth ℂ B] (n : ℕ) (u : Bˣ) (ρ : (B →ₐ[ℂ] ℂ) → ℂ), 0 < n → (∀ (m : ℕ) (V : Set (Fin m → ℂ)) (s : (Fin m → ℂ) → (B →ₐ[ℂ] ℂ)), IsOpen V → (∀ a : B, DifferentiableOn ℂ (fun p => s p a) V) → ContinuousOn (fun p => ρ (s p)) V) → (∀ ψ : B →ₐ[ℂ] ℂ, ρ ψ ^ n = ψ (u : B)) → ∃ b : B, b ^ n = u := by
  first | exact @GlobalTheory.ContRoot.exists_pow_eq_of_continuous_root | exact GlobalTheory.ContRoot.exists_pow_eq_of_continuous_root | (intros; apply GlobalTheory.ContRoot.exists_pow_eq_of_continuous_root <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaKeyRuleValueAtThetaPointStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.FrameUnif GlobalTheory.Reg
open scoped Matrix TensorProduct

theorem _root_.GlobalTheory.T.theta_key_rule_value_at_theta_point : ∀ κ : GlobalTheory.KeyCl.Rule, GlobalTheory.KeyCl.Homog (fun _ => 1) κ → GlobalTheory.KeyCl.ThetaOne κ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (k : Fin F.n) (T : ThetaData e F M k), ∀ b ∈ T.co ⁻¹' (M.X k).dom, ∀ (a : ℂ) (y : FrPt Xo c (CAt σ)) (Φ : FibKey Xo ℂ y.x), a ≠ 0 → IsThetaPt T b a y → Tied (S := ℂ) e y.s y.u Φ → a ^ 8 * (κ ℂ Φ.key : ℂ) = ((2 * Real.pi * Complex.I) ^ g * (T.h b).det) ^ 4 := by
  first | exact @GlobalTheory.KeyFourth.value_at_thetaPt | exact GlobalTheory.KeyFourth.value_at_thetaPt | (intros; apply GlobalTheory.KeyFourth.value_at_thetaPt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsKeySectionUnif

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT
open GlobalTheory.FrameUnif GlobalTheory.Reg
open scoped Matrix TensorProduct

namespace GlobalTheory.KeyFourth

theorem exists_eq_smul_pow {K : Type} [Field K] [Algebra K ℂ] {A : Type} [CommRing A] [Algebra K A]
    [Algebra.Smooth K A] [IsDomain (ℂ ⊗[K] A)] {n : ℕ} (hn : 0 < n) (u : Aˣ) {C : ℂ} (hC : C ≠ 0)
    (ρ : (A →ₐ[K] ℂ) → ℂ)
    (hρ : ∀ (m : ℕ) (V : Set (Fin m → ℂ)) (s : (Fin m → ℂ) → (A →ₐ[K] ℂ)), IsOpen V →
      (∀ a : A, DifferentiableOn ℂ (fun p => s p a) V) → ContinuousOn (fun p => ρ (s p)) V)
    (hu : ∀ ψ : A →ₐ[K] ℂ, ρ ψ ^ n = C * ψ (u : A)) : ∃ (a : K) (b : A), a ≠ 0 ∧ (u : A) = a • b ^ n := by
  haveI : Nontrivial A := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact not_subsingleton (ℂ ⊗[K] A) inferInstance
  let res : (ℂ ⊗[K] A →ₐ[ℂ] ℂ) → (A →ₐ[K] ℂ) := fun χ =>
    (χ.restrictScalars K).comp Algebra.TensorProduct.includeRight
  let u' : (ℂ ⊗[K] A)ˣ := Units.map (algebraMap ℂ (ℂ ⊗[K] A) : ℂ →* _) (Units.mk0 C hC) *
    Units.map ((Algebra.TensorProduct.includeRight : A →ₐ[K] ℂ ⊗[K] A) : A →* _) u
  have hu' : (u' : ℂ ⊗[K] A) = C ⊗ₜ[K] (u : A) := by
    simp [u', Algebra.TensorProduct.algebraMap_apply]
  obtain ⟨w, hw⟩ := GlobalTheory.T.exists_pow_eq_unit_of_continuous_complex_root (ℂ ⊗[K] A) n u' (fun χ => ρ (res χ)) hn
    (fun m V s hV hs => hρ m V (fun p => res (s p)) hV fun a => hs _) (fun χ => by
      rw [hu, hu']
      have : C ⊗ₜ[K] (u : A) = C • ((1 : ℂ) ⊗ₜ[K] (u : A)) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [this, map_smul, smul_eq_mul]
      rfl)
  exact GlobalTheory.T.exists_base_field_multiple_of_nth_root_complexification K A n w C u hn hC u.ne_zero (hw.trans hu')

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem keySec_of_generic (h : GenFrEx Xo c) (b : ∀ Z : Comp Xo c, Om Z) (hb0 : ∀ Z, b Z ≠ 0)
    (hb : ∀ C : FChart h, ((kch C.t : (Om C.Z)ˣ) : Om C.Z) * b C.Z ∈ C.R ∧
      (((kch C.t : (Om C.Z)ˣ) : Om C.Z) * b C.Z)⁻¹ ∈ C.R) : Nonempty (KeySec Xo c) := by
  obtain ⟨hL, -, -, hA⟩ := evLaws_genFr_atlas E H Dw l Xo c
  obtain ⟨f, hf, hfb⟩ := GlobalTheory.T.exists_integer_exponent_section_of_chart_regular E H Dw l Xo c h (keyEx Dw) b fun C => (hb C).1
  obtain ⟨f', hf', hfb'⟩ := GlobalTheory.T.exists_integer_exponent_section_of_chart_regular E H Dw l Xo c h (-keyEx Dw) (fun Z => (b Z)⁻¹) fun C => by
    have := (hb C).2
    rw [mul_inv, ← Units.val_inv_eq_inv_val] at this
    simpa only [kch, Pi.neg_apply, zpow_neg, Finset.prod_inv_distrib] using this
  have h0 : GlobalTheory.AllWt.secZ Xo c 0 = sec Xo c 0 0 := by
    rw [← GlobalTheory.AllWt.secZ_nat]
    congr 1
    funext i
    cases i <;> rfl
  have hm := GlobalTheory.AllWt.mul_mem_secZ hf hf'
  rw [add_neg_cancel, h0] at hm
  have h1 := GlobalTheory.AllWt.one_mem_secZ (Xo := Xo) (c := c)
  rw [h0] at h1
  have hff : f * f' = 1 := by
    refine sub_eq_zero.1 (sec_eq_zero_of_generic_values E H Dw l Xo c hL h (hA h) 0 0 _ (sub_mem hm h1) fun Z => ?_)
    have e₁ : evC h Z (f * f') = evC h Z f * evC h Z f' := by simp only [evC, evR, evalAt_mul]
    have e₂ : evC h Z (1 : Rul Xo c) = 1 := evalAt_one _ _ _ (hL.test _ _)
    have e₃ := (evalL (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (genFr h Z)).map_sub
      (f * f') 1
    refine e₃.trans ?_
    change evC h Z (f * f') - evC h Z 1 = 0
    rw [e₁, e₂, hfb, hfb', mul_inv_cancel₀ (hb0 Z), sub_self]
  exact ⟨⟨⟨f, f', hff, (mul_comm _ _).trans hff⟩, hf⟩⟩

attribute [local instance 1100] Subalgebra.algebra in
theorem exists_chart_units {κ : GlobalTheory.KeyCl.Rule} (h₁ : GlobalTheory.KeyCl.Homog (fun _ => 1) κ) (h₂ : GlobalTheory.KeyCl.Funct κ)
    (h₃ : GlobalTheory.KeyCl.FamUnit κ) {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (hpq : 1 ≤ Dw.p + Dw.q)
    (h : GenFrEx Xo c) : ∃ v : ∀ Z : Comp Xo c, (Om Z)ˣ, ∀ C : FChart h,
      ∃ (Φ : FibKey Xo C.R C.y.x) (u : (C.R)ˣ), Tied e C.y.s C.y.u Φ ∧ GlobalTheory.KeyCl.IsValue κ Φ.key (u : C.R) ∧
        ((u : C.R) : Om C.Z) = ((kch C.t ^ 4 * v C.Z : (Om C.Z)ˣ) : Om C.Z) := by
  have hc : ∀ Z : Comp Xo c, CharZero (Om Z) := fun Z =>
    charZero_of_injective_algebraMap (algebraMap c.F (Om Z)).injective
  choose Ψ hΨ using fun Z : Comp Xo c => GlobalTheory.T.exists_universalTripleFibre_at_framedPoint E H Dw l Xo c g e (Om Z) (genFr h Z) hpq
  refine ⟨fun Z => κ (Om Z) (Ψ Z).key, fun C => ?_⟩
  haveI := C.sm
  haveI : IsIntegrallyClosed C.R := isIntegrallyClosed_of_smooth c.F C.R
  haveI : IsNoetherianRing C.R := Algebra.FiniteType.isNoetherianRing c.F C.R
  haveI : CharZero C.R := charZero_of_injective_algebraMap (algebraMap c.F C.R).injective
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.exists_universalTripleFibre_at_framedPoint E H Dw l Xo c g e C.R C.y hpq
  obtain ⟨Φ', hΦ'⟩ := GlobalTheory.T.exists_universalTripleFibre_at_framedPoint E H Dw l Xo c g e (Om C.Z) C.yg hpq
  obtain ⟨u, hu⟩ := h₃ C.R Φ.key
  refine ⟨Φ, u, hΦ, hu, ?_⟩
  rw [← GlobalTheory.T.theta_key_rule_triangular_frame_change_fourth_power κ h₁ h₂ E H Dw l Xo c g e (Om C.Z) C.t _ _ (Ψ C.Z) Φ' C.bor (hΨ _) hΦ']
  exact (hu (Om C.Z) _ _ (GlobalTheory.T.universal_triple_fibres_base_change_key_data E H Dw l Xo c g e _ _ C.R.val C.y C.yg Φ Φ' C.gen hΦ hΦ')).symm

theorem rule_eq_of_rootVal {κ : GlobalTheory.KeyCl.Rule} (h₁ : GlobalTheory.KeyCl.Homog (fun _ => 1) κ) (h₂ : GlobalTheory.KeyCl.Funct κ)
    (h₃ : GlobalTheory.KeyCl.ThetaOne κ) {σ : c.F →+* ℂ} {g : ℕ} {e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)}
    {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom)
      (fun j => Formalism.L2.PjFree.relab c σ (e j).1)} {r : ℕ} {M : ModelsOf F r} (T : ∀ k, ThetaData e F M k)
    {un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ)} (hun : ∀ k, IsNormUn (T k) (un k)) (hpq : 1 ≤ Dw.p + Dw.q)
    {N : ℂ} (hN : N ≠ 0) (hNk : ∀ k, (normConst (fun j => Formalism.L2.PjFree.relab c σ (e j).1) (M.X k).ξ0 : ℂ) = N)
    {y : FrPt Xo c (CAt σ)} {v : ℂ} (hv : RootVal (unfOf e F M un) y v) (Φ : FibKey Xo ℂ y.x)
    (hΦ : Tied (S := ℂ) e y.s y.u Φ) :
    v ^ 4 = (N / (2 * Real.pi * Complex.I) ^ g) ^ 4 * (κ ℂ Φ.key : ℂ) := by
  obtain ⟨k, x, t, ht, rfl⟩ : ∃ (k : Fin F.n) (x : (M.X k).dom) (t : Ix Dw → (CAt σ)ˣ), FrBor t (un k x) y ∧
    v = Formalism.L2.PjFree.toC ((kch t : (CAt σ)ˣ) : CAt σ) := hv
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : FibKey Xo ℂ (un k x).x, Tied (S := ℂ) e (un k x).s (un k x).u Ψ :=
    @GlobalTheory.T.exists_universalTripleFibre_at_framedPoint E _ _ _ H Dw l Xo c g e ℂ _ _ σ.toAlgebra (un k x) hpq
  have e₁ : κ ℂ Φ.key = kch (S := ℂ) t ^ 4 * κ ℂ Ψ.key :=
    @GlobalTheory.T.theta_key_rule_triangular_frame_change_fourth_power κ h₁ h₂ E _ _ _ H Dw l Xo c g e ℂ _ _ σ.toAlgebra t (un k x) y Ψ Φ ht hΨ hΦ
  obtain ⟨a, ha, hy⟩ := hun k x
  have hb : (T k).co.symm x.1 ∈ (T k).co ⁻¹' (M.X k).dom := by
    show (T k).co ((T k).co.symm x.1) ∈ (M.X k).dom
    rw [(T k).co.apply_symm_apply]; exact x.2
  have d1 := ((T k).norm _ hb).1.ne_zero
  rw [hNk] at ha
  have a0 : a ≠ 0 := fun h0 => mul_ne_zero hN d1 (by rw [← ha, h0]; simp)
  have e₂ := GlobalTheory.T.theta_key_rule_value_at_theta_point κ h₁ h₃ E H Dw l Xo c σ g e F r M k (T k) _ hb a (un k x) Ψ a0 hy hΨ
  have e₃ : N ^ 4 * (κ ℂ Ψ.key : ℂ) = ((2 * Real.pi * Complex.I) ^ g) ^ 4 := by
    refine mul_right_cancel₀ (pow_ne_zero 4 d1) ?_
    rw [show a ^ 8 = (a ^ 2) ^ 4 by ring, ha] at e₂
    linear_combination e₂
  have hπ : ((2 * Real.pi * Complex.I : ℂ) ^ g) ^ 4 ≠ 0 :=
    pow_ne_zero _ (pow_ne_zero _ Complex.two_pi_I_ne_zero)
  have e₄ : (κ ℂ Φ.key : ℂ) = Formalism.L2.PjFree.toC ((kch t : (CAt σ)ˣ) : CAt σ) ^ 4 * (κ ℂ Ψ.key : ℂ) := by
    rw [e₁]
    rfl
  rw [e₄, div_pow, mul_left_comm, div_mul_eq_mul_div, e₃, div_self hπ, mul_one]


end GlobalTheory.KeyFourth
end
end
end
