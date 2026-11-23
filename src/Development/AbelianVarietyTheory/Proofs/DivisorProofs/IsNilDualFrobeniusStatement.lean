module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffPLogarithmsEqInvFrobeniusMatrixStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffIterateInvariantDerivationLinearStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffPIterateInvariantDerivationCoordStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvPowOfConvSubConstantCoeffInvariantDerivationStatement
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvDer
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Mathlib.RingTheory.MvPowerSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNilpotentDualFrobeniusOfBlockStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapInvariantDerivationFormalGroupLawIterateStatement
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierDualLiftLinearCoefficientsMod

section

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

theorem GlobalTheory.QLog.Chart.exists_dual_lift_lin : ∀ (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (m : Ideal O), (p : O) ∈ m → ∃ n : ℕ, ∀ u : Fin d → O, ∃ φ : G.dual.A n, ∀ F, φ (c.ev n F) - ∑ i, u i * lin F i ∈ m := by
  intro p O _ G d c m hp
  obtain ⟨n, hn⟩ := c.ker 1 2
  refine ⟨n, fun u => ?_⟩
  let L : MvPowerSeries (Fin d) O →ₗ[O] O := ∑ i, u i • coeff (Finsupp.single i 1)
  have hL : ∀ F, L F = ∑ i, u i * lin F i := fun F => by simp [L, LinearMap.sum_apply, lin]
  let f : MvPowerSeries (Fin d) O →ₗ[O] O ⧸ m := m.mkQ ∘ₗ L
  have hk : LinearMap.ker (c.ev n).toLinearMap ≤ LinearMap.ker f := by
    intro F hF
    have h := hn F hF
    change Ideal.Quotient.mk m (L F) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, hL]
    refine Submodule.sum_mem _ fun i _ => m.mul_mem_left _ ?_
    obtain ⟨a, ha⟩ := h (Finsupp.single i 1) (by simp)
    have : lin F i = p ^ 1 * a := ha
    rw [this, pow_one]
    exact m.mul_mem_right _ hp
  let g : G.A n →ₗ[O] O ⧸ m := (LinearMap.ker (c.ev n).toLinearMap).liftQ f hk ∘ₗ
    ((c.ev n).toLinearMap.quotKerEquivOfSurjective (c.surj n)).symm.toLinearMap
  have hg : ∀ F, g (c.ev n F) = f F := fun F => by
    have : ((c.ev n).toLinearMap.quotKerEquivOfSurjective (c.surj n)).symm (c.ev n F) =
        Submodule.Quotient.mk F := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    simp only [g, LinearMap.comp_apply, LinearEquiv.coe_coe, this, Submodule.liftQ_apply]
  obtain ⟨φ, hφ⟩ := Module.projective_lifting_property m.mkQ g m.mkQ_surjective
  refine ⟨WithConv.toConv φ, fun F => ?_⟩
  rw [← hL, ← Submodule.Quotient.eq]
  exact (LinearMap.congr_fun hφ (c.ev n F)).trans (hg F)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierDualLiftLinearCoefficientsModStatement

section

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

theorem _root_.GlobalTheory.T.exists_cartierDual_lift_linearCoefficients_mod : ∀ (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (m : Ideal O), (p : O) ∈ m → ∃ n : ℕ, ∀ u : Fin d → O, ∃ φ : G.dual.A n, ∀ F, φ (c.ev n F) - ∑ i, u i * lin F i ∈ m := by
  first | exact @GlobalTheory.QLog.Chart.exists_dual_lift_lin | exact GlobalTheory.QLog.Chart.exists_dual_lift_lin | (intros; apply GlobalTheory.QLog.Chart.exists_dual_lift_lin <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformConvolutionPowApplyMemLocalDual

section

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

namespace GlobalTheory.LocalDualNil

theorem exists_pow_mem_map {O R : Type*} [CommRing O] [CommRing R] [Algebra O R]
    [Module.Finite O R] [IsLocalRing R] (ε : R →ₐ[O] O) (m : Ideal O) (hm : m.IsMaximal) :
    ∃ r : ℕ, ∀ φ : R, ε φ ∈ m → ∀ s, r ≤ s → φ ^ s ∈ m.map (algebraMap O R) := by
  set J : Ideal R := m.map (algebraMap O R) with hJ
  by_cases htop : J = ⊤
  · exact ⟨0, fun φ _ s _ => htop ▸ Submodule.mem_top⟩
  letI : Field (O ⧸ m) := Ideal.Quotient.field m
  haveI : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.2 htop
  haveI : IsLocalRing (R ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  haveI : Module.Finite (O ⧸ m) (R ⧸ J) := Module.Finite.of_restrictScalars_finite O _ _
  haveI : IsArtinianRing (R ⧸ J) := IsArtinianRing.of_finite (O ⧸ m) _
  obtain ⟨r, hr⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := R ⧸ J)
  rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top] at hr
  haveI : IsLocalHom (Ideal.Quotient.mk J) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  refine ⟨r, fun φ hφ s hs => ?_⟩
  have h1 : ¬ IsUnit φ := fun h => hm.ne_top (Ideal.eq_top_of_isUnit_mem _ hφ (h.map ε))
  have h2 : Ideal.Quotient.mk J φ ∈ IsLocalRing.maximalIdeal (R ⧸ J) :=
    fun h => h1 (isUnit_of_map_unit _ _ h)
  have h3 := Ideal.pow_mem_pow h2 r
  rw [hr, Submodule.zero_eq_bot, Ideal.mem_bot, ← map_pow, Ideal.Quotient.eq_zero_iff_mem] at h3
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hs
  rw [pow_add]
  exact J.mul_mem_right _ h3

theorem exists_pow_apply_mem : ∀ (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (n : ℕ)
    (m : Ideal O), m.IsMaximal → IsLocalRing (G.dual.A n) → ∃ r : ℕ, ∀ φ : G.dual.A n,
      φ 1 ∈ m → ∀ s, r ≤ s → ∀ a : G.A n, (φ ^ s) a ∈ m := by
  intro p O _ G n m hm hloc
  obtain ⟨r, hr⟩ := exists_pow_mem_map (Bialgebra.counitAlgHom O (G.dual.A n)) m hm
  refine ⟨r, fun φ hφ s hs a => ?_⟩
  have h := hr φ hφ s hs
  generalize φ ^ s = ψ at h
  have h' : ψ ∈ m • (⊤ : Submodule O (G.dual.A n)) := by
    rw [Ideal.smul_top_eq_map]
    exact h
  refine Submodule.smul_induction_on (p := fun ψ : G.dual.A n => ψ a ∈ m) h' ?_ ?_
  · intro c hc χ _
    exact m.mul_mem_right (χ a) hc
  · intro x y hx hy
    exact m.add_mem hx hy

end GlobalTheory.LocalDualNil
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformConvolutionPowApplyMemLocalDualStatement

section

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

theorem _root_.GlobalTheory.T.exists_uniform_convolution_pow_apply_mem_localDual : ∀ (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (n : ℕ) (m : Ideal O), m.IsMaximal → IsLocalRing (G.dual.A n) → ∃ r : ℕ, ∀ φ : G.dual.A n, φ 1 ∈ m → ∀ s, r ≤ s → ∀ a : G.A n, (φ ^ s) a ∈ m := by
  first | exact @GlobalTheory.LocalDualNil.exists_pow_apply_mem | exact GlobalTheory.LocalDualNil.exists_pow_apply_mem | (intros; apply GlobalTheory.LocalDualNil.exists_pow_apply_mem <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNilDualFrobenius

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

theorem GlobalTheory.DualFrobNil.isNil_dual_frobenius : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q), IsBasis μ' e → IsAdapted F.θ μ' e → IsConn G.dual → ∀ U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B, IsUnit U → (∀ i, In (⊤ : Ideal F.B) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e) ∧ ∀ i', i = Sum.inl i' → In (Ideal.span {(p : F.B)}) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e)) → IsNil F.θ F.σ (U.transpose⁻¹ * blk d k 1 (p : F.B)) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F G d c μ' hL hμ k e hB hA hconn U hU hfr
  obtain ⟨m, hmax, hpm⟩ := Ideal.exists_le_maximal (Ideal.span {(p : O)}) (by
    rw [Ne, Ideal.span_singleton_eq_top]; exact Fact.out)
  have hp : (p : O) ∈ m := hpm (Ideal.mem_span_singleton_self _)
  obtain ⟨c', hc'⟩ := GlobalTheory.T.coeff_p_logarithms_congr_inv_frobenius_matrix_mod_p p F.B F.Q F.s F.σ F.s_alg F.frame.inj d k e U hU hfr (fun a => (hA a).2)
    (fun r j => by obtain ⟨b, -, hb⟩ := (hB.1 r).2.1 j; exact ⟨b, hb⟩)
  refine GlobalTheory.T.isNilpotent_dualFrobenius_of_block F.B O F.θ F.σ p m (by rw [map_natCast]; exact hp) hmax.ne_top
    (fun b => by obtain ⟨c, hc⟩ := F.σ_pow b; exact ⟨c, hc⟩) d k U c' (fun a j => (hc' a j).2) ?_
  set Sh : (Fin d → O ⧸ m) → (Fin d → O ⧸ m) :=
    fun w a => ∑ j, Ideal.Quotient.mk m (F.θ (c' a j)) * w j ^ p with hSh
  obtain ⟨n, hlift⟩ := GlobalTheory.T.exists_cartierDual_lift_linearCoefficients_mod p O G d c m hp
  obtain ⟨r, hr⟩ := GlobalTheory.T.exists_uniform_convolution_pow_apply_mem_localDual p O G n m hmax (hconn n)
  have hθ : ∀ x ∈ RingHom.ker F.θ ⊔ Ideal.span {(p : F.B)}, F.θ x ∈ m := by
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.1 hz
    rw [map_add (f := _), RingHom.mem_ker.1 hy, zero_add, map_mul, map_natCast]
    exact m.mul_mem_left _ hp
  have step : ∀ (u : Fin d → O) (φ : G.dual.A n), (∀ Fs, φ (c.ev n Fs) - ∑ i, u i * lin Fs i ∈ m) →
      ∃ u' : Fin d → O, (∀ Fs, (φ ^ p) (c.ev n Fs) - ∑ i, u' i * lin Fs i ∈ m) ∧
        (fun a => Ideal.Quotient.mk m (u' a)) = Sh (fun a => Ideal.Quotient.mk m (u a)) := by
    intro u φ hφ
    refine ⟨fun a => constantCoeff ((invDer c.μ u)^[p] (X a)), fun Fs => ?_, ?_⟩
    · obtain ⟨t, ht⟩ := GlobalTheory.T.constantCoeff_iterate_invariant_derivation_linear p O d c.μ c.isLaw.const c.isLaw.unit c.isLaw.comm u Fs
      have h1 := GlobalTheory.T.convPow_ofConv_sub_constantCoeff_invariantDerivation p O G d c n m hp u φ hφ p Fs
      have h2 : (p : O) * t ∈ m := m.mul_mem_right t hp
      have e1 : (φ ^ p) (c.ev n Fs) - ∑ i, constantCoeff ((invDer c.μ u)^[p] (X i)) * lin Fs i =
          ((φ ^ p) (c.ev n Fs) - constantCoeff ((invDer c.μ u)^[p] Fs)) + p * t := by
        rw [← ht]; simp only [lin]; ring
      rw [e1]; exact m.add_mem h1 h2
    · funext a
      choose ũ hũ using fun i => F.frame.surj (u i)
      have hnat := GlobalTheory.T.map_invariantDerivationFormalGroupLaw_iterate F.B O F.θ d μ' hL.const ũ p (X a)
      have hmu : (fun i => map F.θ (μ' i)) = c.μ := funext hμ
      have hu : (fun i => F.θ (ũ i)) = u := funext hũ
      rw [hmu, hu, map_X] at hnat
      have key := hθ _ (GlobalTheory.T.constantCoeff_pIterate_invariantDerivation_coord p F.B O F.Q F.θ F.frame d μ' hL (e (Sum.inl a)) a (hB.1 _) (hA a).1
        (hA a).2 (c' a) (fun i => (hc' a i).1) ũ)
      have hcc : constantCoeff ((invDer c.μ u)^[p] (X a)) =
          F.θ (constantCoeff ((invDer μ' ũ)^[p] (X a))) := by
        rw [← hnat, ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply]
      simp only [hSh]
      rw [hcc, ← hu]

      simp only [← map_pow, ← map_mul, ← map_sum]
      rw [Ideal.Quotient.eq]

      simpa [map_sub, map_sum, map_mul, map_pow] using key
  have iter : ∀ t (u : Fin d → O) (φ : G.dual.A n), (∀ Fs, φ (c.ev n Fs) - ∑ i, u i * lin Fs i ∈ m) →
      ∃ u' : Fin d → O, (∀ Fs, (φ ^ (p ^ t)) (c.ev n Fs) - ∑ i, u' i * lin Fs i ∈ m) ∧
        (fun a => Ideal.Quotient.mk m (u' a)) = Sh^[t] (fun a => Ideal.Quotient.mk m (u a)) := by
    intro t
    induction t with
    | zero => intro u φ hφ; exact ⟨u, by simpa using hφ, rfl⟩
    | succ t ih =>
      intro u φ hφ
      obtain ⟨u1, h1, e1⟩ := ih u φ hφ
      obtain ⟨u2, h2, e2⟩ := step u1 _ h1
      refine ⟨u2, fun Fs => ?_, ?_⟩
      · rw [pow_succ, pow_mul]; exact h2 Fs
      · rw [e2, e1, Function.iterate_succ_apply']
  refine ⟨r, fun w => ?_⟩
  obtain ⟨u, rfl⟩ : ∃ u : Fin d → O, (fun a => Ideal.Quotient.mk m (u a)) = w :=
    ⟨fun a => (Ideal.Quotient.mk_surjective (w a)).choose,
      funext fun a => (Ideal.Quotient.mk_surjective (w a)).choose_spec⟩
  obtain ⟨φ, hφ⟩ := hlift u
  obtain ⟨u', h', e'⟩ := iter r u φ hφ
  rw [← e']
  funext a
  have h1 : φ 1 ∈ m := by
    have := hφ 1
    simpa [lin, coeff_one] using this
  have hle : r ≤ p ^ r := (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le
  have h3 := hr φ h1 (p ^ r) hle (c.x n a)
  have h4 := h' (X a)
  rw [(c.isEval n).1 a] at h4
  have hs : ∑ i, u' i * lin (X a : MvPowerSeries (Fin d) O) i = u' a := by
    simp [lin, coeff_X, Finsupp.single_eq_single_iff]
  rw [hs] at h4
  have h5 : u' a ∈ m := by
    have := m.sub_mem h3 h4
    simpa using this
  simpa [Ideal.Quotient.eq_zero_iff_mem] using h5
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNilDualFrobeniusStatement

section

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.isNil_dual_frobenius_alt : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q), IsBasis μ' e → IsAdapted F.θ μ' e → IsConn G.dual → ∀ U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B, IsUnit U → (∀ i, In (⊤ : Ideal F.B) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e) ∧ ∀ i', i = Sum.inl i' → In (Ideal.span {(p : F.B)}) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e)) → IsNil F.θ F.σ (U.transpose⁻¹ * blk d k 1 (p : F.B)) := by
  first | exact @GlobalTheory.DualFrobNil.isNil_dual_frobenius | exact GlobalTheory.DualFrobNil.isNil_dual_frobenius | (intros; apply GlobalTheory.DualFrobNil.isNil_dual_frobenius <;> assumption)
end
end
