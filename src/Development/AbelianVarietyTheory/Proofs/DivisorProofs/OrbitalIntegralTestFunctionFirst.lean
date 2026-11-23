module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugatePairsSameSimilitude
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateTwistedUnitCommutes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFixedUnitClassesCentralizerRegularStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CofinitePlacesRealizePrimes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyKottwitzLatticeSeparableMinpolyStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyTauFixedUnitCentralizerIsNormStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactSupportTwistedHeckeTestFunctionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHodgeLatticeGermSystem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalConjTrivializationAtPlaceAwayP
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntCZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralConjugationStableStructure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTwistedNormConclusionTransferRingEquivStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalSupportFinitePrimeSet
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedNormUnitCommutation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsConjOfMinpolyEqOfSeparable
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalConjTrivializationAtPlaceAwayPStatement

section

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.exists_local_conj_trivialization_at_place_awayP : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) β x t) (y : grp G β) (g : G.GAf) (c Y : G.Cˣ),
    (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = c * Y * ((c⁻¹ : G.Cˣ) : G.C) → ∀ w : AwayP p,
    ∃ (k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) (lam : (w.1.adicCompletion ℚ)ˣ),
      (k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) * inC G (w.1.adicCompletion ℚ) (Y : G.C) * ((k⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) = ((((compL G w (g⁻¹ * toAfF G β x t hx y * g) : UPts G.star (w.1.adicCompletion ℚ)) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ × (w.1.adicCompletion ℚ)ˣ).1 : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) ∧
      (k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) * inC G (w.1.adicCompletion ℚ) ((Y⁻¹ : G.Cˣ) : G.C) * ((k⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) = (((((compL G w (g⁻¹ * toAfF G β x t hx y * g) : UPts G.star (w.1.adicCompletion ℚ)) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ × (w.1.adicCompletion ℚ)ˣ).1 : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ)⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) ∧
      (k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) * (inC G (w.1.adicCompletion ℚ) (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) *
        inC G (w.1.adicCompletion ℚ) (β : G.C)) * (starT G.star (w.1.adicCompletion ℚ) (k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop = algebraMap (w.1.adicCompletion ℚ) (w.1.adicCompletion ℚ ⊗[ℚ] G.C) (lam : w.1.adicCompletion ℚ) := by
  first | (exact @GlobalTheory.FinClsLoc.glueL_main) | (exact GlobalTheory.FinClsLoc.glueL_main) | (intros; apply GlobalTheory.FinClsLoc.glueL_main  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorRegularConjugateLocalScalarNorm

section

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.CxRegLoc

theorem local_class_scalar_norm_sep : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ),
    IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
    ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), sh G β = β →
    ∀ y₀ : grp G β, (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable →
    (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n →
    ∃ S : Finset ℕ, ∀ (y : grp G β) (g : G.GAf), f (g⁻¹ * toAfF G β x t hx y * g) ≠ 0 →
    ∀ c : G.Cˣ, (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = c * (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * ((c⁻¹ : G.Cˣ) : G.C) →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ∉ S → ∃ (u : ℚ_[ℓ]ˣ) (z : (ℚ_[ℓ] ⊗[ℚ] G.C)ˣ), Commute (z : ℚ_[ℓ] ⊗[ℚ] G.C) (inC G ℚ_[ℓ] (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) ∧
      inC G ℚ_[ℓ] (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) = algebraMap ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] G.C) (u : ℚ_[ℓ]) * ((z : ℚ_[ℓ] ⊗[ℚ] G.C) * inC G ℚ_[ℓ] (β : G.C) *
        (starT G.star ℚ_[ℓ] (z : ℚ_[ℓ] ⊗[ℚ] G.C)).unop * inC G ℚ_[ℓ] ((β⁻¹ : G.Cˣ) : G.C)) := by
  intro p _ G L f hf β x t hx hβ y₀ hsep hdeg
  have hcomm : ∀ a b : G.C, Commute a (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) →
      Commute b (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) → Commute a b :=
    fun a b ha hb => GlobalTheory.LKCx.ClsReg.commute_of_commute_of_separable G _ hsep hdeg a b ha hb
  obtain ⟨Ω, hΩc, hΩ⟩ := GlobalTheory.T.exists_compact_support_twistedHeckeTestFunction p G L f hf
  have hev := eventually_compL_mem_intPts p G Ω hΩc
  have hlat := GlobalTheory.T.eventually_kottwitz_lattice_separable_minpoly p G (y₀ : G.Cˣ × ℚˣ).1 hsep hdeg
  have hnorm := GlobalTheory.T.eventually_tauFixed_unit_centralizer_is_norm p G β hβ (y₀ : G.Cˣ × ℚˣ).1 _ y₀.2.1 hsep hdeg
  have hstab := GlobalTheory.FinClsLoc.intC_stab p G β
  obtain ⟨S, hS⟩ := GlobalTheory.FinClsLoc.exists_finset_forall_prime_awayP_padic p _ (hev.and (hlat.and (hnorm.and hstab)))
  refine ⟨S, fun y g hfy c hc ℓ _ hℓ => ?_⟩
  obtain ⟨w, ⟨hev', hlat', hnorm', hmul, hstar, hβi, hβi'⟩, ⟨e⟩⟩ := hS ℓ hℓ
  apply GlobalTheory.T.localTwistedNormConclusion_transfer_ringEquiv p G (w.1.adicCompletion ℚ) ℚ_[ℓ] e
  have hint := hev' _ (hΩ _ hfy)
  obtain ⟨k, lam, hk1, hk2, hk3⟩ := GlobalTheory.T.exists_local_conj_trivialization_at_place_awayP p G β x t hx y g c (y₀ : G.Cˣ × ℚˣ).1 hc w
  obtain ⟨z, m, hz, hm, hm', hkzm⟩ := hlat' k (by rw [hk1]; exact hint.1) (by rw [hk2]; exact hint.2.1)
  have hap := GlobalTheory.grp_conj_unit_props p G β hβ y y₀ c hc (GlobalTheory.grp_factor_eq_of_conj p G β y y₀ c hc)
  have hinv := starT_invol G (w.1.adicCompletion ℚ)
  have hbb : inC G (w.1.adicCompletion ℚ) ((β⁻¹ : G.Cˣ) : G.C) * inC G (w.1.adicCompletion ℚ) (β : G.C) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have hβ' : (starT G.star (w.1.adicCompletion ℚ) (inC G (w.1.adicCompletion ℚ) (β : G.C))).unop = inC G (w.1.adicCompletion ℚ) (β : G.C) := by
    show (starT G.star (w.1.adicCompletion ℚ) ((1 : w.1.adicCompletion ℚ) ⊗ₜ (β : G.C))).unop = (1 : w.1.adicCompletion ℚ) ⊗ₜ (β : G.C)
    rw [starT_tmul]
    exact congrArg (TensorProduct.tmul ℚ (1 : w.1.adicCompletion ℚ)) hβ
  have hY' : inC G (w.1.adicCompletion ℚ) (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * inC G (w.1.adicCompletion ℚ) (β : G.C) *
      (starT G.star (w.1.adicCompletion ℚ) (inC G (w.1.adicCompletion ℚ) (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C))).unop =
      algebraMap (w.1.adicCompletion ℚ) (w.1.adicCompletion ℚ ⊗[ℚ] G.C) (algebraMap ℚ (w.1.adicCompletion ℚ) ((y₀ : G.Cˣ × ℚˣ).2 : ℚ)) * inC G (w.1.adicCompletion ℚ) (β : G.C) := by
    have h := congrArg (inC G (w.1.adicCompletion ℚ)) y₀.2.1
    rw [map_mul, map_mul, map_mul] at h
    have e1 : inC G (w.1.adicCompletion ℚ) (sh G (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) =
        (starT G.star (w.1.adicCompletion ℚ) (inC G (w.1.adicCompletion ℚ) (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C))).unop :=
      (starT_tmul G.star (w.1.adicCompletion ℚ) 1 _).symm
    have e2 : inC G (w.1.adicCompletion ℚ) (algebraMap ℚ G.C ((y₀ : G.Cˣ × ℚˣ).2 : ℚ)) =
        algebraMap (w.1.adicCompletion ℚ) (w.1.adicCompletion ℚ ⊗[ℚ] G.C) (algebraMap ℚ (w.1.adicCompletion ℚ) ((y₀ : G.Cˣ × ℚˣ).2 : ℚ)) := by
      rw [← IsScalarTower.algebraMap_apply]
      exact (Algebra.TensorProduct.includeRight : G.C →ₐ[ℚ] w.1.adicCompletion ℚ ⊗[ℚ] G.C).commutes _
    rw [e1, e2] at h
    exact h
  have hN : ∀ m' : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ, (m' : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) = m * (starT G.star (w.1.adicCompletion ℚ) (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop * inC G (w.1.adicCompletion ℚ) ((β⁻¹ : G.Cˣ) : G.C) →
      Commute (m' : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) (inC G (w.1.adicCompletion ℚ) (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) →
      inC G (w.1.adicCompletion ℚ) (β : G.C) * (starT G.star (w.1.adicCompletion ℚ) (m' : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop * inC G (w.1.adicCompletion ℚ) ((β⁻¹ : G.Cˣ) : G.C) = m' →
      ∃ v : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ, Commute (v : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) (inC G (w.1.adicCompletion ℚ) (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) ∧
        (m' : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) = v * (inC G (w.1.adicCompletion ℚ) (β : G.C) * (starT G.star (w.1.adicCompletion ℚ) (v : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop * inC G (w.1.adicCompletion ℚ) ((β⁻¹ : G.Cˣ) : G.C)) := by
    intro m' hm'v hcm hτ
    have hss : (starT G.star (w.1.adicCompletion ℚ) (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop * (starT G.star (w.1.adicCompletion ℚ) ((m⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop = 1 := by
      rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
    have h1 : (m' : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) * (inC G (w.1.adicCompletion ℚ) (β : G.C) * (starT G.star (w.1.adicCompletion ℚ) ((m⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop *
        ((m⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))) = 1 := by
      rw [hm'v]
      calc _ = (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) * ((starT G.star (w.1.adicCompletion ℚ) (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop *
            (inC G (w.1.adicCompletion ℚ) ((β⁻¹ : G.Cˣ) : G.C) * inC G (w.1.adicCompletion ℚ) (β : G.C)) *
            (starT G.star (w.1.adicCompletion ℚ) ((m⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop) * ((m⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) := by
            simp only [mul_assoc]
        _ = 1 := by rw [hbb, mul_one, hss, mul_one, Units.mul_inv]
    have hinv' := Units.inv_eq_of_mul_eq_one_right h1
    refine hnorm' m' hcm ?_ ?_ hτ
    · rw [hm'v]; exact hmul _ _ (hmul _ _ hm (hstar _ hm)) hβi'
    · rw [hinv']; exact hmul _ _ (hmul _ _ hβi (hstar _ hm')) hm'
  have halg := GlobalTheory.twisted_norm_local_step (starT G.star (w.1.adicCompletion ℚ)) hinv
    (Units.map (inC G (w.1.adicCompletion ℚ)).toMonoidHom β)
    (Units.map (inC G (w.1.adicCompletion ℚ)).toMonoidHom (y₀ : G.Cˣ × ℚˣ).1) k z m
    (inC G (w.1.adicCompletion ℚ) (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)))
    lam (Units.map (algebraMap ℚ (w.1.adicCompletion ℚ)).toMonoidHom (y₀ : G.Cˣ × ℚˣ).2) hβ' hY'
    (hap.2.1.map (inC G (w.1.adicCompletion ℚ))) hk3 hkzm hz hN
  obtain ⟨z', hz', hz'eq⟩ := halg
  exact ⟨lam, z', hz', hz'eq⟩

end GlobalTheory.CxRegLoc
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorRegularConjugateLocalScalarNormStatement

section

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
theorem _root_.GlobalTheory.T.harrisTaylor_regular_conjugate_local_scalar_norm : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ),
    IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
    ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), sh G β = β →
    ∀ y₀ : grp G β, (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable →
    (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n →
    ∃ S : Finset ℕ, ∀ (y : grp G β) (g : G.GAf), f (g⁻¹ * toAfF G β x t hx y * g) ≠ 0 →
    ∀ c : G.Cˣ, (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = c * (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * ((c⁻¹ : G.Cˣ) : G.C) →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ∉ S → ∃ (u : ℚ_[ℓ]ˣ) (z : (ℚ_[ℓ] ⊗[ℚ] G.C)ˣ), Commute (z : ℚ_[ℓ] ⊗[ℚ] G.C) (inC G ℚ_[ℓ] (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) ∧
      inC G ℚ_[ℓ] (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) = algebraMap ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] G.C) (u : ℚ_[ℓ]) * ((z : ℚ_[ℓ] ⊗[ℚ] G.C) * inC G ℚ_[ℓ] (β : G.C) *
        (starT G.star ℚ_[ℓ] (z : ℚ_[ℓ] ⊗[ℚ] G.C)).unop * inC G ℚ_[ℓ] ((β⁻¹ : G.Cˣ) : G.C)) := by
  first | exact @GlobalTheory.CxRegLoc.local_class_scalar_norm_sep | exact GlobalTheory.CxRegLoc.local_class_scalar_norm_sep
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedConjugatesAlgebraRelation

section

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.Div

theorem conj_of_twist : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ) (y₁ y₂ : grp G β) (y₀ c₁ c₂ w : G.Cˣ) (r : ℚ),
    (((y₁ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = c₁ * y₀ * ((c₁⁻¹ : G.Cˣ) : G.C) →
    (((y₂ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = c₂ * y₀ * ((c₂⁻¹ : G.Cˣ) : G.C) →
    (y₁ : G.Cˣ × ℚˣ).2 = (y₂ : G.Cˣ × ℚˣ).2 → Commute (w : G.C) y₀ → 0 < r →
    (((c₂⁻¹ : G.Cˣ) : G.C) * β * sh G ((c₂⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) = algebraMap ℚ G.C r * ((w : G.C) * (((c₁⁻¹ : G.Cˣ) : G.C) * β * sh G ((c₁⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) * ((β : G.C) * sh G (w : G.C) * ((β⁻¹ : G.Cˣ) : G.C))) →
    ∃ γ : grp G β, y₂ = γ * y₁ * γ⁻¹ := by
  intro p _ G β y₁ y₂ y₀ c₁ c₂ w r h1 h2 hs hw hr H
  have shm : ∀ a b : G.C, sh G (a * b) = sh G b * sh G a := by
    intro a b; simp only [sh, map_mul, MulOpposite.unop_mul]
  have shc : sh G ((c₂⁻¹ : G.Cˣ) : G.C) * sh G (c₂ : G.C) = 1 := by
    rw [← shm, Units.mul_inv]; simp [sh]
  have hR : algebraMap ℚ G.C r⁻¹ * algebraMap ℚ G.C r = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hr.ne', map_one]
  set ru : ℚˣ := Units.mk0 r hr.ne' with hru

  have HX : (w : G.C) * (((c₁⁻¹ : G.Cˣ) : G.C) * β * sh G ((c₁⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) *
      ((β : G.C) * sh G (w : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) = algebraMap ℚ G.C r⁻¹ *
      (((c₂⁻¹ : G.Cˣ) : G.C) * β * sh G ((c₂⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) := by
    rw [H, ← mul_assoc (algebraMap ℚ G.C r⁻¹), hR, one_mul]
  have mem : ((c₂ * w * c₁⁻¹, ru⁻¹) : G.Cˣ × ℚˣ) ∈ grp G β := by
    refine ⟨?_, ?_⟩
    · change ((c₂ * w * c₁⁻¹ : G.Cˣ) : G.C) * β * sh G ((c₂ * w * c₁⁻¹ : G.Cˣ) : G.C) =
        algebraMap ℚ G.C ((ru⁻¹ : ℚˣ) : ℚ) * β
      rw [Units.val_inv_eq_inv_val, hru, Units.val_mk0]
      simp only [Units.val_mul, shm]
      calc (c₂ : G.C) * w * ((c₁⁻¹ : G.Cˣ) : G.C) * β * (sh G ((c₁⁻¹ : G.Cˣ) : G.C) * (sh G (w : G.C) * sh G (c₂ : G.C)))
          = c₂ * ((w : G.C) * (((c₁⁻¹ : G.Cˣ) : G.C) * β * sh G ((c₁⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) *
            ((β : G.C) * sh G (w : G.C) * ((β⁻¹ : G.Cˣ) : G.C))) * β * sh G (c₂ : G.C) := by
            simp only [mul_assoc, Units.inv_mul_cancel_left]
        _ = algebraMap ℚ G.C r⁻¹ * ((c₂ : G.C) * ((c₂⁻¹ : G.Cˣ) : G.C) * β *
              (sh G ((c₂⁻¹ : G.Cˣ) : G.C) * sh G (c₂ : G.C))) := by
            rw [HX, Algebra.left_comm]
            simp only [mul_assoc, Units.inv_mul_cancel_left]
        _ = _ := by rw [shc, Units.mul_inv, one_mul, mul_one]
    · change 0 < ((ru⁻¹ : ℚˣ) : ℚ)
      rw [Units.val_inv_eq_inv_val, hru, Units.val_mk0]; exact inv_pos.2 hr
  refine ⟨⟨_, mem⟩, ?_⟩
  have e1 : (y₁ : G.Cˣ × ℚˣ).1 = c₁ * y₀ * c₁⁻¹ := Units.ext (by rw [h1]; simp)
  have e2 : (y₂ : G.Cˣ × ℚˣ).1 = c₂ * y₀ * c₂⁻¹ := Units.ext (by rw [h2]; simp)
  have hwu : w * y₀ = y₀ * w := Units.ext (by simpa using hw.eq)
  have hwu' : ∀ x : G.Cˣ, w * (y₀ * x) = y₀ * (w * x) := fun x => by rw [← mul_assoc, hwu, mul_assoc]
  apply Subtype.ext
  apply Prod.ext
  · show (y₂ : G.Cˣ × ℚˣ).1 = (c₂ * w * c₁⁻¹) * (y₁ : G.Cˣ × ℚˣ).1 * (c₂ * w * c₁⁻¹)⁻¹
    rw [e1, e2]
    simp only [_root_.mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left, hwu', mul_inv_cancel_left]
  · show (y₂ : G.Cˣ × ℚˣ).2 = ru⁻¹ * (y₁ : G.Cˣ × ℚˣ).2 * ru⁻¹⁻¹
    rw [hs, mul_comm ru⁻¹, mul_assoc, mul_inv_cancel, mul_one]

end GlobalTheory.Div
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicEmbeddingValuationSubring

section

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKCx.ClsReg

theorem classes_finite : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ v : InfinitePlace G.F, sigPosH (G.gram_herm v) = 1 → ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), (∀ (y : grp G β) (h : G.GAf), f (h⁻¹ * toAfF G β x t hx y * h) ≠ 0 → (∃ z : Fin G.n → ℂ, 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re ∧ FixL G v β y z) → (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n ∧ (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable) → sh G β = β → (∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) → ∀ P : Polynomial G.F, ∃ Y : Finset (grp G β), ∀ y : grp G β, minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = P → (∃ a : Dat G v β, FixL G v β y a.2.1 ∧ f (a.1.1⁻¹ * toAfF G β x t hx y * a.1.1) * f' (a.1.2⁻¹ * toP1 G β y * a.1.2) ≠ 0) → ∃ y₀ ∈ Y, ∃ γ : grp G β, y = γ * y₀ * γ⁻¹ := by
  intro p _ G _ v _ L f hf K' f' _ β x t hx hreg hβ _ P
  by_cases hne : ∃ y₀ : grp G β, minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = P ∧
      ∃ a : Dat G v β, FixL G v β y₀ a.2.1 ∧
        f (a.1.1⁻¹ * toAfF G β x t hx y₀ * a.1.1) * f' (a.1.2⁻¹ * toP1 G β y₀ * a.1.2) ≠ 0
  swap
  · exact ⟨∅, fun y hy ha => absurd ⟨y, hy, ha⟩ hne⟩
  obtain ⟨y₀, hP₀, a₀, hfix₀, ha₀⟩ := hne
  obtain ⟨hdeg₀, hsep₀⟩ := hreg y₀ a₀.1.1 (left_ne_zero_of_mul ha₀) ⟨a₀.2.1, a₀.2.2, hfix₀⟩
  obtain ⟨hy₀, -⟩ := y₀.prop
  obtain ⟨S, hS⟩ := GlobalTheory.T.harrisTaylor_regular_conjugate_local_scalar_norm p G L f hf β x t hx hβ y₀ hsep₀ hdeg₀
  obtain ⟨A, hA⟩ := GlobalTheory.T.finite_fixed_unit_classes_centralizer_regular p G β hβ ((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) (((y₀ : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) hy₀ hsep₀ hdeg₀ S
  have key : ∀ y : grp G β, minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = P → ∀ g : G.GAf,
      f (g⁻¹ * toAfF G β x t hx y * g) ≠ 0 → ∃ a' ∈ A, ∃ b : Bool, ∃ (c : G.Cˣ) (r : ℚˣ) (e : G.Cˣ),
        (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = c * (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * ((c⁻¹ : G.Cˣ) : G.C) ∧
        Commute (e : G.C) (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) ∧ decide (0 < (r : ℚ)) = b ∧
        (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) = algebraMap ℚ G.C (r : ℚ) * ((e : G.C) * a' * ((β : G.C) * sh G (e : G.C) * ((β⁻¹ : G.Cˣ) : G.C))) := by
    intro y hy g hg
    obtain ⟨c, hc⟩ := units_conj_of_minpoly_eq_of_separable G ((y : G.Cˣ × ℚˣ).1) ((y₀ : G.Cˣ × ℚˣ).1)
      (by rw [hy, hP₀]) hsep₀ hdeg₀
    have h2 := GlobalTheory.grp_factor_eq_of_conj p G β y y₀ c hc
    obtain ⟨hu, hcm, hfix⟩ := GlobalTheory.grp_conj_unit_props p G β hβ y y₀ c hc h2
    obtain ⟨a', ha', r, e, he, hre⟩ := hA _ hu hcm hfix (fun ℓ _ hℓ => hS y g hg c hc ℓ hℓ)
    exact ⟨a', ha', decide (0 < (r : ℚ)), c, r, e, hc, he, rfl, hre⟩
  let D : G.C × Bool → grp G β → Prop := fun ab y => ∃ (c : G.Cˣ) (r : ℚˣ) (e : G.Cˣ),
        (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = c * (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * ((c⁻¹ : G.Cˣ) : G.C) ∧
        Commute (e : G.C) (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) ∧ decide (0 < (r : ℚ)) = ab.2 ∧
        (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) = algebraMap ℚ G.C (r : ℚ) * ((e : G.C) * ab.1 * ((β : G.C) * sh G (e : G.C) * ((β⁻¹ : G.Cˣ) : G.C)))
  let ρ : G.C × Bool → grp G β := fun ab => if h : ∃ y, D ab y then h.choose else 1
  refine ⟨(A ×ˢ (Finset.univ : Finset Bool)).image ρ, ?_⟩
  rintro y hy ⟨a, _, ha⟩
  obtain ⟨a', ha', b, hD⟩ := key y hy a.1.1 (left_ne_zero_of_mul ha)
  have hex : ∃ y, D (a', b) y := ⟨y, hD⟩
  refine ⟨ρ (a', b), Finset.mem_image_of_mem _ (Finset.mem_product.2 ⟨ha', Finset.mem_univ _⟩), ?_⟩
  have hρ : ρ (a', b) = hex.choose := dif_pos hex
  rw [hρ]
  obtain ⟨c', r', e', hc', he', hb', hre'⟩ := hex.choose_spec
  dsimp only at hb' hre'
  obtain ⟨c, r, e, hc, he, hb, hre⟩ := hD
  have h2 : (hex.choose : G.Cˣ × ℚˣ).2 = (y : G.Cˣ × ℚˣ).2 := by
    rw [GlobalTheory.grp_factor_eq_of_conj p G β _ y₀ c' hc', GlobalTheory.grp_factor_eq_of_conj p G β y y₀ c hc]
  refine GlobalTheory.Div.conj_of_twist p G β hex.choose y ((y₀ : G.Cˣ × ℚˣ).1) c' c (e * e'⁻¹) ((r : ℚ) / r') hc' hc h2 ?_ ?_ ?_
  · rw [Units.val_mul]
    exact he.mul_left he'.units_inv_left
  · have hr : (0 < (r : ℚ)) ↔ (0 < (r' : ℚ)) := by
      rw [← decide_eq_decide, hb, hb']
    rcases lt_or_gt_of_ne r'.ne_zero with h | h
    · have hn : ¬ (0 < (r : ℚ)) := fun h0 => absurd (hr.1 h0) (not_lt.2 h.le)
      exact div_pos_of_neg_of_neg (lt_of_le_of_ne (not_lt.1 hn) r.ne_zero) h
    · exact div_pos (hr.2 h) h
  · rw [hre', hre]
    exact conj_rel_alg' G β e e' a' r r'

end GlobalTheory.LKCx.ClsReg
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalIntegralTestFunctionFirst

section

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
theorem _root_.GlobalTheory.T.orbital_integral_test_function_first : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ v : InfinitePlace G.F, sigPosH (G.gram_herm v) = 1 → ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), (∀ (y : grp G β) (h : G.GAf), f (h⁻¹ * toAfF G β x t hx y * h) ≠ 0 → (∃ z : Fin G.n → ℂ, 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re ∧ FixL G v β y z) → (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n ∧ (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable) → sh G β = β → (∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) → ∀ P : Polynomial G.F, ∃ Y : Finset (grp G β), ∀ y : grp G β, minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = P → (∃ a : Dat G v β, FixL G v β y a.2.1 ∧ f (a.1.1⁻¹ * toAfF G β x t hx y * a.1.1) * f' (a.1.2⁻¹ * toP1 G β y * a.1.2) ≠ 0) → ∃ y₀ ∈ Y, ∃ γ : grp G β, y = γ * y₀ * γ⁻¹ := by
  first | exact @GlobalTheory.LKCx.ClsReg.classes_finite | exact GlobalTheory.LKCx.ClsReg.classes_finite
end
end
