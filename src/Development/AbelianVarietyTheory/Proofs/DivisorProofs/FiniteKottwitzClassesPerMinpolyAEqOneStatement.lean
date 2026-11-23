module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugatePairRelated
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFixedUnitClassesCentralizerRegularStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CofinitePlacesRealizePrimes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyKottwitzLatticeSeparableMinpolyStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyTauFixedUnitCentralizerIsNormStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactSupportTwistedHeckeTestFunctionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHodgeLatticeGermSystem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalConjTrivializationAtPlaceAwayP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralConjugationStableStructure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTwistedNormConclusionTransferRingEquivStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalSupportFinitePrimeSet
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedNormUnitCommutation
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsConjOfMinpolyEqOfSeparable
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KottwitzPairFormRatioLocalScalarNorm

section

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.CxRegPair

variable {p : ℕ} [Fact p.Prime]

theorem sh_mul_sh_inv (G : HTGroup p) (c : G.Cˣ) : sh G (c : G.C) * sh G ((c⁻¹ : G.Cˣ) : G.C) = 1 := by
  simp only [sh]
  rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]

theorem commute_mul_inv_of_sim (G : HTGroup p) (β β₁ γ : G.Cˣ) (c : ℚ)
    (h : (γ : G.C) * β * sh G γ = algebraMap ℚ G.C c * β)
    (h₁ : (γ : G.C) * β₁ * sh G γ = algebraMap ℚ G.C c * β₁) :
    Commute ((β : G.C) * ((β₁⁻¹ : G.Cˣ) : G.C)) (γ : G.C) := by
  have key : (γ : G.C) * ((β : G.C) * ((β₁⁻¹ : G.Cˣ) : G.C)) * ((β₁ : G.C) * sh G γ) =
      (β : G.C) * ((β₁⁻¹ : G.Cˣ) : G.C) * γ * ((β₁ : G.C) * sh G γ) := by
    calc (γ : G.C) * ((β : G.C) * ((β₁⁻¹ : G.Cˣ) : G.C)) * ((β₁ : G.C) * sh G γ)
        = (γ : G.C) * β * (((β₁⁻¹ : G.Cˣ) : G.C) * β₁) * sh G γ := by simp only [mul_assoc]
      _ = algebraMap ℚ G.C c * β := by rw [Units.inv_mul, mul_one, h]
      _ = (β : G.C) * ((β₁⁻¹ : G.Cˣ) : G.C) * (algebraMap ℚ G.C c * β₁) := by
          rw [mul_assoc, ← mul_assoc ((β₁⁻¹ : G.Cˣ) : G.C), ← Algebra.commutes, mul_assoc, Units.inv_mul, mul_one, Algebra.commutes]
      _ = _ := by rw [← h₁]; simp only [mul_assoc]
  have hinv : ((β₁ : G.C) * sh G γ) * (sh G ((γ⁻¹ : G.Cˣ) : G.C) * ((β₁⁻¹ : G.Cˣ) : G.C)) = 1 := by
    rw [mul_assoc, ← mul_assoc (sh G γ), sh_mul_sh_inv, one_mul, Units.mul_inv]
  show (β : G.C) * ((β₁⁻¹ : G.Cˣ) : G.C) * γ = γ * ((β : G.C) * ((β₁⁻¹ : G.Cˣ) : G.C))
  have := congrArg (· * (sh G ((γ⁻¹ : G.Cˣ) : G.C) * ((β₁⁻¹ : G.Cˣ) : G.C))) key
  simp only [mul_assoc] at this hinv
  simp only [mul_assoc]
  rw [hinv, mul_one, mul_one] at this
  exact this.symm

theorem glue_pair (G : HTGroup p) (P : Pair G) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) P.β x t) (g : G.GAf) (w : AwayP p) :
    ∃ (k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) (lam : (w.1.adicCompletion ℚ)ˣ),
      (k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) * inC G (w.1.adicCompletion ℚ) (P.γ : G.C) * ((k⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) = ((((compL G w (g⁻¹ * P.toAf x t hx P.self * g) : UPts G.star (w.1.adicCompletion ℚ)) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ × (w.1.adicCompletion ℚ)ˣ).1 : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) ∧
      (k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) * inC G (w.1.adicCompletion ℚ) ((P.γ⁻¹ : G.Cˣ) : G.C) * ((k⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) = (((((compL G w (g⁻¹ * P.toAf x t hx P.self * g) : UPts G.star (w.1.adicCompletion ℚ)) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ × (w.1.adicCompletion ℚ)ˣ).1 : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ)⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) ∧
      (k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) * inC G (w.1.adicCompletion ℚ) (P.β : G.C) * (starT G.star (w.1.adicCompletion ℚ) (k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop = algebraMap (w.1.adicCompletion ℚ) (w.1.adicCompletion ℚ ⊗[ℚ] G.C) (lam : w.1.adicCompletion ℚ) := by
  let φ := Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C)
  let u : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ :=
    ((compL G w g : UPts G.star (w.1.adicCompletion ℚ)) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ × (w.1.adicCompletion ℚ)ˣ).1
  let ν : (w.1.adicCompletion ℚ)ˣ :=
    ((compL G w g : UPts G.star (w.1.adicCompletion ℚ)) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ × (w.1.adicCompletion ℚ)ˣ).2
  let xw : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ := Units.map (φ : AfP p ⊗[ℚ] G.C →* w.1.adicCompletion ℚ ⊗[ℚ] G.C) x
  let mY : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ := Units.map (inC G (w.1.adicCompletion ℚ)).toMonoidHom P.γ
  let tw : (w.1.adicCompletion ℚ)ˣ := Units.map (AfP.eval w : AfP p →* w.1.adicCompletion ℚ) t
  have hT : ((compL G w (P.toAf x t hx P.self) : UPts G.star (w.1.adicCompletion ℚ)) :
      (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ × (w.1.adicCompletion ℚ)ˣ).1 = xw * mY * xw⁻¹ := by
    apply Units.ext
    show φ ((x : AfP p ⊗[ℚ] G.C) * inC G (AfP p) (P.γ : G.C) * ((x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C)) = _
    rw [map_mul, map_mul, glueL_evalT_inC]
    rfl
  have E : ((compL G w (g⁻¹ * P.toAf x t hx P.self * g) : UPts G.star (w.1.adicCompletion ℚ)) :
      (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ × (w.1.adicCompletion ℚ)ˣ).1 = (u⁻¹ * xw) * mY * (u⁻¹ * xw)⁻¹ := by
    rw [map_mul, map_mul, map_inv]
    change u⁻¹ * ((compL G w (P.toAf x t hx P.self) : UPts G.star (w.1.adicCompletion ℚ)) :
      (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ × (w.1.adicCompletion ℚ)ˣ).1 * u = _
    rw [hT]
    group
  refine ⟨u⁻¹ * xw, tw * ν⁻¹, ?_, ?_, ?_⟩
  · rw [E]; rfl
  · rw [E, show (u⁻¹ * xw * mY * (u⁻¹ * xw)⁻¹)⁻¹ = (u⁻¹ * xw) * mY⁻¹ * (u⁻¹ * xw)⁻¹ by group]
    rfl
  · have hu : ((u⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C) *
        (starT G.star (w.1.adicCompletion ℚ) ((u⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C)).unop =
        algebraMap (w.1.adicCompletion ℚ) (w.1.adicCompletion ℚ ⊗[ℚ] G.C) ((ν⁻¹ : (w.1.adicCompletion ℚ)ˣ) : w.1.adicCompletion ℚ) :=
      ((compL G w g)⁻¹).2
    have hxw : φ (x : AfP p ⊗[ℚ] G.C) * inC G (w.1.adicCompletion ℚ) (P.β : G.C) *
        (starT G.star (w.1.adicCompletion ℚ) (φ (x : AfP p ⊗[ℚ] G.C))).unop =
        algebraMap (w.1.adicCompletion ℚ) (w.1.adicCompletion ℚ ⊗[ℚ] G.C) (tw : w.1.adicCompletion ℚ) := by
      have h := congrArg φ hx
      rw [map_mul, map_mul, glueL_evalT_inC, glueL_evalT_starT, glueL_evalT_algebraMap] at h
      exact h
    have hk : (((u⁻¹ * xw : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ)) : w.1.adicCompletion ℚ ⊗[ℚ] G.C) =
        ((u⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C) * φ (x : AfP p ⊗[ℚ] G.C) := rfl
    rw [hk, RingHom.map_mul (starT G.star (w.1.adicCompletion ℚ)), MulOpposite.unop_mul]
    calc _ = ((u⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C) *
          (φ (x : AfP p ⊗[ℚ] G.C) * inC G (w.1.adicCompletion ℚ) (P.β : G.C) *
          (starT G.star (w.1.adicCompletion ℚ) (φ (x : AfP p ⊗[ℚ] G.C))).unop) *
          (starT G.star (w.1.adicCompletion ℚ) ((u⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C)).unop := by
          simp only [mul_assoc]
      _ = algebraMap (w.1.adicCompletion ℚ) (w.1.adicCompletion ℚ ⊗[ℚ] G.C) (tw : w.1.adicCompletion ℚ) *
          (((u⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C) *
          (starT G.star (w.1.adicCompletion ℚ) ((u⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C)).unop) := by
          rw [hxw, ← mul_assoc, ← Algebra.commutes, mul_assoc]
      _ = _ := by rw [hu, ← map_mul, Units.val_mul]

theorem local_pair_scalar_norm : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → (∀ g, f g ≠ 0 → RegAf G g) → ∀ P₁ : Pair G, ∃ S : Finset ℕ, ∀ (P : Pair G), P.γ = P₁.γ → P.c = P₁.c → ∀ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) (g : G.GAf), f (g⁻¹ * P.toAf x t hx P.self * g) ≠ 0 → ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ∉ S → ∃ (u : ℚ_[ℓ]ˣ) (z : (ℚ_[ℓ] ⊗[ℚ] G.C)ˣ), Commute (z : ℚ_[ℓ] ⊗[ℚ] G.C) (inC G ℚ_[ℓ] (P₁.γ : G.C)) ∧ inC G ℚ_[ℓ] ((P.β : G.C) * ((P₁.β⁻¹ : G.Cˣ) : G.C)) = algebraMap ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] G.C) (u : ℚ_[ℓ]) * ((z : ℚ_[ℓ] ⊗[ℚ] G.C) * inC G ℚ_[ℓ] (P₁.β : G.C) * (starT G.star ℚ_[ℓ] (z : ℚ_[ℓ] ⊗[ℚ] G.C)).unop * inC G ℚ_[ℓ] ((P₁.β⁻¹ : G.Cˣ) : G.C)) := by
  intro p _ G L f hf _ P₁
  have hdeg := P₁.reg.1
  have hsep := P₁.reg.2
  obtain ⟨Ω, hΩc, hΩ⟩ := GlobalTheory.T.exists_compact_support_twistedHeckeTestFunction p G L f hf
  have hev := eventually_compL_mem_intPts p G Ω hΩc
  have hlat := GlobalTheory.T.eventually_kottwitz_lattice_separable_minpoly p G P₁.γ hsep hdeg
  have hnorm := GlobalTheory.T.eventually_tauFixed_unit_centralizer_is_norm p G P₁.β P₁.sym P₁.γ (P₁.c : ℚ) P₁.sim hsep hdeg
  have hstab := GlobalTheory.FinClsLoc.intC_stab p G P₁.β
  obtain ⟨S, hS⟩ := GlobalTheory.FinClsLoc.exists_finset_forall_prime_awayP_padic p _ (hev.and (hlat.and (hnorm.and hstab)))
  refine ⟨S, fun P hγ hc x t hx g hfy ℓ _ hℓ => ?_⟩
  obtain ⟨w, ⟨hev', hlat', hnorm', hmul, hstar, hβi, hβi'⟩, ⟨e⟩⟩ := hS ℓ hℓ
  apply GlobalTheory.T.localTwistedNormConclusion_transfer_ringEquiv p G (w.1.adicCompletion ℚ) ℚ_[ℓ] e
  have hint := hev' _ (hΩ _ hfy)
  obtain ⟨k, lam, hk1, hk2, hk3⟩ := GlobalTheory.CxRegPair.glue_pair G P x t hx g w
  rw [hγ] at hk1 hk2
  obtain ⟨z, m, hz, hm, hm', hkzm⟩ := hlat' k (by rw [hk1]; exact hint.1) (by rw [hk2]; exact hint.2.1)
  have hcm : Commute ((P.β : G.C) * ((P₁.β⁻¹ : G.Cˣ) : G.C)) (P₁.γ : G.C) := by
    have h := P.sim
    rw [hγ, hc] at h
    exact GlobalTheory.CxRegPair.commute_mul_inv_of_sim G P.β P₁.β P₁.γ (P₁.c : ℚ) h P₁.sim
  have hinv := starT_invol G (w.1.adicCompletion ℚ)
  have hbb : inC G (w.1.adicCompletion ℚ) ((P₁.β⁻¹ : G.Cˣ) : G.C) * inC G (w.1.adicCompletion ℚ) (P₁.β : G.C) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have hβ' : (starT G.star (w.1.adicCompletion ℚ) (inC G (w.1.adicCompletion ℚ) (P₁.β : G.C))).unop = inC G (w.1.adicCompletion ℚ) (P₁.β : G.C) := by
    show (starT G.star (w.1.adicCompletion ℚ) ((1 : w.1.adicCompletion ℚ) ⊗ₜ (P₁.β : G.C))).unop = (1 : w.1.adicCompletion ℚ) ⊗ₜ (P₁.β : G.C)
    rw [starT_tmul]
    exact congrArg (TensorProduct.tmul ℚ (1 : w.1.adicCompletion ℚ)) P₁.sym
  have hY' : inC G (w.1.adicCompletion ℚ) (P₁.γ : G.C) * inC G (w.1.adicCompletion ℚ) (P₁.β : G.C) *
      (starT G.star (w.1.adicCompletion ℚ) (inC G (w.1.adicCompletion ℚ) (P₁.γ : G.C))).unop =
      algebraMap (w.1.adicCompletion ℚ) (w.1.adicCompletion ℚ ⊗[ℚ] G.C) (algebraMap ℚ (w.1.adicCompletion ℚ) (P₁.c : ℚ)) * inC G (w.1.adicCompletion ℚ) (P₁.β : G.C) := by
    have h := congrArg (inC G (w.1.adicCompletion ℚ)) P₁.sim
    rw [map_mul, map_mul, map_mul] at h
    have e1 : inC G (w.1.adicCompletion ℚ) (sh G (P₁.γ : G.C)) =
        (starT G.star (w.1.adicCompletion ℚ) (inC G (w.1.adicCompletion ℚ) (P₁.γ : G.C))).unop :=
      (starT_tmul G.star (w.1.adicCompletion ℚ) 1 _).symm
    have e2 : inC G (w.1.adicCompletion ℚ) (algebraMap ℚ G.C (P₁.c : ℚ)) =
        algebraMap (w.1.adicCompletion ℚ) (w.1.adicCompletion ℚ ⊗[ℚ] G.C) (algebraMap ℚ (w.1.adicCompletion ℚ) (P₁.c : ℚ)) := by
      rw [← IsScalarTower.algebraMap_apply]
      exact (Algebra.TensorProduct.includeRight : G.C →ₐ[ℚ] w.1.adicCompletion ℚ ⊗[ℚ] G.C).commutes _
    rw [e1, e2] at h
    exact h
  have hk3' : (k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) * (inC G (w.1.adicCompletion ℚ) ((P.β : G.C) * ((P₁.β⁻¹ : G.Cˣ) : G.C)) * inC G (w.1.adicCompletion ℚ) (P₁.β : G.C)) * (starT G.star (w.1.adicCompletion ℚ) (k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop = algebraMap (w.1.adicCompletion ℚ) (w.1.adicCompletion ℚ ⊗[ℚ] G.C) (lam : w.1.adicCompletion ℚ) := by
    rw [← map_mul, mul_assoc (P.β : G.C), Units.inv_mul, mul_one]
    exact hk3
  have hN : ∀ m' : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ, (m' : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) = m * (starT G.star (w.1.adicCompletion ℚ) (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop * inC G (w.1.adicCompletion ℚ) ((P₁.β⁻¹ : G.Cˣ) : G.C) →
      Commute (m' : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) (inC G (w.1.adicCompletion ℚ) (P₁.γ : G.C)) →
      inC G (w.1.adicCompletion ℚ) (P₁.β : G.C) * (starT G.star (w.1.adicCompletion ℚ) (m' : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop * inC G (w.1.adicCompletion ℚ) ((P₁.β⁻¹ : G.Cˣ) : G.C) = m' →
      ∃ v : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ, Commute (v : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) (inC G (w.1.adicCompletion ℚ) (P₁.γ : G.C)) ∧
        (m' : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) = v * (inC G (w.1.adicCompletion ℚ) (P₁.β : G.C) * (starT G.star (w.1.adicCompletion ℚ) (v : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop * inC G (w.1.adicCompletion ℚ) ((P₁.β⁻¹ : G.Cˣ) : G.C)) := by
    intro m' hm'v hcm' hτ
    have hss : (starT G.star (w.1.adicCompletion ℚ) (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop * (starT G.star (w.1.adicCompletion ℚ) ((m⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop = 1 := by
      rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
    have h1 : (m' : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) * (inC G (w.1.adicCompletion ℚ) (P₁.β : G.C) * (starT G.star (w.1.adicCompletion ℚ) ((m⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop *
        ((m⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))) = 1 := by
      rw [hm'v]
      calc _ = (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) * ((starT G.star (w.1.adicCompletion ℚ) (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop *
            (inC G (w.1.adicCompletion ℚ) ((P₁.β⁻¹ : G.Cˣ) : G.C) * inC G (w.1.adicCompletion ℚ) (P₁.β : G.C)) *
            (starT G.star (w.1.adicCompletion ℚ) ((m⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop) * ((m⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) := by
            simp only [mul_assoc]
        _ = 1 := by rw [hbb, mul_one, hss, mul_one, Units.mul_inv]
    have hinv' := Units.inv_eq_of_mul_eq_one_right h1
    refine hnorm' m' hcm' ?_ ?_ hτ
    · rw [hm'v]; exact hmul _ _ (hmul _ _ hm (hstar _ hm)) hβi'
    · rw [hinv']; exact hmul _ _ (hmul _ _ hβi (hstar _ hm')) hm'
  have halg := GlobalTheory.twisted_norm_local_step (starT G.star (w.1.adicCompletion ℚ)) hinv
    (Units.map (inC G (w.1.adicCompletion ℚ)).toMonoidHom P₁.β)
    (Units.map (inC G (w.1.adicCompletion ℚ)).toMonoidHom P₁.γ) k z m
    (inC G (w.1.adicCompletion ℚ) ((P.β : G.C) * ((P₁.β⁻¹ : G.Cˣ) : G.C)))
    lam (Units.map (algebraMap ℚ (w.1.adicCompletion ℚ)).toMonoidHom P₁.c) hβ' hY'
    (hcm.map (inC G (w.1.adicCompletion ℚ))) hk3' hkzm hz hN
  obtain ⟨z', hz', hz'eq⟩ := halg
  exact ⟨lam, z', hz', hz'eq⟩

end GlobalTheory.CxRegPair
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KottwitzPairFormRatioLocalScalarNormStatement

section

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.kottwitzPair_form_ratio_local_scalar_norm : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → (∀ g, f g ≠ 0 → RegAf G g) → ∀ P₁ : Pair G, ∃ S : Finset ℕ, ∀ (P : Pair G), P.γ = P₁.γ → P.c = P₁.c → ∀ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) (g : G.GAf), f (g⁻¹ * P.toAf x t hx P.self * g) ≠ 0 → ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ∉ S → ∃ (u : ℚ_[ℓ]ˣ) (z : (ℚ_[ℓ] ⊗[ℚ] G.C)ˣ), Commute (z : ℚ_[ℓ] ⊗[ℚ] G.C) (inC G ℚ_[ℓ] (P₁.γ : G.C)) ∧ inC G ℚ_[ℓ] ((P.β : G.C) * ((P₁.β⁻¹ : G.Cˣ) : G.C)) = algebraMap ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] G.C) (u : ℚ_[ℓ]) * ((z : ℚ_[ℓ] ⊗[ℚ] G.C) * inC G ℚ_[ℓ] (P₁.β : G.C) * (starT G.star ℚ_[ℓ] (z : ℚ_[ℓ] ⊗[ℚ] G.C)).unop * inC G ℚ_[ℓ] ((P₁.β⁻¹ : G.Cˣ) : G.C)) := by
  first | (exact @GlobalTheory.CxRegPair.local_pair_scalar_norm) | (exact GlobalTheory.CxRegPair.local_pair_scalar_norm) | (intros; apply GlobalTheory.CxRegPair.local_pair_scalar_norm  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SameElementSignAmbiguity

section

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid.Pair

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p}

theorem finiteQ (G : HTGroup p) : Module.Finite ℚ G.C := Module.Finite.trans G.F G.C

theorem norm_sim (P : Pair G) :
    Algebra.norm ℚ (P.γ : G.C) * Algebra.norm ℚ (sh G P.γ) = (P.c : ℚ) ^ Module.finrank ℚ G.C := by
  haveI := finiteQ G
  have h := congrArg (Algebra.norm ℚ) P.sim
  rw [map_mul, map_mul, map_mul, Algebra.norm_algebraMap] at h
  have hb : Algebra.norm ℚ (P.β : G.C) ≠ 0 := (P.β.isUnit.map (Algebra.norm ℚ)).ne_zero
  apply mul_right_cancel₀ hb
  rw [← h]; ring

theorem c_eq_or_eq_neg : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P P' : Pair G), P'.γ = P.γ → P'.c = P.c ∨ P'.c = -P.c := by
  intro p _ G P P' hγ
  haveI := finiteQ G
  have h1 := norm_sim P
  have h2 := norm_sim P'
  rw [hγ, h1] at h2
  have hN : Module.finrank ℚ G.C ≠ 0 := Module.finrank_pos.ne'
  rcases (pow_eq_pow_iff_of_ne_zero hN).1 h2.symm with h | ⟨h, _⟩
  · exact Or.inl (Units.ext h)
  · exact Or.inr (Units.ext (by rw [h, Units.val_neg]))

end GlobalTheory.LKMid.Pair
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteKottwitzClassesPerMinpolyAEqOne

section

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKCx.PeriodicClassFixedPoints

variable {p : ℕ} [Fact p.Prime]

theorem sh_mul' (G : HTGroup p) (a b : G.C) : sh G (a * b) = sh G b * sh G a := by
  simp only [sh, map_mul, MulOpposite.unop_mul]

theorem sh_one' (G : HTGroup p) : sh G 1 = 1 := by simp [sh]

theorem sh_mul_inv' (G : HTGroup p) (e : G.Cˣ) : sh G (e : G.C) * sh G ((e⁻¹ : G.Cˣ) : G.C) = 1 := by
  rw [← sh_mul', Units.inv_mul, sh_one']

theorem commute_ratio (G : HTGroup p) (β β₁ γ : G.Cˣ) (c : ℚ) (hc : c ≠ 0)
    (h : (γ : G.C) * β * sh G γ = algebraMap ℚ G.C c * β)
    (h₁ : (γ : G.C) * β₁ * sh G γ = algebraMap ℚ G.C c * β₁) :
    Commute ((β : G.C) * ((β₁⁻¹ : G.Cˣ) : G.C)) (γ : G.C) := by
  have hs : sh G γ = ((β₁⁻¹ : G.Cˣ) : G.C) * ((γ⁻¹ : G.Cˣ) : G.C) * (algebraMap ℚ G.C c * β₁) := by
    rw [← h₁]; simp [mul_assoc]
  rw [hs, ← Algebra.smul_def, ← Algebra.smul_def] at h
  simp only [mul_smul_comm] at h
  have h2 : (γ : G.C) * β * (((β₁⁻¹ : G.Cˣ) : G.C) * ((γ⁻¹ : G.Cˣ) : G.C) * β₁) = β := smul_right_injective G.C hc h
  have h3 : (γ : G.C) * β * ((β₁⁻¹ : G.Cˣ) : G.C) * ((γ⁻¹ : G.Cˣ) : G.C) = β * ((β₁⁻¹ : G.Cˣ) : G.C) := by
    conv_rhs => rw [← h2]
    simp [mul_assoc]
  show (β : G.C) * ((β₁⁻¹ : G.Cˣ) : G.C) * γ = γ * (β * ((β₁⁻¹ : G.Cˣ) : G.C))
  calc (β : G.C) * ((β₁⁻¹ : G.Cˣ) : G.C) * γ
      = ((γ : G.C) * β * ((β₁⁻¹ : G.Cˣ) : G.C) * ((γ⁻¹ : G.Cˣ) : G.C)) * γ := by rw [h3]
    _ = γ * (β * ((β₁⁻¹ : G.Cˣ) : G.C)) := by simp [mul_assoc]

theorem tau_ratio (G : HTGroup p) (β β₁ : G.Cˣ) (h : sh G β = β) (h₁ : sh G β₁ = β₁) :
    (β₁ : G.C) * sh G ((β : G.C) * ((β₁⁻¹ : G.Cˣ) : G.C)) * ((β₁⁻¹ : G.Cˣ) : G.C) =
      (β : G.C) * ((β₁⁻¹ : G.Cˣ) : G.C) := by
  have e : (β₁ : G.C) * sh G ((β₁⁻¹ : G.Cˣ) : G.C) = 1 := by
    conv_lhs => rw [← h₁]
    exact sh_mul_inv' G β₁
  rw [sh_mul', h, ← mul_assoc, e, one_mul]

theorem rel_of_same (G : HTGroup p) (β₁ γ₀ : G.Cˣ) (a₀ : G.C) (P Q : Pair G) (hP : P.γ = γ₀) (hQ : Q.γ = γ₀)
    (r r' : ℚˣ) (e e' : G.Cˣ) (he : Commute (e : G.C) γ₀) (he' : Commute (e' : G.C) γ₀)
    (hr : (0 < (r : ℚ)) ↔ (0 < (r' : ℚ)))
    (hPβ : (P.β : G.C) = algebraMap ℚ G.C r * ((e : G.C) * a₀ * β₁ * sh G (e : G.C)))
    (hQβ : (Q.β : G.C) = algebraMap ℚ G.C r' * ((e' : G.C) * a₀ * β₁ * sh G (e' : G.C))) : Pair.Rel P Q := by
  refine ⟨e' * e⁻¹, (r' : ℚ) / r, ?_, ?_, ?_⟩
  · rcases lt_or_gt_of_ne r.ne_zero with h | h
    · have hn : ¬ (0 < (r' : ℚ)) := fun h0 => absurd (hr.2 h0) (not_lt.2 h.le)
      exact div_pos_of_neg_of_neg (lt_of_le_of_ne (not_lt.1 hn) r'.ne_zero) h
    · exact div_pos (hr.1 h) h
  · rw [hQβ, hPβ, ← Algebra.smul_def, ← Algebra.smul_def, ← Algebra.smul_def]
    simp only [mul_smul_comm, smul_mul_assoc, smul_smul]
    have hrr : (r' : ℚ) / r * r = r' := by field_simp
    rw [hrr]
    congr 1
    rw [Units.val_mul, sh_mul']
    calc (e' : G.C) * a₀ * β₁ * sh G (e' : G.C)
        = (e' : G.C) * (((e⁻¹ : G.Cˣ) : G.C) * e) * a₀ * β₁ * (sh G (e : G.C) * sh G ((e⁻¹ : G.Cˣ) : G.C)) * sh G (e' : G.C) := by
          rw [Units.inv_mul, sh_mul_inv', mul_one, mul_one]
      _ = _ := by simp only [mul_assoc]
  · have hc : Commute ((e' * e⁻¹ : G.Cˣ) : G.C) (γ₀ : G.C) := by
      rw [Units.val_mul]; exact he'.mul_left he.units_inv_left
    ext
    rw [hP, hQ, Units.val_mul, Units.val_mul, hc.eq, mul_assoc, Units.mul_inv, mul_one]

theorem exists_point_of_term_ne_zero' {G : HTGroup p} (P : Pair G) (Kf : Subgroup G.GAf)
    (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ) (h : P.term Kf f r K φ ≠ 0) :
    ∃ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) (g : G.GAf),
      f (g⁻¹ * P.toAf x t hx P.self * g) ≠ 0 := by
  unfold Pair.term at h
  split_ifs at h with hd
  · unfold Pair.termAt pointSum at h
    obtain ⟨q, hq⟩ := not_forall.1 (fun hc => h (finsum_eq_zero_of_forall_eq_zero hc))
    refine ⟨_, _, P.trivAf.choose_spec.choose_spec, (Quotient.out q).1, fun h0 => hq ?_⟩
    rw [h0, zero_mul, mul_zero]
  · exact absurd rfl h

theorem finite_fixed (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ)
    (hf : IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f) (hreg : ∀ g, f g ≠ 0 → RegAf G g)
    (γ₀ : G.Cˣ) (c₀ : ℚˣ) :
    {q : Cls G | ∃ P : Pair G, (Quot.mk Pair.Rel P : Cls G) = q ∧ P.γ = γ₀ ∧ P.c = c₀ ∧
      ∃ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) (g : G.GAf),
        f (g⁻¹ * P.toAf x t hx P.self * g) ≠ 0}.Finite := by
  by_cases hne : ∃ P₁ : Pair G, P₁.γ = γ₀ ∧ P₁.c = c₀
  swap
  · refine Set.finite_empty.subset ?_
    rintro q ⟨P, -, hγ, hc, -⟩
    exact hne ⟨P, hγ, hc⟩
  obtain ⟨P₁, rfl, rfl⟩ := hne
  obtain ⟨S, hS⟩ := GlobalTheory.T.kottwitzPair_form_ratio_local_scalar_norm p G L f hf hreg P₁
  obtain ⟨A, hA⟩ := GlobalTheory.T.finite_fixed_unit_classes_centralizer_regular p G P₁.β P₁.sym P₁.γ P₁.c P₁.sim P₁.reg.2 P₁.reg.1 S
  let D : G.C × Bool → Pair G → Prop := fun ab P => P.γ = P₁.γ ∧ ∃ (r : ℚˣ) (e : G.Cˣ),
    Commute (e : G.C) P₁.γ ∧ decide (0 < (r : ℚ)) = ab.2 ∧
    (P.β : G.C) = algebraMap ℚ G.C r * ((e : G.C) * ab.1 * P₁.β * sh G (e : G.C))
  let ρ : G.C × Bool → Cls G := fun ab => if h : ∃ P, D ab P then Quot.mk _ h.choose else Quot.mk _ P₁
  refine (Finset.finite_toSet ((A ×ˢ (Finset.univ : Finset Bool)).image ρ)).subset ?_
  rintro q ⟨P, rfl, hγ, hc, x, t, hx, g, hg⟩
  have hcomm := commute_ratio G P.β P₁.β P₁.γ P₁.c P₁.c.ne_zero (by rw [← hγ, ← hc]; exact P.sim) P₁.sim
  have hτ := tau_ratio G P.β P₁.β P.sym P₁.sym
  have hu : IsUnit ((P.β : G.C) * ((P₁.β⁻¹ : G.Cˣ) : G.C)) := by
    simpa using (P.β * P₁.β⁻¹).isUnit
  obtain ⟨a₀, ha₀, r, e, he, hre⟩ := hA _ hu hcomm hτ (fun ℓ _ hℓ => hS P hγ hc x t hx g hg ℓ hℓ)
  have hβeq : (P.β : G.C) = algebraMap ℚ G.C r * ((e : G.C) * a₀ * P₁.β * sh G (e : G.C)) := by
    calc (P.β : G.C) = ((P.β : G.C) * ((P₁.β⁻¹ : G.Cˣ) : G.C)) * P₁.β := by simp [mul_assoc]
      _ = _ := by rw [hre]; simp [mul_assoc]
  have hex : ∃ P', D (a₀, decide (0 < (r : ℚ))) P' := ⟨P, hγ, r, e, he, rfl, hβeq⟩
  refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨(a₀, decide (0 < (r : ℚ))),
    Finset.mem_product.2 ⟨ha₀, Finset.mem_univ _⟩, ?_⟩)
  have hρ : ρ (a₀, decide (0 < (r : ℚ))) = Quot.mk _ hex.choose := dif_pos hex
  rw [hρ]
  obtain ⟨hγ', r', e', he', hb', hβ'⟩ := hex.choose_spec
  refine Quot.sound (rel_of_same G P₁.β P₁.γ a₀ _ P hγ' hγ r' r e' e he' he ?_ hβ' hβeq)
  rw [← decide_eq_decide]; exact hb'

theorem finite_classes_of_pol_a_one : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → (∀ g, f g ≠ 0 → RegAf G g) → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ P0 : Polynomial G.F, {q : Cls G | (Quot.out q).pol = P0 ∧ (∃ μ, (Quot.out q).Mark μ) ∧ (Quot.out q).term L.K.toSubgroup f 1 K' f' ≠ 0}.Finite := by
  intro p _ G _ L f hf hreg K' f' _ P0
  by_cases hne : {q : Cls G | (Quot.out q).pol = P0 ∧ (∃ μ, (Quot.out q).Mark μ) ∧
      (Quot.out q).term L.K.toSubgroup f 1 K' f' ≠ 0}.Nonempty
  · obtain ⟨q₀, hq₀⟩ := hne
    refine ((finite_fixed G L f hf hreg (Quot.out q₀).γ (Quot.out q₀).c).union
      (finite_fixed G L f hf hreg (Quot.out q₀).γ (-(Quot.out q₀).c))).subset ?_
    intro q hq
    obtain ⟨x, t, hx, g, hg⟩ := exists_point_of_term_ne_zero' _ _ _ _ _ _ hq.2.2
    obtain ⟨y, hy⟩ := GlobalTheory.LKCx.ClsReg.units_conj_of_minpoly_eq_of_separable G (Quot.out q).γ (Quot.out q₀).γ
      (hq.1.trans hq₀.1.symm) (Quot.out q₀).reg.2 (Quot.out q₀).reg.1
    obtain ⟨P', hrel, hγ, -, htr⟩ := GlobalTheory.LKMid.Pair.exists_conj p G (Quot.out q) y⁻¹
    obtain ⟨x', hx', he⟩ := htr x t hx
    have hq' : (Quot.mk Pair.Rel P' : Cls G) = q := by
      rw [← Quot.sound hrel]; exact Quot.out_eq q
    have hγ' : P'.γ = (Quot.out q₀).γ := by
      rw [hγ]; ext
      rw [Units.val_mul, Units.val_mul, hy]
      simp [mul_assoc]
    have hg' : f (g⁻¹ * P'.toAf x' t hx' P'.self * g) ≠ 0 := by rw [he]; exact hg
    rcases GlobalTheory.LKMid.Pair.c_eq_or_eq_neg p G (Quot.out q₀) P' hγ' with hc | hc
    · exact Or.inl ⟨P', hq', hγ', hc, x', t, hx', g, hg'⟩
    · exact Or.inr ⟨P', hq', hγ', hc, x', t, hx', g, hg'⟩
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne]; exact Set.finite_empty

end GlobalTheory.LKCx.PeriodicClassFixedPoints
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteKottwitzClassesPerMinpolyAEqOneStatement

section

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.finite_kottwitz_classes_per_minpoly_a_eq_one : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → (∀ g, f g ≠ 0 → RegAf G g) → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ P0 : Polynomial G.F, {q : Cls G | (Quot.out q).pol = P0 ∧ (∃ μ, (Quot.out q).Mark μ) ∧ (Quot.out q).term L.K.toSubgroup f 1 K' f' ≠ 0}.Finite := by
  first | (exact @GlobalTheory.LKCx.PeriodicClassFixedPoints.finite_classes_of_pol_a_one) | (exact GlobalTheory.LKCx.PeriodicClassFixedPoints.finite_classes_of_pol_a_one) | (intros; apply GlobalTheory.LKCx.PeriodicClassFixedPoints.finite_classes_of_pol_a_one  <;> assumption)
end
end
