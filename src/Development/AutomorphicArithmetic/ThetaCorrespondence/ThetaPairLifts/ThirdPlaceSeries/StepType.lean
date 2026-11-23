module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.StepsNoCut
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlOfNotIsConjPl
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypeLocalGlobal
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.CardRootsBar
public import Mathlib.Basic.Complex.Basic
public import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CentralIdemCoeff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypeLocalGlobal
public import Development.AutomorphicArithmetic.ThetaCorrespondence.CuspidalSupport.GaloisStatementWeakOfFull
import Formalism.ConjugateSelfDual.Statement
import Formalism.LocalRingCardinality.SpanPowerMembership.NZTypeD
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.CompatR
import Mathlib.GroupTheory.Nilpotent
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.StepTypeProofTyz

section

@[expose] public section



section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
abbrev _root_.GlobalTheory.Pass.stepType_proof_tyz : Prop :=  _root_.GlobalTheory.Pass.StepTypeAlt
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.CommTriv

section

@[expose] public section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
open Polynomial
open GlobalTheory.TypeAbove

noncomputable section

namespace UpperTheory.GalS

open UpperTheory.Lit.Car (IneAb comm_le_ine)

theorem comm_triv {G : Type} [Group G] (I : Subgroup G) (φ : G → ℂ) (h1 : φ 1 = 1)
    (hm : ∀ a ∈ I, ∀ b ∈ I, φ (a * b) = φ a * φ b) : ∀ σ ∈ ⁅I, I⁆, φ σ = 1 := by
  have hinv : ∀ a ∈ I, φ a * φ a⁻¹ = 1 := fun a ha => by
    rw [← hm a ha a⁻¹ (I.inv_mem ha), mul_inv_cancel, h1]
  let K : Subgroup G :=
    { carrier := {x | x ∈ I ∧ φ x = 1}
      mul_mem' := fun {x y} hx hy => ⟨I.mul_mem hx.1 hy.1, by rw [hm x hx.1 y hy.1, hx.2, hy.2, one_mul]⟩
      one_mem' := ⟨I.one_mem, h1⟩
      inv_mem' := fun {x} hx => ⟨I.inv_mem hx.1, by simpa [hx.2] using hinv x hx.1⟩ }
  have hle : ⁅I, I⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    refine ⟨I.mul_mem (I.mul_mem (I.mul_mem ha hb) (I.inv_mem ha)) (I.inv_mem hb), ?_⟩
    rw [commutatorElement_def, hm _ (I.mul_mem (I.mul_mem ha hb) (I.inv_mem ha)) _ (I.inv_mem hb),
      hm _ (I.mul_mem ha hb) _ (I.inv_mem ha), hm a ha b hb]
    linear_combination φ b * φ b⁻¹ * hinv a ha + hinv b hb
  exact fun σ hσ => (hle hσ).2

end UpperTheory.GalS

end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.StepType

section

@[expose] public section



section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
open Polynomial
open GlobalTheory.TypeAbove
noncomputable section
namespace UpperTheory.GalS
open UpperTheory.Lit.Car (IneAb comm_le_ine)
theorem stepType_alt : _root_.GlobalTheory.Pass.stepType_proof_tyz := by
  intro D P hDZ h0 h1 h2' h5 i k hl r hr x PI hPI v τ hτ hsq hroot
  have h2 := _root_.UpperTheory.GalS.weak' h2'
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  have hnc := nc_of_label P hDZ h1 i k v PI τ hτ hsq hroot
  obtain ⟨u, hu, hm0, hlab, hconj⟩ := hDZ i k v PI τ hτ hsq hroot
  refine ⟨u, hu, ?_⟩
  have hcard : ∀ a : (ZMod (D.host.g k))[X], Multiset.card (Formalism.CyclotomicNorms.rootsBar a) = a.natDegree := fun a => by
    unfold Formalism.CyclotomicNorms.rootsBar
    rw [← (IsAlgClosed.splits _).natDegree_eq_card_roots, natDegree_map]
  have hroot0 : ∀ y ∈ Formalism.CyclotomicNorms.rootsBar ((P.lz k).lab τ * (X - C (u : ZMod (D.host.g k))) ^ D.R.t), y ≠ 0 := by
    rintro y hy rfl
    unfold Formalism.CyclotomicNorms.rootsBar at hy
    have h := isRoot_of_mem_roots hy
    rw [IsRoot.def, ← coeff_zero_eq_eval_zero, coeff_map, map_eq_zero, mul_coeff_zero, coeff_zero_eq_eval_zero (_ ^ _)] at h
    rcases mul_eq_zero.1 h with h | h
    · exact ((P.lz k).lab_spec τ).2.2 h
    · simp at h
  have key : ∀ w, w ∈ placesOver D.host.E (D.host.g k) → IsSplitPl D.host w → Nc D.nd D.naut (D.naut.locV i PI w) →
      D.naut.mono0 (D.naut.locV i PI w) →
      (D.naut.items₂ k w (D.naut.locV i PI w)).natDegree = D.R.nV →
      (∀ y ∈ Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k w (D.naut.locV i PI w)), y ≠ 0) →
      D.naut.IsdRW i (mapRep (iotaOQ D.nd D.naut i) (r x)) w ∧
      D.naut.mono0 (D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) (r x)) w) ∧
      ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w),
        D.naut.inePol (D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) (r x)) w) σ =
          ((Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k w (D.naut.locV i PI w))).map
            fun y => X - C (P.om k w y σ)).prod := by
    intro w hw hs hn hm hdeg hnz
    have hwl : w ∈ placesOver D.host.E (D.nd.l i) := hl ▸ hw
    obtain ⟨Pa, hB⟩ := h1 i PI
    obtain ⟨hdR, heq, -⟩ := compatR D h0 h2 h5 i r hr x PI Pa hPI hB w hwl (by rw [hB.2.2.2.1 w hs]; exact hn)
    rw [hB.2.2.2.1 w hs] at heq
    have hdim : D.naut.lpDim (D.naut.locV i PI w) = D.R.nV := by
      have h := D.naut.wdOf_dim i (mapRep (iotaOQ D.nd D.naut i) (r x)) w
      rwa [heq.dim, D.naut.lpDim_tw] at h
    refine ⟨hdR, ?_, fun σ hσ => ?_⟩
    · refine heq.mono ?_
      rw [D.naut.monomial_twist_iff]; exact hm
    · have hab : IneAb D.nd D.naut (D.naut.lpTw (D.naut.locV i PI w) ((1 - (D.R.nV : ℝ)) / 2)) := fun s hs' => by
        rw [D.naut.inePol_tw _ _ s (comm_le_ine w hs'), D.naut.lpDim_tw,
          P.inertiaCharpoly_eigenvalues k w hw _ (hdeg.trans hdim.symm) s (comm_le_ine w hs'),
          Multiset.map_congr rfl (fun y hy => by rw [comm_triv _ (P.om k w y) (P.om_one k w y (hnz y hy)) (P.om_mul k w y (hnz y hy)) s hs', C_1]),
          Multiset.map_const', Multiset.prod_replicate, hcard, hdeg, hdim]
      rw [heq.ine ⟨(D.naut.monomial_twist_iff _ _).2 hm, hab⟩ σ hσ, D.naut.inePol_tw _ _ σ hσ]
      exact P.inertiaCharpoly_eigenvalues k w hw _ (hdeg.trans hdim.symm) σ hσ
  intro w M hwM
  rcases hwM with ⟨rfl, rfl⟩ | ⟨hc, rfl⟩
  · have hdeg : (D.naut.items₂ k (D.naut.plGw k v) (D.naut.locV i PI (D.naut.plGw k v))).natDegree = D.R.nV := by
      rw [hlab, ((P.lz k).lab_spec τ).1.natDegree_mul ((monic_X_sub_C _).pow _),
        ((P.lz k).lab_spec τ).2.1, (monic_X_sub_C _).natDegree_pow, natDegree_X_sub_C, mul_one]
      rfl
    have h := key _ (D.naut.plGw_over k v) (GlobalTheory.FixedPlaceSplit.isSplitPl_plGw D k v) (hnc _ (Or.inl rfl)) hm0 hdeg (by rw [hlab]; exact hroot0)
    rw [hlab] at h
    exact h
  · obtain ⟨hw, hs⟩ := conj_over_split D (D.naut.plGw_over k v) (GlobalTheory.FixedPlaceSplit.isSplitPl_plGw D k v) hc
    obtain ⟨hm, hdeg, hroots⟩ := hconj w hc
    have h := key w hw hs (hnc w (Or.inr hc)) hm hdeg (by
      rw [hroots]
      intro y hy
      obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 hy
      exact inv_ne_zero (hroot0 z hz))
    rw [hroots] at h
    exact h
end UpperTheory.GalS
end
end
end
end
