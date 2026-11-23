module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Valuation.Integers
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTorsionLift
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
public import Mathlib.RingTheory.Valuation.Integral
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
import Development.AbelianVarietyTheory.Definitions.Divisors.XiMulNu
import Mathlib.Topology.Sheaves.Init
import Mathlib.RingTheory.Valuation.Integral

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgHomLiftResiduePointFiniteFlat

section

@[expose] public section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.ResiduePointLift

theorem exists_algHom_lift : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] [IsLocalRing O], v.Integers O →
    ∀ (A : Type) [CommRing A] [Algebra O A] [Module.Finite O A] [Module.Flat O A]
    (c : A →ₐ[O] IsLocalRing.ResidueField O), ∃ x : A →ₐ[O] O, ∀ a, IsLocalRing.residue O (x a) = c a := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ hv A _ _ _ _ c
  haveI : IsFractionRing O C := hv.isFractionRing
  haveI : IsIntegrallyClosed O := hv.isIntegrallyClosed
  obtain ⟨ψ, h1, h2⟩ := GlobalTheory.UT.ExactTerm.exists_ringHom_lift C (c : A →+* IsLocalRing.ResidueField O)
    (RingHom.ext fun o => by simp [IsLocalRing.ResidueField.algebraMap_eq])
  refine ⟨{ ψ with commutes' := fun o => RingHom.congr_fun h1 o }, fun a => RingHom.congr_fun h2 a⟩

end GlobalTheory.ResiduePointLift
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgHomLiftResiduePointFiniteFlatStatement

section

@[expose] public section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.exists_algHom_lift_residuePoint_finite_flat : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] [IsLocalRing O], v.Integers O → ∀ (A : Type) [CommRing A] [Algebra O A] [Module.Finite O A] [Module.Flat O A] (c : A →ₐ[O] IsLocalRing.ResidueField O), ∃ x : A →ₐ[O] O, ∀ a, IsLocalRing.residue O (x a) = c a := by
  first | exact @GlobalTheory.ResiduePointLift.exists_algHom_lift | exact GlobalTheory.ResiduePointLift.exists_algHom_lift | (intros; apply GlobalTheory.ResiduePointLift.exists_algHom_lift <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupResidueFieldTateLevelSection

section

@[expose] public section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

noncomputable section

namespace GlobalTheory.TateResidue

open WithConv

theorem conv_eq_one_of_mul {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] (G : PDivGroup p O)
    {B : Type} [CommRing B] [Algebra O B] (n : ℕ) (a b : WithConv (G.A n →ₐ[O] B))
    (h : a * b = b) : a = 1 :=
  (IsUnit.of_pow_eq_one (G.pts_pow_self n b)
    (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)).mul_right_cancel (h.trans (one_mul _).symm)

theorem main : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] [IsLocalRing O], v.Integers O → ∀ G : PDivGroup p O, (∀ (n : ℕ) (c : G.A n →ₐ[O] IsLocalRing.ResidueField O), ∃ t : G.TateOver (IsLocalRing.ResidueField O), t.pt n = c) ∧ ∃ s : G.TateOver (IsLocalRing.ResidueField O) →ₗ[ℤ_[p]] G.Tate, (∀ t, G.tatePush (Algebra.ofId O (IsLocalRing.ResidueField O)) (s t) = t) ∧ ∀ (n : ℕ) (t t' : G.TateOver (IsLocalRing.ResidueField O)), t.pt n = t'.pt n → (s t).pt n = (s t').pt n := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ hv G
  have : IsIntegrallyClosedIn O C := isIntegrallyClosedIn_iff.2 ⟨hv.hom_inj, fun h =>
    hv.exists_of_le_one (hv.isIntegral_iff_v_le_one.1 h)⟩
  set k := IsLocalRing.ResidueField O
  set π := G.tatePush (Algebra.ofId O k)

  have hlift : ∀ (n : ℕ) (c : G.A n →ₐ[O] k), ∃ t : G.Tate, (π t).pt n = c := by
    intro n c
    obtain ⟨x, hx⟩ := GlobalTheory.T.exists_algHom_lift_residuePoint_finite_flat p C v O hv (G.A n) c
    obtain ⟨t, ht⟩ := G.pt_surjective C n x
    refine ⟨t, AlgHom.ext fun a => ?_⟩
    rw [tatePush_pt]
    change IsLocalRing.residue O (t.pt n a) = c a
    rw [show t.pt n = x from ht]
    exact hx a
  refine ⟨fun n c => ?_, ?_⟩
  · obtain ⟨t, ht⟩ := hlift n c
    exact ⟨π t, ht⟩
  have := G.finite_tate C
  have hπ : Function.Surjective π := by
    refine TateFree.surjective_of_mod π TateOver.eq_zero_of_forall_pow_smul fun y => ?_
    obtain ⟨x, hx⟩ := hlift 1 (y.pt 1)
    obtain ⟨z, hz⟩ := (TateOver.conv_eq_one_iff (y - π x) 1).1 <| by
      have h1 : (y - π x + π x).conv 1 = y.conv 1 := by rw [sub_add_cancel]
      rw [TateOver.add_conv] at h1
      have h2 : (π x).conv 1 = y.conv 1 := congrArg toConv hx
      rw [h2] at h1
      exact conv_eq_one_of_mul G _ _ _ h1
    exact ⟨x, z, by rwa [pow_one] at hz⟩
  have : Module.Finite ℤ_[p] (G.TateOver k) := Module.Finite.of_surjective π hπ
  have : Module.Free ℤ_[p] (G.TateOver k) := inferInstance
  obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hπ
  refine ⟨s, fun t => LinearMap.congr_fun hs t, fun n t t' h => ?_⟩
  have hd : (t - t').conv n = 1 := by
    have h1 : (t - t' + t').conv n = t.conv n := by rw [sub_add_cancel]
    rw [TateOver.add_conv, show t'.conv n = t.conv n from congrArg toConv h.symm] at h1
    exact conv_eq_one_of_mul G _ _ _ h1
  obtain ⟨u, hu⟩ := (TateOver.conv_eq_one_iff (t - t') n).1 hd
  have h3 : (s t - s t').conv n = 1 := by
    rw [← map_sub, ← hu, map_smul]
    exact (TateOver.conv_eq_one_iff _ n).2 ⟨_, rfl⟩
  have h4 : (s t - s t' + s t').conv n = (s t).conv n := by rw [sub_add_cancel]
  rw [TateOver.add_conv, h3, one_mul] at h4
  exact congrArg ofConv h4.symm

end GlobalTheory.TateResidue
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupResidueFieldTateLevelSectionStatement

section

@[expose] public section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.pDivGroup_residueField_tate_level_section : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] [IsLocalRing O], v.Integers O → ∀ G : PDivGroup p O, (∀ (n : ℕ) (c : G.A n →ₐ[O] IsLocalRing.ResidueField O), ∃ t : G.TateOver (IsLocalRing.ResidueField O), t.pt n = c) ∧ ∃ s : G.TateOver (IsLocalRing.ResidueField O) →ₗ[ℤ_[p]] G.Tate, (∀ t, G.tatePush (Algebra.ofId O (IsLocalRing.ResidueField O)) (s t) = t) ∧ ∀ (n : ℕ) (t t' : G.TateOver (IsLocalRing.ResidueField O)), t.pt n = t'.pt n → (s t).pt n = (s t').pt n := by
  first | exact @GlobalTheory.TateResidue.main | exact GlobalTheory.TateResidue.main | (intros; apply GlobalTheory.TateResidue.main <;> assumption)
end
end
