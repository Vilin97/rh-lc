module

public import Mathlib.RingTheory.RingHom.Etale
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueSpecializes
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ChainRuleAndJacobianCriterion
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsHolFormConst
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.LocalRing.Module
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalGeneratorsResidueBasis

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.FibreBasisSpread

theorem exists_away_linearCombination_bijective : ∀ (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Projective R M] (J : Type) [Fintype J] (v : J → M) (p : Ideal R) [p.IsPrime],
    Function.Bijective (Finsupp.linearCombination p.ResidueField (fun i => (1 : p.ResidueField) ⊗ₜ[R] v i)) →
    ∃ g : R, g ∉ p ∧ (∀ x : M, ∃ (n : ℕ) (c : J →₀ R), g ^ n • x = Finsupp.linearCombination R v c) ∧
      (∀ c : J →₀ R, Finsupp.linearCombination R v c = 0 → ∃ n : ℕ, g ^ n • c = 0) := by
  intro R _ M _ _ _ _ J _ v p _ hbij
  classical
  haveI : Module.FinitePresentation R M := Module.finitePresentation_of_projective R M
  let Rp := Localization.AtPrime p
  have hloc : Function.Bijective (IsLocalizedModule.map p.primeCompl
      (Finsupp.mapRange.linearMap (Algebra.linearMap R Rp)) (TensorProduct.mk R Rp M 1)
      (Finsupp.linearCombination R v)) := by
    rw [IsLocalizedModule.map_linearCombination, LinearMap.coe_restrictScalars]
    apply Module.IsLocalRing.linearCombination_bijective_of_flat
    rw [← (AlgebraTensorModule.cancelBaseChange R Rp p.ResidueField p.ResidueField M).comp_bijective]
    have heq : (AlgebraTensorModule.cancelBaseChange R Rp p.ResidueField p.ResidueField M).toLinearMap ∘ₗ
        Finsupp.linearCombination p.ResidueField
          (TensorProduct.mk Rp p.ResidueField (Rp ⊗[R] M) 1 ∘ (TensorProduct.mk R Rp M 1 ∘ v)) =
        Finsupp.linearCombination p.ResidueField (fun i => (1 : p.ResidueField) ⊗ₜ[R] v i) := by
      ext i
      simp
    convert hbij using 1
    rw [← heq, LinearMap.coe_comp]
    rfl
  obtain ⟨g, hg, h⟩ := Module.FinitePresentation.exists_notMem_bijective
    (Finsupp.linearCombination R v) p _ _ hloc
  refine ⟨g, hg, fun x => ?_, fun c hc => ?_⟩
  · obtain ⟨y, hy⟩ := h.2 (LocalizedModule.mk x 1)
    induction y using LocalizedModule.induction_on with
    | h c s =>
      rw [LocalizedModule.map_mk, LocalizedModule.mk_eq] at hy
      obtain ⟨⟨u, hu⟩, hu'⟩ := hy
      obtain ⟨a, rfl⟩ := hu
      obtain ⟨b, hb⟩ := s.2
      refine ⟨a + b, g ^ a • c, ?_⟩
      have hb' : (s : R) = g ^ b := hb.symm
      simp only [Submonoid.smul_def, one_smul] at hu'
      rw [map_smul, hu', hb', smul_smul, pow_add]
  · have h0 : LocalizedModule.map (Submonoid.powers g) (Finsupp.linearCombination R v)
        (LocalizedModule.mk c 1) = LocalizedModule.map (Submonoid.powers g)
        (Finsupp.linearCombination R v) 0 := by
      rw [LocalizedModule.map_mk, hc, map_zero, LocalizedModule.zero_mk]
    have h1 := h.1 h0
    rw [← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq] at h1
    obtain ⟨⟨u, hu⟩, hu'⟩ := h1
    obtain ⟨a, rfl⟩ := hu
    exact ⟨a, by simpa [Submonoid.smul_def] using hu'⟩

end GlobalTheory.FibreBasisSpread
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoordinatesKaehlerBasis

section

@[expose] public section

open scoped TensorProduct Polynomial

namespace GlobalTheory.EtaleCoordSpread

open KaehlerDifferential TensorProduct

theorem fibre_bijective (B K : Type) [CommRing B] [Field K] [Algebra B K] (M : Type) [AddCommGroup M]
    [Module B M] [Module.Finite B M] (d : ℕ) (v : Fin d → M)
    (hd : Module.finrank K (K ⊗[B] M) = d)
    (hli : LinearIndependent K (fun a => (1 : K) ⊗ₜ[B] v a)) :
    Function.Bijective (Finsupp.linearCombination (RingHom.ker (algebraMap B K)).ResidueField
      (fun a => (1 : (RingHom.ker (algebraMap B K)).ResidueField) ⊗ₜ[B] v a)) := by
  classical
  set p := RingHom.ker (algebraMap B K) with hp
  let φ : p.ResidueField →+* K := Ideal.ResidueField.lift p (algebraMap B K) le_rfl (fun x hx => by
    simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff, isUnit_iff_ne_zero]
    exact fun h => hx (RingHom.mem_ker.2 h))
  letI : Algebra p.ResidueField K := φ.toAlgebra
  haveI : IsScalarTower B p.ResidueField K := IsScalarTower.of_algebraMap_eq fun r =>
    (Ideal.ResidueField.lift_algebraMap _ _ _ _ r).symm
  let e := AlgebraTensorModule.cancelBaseChange B p.ResidueField K K M
  have he : ∀ a, e ((1 : K) ⊗ₜ[p.ResidueField] ((1 : p.ResidueField) ⊗ₜ[B] v a)) = (1 : K) ⊗ₜ[B] v a :=
    fun a => by simp [e, AlgebraTensorModule.cancelBaseChange_tmul]
  have hfun : (e.symm.toLinearMap ∘ fun a => (1 : K) ⊗ₜ[B] v a) =
      fun a => (1 : K) ⊗ₜ[p.ResidueField] ((1 : p.ResidueField) ⊗ₜ[B] v a) := by
    funext a
    simp only [Function.comp_apply, LinearEquiv.coe_coe]
    rw [LinearEquiv.symm_apply_eq, he]
  have hli2 : LinearIndependent K (fun a => (1 : K) ⊗ₜ[p.ResidueField] ((1 : p.ResidueField) ⊗ₜ[B] v a)) :=
    hfun ▸ hli.map' e.symm.toLinearMap (LinearEquiv.ker _)
  have hli3 : LinearIndependent p.ResidueField (fun a => (1 : p.ResidueField) ⊗ₜ[B] v a) := by
    haveI : FaithfulSMul p.ResidueField K := (faithfulSMul_iff_algebraMap_injective _ K).2 φ.injective
    exact LinearIndependent.of_comp (TensorProduct.mk p.ResidueField K (p.ResidueField ⊗[B] M) 1)
      (hli2.restrict_scalars' p.ResidueField)
  have hdim : Module.finrank p.ResidueField (p.ResidueField ⊗[B] M) = d := by
    rw [← hd, ← e.finrank_eq]
    exact (Module.finrank_baseChange (R := K) (S := p.ResidueField) (M' := p.ResidueField ⊗[B] M)).symm
  refine ⟨hli3, ?_⟩
  rw [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by rw [Module.finrank_finsupp_self, Fintype.card_fin]; exact hdim.symm)]
  exact hli3

theorem exists_away_etale : ∀ (R B K : Type) [CommRing R] [CommRing B] [Field K] [Algebra R B] [Algebra B K] [Algebra.Smooth R B] (d : ℕ) (t : Fin d → B), Module.finrank K (K ⊗[B] Ω[B⁄R]) = d → LinearIndependent K (fun a => (1 : K) ⊗ₜ[B] KaehlerDifferential.D R B (t a)) → ∃ h : B, algebraMap B K h ≠ 0 ∧ (MvPolynomial.eval₂Hom (algebraMap R (Localization.Away h)) (fun a => algebraMap B (Localization.Away h) (t a))).Etale := by
  intro R B K _ _ _ _ _ _ d t hd hli
  classical
  have hbij := fibre_bijective B K Ω[B⁄R] d (fun a => D R B (t a)) hd hli
  obtain ⟨g, hg, hspan, hrel⟩ := GlobalTheory.FibreBasisSpread.exists_away_linearCombination_bijective B
    Ω[B⁄R] (Fin d) (fun a => D R B (t a)) (RingHom.ker (algebraMap B K)) hbij
  refine ⟨g, fun h0 => hg (RingHom.mem_ker.2 h0), ?_⟩
  let A := Localization.Away g
  haveI : Algebra.Smooth B A := Algebra.Smooth.of_isLocalization_Away g
  haveI : Algebra.Smooth R A := Algebra.Smooth.comp R B A
  let f := KaehlerDifferential.map R R B A
  haveI : IsLocalizedModule (Submonoid.powers g) f :=
    KaehlerDifferential.isLocalizedModule_map R B A (Submonoid.powers g)
  let w : Fin d → Ω[A⁄R] := fun a => D R A (algebraMap B A (t a))
  have hfw : ∀ a, f (D R B (t a)) = w a := fun a => KaehlerDifferential.map_D R R B A (t a)
  have hunit : ∀ s ∈ Submonoid.powers g, IsUnit (algebraMap B A s) := fun s hs =>
    IsLocalization.map_units A (⟨s, hs⟩ : Submonoid.powers g)
  have hsB : ∀ (s : B) (y : Ω[A⁄R]), s • y = algebraMap B A s • y := fun s y =>
    (algebraMap_smul A s y).symm

  have hsp : ⊤ ≤ Submodule.span A (Set.range w) := by
    intro y _
    obtain ⟨⟨x, s⟩, hxs⟩ := IsLocalizedModule.surj (Submonoid.powers g) f y
    obtain ⟨n, c, hc⟩ := hspan x
    have h1 : ((g ^ n * s : B)) • y = Finsupp.linearCombination B (f ∘ fun a => D R B (t a)) c := by
      rw [mul_smul, Submonoid.smul_def] at *
      simp only at hxs
      rw [hxs, ← map_smul, hc, Finsupp.apply_linearCombination]
    have h2 : ((g ^ n * s : B)) • y ∈ Submodule.span A (Set.range w) := by
      rw [h1]
      refine Submodule.span_le_restrictScalars B A _ ?_
      rw [Finsupp.mem_span_range_iff_exists_finsupp]
      refine ⟨c, ?_⟩
      rw [Finsupp.linearCombination_apply]
      simp only [Function.comp_apply, hfw]
    rw [hsB] at h2
    obtain ⟨u, hu⟩ := hunit (g ^ n * s) (Submonoid.mul_mem _ (Submonoid.pow_mem _ (Submonoid.mem_powers g) n) s.2)
    have key : y = (↑u⁻¹ : A) • ((algebraMap B A (g ^ n * s)) • y) := by
      rw [← hu, smul_smul, Units.inv_mul, one_smul]
    rw [key]
    exact Submodule.smul_mem _ _ h2

  have hliA : LinearIndependent A w := by
    rw [Fintype.linearIndependent_iff]
    intro a ha i
    obtain ⟨⟨b, hb⟩, hbint⟩ := IsLocalization.exist_integer_multiples (Submonoid.powers g)
      (Finset.univ : Finset (Fin d)) a
    choose c hc using fun j => hbint j (Finset.mem_univ j)

    have h1 : f (∑ j, c j • D R B (t j)) = 0 := by

      rw [map_sum]
      simp only [map_smul, hfw, hsB, hc]
      simp only [smul_assoc, ← Finset.smul_sum, ha, smul_zero]
    obtain ⟨⟨s, hs⟩, hs0⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers g) (f := f)
      (h1.trans (map_zero f).symm)
    rw [smul_zero] at hs0
    replace hs0 : s • (∑ j, c j • D R B (t j)) = 0 := hs0
    obtain ⟨n, hn⟩ := hrel (Finsupp.equivFunOnFinite.symm (fun j => s * c j)) (by
      simpa [Finsupp.linearCombination_apply, Finsupp.sum_fintype, mul_smul, ← Finset.smul_sum] using hs0)
    have hi : g ^ n * (s * c i) = 0 := by
      have := congrArg (fun x => x i) hn
      simpa using this
    have hci : algebraMap B A (c i) = 0 := by
      have hu := hunit (g ^ n * s) (Submonoid.mul_mem _ (Submonoid.pow_mem _ (Submonoid.mem_powers g) n) hs)
      rw [← hu.mul_right_eq_zero, ← map_mul, mul_assoc, hi, map_zero]
    rw [hc, Algebra.smul_def] at hci
    exact ((hunit b hb).mul_right_eq_zero).1 hci
  letI : Algebra (MvPolynomial (Fin d) R) A :=
    (MvPolynomial.eval₂Hom (algebraMap R A) (fun a => algebraMap B A (t a))).toAlgebra
  haveI : IsScalarTower R (MvPolynomial (Fin d) R) A :=
    IsScalarTower.of_algebraMap_eq fun r => by
      change algebraMap R A r = MvPolynomial.eval₂Hom (algebraMap R A) _ (MvPolynomial.C r)
      simp
  refine GlobalTheory.EtaleCoordJacobian.etale_of_basis R A (Fin d) (Module.Basis.mk hliA hsp) fun i => ?_
  rw [Module.Basis.mk_apply]
  show D R A (algebraMap B A (t i)) = D R A (MvPolynomial.eval₂Hom (algebraMap R A)
    (fun a => algebraMap B A (t a)) (MvPolynomial.X i))
  rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]

end GlobalTheory.EtaleCoordSpread
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.EtaleCoordinatesKaehlerBasis

section

@[expose] public section

open scoped TensorProduct Polynomial
theorem _root_.GlobalTheory.T.etale_coordinates_kaehler_basis : ∀ (R B K : Type) [CommRing R] [CommRing B] [Field K] [Algebra R B] [Algebra B K] [Algebra.Smooth R B] (d : ℕ) (t : Fin d → B), Module.finrank K (K ⊗[B] Ω[B⁄R]) = d → LinearIndependent K (fun a => (1 : K) ⊗ₜ[B] KaehlerDifferential.D R B (t a)) → ∃ h : B, algebraMap B K h ≠ 0 ∧ (MvPolynomial.eval₂Hom (algebraMap R (Localization.Away h)) (fun a => algebraMap B (Localization.Away h) (t a))).Etale := by
  first | exact @_root_.GlobalTheory.EtaleCoordSpread.exists_away_etale | exact _root_.GlobalTheory.EtaleCoordSpread.exists_away_etale | (intros; apply _root_.GlobalTheory.EtaleCoordSpread.exists_away_etale <;> assumption)
end
end
