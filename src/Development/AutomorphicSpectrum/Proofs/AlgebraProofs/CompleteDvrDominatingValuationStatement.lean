module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.Data.Nat.Choose.Multinomial
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Formalism.LocalToGlobal.ProjectiveLattices.SubConstMemOrig
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut
public import Mathlib.FieldTheory.Extension
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

-- Source module: Development.WeilBound.CoreStatements.HodgeTatePoints.PdvrExt

section

@[expose] public section

namespace PositivityTheory.HtPt.Pdvr

open Polynomial IsLocalRing

theorem exists_root (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (q : (ResidueField V)[X]) (hm : q.Monic) (hq : Irreducible q) :
    ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R)
      (f : V →+* R) (_ : IsLocalHom f), Function.Injective f ∧
      ∃ a, (q.map (ResidueField.map f)).IsRoot a := by
  obtain ⟨P, hP, hdeg, hPm⟩ := lifts_and_degree_eq_and_monic
    ((mem_lifts q).mpr (map_surjective (residue V) residue_surjective q)) hm
  have hPi : Irreducible P :=
    Monic.irreducible_of_irreducible_map (residue V) P hPm (hP ▸ hq)
  have : IsDomain (AdjoinRoot P) := AdjoinRoot.isDomain_of_prime hPi.prime
  have hinj : Function.Injective (AdjoinRoot.of P) :=
    AdjoinRoot.of.injective_of_degree_ne_zero (hdeg ▸ (degree_pos_of_irreducible hq).ne')
  have : Module.Finite V (AdjoinRoot P) := hPm.finite_adjoinRoot
  have hmax : (Ideal.map (AdjoinRoot.of P) (maximalIdeal V)).IsMaximal := by
    apply Ideal.Quotient.maximal_of_isField
    have : Fact (Irreducible (P.map (residue V))) := ⟨hP ▸ hq⟩
    have h1 : IsField (AdjoinRoot (P.map (residue V))) := Field.toIsField _
    exact MulEquiv.isField h1
      (AdjoinRoot.quotEquivQuotMap P (maximalIdeal V)).toRingEquiv.toMulEquiv
  have huniq : ∀ M : Ideal (AdjoinRoot P), M.IsMaximal →
      M = Ideal.map (AdjoinRoot.of P) (maximalIdeal V) := by
    intro M hM
    have h1 : (M.comap (algebraMap V (AdjoinRoot P))).IsMaximal := by
      letI := hM
      exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal
        (algebraMap V (AdjoinRoot P)) (by
          intro x
          exact Algebra.IsIntegral.isIntegral x) M
    have h2 := eq_maximalIdeal h1
    refine (hmax.eq_of_le hM.ne_top ?_).symm
    rw [Ideal.map_le_iff_le_comap, ← h2]
    exact le_rfl
  have : IsLocalRing (AdjoinRoot P) := .of_unique_max_ideal ⟨_, hmax, huniq⟩
  have hme : maximalIdeal (AdjoinRoot P) = Ideal.map (AdjoinRoot.of P) (maximalIdeal V) :=
    huniq _ inferInstance
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hme' : maximalIdeal (AdjoinRoot P) = Ideal.span {AdjoinRoot.of P π} := by
    rw [hme, hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  have hnf : ¬ IsField (AdjoinRoot P) := by
    rw [isField_iff_maximalIdeal_eq, hme', Ideal.span_singleton_eq_bot]
    exact fun h => hπ.ne_zero (hinj (h.trans (map_zero _).symm))
  have : IsNoetherianRing (AdjoinRoot P) := IsNoetherianRing.of_finite V _
  have hdvr : IsDiscreteValuationRing (AdjoinRoot P) :=
    ((IsDiscreteValuationRing.TFAE (AdjoinRoot P) hnf).out 1 5).mpr
      (show (maximalIdeal (AdjoinRoot P)).IsPrincipal from ⟨_, hme'⟩)
  have hloc : IsLocalHom (AdjoinRoot.of P) := by
    refine ⟨fun a ha => ?_⟩
    by_contra h
    have : AdjoinRoot.of P a ∈ maximalIdeal (AdjoinRoot P) :=
      hme ▸ Ideal.mem_map_of_mem _ h
    exact this ha
  refine ⟨AdjoinRoot P, inferInstance, inferInstance, hdvr, AdjoinRoot.of P, hloc, hinj,
    residue _ (AdjoinRoot.root P), ?_⟩
  rw [← hP, Polynomial.map_map, ResidueField.map_comp_residue, IsRoot.def, eval_map,
    ← Polynomial.hom_eval₂, AdjoinRoot.eval₂_root, map_zero]

theorem exists_splits (n : ℕ) : ∀ (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (q : (ResidueField V)[X]), q.natDegree = n →
    ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R)
      (f : V →+* R) (_ : IsLocalHom f), Function.Injective f ∧
      (q.map (ResidueField.map f)).Splits := by
  induction n with
  | zero =>
    intro V _ _ _ q hq
    exact ⟨V, inferInstance, inferInstance, inferInstance, RingHom.id V, inferInstance,
      Function.injective_id, (Splits.of_natDegree_eq_zero hq).map _⟩
  | succ n ih =>
    intro V _ _ _ q hq
    have hq0 : q ≠ 0 := by
      rintro rfl
      simp at hq
    have hnu : ¬ IsUnit q := not_isUnit_of_natDegree_pos q (by omega)
    obtain ⟨g, hgm, hgi, hgd⟩ := exists_monic_irreducible_factor q hnu
    obtain ⟨R, _, _, _, f, _, hf, a, ha⟩ := exists_root V g hgm hgi
    have hr : (q.map (ResidueField.map f)).IsRoot a := ha.dvd (Polynomial.map_dvd _ hgd)
    obtain ⟨q', hq'⟩ := dvd_iff_isRoot.mpr hr
    have hq1 : q.map (ResidueField.map f) ≠ 0 := Polynomial.map_ne_zero hq0
    have hd : q'.natDegree = n := by
      have h1 := congrArg natDegree hq'
      have h2 : q' ≠ 0 := by
        rintro rfl
        exact hq1 (by rw [hq', mul_zero])
      rw [natDegree_map, natDegree_mul (X_sub_C_ne_zero a) h2, natDegree_X_sub_C] at h1
      omega
    obtain ⟨S, _, _, _, f', _, hf', hs⟩ := ih R q' hd
    refine ⟨S, inferInstance, inferInstance, inferInstance, f'.comp f, inferInstance,
      hf'.comp hf, ?_⟩
    rw [ResidueField.map_comp, ← Polynomial.map_map, hq', Polynomial.map_mul]
    exact ((Splits.X_sub_C a).map _).mul hs

theorem exists_complete (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] :
    ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R)
      (f : V →+* R) (_ : IsLocalHom f), IsAdicComplete (maximalIdeal R) R ∧
      Function.Injective f := by
  classical
  let R := AdicCompletion (maximalIdeal V) V
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible V
  let ϖ : R := algebraMap V R π
  have hme : maximalIdeal R = Ideal.span {ϖ} := by
    refine AdicCompletion.maximalIdeal_eq_map.trans ?_
    refine (congrArg (Ideal.map (algebraMap V R)) hπ.maximalIdeal_eq).trans ?_
    rw [Ideal.map_span, Set.image_singleton]
  have hreg : ∀ r : V, r ≠ 0 → ∀ x : R, algebraMap V R r * x = 0 → x = 0 := by
    intro r hr x hx
    have h1 : IsSMulRegular R r :=
      Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hr)
    apply h1
    change r • x = r • (0 : R)
    rw [smul_zero, Algebra.smul_def, hx]
  have hfac : ∀ x : R, x ≠ 0 → ∃ (n : ℕ) (u : Rˣ), ϖ ^ n * u = x := by
    intro x hx
    have hex : ∃ n : ℕ, ¬ ϖ ^ n ∣ x := by
      by_contra h
      push Not at h
      apply hx
      refine IsHausdorff.haus' (I := maximalIdeal R) x fun n => ?_
      rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, hme, Ideal.span_singleton_pow,
        Ideal.mem_span_singleton]
      exact h n
    have h0 : Nat.find hex ≠ 0 := by
      intro h
      have := Nat.find_spec hex
      rw [h, pow_zero] at this
      exact this (one_dvd _)
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero h0
    have h1 : ϖ ^ n ∣ x := not_not.mp (Nat.find_min hex (by omega))
    obtain ⟨y, rfl⟩ := h1
    have hy : IsUnit y := by
      by_contra h
      have h2 : y ∈ maximalIdeal R := h
      rw [hme, Ideal.mem_span_singleton] at h2
      have h3 := Nat.find_spec hex
      rw [hn, pow_succ] at h3
      exact h3 (mul_dvd_mul_left _ h2)
    exact ⟨n, hy.unit, rfl⟩
  have : NoZeroDivisors R := ⟨fun {a b} hab => by
    by_cases ha : a = 0
    · exact Or.inl ha
    · right
      obtain ⟨n, u, rfl⟩ := hfac a ha
      have h1 : algebraMap V R (π ^ n) * (u * b) = 0 := by
        rw [map_pow, ← mul_assoc]
        exact hab
      have h2 := hreg _ (pow_ne_zero n hπ.ne_zero) _ h1
      exact (Units.mul_right_eq_zero u).mp h2⟩
  have : IsDomain R := NoZeroDivisors.to_isDomain R
  have hinj : Function.Injective (algebraMap V R) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra h
    exact one_ne_zero (hreg a h 1 (by rw [ha, zero_mul]))
  have hϖ0 : ϖ ≠ 0 := fun h => hπ.ne_zero (hinj (h.trans (map_zero _).symm))
  have hϖ : Irreducible ϖ := by
    refine Prime.irreducible ((Ideal.span_singleton_prime hϖ0).mp ?_)
    rw [← hme]
    infer_instance
  have hdvr : IsDiscreteValuationRing R :=
    IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
      ⟨ϖ, hϖ, fun {x} hx => hfac x hx⟩
  exact ⟨R, inferInstance, inferInstance, hdvr, algebraMap V R, inferInstance,
    (inferInstance : IsAdicComplete (maximalIdeal R) R), hinj⟩

end PositivityTheory.HtPt.Pdvr
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CompleteDvrDominatingValuation

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.CompanionTheory.Relay.complete_dvr_dominating_valuation : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (l : Type) [Field l] [Algebra (IsLocalRing.ResidueField V) l] [FiniteDimensional (IsLocalRing.ResidueField V) l], ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R) (f : V →+* R) (_ : IsLocalHom f) (s : l →+* IsLocalRing.ResidueField R), IsAdicComplete (IsLocalRing.maximalIdeal R) R ∧ Function.Injective f ∧ s.comp (algebraMap _ l) = IsLocalRing.ResidueField.map f := by
  intro V _ _ _ l _ _ _
  obtain ⟨n, b⟩ : ∃ n, Nonempty (Module.Basis (Fin n) (IsLocalRing.ResidueField V) l) :=
    ⟨_, ⟨Module.finBasis (IsLocalRing.ResidueField V) l⟩⟩
  obtain ⟨b⟩ := b
  have hne : ∀ i, minpoly (IsLocalRing.ResidueField V) (b i) ≠ 0 := fun i =>
    minpoly.ne_zero (Algebra.IsIntegral.isIntegral (b i))
  obtain ⟨R1, _, _, _, f1, _, hinj1, hsplit⟩ := PositivityTheory.HtPt.Pdvr.exists_splits _ V
    (∏ i, minpoly (IsLocalRing.ResidueField V) (b i)) rfl
  letI : Algebra (IsLocalRing.ResidueField V) (IsLocalRing.ResidueField R1) :=
    (IsLocalRing.ResidueField.map f1).toAlgebra
  have hS : IntermediateField.adjoin (IsLocalRing.ResidueField V) (Set.range b) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hspan : Submodule.span (IsLocalRing.ResidueField V) (Set.range b) ≤
        (IntermediateField.adjoin (IsLocalRing.ResidueField V) (Set.range b)).toSubalgebra.toSubmodule :=
      Submodule.span_le.mpr (IntermediateField.subset_adjoin _ _)
    exact hspan (b.span_eq ▸ Submodule.mem_top)
  have hK : ∀ s ∈ Set.range b, IsIntegral (IsLocalRing.ResidueField V) s ∧
      ((minpoly (IsLocalRing.ResidueField V) s).map
        (algebraMap (IsLocalRing.ResidueField V) (IsLocalRing.ResidueField R1))).Splits := by
    rintro s ⟨i, rfl⟩
    refine ⟨Algebra.IsIntegral.isIntegral (b i), ?_⟩
    refine Polynomial.Splits.of_dvd hsplit ?_ ?_
    · exact Polynomial.map_ne_zero (Finset.prod_ne_zero_iff.mpr fun j _ => hne j)
    · exact Polynomial.map_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
  obtain ⟨φ⟩ := IntermediateField.nonempty_algHom_of_adjoin_splits hK hS
  obtain ⟨R, _, _, _, f2, _, hcomp, hinj2⟩ := PositivityTheory.HtPt.Pdvr.exists_complete R1
  refine ⟨R, inferInstance, inferInstance, inferInstance, f2.comp f1, inferInstance,
    (IsLocalRing.ResidueField.map f2).comp φ.toRingHom, hcomp, hinj2.comp hinj1, ?_⟩
  ext x
  rw [IsLocalRing.ResidueField.map_comp]
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
  rfl
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CompleteDvrDominatingValuationStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.complete_dvr_dominating_valuation : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (l : Type) [Field l] [Algebra (IsLocalRing.ResidueField V) l] [FiniteDimensional (IsLocalRing.ResidueField V) l], ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R) (f : V →+* R) (_ : IsLocalHom f) (s : l →+* IsLocalRing.ResidueField R), IsAdicComplete (IsLocalRing.maximalIdeal R) R ∧ Function.Injective f ∧ s.comp (algebraMap _ l) = IsLocalRing.ResidueField.map f := by
  first | exact @GlobalTheory.CompanionTheory.Relay.complete_dvr_dominating_valuation | exact GlobalTheory.CompanionTheory.Relay.complete_dvr_dominating_valuation | (intros; apply GlobalTheory.CompanionTheory.Relay.complete_dvr_dominating_valuation <;> assumption)
end
end
