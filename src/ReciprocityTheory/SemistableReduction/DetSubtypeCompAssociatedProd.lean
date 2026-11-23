module

public import ReciprocityTheory.SemistableReduction.ComapInclusionIsLocalHom
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CapelliComplements.GeneralBFactAlt
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.FreeModule.PID
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
public import Mathlib.RingTheory.OrderOfVanishing.Noetherian
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.TypeStar
public import Lemmata.GeneralBFactLast.Imports
public import Mathlib.RingTheory.OrderOfVanishing.Basic

-- Source module: Lemmata.GeneralBFactTail.Imports

section

@[expose] public section

universe u_1 u_2 u_3

namespace Bl.general_b_fact_tail

theorem goal1 :
  ∀ {R : Type u_1} {M : Type u_2} [inst : CommRing.{u_1} R] [inst_1 : IsDomain.{u_1} R]
  [inst_2 : IsPrincipalIdealRing.{u_1} R] [inst_3 : AddCommGroup.{u_2} M] [inst_4 : Module.{u_1, u_2} R M]
  {ι : Type u_3} [inst_5 : Fintype.{u_3} ι] [DecidableEq.{u_3 + 1} ι] (b : Module.Basis.{u_3, u_1, u_2} ι R M)
  (N : Submodule.{u_1, u_2} R M)
  (h :
    Eq.{1} (Module.finrank.{u_1, u_2} R (Subtype.{u_2 + 1} fun (x : M) ↦ Membership.mem.{u_2, u_2} N x))
      (Module.finrank.{u_1, u_2} R M))
  (e :
    LinearEquiv.{u_1, u_1, u_2, u_2} (RingHom.id.{u_1} R) M
      (Subtype.{u_2 + 1} fun (x : M) ↦ Membership.mem.{u_2, u_2} N x)),
  Associated.{u_1}
    (DFunLike.coe.{max (u_1 + 1) (u_2 + 1), u_2 + 1, u_1 + 1} LinearMap.det.{u_2, u_1}
      (LinearMap.comp.{u_1, u_1, u_1, u_2, u_2, u_2} (Submodule.subtype.{u_1, u_2} N)
        (LinearEquiv.toLinearMap.{u_1, u_1, u_2, u_2} e)))
    (Finset.prod.{u_3, u_1} Finset.univ.{u_3} fun (i : ι) ↦ Submodule.smithNormalFormCoeffs.{u_3, u_1, u_2} b h i) := by
  intro R M _ _ _ _ _ ι _ _ b N h e
  have ab_eq := Submodule.smithNormalFormBotBasis_def b h
  let b' := Submodule.smithNormalFormTopBasis b h
  let e' : M ≃ₗ[R] N := b'.equiv (Submodule.smithNormalFormBotBasis b h) (Equiv.refl _)
  refine (LinearMap.associated_det_comp_equiv N.subtype e e').trans (Associated.of_eq ?_)
  have h1 := Module.Basis.det_comp b' (N.subtype ∘ₗ (e' : M →ₗ[R] N)) b'
  rw [Module.Basis.det_self, mul_one] at h1
  rw [← h1]
  have h2 : (⇑(N.subtype ∘ₗ (e' : M →ₗ[R] N)) ∘ ⇑b') =
      fun i => Submodule.smithNormalFormCoeffs b h i • b' i := by
    funext i
    simp only [Function.comp_apply, LinearMap.coe_comp, LinearEquiv.coe_coe, e',
      Module.Basis.equiv_apply, Equiv.refl_apply, Submodule.subtype_apply]
    exact ab_eq i
  rw [h2, AlternatingMap.map_smul_univ, Module.Basis.det_self, smul_eq_mul, mul_one]

end Bl.general_b_fact_tail
end
end

-- Source module: ReciprocityTheory.SemistableReduction.DetSubtypeCompAssociatedProd

section

@[expose] public section

namespace ReciprocityTheory.MultiplicativeHeights

open Module Submodule

theorem det_subtype_comp_associated_prod {R M : Type*} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] [AddCommGroup M] [Module R M] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : Basis ι R M) (N : Submodule R M)
    (h : finrank R N = finrank R M) (e : M ≃ₗ[R] N) :
    Associated (LinearMap.det (N.subtype ∘ₗ (e : M →ₗ[R] N)))
      (∏ i, smithNormalFormCoeffs b h i) := by
  first | exact Bl.general_b_fact_tail.goal1 .. | (apply Bl.general_b_fact_tail.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_tail.goal1 <;> assumption)

theorem addVal_prod {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {ι : Type*} (s : Finset ι) (a : ι → O) :
    IsDiscreteValuationRing.addVal O (∏ i ∈ s, a i) =
      ∑ i ∈ s, IsDiscreteValuationRing.addVal O (a i) := by
  first | exact Bl.general_b_fact'''''''.goal1 .. | (apply Bl.general_b_fact'''''''.goal1 <;> assumption) | (intros; apply Bl.general_b_fact'''''''.goal1 <;> assumption)

theorem gaugeSplitting_holds : NormLengthStatement := by
  intro O B _ _ _ _ _ _ _ _ g hg
  classical
  have : Module.Free O B := Module.free_iff_isTorsionFree.mpr inferInstance
  set b := Module.Free.chooseBasis O B
  set I : Ideal B := Ideal.span ({g} : Set B)
  have hI : I ≠ ⊥ := by simpa [I] using hg
  have h := Ideal.finrank_eq_finrank b I hI
  have hlen : Module.length O (B ⧸ I) =
      ∑ i, IsDiscreteValuationRing.addVal O (smithNormalFormCoeffs b h i) := by
    rw [(Ideal.quotientEquivPiSpan I b hI).length_eq, Module.length_pi_of_fintype]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Ring.ord_eq_addVal]
    rfl
  have hdet : Associated (Algebra.norm O g) (∏ i, smithNormalFormCoeffs b h i) := by
    rw [Algebra.norm_apply]
    have key := det_subtype_comp_associated_prod b (I.restrictScalars O) h
      (b.equiv (Ideal.basisSpanSingleton b hg) (Equiv.refl _))
    convert key using 2
    refine b.ext fun i => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, Submodule.subtype_apply]
    have h1 := Basis.equiv_apply (b := b) (b' := Ideal.basisSpanSingleton b hg) (e := Equiv.refl _) i
    refine Eq.trans ?_ (congrArg Subtype.val h1).symm
    rw [Equiv.refl_apply, Ideal.basisSpanSingleton_apply]
    rfl
  rw [hlen, ← addVal_prod, ← Ring.ord_eq_addVal, ← Ring.ord_eq_addVal]
  exact Ring.ord_eq_of_associated hdet

end ReciprocityTheory.MultiplicativeHeights
end
end
