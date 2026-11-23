module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import Development.WeilBound.CoreStatements.IdealCycleValues.OfIdealCycleNe
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.Colon
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
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Ideal.BigOperators
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyCN
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialDimBound
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSupSpanMultiHomog
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PIntNumBaseChange
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

-- Source module: Development.WeilBound.CoreStatements.IdealCycleValues.FlatColon

section

@[expose] public section

namespace BaseChangeColon.BC

open MvPolynomial

theorem flat_colon {R R' : Type*} [CommRing R] [CommRing R'] [Algebra R R'] [Module.Flat R R']
    (I : Ideal R) (x : R) :
    (I.map (algebraMap R R')).colon {algebraMap R R' x} = (I.colon {x}).map (algebraMap R R') := by
  apply le_antisymm
  · intro g hg
    rw [Submodule.mem_colon_singleton, smul_eq_mul] at hg
    obtain ⟨n, c, t, ht⟩ := Submodule.mem_span_set'.1 hg
    choose j hj hj' using fun i => (t i).2
    have hrel : ∑ o : Option (Fin n), (o.elim x fun i => -j i) • (o.elim g c : R') = 0 := by
      rw [Fintype.sum_option]
      simp only [Option.elim, Algebra.smul_def, map_neg, neg_mul, Finset.sum_neg_distrib]
      rw [mul_comm, ← ht, add_neg_eq_zero]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hj', smul_eq_mul, mul_comm]
    obtain ⟨k, a, y, h1, h2⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := R) (M := R')
      (f := fun o : Option (Fin n) => o.elim x fun i => -j i) (x := fun o => o.elim g c) hrel
    have hg' : g = ∑ l, a none l • y l := h1 none
    rw [hg']
    refine Ideal.sum_mem _ fun l _ => ?_
    rw [Algebra.smul_def]
    refine Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)
    rw [Submodule.mem_colon_singleton, smul_eq_mul]
    have h3 := h2 l
    rw [Fintype.sum_option] at h3
    simp only [Option.elim, neg_mul, Finset.sum_neg_distrib, add_neg_eq_zero] at h3
    rw [mul_comm, h3]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (hj i)
  · rw [Ideal.map_le_iff_le_comap]
    intro y hy
    rw [Submodule.mem_colon_singleton, smul_eq_mul] at hy
    rw [Ideal.mem_comap, Submodule.mem_colon_singleton, smul_eq_mul, ← map_mul]
    exact Ideal.mem_map_of_mem _ hy

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem map_colon {O O' σ : Type} [CommRing O] [CommRing O'] [Algebra O O'] [Module.Flat O O']
    (I : Ideal (MvPolynomial σ O)) (x : MvPolynomial σ O) :
    (I.map (MvPolynomial.map (algebraMap O O'))).colon {MvPolynomial.map (algebraMap O O') x} =
      (I.colon {x}).map (MvPolynomial.map (algebraMap O O')) := by
  have hb := (inferInstance :
    Algebra.IsPushout O (MvPolynomial σ O) O' (MvPolynomial σ O')).out
  haveI : Module.Flat (MvPolynomial σ O) (MvPolynomial σ O') :=
    Module.Flat.isBaseChange O (MvPolynomial σ O) O' (MvPolynomial σ O') hb
  exact flat_colon (R' := MvPolynomial σ O') I x

theorem ram_colon {O O' σ : Type} [CommRing O] [CommRing O'] [IsDomain O'] [Algebra O O'] (ϖ : O)
    (hm : (Ideal.span {ϖ}).IsMaximal) (ϖ' : O') (h0 : ϖ' ≠ 0) (u : O'ˣ) (e k : ℕ)
    (he : algebraMap O O' ϖ = u * ϖ' ^ e) (hk : k < e) (J : Ideal (MvPolynomial σ O))
    (hJ : C ϖ ∈ J) (g : MvPolynomial σ O')
    (hg : C ϖ' ^ k * g ∈ J.map (MvPolynomial.map (algebraMap O O'))) :
    g ∈ J.map (MvPolynomial.map (algebraMap O O')) ⊔ Ideal.span {C ϖ'} := by
  classical
  set J' := J.map (MvPolynomial.map (algebraMap O O')) with hJ'
  set m : Ideal O := Ideal.span {ϖ} with hmdef
  letI : Field (O ⧸ m) := Ideal.Quotient.field m
  have hle : m ≤ J.comap (algebraMap O (MvPolynomial σ O)) := by
    rw [hmdef, Ideal.span_le, Set.singleton_subset_iff]
    exact hJ
  letI : Algebra (O ⧸ m) (MvPolynomial σ O ⧸ J) := Ideal.Quotient.algebraQuotientOfLEComap hle
  haveI : IsScalarTower O (O ⧸ m) (MvPolynomial σ O ⧸ J) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨ι, ⟨b⟩⟩ : ∃ ι : Type, Nonempty (Module.Basis ι (O ⧸ m) (MvPolynomial σ O ⧸ J)) :=
    ⟨_, ⟨Module.Basis.ofVectorSpace _ _⟩⟩
  have hb := (inferInstance :
    Algebra.IsPushout O O' (MvPolynomial σ O) (MvPolynomial σ O')).out
  set m' : Ideal O' := Ideal.span {algebraMap O O' ϖ} with hm'
  have hle' : m ≤ m'.comap (Algebra.ofId O O') := by
    rw [hmdef, Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_span_singleton_self _
  let ι0 : (O ⧸ m) →ₐ[O] (O' ⧸ m') := Ideal.quotientMapₐ m' (Algebra.ofId O O') hle'
  let lam : ι → (MvPolynomial σ O →ₗ[O] (O' ⧸ m')) := fun i =>
    ι0.toLinearMap ∘ₗ ((b.coord i).restrictScalars O) ∘ₗ (Ideal.Quotient.mkₐ O J).toLinearMap
  have hlam : ∀ i s, lam i s = ι0 (b.coord i (Ideal.Quotient.mk J s)) := fun _ _ => rfl
  let Λ : ι → (MvPolynomial σ O' →ₗ[O'] (O' ⧸ m')) := fun i => hb.lift (lam i)
  have hΛ : ∀ i s, Λ i (MvPolynomial.map (algebraMap O O') s) = lam i s := fun i s =>
    hb.lift_eq (lam i) s
  have hkill : ∀ i, ∀ w ∈ J', Λ i w = 0 := by
    intro i w hw
    suffices h : ∀ h, Λ i (h * w) = 0 by simpa using h 1
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨s, hs, rfl⟩ := hx
      intro h
      induction h using hb.inductionOn with
      | tmul t =>
        change Λ i (MvPolynomial.map (algebraMap O O') t * _) = 0
        rw [← map_mul, hΛ, hlam, Ideal.Quotient.eq_zero_iff_mem.2 (J.mul_mem_left t hs)]
        rw [map_zero, map_zero]
      | smul a t ht => rw [smul_mul_assoc, map_smul, ht, smul_zero]
      | add a t ha ht => rw [add_mul, map_add (f := _), ha, ht, add_zero]
    | zero => simp
    | add x y _ _ hx hy => intro h; rw [mul_add, map_add (f := _), hx, hy, add_zero]
    | smul a x _ hx => intro h; rw [smul_eq_mul, ← mul_assoc, hx]
  choose B hB using fun i => Ideal.Quotient.mk_surjective (I := J) (b i)
  let U : Submodule O' (MvPolynomial σ O') :=
    Submodule.span O' (Set.range fun i => MvPolynomial.map (algebraMap O O') (B i)) ⊔
      J'.restrictScalars O'
  have hJU : ∀ s ∈ J, MvPolynomial.map (algebraMap O O') s ∈ U := fun s hs =>
    Submodule.mem_sup_right (Ideal.mem_map_of_mem _ hs)
  have hU1 : ∀ x ∈ Submodule.span (O ⧸ m) (Set.range b), ∀ s, Ideal.Quotient.mk J s = x →
      MvPolynomial.map (algebraMap O O') s ∈ U := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      intro s hs
      have h1 := hJU _ (Ideal.Quotient.eq.1 (hs.trans (hB i).symm))
      have h2 : MvPolynomial.map (algebraMap O O') (B i) ∈ U :=
        Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩)
      simpa using U.add_mem h1 h2
    | zero => exact fun s hs => hJU s (Ideal.Quotient.eq_zero_iff_mem.1 hs)
    | add x y _ _ hx hy =>
      intro s hs
      obtain ⟨s1, rfl⟩ := Ideal.Quotient.mk_surjective x
      have h1 := hx s1 rfl
      have h2 := hy (s - s1) (by rw [map_sub, hs, add_sub_cancel_left])
      simpa using U.add_mem h1 h2
    | smul c x _ hx =>
      intro s hs
      obtain ⟨s1, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨o, rfl⟩ := Ideal.Quotient.mk_surjective c
      have h1 := U.smul_mem (algebraMap O O' o) (hx s1 rfl)
      have h3 : Ideal.Quotient.mk J s = Ideal.Quotient.mk J (C o * s1) := by
        rw [hs, Algebra.smul_def, map_mul]
        rfl
      have h2 := hJU _ (Ideal.Quotient.eq.1 h3)
      rw [smul_eq_C_mul] at h1
      simpa using U.add_mem h1 h2
  have hU : ∀ w, w ∈ U := by
    intro w
    induction w using hb.inductionOn with
    | tmul t => exact hU1 _ (by rw [b.span_eq]; trivial) t rfl
    | smul a t ht => exact U.smul_mem a ht
    | add a t ha ht => exact U.add_mem ha ht
  obtain ⟨v, hv, w, hw, rfl⟩ := Submodule.mem_sup.1 (hU g)
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hv
  refine Ideal.add_mem _ (Ideal.mem_sup_right ?_) (Ideal.mem_sup_left hw)
  refine Ideal.sum_mem _ fun i hi => ?_
  have h1 := hkill i _ hg

  rw [← C_pow, ← smul_eq_C_mul, map_smul, map_add (f := _), hkill i w hw, add_zero, Finsupp.sum, map_sum,
  Finset.sum_eq_single i] at h1
  · rw [map_smul, hΛ, hlam, hB] at h1
    have h2 : Ideal.Quotient.mk m' (ϖ' ^ k * c i) = 0 := by
      rw [← h1]
      simp [Algebra.smul_def]
    rw [Ideal.Quotient.eq_zero_iff_mem, hm', Ideal.mem_span_singleton', he] at h2
    obtain ⟨z, hz⟩ := h2
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_lt hk
    have h3 : c i = ϖ' * (z * u * ϖ' ^ r) := by
      apply mul_left_cancel₀ (pow_ne_zero k h0)
      rw [← hz]; ring
    change c i • _ ∈ _
    rw [h3, smul_eq_C_mul, C_mul, mul_assoc]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  · intro l _ hl
    rw [map_smul, hΛ, hlam, hB]
    simp [hl]
  · exact fun h => absurd hi h

end BaseChangeColon.BC
end
end

-- Source module: Development.WeilBound.CoreStatements.IdealCycleValues.IsModelOverRamifiedBaseChange

section

@[expose] public section

namespace BaseChangeColon.BC

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {O O' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing O'] [IsDomain O']
  [IsDiscreteValuationRing O'] [Algebra O O'] {ϖ : O} {ϖ' : O'} {u : O'ˣ} {e : ℕ}

omit [IsDomain O] [IsDiscreteValuationRing O] [IsDiscreteValuationRing O'] in
theorem mem_of_mem {σ : Type} (he : 0 < e) (h : algebraMap O O' ϖ = u * ϖ' ^ e)
    (W : Ideal (MvPolynomial σ O')) (hW : C ϖ' ∈ W) :
    MvPolynomial.map (algebraMap O O') (C ϖ) ∈ W := by
  rw [map_C, h, C_mul, C_pow]
  exact W.mul_mem_left _ (W.pow_mem_of_mem hW e he)

omit [IsDiscreteValuationRing O'] in
theorem flat_of (hϖ : Irreducible ϖ) (hϖ' : Irreducible ϖ') (h : algebraMap O O' ϖ = u * ϖ' ^ e) :
    Module.Flat O O' := by
  have hinj : Function.Injective (algebraMap O O') := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra h0
    obtain ⟨n, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ
    rw [map_mul, map_pow, h] at ha
    exact mul_ne_zero (v.isUnit.map (algebraMap O O')).ne_zero
      (pow_ne_zero n (mul_ne_zero u.ne_zero (pow_ne_zero e hϖ'.ne_zero))) ha
  have : FaithfulSMul O O' := (faithfulSMul_iff_algebraMap_injective O O').2 hinj
  infer_instance

theorem local_of (hϖ : Irreducible ϖ) (hϖ' : Irreducible ϖ') (he : 0 < e)
    (h : algebraMap O O' ϖ = u * ϖ' ^ e) : IsLocalHom (algebraMap O O') := by
  refine ⟨fun a ha => ?_⟩
  by_contra h0
  have h1 : a ∈ IsLocalRing.maximalIdeal O := h0
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton'] at h1
  obtain ⟨c, rfl⟩ := h1
  rw [map_mul, h] at ha
  exact hϖ'.not_isUnit ((isUnit_pow_iff he.ne').1
    (isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_right ha)))

theorem bc_vert (hϖ : Irreducible ϖ) (hϖ' : Irreducible ϖ') (he : 0 < e)
    (h : algebraMap O O' ϖ = u * ϖ' ^ e) {d : ℕ} (bs : Fin d → K → ℤ) (J : Ideal (MRing ι O))
    (hJ : IsMultiHomogIdeal J) (hJ' : IsMultiHomogIdeal (J.map (MvPolynomial.map (algebraMap O O'))))
    (hd : ringKrullDim (MRing ι O ⧸ J) < ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞))
    (hd' : ringKrullDim (MRing ι O' ⧸ J.map (MvPolynomial.map (algebraMap O O'))) <
      ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞)) (hm : C ϖ ∈ J) :
    NN (J.map (MvPolynomial.map (algebraMap O O'))) bs = e * NN J bs := by
  have := local_of hϖ hϖ' he h
  have hmax : (Ideal.span {ϖ}).IsMaximal := hϖ.maximalIdeal_eq ▸ IsLocalRing.maximalIdeal.isMaximal O
  have h1 : (C ϖ' ^ e : MRing ι O') ∈ J.map (MvPolynomial.map (algebraMap O O')) := by
    have h2 := Ideal.mul_mem_left _ (C (↑u⁻¹ : O'))
      (Ideal.mem_map_of_mem (MvPolynomial.map (algebraMap O O')) hm)
    rwa [map_C, h, ← C_mul, Units.inv_mul_cancel_left, C_pow] at h2
  rw [NN_pow hϖ' hJ' hd' e h1
      (fun k hk g hg => ram_colon ϖ hmax ϖ' hϖ'.ne_zero u e k h hk J hm g hg) bs,
    NN_vert hϖ' (SupSpanMultiHomog.proof O' K ι _ _ 0 hJ' (homog_C ϖ'))
      ((dim_mono le_sup_left).trans_lt hd')
      (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)) bs,
    special_sup hϖ', NN_vert hϖ hJ hd hm bs]
  congr 1
  rw [← ((GroundTheory.Heights₂.Heights.FieldNumbers.IntNumBaseChange.intersectionNumber_baseChange.1 (IsLocalRing.ResidueField O)
    (IsLocalRing.ResidueField O') K ι (specialIdeal J)).2 d bs)]
  congr 1
  unfold specialIdeal
  rw [Ideal.map_map, Ideal.map_map]
  congr 1
  refine RingHom.ext fun p => ?_
  simp only [RingHom.comp_apply, map_map]
  rfl

theorem bc_all (hϖ : Irreducible ϖ) (hϖ' : Irreducible ϖ') (he : 0 < e)
    (h : algebraMap O O' ϖ = u * ϖ' ^ e) {d : ℕ} (bs : Fin d → K → ℤ) (J : Ideal (MRing ι O)) :
    IsMultiHomogIdeal J → IsMultiHomogIdeal (J.map (MvPolynomial.map (algebraMap O O'))) →
    ringKrullDim (MRing ι O ⧸ J) < ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ringKrullDim (MRing ι O' ⧸ J.map (MvPolynomial.map (algebraMap O O'))) <
      ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) →
    NN (J.map (MvPolynomial.map (algebraMap O O'))) bs = e * NN J bs := by
  have := flat_of hϖ hϖ' h
  induction J using IsNoetherian.induction with
  | hgt J ih =>
    intro hJ hJ' hd hd'
    have hcol := map_colon (O' := O') J (C ϖ)
    have hC : IsMultiHomog (MvPolynomial.map (algebraMap O O') (C ϖ : MRing ι O)) 0 := by
      rw [map_C]; exact homog_C _
    by_cases hc : J.colon {C ϖ} = J
    · rw [hc] at hcol
      rw [NN_nzd hϖ hJ hd (C ϖ) (fun _ hW => hW) hc bs,
        NN_nzd hϖ' hJ' hd' _ (mem_of_mem he h) hcol bs, mul_zero]
    · have hsup : Ideal.map (MvPolynomial.map (algebraMap O O')) (J ⊔ Ideal.span {C ϖ}) =
          Ideal.map (MvPolynomial.map (algebraMap O O')) J ⊔
            Ideal.span {MvPolynomial.map (algebraMap O O') (C ϖ : MRing ι O)} := by
        rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
      have h1 := ih (J.colon {C ϖ}) (lt_of_le_of_ne (le_colon J _) (Ne.symm hc))
        (ColonMultiHomog.full O K ι J _ 0 hJ (homog_C ϖ))
        (hcol ▸ ColonMultiHomog.full O' K ι _ _ 0 hJ' hC)
        ((dim_mono (le_colon J _)).trans_lt hd)
        ((dim_mono (Ideal.map_mono (le_colon J _))).trans_lt hd')
      have h2 := bc_vert hϖ hϖ' he h bs (J ⊔ Ideal.span {C ϖ})
        (SupSpanMultiHomog.proof O K ι J _ 0 hJ (homog_C ϖ))
        (hsup ▸ SupSpanMultiHomog.proof O' K ι _ _ 0 hJ' hC)
        ((dim_mono le_sup_left).trans_lt hd)
        ((dim_mono (Ideal.map_mono le_sup_left)).trans_lt hd')
        (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
      rw [NN_add hϖ' hJ' hd' hC bs, NN_add hϖ hJ hd (homog_C ϖ) bs, hcol, ← hsup, h1, h2, mul_add]

theorem bc_div (hϖ : Irreducible ϖ) (hϖ' : Irreducible ϖ') (he : 0 < e)
    (h : algebraMap O O' ϖ = u * ϖ' ^ e) {d : ℕ} (P : Ideal (MRing ι O)) (hP : IsModelOver P d)
    (hP' : IsModelOver (P.map (MvPolynomial.map (algebraMap O O'))) d) (a : K → ℕ) (f : MRing ι O)
    (hf : IsMultiHomog f a) (hfP : f ∉ P) (bs : Fin d → K → ℤ) :
    NN (P.map (MvPolynomial.map (algebraMap O O')) ⊔
      Ideal.span {MvPolynomial.map (algebraMap O O') f}) bs = e * NN (P ⊔ Ideal.span {f}) bs := by
  have := flat_of hϖ hϖ' h
  have hf' : IsMultiHomog (MvPolynomial.map (algebraMap O O') f) a := fun m hm =>
    hf (d := m) fun h0 => hm (by rw [coeff_map, h0, map_zero])
  have hc : P.colon {f} = P := by
    refine le_antisymm (fun y hy => ?_) (le_colon P f)
    rw [Submodule.mem_colon_singleton, smul_eq_mul] at hy
    exact (hP.multiProj.isPrime.mem_or_mem hy).resolve_right hfP
  have hcol := map_colon (O' := O') P f
  rw [hc] at hcol
  have hfP' : MvPolynomial.map (algebraMap O O') f ∉ P.map (MvPolynomial.map (algebraMap O O')) := by
    intro h0
    apply hP'.multiProj.isPrime.ne_top
    rw [← hcol, Ideal.eq_top_iff_one, Submodule.mem_colon_singleton, one_smul]
    exact h0
  have hsup : (P ⊔ Ideal.span {f}).map (MvPolynomial.map (algebraMap O O')) =
      P.map (MvPolynomial.map (algebraMap O O')) ⊔
        Ideal.span {MvPolynomial.map (algebraMap O O') f} := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  have h1 := bc_all hϖ hϖ' he h bs (P ⊔ Ideal.span {f})
    (SupSpanMultiHomog.proof O K ι P f a hP.multiProj.multiHomog hf)
    (hsup ▸ SupSpanMultiHomog.proof O' K ι _ _ a hP'.multiProj.multiHomog hf')
    (withBotENat_lt_of_add_one_le (hP.dim ▸ dim_drop hP.multiProj.isPrime hfP))
    (hsup ▸ withBotENat_lt_of_add_one_le (hP'.dim ▸ dim_drop hP'.multiProj.isPrime hfP'))
  rwa [hsup] at h1

end BaseChangeColon.BC

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)

theorem BaseChangeColon.isModelOver_ramified_base_change : ∀ (O O' : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] (ϖ : O) (ϖ' : O') (u : O'ˣ) (e : ℕ), Irreducible ϖ → Irreducible ϖ' → 0 < e → algebraMap O O' ϖ = u * ϖ' ^ e → ∀ (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (MvPolynomial (Σ k, J k) O)) (d : ℕ), IsModelOver P d → IsModelOver (P.map (MvPolynomial.map (algebraMap O O'))) d → ∀ (a : K → ℕ) (f : MvPolynomial (Σ k, J k) O), GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog f a → f ∉ P → ∀ l : List (K → ℤ), l.length = d → cycList (divCycle (P.map (MvPolynomial.map (algebraMap O O'))) (MvPolynomial.map (algebraMap O O') f)) l = e * cycList (divCycle P f) l := by
  intro O O' _ _ _ _ _ _ _ ϖ ϖ' u e hϖ hϖ' he h K _ _ J _ P d hP hP' a f hf hfP l hl
  subst hl
  exact BaseChangeColon.BC.bc_div hϖ hϖ' he h P hP hP' a f hf hfP l.get
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModelOverRamifiedExtension

section

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem numbers_divCycle_baseChange_dvr : ∀ (O O' : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] (ϖ : O) (ϖ' : O') (u : O'ˣ) (e : ℕ), Irreducible ϖ → Irreducible ϖ' → 0 < e → algebraMap O O' ϖ = u * ϖ' ^ e → ∀ (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (MvPolynomial (Σ k, J k) O)) (d : ℕ), IsModelOver P d → IsModelOver (P.map (MvPolynomial.map (algebraMap O O'))) d → ∀ (a : K → ℕ) (f : MvPolynomial (Σ k, J k) O), GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog f a → f ∉ P → ∀ l : List (K → ℤ), l.length = d → cycList (divCycle (P.map (MvPolynomial.map (algebraMap O O'))) (MvPolynomial.map (algebraMap O O') f)) l = e * cycList (divCycle P f) l :=
  BaseChangeColon.isModelOver_ramified_base_change

end GlobalTheory.CompanionTheory.Ar.Num
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModelOverRamifiedExtensionStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)

theorem _root_.GlobalTheory.T.model_over_ramified_extension : ∀ (O O' : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] (ϖ : O) (ϖ' : O') (u : O'ˣ) (e : ℕ), Irreducible ϖ → Irreducible ϖ' → 0 < e → algebraMap O O' ϖ = u * ϖ' ^ e → ∀ (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (MvPolynomial (Σ k, J k) O)) (d : ℕ), IsModelOver P d → IsModelOver (P.map (MvPolynomial.map (algebraMap O O'))) d → ∀ (a : K → ℕ) (f : MvPolynomial (Σ k, J k) O), GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog f a → f ∉ P → ∀ l : List (K → ℤ), l.length = d → cycList (divCycle (P.map (MvPolynomial.map (algebraMap O O'))) (MvPolynomial.map (algebraMap O O') f)) l = e * cycList (divCycle P f) l := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.numbers_divCycle_baseChange_dvr | exact GlobalTheory.CompanionTheory.Ar.Num.numbers_divCycle_baseChange_dvr | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.numbers_divCycle_baseChange_dvr <;> assumption)
end
end
