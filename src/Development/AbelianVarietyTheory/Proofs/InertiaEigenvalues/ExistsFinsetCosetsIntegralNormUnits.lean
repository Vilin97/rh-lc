module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsReducedOfSeparableMarkedCharpoly
public import Mathlib.GroupTheory.FiniteAbelian.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FgUnitsQuotIntegralUnitsFiniteFieldExt

section

@[expose] public section

open GlobalTheory.UnitLemma Polynomial IsDedekindDomain

noncomputable section
namespace GlobalTheory.FieldUnitsQuotFG

theorem fg_quot_ker {G S : Type} [CommGroup G] [Finite S] (φ : G →* (S → Multiplicative ℤ)) :
    Group.FG (G ⧸ φ.ker) := by
  let e : (S → ℤ) ≃+ Additive (S → Multiplicative ℤ) :=
    { toFun := fun f => Additive.ofMul (fun v => Multiplicative.ofAdd (f v))
      invFun := fun g v => Multiplicative.toAdd (Additive.toMul g v)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  haveI : Module.Finite ℤ (Additive (S → Multiplicative ℤ)) := Module.Finite.equiv e.toIntLinearEquiv
  have h1 : φ.range.FG := by
    rw [Subgroup.fg_iff_add_fg]
    rw [← AddSubgroup.toIntSubmodule_toAddSubgroup (Subgroup.toAddSubgroup φ.range)]
    exact (Submodule.fg_iff_addSubgroup_fg _).1 (IsNoetherian.noetherian _)
  haveI : Group.FG φ.range := (Group.fg_iff_subgroup_fg _).2 h1
  exact Group.fg_of_surjective (f := (QuotientGroup.quotientKerEquivRange φ).symm.toMonoidHom)
    (QuotientGroup.quotientKerEquivRange φ).symm.surjective

variable (K : UQ) (L : Type) [Field L] [Algebra K.O L] [Algebra K.E L] [IsScalarTower K.O K.E L]
  [FiniteDimensional K.E L]

theorem finite_spec [IsDedekindDomain (integralClosure K.O L)] :
    Finite (HeightOneSpectrum (integralClosure K.O L)) := by
  set C := integralClosure K.O L
  have hinj : Function.Injective (algebraMap K.O C) := by
    intro a b h
    have h2 : algebraMap K.O L a = algebraMap K.O L b := by
      rw [IsScalarTower.algebraMap_apply K.O C L a, h, ← IsScalarTower.algebraMap_apply]
    rw [IsScalarTower.algebraMap_apply K.O K.E L, IsScalarTower.algebraMap_apply K.O K.E L] at h2
    exact IsFractionRing.injective K.O K.E ((algebraMap K.E L).injective h2)
  set I := Ideal.map (algebraMap K.O C) (IsLocalRing.maximalIdeal K.O)
  have hI : I ≠ 0 := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible K.O
    intro h0
    have : algebraMap K.O C ϖ ∈ I :=
      Ideal.mem_map_of_mem _ (by rw [hϖ.maximalIdeal_eq]; exact Ideal.mem_span_singleton_self ϖ)
    rw [h0, Submodule.zero_eq_bot, Ideal.mem_bot] at this
    exact hϖ.ne_zero (hinj (this.trans (map_zero _).symm))
  have hall : ∀ v : HeightOneSpectrum C, v.asIdeal ∣ I := by
    intro v
    rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap]
    have hp : (v.asIdeal.comap (algebraMap K.O C)).IsPrime := Ideal.comap_isPrime _ _
    have hne : v.asIdeal.comap (algebraMap K.O C) ≠ ⊥ := by
      intro h
      exact v.ne_bot (Ideal.eq_bot_of_comap_eq_bot h)
    have hmax := hp.isMaximal hne
    rw [IsLocalRing.eq_maximalIdeal hmax]
  have := Ideal.finite_factors hI
  have huniv : (Set.univ : Set (HeightOneSpectrum C)) = {v | v.asIdeal ∣ I} := by
    ext v; simp [hall v]
  exact Set.finite_univ_iff.1 (huniv ▸ this)

def valHom [IsDedekindDomain (integralClosure K.O L)] [IsFractionRing (integralClosure K.O L) L] :
    Lˣ →* (HeightOneSpectrum (integralClosure K.O L) → Multiplicative ℤ) :=
  Pi.monoidHom fun v => WithZero.unitsWithZeroEquiv.toMonoidHom.comp
    (Units.map ((v.valuation L : Valuation L (WithZero (Multiplicative ℤ))) : L →* WithZero (Multiplicative ℤ)))

theorem valHom_apply [IsDedekindDomain (integralClosure K.O L)] [IsFractionRing (integralClosure K.O L) L]
    (x : Lˣ) (v : HeightOneSpectrum (integralClosure K.O L)) :
    ((valHom K L x v : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = v.valuation L (x : L) := by
  show ((WithZero.unitsWithZeroEquiv (Units.map ((v.valuation L : Valuation L (WithZero (Multiplicative ℤ))) :
    L →* WithZero (Multiplicative ℤ)) x) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = _
  rw [WithZero.coe_unitsWithZeroEquiv_eq_units_val]
  rfl

theorem ker_valHom [IsDedekindDomain (integralClosure K.O L)] [IsFractionRing (integralClosure K.O L) L] :
    (valHom K L).ker = intUnits K.O L := by
  ext x
  rw [MonoidHom.mem_ker]
  have key : ∀ y : L, IsIntegral K.O y ↔
      ∀ v : HeightOneSpectrum (integralClosure K.O L), v.valuation L y ≤ 1 := by
    intro y
    constructor
    · intro hy v
      have : y = algebraMap (integralClosure K.O L) L ⟨y, hy⟩ := rfl
      rw [this]
      exact v.valuation_le_one _
    · intro h
      obtain ⟨c, hc⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one L y h
      rw [← hc]
      exact c.2
  have h1 : valHom K L x = 1 ↔ ∀ v : HeightOneSpectrum (integralClosure K.O L), v.valuation L (x : L) = 1 := by
    rw [funext_iff]
    refine forall_congr' fun v => ?_
    rw [← valHom_apply, Pi.one_apply]
    constructor
    · intro h
      rw [h, WithZero.coe_one]
    · intro h
      exact WithZero.coe_injective (h.trans WithZero.coe_one.symm)
  rw [h1]
  show _ ↔ IsIntegral K.O (x : L) ∧ IsIntegral K.O ((x⁻¹ : Lˣ) : L)
  rw [key, key]
  constructor
  · intro h
    refine ⟨fun v => (h v).le, fun v => ?_⟩
    rw [Units.val_inv_eq_inv_val, map_inv₀, h v, inv_one]
  · rintro ⟨ha, hb⟩ v
    apply le_antisymm (ha v)
    have hx : v.valuation L (x : L) * v.valuation L ((x⁻¹ : Lˣ) : L) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    calc 1 = v.valuation L (x : L) * v.valuation L ((x⁻¹ : Lˣ) : L) := hx.symm
      _ ≤ v.valuation L (x : L) * 1 := by gcongr; exact hb v
      _ = v.valuation L (x : L) := mul_one _

theorem fg_units_quot : ∀ (K : UQ) (L : Type) [Field L] [Algebra K.O L] [Algebra K.E L] [IsScalarTower K.O K.E L]
    [FiniteDimensional K.E L], Group.FG (Lˣ ⧸ intUnits K.O L) := by
  intro K L _ _ _ _ _
  haveI : IsDedekindDomain (integralClosure K.O L) := integralClosure.isDedekindDomain K.O K.E L
  haveI : IsFractionRing (integralClosure K.O L) L := integralClosure.isFractionRing_of_finite_extension K.E L
  haveI := finite_spec K L
  rw [← ker_valHom K L]
  exact fg_quot_ker _

end GlobalTheory.FieldUnitsQuotFG
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FgUnitsQuotIntegralUnitsFiniteFieldExtStatement

section

@[expose] public section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.fg_units_quot_integralUnits_finite_field_ext : ∀ (K : UQ) (L : Type) [Field L] [Algebra K.O L] [Algebra K.E L] [IsScalarTower K.O K.E L] [FiniteDimensional K.E L], Group.FG (Lˣ ⧸ intUnits K.O L) := by
  first | exact @GlobalTheory.FieldUnitsQuotFG.fg_units_quot | exact GlobalTheory.FieldUnitsQuotFG.fg_units_quot | (intros; apply GlobalTheory.FieldUnitsQuotFG.fg_units_quot <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FgUnitsQuotIntegralUnitsReducedFiniteAlgebra

section

@[expose] public section

noncomputable section

open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma.NormUnits

theorem group_fg_pi {ι : Type} [Finite ι] (G : ι → Type) [∀ i, CommGroup (G i)]
    (hG : ∀ i, Group.FG (G i)) : Group.FG (∀ i, G i) := by
  classical
  have := Fintype.ofFinite ι
  choose S hS using fun i => Group.fg_iff.mp (hG i)
  refine Group.fg_iff.mpr ⟨⋃ i, Pi.mulSingle i '' S i, ?_,
    Set.finite_iUnion fun i => (hS i).2.image _⟩
  rw [eq_top_iff]
  intro x _
  rw [← Finset.univ_prod_mulSingle x]
  refine Subgroup.prod_mem _ fun i _ => ?_
  have hx : x i ∈ Subgroup.closure (S i) := by rw [(hS i).1]; trivial
  have h1 : Pi.mulSingle i (x i) ∈ (Subgroup.closure (S i)).map (MonoidHom.mulSingle G i) :=
    ⟨x i, hx, rfl⟩
  rw [MonoidHom.map_closure] at h1
  exact Subgroup.closure_mono (fun y hy => Set.mem_iUnion.2 ⟨i, hy⟩) h1

theorem isIntegral_of_forall_quot {O A : Type} [CommRing O] [CommRing A] [Algebra O A]
    [IsArtinianRing A] [IsReduced A] (x : A)
    (hx : ∀ I : MaximalSpectrum A, IsIntegral O (Ideal.Quotient.mk I.asIdeal x)) :
    IsIntegral O x := by
  classical
  have := Fintype.ofFinite (MaximalSpectrum A)
  choose p hpm hp using hx
  refine ⟨∏ I, p I, monic_prod_of_monic _ _ fun I _ => hpm I, ?_⟩
  rw [← aeval_def]
  apply (IsArtinianRing.equivPi A).injective
  funext J
  rw [map_zero, Pi.zero_apply, IsArtinianRing.equivPi_apply, map_prod, map_prod]
  refine Finset.prod_eq_zero (Finset.mem_univ J) ?_
  have h2 := aeval_algHom_apply (Ideal.Quotient.mkₐ O J.asIdeal) x (p J)
  rw [Ideal.Quotient.mkₐ_eq_mk] at h2
  rw [← h2, aeval_def]
  exact hp J

theorem units_quot_intUnits_fg : ∀ (K : UQ), (∀ (L : Type) [Field L] [Algebra K.O L] [Algebra K.E L]
    [IsScalarTower K.O K.E L] [FiniteDimensional K.E L], Group.FG (Lˣ ⧸ intUnits K.O L)) →
    ∀ (A : Type) [CommRing A] [Algebra K.O A] [Algebra K.E A] [IsScalarTower K.O K.E A]
    [Module.Finite K.E A], IsReduced A → Group.FG (Aˣ ⧸ intUnits K.O A) := by
  intro K hL A _ _ _ _ _ _
  classical
  haveI : IsArtinianRing A := IsArtinianRing.of_finite K.E A
  have := Fintype.ofFinite (MaximalSpectrum A)

  have hfg : ∀ I : MaximalSpectrum A,
      Group.FG ((A ⧸ I.asIdeal)ˣ ⧸ intUnits K.O (A ⧸ I.asIdeal)) := by
    intro I
    haveI := I.isMaximal
    letI : Field (A ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
    haveI : FiniteDimensional K.E (A ⧸ I.asIdeal) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ K.E I.asIdeal).toLinearMap
        Ideal.Quotient.mk_surjective
    exact hL (A ⧸ I.asIdeal)
  have hP := group_fg_pi (fun I : MaximalSpectrum A =>
    (A ⧸ I.asIdeal)ˣ ⧸ intUnits K.O (A ⧸ I.asIdeal)) hfg
  let ψ : Aˣ →* ∀ I : MaximalSpectrum A, (A ⧸ I.asIdeal)ˣ ⧸ intUnits K.O (A ⧸ I.asIdeal) :=
    MonoidHom.pi fun I => (QuotientGroup.mk' _).comp
      (Units.map (Ideal.Quotient.mk I.asIdeal).toMonoidHom)
  have hsurj : Function.Surjective ψ := by
    intro c
    choose u hu using fun I => QuotientGroup.mk'_surjective _ (c I)
    let e := IsArtinianRing.equivPi A
    refine ⟨Units.map (e.symm : (∀ I : MaximalSpectrum A, A ⧸ I.asIdeal) →* A)
      (MulEquiv.piUnits.symm u), ?_⟩
    funext I
    rw [← hu I]
    change QuotientGroup.mk' _ _ = _
    congr 1
    ext
    have h3 : ∀ z : ∀ I : MaximalSpectrum A, A ⧸ I.asIdeal,
        Ideal.Quotient.mk I.asIdeal (e.symm z) = z I := fun z => by
      rw [← IsArtinianRing.equivPi_apply A (e.symm z) I]
      exact congrFun (e.apply_symm_apply z) I
    simp only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
    rw [h3]
    rfl
  have hker : ψ.ker ≤ intUnits K.O A := by
    intro t ht
    have hI : ∀ I : MaximalSpectrum A,
        Units.map (Ideal.Quotient.mk I.asIdeal).toMonoidHom t ∈ intUnits K.O (A ⧸ I.asIdeal) :=
      fun I => (QuotientGroup.eq_one_iff _).mp (congrFun (MonoidHom.mem_ker.mp ht) I)
    refine ⟨NormUnits.isIntegral_of_forall_quot _ fun I => (hI I).1,
      NormUnits.isIntegral_of_forall_quot _ fun I => ?_⟩
    have := (hI I).2
    rwa [Units.coe_map_inv] at this
  haveI : Group.FG (Aˣ ⧸ ψ.ker) :=
    Group.fg_of_surjective (f := (QuotientGroup.quotientKerEquivOfSurjective ψ hsurj).symm.toMonoidHom)
      (QuotientGroup.quotientKerEquivOfSurjective ψ hsurj).symm.surjective
  refine Group.fg_of_surjective
    (f := QuotientGroup.map ψ.ker (intUnits K.O A) (MonoidHom.id _) fun t ht => hker ht) ?_
  intro q
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ q
  exact ⟨QuotientGroup.mk y, rfl⟩

end GlobalTheory.UnitLemma.NormUnits
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FgUnitsQuotIntegralUnitsReducedFiniteAlgebraStatement

section

@[expose] public section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.fg_units_quot_integralUnits_reduced_finite_algebra : ∀ (K : UQ), (∀ (L : Type) [Field L] [Algebra K.O L] [Algebra K.E L] [IsScalarTower K.O K.E L] [FiniteDimensional K.E L], Group.FG (Lˣ ⧸ intUnits K.O L)) → ∀ (A : Type) [CommRing A] [Algebra K.O A] [Algebra K.E A] [IsScalarTower K.O K.E A] [Module.Finite K.E A], IsReduced A → Group.FG (Aˣ ⧸ intUnits K.O A) := by
  first | exact @GlobalTheory.UnitLemma.NormUnits.units_quot_intUnits_fg | exact GlobalTheory.UnitLemma.NormUnits.units_quot_intUnits_fg | (intros; apply GlobalTheory.UnitLemma.NormUnits.units_quot_intUnits_fg <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsReducedOfSeparableMarkedCharpolyStatement

section

@[expose] public section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.isReduced_of_separable_markedCharpoly : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → IsReduced B.A := by
  first | exact @GlobalTheory.UnitLemma.InvAlg.isReduced_of_separable_P | exact GlobalTheory.UnitLemma.InvAlg.isReduced_of_separable_P | (intros; apply GlobalTheory.UnitLemma.InvAlg.isReduced_of_separable_P <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinsetCosetsIntegralNormUnits

section

@[expose] public section

open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.NormUnits

theorem fg_quot_intUnits : ∀ (K : UQ) (B : InvAlg K), B.P.Separable →
    Group.FG (B.Aˣ ⧸ intUnits K.O B.A) := fun K B hP =>
  haveI := GlobalTheory.T.isReduced_of_separable_markedCharpoly K B hP
  GlobalTheory.T.fg_units_quot_integralUnits_reduced_finite_algebra K (GlobalTheory.T.fg_units_quot_integralUnits_finite_field_ext K) B.A (GlobalTheory.T.isReduced_of_separable_markedCharpoly K B hP)

theorem exists_finset_sq_mem {G : Type} [CommGroup G] (N : Subgroup G) (hN : Group.FG (G ⧸ N)) :
    ∃ F : Finset G, ∀ u : G, u ^ 2 ∈ N → ∃ f ∈ F, u * f⁻¹ ∈ N := by
  let M := Additive (G ⧸ N)
  haveI : AddGroup.FG M := inferInstance
  haveI : Module.Finite ℤ M := Module.Finite.iff_addGroup_fg.mpr inferInstance
  let K2 : Submodule ℤ M := LinearMap.ker (LinearMap.lsmul ℤ M 2)
  haveI : Module.Finite ℤ K2 := Module.IsNoetherian.finite ℤ K2
  haveI : Finite K2 := Module.finite_of_fg_torsion K2 (fun x => ⟨⟨2, mem_nonZeroDivisors_of_ne_zero (by norm_num)⟩, by
    apply Subtype.ext; have h := x.2; rw [LinearMap.mem_ker, LinearMap.lsmul_apply] at h
    simpa using h⟩)
  let r : K2 → G := fun k => Quotient.out (Additive.toMul (k : M))
  refine ⟨(Set.finite_range r).toFinset, fun u hu => ?_⟩
  have hk : (Additive.ofMul (QuotientGroup.mk u : G ⧸ N) : M) ∈ K2 := by
    show (2 : ℤ) • (Additive.ofMul (QuotientGroup.mk u : G ⧸ N) : M) = 0
    rw [← ofMul_zpow]
    show Additive.ofMul ((QuotientGroup.mk u : G ⧸ N) ^ (2 : ℤ)) = Additive.ofMul 1
    congr 1
    rw [zpow_two, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, ← pow_two]; exact hu
  refine ⟨r ⟨_, hk⟩, by simp, ?_⟩
  have h1 : (QuotientGroup.mk (r ⟨_, hk⟩) : G ⧸ N) = QuotientGroup.mk u := by
    simp only [r]; exact Quotient.out_eq' _
  have := QuotientGroup.eq.mp h1.symm
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, h1, mul_inv_cancel]

end GlobalTheory.NormUnits

namespace GlobalTheory.NormUnits

theorem exists_finset_normUnits : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → ∃ F : Finset B.Aˣ, ∀ u : B.Aˣ,
    (∃ w ∈ intUnits K.O B.A, (w : B.A) = u * B.σ u) →
      ∃ f ∈ F, ∃ t ∈ B.T, u * f⁻¹ * t⁻¹ ∈ intUnits K.O B.A := by
  intro K B hP
  let N : Subgroup B.Aˣ := B.T ⊔ intUnits K.O B.A
  have hFG : Group.FG (B.Aˣ ⧸ N) :=
    haveI := fg_quot_intUnits K B hP
    Group.fg_of_surjective (f := QuotientGroup.map (intUnits K.O B.A) N (MonoidHom.id _) le_sup_right)
      (fun q => QuotientGroup.induction_on q fun x => ⟨QuotientGroup.mk x, rfl⟩)
  obtain ⟨F, hF⟩ := exists_finset_sq_mem N hFG
  refine ⟨F, fun u ⟨w, hw, hwu⟩ => ?_⟩
  let su : B.Aˣ := Units.map (B.σ : B.A →* B.A) u
  have hsu : (su : B.A) = B.σ u := rfl
  have ht : u * su⁻¹ ∈ B.T := by
    show ((u * su⁻¹ : B.Aˣ) : B.A) * B.σ ((u * su⁻¹ : B.Aˣ) : B.A) = 1
    have h1 : B.σ ((su⁻¹ : B.Aˣ) : B.A) * u = 1 := by
      have : B.σ ((su⁻¹ : B.Aˣ) : B.A) * B.σ (su : B.A) = 1 := by rw [← map_mul, Units.inv_mul, map_one]
      rwa [hsu, B.σ_σ] at this
    calc ((u * su⁻¹ : B.Aˣ) : B.A) * B.σ ((u * su⁻¹ : B.Aˣ) : B.A)
        = (B.σ ((su⁻¹ : B.Aˣ) : B.A) * u) * ((su : B.A) * ((su⁻¹ : B.Aˣ) : B.A)) := by
          simp only [Units.val_mul, map_mul]; rw [hsu]; ring
      _ = 1 := by rw [h1, Units.mul_inv, one_mul]
  have hsq : u ^ 2 ∈ N := by
    have : u ^ 2 = (u * su⁻¹) * w := by
      ext; rw [Units.val_mul, hwu, ← hsu]
      simp only [Units.val_pow_eq_pow_val, Units.val_mul]
      calc (u : B.A) ^ 2 = (u : B.A) * u * (((su⁻¹ : B.Aˣ) : B.A) * su) := by rw [Units.inv_mul, mul_one, sq]
        _ = _ := by ring
    rw [this]; exact N.mul_mem (Subgroup.mem_sup_left ht) (Subgroup.mem_sup_right hw)
  obtain ⟨f, hfF, hf⟩ := hF u hsq
  obtain ⟨t, htT, z, hz, htz⟩ := Subgroup.mem_sup.mp hf
  refine ⟨f, hfF, t, htT, ?_⟩
  have : u * f⁻¹ * t⁻¹ = z := by rw [← htz, mul_comm t z, mul_assoc, mul_inv_cancel, mul_one]
  rw [this]; exact hz

end GlobalTheory.NormUnits
end
end
