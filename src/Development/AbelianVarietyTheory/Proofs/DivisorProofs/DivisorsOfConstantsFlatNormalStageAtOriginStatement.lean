module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalizationAtPrimeIsDomainIsIntegrallyClos
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRootSubMemOfEvalMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStrictHenselisation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStrictHenselisationOfDirectedUnion
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRingHomOfIsStrictHenselisation
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIndEtaleOfEtaleOfIsIndEtale
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
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalStageTensorPolynomialOrigin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdealExtensionPrime
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictHenselisationEtaleOverPolynomial
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.TotallySplit

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalHomToStrictlyHenselianNormal

section

@[expose] public section

open IsLocalRing Polynomial

namespace GlobalTheory.NormalStrictHens

theorem exists_mem_finset {S : Type} [CommRing S] {ι : Type} [Preorder ι] [IsDirected ι (· ≤ ·)]
    [Nonempty ι] (R : ι → Subring S) (hmono : Monotone R) (hcov : ∀ x : S, ∃ i, x ∈ R i)
    (s : Finset S) : ∃ i, ∀ x ∈ s, x ∈ R i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨Classical.arbitrary ι, by simp⟩
  | insert x s _ ih =>
    obtain ⟨i, hi⟩ := ih
    obtain ⟨j, hj⟩ := hcov x
    obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
    refine ⟨k, fun y hy => ?_⟩
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact hmono hjk hj
    · exact hmono hik (hi y hy)

theorem isDomain_of_directed {S : Type} [CommRing S] [Nontrivial S] {ι : Type} [Preorder ι]
    [IsDirected ι (· ≤ ·)] [Nonempty ι] (R : ι → Subring S) (hmono : Monotone R)
    (hcov : ∀ x : S, ∃ i, x ∈ R i) (hdom : ∀ i, IsDomain (R i)) : IsDomain S := by
  classical
  haveI : NoZeroDivisors S := ⟨fun {x y} hxy => by
    obtain ⟨k, hk⟩ := exists_mem_finset R hmono hcov {x, y}
    haveI := hdom k
    have hx : x ∈ R k := hk x (by simp)
    have hy : y ∈ R k := hk y (by simp)
    have h : (⟨x, hx⟩ : R k) * ⟨y, hy⟩ = 0 := Subtype.ext hxy
    rcases mul_eq_zero.1 h with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)⟩
  exact NoZeroDivisors.to_isDomain S

theorem isIntegrallyClosed_of_directed {S : Type} [CommRing S] [IsDomain S] {ι : Type} [Preorder ι]
    [IsDirected ι (· ≤ ·)] [Nonempty ι] (R : ι → Subring S) (hmono : Monotone R)
    (hcov : ∀ x : S, ∃ i, x ∈ R i) (hdom : ∀ i, IsDomain (R i))
    (hic : ∀ i, IsIntegrallyClosed (R i)) : IsIntegrallyClosed S := by
  classical
  rw [isIntegrallyClosed_iff (FractionRing S)]
  intro x hx
  obtain ⟨f, hfm, hf⟩ := hx
  obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors S) x
  obtain ⟨k, hk⟩ := exists_mem_finset R hmono hcov (insert a (insert (b : S) f.coeffs))
  haveI := hdom k
  haveI := hic k
  have ha : a ∈ R k := hk a (by simp)
  have hb : (b : S) ∈ R k := hk b (by simp)
  have hcf : (f.coeffs : Set S) ⊆ R k := fun c hc =>
    hk c (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hc))
  have hgm : (f.toSubring (R k) hcf).Monic := (monic_toSubring f (R k) hcf).2 hfm
  have hgf : (f.toSubring (R k) hcf).map (R k).subtype = f := map_toSubring f (R k) hcf
  have hinj : Function.Injective ((algebraMap S (FractionRing S)).comp (R k).subtype) :=
    (IsFractionRing.injective S (FractionRing S)).comp Subtype.val_injective
  let φ : FractionRing (R k) →+* FractionRing S := IsFractionRing.lift hinj
  have hφ : ∀ r : R k, φ (algebraMap (R k) (FractionRing (R k)) r) = algebraMap S (FractionRing S) r :=
    fun r => IsFractionRing.lift_algebraMap hinj r
  have hb0 : (⟨b, hb⟩ : R k) ∈ nonZeroDivisors (R k) := by
    rw [mem_nonZeroDivisors_iff_ne_zero]
    intro h
    exact nonZeroDivisors.coe_ne_zero b (congrArg Subtype.val h)
  have hφy : φ (IsLocalization.mk' (FractionRing (R k)) (⟨a, ha⟩ : R k) ⟨⟨b, hb⟩, hb0⟩) =
      IsLocalization.mk' (FractionRing S) a b := by
    rw [IsFractionRing.lift_mk', IsFractionRing.mk'_eq_div]
    rfl
  have hcomp : φ.comp (algebraMap (R k) (FractionRing (R k))) =
      (algebraMap S (FractionRing S)).comp (R k).subtype := by
    ext r
    exact hφ r
  have hy : IsIntegral (R k) (IsLocalization.mk' (FractionRing (R k)) (⟨a, ha⟩ : R k) ⟨⟨b, hb⟩, hb0⟩) := by
    refine ⟨f.toSubring (R k) hcf, hgm, ?_⟩
    apply φ.injective
    rw [map_zero, hom_eval₂, hφy, hcomp, ← eval₂_map, hgf]
    exact hf
  obtain ⟨c, hc⟩ := (isIntegrallyClosed_iff (FractionRing (R k))).1 inferInstance hy
  refine ⟨c, ?_⟩
  rw [← hφ, hc, hφy]

end GlobalTheory.NormalStrictHens

namespace GlobalTheory


open GlobalTheory.NormalStrictHens in
theorem exists_strictlyHenselian_normal_between : ∀ (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T],
    GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      (i : A →+* T), IsLocalHom i →
    ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : HenselianLocalRing A')
      (_ : IsSepClosed (ResidueField A')) (_ : IsNoetherianRing A') (_ : IsIntegrallyClosed A')
      (ι : A →+* A') (α : A' →+* T), α.comp ι = i ∧ IsLocalHom α := by
  intro T _ _ _ hT A _ _ _ _ _ i hi
  haveI := hi
  obtain ⟨hThens, hTac, -⟩ :=
    GlobalTheory.AbsIntClosedLocal.henselian_isAlgClosed_pow_surj T ⟨inferInstance, hT⟩
  haveI := hThens
  haveI := hTac
  obtain ⟨S, _, _, _, hloc, hsc, -, hmax, -, ι, _, _, _, Si, hmono, hcov, hSi⟩ :=
    GlobalTheory.exists_strictHenselisation A (SeparableClosure (ResidueField A))
  haveI := hsc
  have hind : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap A S) :=
    GlobalTheory.StrictHensUnion.indEtale_of_directed_union A S ι Si hmono hcov fun k => by
      obtain ⟨B, _, _, _, q, _, ⟨e⟩⟩ := hSi k
      exact GlobalTheory.StrictHensUnion.indEtale_of_algEquiv e
        (GlobalTheory.StrictHensUnion.indEtale_localization_of_etale A B q.primeCompl)
  have hsh : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation (algebraMap A S) :=
    ⟨inferInstance, hsc, hloc, hind⟩
  haveI : IsNoetherianRing S := GlobalTheory.StalkNoeth.isNoetherianRing_of_indEt A S hind
  have hdi : ∀ k, IsDomain (Si k).toSubring ∧ IsIntegrallyClosed (Si k).toSubring := fun k => by
    obtain ⟨B, _, _, _, q, _, ⟨e⟩⟩ := hSi k
    obtain ⟨h1, h2⟩ := GlobalTheory.etale_localization_atPrime_isDomain_isIntegrallyClosed A B q
    let e' : Localization.AtPrime q ≃+* (Si k).toSubring :=
      e.toRingEquiv.trans
        { toFun := fun x => ⟨x.1, x.2⟩
          invFun := fun x => ⟨x.1, x.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_mul' := fun _ _ => rfl
          map_add' := fun _ _ => rfl }
    exact ⟨e'.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e'⟩
  have hmono' : Monotone fun k => (Si k).toSubring := fun _ _ h => hmono h
  haveI : IsDomain S := isDomain_of_directed _ hmono' hcov fun k => (hdi k).1
  have hic : IsIntegrallyClosed S :=
    isIntegrallyClosed_of_directed _ hmono' hcov (fun k => (hdi k).1) fun k => (hdi k).2
  obtain ⟨α, hα⟩ :=
    GlobalTheory.NCyc.StrictLocLift.exists_ringHom_of_isStrictHenselisation (algebraMap A S) hsh i
  have hle : maximalIdeal S ≤ (maximalIdeal T).comap α := by
    rw [← hmax, Ideal.map_le_iff_le_comap, Ideal.comap_comap, hα]
    intro a ha
    exact map_nonunit i a ha
  refine ⟨S, inferInstance, inferInstance, inferInstance, hsc, inferInstance, hic,
    algebraMap A S, α, hα, ⟨fun s hs => ?_⟩⟩
  by_contra h
  exact (mem_maximalIdeal _).1 (hle ((mem_maximalIdeal s).2 h)) hs

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalHomToStrictlyHenselianNormalStatement

section

@[expose] public section

open IsLocalRing Polynomial

theorem _root_.GlobalTheory.T.exists_local_hom_to_strictly_henselian_normal : ∀ (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      (i : A →+* T), IsLocalHom i →
    ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : HenselianLocalRing A')
      (_ : IsSepClosed (ResidueField A')) (_ : IsNoetherianRing A') (_ : IsIntegrallyClosed A')
      (ι : A →+* A') (α : A' →+* T), α.comp ι = i ∧ IsLocalHom α := by
  first | (exact @GlobalTheory.exists_strictlyHenselian_normal_between) | (exact GlobalTheory.exists_strictlyHenselian_normal_between) | (intros; apply GlobalTheory.exists_strictlyHenselian_normal_between  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalStageTensorPolynomialOriginStatement

section

@[expose] public section

open IsLocalRing Polynomial

theorem _root_.GlobalTheory.T.exists_localStage_tensor_polynomial_origin : ∀ (T O : Type) [CommRing T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O],
    (maximalIdeal O).comap (algebraMap (Polynomial T) O) = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (A : Type) [CommRing A] [IsLocalRing A] (i : A →+* T), IsLocalHom i →
    ∀ (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime],
      QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ (jA : Localization.AtPrime QA →+* O),
      jA.comp (algebraMap (Polynomial A) (Localization.AtPrime QA)) =
        (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) →
    ∀ (A' : Type) [CommRing A'] [IsLocalRing A'] (ι : A →+* A') (α : A' →+* T), α.comp ι = i → IsLocalHom α →
    ∃ (E' : Type) (_ : CommRing E') (_ : Algebra (Polynomial A') E') (_ : Algebra.Etale (Polynomial A') E')
      (Q' : Ideal E') (_ : Q'.IsPrime),
      Q'.comap (algebraMap (Polynomial A') E') = GlobalTheory.KeyOriginCut.originIdeal A' ∧
      ∃ (β : Localization.AtPrime QA →+* Localization.AtPrime Q') (γ : Localization.AtPrime Q' →+* O),
        ((algebraMap (Polynomial A') (Localization.AtPrime Q')).comp Polynomial.C).comp ι =
          β.comp ((algebraMap (Polynomial A) (Localization.AtPrime QA)).comp Polynomial.C) ∧
        γ.comp β = jA ∧
        γ.comp ((algebraMap (Polynomial A') (Localization.AtPrime Q')).comp Polynomial.C) =
          (algebraMap T O).comp α := by
  first | (exact @GlobalTheory.LocalStage.localStage) | (exact GlobalTheory.LocalStage.localStage) | (intros; apply GlobalTheory.LocalStage.localStage  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorsOfConstantsFlatNormalStageAtOrigin

section

@[expose] public section

open IsLocalRing Polynomial

noncomputable section

namespace GlobalTheory.GoodStageOrigin

theorem local_props (A' : Type) [CommRing A'] [IsDomain A'] [IsNoetherianRing A'] [IsIntegrallyClosed A']
    (E : Type) [CommRing E] [Algebra (Polynomial A') E] [Algebra.Etale (Polynomial A') E]
    (Q : Ideal E) [Q.IsPrime] :
    IsDomain (Localization.AtPrime Q) ∧ IsNoetherianRing (Localization.AtPrime Q) ∧
      IsIntegrallyClosed (Localization.AtPrime Q) ∧
      (letI : Algebra A' (Localization.AtPrime Q) :=
        ((algebraMap (Polynomial A') (Localization.AtPrime Q)).comp Polynomial.C).toAlgebra
       Module.Flat A' (Localization.AtPrime Q)) := by
  haveI : IsIntegrallyClosed (Polynomial A') := by
    haveI := GlobalTheory.isIntegrallyClosed_mvPolynomial_fin A' 1
    exact IsIntegrallyClosed.of_equiv
      (MvPolynomial.uniqueAlgEquiv A' (Fin 1)).toRingEquiv
  obtain ⟨h1, h2⟩ := GlobalTheory.etale_localization_atPrime_isDomain_isIntegrallyClosed (Polynomial A') E Q
  haveI : IsNoetherianRing E := Algebra.FiniteType.isNoetherianRing (Polynomial A') E
  refine ⟨h1, IsLocalization.isNoetherianRing Q.primeCompl _ inferInstance, h2, ?_⟩
  letI : Algebra A' (Localization.AtPrime Q) :=
    ((algebraMap (Polynomial A') (Localization.AtPrime Q)).comp Polynomial.C).toAlgebra
  haveI : IsScalarTower A' (Polynomial A') (Localization.AtPrime Q) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Module.Flat (Polynomial A') E := inferInstance
  haveI : Module.Flat E (Localization.AtPrime Q) := IsLocalization.flat _ Q.primeCompl
  haveI : Module.Flat (Polynomial A') (Localization.AtPrime Q) := Module.Flat.trans (Polynomial A') E _
  exact Module.Flat.trans A' (Polynomial A') _

theorem good_stage : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T), Function.Injective i → IsLocalHom i →
    ∀ (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime],
      QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ (jA : Localization.AtPrime QA →+* O),
      jA.comp (algebraMap (Polynomial A) (Localization.AtPrime QA)) =
        (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) →
    ∀ (sA : A), sA ≠ 0 →
    ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : IsNoetherianRing A') (_ : IsIntegrallyClosed A')
      (B' : Type) (_ : CommRing B') (_ : IsDomain B') (_ : IsLocalRing B') (_ : IsNoetherianRing B')
      (_ : IsIntegrallyClosed B') (_ : Algebra A' B') (_ : Module.Flat A' B')
      (ι : A →+* A') (α : A' →+* T) (β : Localization.AtPrime QA →+* B') (γ : B' →+* O),
      (algebraMap A' B').comp ι = β.comp (algebraMap A (Localization.AtPrime QA)) ∧
      γ.comp β = jA ∧ γ.comp (algebraMap A' B') = (algebraMap T O).comp α ∧ ι sA ≠ 0 ∧
      ∀ 𝔭 : Ideal A', 𝔭.IsPrime → 𝔭.height = 1 → ι sA ∈ 𝔭 →
        (𝔭.map (algebraMap A' B')).IsPrime := by
  intro T O _ _ _ _ _ _ _ _ hT P _ φ hφ hsh hP A _ _ _ _ _ _ i hi hil EA _ _ _ _ _ QA _ hQA jA hjA sA hsA
  have hO : (maximalIdeal O).comap (algebraMap (Polynomial T) O) = GlobalTheory.KeyOriginCut.originIdeal T := by
    haveI : IsLocalHom φ := hsh.2.2.1
    rw [← hφ, ← Ideal.comap_comap, GlobalTheory.comap_maximalIdeal_of_localHom_strictHens φ, ← hP]
    first
      | exact Localization.AtPrime.under_maximalIdeal (Localization.AtPrime P) P
      | exact Localization.AtPrime.under_maximalIdeal
      | simpa [Ideal.under] using Localization.AtPrime.under_maximalIdeal (Localization.AtPrime P) P
  obtain ⟨A', _, _, _, _, _, _, ι, α, hια, hα⟩ := GlobalTheory.T.exists_local_hom_to_strictly_henselian_normal T hT A i hil
  obtain ⟨E', _, _, _, Q', _, hQ', β, γ, h1, h2, h3⟩ :=
    GlobalTheory.T.exists_localStage_tensor_polynomial_origin T O hO A i hil EA QA hQA jA hjA A' ι α hια hα
  obtain ⟨hd, hn, hic, hfl⟩ := local_props A' E' Q'
  letI alg : Algebra A' (Localization.AtPrime Q') :=
    ((algebraMap (Polynomial A') (Localization.AtPrime Q')).comp Polynomial.C).toAlgebra
  refine ⟨A', inferInstance, inferInstance, inferInstance, inferInstance, Localization.AtPrime Q',
    inferInstance, hd, inferInstance, hn, hic, alg, hfl, ι, α, β, γ, ?_, h2, h3, ?_, ?_⟩
  · have e : algebraMap A (Localization.AtPrime QA) =
        (algebraMap (Polynomial A) (Localization.AtPrime QA)).comp Polynomial.C := by
      rw [IsScalarTower.algebraMap_eq A EA (Localization.AtPrime QA),
        IsScalarTower.algebraMap_eq A (Polynomial A) EA, Polynomial.algebraMap_eq,
        IsScalarTower.algebraMap_eq (Polynomial A) EA (Localization.AtPrime QA)]
      rfl
    rw [e]
    exact h1
  · intro h
    apply hsA
    apply hi
    rw [map_zero, ← hια, RingHom.comp_apply, h, map_zero]
  · intro 𝔭 _ _ _
    exact GlobalTheory.T.origin_ideal_extension_prime A' 𝔭 E' Q' hQ'

end GlobalTheory.GoodStageOrigin
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorsOfConstantsFlatNormalStageAtOriginStatement

section

@[expose] public section

open IsLocalRing Polynomial

theorem _root_.GlobalTheory.T.divisorsOfConstants_flat_normal_stage_at_origin : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T), Function.Injective i → IsLocalHom i →
    ∀ (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime],
      QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ (jA : Localization.AtPrime QA →+* O),
      jA.comp (algebraMap (Polynomial A) (Localization.AtPrime QA)) =
        (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) →
    ∀ (sA : A), sA ≠ 0 →
    ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : IsNoetherianRing A') (_ : IsIntegrallyClosed A')
      (B' : Type) (_ : CommRing B') (_ : IsDomain B') (_ : IsLocalRing B') (_ : IsNoetherianRing B')
      (_ : IsIntegrallyClosed B') (_ : Algebra A' B') (_ : Module.Flat A' B')
      (ι : A →+* A') (α : A' →+* T) (β : Localization.AtPrime QA →+* B') (γ : B' →+* O),
      (algebraMap A' B').comp ι = β.comp (algebraMap A (Localization.AtPrime QA)) ∧
      γ.comp β = jA ∧ γ.comp (algebraMap A' B') = (algebraMap T O).comp α ∧ ι sA ≠ 0 ∧
      ∀ 𝔭 : Ideal A', 𝔭.IsPrime → 𝔭.height = 1 → ι sA ∈ 𝔭 →
        (𝔭.map (algebraMap A' B')).IsPrime := by
  first | (exact @GlobalTheory.GoodStageOrigin.good_stage) | (exact GlobalTheory.GoodStageOrigin.good_stage) | (intros; apply GlobalTheory.GoodStageOrigin.good_stage <;> assumption)
end
end
