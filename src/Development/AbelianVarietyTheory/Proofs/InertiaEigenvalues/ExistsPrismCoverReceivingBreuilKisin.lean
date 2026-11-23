module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteProductOrientedBoundedPrismsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsPrismLocalizationAwayOfGeneratedStatement
public import Mathlib.RingTheory.PicardGroup
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPrismCoverBreuilKisinCoproductInlStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPrismCoverOfStableMaximalMapNeTop
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsStablePrismHomComp
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsStablePrismHomOfFiniteProductComponentsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismHomMapIdealEqStatement
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyBreuilKisinPrismCoproductStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvertibleIdealPrincipalOnZariskiCover

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.ZarPrincipal

theorem form_mul_comm {A : Type} [CommRing A] (I : Ideal A) (f : Module.Dual A ↥I)
    (y x : ↥I) : f y * (x : A) = f x * (y : A) := by
  have h : (x : A) • y = (y : A) • x := by
    ext; simp [mul_comm]
  have := congrArg f h
  simp only [map_smul, smul_eq_mul] at this
  rw [mul_comm, this, mul_comm]

theorem one_mem_span_values {A : Type} [CommRing A] (I : Ideal A) [Module.Invertible A ↥I] :
    (1 : A) ∈ Ideal.span {a | ∃ (f : Module.Dual A ↥I) (y : ↥I), f y = a} := by
  obtain ⟨t, ht⟩ := (Module.Invertible.bijective (R := A) (M := ↥I)).2 1
  rw [← ht]
  clear ht
  induction t with
  | tmul f y => exact Ideal.subset_span ⟨f, y, by simp [contractLeft_apply]⟩
  | add a b ha hb => rw [map_add (f := _)]; exact Ideal.add_mem _ ha hb

end GlobalTheory.BSP.ZarPrincipal


open GlobalTheory.BSP.ZarPrincipal in
theorem GlobalTheory.BSP.invertible_ideal_principal_on_cover :
    ∀ (A : Type) [CommRing A] (I : Ideal A), Module.Invertible A ↥I → ∃ (n : ℕ) (s t : Fin n → A),
      Ideal.span (Set.range s) = ⊤ ∧ ∀ i, t i ∈ I ∧ ∀ x ∈ I, ∃ c, s i * x = c * t i := by
  intro A _ I hI
  set S : Set A := {a | ∃ (f : Module.Dual A ↥I) (y : ↥I), f y = a} with hS
  have h1 : (1 : A) ∈ Ideal.span S := one_mem_span_values I
  obtain ⟨T, hTS, hT⟩ := Submodule.mem_span_finite_of_mem_span h1
  have hmem : ∀ a : T, ∃ (f : Module.Dual A ↥I) (y : ↥I), f y = (a : A) := fun a => hTS a.2
  choose f y hfy using hmem
  let e := T.equivFin
  refine ⟨T.card, fun i => ((e.symm i : T) : A), fun i => (y (e.symm i) : A), ?_, ?_⟩
  · rw [Ideal.eq_top_iff_one]
    refine Submodule.span_mono ?_ hT
    intro a ha
    exact ⟨e ⟨a, ha⟩, by simp⟩
  · intro i
    refine ⟨(y (e.symm i)).2, fun x hx => ⟨f (e.symm i) ⟨x, hx⟩, ?_⟩⟩
    show ((e.symm i : T) : A) * x = _ * (y (e.symm i) : A)
    rw [← hfy (e.symm i)]
    exact form_mul_comm I (f (e.symm i)) (y (e.symm i)) ⟨x, hx⟩
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvertibleIdealPrincipalOnZariskiCoverStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.invertible_ideal_principal_on_zariski_cover : ∀ (A : Type) [CommRing A] (I : Ideal A), Module.Invertible A ↥I → ∃ (n : ℕ) (s t : Fin n → A), Ideal.span (Set.range s) = ⊤ ∧ ∀ i, t i ∈ I ∧ ∀ x ∈ I, ∃ c, s i * x = c * t i := by
  first | exact @GlobalTheory.BSP.invertible_ideal_principal_on_cover | exact GlobalTheory.BSP.invertible_ideal_principal_on_cover | (intros; apply GlobalTheory.BSP.invertible_ideal_principal_on_cover <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPrismCoverOfStableMaximalMapNeTopStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.isPrismCover_of_stable_maximal_map_ne_top : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B C : Obj l R) (h : Hom B C), Stable h → (∀ 𝔪 : Ideal B.A, 𝔪.IsMaximal → 𝔪.map h.f ≠ ⊤) → Cover h := by
  first | exact @GlobalTheory.BSP.cover_of_stable_of_map_ne_top | exact GlobalTheory.BSP.cover_of_stable_of_map_ne_top | (intros; apply GlobalTheory.BSP.cover_of_stable_of_map_ne_top <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsStablePrismHomCompStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.isStablePrismHom_comp : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B C D : Obj l R) (h : Hom B C) (h₂ : Hom C D), Stable h → Stable h₂ → Stable (h₂.comp h) := by
  first | exact @GlobalTheory.BSP.stable_comp | exact GlobalTheory.BSP.stable_comp | (intros; apply GlobalTheory.BSP.stable_comp <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsStablePrismHomOfLocalizationAway

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem isPushout_of_away {A C A' C' : Type} [CommRing A] [CommRing C] [CommRing A'] [CommRing C']
    (h : A →+* C) (k : A →+* A') (k' : C →+* C') (h' : A' →+* C') (e : k'.comp h = h'.comp k) (x : A)
    (H : letI := h.toAlgebra; IsLocalization.Away x C)
    (H' : letI := h'.toAlgebra; IsLocalization.Away (k x) C') :
    CategoryTheory.IsPushout (CommRingCat.ofHom h) (CommRingCat.ofHom k) (CommRingCat.ofHom k')
      (CommRingCat.ofHom h') := by
  letI : Algebra A C := h.toAlgebra
  letI : Algebra A A' := k.toAlgebra
  letI : Algebra C C' := k'.toAlgebra
  letI : Algebra A' C' := h'.toAlgebra
  letI : Algebra A C' := (h'.comp k).toAlgebra
  haveI : IsScalarTower A A' C' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower A C C' := IsScalarTower.of_algebraMap_eq fun a => (RingHom.congr_fun e a).symm
  haveI : IsLocalization (Submonoid.powers x) C := H
  haveI : IsLocalization (Algebra.algebraMapSubmonoid A' (Submonoid.powers x)) C' := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
    exact H'
  haveI : Algebra.IsPushout A A' C C' :=
    Algebra.isPushout_of_isLocalization (Submonoid.powers x) C A' C'
  exact (CommRingCat.isPushout_iff_isPushout (R := A) (R' := C) (S := A') (S' := C')).2
    (Algebra.IsPushout.symm inferInstance)

theorem IsLoc.isUnit_of_complete {l : ℕ} {R : Type} [CommRing R] {B C : Obj l R} {s : B.A} {h : Hom B C}
    (H : IsLoc s h) : IsUnit (h.f s) := by
  have hu : IsUnit (qmap h 1 (Ideal.Quotient.mk (adI B ^ 1) s)) := by
    letI := (qmap h 1).toAlgebra
    haveI := H.away 1
    exact IsLocalization.Away.algebraMap_isUnit _
  rw [qmap_mk] at hu
  haveI := C.complete
  have hj : adI C ^ 1 ≤ (⊥ : Ideal C.A).jacobson := by
    rw [pow_one]
    exact IsAdicComplete.le_jacobson_bot _
  haveI := isLocalHom_of_le_jacobson_bot _ hj
  exact IsUnit.of_map (Ideal.Quotient.mk _) _ hu

theorem stable_of_isLoc : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B C : Obj l R) (s : B.A) (h : Hom B C),
    (∃ t ∈ B.I, ∀ x ∈ B.I, ∃ k : ℕ, s ^ k * x ∈ Ideal.span {t}) → IsLoc s h → Stable h := by
  rintro l _ R _ B C s h ⟨t, ht, hst⟩ H
  refine ⟨fun m => ?_, fun B' k => ?_⟩
  · letI := (qmap h m).toAlgebra
    haveI := H.away m
    exact IsLocalization.flat _ (Submonoid.powers (Ideal.Quotient.mk (adI B ^ m) s))
  ·
    have hgen : GenAway B' (k.f s) (k.f t) := by
      refine ⟨k.f_I t ht, fun x hx => ?_⟩
      rw [← GlobalTheory.T.prism_hom_map_ideal_eq l R B B' k] at hx
      have hx' : x ∈ Ideal.span (k.f '' B.I) := hx
      refine Submodule.span_induction
        (p := fun x _ => ∃ n : ℕ, k.f s ^ n * x ∈ Ideal.span {k.f t}) ?_ ?_ ?_ ?_ hx'
      · rintro _ ⟨y, hy, rfl⟩
        obtain ⟨n, hn⟩ := hst y hy
        obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hn
        refine ⟨n, Ideal.mem_span_singleton'.2 ⟨k.f c, ?_⟩⟩
        simpa only [map_mul, map_pow] using congrArg k.f hc
      · exact ⟨0, by simp⟩
      · rintro a b _ _ ⟨n₁, h₁⟩ ⟨n₂, h₂⟩
        refine ⟨n₁ + n₂, ?_⟩
        have hab : k.f s ^ (n₁ + n₂) * (a + b) =
            k.f s ^ n₂ * (k.f s ^ n₁ * a) + k.f s ^ n₁ * (k.f s ^ n₂ * b) := by ring
        rw [hab]
        exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h₁) (Ideal.mul_mem_left _ _ h₂)
      · rintro a b _ ⟨n, hn⟩
        refine ⟨n, ?_⟩
        rw [smul_eq_mul, mul_left_comm]
        exact Ideal.mul_mem_left _ _ hn
    obtain ⟨C', h', hloc', -⟩ := GlobalTheory.T.exists_isPrismLocalizationAway_of_generated l R B' (k.f s) (k.f t) hgen
    obtain ⟨k', hk'⟩ := H.univ C' (h'.comp k)
      (show IsUnit (h'.f (k.f s)) from IsLoc.isUnit_of_complete hloc')
    refine ⟨C', k', h', hk', fun m => ?_⟩
    refine isPushout_of_away (qmap h m) (qmap k m) (qmap k' m) (qmap h' m) ?_
      (Ideal.Quotient.mk _ s) (H.away m) ?_
    · refine Ideal.Quotient.ringHom_ext (RingHom.ext fun a => ?_)
      simp only [RingHom.comp_apply, qmap_mk]
      exact congrArg (fun g : Hom B C' => Ideal.Quotient.mk (adI C' ^ m) (g.f a)) hk'
    · rw [qmap_mk]
      exact hloc'.away m

end GlobalTheory.BSP
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsStablePrismHomOfLocalizationAwayStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.isStablePrismHom_of_localizationAway : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B C : Obj l R) (s : B.A) (h : Hom B C), (∃ t ∈ B.I, ∀ x ∈ B.I, ∃ k : ℕ, s ^ k * x ∈ Ideal.span {t}) → IsLoc s h → Stable h := by
  first | exact @GlobalTheory.BSP.stable_of_isLoc | exact GlobalTheory.BSP.stable_of_isLoc | (intros; apply GlobalTheory.BSP.stable_of_isLoc <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrismCoverReceivingBreuilKisin

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem map_ne_top_of_isLoc_ff {l : ℕ} {R : Type} [CommRing R] {B L C : Obj l R} (s : B.A) (h : Hom B L)
    (hL : IsLoc s h) (e : Hom L C) (he : (qmap e 1).FaithfullyFlat) (𝔪 : Ideal B.A) (hm : 𝔪.IsMaximal)
    (hs : s ∉ 𝔪) : 𝔪.map (e.comp h).f ≠ ⊤ := by
  have hJ : adI B ^ 1 ≤ 𝔪 := by
    rw [pow_one]
    haveI := B.complete
    exact le_trans (IsAdicComplete.le_jacobson_bot (adI B)) fun x hx => Ideal.mem_sInf.1 hx ⟨bot_le, hm⟩
  haveI : 𝔪.IsPrime := hm.isPrime
  have hp : (𝔪.map (Ideal.Quotient.mk (adI B ^ 1))).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have hs' : Ideal.Quotient.mk (adI B ^ 1) s ∉ 𝔪.map (Ideal.Quotient.mk (adI B ^ 1)) := by
    rwa [Ideal.mem_quotient_iff_mem hJ]
  letI := (qmap h 1).toAlgebra
  haveI := hL.away 1
  have h1 : ((𝔪.map (Ideal.Quotient.mk (adI B ^ 1))).map (qmap h 1)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers (Ideal.Quotient.mk (adI B ^ 1) s))
      (L.A ⧸ adI L ^ 1) _ hp ((Ideal.disjoint_powers_iff_notMem_of_isPrime _).2 hs')
  have h2 : ((𝔪.map (Ideal.Quotient.mk (adI B ^ 1))).map (qmap h 1)).map (qmap e 1) ≠ ⊤ := by
    intro htop
    apply h1.ne_top
    letI := (qmap e 1).toAlgebra
    haveI : Module.FaithfullyFlat (L.A ⧸ adI L ^ 1) (C.A ⧸ adI C ^ 1) := he
    rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := C.A ⧸ adI C ^ 1)
      ((𝔪.map (Ideal.Quotient.mk (adI B ^ 1))).map (qmap h 1))]
    change Ideal.comap (qmap e 1) (Ideal.map (qmap e 1) _) = ⊤
    rw [htop, Ideal.comap_top]
  intro htop
  apply h2
  rw [Ideal.map_map, Ideal.map_map]
  have : ((qmap e 1).comp (qmap h 1)).comp (Ideal.Quotient.mk (adI B ^ 1)) =
      (Ideal.Quotient.mk (adI C ^ 1)).comp (e.comp h).f := RingHom.ext fun _ => rfl
  rw [this, ← Ideal.map_map, htop, Ideal.map_top]

end GlobalTheory.BSP

namespace GlobalTheory.BSP

theorem map_ne_top_of_comp {l : ℕ} {R : Type} [CommRing R] {B Q C : Obj l R} (c : Hom B Q) (π : Hom Q C)
    (a : Hom B C) (hc : π.comp c = a) (𝔪 : Ideal B.A) (ha : 𝔪.map a.f ≠ ⊤) : 𝔪.map c.f ≠ ⊤ := by
  subst hc
  intro htop
  apply ha
  change Ideal.map (π.f.comp c.f) 𝔪 = ⊤
  rw [← Ideal.map_map, htop, Ideal.map_top]

theorem exists_cover_receiving_bk : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K)),
    ∃ (C : Obj l ↥(OL K)) (h : Hom B C), Nonempty (Hom bk.prism C) ∧ Cover h := by
  intro l _ K bk B
  obtain ⟨n, s, t, hspan, hst⟩ := GlobalTheory.T.invertible_ideal_principal_on_zariski_cover B.A B.I B.inv
  have hga : ∀ i, GenAway B (s i) (t i) := fun i => ⟨(hst i).1, fun x hx => by
    obtain ⟨c, hc⟩ := (hst i).2 x hx
    exact ⟨1, by rw [pow_one, hc]; exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)⟩⟩
  choose L h hL hLI using fun i => GlobalTheory.T.exists_isPrismLocalizationAway_of_generated l (↥(OL K)) B (s i) (t i) (hga i)
  have hfr : ∀ i, ∃ p, IsFrame bk (L i) ((h i).f (t i)) p := fun i => by
    obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective ((L i).str (bk.str.symm (Ideal.Quotient.mk _ X)))
    exact ⟨p, hLI i, hp⟩
  choose p hp using hfr
  have En : ∀ i, Env bk (L i) ((h i).f (t i)) (p i) := fun i => (GlobalTheory.T.nonempty_breuilKisinPrismCoproduct l K bk (L i) _ _ (hp i)).some
  obtain ⟨Q, π, hbij, -, huniv⟩ := GlobalTheory.T.exists_finite_product_oriented_boundedPrisms l (↥(OL K)) n (fun i => (En i).Q) fun i => ⟨_, (En i).I_eq⟩
  obtain ⟨c, hc⟩ := huniv B fun i => (En i).inl.comp (h i)
  obtain ⟨g, -⟩ := huniv bk.prism fun i => (En i).inr
  refine ⟨Q, c, ⟨g⟩, ?_⟩
  have hcov : ∀ i, Cover (En i).inl := fun i => GlobalTheory.T.isPrismCover_breuilKisinCoproduct_inl l K bk (L i) _ _ (hp i) (En i)
  have hstab : ∀ i, Stable ((π i).comp c) := fun i => by
    rw [hc i]
    exact GlobalTheory.T.isStablePrismHom_comp l _ B (L i) (En i).Q (h i) (En i).inl
      (GlobalTheory.T.isStablePrismHom_of_localizationAway l _ B (L i) (s i) (h i) ⟨t i, (hga i).1, (hga i).2⟩ (hL i)) (hcov i).stable
  refine GlobalTheory.T.isPrismCover_of_stable_maximal_map_ne_top l _ B Q c (GlobalTheory.T.isStablePrismHom_of_finite_product_components l _ n _ (fun i => ⟨_, (En i).I_eq⟩) Q π hbij B c hstab) ?_
  intro 𝔪 hm
  obtain ⟨i, hi⟩ : ∃ i, s i ∉ 𝔪 := by
    by_contra hall
    push_neg at hall
    exact hm.ne_top (eq_top_iff.2 (hspan ▸ Ideal.span_le.2 (Set.range_subset_iff.2 hall)))
  exact map_ne_top_of_comp c (π i) _ (hc i) 𝔪
    (map_ne_top_of_isLoc_ff (s i) (h i) (hL i) (En i).inl ((hcov i).ff 1) 𝔪 hm hi)

end GlobalTheory.BSP
end
end
