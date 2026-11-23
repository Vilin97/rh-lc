module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdicTopologicalBasisBasisModPowStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismHomMapIdealEqStatement
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
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemNonZeroDivisorsOfInvertibleSpanSingleton
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyBreuilKisinPrismCoproductStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismHomMapIdealEqStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrismCoproductFaithfullyFlatModAdicPo

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.EnvFF

theorem adI_map {l : ℕ} [Fact l.Prime] {R : Type} [CommRing R] {B B' : Obj l R} (f : Hom B B') (m : ℕ) :
    (adI B ^ m).map f.f = adI B' ^ m := by
  rw [Ideal.map_pow, adI, adI, Ideal.map_sup, Ideal.map_span, Set.image_singleton, map_natCast,
    GlobalTheory.T.prism_hom_map_ideal_eq l R B B' f]

theorem ff_of_basis {R S : Type} [CommRing R] [CommRing S] (g : R →+* S) (ι : Type) [Nonempty ι]
    (h : letI := g.toAlgebra; Nonempty (Module.Basis ι R S)) : g.FaithfullyFlat := by
  letI := g.toAlgebra
  obtain ⟨b⟩ := h
  exact Module.FaithfullyFlat.of_linearEquiv _ _ b.repr

end GlobalTheory.BSP.EnvFF

open GlobalTheory.BSP.EnvFF

theorem GlobalTheory.BSP.envFF : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K)) (t p : B.A)
    (En : Env bk B t p) (m : ℕ), (qmap En.inl m).FaithfullyFlat := by
  intro l _ K bk B t p En m
  have hJ : (adI B ^ m).map En.inl.f = adI En.Q ^ m := adI_map En.inl m
  have e : qmap En.inl m = (Ideal.quotEquivOfEq hJ).toRingHom.comp
      (Ideal.quotientMap ((adI B ^ m).map En.inl.f) En.inl.f Ideal.le_comap_map) := by
    refine Ideal.Quotient.ringHom_ext (RingHom.ext fun a => ?_)
    rfl
  have h2 : (Ideal.quotEquivOfEq hJ).toRingHom.FaithfullyFlat :=
    RingHom.FaithfullyFlat.of_bijective (Ideal.quotEquivOfEq hJ).bijective
  have h1 : (Ideal.quotientMap ((adI B ^ m).map En.inl.f) En.inl.f Ideal.le_comap_map).FaithfullyFlat := by
    haveI : Nonempty (Digits l) := ⟨⟨0, fun _ => (Fact.out : l.Prime).pos⟩⟩
    obtain ⟨b, -⟩ := GlobalTheory.T.adicTopologicalBasis_basis_mod_pow B.A En.Q.A En.inl.f (adI B) (Digits l) En.tb m
    exact ff_of_basis _ (Digits l) ⟨b⟩
  rw [e]
  exact RingHom.FaithfullyFlat.stableUnderComposition _ _ h1 h2
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrismCoproductFaithfullyFlatModAdicPoStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.breuilKisinPrismCoproduct_faithfullyFlat_mod_adic_pow : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K)) (t p : B.A) (En : Env bk B t p) (m : ℕ), (qmap En.inl m).FaithfullyFlat := by
  first | exact @GlobalTheory.BSP.envFF | exact GlobalTheory.BSP.envFF | (intros; apply GlobalTheory.BSP.envFF <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrismCoproductIsPushoutBaseChange

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem isPushout_of_bases {R S R' S' : Type} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    (f : R →+* S) (g : R →+* R') (g' : S →+* S') (f' : R' →+* S') (hc : g'.comp f = f'.comp g) {ι : Type} :
    letI := f.toAlgebra; letI := f'.toAlgebra
    ∀ (b : Module.Basis ι R S) (b' : Module.Basis ι R' S'), (∀ i, g' (b i) = b' i) →
      CategoryTheory.IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom g) (CommRingCat.ofHom g')
        (CommRingCat.ofHom f') := by
  letI := f.toAlgebra; letI := g.toAlgebra; letI := g'.toAlgebra; letI := f'.toAlgebra
  letI : Algebra R S' := (f'.comp g).toAlgebra
  intro b b' hb
  haveI : IsScalarTower R R' S' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower R S S' := IsScalarTower.of_algebraMap_eq fun x => (RingHom.congr_fun hc x).symm
  have hbc : IsBaseChange R' (IsScalarTower.toAlgHom R S S').toLinearMap := by
    refine IsBaseChange.of_equiv ((Algebra.TensorProduct.basis R' b).equiv b' (Equiv.refl _)) fun m => ?_
    have : (((Algebra.TensorProduct.basis R' b).equiv b' (Equiv.refl _)).toLinearMap.restrictScalars R ∘ₗ
        TensorProduct.mk R R' S 1) = (IsScalarTower.toAlgHom R S S').toLinearMap := b.ext fun i => by
      simp only [LinearMap.coe_comp, Function.comp_apply, TensorProduct.mk_apply,
        LinearMap.coe_restrictScalars, LinearEquiv.coe_coe, AlgHom.toLinearMap_apply,
        IsScalarTower.coe_toAlgHom']
      rw [← Algebra.TensorProduct.basis_apply, Module.Basis.equiv_apply, Equiv.refl_apply]
      exact (hb i).symm
    exact LinearMap.congr_fun this m
  haveI : Algebra.IsPushout R R' S S' := ⟨hbc⟩
  haveI : Algebra.IsPushout R S R' S' := Algebra.IsPushout.symm inferInstance
  exact CommRingCat.isPushout_of_isPushout R S R' S'

end GlobalTheory.BSP

namespace GlobalTheory.BSP

theorem exists_basis_quot_of_map_eq {S A : Type} [CommRing S] [CommRing A] (s : S →+* A) (I : Ideal S) (J : Ideal A)
    (hJ : I.map s = J) (hle : I ≤ J.comap s) {ι : Type} (b₀ : ι → A)
    (h : letI := (Ideal.quotientMap (I.map s) s Ideal.le_comap_map).toAlgebra
      ∃ b : Module.Basis ι (S ⧸ I) (A ⧸ I.map s), ∀ i, b i = Ideal.Quotient.mk _ (b₀ i)) :
    letI := (Ideal.quotientMap J s hle).toAlgebra
    ∃ b : Module.Basis ι (S ⧸ I) (A ⧸ J), ∀ i, b i = Ideal.Quotient.mk _ (b₀ i) := by
  subst hJ
  exact h

theorem map_adI_pow {R : Type} [CommRing R] {l : ℕ} {B B' : Obj l R} (f : Hom B B') (hI : B.I.map f.f = B'.I)
    (m : ℕ) : (adI B ^ m).map f.f = adI B' ^ m := by
  rw [Ideal.map_pow, adI, adI, Ideal.map_sup, Ideal.map_span, Set.image_singleton, map_natCast, hI]

end GlobalTheory.BSP

namespace GlobalTheory.BSP

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l}

theorem env_map_tb_b {bk : BK K} {B B' : Obj l ↥(OL K)} {t p : B.A} {k : Hom B B'} {En : Env bk B t p}
    {En' : Env bk B' (k.f t) (k.f p)} (k' : Hom En.Q En'.Q) (h1 : k'.comp En.inl = En'.inl.comp k)
    (h2 : k'.comp En.inr = En'.inr) (α : Digits l) : k'.f (En.tb.b α) = En'.tb.b α := by
  have hreg : En'.inl.f (k.f t) ∈ nonZeroDivisors En'.Q.A :=
    by
    haveI := En'.Q.inv
    exact mem_nonZeroDivisors_of_invertible_span_singleton _ _ (Module.Invertible.congr (LinearEquiv.ofEq _ _ En'.I_eq))
  have e1 : ∀ a, k'.f (En.inl.f a) = En'.inl.f (k.f a) := fun a => by
    have := congrArg (fun h => Hom.f h a) h1
    exact this
  have e2 : k'.f (BK.hf En.inr X) = BK.hf En'.inr X := by
    have := congrArg (fun h => Hom.f h X) h2
    exact this
  have hw : k'.f En.w = En'.w := by
    have a1 := congrArg k'.f En.w_eq
    have a2 := En'.w_eq
    have a3 : k'.f (En.inl.f p + En.inl.f t * En.w) = En'.inl.f (k.f p) + En'.inl.f (k.f t) * k'.f En.w := by
      simp only [map_add (f := _), map_mul, e1]
    have : En'.inl.f (k.f t) * (k'.f En.w - En'.w) = 0 := by linear_combination -a3 - a1 + e2 + a2
    exact sub_eq_zero.1 ((mem_nonZeroDivisors_iff.1 hreg).2 _ (by rw [mul_comm]; exact this))
  have hδ : ∀ i : ℕ, k'.f (En.Q.D.δ^[i] En.w) = En'.Q.D.δ^[i] En'.w := fun i =>
    (Function.Semiconj.iterate_right (f := k'.f) k'.f_δ i En.w).trans (congrArg (En'.Q.D.δ^[i]) hw)
  calc k'.f (En.tb.b α) = k'.f (α.1.prod fun i n => (En.Q.D.δ^[i] En.w) ^ n) := congrArg k'.f (En.tb_b α)
    _ = α.1.prod fun i n => k'.f ((En.Q.D.δ^[i] En.w) ^ n) := map_finsuppProd k'.f _ _
    _ = α.1.prod fun i n => (En'.Q.D.δ^[i] En'.w) ^ n :=
      Finsupp.prod_congr fun i _ => (map_pow _ _ _).trans (congrArg (· ^ α.1 i) (hδ i))
    _ = En'.tb.b α := (En'.tb_b α).symm

end GlobalTheory.BSP

namespace GlobalTheory.BSP

theorem env_isPO : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B B' : Obj l ↥(OL K)) (t p : B.A)
    (k : Hom B B') (En : Env bk B t p) (En' : Env bk B' (k.f t) (k.f p)),
    ∃ k' : Hom En.Q En'.Q, IsPO En.inl k k' En'.inl := by
  intro l _ K bk B B' t p k En En'
  obtain ⟨k', ⟨h1, h2⟩, -⟩ := En.univ En'.Q (En'.inl.comp k) En'.inr
  have e1 : ∀ a, k'.f (En.inl.f a) = En'.inl.f (k.f a) := fun a => by
    have := congrArg (fun h => Hom.f h a) h1
    exact this
  refine ⟨k', ⟨h1, fun m => ?_⟩⟩
  have q1 := map_adI_pow En.inl (GlobalTheory.T.prism_hom_map_ideal_eq l _ B En.Q En.inl) m
  have q2 := GlobalTheory.T.adicTopologicalBasis_basis_mod_pow B.A En.Q.A En.inl.f (adI B) (Digits l) En.tb m
  have q3 := exists_basis_quot_of_map_eq En.inl.f (adI B ^ m) (adI En.Q ^ m) q1 (adI_pow_le En.inl m) En.tb.b q2
  obtain ⟨b, hb⟩ := q3
  have r1 := map_adI_pow En'.inl (GlobalTheory.T.prism_hom_map_ideal_eq l _ B' En'.Q En'.inl) m
  have r2 := GlobalTheory.T.adicTopologicalBasis_basis_mod_pow B'.A En'.Q.A En'.inl.f (adI B') (Digits l) En'.tb m
  have r3 := exists_basis_quot_of_map_eq En'.inl.f (adI B' ^ m) (adI En'.Q ^ m) r1 (adI_pow_le En'.inl m) En'.tb.b r2
  obtain ⟨b', hb'⟩ := r3
  refine isPushout_of_bases (qmap En.inl m) (qmap k m) (qmap k' m) (qmap En'.inl m) ?_ b b' fun α => ?_
  · refine Ideal.Quotient.ringHom_ext (RingHom.ext fun a => ?_)
    exact congrArg (Ideal.Quotient.mk (adI En'.Q ^ m)) (e1 a)
  · exact (congrArg (qmap k' m) (hb α)).trans ((qmap_mk k' m _).trans
      ((congrArg (Ideal.Quotient.mk (adI En'.Q ^ m)) (env_map_tb_b k' h1 h2 α)).trans (hb' α).symm))

end GlobalTheory.BSP
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrismCoproductIsPushoutBaseChangeStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.breuilKisinPrismCoproduct_isPushout_base_change : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B B' : Obj l ↥(OL K)) (t p : B.A) (k : Hom B B') (En : Env bk B t p) (En' : Env bk B' (k.f t) (k.f p)), ∃ k' : Hom En.Q En'.Q, IsPO En.inl k k' En'.inl := by
  first | exact @GlobalTheory.BSP.env_isPO | exact GlobalTheory.BSP.env_isPO | (intros; apply GlobalTheory.BSP.env_isPO <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPrismCoverBreuilKisinCoproductInl

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem isFrame_map {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {B B' : Obj l ↥(OL K)} {t p : B.A}
    (h : IsFrame bk B t p) (k : Hom B B') : IsFrame bk B' (k.f t) (k.f p) := by
  refine ⟨?_, k.f_str _ p h.2⟩
  rw [← GlobalTheory.T.prism_hom_map_ideal_eq l _ B B' k, h.1, Ideal.map_span, Set.image_singleton]

theorem env_inl_cover : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K)) (t p : B.A),
    IsFrame bk B t p → ∀ En : Env bk B t p, Cover En.inl := by
  intro l _ K bk B t p hF En
  refine ⟨⟨fun m => (GlobalTheory.T.breuilKisinPrismCoproduct_faithfullyFlat_mod_adic_pow l K bk B t p En m).flat, fun B' k => ?_⟩, GlobalTheory.T.breuilKisinPrismCoproduct_faithfullyFlat_mod_adic_pow l K bk B t p En⟩
  obtain ⟨En'⟩ := GlobalTheory.T.nonempty_breuilKisinPrismCoproduct l K bk B' (k.f t) (k.f p) (isFrame_map hF k)
  obtain ⟨k', hk'⟩ := GlobalTheory.T.breuilKisinPrismCoproduct_isPushout_base_change l K bk B B' t p k En En'
  exact ⟨En'.Q, k', En'.inl, hk'⟩

end GlobalTheory.BSP
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPrismCoverBreuilKisinCoproductInlStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.isPrismCover_breuilKisinCoproduct_inl : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K)) (t p : B.A), IsFrame bk B t p → ∀ En : Env bk B t p, Cover En.inl := by
  first | exact @GlobalTheory.BSP.env_inl_cover | exact GlobalTheory.BSP.env_inl_cover | (intros; apply GlobalTheory.BSP.env_inl_cover <;> assumption)
end
end
