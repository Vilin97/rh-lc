module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRangeOfBaseChangeRatioSectionsStatement
import Mathlib.Tactic.Basify
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGenFlat

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericPointFactorOfInjectiveBaseMap

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_fractionRing_map_comp_eq {R W B : Type} [CommRing R] [IsDomain R] [CommRing W] [IsDomain W] [CommRing B]
    (φ : R →+* W) (hφ : Function.Injective φ) (c : R →+* B) (a : B →+* FractionRing R) (b : B →+* FractionRing W)
    (ha : Function.Injective a) (hac : a.comp c = algebraMap R (FractionRing R))
    (hbc : b.comp c = (algebraMap W (FractionRing W)).comp φ) :
    ∃ ψ : FractionRing R →+* FractionRing W,
      ψ.comp (algebraMap R (FractionRing R)) = (algebraMap W (FractionRing W)).comp φ ∧ ψ.comp a = b := by
  have hinj : Function.Injective ((algebraMap W (FractionRing W)).comp φ) :=
    (IsFractionRing.injective W (FractionRing W)).comp hφ
  refine ⟨IsFractionRing.lift hinj, ?_, ?_⟩
  · ext r
    simp only [RingHom.comp_apply, IsFractionRing.lift_algebraMap]
  · ext x
    obtain ⟨r, r', hr', h⟩ := IsFractionRing.div_surjective (A := R) (a x)
    have h0 : algebraMap R (FractionRing R) r' ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hr'
    have hac' : ∀ y, a (c y) = algebraMap R (FractionRing R) y := fun y => RingHom.congr_fun hac y
    have hbc' : ∀ y, b (c y) = ((algebraMap W (FractionRing W)).comp φ) y := fun y => RingHom.congr_fun hbc y
    have h1 : x * c r' = c r := by
      apply ha
      rw [map_mul, hac', hac', ← h, div_mul_cancel₀ _ h0]
    have h2 : ((algebraMap W (FractionRing W)).comp φ) r' ≠ 0 := by
      intro h3
      exact nonZeroDivisors.ne_zero hr' (hinj (h3.trans (map_zero _).symm))
    rw [RingHom.comp_apply, ← h, map_div₀, IsFractionRing.lift_algebraMap, IsFractionRing.lift_algebraMap,
      div_eq_iff h2, ← hbc', ← hbc', ← map_mul, h1]

theorem Modif.exists_generic_factor : ∀ (R : Type) [CommRing R] [IsDomain R] (M : Modif R) (W : Type) [CommRing W] [IsDomain W] (φ : R →+* W), Function.Injective φ → ∀ ξ : Sp W ⟶ M.S, ξ ≫ M.π = spMap φ → ∃ ψ : FractionRing R →+* FractionRing W, ψ.comp (algebraMap R (FractionRing R)) = (algebraMap W (FractionRing W)).comp φ ∧ spMap ψ ≫ M.gp = jK W ≫ ξ := by
  intro R _ _ M W _ _ φ hφ ξ hξ
  haveI := M.integral
  haveI := M.dominant
  let s : M.S := (jK W ≫ ξ) (IsLocalRing.closedPoint (FractionRing W))
  obtain ⟨B, f, hf, hs, -⟩ := M.S.exists_affine_mem_range_and_range_subset (x := s) (U := ⊤) trivial
  have hb : Set.range (jK W ≫ ξ) ⊆ Set.range f := by
    rintro _ ⟨y, rfl⟩
    have : y = IsLocalRing.closedPoint (FractionRing W) := Subsingleton.elim (α := PrimeSpectrum (FractionRing W)) _ _
    rw [this]; exact hs
  have ha : Set.range M.gp ⊆ Set.range f := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨z, hz⟩ := M.gp.denseRange.exists_mem_open f.isOpenEmbedding.isOpen_range ⟨s, hs⟩
    have : y = z := Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) _ _
    rw [this]; exact hz
  obtain ⟨a, ha'⟩ := Spec.map_surjective (IsOpenImmersion.lift f M.gp ha)
  obtain ⟨b, hb'⟩ := Spec.map_surjective (IsOpenImmersion.lift f (jK W ≫ ξ) hb)
  obtain ⟨c, hc'⟩ := Spec.map_surjective (f ≫ M.π)
  have e1 : Spec.map a ≫ f = M.gp := by rw [ha', IsOpenImmersion.lift_fac]
  have e2 : Spec.map b ≫ f = jK W ≫ ξ := by rw [hb', IsOpenImmersion.lift_fac]
  have hac : c ≫ a = CommRingCat.ofHom (algebraMap R (FractionRing R)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hc', ← Category.assoc, e1, M.gp_π]
  have hbc : c ≫ b = CommRingCat.ofHom φ ≫ CommRingCat.ofHom (algebraMap W (FractionRing W)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hc', ← Category.assoc, e2, Category.assoc, hξ, Spec.map_comp]
  have hred : IsReduced (Spec B) := isReduced_of_isOpenImmersion f
  have hred' : _root_.IsReduced B := (affine_isReduced_iff B).1 hred
  have hdom : IsDominant (Spec.map a) := by
    haveI : IsDominant (Spec.map a ≫ f) := e1 ▸ M.dominant
    exact IsDominant.of_comp_of_isOpenImmersion _ f
  have hainj : Function.Injective a.hom := by
    have := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical a.hom).1 hdom.1
    rw [nilradical_eq_zero] at this
    exact (RingHom.injective_iff_ker_eq_bot _).2 (le_bot_iff.1 this)
  obtain ⟨ψ, h1, h2⟩ := exists_fractionRing_map_comp_eq φ hφ c.hom a.hom b.hom hainj
    (congrArg CommRingCat.Hom.hom hac) (congrArg CommRingCat.Hom.hom hbc)
  refine ⟨ψ, h1, ?_⟩
  have h3 : a ≫ CommRingCat.ofHom ψ = b := by
    ext1; exact h2
  rw [← e1, ← e2, ← h3, Spec.map_comp, Category.assoc]

end GlobalTheory.Mum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericPointFactorOfInjectiveBaseMapStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_genericPoint_factor_of_injective_base_map : ∀ (R : Type) [CommRing R] [IsDomain R] (M : Modif R) (W : Type) [CommRing W] [IsDomain W] (φ : R →+* W), Function.Injective φ → ∀ ξ : Sp W ⟶ M.S, ξ ≫ M.π = spMap φ → ∃ ψ : FractionRing R →+* FractionRing W, ψ.comp (algebraMap R (FractionRing R)) = (algebraMap W (FractionRing W)).comp φ ∧ spMap ψ ≫ M.gp = jK W ≫ ξ := by
  first | exact @GlobalTheory.Mum.Modif.exists_generic_factor | exact GlobalTheory.Mum.Modif.exists_generic_factor | (intros; apply GlobalTheory.Mum.Modif.exists_generic_factor <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecKRatioTraitDescendsToFractionField

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.RatioDesc

open ReciprocityTheory.ChartRestriction.G.DVR.TG

theorem pull_fst_app_injective {K L : Type} [Field K] [Field L] (ψ : K →+* L) {X : Scheme.{0}} (h : X ⟶ Sp K)
    (U : X.Opens) : Function.Injective ((pullback.fst h (spMap ψ)).app U).hom := by
  have : Flat (spMap ψ) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    letI := ψ.toAlgebra
    exact (RingHom.flat_algebraMap_iff).2 inferInstance
  have : Surjective (spMap ψ) := by
    constructor
    intro x
    exact ⟨IsLocalRing.closedPoint L, Subsingleton.elim _ _⟩
  exact app_injective_of_flat_surj _ U

variable {A : Type} [CommRing A] {X Y Z : Scheme.{0}}

theorem scal_mul' (p : Y ⟶ Sp A) (a b : A) : scal p (a * b) = scal p a * scal p b := by
  unfold scal; rw [map_mul, map_mul]

theorem scal_one' (p : Y ⟶ Sp A) : scal p 1 = 1 := by
  unfold scal; rw [map_one, map_one]

theorem scal_comp' (f : Z ⟶ Y) (p : Y ⟶ Sp A) (r : A) : scal (f ≫ p) r = f.appTop.hom (scal p r) := by
  unfold scal; rw [Scheme.Hom.comp_appTop]; rfl

theorem scal_spMap {B : Type} [CommRing B] (g : Y ⟶ Sp B) (ψ : A →+* B) (r : A) :
    scal (g ≫ Spec.map (CommRingCat.ofHom ψ)) r = scal g (ψ r) := by
  rw [scal_comp']
  unfold scal
  congr 1
  have := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ψ)
  exact (congrArg (fun f => f.hom r) this).symm

theorem gs_top' (f : Z ⟶ Y) (z : Z) (a : Γ(Y, ⊤)) : gs f z ⊤ a = gs (𝟙 Z) z ⊤ (f.appTop.hom a) := by
  have := gs_pull (𝟙 Z) f z ⊤ trivial a
  rw [Category.id_comp] at this
  exact this.symm

theorem gs_zero'' (f : Z ⟶ Y) (z : Z) (U : Y.Opens) : gs f z U 0 = 0 := by
  unfold gs; split_ifs <;> simp

abbrev sg (g : Z ⟶ Sp A) (z : Z) (a : A) : Z.presheaf.stalk z := gs (𝟙 Z) z ⊤ (scal g a)

theorem sg_mul (g : Z ⟶ Sp A) (z : Z) (a b : A) : sg g z (a * b) = sg g z a * sg g z b := by
  unfold sg; rw [scal_mul', gs_mul _ z ⊤ trivial]

theorem sg_one (g : Z ⟶ Sp A) (z : Z) : sg g z 1 = 1 := by
  unfold sg; rw [scal_one', gs_eq _ z ⊤ trivial, map_one, map_one]

theorem sg_isUnit {F : Type} [Field F] (g : Z ⟶ Sp F) (z : Z) {a : F} (ha : a ≠ 0) : IsUnit (sg g z a) :=
  have h1 : sg g z a * sg g z a⁻¹ = 1 := by rw [← sg_mul, mul_inv_cancel₀ ha, sg_one]
  ⟨⟨_, _, h1, by rw [mul_comm]; exact h1⟩, rfl⟩

end GlobalTheory.Mum.RatioDesc

namespace GlobalTheory.Mum

open GlobalTheory.Mum.RatioDesc

theorem secK_ratio_descends : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ) (s₁ s₂ : SecK C.P.L.L C.α k) (c d : W), c ≠ 0 → d ≠ 0 → (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ (z : Z) (J : (Z ⟶ C.G.left) → C.P.L.L.ι), Good C.P.L.L z J → gs p z ⊤ (scal T.G.hom c) * sval s₁ p' z J = gs p z ⊤ (scal T.G.hom d) * sval s₂ p' z J) → ∃ r t : R, r ≠ 0 ∧ t ≠ 0 ∧ ∀ (Z : Scheme.{0}) (p' : Z ⟶ C.A.A.left) (z : Z) (J : (Z ⟶ C.G.left) → C.P.L.L.ι), Good C.P.L.L z J → gs p' z ⊤ (scal C.A.A.hom (algebraMap R (FractionRing R) t)) * sval s₁ p' z J = gs p' z ⊤ (scal C.A.A.hom (algebraMap R (FractionRing R) r)) * sval s₂ p' z J := by
  intro R _ _ _ _ D C W _ _ _ T k s₁ s₂ c d hc hd H
  obtain ⟨ψ, hψR, hψ⟩ := GlobalTheory.T.exists_genericPoint_factor_of_injective_base_map R C.toModif W T.φ T.inj T.ξ T.ξ_π
  let Y : Scheme.{0} := pullback C.A.A.hom (spMap ψ)
  let q : Y ⟶ C.A.A.left := pullback.fst C.A.A.hom (spMap ψ)
  let g : Y ⟶ Sp (FractionRing W) := pullback.snd C.A.A.hom (spMap ψ)
  have hw : (q ≫ C.α) ≫ C.G.hom = (g ≫ jK W) ≫ T.ξ := by
    simp only [Category.assoc]
    rw [C.α_cart.1.w, ← Category.assoc q, pullback.condition, Category.assoc]
    exact congrArg (g ≫ ·) hψ
  let p := T.cart.1.lift (q ≫ C.α) (g ≫ jK W) hw
  have hp : p ≫ T.β = q ≫ C.α := T.cart.1.lift_fst _ _ _
  have hpG : p ≫ T.G.hom = g ≫ jK W := T.cart.1.lift_snd _ _ _
  have hsc : ∀ (y : Y) (w : W),
      gs p y ⊤ (scal T.G.hom w) = sg g y (algebraMap W (FractionRing W) w) := by
    intro y w
    rw [gs_top', ← scal_comp', hpG, scal_spMap]

  set c' := algebraMap W (FractionRing W) c with hc'
  set d' := algebraMap W (FractionRing W) d with hd'
  have hc0 : c' ≠ 0 := fun h => hc (IsFractionRing.injective W (FractionRing W) (h.trans (map_zero _).symm))
  have hd0 : d' ≠ 0 := fun h => hd (IsFractionRing.injective W (FractionRing W) (h.trans (map_zero _).symm))
  let Uc : (Fin 1 → C.P.L.L.ι) → C.A.A.left.Opens := fun j => LB.wchart C.P.L.L (fun _ : Fin 1 => C.α) j
  have G0 : ∀ (j : Fin 1 → C.P.L.L.ι) (y : Y), q y ∈ Uc j →
      sg g y c' * gs q y (Uc j) (s₁.f j) = sg g y d' * gs q y (Uc j) (s₂.f j) := by
    intro j y hy
    obtain ⟨J, hJ, hJj⟩ := exists_good C.P.L.L C.P.L.isLB y (fun _ : Unit => q ≫ C.α) (fun _ => j 0)
      (fun _ _ _ => rfl) (fun _ => by simpa using Set.mem_iInter.1 hy 0)
    have e := H Y p q hp y J hJ
    have hj : ∀ i : Fin 1, J (q ≫ C.α) = j i := fun i => by rw [Subsingleton.elim i 0]; exact hJj ()
    rw [hsc, hsc, sval_of s₁ q y J j hj, sval_of s₂ q y J j hj] at e
    exact e

  have key : ∃ m₀ : FractionRing R, m₀ ≠ 0 ∧ ∀ (j : Fin 1 → C.P.L.L.ι) (y : Y), q y ∈ Uc j →
      gs q y (Uc j) (s₁.f j) = sg g y (ψ m₀) * gs q y (Uc j) (s₂.f j) := by
    by_cases h0 : ∀ j, s₂.f j = 0
    · refine ⟨1, one_ne_zero, fun j y hy => ?_⟩
      have e := G0 j y hy
      have hz : gs q y (Uc j) (s₂.f j) = 0 := by rw [h0 j]; exact gs_zero'' _ _ _
      rw [hz, mul_zero] at e
      rw [hz, mul_zero]
      exact (sg_isUnit g y hc0).mul_left_cancel (e.trans (mul_zero _).symm)
    · push Not at h0
      obtain ⟨j₀, hj₀⟩ := h0
      have e : ((q.app (Uc j₀)).hom (s₁.f j₀)) = (q.app (Uc j₀)).hom (s₂.f j₀) * resTop _ (scal g (d' / c')) := by
        apply fn_ext
        intro y hy
        have hy' : q ((𝟙 Y) y) ∈ Uc j₀ := by simpa using hy
        have e1 := gs_pull (𝟙 Y) q y (Uc j₀) hy' (s₁.f j₀)
        have e2 := gs_pull (𝟙 Y) q y (Uc j₀) hy' (s₂.f j₀)
        rw [Category.id_comp] at e1 e2
        rw [gs_mul _ y _ hy, gs_res _ y le_top hy]
        erw [e1, e2]
        apply (sg_isUnit g y hc0).mul_left_cancel
        have hcd : c' * (d' / c') = d' := by field_simp
        rw [G0 j₀ y hy]
        change _ = sg g y c' * (_ * sg g y (d' / c'))
        rw [mul_comm _ (sg g y (d' / c')), ← _root_.mul_assoc, ← sg_mul, hcd]
      obtain ⟨m₀, hm₀⟩ := GlobalTheory.T.mem_range_of_base_change_ratio_sections ψ C.A.A.hom (Uc j₀) (s₁.f j₀) (s₂.f j₀) (d' / c') hj₀ e
      refine ⟨m₀, fun h => ?_, fun j y hy => ?_⟩
      · rw [h, map_zero] at hm₀
        exact div_ne_zero hd0 hc0 hm₀.symm
      · apply (sg_isUnit g y hc0).mul_left_cancel
        have hcd : c' * (d' / c') = d' := by field_simp
        rw [G0 j y hy, hm₀, ← _root_.mul_assoc, ← sg_mul, hcd]

  obtain ⟨m₀, hm0, hm⟩ := key
  obtain ⟨r, t, ht, hrt⟩ := IsFractionRing.div_surjective (A := R) m₀
  have ht0 : t ≠ 0 := nonZeroDivisors.ne_zero ht
  have ht' : algebraMap R (FractionRing R) t ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ht
  have hr0 : r ≠ 0 := by
    rintro rfl
    apply hm0
    rw [← hrt, map_zero, zero_div]
  refine ⟨r, t, hr0, ht0, ?_⟩
  have hK : algebraMap R (FractionRing R) t * m₀ = algebraMap R (FractionRing R) r := by
    rw [← hrt]; field_simp
  let F₁ : ∀ j, Γ(C.A.A.left, Uc j) := fun j => s₁.f j
  let F₂ : ∀ j, Γ(C.A.A.left, Uc j) := fun j => s₂.f j
  have sec : ∀ j : Fin 1 → C.P.L.L.ι, resTop (Uc j) (scal C.A.A.hom (algebraMap R (FractionRing R) t)) * F₁ j =
      resTop (Uc j) (scal C.A.A.hom (algebraMap R (FractionRing R) r)) * F₂ j := by
    intro j
    apply pull_fst_app_injective ψ C.A.A.hom (Uc j)
    apply fn_ext
    intro y hy
    have hy' : q ((𝟙 Y) y) ∈ Uc j := by simpa using hy
    have e1 := gs_pull (𝟙 Y) q y (Uc j) hy' (resTop (Uc j) (scal C.A.A.hom (algebraMap R (FractionRing R) t)) * F₁ j)
    have e2 := gs_pull (𝟙 Y) q y (Uc j) hy' (resTop (Uc j) (scal C.A.A.hom (algebraMap R (FractionRing R) r)) * F₂ j)
    rw [Category.id_comp] at e1 e2
    erw [e1, e2]
    rw [gs_mul q y _ hy, gs_mul q y _ hy, gs_res q y le_top hy, gs_res q y le_top hy, gs_top' q, gs_top' q,
      ← scal_comp', ← scal_comp', pullback.condition, scal_spMap, scal_spMap]
    change sg g y _ * _ = sg g y _ * _
    rw [hm j y hy, ← _root_.mul_assoc, ← sg_mul, ← map_mul, hK]
  intro Z p' z J hJ
  have hm' : p' z ∈ Uc (fun _ => J (p' ≫ C.α)) := hJ.mem (fun _ : Fin 1 => C.α) p'
  have e := congrArg (gs p' z (Uc (fun _ => J (p' ≫ C.α)))) (sec (fun _ => J (p' ≫ C.α)))
  rw [gs_mul p' z _ hm', gs_mul p' z _ hm', gs_res p' z le_top hm', gs_res p' z le_top hm'] at e
  exact e

end GlobalTheory.Mum
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecKRatioTraitDescendsToFractionFieldStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.secK_ratio_trait_descends_to_fractionField : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ) (s₁ s₂ : SecK C.P.L.L C.α k) (c d : W), c ≠ 0 → d ≠ 0 → (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ (z : Z) (J : (Z ⟶ C.G.left) → C.P.L.L.ι), Good C.P.L.L z J → gs p z ⊤ (scal T.G.hom c) * sval s₁ p' z J = gs p z ⊤ (scal T.G.hom d) * sval s₂ p' z J) → ∃ r t : R, r ≠ 0 ∧ t ≠ 0 ∧ ∀ (Z : Scheme.{0}) (p' : Z ⟶ C.A.A.left) (z : Z) (J : (Z ⟶ C.G.left) → C.P.L.L.ι), Good C.P.L.L z J → gs p' z ⊤ (scal C.A.A.hom (algebraMap R (FractionRing R) t)) * sval s₁ p' z J = gs p' z ⊤ (scal C.A.A.hom (algebraMap R (FractionRing R) r)) * sval s₂ p' z J := by
  first | exact @GlobalTheory.Mum.secK_ratio_descends | exact GlobalTheory.Mum.secK_ratio_descends | (intros; apply GlobalTheory.Mum.secK_ratio_descends <;> assumption)
end
end
