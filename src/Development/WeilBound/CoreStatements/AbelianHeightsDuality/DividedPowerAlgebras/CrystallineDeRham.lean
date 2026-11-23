module

public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.CompF
public import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.AcycOfCoprod
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.IsNilpotentOfIsNilDP
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.TagIso

-- Source module: Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.ExistsFilEqBot

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace FubiniStudyChowHeightFormula₂.Adr

variable {R B C : Type} [CommRing R] [CommRing B] [CommRing C] {I : Ideal R} {J J' : Ideal B} {L : Ideal C}

theorem Sup.one_mem_fil (δ : DividedPowers J) : (1 : B) ∈ fil δ 0 :=
  Ideal.subset_span ⟨[], by simp, by simp, by simp⟩

theorem Sup.dpow_mem_fil (δ : DividedPowers J) {x : B} (hx : x ∈ J) (n : ℕ) : δ.dpow n x ∈ fil δ n :=
  Ideal.subset_span ⟨[(n, x)], by simpa using hx, by simp, by simp⟩

theorem Sup.fil_mul_le (δ : DividedPowers J) (m n : ℕ) : fil δ m * fil δ n ≤ fil δ (m + n) := by
  rw [fil, fil, Ideal.span_mul_span', Ideal.span_le]
  rintro _ ⟨_, ⟨l, h1, h2, rfl⟩, _, ⟨l', h1', h2', rfl⟩, rfl⟩
  refine Ideal.subset_span ⟨l ++ l', fun p hp ↦ ?_, ?_, by simp⟩
  · rcases List.mem_append.1 hp with h | h
    exacts [h1 p h, h1' p h]
  · simp only [List.map_append, List.sum_append]; omega

theorem Sup.exists_fil_eq_bot {δ : DividedPowers J} (h : IsNilDP δ) : ∃ N, ∀ n, N ≤ n → fil δ n = ⊥ := by
  obtain ⟨N, h⟩ := h
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [fil, Ideal.span_eq_bot]
  rintro _ ⟨l, h1, h2, rfl⟩
  exact h l h1 (hn.trans h2)

theorem Sup.isPDNilpotent_of_family (δ : DividedPowers J) (s : Set B) (hs : J = Ideal.span s) (F : ℕ → Ideal B)
    (h0 : (1 : B) ∈ F 0) (hm : ∀ m n, F m * F n ≤ F (m + n)) (hg : ∀ x ∈ s, ∀ n, δ.dpow n x ∈ F n)
    (N : ℕ) (hN : ∀ n, N ≤ n → F n = ⊥) : IsNilDP δ := by
  subst hs
  have hdp : ∀ y ∈ Ideal.span s, ∀ n, δ.dpow n y ∈ F n := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx => exact hg x hx
    | zero =>
      intro n
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · rw [δ.dpow_zero (Ideal.zero_mem _)]; exact h0
      · rw [δ.dpow_eval_zero hn.ne']
        exact Ideal.zero_mem _
    | add x y hx hy ihx ihy =>
      intro n
      rw [δ.dpow_add hx hy]
      refine Ideal.sum_mem _ fun k hk ↦ ?_
      have hk' : k.1 + k.2 = n := by simpa using hk
      rw [← hk']
      exact hm _ _ (Ideal.mul_mem_mul (ihx k.1) (ihy k.2))
    | smul c x hx ih =>
      intro n
      rw [smul_eq_mul, δ.dpow_mul hx]
      exact Ideal.mul_mem_left _ _ (ih n)
  have hprod : ∀ l : List (ℕ × B), (∀ p ∈ l, p.2 ∈ Ideal.span s) →
      (l.map fun p ↦ δ.dpow p.1 p.2).prod ∈ F (l.map Prod.fst).sum := by
    intro l hl
    induction l with
    | nil => exact h0
    | cons p l ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      exact hm _ _ (Ideal.mul_mem_mul (hdp p.2 (hl p (by simp)) p.1) (ih fun q hq ↦ hl q (by simp [hq])))
  refine ⟨N, fun l hl h ↦ ?_⟩
  have := hprod l hl
  rwa [hN _ h, Ideal.mem_bot] at this

theorem Sup.sup_map_eq_span (f : R →+* B) : J ⊔ I.map f = Ideal.span ((J : Set B) ∪ f '' I) := by
  rw [Ideal.span_union, Ideal.span_eq]; rfl

theorem nil_sup (κ : DividedPowers I) (δ : DividedPowers J) (f : R →+* B) (δ' : DividedPowers J')
    (hJ : J' = J ⊔ I.map f) (h₁ : IsDPMorphism δ δ' (RingHom.id B)) (h₂ : IsDPMorphism κ δ' f)
    (hκ : IsNilDP κ) (hδ : IsNilDP δ) : IsNilDP δ' := by
  obtain ⟨N₁, k₁⟩ := Sup.exists_fil_eq_bot hκ
  obtain ⟨N₂, k₂⟩ := Sup.exists_fil_eq_bot hδ
  let F : ℕ → Ideal B := fun n ↦ ⨆ p : {p : ℕ × ℕ // p.1 + p.2 = n}, (fil κ p.1.1).map f * fil δ p.1.2
  have hF : ∀ a b n, a + b = n → (fil κ a).map f * fil δ b ≤ F n := fun a b n h ↦
    le_iSup (fun p : {p : ℕ × ℕ // p.1 + p.2 = n} ↦ (fil κ p.1.1).map f * fil δ p.1.2) ⟨(a, b), h⟩
  have one : (1 : B) ∈ (fil κ 0).map f := by
    simpa using Ideal.mem_map_of_mem f (Sup.one_mem_fil κ)
  refine Sup.isPDNilpotent_of_family δ' _ (hJ.trans (Sup.sup_map_eq_span f)) F ?_ (fun m n ↦ ?_) ?_ (N₁ + N₂) fun n hn ↦ ?_
  · simpa using hF 0 0 0 rfl (Ideal.mul_mem_mul one (Sup.one_mem_fil δ))
  · simp only [F, Submodule.iSup_mul, Submodule.mul_iSup, iSup_le_iff]
    rintro ⟨⟨a, b⟩, h⟩ ⟨⟨c, d⟩, h'⟩
    refine le_trans ?_ (hF (c + a) (d + b) _ (by simp only at h h'; omega))
    rw [mul_mul_mul_comm, ← Ideal.map_mul]
    exact Ideal.mul_mono (Ideal.map_mono (Sup.fil_mul_le _ _ _)) (Sup.fil_mul_le _ _ _)
  · rintro x (hx | ⟨r, hr, rfl⟩) n
    · have := h₁.2 (n := n) x hx
      simp only [RingHom.id_apply] at this
      rw [this]
      simpa using hF 0 n n (zero_add n) (Ideal.mul_mem_mul one (Sup.dpow_mem_fil δ hx n))
    · rw [h₂.2 r hr]
      simpa using hF n 0 n rfl (Ideal.mul_mem_mul (Ideal.mem_map_of_mem f (Sup.dpow_mem_fil κ hr n)) (Sup.one_mem_fil δ))
  · simp only [F, iSup_eq_bot]
    rintro ⟨⟨a, b⟩, h⟩
    simp only at h ⊢
    by_cases ha : N₁ ≤ a
    · rw [k₁ a ha, Ideal.map_bot, Ideal.bot_mul]
    · rw [k₂ b (by omega), Ideal.mul_bot]

theorem isDPMorphism_sup (κ : DividedPowers I) (δ : DividedPowers J) (f : R →+* B) (δ' : DividedPowers J')
    (hJ : J' = J ⊔ I.map f) (h₁ : IsDPMorphism δ δ' (RingHom.id B)) (h₂ : IsDPMorphism κ δ' f)
    (θ : DividedPowers L) (g : B →+* C) (k₁ : IsDPMorphism δ θ g) (k₂ : IsDPMorphism κ θ (g.comp f)) :
    IsDPMorphism δ' θ g := by
  refine IsDPMorphism.on_span δ' θ (hJ.trans (Sup.sup_map_eq_span f)) ?_ ?_
  · rintro x (hx | ⟨r, hr, rfl⟩)
    · exact k₁.1 (Ideal.mem_map_of_mem _ hx)
    · exact k₂.1 (Ideal.mem_map_of_mem _ hr)
  · rintro n x (hx | ⟨r, hr, rfl⟩)
    · have := h₁.2 (n := n) x hx
      simp only [RingHom.id_apply] at this
      rw [this]
      exact (k₁.2 x hx).symm
    · rw [h₂.2 r hr]
      exact (k₂.2 r hr).symm

end FubiniStudyChowHeightFormula₂.Adr
end
end
end

-- Source module: Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.IsDPMorphismId

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.PDA

namespace FubiniStudyChowHeightFormula₂.Adr

variable {R : Type} [CommRing R] {I : Ideal R} {X X₀ : Scheme.{0}}

def NT (κ : DividedPowers I) {s : X ⟶ Sp R} {K : Type} (U : K → X.Opens) : ObjectProperty (Tag (dp0 R) s U) :=
  fun S ↦ InN κ S.T

theorem isDPMorphism_id {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) :
    IsDPMorphism δ δ (RingHom.id B) := (DPMorphism.id δ).isDPMorphism

structure Red (κ : DividedPowers I) {R₀ : Type} [CommRing R₀] (π : R →+* R₀) (s : X ⟶ Sp R) (s₀ : X₀ ⟶ Sp R₀)
    (i : X₀ ⟶ X) : Prop where
  nil : IsNilDP κ
  surj : Function.Surjective π
  ker : RingHom.ker π = I
  pb : IsPullback i s₀ s (spMap π)

variable {κ : DividedPowers I} {R₀ : Type} [CommRing R₀] {π : R →+* R₀} {s : X ⟶ Sp R} {s₀ : X₀ ⟶ Sp R₀}
  {i : X₀ ⟶ X} (h : Red κ π s s₀ i)

namespace Red

include h

theorem mor : IsMor (dp0 R) s κ (s₀ ≫ spMap π) (RingHom.id R) i := by
  refine IsMor.of_dividedPowersZeroIdeal κ ?_
  rw [GlobalTheory.Cris.spMap_id, Category.comp_id]
  exact h.pb.w

theorem surjective : Function.Surjective i := by
  have hnil : ∀ x ∈ I, ∃ N : ℕ, x ^ N = 0 := by
    intro x hx
    obtain ⟨N, hN⟩ := h.nil
    refine ⟨N, ?_⟩
    have := hN (List.replicate N (1, x))
      (by
        intro p hp
        rw [List.eq_of_mem_replicate hp]
        exact hx)
      (by simp)
    simpa [List.map_replicate, List.prod_replicate, κ.dpow_one hx] using this
  have hsurj : Function.Surjective (spMap π) := by
    intro p
    have hp : p ∈ Set.range (PrimeSpectrum.comap π) := by
      open PrimeSpectrum in rw [range_comap_of_surjective _ π h.surj, h.ker]
      change (I : Set R) ⊆ (p : PrimeSpectrum R).asIdeal
      intro x hx
      obtain ⟨N, hN⟩ := hnil x hx
      exact p.isPrime.mem_of_pow_mem N (by rw [hN]; exact p.asIdeal.zero_mem)
    exact hp
  have hS : AlgebraicGeometry.Surjective (spMap π) := (AlgebraicGeometry.surjective_iff _).mpr hsurj
  exact (AlgebraicGeometry.surjective_iff i).mp
    (MorphismProperty.of_isPullback (P := @AlgebraicGeometry.Surjective) h.pb.flip hS)

theorem le_of_le {U V : X.Opens} (e : i ⁻¹ᵁ U ≤ i ⁻¹ᵁ V) : U ≤ V := by
  intro x hx
  obtain ⟨y, rfl⟩ := h.surjective x
  exact (show y ∈ i ⁻¹ᵁ V from e (show y ∈ i ⁻¹ᵁ U from hx))

theorem inN_obj (T : Thick κ (s₀ ≫ spMap π)) : InN κ (h.mor.obj T) := by
  show ∃ δ' : DividedPowers (T.J ⊔ Ideal.map (algebraMap R T.B) I),
    T.δ.IsDPMorphism δ' (RingHom.id T.B) ∧ κ.IsDPMorphism δ' (algebraMap R T.B)
  rw [sup_eq_left.mpr T.dp.ideal_comp]
  exact ⟨T.δ, isDPMorphism_id T.δ, T.dp⟩

end Red

section Up

variable (S : Thick (dp0 R) s)

abbrev big (I : Ideal R) : Ideal S.B := S.J ⊔ I.map (algebraMap R S.B)

def rho (I : Ideal R) : S.B₀ →+* S.B ⧸ big S I :=
  RingHom.liftOfSurjective S.π S.surj ⟨Ideal.Quotient.mk _, fun b hb ↦
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_left ((S.ker b).1 hb))⟩

theorem rho_π (I : Ideal R) (b : S.B) : rho S I (S.π b) = Ideal.Quotient.mk _ b :=
  RingHom.liftOfSurjective_comp_apply _ _ _ b

def Red.sig : R₀ →+* S.B ⧸ big S I :=
  RingHom.liftOfSurjective π h.surj ⟨(Ideal.Quotient.mk _).comp (algebraMap R S.B), fun r hr ↦
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_right (Ideal.mem_map_of_mem _ (h.ker ▸ hr)))⟩

theorem Red.sig_π (r : R) : h.sig S (π r) = Ideal.Quotient.mk _ (algebraMap R S.B r) :=
  RingHom.liftOfSurjective_comp_apply _ _ _ r

def Red.pt : Sp (S.B ⧸ big S I) ⟶ X₀ :=
  h.pb.lift (spMap (rho S I) ≫ S.x) (spMap (h.sig S)) (by
    rw [Category.assoc, S.w, ← GlobalTheory.Cris.spMap_comp, ← GlobalTheory.Cris.spMap_comp]
    congr 1
    exact RingHom.ext fun r ↦ (rho_π S I _).trans (h.sig_π S r).symm)

theorem Red.pt_i : h.pt S ≫ i = spMap (rho S I) ≫ S.x := h.pb.lift_fst _ _ _

theorem Red.pt_s : h.pt S ≫ s₀ = spMap (h.sig S) := h.pb.lift_snd _ _ _

@[reducible] def Red.up (hS : InN κ S) : Thick κ (s₀ ≫ spMap π) where
  B := S.B
  J := big S I
  δ := hS.choose
  nil := nil_sup κ S.δ _ _ rfl hS.choose_spec.1 hS.choose_spec.2 h.nil S.nil
  dp := hS.choose_spec.2
  B₀ := S.B ⧸ big S I
  π := Ideal.Quotient.mk _
  surj := Ideal.Quotient.mk_surjective
  ker _ := Ideal.Quotient.eq_zero_iff_mem
  x := h.pt S
  w := by
    rw [← Category.assoc, h.pt_s, ← GlobalTheory.Cris.spMap_comp]
    congr 1
    exact RingHom.ext fun r ↦ h.sig_π S r

variable {S}

def Red.rh {T : Thick κ (s₀ ≫ spMap π)} (f : S ⟶ h.mor.obj T) : S.B →+* T.B :=
  (f.φ : S.B →+* (h.mor.obj T).B)

theorem Red.rh_algebraMap {T : Thick κ (s₀ ≫ spMap π)} (f : S ⟶ h.mor.obj T) (r : R) :
    h.rh f (algebraMap R S.B r) = algebraMap R T.B r := f.φ.commutes r

def Red.upTo (hS : InN κ S) {T : Thick κ (s₀ ≫ spMap π)} (f : S ⟶ h.mor.obj T) : h.up S hS ⟶ T where
  φ := { (h.rh f) with commutes' := h.rh_algebraMap f }
  φ₀ := Ideal.Quotient.lift _ (T.π.comp (h.rh f)) fun b hb ↦ (T.ker _).2 (by
    have : big S I ≤ T.J.comap (h.rh f) := sup_le (fun b hb ↦ f.mem hb)
      (Ideal.map_le_iff_le_comap.2 fun r hr ↦ by
        change h.rh f (algebraMap R S.B r) ∈ T.J
        rw [h.rh_algebraMap]
        exact T.dp.1 (Ideal.mem_map_of_mem _ hr))
    exact this hb)
  comm _ := rfl
  dp := isDPMorphism_sup κ S.δ _ _ rfl hS.choose_spec.1 hS.choose_spec.2 T.δ _ f.dp (by
    change IsDPMorphism κ T.δ ((h.rh f).comp (algebraMap R S.B))
    rw [show (h.rh f).comp (algebraMap R S.B) = algebraMap R T.B from RingHom.ext (h.rh_algebraMap f)]
    exact T.dp)
  pt := by
    refine h.pb.hom_ext ?_ ?_
    · change (_ ≫ h.pt S) ≫ i = _
      rw [Category.assoc, h.pt_i, ← Category.assoc, ← GlobalTheory.Cris.spMap_comp]
      refine Eq.trans ?_ f.pt
      congr 2
      refine RingHom.ext fun b ↦ ?_
      obtain ⟨b, rfl⟩ := S.surj b
      rw [RingHom.comp_apply, rho_π]
      exact (f.comm b).symm
    · change (_ ≫ h.pt S) ≫ s₀ = _
      have : Mono (spMap π) := by
        have : IsClosedImmersion (spMap π) := IsClosedImmersion.spec_of_surjective _ h.surj
        infer_instance
      rw [← cancel_mono (spMap π), Category.assoc, Category.assoc, ← Category.assoc (h.pt S), h.pt_s,
        Category.assoc, T.w, ← GlobalTheory.Cris.spMap_comp, ← GlobalTheory.Cris.spMap_comp]
      congr 1
      refine RingHom.ext fun r ↦ ?_
      simp only [RingHom.comp_apply]
      rw [h.sig_π]
      exact congrArg T.π (h.rh_algebraMap f r)

def Red.unit (hS : InN κ S) : S ⟶ h.mor.obj (h.up S hS) where
  φ := { RingHom.id S.B with commutes' := fun _ ↦ rfl }
  φ₀ := rho S I
  comm := rho_π S I
  dp := hS.choose_spec.1
  pt := (h.pt_i S).symm

end Up

variable {K : Type} (U : K → X.Opens)

abbrev redOpen (i : X₀ ⟶ X) : K → X₀.Opens := fun k ↦ i ⁻¹ᵁ U k

def Red.G : Tag κ (s₀ ≫ spMap π) (redOpen U i) ⥤ (NT κ U (s := s)).FullSubcategory where
  obj T := ⟨⟨h.mor.obj T.T, T.k, T.le⟩, h.inN_obj T.T⟩
  map f := ObjectProperty.homMk (⟨h.mor.functor.map (Tag.Hom.f f), h.le_of_le (Tag.Hom.le f)⟩ : Tag.Hom _ _)
  map_id _ := ObjectProperty.hom_ext _ (Tag.Hom.ext (Thick.Hom.ext' (AlgHom.ext fun _ ↦ rfl)))
  map_comp _ _ := ObjectProperty.hom_ext _ (Tag.Hom.ext (Thick.Hom.ext' (AlgHom.ext fun _ ↦ rfl)))

def Red.H : (NT κ U (s := s)).FullSubcategory ⥤ Tag κ (s₀ ≫ spMap π) (redOpen U i) where
  obj S := ⟨h.up S.obj.T S.property, S.obj.k, (h.unit S.property).le_preimage S.obj.le⟩
  map {S S'} f := ⟨h.upTo S.property (Tag.Hom.f f.hom ≫ h.unit S'.property),
    fun _ hp ↦ Tag.Hom.le f.hom hp⟩
  map_id _ := Tag.Hom.ext (Thick.Hom.ext' (AlgHom.ext fun _ ↦ rfl))
  map_comp f g := by
    refine Tag.Hom.ext (Thick.Hom.ext' (AlgHom.ext fun b ↦ ?_))
    exact (rfl : (Tag.Hom.f g.hom).φ ((Tag.Hom.f f.hom).φ b) = (Tag.Hom.f g.hom).φ ((Tag.Hom.f f.hom).φ b))

abbrev FN (κ : DividedPowers I) (s : X ⟶ Sp R) (U : K → X.Opens) :
    (NT κ U (s := s)).FullSubcategory ⥤ CommAlgCat.{0} R :=
  (NT κ U).ι ⋙ Tag.forget (dp0 R) s U ⋙ O (dp0 R) s

def Red.cG : CoefMap (RingHom.id R) (FN κ s U) (Tag.forget κ _ (redOpen U i) ⋙ O κ (s₀ ≫ spMap π)) where
  G := h.G U
  α T := RingHom.id T.T.B
  naturality _ _ := rfl
  smul T r b := (Algebra.smul_def (A := T.T.B) r b).symm

def Red.cH : CoefMap (RingHom.id R) (Tag.forget κ _ (redOpen U i) ⋙ O κ (s₀ ≫ spMap π)) (FN κ s U) where
  G := h.H U
  α S := RingHom.id S.obj.T.B
  naturality _ _ := rfl
  smul _ _ _ := rfl

def Red.η : 𝟭 _ ⟶ h.H U ⋙ h.G U where
  app S := ObjectProperty.homMk
    (⟨h.unit S.property, le_rfl⟩ : Tag.Hom S.obj ((h.G U).obj ((h.H U).obj S)).obj)
  naturality S S' f := by
    refine ObjectProperty.hom_ext _ (Tag.Hom.ext (Thick.Hom.ext' (AlgHom.ext fun b ↦ ?_)))
    exact (rfl : (Tag.Hom.f f.hom).φ b = (Tag.Hom.f f.hom).φ b)

def Red.ε : h.G U ⋙ h.H U ⟶ 𝟭 _ where
  app T := (⟨h.upTo (h.inN_obj T.T) (𝟙 _), le_rfl⟩ : Tag.Hom ((h.H U).obj ((h.G U).obj T)) T)
  naturality S S' f := by
    refine Tag.Hom.ext (Thick.Hom.ext' (AlgHom.ext fun b ↦ ?_))
    exact (rfl : (Tag.Hom.f f).φ b = (Tag.Hom.f f).φ b)

theorem Red.cG_pull1 : Function.Bijective (h.cG U).pull1 := by
  refine Function.bijective_iff_has_inverse.2 ⟨(h.cH U).pull1, fun c ↦ ?_, fun c ↦ ?_⟩
  · rw [← CoefMap.pullCohomologyOne_comp]
    exact ((CoefMap.id _).pullCohomologyOne_eq_of_natTrans ((h.cG U).comp (h.cH U)) (h.η U) (fun _ b ↦ (rfl : b = b)) c).symm.trans
      (CoefMap.pullCohomologyOne_id c)
  · rw [← CoefMap.pullCohomologyOne_comp]
    exact (((h.cH U).comp (h.cG U)).pullCohomologyOne_eq_of_natTrans (CoefMap.id _) (h.ε U) (fun _ b ↦ (rfl : b = b)) c).trans
      (CoefMap.pullCohomologyOne_id c)

theorem Red.cG_pull2 : Function.Bijective (h.cG U).pull2 := by
  refine Function.bijective_iff_has_inverse.2 ⟨(h.cH U).pull2, fun c ↦ ?_, fun c ↦ ?_⟩
  · rw [← CoefMap.pullCohomologyTwo_comp]
    exact ((CoefMap.id _).pullCohomologyTwo_eq_of_natTrans ((h.cG U).comp (h.cH U)) (h.η U) (fun _ b ↦ (rfl : b = b)) c).symm.trans
      (CoefMap.pullCohomologyTwo_id c)
  · rw [← CoefMap.pullCohomologyTwo_comp]
    exact (((h.cH U).comp (h.cG U)).pullCohomologyTwo_eq_of_natTrans (CoefMap.id _) (h.ε U) (fun _ b ↦ (rfl : b = b)) c).trans
      (CoefMap.pullCohomologyTwo_id c)

end FubiniStudyChowHeightFormula₂.Adr
end
end
end

-- Source module: Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.CrystallineDeRham

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.PDA

namespace FubiniStudyChowHeightFormula₂.Adr

variable {R : Type} [CommRing R] {I : Ideal R} {X : Scheme.{0}}

abbrev chartOpen (s : X ⟶ Sp R) : Chart s → X.Opens := fun U ↦ U.1.1

theorem exists_lev {B : Type} [CommRing B] {J : Ideal B} {δ : DividedPowers J} (h : IsNilDP δ) :
    ∃ n, 1 ≤ n ∧ IsLev δ n := by
  obtain ⟨N, h⟩ := h
  refine ⟨N + 1, by omega, Ideal.span_eq_bot.2 ?_⟩
  rintro _ ⟨l, hl, hN, rfl⟩
  exact h l hl (by omega)

variable {κ : DividedPowers I} {s : X ⟶ Sp R}

theorem acyc_NT (T : Tag (dp0 R) s (chartOpen s)) :
    Acyc R (CostructuredArrow (NT κ (chartOpen s)).ι T) := by
  obtain ⟨n, hn, hT⟩ := exists_lev T.T.nil
  obtain ⟨a₀⟩ := exists_lift T.k T.T T.le
  let D := CostructuredArrow (NT κ (chartOpen s)).ι T
  let mk : ∀ (S : Thick (dp0 R) s) (_ : InN κ S) (_ : ⊤ ≤ S.x ⁻¹ᵁ T.k.1.1) (_ : S ⟶ T.T), D := fun S hS h c ↦
    CostructuredArrow.mk (Y := (⟨⟨S, T.k, h⟩, hS⟩ : (NT κ (chartOpen s)).FullSubcategory))
      (⟨c, le_rfl⟩ : Tag.Hom (⟨S, T.k, h⟩ : Tag (dp0 R) s (chartOpen s)) T)
  let c : ∀ a : D, a.left.obj.T ⟶ T.T := fun a ↦ Tag.Hom.f a.hom
  have hk : ∀ a : D, chartOpen s a.left.obj.k ≤ chartOpen s T.k := fun a ↦ Tag.Hom.le a.hom
  have hle : ∀ a : D, ⊤ ≤ a.left.obj.T.x ⁻¹ᵁ T.k.1.1 := fun a p hp ↦ hk a (a.left.obj.le hp)
  let u : ∀ {a b : D}, (a ⟶ b) → (a.left.obj.T ⟶ b.left.obj.T) := fun f ↦ Tag.Hom.f f.left.hom
  have hu : ∀ {a b : D} (f : a ⟶ b), u f ≫ c b = c a := fun f ↦
    congrArg Tag.Hom.f (CostructuredArrow.w f)
  have ext : ∀ {a b : D} (f g : a ⟶ b), u f = u g → f = g := fun f g h ↦
    CostructuredArrow.hom_ext _ _ (ObjectProperty.hom_ext _ (Tag.Hom.ext h))
  let hom : ∀ (a b : D) (φ : a.left.obj.T ⟶ b.left.obj.T) (_ : chartOpen s a.left.obj.k ≤ chartOpen s b.left.obj.k)
      (_ : φ ≫ c b = c a), a ⟶ b := fun a b φ h e ↦
    CostructuredArrow.homMk (ObjectProperty.homMk (⟨φ, h⟩ : Tag.Hom _ _)) (Tag.Hom.ext e)
  choose P i j hP hl hun using fun a : D ↦ exists_coprod T.k a.left.obj.T a.left.property (hle a) n hn
  choose q hq using fun a : D ↦ (hun a T.T hT (c a) a₀).exists
  let d : D := mk _ (bas_inN T.k) (bas_le T.k.1) a₀
  let Q : D → D := fun a ↦ mk (P a) (hP a) ((i a).le_preimage (hle a)) (q a)
  refine acyc_of_coprod d Q (fun a ↦ hom a (Q a) (i a) (hk a) (hq a).1)
    (fun a ↦ hom d (Q a) (j a) le_rfl (hq a).2) fun a b φ ↦ ?_
  obtain ⟨ψ, hψ, hψ'⟩ := hun a (P b) (hl b) (u φ) (j b)
  have e : ψ ≫ q b = q a := by
    refine (hun a T.T hT (c a) a₀).unique ⟨?_, ?_⟩ (hq a)
    · rw [← Category.assoc, hψ.1]; exact hu φ
    · rw [← Category.assoc, hψ.2]; exact (hq b).2
  refine ⟨hom (Q a) (Q b) ψ le_rfl e, ⟨ext _ _ hψ.1, ext _ _ hψ.2⟩, fun χ hχ ↦ ext _ _ ?_⟩
  exact hψ' (u χ) ⟨congrArg u hχ.1, congrArg u hχ.2⟩

section Final

variable {R₀ : Type} [CommRing R₀] {π : R →+* R₀} {X₀ : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀} {i : X₀ ⟶ X}

theorem red_cover (hs : Smooth s) (i : X₀ ⟶ X) : ⨆ k, redOpen (chartOpen s) i k = ⊤ := by
  rw [← Scheme.Hom.preimage_iSup, chart_cover hs, Scheme.Hom.preimage_top]

theorem red_inf (hs : IsSeparated s) (i : X₀ ⟶ X) (k l : Chart s) :
    ∃ m, redOpen (chartOpen s) i m = redOpen (chartOpen s) i k ⊓ redOpen (chartOpen s) i l := by
  obtain ⟨m, hm⟩ := chart_inf hs k l
  exact ⟨m, by change i ⁻¹ᵁ m.1.1 = _; rw [hm]; rfl⟩

theorem Red.pull1 (h : Red κ π s s₀ i) (hs : Smooth s) (hs' : IsSeparated s) : Function.Bijective h.mor.pull1 := by
  have a := tag_pull1 (γ := dp0 R) (s := s) (chart_cover hs) (chart_inf hs')
  have b := qa1 (Tag.forget (dp0 R) s (chartOpen s) ⋙ O (dp0 R) s) (NT κ (chartOpen s)).ι acyc_NT
  have c := h.cG_pull1 (chartOpen s)
  have d := tag_pull1 (γ := κ) (s := s₀ ≫ spMap π) (red_cover hs i) (red_inf hs' i)
  refine (Function.Bijective.of_comp_iff' d _).1 ?_
  convert c.comp (b.comp a) using 1
  funext z
  obtain ⟨z, rfl⟩ := H1.mk_surjective _ z
  rfl

theorem Red.pull2 (h : Red κ π s s₀ i) (hs : Smooth s) (hs' : IsSeparated s) : Function.Bijective h.mor.pull2 := by
  have a := tag_pull2 (γ := dp0 R) (s := s) (chart_cover hs) (chart_inf hs')
  have b := qa2 (Tag.forget (dp0 R) s (chartOpen s) ⋙ O (dp0 R) s) (NT κ (chartOpen s)).ι acyc_NT
  have c := h.cG_pull2 (chartOpen s)
  have d := tag_pull2 (γ := κ) (s := s₀ ≫ spMap π) (red_cover hs i) (red_inf hs' i)
  refine (Function.Bijective.of_comp_iff' d _).1 ?_
  convert c.comp (b.comp a) using 1
  funext z
  obtain ⟨z, rfl⟩ := H2.mk_surjective _ z
  rfl

end Final

theorem crystallineDeRham : GlobalTheory.Published.CrystallineDeRham := fun _ _ _ _ hκ _ _ _ hπ hI _ _ _ _ _ hs hs' _ hp _ ↦
  ⟨Red.pull1 ⟨hκ, hπ, hI, hp⟩ hs hs', Red.pull2 ⟨hκ, hπ, hI, hp⟩ hs hs'⟩

end FubiniStudyChowHeightFormula₂.Adr
end
end
end
