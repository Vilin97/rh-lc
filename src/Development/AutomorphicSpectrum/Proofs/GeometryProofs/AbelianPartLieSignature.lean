module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianPartLieMultShiftStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DetCondIffOfFieldExtension
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DeterminantConditionSpreadsOfDensePoints
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.Style
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieMultIffExistsFrame
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConnectedGroupSmoothRelDim

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace GlobalTheory.CompanionTheory.Ggeo

theorem exists_smoothOfRelativeDimension_of_geometricallyConnected :
    ∀ (X : Scheme.{0}) [ConnectedSpace X] (G : Over X) [GrpObj G], Smooth G.hom →
      GeometricallyConnected G.hom → ∃ g : ℕ, SmoothOfRelativeDimension g G.hom := by
  intro X _ G _ hs hc
  haveI : Smooth G.hom := hs
  obtain ⟨d, W, hxW, hW⟩ : ∃ (d : G.left → ℕ) (W : G.left → G.left.Opens), (∀ x, x ∈ W x) ∧
      ∀ x, SmoothOfRelativeDimension (d x) ((W x).ι ≫ G.hom) := by
    choose d W hxW hW using fun x => ReciprocityTheory.ChartRestriction.G.H1.exists_dim G.hom x
    exact ⟨d, W, hxW, hW⟩
  have hres : ∀ (x : G.left) (V : G.left.Opens), V ≤ W x →
      SmoothOfRelativeDimension (d x) (V.ι ≫ G.hom) := by
    intro x V hV
    have h := HasRingHomProperty.comp_of_isOpenImmersion (@SmoothOfRelativeDimension (d x))
      (G.left.homOfLE hV) ((W x).ι ≫ G.hom) (hW x)
    rwa [← Category.assoc, Scheme.homOfLE_ι] at h
  have hd : IsLocallyConstant d := by
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    refine ⟨W x, (W x).isOpen, hxW x, fun y hy => ?_⟩
    have h1 := hres x (W x ⊓ W y) inf_le_left
    have h2 := hres y (W x ⊓ W y) inf_le_right
    exact ReciprocityTheory.ChartRestriction.G.H1.dim_unique _ h2 h1 ⟨y, hy, hxW y⟩
  let e : X ⟶ G.left := (η[G]).left
  have hcomp : e ≫ G.hom = 𝟙 X := Over.w (η[G])
  have he : ∀ s : X, G.hom (e s) = s := by
    intro s
    have h := congrArg (fun g : X ⟶ X => g s) hcomp
    simpa using h
  have hfib : ∀ s : X, _root_.IsPreconnected (G.hom ⁻¹' {s}) := by
    intro s
    rw [← Scheme.Hom.range_fiberι]
    exact isPreconnected_range (Scheme.Hom.continuous _)
  obtain ⟨s₀⟩ : Nonempty X := inferInstance
  have hconst : ∀ x, d x = d (e s₀) := by
    intro x
    have h1 : d x = d (e (G.hom x)) :=
      hd.apply_eq_of_isPreconnected (hfib (G.hom x)) rfl (he (G.hom x))
    have h2 : d (e (G.hom x)) = d (e s₀) :=
      (hd.comp_continuous (Scheme.Hom.continuous e)).apply_eq_of_isPreconnected
        isPreconnected_univ trivial trivial
    exact h1.trans h2
  refine ⟨d (e s₀), ?_⟩
  haveI : IsZariskiLocalAtSource (@SmoothOfRelativeDimension (d (e s₀))) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  exact IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension (d (e s₀))) W
    (eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxW x⟩)
    (fun x => by rw [← hconst x]; exact hW x)

end GlobalTheory.CompanionTheory.Ggeo
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.EmbeddingFactorsThroughCmType

section

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LabelCover

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem exists_ext {E : Type} [Field E] [NumberField E] {K : Type} [Field K] [CharZero K] (τ : 𝓞 E →+* K) :
    ∃ ψ : E →+* K, ψ.comp (algebraMap (𝓞 E) E) = τ := by
  have hker : RingHom.ker τ = ⊥ := by
    apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
    rw [Ideal.under_def, RingHom.comap_ker, RingHom.ker_eq_bot_iff_eq_zero]
    intro n hn
    simpa using hn
  have hinj : Function.Injective τ := (RingHom.injective_iff_ker_eq_bot τ).mpr hker
  exact ⟨IsFractionRing.lift hinj, RingHom.ext fun x => IsFractionRing.lift_algebraMap hinj x⟩

theorem charZero_of_coeff {F : IntermediateField ℚ ℂ} {k : Type} [Field k] (φ : F →+* k) : CharZero k :=
  (RingHom.charZero_iff (φ.comp (algebraMap ℚ F)).injective).mp inferInstance

theorem exists_factor {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l)
    {k : Type} [Field k] [IsAlgClosed k] (φ : c.F →+* k) (ψ : E →+* k) :
    ∃ τ₁ : E →+* ℂ, φ.comp (τ₁.codRestrict c.F (c.conj τ₁)) = ψ := by
  haveI : CharZero k := charZero_of_coeff φ
  let g : (E →+* ℂ) → (E →+* k) := fun τ => φ.comp (τ.codRestrict c.F (c.conj τ))
  have hg : Function.Injective g := by
    intro τ τ' h
    ext a
    have h1 := RingHom.congr_fun h a
    simp only [g, RingHom.comp_apply] at h1
    exact congrArg Subtype.val (φ.injective h1)
  have hcard : Fintype.card (E →+* ℂ) = Fintype.card (E →+* k) := by
    rw [NumberField.Embeddings.card, NumberField.Embeddings.card]
  obtain ⟨τ₁, hτ₁⟩ := ((Fintype.bijective_iff_injective_and_card g).mpr ⟨hg, hcard⟩).2 ψ
  exact ⟨τ₁, hτ₁⟩

theorem exists_label : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l)
    (ρ₀ : c.F), (ρ₀ : ℂ) = H.rt0 → ∀ (k : Type) [Field k] [IsAlgClosed k] (φ : c.F →+* k) (τ : 𝓞 E →+* k),
    (τ H.rt = φ ρ₀ → ∃ t : CMType H, φ.comp (labelEmb c (.inl t)) = τ) ∧
    (τ H.rt ≠ φ ρ₀ → ∃ t : CMType H, φ.comp (labelEmb c (.inr t)) = τ) := by
  intro E _ _ _ H l c ρ₀ hρ₀ k _ _ φ τ
  haveI : CharZero k := charZero_of_coeff φ
  obtain ⟨ψ, hψ⟩ := exists_ext τ
  obtain ⟨τ₁, hτ₁⟩ := exists_factor c φ ψ
  have key : ∀ a : 𝓞 E, φ ⟨τ₁ (a : E), c.conj τ₁ (a : E)⟩ = τ a := by
    intro a
    rw [← hψ, ← hτ₁]
    rfl
  have hrt : τ₁ (H.rt : E) = H.rt0 ↔ τ H.rt = φ ρ₀ := by
    constructor
    · intro h
      rw [← key]
      congr 1
      exact Subtype.ext (h.trans hρ₀.symm)
    · intro h
      rw [← key] at h
      rw [← hρ₀]
      exact congrArg Subtype.val (φ.injective h)
  refine ⟨fun h => ⟨⟨τ₁, hrt.mpr h⟩, RingHom.ext fun a => key a⟩, fun h => ?_⟩
  have hne : τ₁ (H.rt : E) ≠ H.rt0 := fun h' => h (hrt.mp h')
  have hsqE : (H.rt : E) ^ 2 = -(H.d : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    simpa using this
  have hsq : τ₁ (H.rt : E) ^ 2 = H.rt0 ^ 2 := by
    rw [← map_pow, hsqE, map_neg, map_natCast, H.sqrt_neg_disc_sq]
  have hneg : τ₁ (H.rt : E) = -H.rt0 := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h1 | h1
    · exact absurd h1 hne
    · exact h1
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hre : H.rt0.re = 0 := by
    have h1 := congrArg Complex.re H.sqrt_neg_disc_sq
    have h2 := congrArg Complex.im H.sqrt_neg_disc_sq
    simp only [sq, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re,
      Complex.natCast_im, neg_zero] at h1 h2
    have h3 : H.rt0.re * H.rt0.im = 0 := by linarith
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact h4
    · exfalso
      rw [h4] at h1
      nlinarith [sq_nonneg H.rt0.re]
  have hconj : (starRingEnd ℂ) (-H.rt0) = H.rt0 := by
    apply Complex.ext <;> simp [hre]
  refine ⟨⟨τ₁.comp (NumberField.IsCMField.complexConj E).toRingEquiv.toRingHom, ?_⟩, ?_⟩
  · show τ₁ (NumberField.IsCMField.complexConj E (H.rt : E)) = H.rt0
    rw [NumberField.IsCMField.complexEmbedding_complexConj, hneg, hconj]
  · refine RingHom.ext fun a => ?_
    rw [← key a, RingHom.comp_apply]
    refine congrArg φ (Subtype.ext ?_)
    show τ₁ (NumberField.IsCMField.complexConj E ((H.bar a : 𝓞 E) : E)) = τ₁ (a : E)
    rw [H.bar_eq, NumberField.IsCMField.complexConj_apply_apply]

end GlobalTheory.CompanionTheory.Ar.LabelCover
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieMultLabelRank

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.HodgeCpt

theorem lieMult_label_generic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β)
    (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω)
    (𝔐 : HodgeCpt Y S y) (s : CMType H ⊕ CMType H), LieMult 𝔐.t.act 𝔐.ξ (𝔐.emb s) (labelRk D s) := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J y 𝔐 s
  letI := 𝔐.acg
  letI := 𝔐.mod
  obtain ⟨U, hU, b, hspan, hfr⟩ := 𝔐.vb s ⟨genPt 𝔐.ξ, specializes_refl _⟩ (Set.mem_univ _)
  exact (Fl.Test.lieMult_iff_exists_frame _ _ _ _).2
    ⟨_, (Fl.Test.isEigFrame_iff 𝔐.M 𝔐.t.act 𝔐.ρ 𝔐.act (𝔐.emb s) b).2
      ⟨(hfr _ (Set.mem_univ _) hU).1, hspan⟩⟩

end GlobalTheory.CompanionTheory.Ar.HodgeCpt
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsSqrtNegDiscPoint

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.PointDet

theorem isReduced_of_isNormalScheme {X : Scheme.{0}} (h : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) : IsReduced X := by
  have : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
    have := (h x).1
    infer_instance
  exact isReduced_of_isReduced_stalk X

theorem connectedSpace_of_specializes {X : Scheme.{0}} (x : X) (h : ∀ q : X, x ⤳ q) : ConnectedSpace X := by
  have hcl : closure {x} = (Set.univ : Set X) :=
    Set.eq_univ_of_forall fun q => specializes_iff_mem_closure.1 (h q)
  have hp : PreconnectedSpace X := ⟨by rw [← hcl]; exact isPreconnected_singleton.closure⟩
  exact { toPreconnectedSpace := hp, toNonempty := ⟨x⟩ }

theorem spMap_comp_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

noncomputable def rtF {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l) : c.F :=
  ⟨H.rt0, c.le (IntermediateField.subset_adjoin _ _ (by simp))⟩

theorem rtF_sq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l) :
    rtF c ^ 2 = -(H.d : c.F) := by
  apply Subtype.ext
  simpa [rtF] using H.sqrt_neg_disc_sq

theorem isIntegral_rtF {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l) :
    IsIntegral ℤ (rtF c) := by
  refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
  rw [rtF_sq]
  have := isIntegral_algebraMap (R := ℤ) (A := c.F) (x := -(H.d : ℤ))
  simpa using this

noncomputable def rtO {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l) : 𝓞 c.F :=
  IsIntegralClosure.mk' (𝓞 c.F) (rtF c) (isIntegral_rtF c)

theorem algebraMap_rtO {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l) :
    algebraMap (𝓞 c.F) c.F (rtO c) = rtF c :=
  IsIntegralClosure.algebraMap_mk' _ _ _

theorem rtO_sq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l) :
    rtO c ^ 2 = -(H.d : 𝓞 c.F) := by
  apply RingOfIntegers.ext
  have := rtF_sq c
  rw [← algebraMap_rtO] at this
  simpa using this

theorem detCond_at_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (L : Type) [Field L] [NumberField L] (z : Sp L ⟶ 𝔐.X), ∃ ρ : L, ρ ^ 2 = -(H.d : L) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (g : L →+* k), DetCond D 𝔐.t.act (spMap g ≫ z) (g ρ) := by
  intro E _ _ _ H D l Xo c Y S Ω _ Kf _ J _ y 𝔐 L _ _ z
  haveI : IsReduced 𝔐.X := isReduced_of_isNormalScheme 𝔐.normal
  haveI : ConnectedSpace 𝔐.X := connectedSpace_of_specializes _ 𝔐.all
  haveI : Smooth 𝔐.t.G.hom := 𝔐.t.semi.smooth
  obtain ⟨n, hn⟩ := GlobalTheory.CompanionTheory.Ggeo.exists_smoothOfRelativeDimension_of_geometricallyConnected 𝔐.X 𝔐.t.G 𝔐.t.semi.smooth 𝔐.t.semi.geomConnected
  let s : 𝔐.X ⟶ Sp (𝓞 c.F) := 𝔐.f ≫ Y.s
  have hd : Dense {p : 𝔐.X | ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (_ : CharZero K) (x : Sp K ⟶ 𝔐.X)
      (β : 𝓞 c.F →+* K), p ∈ Set.range x ∧ x ≫ s = spMap β ∧ DetCond D 𝔐.t.act x (β (rtO c))} := by
    intro q
    refine closure_mono (Set.singleton_subset_iff.2 ?_) (specializes_iff_mem_closure.1 (𝔐.all q))
    let i : Ω →+* AlgebraicClosure Ω := algebraMap Ω (AlgebraicClosure Ω)
    haveI : CharZero Ω := charZero_of_injective_ringHom 𝔐.cst.injective
    haveI : CharZero (AlgebraicClosure Ω) := charZero_of_injective_ringHom i.injective
    refine ⟨AlgebraicClosure Ω, inferInstance, inferInstance, inferInstance, spMap i ≫ 𝔐.ξ,
      i.comp (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)), ?_, ?_, ?_⟩
    · let y₀ : Sp (AlgebraicClosure Ω) := (default : PrimeSpectrum (AlgebraicClosure Ω))
      refine ⟨y₀, ?_⟩
      rw [Scheme.Hom.comp_apply]
      exact congrArg 𝔐.ξ (Subsingleton.elim _ _)
    · have h := 𝔐.cst_over
      change (spMap i ≫ 𝔐.ξ) ≫ 𝔐.f ≫ Y.s = _
      rw [Category.assoc, h, spMap_comp_spMap]
    · intro τ
      have hβ : (i.comp (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F))) (rtO c) = (i.comp 𝔐.cst) (rtF c) := by
        simp only [RingHom.comp_apply, algebraMap_rtO]
      rw [hβ]
      obtain ⟨h₁, h₂⟩ := GlobalTheory.CompanionTheory.Ar.LabelCover.exists_label E H l c (rtF c) rfl (AlgebraicClosure Ω) (i.comp 𝔐.cst) τ
      constructor
      · intro h
        obtain ⟨t, rfl⟩ := h₁ h
        exact (GlobalTheory.DetExtend.lieMult_extend i 𝔐.ξ 𝔐.t.act (𝔐.emb (.inl t)) D.p).2
          (GlobalTheory.CompanionTheory.Ar.HodgeCpt.lieMult_label_generic E H D l Xo c (𝓞 c.F) (algebraMap (𝓞 c.F) c.F) Y S Ω Kf J y 𝔐 (.inl t))
      · intro h
        obtain ⟨t, rfl⟩ := h₂ h
        exact (GlobalTheory.DetExtend.lieMult_extend i 𝔐.ξ 𝔐.t.act (𝔐.emb (.inr t)) D.q).2
          (GlobalTheory.CompanionTheory.Ar.HodgeCpt.lieMult_label_generic E H D l Xo c (𝓞 c.F) (algebraMap (𝓞 c.F) c.F) Y S Ω Kf J y 𝔐 (.inr t))
  obtain ⟨b, hb⟩ := Spec.map_surjective (z ≫ s)
  refine ⟨b.hom (rtO c), ?_, ?_⟩
  · have := congrArg b.hom (rtO_sq c)
    rw [map_pow, map_neg, map_natCast] at this
    exact this
  · intro k _ _ g
    haveI : CharZero k := charZero_of_injective_ringHom g.injective
    refine GlobalTheory.DetSpread.detCond_of_dense E H D 𝔐.X 𝔐.t.G n 𝔐.t.act (𝓞 c.F) s (rtO c) hn (rtO_sq c) hd k
      (spMap g ≫ z) (g.comp b.hom) ?_
    rw [Category.assoc, ← hb]
    exact spMap_comp_spMap b.hom g

end GlobalTheory.CompanionTheory.Ar.PointDet
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsSqrtNegDiscPointStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.exists_sqrt_neg_disc_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (L : Type) [Field L] [NumberField L] (z : Sp L ⟶ 𝔐.X), ∃ ρ : L, ρ ^ 2 = -(H.d : L) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (g : L →+* k), DetCond D 𝔐.t.act (spMap g ≫ z) (g ρ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PointDet.detCond_at_point | exact GlobalTheory.CompanionTheory.Ar.PointDet.detCond_at_point | (intros; apply GlobalTheory.CompanionTheory.Ar.PointDet.detCond_at_point <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianPartLieSignature

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.AbPartConst

theorem lieMult_constant_along_cmType : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (L : Type) [Field L] [NumberField L] (z : Sp L ⟶ 𝔐.X) (P : AbPart 𝔐.t z), ∃ (ρ : L) (p' q' : ℕ), ρ ^ 2 = -(H.d : L) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (g : L →+* k) (τ : 𝓞 E →+* k), (τ H.rt = g ρ → LieMult P.tB.act (spMap g) τ p') ∧ (τ H.rt ≠ g ρ → LieMult P.tB.act (spMap g) τ q') := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J _ y 𝔐 L _ _ z P
  obtain ⟨ρ, hρ, hdet⟩ := GlobalTheory.T.exists_sqrt_neg_disc_point E H D l Xo c Y S Ω K J y 𝔐 L z
  obtain ⟨r, hr⟩ := GlobalTheory.T.abelian_part_lie_mult_shift E H 𝔐.X 𝔐.t L z P
  refine ⟨ρ, D.p - r, D.q - r, hρ, fun k _ _ g τ => ⟨fun h => ?_, fun h => ?_⟩⟩
  · have h1 := (hdet k g τ).1 h
    have h2 := (GlobalTheory.LiePull.lieMult_pull _ _ _ _ _ _ _ _ _ P.m.cart P.m.act k (spMap g) τ D.p).mpr h1
    exact (hr k g τ D.p h2).2
  · have h1 := (hdet k g τ).2 h
    have h2 := (GlobalTheory.LiePull.lieMult_pull _ _ _ _ _ _ _ _ _ P.m.cart P.m.act k (spMap g) τ D.q).mpr h1
    exact (hr k g τ D.q h2).2

end GlobalTheory.CompanionTheory.Ar.AbPartConst
end
end
