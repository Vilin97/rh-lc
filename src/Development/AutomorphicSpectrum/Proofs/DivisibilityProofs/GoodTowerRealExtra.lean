module

public import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.NearRecordOfValue
public import Development.WeilBound.CoreStatements.FlagImmersions.CptEx
public import Development.WeilBound.CoreStatements.FlagImmersions.ExistsIntProj
public import Development.WeilBound.CoreStatements.FlagImmersions.ExistsLiftGenFibre
public import Development.WeilBound.CoreStatements.FlagImmersions.FibSandwich
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Development.WeilBound.CoreStatements.FlagImmersions.LocalCmpOf
public import Development.WeilBound.CoreStatements.FlagImmersions.LogIdealNonpos
public import Development.WeilBound.CoreStatements.FlagImmersions.MemGenFibre
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearEquivLift
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPeriodDomainParam
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsHolToFibPtAndCompFibre
public import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyUniformisationLocalPeriodStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GagaLineGeneratorEmbedding
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericOfSmoothSurjectiveStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.InducedModelMorphismCompStructureMap
public import Development.WeilBound.CoreStatements.VolumeEquality.OnePieceA
public import Development.WeilBound.CoreStatements.VolumeEquality.OnePieceB
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Tactic.Linter.Style
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.UnLocal
import Mathlib.Algebra.Azumaya.Basic
public import Development.WeilBound.CoreStatements.FlagImmersions.RootFlatOnHodgeOf
public import Development.WeilBound.CoreStatements.FlagImmersions.ExistsUnitMetric
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordOverIntOfFiniteOrder
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFormNotInCoordIdeal
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsPlaceWeightConjInvariantStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemOfAevalEqZero
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PointOverNumberFieldValue
public import Development.WeilBound.CoreStatements.VolumeEquality.ChartMeetsPoint
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Development.WeilBound.CoreStatements.FlagImmersions.ValAtOfExtends

-- Source module: Development.WeilBound.CoreStatements.FlagImmersions.HostRd

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl

namespace RootFieldNumerics.RF

theorem chiEx : ChiEx := by
  intro E _ _ _ H _
  haveI : Fact (Nat.Prime H.d) := ⟨H.d_prime⟩
  have h4 : H.d % 4 = 3 := by
    have := H.d_mod
    omega
  refine ⟨(quadraticChar (ZMod H.d)).ringHomComp (Int.castRingHom ℂ), GlobalTheory.isKroneckerChar_quadraticChar h4, ?_⟩
  have hr : rootDiscr E = hostRd E := by
    simp [rootDiscr_def, hostRd, Int.cast_abs, one_div]
  have hpos : 0 < hostRd E := by
    unfold hostRd
    apply Real.rpow_pos_of_pos
    exact abs_pos.2 (Int.cast_ne_zero.2 (NumberField.discr_ne_zero E))
  simp only [GlobalTheory.CM.logOm, hostLval]
  rw [Complex.sub_re, Complex.ofReal_re, hr, Real.log_div (by positivity) hpos.ne']
  ring

end RootFieldNumerics.RF
end
end
end

-- Source module: Development.WeilBound.CoreStatements.FlagImmersions.RangeSubIff

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl

namespace RootFieldNumerics.RF

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l}

theorem range_sub_iff {X : Scheme.{0}} (y : Sp ℂ ⟶ X) (U : Set X) : Set.range y ⊆ U ↔ centre y ∈ U := by
  refine ⟨fun h => h ⟨_, rfl⟩, ?_⟩
  rintro h _ ⟨p, rfl⟩
  obtain rfl : p = IsLocalRing.closedPoint ℂ := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
  exact h

theorem mem_of_period {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ ty)
    (hty : IsTypeFn H D.p D.q ty) (j : c.F →+* ℂ) {U : Set (Xo.XF c)} (hU : IsClopen U) (i : Fin F.n)
    {P P' : (F.Di i).La →+ (Fin g → ℂ)} (hP : IsPeriod (F.Di i) ty P) (hP' : IsPeriod (F.Di i) ty P')
    {x x' : Sp ℂ ⟶ Xo.XF c} (hx1 : x ≫ pullback.fst _ _ = F.u i P) (hx2 : x ≫ pullback.snd _ _ = spMap j)
    (hx1' : x' ≫ pullback.fst _ _ = F.u i P') (hx2' : x' ≫ pullback.snd _ _ = spMap j) (hx : centre x ∈ U) :
    centre x' ∈ U := by
  classical
  have hty' : IsTypeFn H (F.Di i).p (F.Di i).q ty := by
    rw [(F.sig i).1, (F.sig i).2]
    exact hty
  obtain ⟨B, Q, hBo, hBc, hQ, huniq⟩ := GlobalTheory.exists_period_domain_param E H (F.Di i) g ty hty'
  have hcond : spMap σ = spMap j ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
    rw [← F.over_σ i P hP, ← hx1, ← hx2, Category.assoc, Category.assoc, pullback.condition]
  let y : (Fin (F.Di i).dim → ℂ) → (Sp ℂ ⟶ Xo.XF c) := fun b =>
    if hb : b ∈ B then pullback.lift (F.u i (Q b)) (spMap j) ((F.over_σ i _ (hQ.1 b hb)).trans hcond) else x
  have hy1 : ∀ b ∈ B, y b ≫ pullback.fst _ _ = F.u i (Q b) := fun b hb => by
    simp only [y, dif_pos hb, pullback.lift_fst]
  have hy2 : ∀ b ∈ B, y b ≫ pullback.snd _ _ = spMap j := fun b hb => by
    simp only [y, dif_pos hb, pullback.lift_snd]
  have hhol : IsHolTo B y :=
    GlobalTheory.HolFibre.isHolTo_of_isPullback (IsPullback.of_hasPullback _ _)
      (GlobalTheory.LocLift.isHolTo_congr (F.hol i _ B Q hBo hQ).1 hy1)
      (GlobalTheory.LocLift.isHolTo_congr (GlobalTheory.HolFibre.isHolTo_const hBo (spMap j)) hy2)
  have hfind : ∀ R, IsPeriod (F.Di i) ty R → ∀ z : Sp ℂ ⟶ Xo.XF c, z ≫ pullback.fst _ _ = F.u i R →
      z ≫ pullback.snd _ _ = spMap j → ∃ b ∈ B, y b = z := by
    intro R hR z hz1 hz2
    obtain ⟨b, ⟨hb, h, hh⟩, -⟩ := huniq R hR
    refine ⟨b, hb, pullback.hom_ext ?_ ?_⟩
    · rw [hy1 b hb, hz1]
      exact (F.fibre i _ _ (hQ.1 b hb) hR).2 ⟨LinearEquiv.refl _ _, h, fun _ _ => rfl,
        fun a _ => ⟨0, by simp⟩, fun a => ⟨0, by simp⟩, hh⟩
    · rw [hy2 b hb, hz2]
  obtain ⟨b, hb, e⟩ := hfind P hP x hx1 hx2
  obtain ⟨b', hb', e'⟩ := hfind P' hP' x' hx1' hx2'
  by_contra hn
  let W : (Xo.XF c).Opens := ⟨U, hU.isOpen⟩
  let W' : (Xo.XF c).Opens := ⟨Uᶜ, hU.compl.isOpen⟩
  obtain ⟨t, -, ht, ht'⟩ := hBc.isPreconnected _ _ (hhol W 0).1 (hhol W' 0).1
    (fun t ht => by
      by_cases h : centre (y t) ∈ U
      · exact Or.inl ⟨ht, GagaRat.top_le_of_centre_mem (show centre (y t) ∈ W from h)⟩
      · exact Or.inr ⟨ht, GagaRat.top_le_of_centre_mem (show centre (y t) ∈ W' from h)⟩)
    ⟨b, hb, hb, GagaRat.top_le_of_centre_mem (show centre (y b) ∈ W from e ▸ hx)⟩
    ⟨b', hb', hb', GagaRat.top_le_of_centre_mem (show centre (y b') ∈ W' from e' ▸ hn)⟩
  exact (GagaRat.centre_mem ht'.2 : centre (y t) ∈ W') (GagaRat.centre_mem ht.2 : centre (y t) ∈ W)

theorem over_const [NumberField c.F] {m : ℕ} {T : Set (Fin m → ℂ)} {y : (Fin m → ℂ) → (Sp ℂ ⟶ Xo.XF c)}
    (hTc : IsPreconnected T) (hy : IsHolTo T y) {b b' : Fin m → ℂ} (hb : b ∈ T) (hb' : b' ∈ T) :
    y b ≫ pullback.snd _ _ = y b' ≫ pullback.snd _ _ := by
  have hemb : ∀ p : Sp ℂ ⟶ Xo.XF c, ∃ κ : c.F →+* ℂ, p ≫ pullback.snd _ _ = spMap κ := fun p =>
    ⟨(Spec.preimage (p ≫ pullback.snd _ _)).hom, by
      unfold spMap
      rw [CommRingCat.ofHom_hom, Spec.map_preimage]⟩
  choose κ hκy using fun b => hemb (y b)
  have hd : ∀ r : 𝓞 c.F, DifferentiableOn ℂ (fun b => κ b (r : c.F)) T := fun r => by
    have h3 := (GagaRat.isHolTo_comp (pullback.snd _ _) hy ⊤ ((Scheme.ΓSpecIso (CommRingCat.of c.F)).inv (r : c.F))).2
    have hset : T ⊆ {b ∈ T | ⊤ ≤ (y b ≫ pullback.snd _ _) ⁻¹ᵁ ⊤} := fun b hb => ⟨hb, le_top⟩
    refine (h3.mono hset).congr fun b _ => ?_
    show κ b (r : c.F) = valAt' (y b ≫ pullback.snd _ _) ⊤ _
    rw [hκy b]
    exact (PullbackSections.valAt'_spMap (κ b) (r : c.F)).symm
  rw [hκy, hκy, GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.embedding_const_preconnected hTc κ hd hb hb']

theorem periodOf : PeriodOf := by
  intro hG E _ _ _ H D l Xo c _ Y U Z hp hq hU _ hgeom
  classical
  have hN : N1c := hG.1.2.2.1
  obtain ⟨g, ty, hty⟩ := GlobalTheory.AllClasses.exists_isTypeFn H D.p D.q
  obtain ⟨FU⟩ := hN E H D l Xo (algebraMap (KA l) ℂ) g ty (by omega) rfl hty
  let s : Xo.XF c ⟶ Sp c.F := pullback.snd _ _
  have hsm : SmoothOfRelativeDimension D.dim s :=
    (smoothOfRelativeDimension_isStableUnderBaseChange D.dim).of_isPullback (IsPullback.of_hasPullback _ _) Xo.smooth
  have hsm' : Smooth s := SmoothOfRelativeDimension.smooth D.dim s
  haveI := Y.jQ_open
  haveI : IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 c.F)) (S := c.F)
  haveI : IsPreimmersion Y.j := by
    show IsPreimmersion (Y.jQ ≫ pullback.fst _ _)
    infer_instance
  have hξ : IsCptGen Z.ξ₀ := GlobalTheory.T.generic_of_smooth_surjective c.F _ _ _ _ _ Y.j s hsm' rfl Z.gen (Y.j.stalkMap_surjective _)
  letI : Algebra c.F Z.Ω := Z.inc.toAlgebra
  have hcl : ConstClosed c.F Z.Ω := by
    rintro a ⟨f, hf, hfa⟩
    obtain ⟨x, hx⟩ := hgeom a ⟨f, hf, hfa⟩
    exact ⟨x, 1, one_ne_zero, by rw [map_one, mul_one]; exact hx.symm⟩
  have hover : ∀ x : Sp ℂ ⟶ Xo.XF c, x ≫ s = spMap (algebraMap c.F ℂ) →
      under x ≫ Xo.s = spMap (algebraMap (KA l) ℂ) := by
    intro x hx
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    erw [hx]
    exact GagaRat.spMap_comp _ _
  have hexF : ∀ x : Sp ℂ ⟶ Xo.XF c, ∃ r : ℂ, (x ≫ s ≠ spMap (algebraMap c.F ℂ) → r = 0) ∧
      (x ≫ s = spMap (algebraMap c.F ℂ) → ∀ k P, IsPeriod (FU.Di k) ty P → FU.u k P = under x → r = ((k : ℕ) : ℂ)) := by
    intro x
    by_cases hx : x ≫ s = spMap (algebraMap c.F ℂ)
    · obtain ⟨k, P, hP, e⟩ := FU.onto _ (hover x hx)
      exact ⟨((k : ℕ) : ℂ), fun h => absurd hx h, fun _ k' P' hP' e' => by rw [FU.disj k k' P P' hP hP' (e.trans e'.symm)]⟩
    · exact ⟨0, fun _ => rfl, fun h => absurd h hx⟩
  choose F hF0 hF using hexF
  have hconst := SheetDecomposition.One.const_of_hol (algebraMap c.F ℂ) s Z.ξ₀ ⊤ F D.dim hsm Z.over_inc hξ hcl (by
    intro m T y hT hc hy _ b₁ hb₁ b₂ hb₂
    have hall : ∀ b ∈ T, y b ≫ s = y b₁ ≫ s := fun b hb => over_const hc hy hb hb₁
    by_cases h : y b₁ ≫ s = spMap (algebraMap c.F ℂ)
    · obtain ⟨i, hi⟩ := GlobalTheory.T.family_uniformisation_local_period E H D l Xo _ g ty FU m T (fun b => under (y b)) hT hc ⟨b₁, hb₁⟩
        (fun b hb => hover _ ((hall b hb).trans h)) (GagaRat.isHolTo_comp _ hy)
      have key : ∀ b ∈ T, F (y b) = ((i : ℕ) : ℂ) := fun b hb => by
        obtain ⟨B', P, -, m1, -, hP, e⟩ := hi b hb
        exact hF _ ((hall b hb).trans h) i (P b) (hP.1 b m1) (e b m1)
      rw [key b₁ hb₁, key b₂ hb₂]
    · rw [hF0 _ h, hF0 _ (by rw [hall b₂ hb₂]; exact h)])
  obtain ⟨x, hx, hxU⟩ := SheetDecomposition.One.exists_point (algebraMap c.F ℂ) s ⟨U, hU.isOpen⟩ (q := genPt Z.ξ₀) Z.genPt_mem
  have hxU' : centre x ∈ U := GagaRat.centre_mem hxU
  obtain ⟨i, P₀, hP₀, e₀⟩ := FU.onto _ (hover x hx)
  refine ⟨g, ty, FU, i, hty, fun y hy => ?_⟩
  rw [range_sub_iff]
  constructor
  · intro hyU
    obtain ⟨k, P, hP, e⟩ := FU.onto _ (hover y hy)
    have := hconst y x hy hx le_top le_top ((Z.closure _).1 hyU) ((Z.closure _).1 hxU')
    rw [hF _ hy k P hP e, hF _ hx i P₀ hP₀ e₀] at this
    obtain rfl : k = i := Fin.ext (Nat.cast_injective this)
    exact ⟨P, hP, e.symm⟩
  · rintro ⟨P, hP, e⟩
    exact mem_of_period FU hty _ hU i hP₀ hP e₀.symm hx e hy hxU'

end RootFieldNumerics.RF
end
end
end

-- Source module: Development.WeilBound.CoreStatements.FlagImmersions.UnitAtOfSpan

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
  GlobalTheory.CompanionTheory.Ar.Flat.UnitChart

namespace RootFieldNumerics.RF

namespace Smooth

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem mem_genFibre (z : Spec (CommRingCat.of ℂ) ⟶ X) (hc : genPt ξ ⤳ centre z) :
    (⟨centre z, hc⟩ : Cpt ξ) ∈ genFibre ℤ ξ := by
  intro o ho
  have h1 : ValAt ξ z (o : Ω) (o : ℂ) := LiesOver.valAt_int hc o
  have h2 := CxVal.inv h1 (by exact_mod_cast ho)
  have h3 := CxVal.mul h1 h2
  have h0 : (o : Ω) ≠ 0 := by
    intro h
    have h4 : ValAt ξ z (0 : Ω) (0 : ℂ) := by simpa using LiesOver.valAt_int hc 0
    rw [h] at h1
    exact ho (by exact_mod_cast CxVal.unique h1 h4)
  obtain ⟨_, s, e, -⟩ := h1
  obtain ⟨_, s', e', -⟩ := h2
  exact ⟨by simpa using h0, ⟨s, by simpa using e⟩, ⟨s', by simpa using e'⟩⟩

theorem val_ne_zero {z : Spec (CommRingCat.of ℂ) ⟶ X} {hc : genPt ξ ⤳ centre z} {u : Ω} {r : ℂ}
    (hu : unitAt ξ ⟨centre z, hc⟩ u) (hr : ValAt ξ z u r) : r ≠ 0 := by
  obtain ⟨s, hs⟩ := hu.2.2
  have h1 := CxVal.mul hr (⟨hc, s, hs, rfl⟩ : ValAt ξ z u⁻¹ _)
  rw [mul_inv_cancel₀ hu.1] at h1
  exact left_ne_zero_of_mul_eq_one (CxVal.unique h1 (CxVal.one hc))

theorem unitAt_of_span {p : Cpt ξ} {s t : Ω} (hs : s ≠ 0) (ht : t ≠ 0)
    (h : Submodule.span (regAt ξ p) {s} = Submodule.span (regAt ξ p) {t}) : unitAt ξ p (s / t) := by
  have key : ∀ {s t : Ω}, t ≠ 0 → s ∈ Submodule.span (regAt ξ p) {t} → s / t ∈ regAt ξ p := by
    intro s t ht hm
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 hm
    have : s / t = r := by
      rw [← hr]
      exact mul_div_cancel_right₀ _ ht
    rw [this]
    exact r.2
  refine ⟨div_ne_zero hs ht, key ht (h ▸ Submodule.mem_span_singleton_self s), ?_⟩
  rw [inv_div]
  exact key hs (h ▸ Submodule.mem_span_singleton_self t)

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}

theorem pres_on (hT : CoordTie ℤ ξ fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) {L : Lat ξ Ω} {a : K → ℤ} {e₀ c₀ : Ω}
    (hD : L.IsDegOn Set.univ y a e₀) (hg : ∀ p ∈ genFibre ℤ ξ, L.IsGenAt p (c₀ * e₀))
    {w : (Σ k, J k) → ℂ} (hw : w ∈ mcPts (mCoordIdeal y)) :
    ∃ g h dg dh, Pres y a c₀ g h dg dh ∧ evC w g ≠ 0 ∧ evC w h ≠ 0 := by
  classical
  obtain ⟨z, hz, hco⟩ := SheetDecomposition.ChartForm.exists_point hT w
    (fun k => (hw.1 k).imp fun _ h => IsUnit.mk0 _ h) (fun g hg => by rw [← evC_eq]; exact hw.2 g hg)
  choose c hc using hco.1
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => (hco.2 k _ (hc k)).1
  have hY : ∀ m : K → ℕ, (∏ k, y ⟨k, c k⟩ ^ m k) ≠ 0 := fun m =>
    Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hy k)
  have hW : ∀ m : K → ℕ, (∏ k, w ⟨k, c k⟩ ^ m k) ≠ 0 := fun m =>
    Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k).ne_zero
  have hxc : (∏ k, y ⟨k, c k⟩) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hy k
  let p : Cpt ξ := ⟨centre z, hz⟩
  have hch : InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c p := by
    refine ⟨hxc, fun c' => ?_⟩
    show (∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, c k⟩ ∈ _
    rw [← Finset.prod_div_distrib]
    refine Subring.prod_mem _ fun k _ => ?_
    obtain ⟨r, ⟨_, s, e, -⟩, -⟩ := (hco.2 k _ (hc k)).2 (c' k)
    exact ⟨s, e⟩
  have hYa : (∏ k, y ⟨k, c k⟩ ^ a k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy k)
  have hgen := hg p (mem_genFibre z hz)
  have hu : unitAt ξ p (c₀ / ∏ k, y ⟨k, c k⟩ ^ a k) := by
    have := unitAt_of_span hgen.1 (mul_ne_zero hYa hD.1) (hgen.2.symm.trans (hD.2 p trivial c hch))
    rwa [mul_div_mul_right _ _ hD.1] at this
  obtain ⟨U, hU, hmem⟩ := hT.affine c hxc
  have hpU : p.1 ∈ U := (hmem _).2 ⟨hz, hch⟩
  have hgU : genPt ξ ∈ U := (hmem _).2 ⟨specializes_rfl, CoordBase.inChart_gen hT hxc⟩
  obtain ⟨s, hs⟩ := hu.2.1
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨p.1, hpU⟩ : U)
  have hloc := hU.isLocalization_stalk ⟨p.1, hpU⟩
  obtain ⟨⟨t, f⟩, e⟩ := IsLocalization.surj (hU.primeIdealOf ⟨p.1, hpU⟩).asIdeal.primeCompl s
  have e' : s * X.presheaf.germ U p.1 hpU f.1 = X.presheaf.germ U p.1 hpU t := e
  have hfu : IsUnit (X.presheaf.germ U p.1 hpU f.1) := IsLocalization.map_units (X.presheaf.stalk p.1) f
  have h2 := congrArg (genMap ξ p) e'
  rw [map_mul, hs, CoordBase.genMap_germ_val U hgU p hpU, CoordBase.genMap_germ_val U hgU p hpU] at h2
  have hfu' : unitAt ξ p (CoordBase.val U hgU f.1) := by
    rw [← CoordBase.genMap_germ_val U hgU p hpU]
    obtain ⟨v, hv⟩ := hfu
    rw [← hv]
    exact ⟨(v.isUnit.map _).ne_zero, ⟨_, rfl⟩, ⟨v⁻¹.val, map_units_inv _ v⟩⟩
  have htu : unitAt ξ p (CoordBase.val U hgU t) := h2 ▸ ZUnit.mul hu hfu'
  have hin : ∀ b : Γ(X, U), CoordBase.val U hgU b ∈ chartRingZ y c := fun b => by
    rw [← CptIn.Intr.segre_chart y c hy]
    exact (CoordBase.mem_adjoin_iff hT hxc hU hmem hgU _).2 ⟨b, rfl⟩
  obtain ⟨δt, Gt, ht1, ht2, ht3⟩ := LiesOver.exists_form_valAt hz hco c hy hc (hin t)
  obtain ⟨δf, Gf, hf1, hf2, hf3⟩ := LiesOver.exists_form_valAt hz hco c hy hc (hin f.1)
  have nt : evC w Gt ≠ 0 := fun h => val_ne_zero htu ht3 (by rw [h, zero_div])
  have nf : evC w Gf ≠ 0 := fun h => val_ne_zero hfu' hf3 (by rw [h, zero_div])
  have hm : ∀ m : K → ℕ, evC w (cMon c m) ≠ 0 := fun m => by
    rw [evC_eq, aeval_cMon]
    exact hW m
  refine ⟨Gt * cMon c δf * cMon c fun k => (a k).toNat, Gf * cMon c δt * cMon c fun k => (-a k).toNat, _, _,
    ⟨homog_mul (homog_mul ht1 (homog_cMon _ _)) (homog_cMon _ _),
      homog_mul (homog_mul hf1 (homog_cMon _ _)) (homog_cMon _ _), fun k => ?_, ?_⟩, ?_, ?_⟩
  · simp only [Pi.add_apply]
    omega
  · have ea : (∏ k, y ⟨k, c k⟩ ^ (a k).toNat) = (∏ k, y ⟨k, c k⟩ ^ a k) * ∏ k, y ⟨k, c k⟩ ^ (-a k).toNat := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hy k)]
      congr 1
      omega
    simp only [map_mul, aeval_cMon, ht2, hf2]
    rw [ea, ← h2]
    field_simp
  · rw [evC_mul, evC_mul]; exact mul_ne_zero (mul_ne_zero nt (hm _)) (hm _)
  · rw [evC_mul, evC_mul]; exact mul_ne_zero (mul_ne_zero nf (hm _)) (hm _)

end Smooth

open Smooth in
theorem smoothLine : SmoothLine := by
  intro X Ω _ ξ K _ J _ y F' _ _ ψ L a e₀ c₀ cinf n _ hT _ hO _ hvar hD hg hpos hconj
  obtain ⟨A₀, ha, hsm, hcj, hn⟩ := exists_unit_metric y a c₀ fun w hw => by
    by_cases h : w ∈ mcPts (mCoordIdeal y)
    · exact pres_on hT hD hg h
    · exact pres_off hvar.2.1.2.1 a c₀ hw h
  obtain ⟨u, hu, huc⟩ := GlobalTheory.T.exists_place_weight_conj_invariant K J Ω F' y ψ (fun σ => Real.log (cinf σ)) hO
  have huc' := huc fun σ => by simp only [hconj]
  refine ⟨hu.shift A₀, ?_, ?_, fun z => ?_, ?_, fun w hw => ?_⟩
  · show A₀.a + 0 = a
    rw [add_zero, ha]
  · exact ContDiffOn.mul hsm hu.smooth.neg.exp
  · show A₀.h _ * Real.exp (-u _) = A₀.h z * Real.exp (-u z)
    rw [hcj z, huc' z]
  · intro σ z g h dg dh hz h1 h2 h3 h4
    have h3' : ∀ k, (dg k : ℤ) - dh k = a k := fun k => by
      rw [h3 k]
      show (A₀.a + 0) k = a k
      rw [add_zero, ha]
    rw [hn z hz.1 g h dg dh ⟨h1, h2, h3', h4⟩]
    show _ = cinf σ * (A₀.h z * Real.exp (-u z)) * _
    rw [(hu.near σ z hz).self_of_nhds, Real.exp_neg, Real.exp_log (hpos σ)]
    have := (hpos σ).ne'
    field_simp
  · obtain ⟨g, h, dg, dh, hP, -, hh⟩ := pres_on hT hD hg hw
    exact ⟨g, h, dg, dh, hP.1, hP.2.1, hP.2.2.1, hP.2.2.2, hh⟩

end RootFieldNumerics.RF
end
end
end

-- Source module: Development.WeilBound.CoreStatements.FlagImmersions.GlobalModelTowerFinalCondition

section

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)

namespace RootFieldNumerics

theorem rootFlatOnHodge (hFD : Fl.FlatDegree) (hG : Given) : Flat.RootFlatOnHodge :=
  RF.rootFlatOnHodge_of RF.cptEx RF.periodOf RF.smoothLine
    (RF.localCmp_of RF.pointEx RF.valuePhi RF.intFrames RF.fibSandwich) RF.chiEx RF.numerics hFD hG

theorem global_model_tower_final_condition : Fl.FlatDegree → Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem), IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → ∀ a τ, ∃ R : Flat.RootFlat (T.M 2 a) τ, Flat.NearRecord (D.p + D.q) T.bad (hostRd E) (hostLval H) R.ht := by
  intro hFD hG E _ _ _ _ H D Xo l c Y _ T o II hY _ _ _ _ a τ
  exact Flat.OnHodge.tower (rootFlatOnHodge hFD hG) hY ⟨o.toTowerOrigin, o.omVB⟩ a τ

end RootFieldNumerics
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GoodTowerRealExtra

section

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)

theorem _root_.GlobalTheory.CompanionTheory.Relay.good_tower_real_extra : Fl.FlatDegree → Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem), IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → ∀ a τ, ∃ R : Flat.RootFlat (T.M 2 a) τ, Flat.NearRecord (D.p + D.q) T.bad (hostRd E) (hostLval H) R.ht := by
  first | exact @RootFieldNumerics.global_model_tower_final_condition | exact RootFieldNumerics.global_model_tower_final_condition
end
end
