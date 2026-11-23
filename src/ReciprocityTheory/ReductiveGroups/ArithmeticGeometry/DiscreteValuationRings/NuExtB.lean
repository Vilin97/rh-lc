module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.NuExtA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation

-- Source module: Lemmata.MiscLemmasN.Imports

section

@[expose] public section

namespace Bl.SecondBlockLemmaO

theorem goal1 :
  ∀ {V : Type} [inst : CommRing.{0} V] [inst_1 : IsDomain.{0} V] [IsDiscreteValuationRing.{0} V] {ϖ : V},
  Irreducible.{0} ϖ → IsLocalization.Away.{0, 0} ϖ (FractionRing.{0} V) := by
  intro V _ _ _ ϖ hϖ
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  have hinj := IsFractionRing.injective V (FractionRing V)
  refine (isLocalization_iff _ _).2 ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    rw [isUnit_iff_ne_zero]
    exact (map_ne_zero_iff _ hinj).2 (pow_ne_zero n hϖ0)
  · intro z
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := V) z
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have hbK : algebraMap V (FractionRing V) b ≠ 0 := (map_ne_zero_iff _ hinj).2 hb0
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
    refine ⟨⟨a * ↑u⁻¹, ⟨ϖ ^ n, n, rfl⟩⟩, ?_⟩
    have hu' : algebraMap V (FractionRing V) (↑u⁻¹ : V) * algebraMap V (FractionRing V) (↑u : V) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    show algebraMap V (FractionRing V) a / algebraMap V (FractionRing V) b *
      algebraMap V (FractionRing V) (ϖ ^ n) = algebraMap V (FractionRing V) (a * ↑u⁻¹)
    rw [div_mul_eq_mul_div, div_eq_iff hbK, hu]
    simp only [map_mul, map_pow]
    linear_combination (-(algebraMap V (FractionRing V) a * algebraMap V (FractionRing V) ϖ ^ n)) * hu'
  · intro x y h
    exact ⟨1, by rw [hinj h]⟩

end Bl.SecondBlockLemmaO
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenInj

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem away_fractionRing {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
    (hϖ : Irreducible ϖ) : IsLocalization.Away ϖ (FractionRing V) := by
  first | exact Bl.SecondBlockLemmaO.goal1 .. | (apply Bl.SecondBlockLemmaO.goal1 <;> assumption) | (intros; apply Bl.SecondBlockLemmaO.goal1 <;> assumption)

theorem gs_zero' {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) : gs f y U 0 = 0 := by
  unfold gs; split_ifs <;> simp

theorem eq_zero_of_app_fst_open {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    {X T : AlgebraicGeometry.Scheme.{0}} (p : X ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp V) [AlgebraicGeometry.Flat p]
    (t : T ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp V) [AlgebraicGeometry.IsOpenImmersion t] [Nonempty T]
    (W : X.Opens) (d : Γ(X, W)) (h : ((CategoryTheory.Limits.pullback.fst p t).app W).hom d = 0) : d = 0 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  let ϖ' : Γ(Sp V, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom ϖ
  have hrange : ∀ t' : Sp V, t' ∈ (Sp V).basicOpen ϖ' → t' ∈ Set.range t.base := by
    intro t' ht
    have ht' : t' ∈ (PrimeSpectrum.basicOpen ϖ : Set (PrimeSpectrum V)) := by
      have := basicOpen_eq_of_affine (R := CommRingCat.of V) ϖ
      rw [← this]; exact ht
    have hbot : PrimeSpectrum.asIdeal (R := V) t' = ⊥ := by
      by_contra hne
      have hmax := Ideal.IsPrime.isMaximal (PrimeSpectrum.isPrime (R := V) t') hne
      have hm := IsLocalRing.eq_maximalIdeal hmax
      apply (PrimeSpectrum.mem_basicOpen _ _).1 ht'
      rw [hm]
      exact (IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit
    obtain ⟨y⟩ := ‹Nonempty T›
    have hle : PrimeSpectrum.asIdeal (R := V) t' ≤ PrimeSpectrum.asIdeal (R := V) (t.base y) := by
      rw [hbot]; exact bot_le
    have hsp : t' ⤳ t.base y := (PrimeSpectrum.le_iff_specializes (R := V) _ _).1 ((PrimeSpectrum.asIdeal_le_asIdeal _ _).1 hle)
    exact hsp.mem_open t.isOpenEmbedding.isOpen_range ⟨y, rfl⟩
  let O : X.Opens := p ⁻¹ᵁ (Sp V).basicOpen ϖ'
  let q := IsOpenImmersion.lift t (O.ι ≫ p) (by
    rintro _ ⟨a, rfl⟩
    exact hrange _ a.2)
  let s : O.toScheme ⟶ pullback p t :=
    pullback.lift O.ι q (IsOpenImmersion.lift_fac _ _ _).symm
  have hs : s ≫ pullback.fst p t = O.ι := pullback.lift_fst _ _ _
  have hO : ∀ x ∈ W, x ∈ O → gs (𝟙 X) x W d = 0 := by
    intro x hxW hxO
    have hm : (s ≫ pullback.fst p t) ⟨x, hxO⟩ ∈ W := by rw [hs]; exact hxW
    have e1 : gs O.ι ⟨x, hxO⟩ W d = 0 := by
      rw [← hs, ← gs_pull s (pullback.fst p t) ⟨x, hxO⟩ W hm, h]
      exact gs_zero' _ _ _
    rw [gs_stalkMap O.ι ⟨x, hxO⟩ W hxW] at e1
    have : IsIso (O.ι.stalkMap ⟨x, hxO⟩) := (IsOpenImmersion.iff_isIso_stalkMap.1 inferInstance).2 _
    exact (ConcreteCategory.bijective_of_isIso (O.ι.stalkMap ⟨x, hxO⟩)).1 (e1.trans (map_zero _).symm)
  refine fn_ext fun x hx => ?_
  rw [gs_zero']
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx W.2
  have hU' : IsAffineOpen (U : X.Opens) := hU
  let g : Γ(X, U) := constFn p U ϖ
  let dU : Γ(X, U) := (X.presheaf.map (homOfLE hUW).op).hom d
  have hgs : ∀ x' ∈ U, gs (𝟙 X) x' U g = cst p x' ϖ := fun x' hx' =>
    (gs_constFn p U (𝟙 X) x' hx' ϖ).trans (by rw [Category.id_comp])
  refine (exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact X hU'.isCompact dU g ?_).elim
    fun n hn => ?_
  · refine fn_ext fun x' hx' => ?_
    have hx'U : x' ∈ U := X.basicOpen_le g hx'
    have hunit : IsUnit (X.presheaf.germ U x' hx'U g) := (X.mem_basicOpen g x' hx'U).1 hx'
    have h2 : IsUnit (cst p x' ϖ) := by
      rw [← hgs x' hx'U, gs_eq (𝟙 X) x' U hx'U]; exact hunit
    have h3 : IsUnit (gs (𝟙 (Sp V)) (p x') ⊤ ϖ') := by
      rw [cst, gs_stalkMap p x' ⊤ trivial] at h2
      exact (isUnit_map_iff (p.stalkMap x').hom _).1 h2
    have hxO : x' ∈ O := by
      show p x' ∈ (Sp V).basicOpen ϖ'
      rw [gs_eq (𝟙 (Sp V)) (p x') ⊤ trivial] at h3
      exact ((Sp V).mem_basicOpen ϖ' (p x') trivial).2 h3
    change gs (𝟙 X) x' _ ((X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom dU) = gs (𝟙 X) x' _ 0
    rw [gs_zero', gs_res (𝟙 X) x' (X.basicOpen_le g) hx']
    exact (gs_res (𝟙 X) x' hUW hx'U d).trans (hO x' (hUW hx'U) hxO)
  · have e := congrArg (gs (𝟙 X) x U) hn
    have hdU : gs (𝟙 X) x U dU = gs (𝟙 X) x W d := gs_res (𝟙 X) x hUW hxU d
    rw [gs_zero', gs_mul (𝟙 X) x U hxU, hdU] at e
    have hpow : gs (𝟙 X) x U (g ^ n) = cst p x ϖ ^ n := by
      rw [gs_eq (𝟙 X) x U hxU, map_pow, map_pow, ← gs_eq (𝟙 X) x U hxU, hgs x hxU]
    rw [hpow] at e
    exact ((cst_regular p x hϖ.ne_zero).pow n) (e.trans (mul_zero _).symm)

end ReciprocityTheory.ChartRestriction.G.DVR
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.NuExtB

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi IsLocalRing QForm
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem app_fst_eq_zero_of_snd {X T S : Scheme.{0}} (p : X ⟶ S) (t : T ⟶ S) (W : X.Opens) (d : Γ(X, W))
    (h : ((pullback.snd t p).app W).hom d = 0) : ((pullback.fst p t).app W).hom d = 0 := by
  rw [← CategoryTheory.Limits.pullbackSymmetry_hom_comp_snd, AlgebraicGeometry.Scheme.Hom.comp_app]
  erw [CommRingCat.hom_comp, RingHom.comp_apply, h, map_zero]

theorem snd_app_eq_zero {X T S : Scheme.{0}} (p : X ⟶ S) (t : T ⟶ S) (W : X.Opens) (d : Γ(X, W))
    (h : ∀ y : ↥(CategoryTheory.Limits.pullback t p : Scheme.{0}), CategoryTheory.Limits.pullback.snd t p y ∈ W → gs (CategoryTheory.Limits.pullback.snd t p) y W d = 0) :
    ((CategoryTheory.Limits.pullback.snd t p).app W).hom d = 0 := by
  refine TopCat.Presheaf.section_ext (CategoryTheory.Limits.pullback t p).sheaf _ _ _ fun y hy => ?_
  have hy' : CategoryTheory.Limits.pullback.snd t p y ∈ W := hy
  have := h y hy'
  simp only [gs, dif_pos hy'] at this
  erw [this]
  exact (map_zero _).symm

theorem secB_dvd_of_vge {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
    (hϖ : Irreducible ϖ) {D : Out.DegData V (IsLocalRing.maximalIdeal V)}
    {vK : AddValuation (FractionRing V) (WithTop ℚ)} (hv : ValOver ϖ (FractionRing V) vK) {k : ℕ}
    {α : D.toPre.X}
    {E : LB.Sec (LB.LinComb D.toPre.P.L (Out.DegPre.famφ D.toPre (FractionRing V) α) (Out.DegPre.famε k))}
    (hE : VGe D (FractionRing V) vK k α E 0) {r : V} (hr : r ≠ 0) (f : D.toPre.SecB k α)
    (hf : Out.GeneratorPullback.SecScal D.toPre.P.L (Out.DegPre.famφ D.toPre (FractionRing V) α) (Out.DegPre.famε k) E
      (D.toPre.famφB α) (Out.DegPre.famε k) f (Out.DegPre.prB D.toPre (FractionRing V)).left
      (Out.scal (Out.DegPre.BF D.toPre (FractionRing V)).hom r)) :
    ∀ j, ∃ g : Γ(D.toPre.P.A.left, LB.wchart D.toPre.P.L (D.toPre.famφB α) j),
      f.f j = Geo.Tor.constFn D.toPre.P.A.hom _ r * g := by
  obtain ⟨n, a, σ, σF, hscal, hva, hsum⟩ := hE
  have hb : ∀ i, ∃ b : V, algebraMap V (FractionRing V) b = a i := fun i => by
    obtain ⟨b, hb⟩ := mem_range_of_val_nonneg hϖ hv (a i) (by simpa using hva i)
    exact ⟨b, hb⟩
  choose b hb using hb
  have hflat : Flat D.toPre.P.A.hom := by
    have := D.toPre.P.smoothDim
    have := SmoothOfRelativeDimension.smooth D.toPre.P.g D.toPre.P.A.hom
    infer_instance
  have hjK : IsOpenImmersion (jK V) := by
    obtain ⟨ϖ₀, h₀⟩ := IsDiscreteValuationRing.exists_irreducible V
    have := away_fractionRing h₀
    exact IsOpenImmersion.of_isLocalization ϖ₀
  have hjFK : IsIso (jFK (R := V) (FractionRing V)) := by
    show IsIso (Spec.map (CommRingCat.ofHom (RingHom.id (FractionRing V))))
    rw [CommRingCat.ofHom_id, Spec.map_id]
    infer_instance
  have ht : IsOpenImmersion (TF (R := V) (FractionRing V)).hom := by
    show IsOpenImmersion (jFK (R := V) (FractionRing V) ≫ jK V)
    infer_instance
  have : Nonempty (TF (R := V) (FractionRing V)).left := ⟨IsLocalRing.closedPoint (FractionRing V)⟩

  have hBF : (Out.DegPre.BF D.toPre (FractionRing V)).hom =
      pullback.snd (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom ≫ D.toPre.P.A.hom := pullback.condition
  have hnat : ∀ {R S : CommRingCat.{0}} (g : R ⟶ S) (x : R),
      (Spec.map g).appTop.hom ((Scheme.ΓSpecIso R).inv.hom x) = (Scheme.ΓSpecIso S).inv.hom (g.hom x) := by
    intro R S g x
    exact (congrArg (fun q => q.hom x) (Scheme.ΓSpecIso_inv_naturality g)).symm
  have hTF : ∀ c : V, (TF (R := V) (FractionRing V)).hom.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom c) =
      (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv.hom (algebraMap V (FractionRing V) c) := by
    intro c
    show (jFK (R := V) (FractionRing V) ≫ jK V).appTop.hom _ = _
    rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, hnat, hnat]
    rfl

  have H : ∀ j : (LB.LinComb D.toPre.P.L (D.toPre.famφB α) (Out.DegPre.famε k)).ι,
      f.f j - constFn D.toPre.P.A.hom _ r * ∑ i, constFn D.toPre.P.A.hom _ (b i) * (σ i).f j = 0 := by
    intro j
    refine eq_zero_of_app_fst_open D.toPre.P.A.hom (TF (R := V) (FractionRing V)).hom _ _
      (app_fst_eq_zero_of_snd _ _ _ _ (snd_app_eq_zero _ _ _ _ fun y hy => ?_))
    choose J hJ using fun ψ : (Out.DegPre.BF D.toPre (FractionRing V)).left ⟶ D.toPre.P.A.left =>
      exists_chart D.toPre.P.isLB (ψ y)
    have hG : Good D.toPre.P.L y J := hJ
    set π := pullback.snd (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom
    set U := (LB.LinComb D.toPre.P.L (D.toPre.famφB α) (Out.DegPre.famε k)).U j
    obtain ⟨tj, htj⟩ : ∃ tj, (trF (L := D.toPre.P.L) (D.toPre.famφB α) (Out.DegPre.famε k) π y j
        (fun k => J (π ≫ D.toPre.famφB α k))).val = tj := ⟨_, rfl⟩
    have e_f : gs π y U (f.f j) = tj * sval f π y J :=
      (sec_trans f π y hy (hG.mem _ π)).trans (congrArg (· * sval f π y J) htj)
    have e_σ : ∀ i, gs π y U ((σ i).f j) = tj * sval (σ i) π y J := fun i =>
      (sec_trans (σ i) π y hy (hG.mem _ π)).trans (congrArg (· * sval (σ i) π y J) htj)
    have hf' : sval f (𝟙 (pullback (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom) ≫ π) y J = gs (𝟙 (pullback (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom)) y ⊤ (Out.scal (Out.DegPre.BF D.toPre (FractionRing V)).hom r) *
        sval E (𝟙 (pullback (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom)) y J := secScal_sval_c hf (𝟙 (pullback (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom)) y hG
    have hσ' : ∀ i, sval (σ i) (𝟙 (pullback (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom) ≫ π) y J = sval (σF i) (𝟙 (pullback (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom)) y J := fun i =>
      SectionScalarValuation.secScal_sval (hscal i) (𝟙 (pullback (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom)) y hG
    rw [Category.id_comp] at hf'
    simp only [Category.id_comp] at hσ'
    let bg : Fin n → Γ((pullback (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom), ⊤) := fun i =>
      (pullback.fst (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv.hom (a i))
    have hE' : sval E (𝟙 (pullback (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom)) y J = ∑ i, gs (𝟙 (pullback (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom)) y ⊤ (bg i) * sval (σF i) (𝟙 (pullback (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom)) y J :=
      SectionScalarValuation.sval_lin bg σF hsum (𝟙 (pullback (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom)) y hG
    have c1 : gs (𝟙 (pullback (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom)) y ⊤ (Out.scal (Out.DegPre.BF D.toPre (FractionRing V)).hom r) = cst (π ≫ D.toPre.P.A.hom) y r :=
      (gs_pull (𝟙 (pullback (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom)) _ y ⊤ trivial _).trans (by rw [Category.id_comp, hBF]; rfl)
    have c2 : ∀ i, gs (𝟙 (pullback (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom)) y ⊤ (bg i) = cst (π ≫ D.toPre.P.A.hom) y (b i) := by
      intro i
      refine (gs_pull (𝟙 (pullback (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom)) _ y ⊤ trivial _).trans ?_
      rw [Category.id_comp, cst, ← pullback.condition, ← gs_pull _ _ y ⊤ trivial]
      exact (congrArg (fun z => gs (pullback.fst (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom) y ⊤
          ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv.hom z)) (hb i).symm).trans
        (congrArg (gs (pullback.fst (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom) y ⊤) (hTF (b i)).symm)
    have e_sub : gs π y U (f.f j - constFn D.toPre.P.A.hom U r * ∑ i, constFn D.toPre.P.A.hom U (b i) * (σ i).f j) =
        gs π y U (f.f j) - gs π y U (constFn D.toPre.P.A.hom U r) *
          ∑ i, gs π y U (constFn D.toPre.P.A.hom U (b i)) * gs π y U ((σ i).f j) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [gs_eq π y U hy, map_sub, map_mul, map_sum]
    rw [e_sub, e_f, hf', hE', gs_constFn _ _ _ _ hy]
    simp only [e_σ, hσ', c1, c2, gs_constFn _ _ _ _ hy]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_eq_zero fun i _ => by ring
  intro j
  exact ⟨_, sub_eq_zero.1 (H j)⟩

end ReciprocityTheory.ChartRestriction.G.DVR
end
end
end
