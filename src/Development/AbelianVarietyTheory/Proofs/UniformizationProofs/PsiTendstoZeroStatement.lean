module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SecEqZeroOfThickeningsOfSection
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValuesNatural
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUnitValEqMul
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.StalkMapInjectiveOfFlat
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.JKAppTopInjective
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiInIffScalarMem
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsMemPowOfRatioOfTorsionFree

section

@[expose] public section

namespace GlobalTheory

theorem exists_mem_pow_of_ratio_of_torsionFree :
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (O : Type) [CommRing O]
      (io : V →+* O), (∀ v : V, v ≠ 0 → ∀ x : O, io v * x = 0 → x = 0) →
      ∀ (f h : O) (p q : V) (m n : ℕ), q ≠ 0 → io q * f = io p * h →
      f ∈ (IsLocalRing.maximalIdeal V ^ (m + n)).map io →
      h ∉ (IsLocalRing.maximalIdeal V ^ (m + 1)).map io →
      ∃ r ∈ IsLocalRing.maximalIdeal V ^ n, p = r * q := by
  intro V _ _ _ O _ io htf f h p q m n hq e hf hh
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hm : IsLocalRing.maximalIdeal V = Ideal.span {π} := hπ.maximalIdeal_eq
  have hπn : π ^ n ∈ IsLocalRing.maximalIdeal V ^ n := by
    rw [hm, Ideal.span_singleton_pow]; exact Ideal.mem_span_singleton_self _
  have key : π ^ n * q ∣ p → ∃ r ∈ IsLocalRing.maximalIdeal V ^ n, p = r * q := by
    rintro ⟨c, hc⟩
    exact ⟨π ^ n * c, Ideal.mul_mem_right _ _ hπn, by rw [hc]; ring⟩
  rcases ValuationRing.dvd_total (π ^ n * q) p with hd | ⟨c, hc⟩
  · exact key hd
  by_cases hu : IsUnit c
  · apply key
    obtain ⟨u, rfl⟩ := hu
    exact ⟨(u⁻¹ : Vˣ), by rw [hc, mul_assoc, Units.mul_inv, mul_one]⟩
  exfalso
  apply hh
  have hcm : c ∈ IsLocalRing.maximalIdeal V := hu
  rw [hm, Ideal.mem_span_singleton] at hcm
  obtain ⟨d, rfl⟩ := hcm
  have hp : p ≠ 0 := by
    rintro rfl
    exact mul_ne_zero (pow_ne_zero n hπ.ne_zero) hq (by simpa using hc)
  rw [hm, Ideal.span_singleton_pow, Ideal.map_span, Set.image_singleton,
    Ideal.mem_span_singleton] at hf ⊢
  obtain ⟨g, rfl⟩ := hf
  refine ⟨io d * g, ?_⟩
  have h0 := htf p hp (h - io (π ^ (m + 1)) * (io d * g)) (by
    have hc' := congrArg io hc
    simp only [map_mul, map_pow] at hc' e ⊢
    linear_combination (io π ^ m * g) * hc' - e)
  exact sub_eq_zero.mp h0

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsOrderTranslates

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory

theorem stalkMap_mem_map_base {R : Type} [CommRing R] (I : Ideal R) {Z Z' : Scheme.{0}}
    (p : Z ⟶ Spec (CommRingCat.of R)) (p' : Z' ⟶ Spec (CommRingCat.of R)) (ρ : Z' ⟶ Z) (h : ρ ≫ p = p') (z : Z')
    (a : Z.presheaf.stalk (ρ z))
    (ha : a ∈ I.map ((Z.presheaf.germ ⊤ (ρ z) trivial).hom.comp
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom))) :
    (ρ.stalkMap z).hom a ∈ I.map ((Z'.presheaf.germ ⊤ z trivial).hom.comp
      (p'.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)) := by
  subst h
  have := Ideal.mem_map_of_mem (ρ.stalkMap z).hom ha
  rw [Ideal.map_map] at this
  convert this using 2
  ext r
  exact (Scheme.Hom.germ_stalkMap_apply ρ ⊤ z trivial _).symm

theorem map_base_eq_bot {R : Type} [CommRing R] (I : Ideal R) {Z : Scheme.{0}}
    (ρ : Z ⟶ Spec (CommRingCat.of (R ⧸ I))) (z : Z) :
    I.map ((Z.presheaf.germ ⊤ z trivial).hom.comp
      ((ρ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).appTop.hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)) = ⊥ := by
  rw [Ideal.map_eq_bot_iff_le_ker]
  intro r hr
  have e := congrArg (fun q => q.hom r)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.mk I)))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
    Ideal.Quotient.eq_zero_iff_mem.2 hr, map_zero] at e
  rw [RingHom.mem_ker, Scheme.Hom.comp_appTop]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply]
  erw [← e]
  simp only [map_zero]

theorem exists_order_translates : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDVR V → ∀ (D : DegPre V) (k : ℕ) (f₀ : SecBT D (𝟙_ _) k 0), (∃ j, f₀.f j ≠ 0) → ∃ m : ℕ, ∀ χ : D.X, ∃ (z : (𝟙_ _ ⊗ D.P.A).left) (J : _), Good D.P.L z J ∧ sval f₀ (lift (fst (𝟙_ _) D.P.A) (snd (𝟙_ _) D.P.A * cT D _ χ)).left z J ∉ (IsLocalRing.maximalIdeal V ^ (m + 1)).map (((𝟙_ _ ⊗ D.P.A).left.presheaf.germ ⊤ z trivial).hom.comp (((𝟙_ _ ⊗ D.P.A).hom.appTop.hom).comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom)) := by
  intro V _ _ _ hV D k f₀ ⟨j, hj⟩
  haveI := hV.1
  haveI := D.P.isAb.smooth
  haveI := D.P.isAb.geomConnected
  haveI : IsAffine (𝟙_ (Over (Spec (CommRingCat.of V)))).left :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of V)))
  haveI : IsNoetherianRing Γ((𝟙_ (Over (Spec (CommRingCat.of V)))).left, ⊤) :=
    isNoetherianRing_of_ringEquiv V (Scheme.ΓSpecIso (CommRingCat.of V)).commRingCatIsoToRingEquiv.symm
  obtain ⟨m, z₀, J₀, hJ₀, h₀⟩ : ∃ (m : ℕ) (z : (𝟙_ _ ⊗ D.P.A).left) (J : _), Good D.P.L z J ∧
      sval f₀ (𝟙 _) z J ∉ (IsLocalRing.maximalIdeal V ^ (m + 1)).map (((𝟙_ _ ⊗ D.P.A).left.presheaf.germ ⊤ z trivial).hom.comp (((𝟙_ _ ⊗ D.P.A).hom.appTop.hom).comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom)) := by
    by_contra hc
    push Not at hc
    refine hj (sec_eq_zero_of_sval_finite_level V (IsLocalRing.maximalIdeal V) (𝟙_ _) D.P.A ?_ _ D.P.L D.P.isLB
      _ _ _ f₀ ?_ j)
    · intro r hr
      let e : V ≃+* Γ(Spec (CommRingCat.of V), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of V)).commRingCatIsoToRingEquiv.symm
      have h1 : r ∈ Ideal.jacobson (⊥ : Ideal V) := by
        rwa [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
      have h2 := Ideal.mem_map_of_mem e.toRingHom h1
      rw [Ideal.map_jacobson_of_bijective (f := e.toRingHom) e.bijective, Ideal.map_bot] at h2
      exact h2
    · rintro e Z r ⟨ρ, hρ⟩ z J hJ
      obtain ⟨g, hs, -⟩ := values_natural _ _ _ _ D.P.L _ (famφT D (𝟙_ _) 0) (DegPre.famε k) (𝟙 _) r z J hJ
      have h1 := stalkMap_mem_map_base _ _ _ r hρ.symm z _ (hc e _ _ g)
      rw [← hs f₀, Category.comp_id, map_base_eq_bot] at h1
      exact h1
  refine ⟨m, fun χ => ?_⟩
  let σ : 𝟙_ _ ⊗ D.P.A ⟶ 𝟙_ _ ⊗ D.P.A := lift (fst (𝟙_ _) D.P.A) (snd (𝟙_ _) D.P.A * (cT D _ χ)⁻¹)
  let τ : 𝟙_ _ ⊗ D.P.A ⟶ 𝟙_ _ ⊗ D.P.A := lift (fst (𝟙_ _) D.P.A) (snd (𝟙_ _) D.P.A * cT D _ χ)
  have hστ : σ ≫ τ = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · exact toUnit_unique _ _
    · have : σ ≫ cT D _ χ = cT D _ χ := by
        rw [cT, ← Category.assoc, toUnit_unique (σ ≫ toUnit _) (toUnit _)]
      rw [Category.assoc, lift_snd, MonObj.comp_mul, this, lift_snd, inv_mul_cancel_right, Category.id_comp]
  obtain ⟨g, hs, -⟩ := values_natural _ _ _ _ D.P.L _ (famφT D (𝟙_ _) 0) (DegPre.famε k) τ.left σ.left z₀ J₀ hJ₀
  refine ⟨_, _, g, fun hm => h₀ ?_⟩
  have h1 := stalkMap_mem_map_base _ _ _ σ.left (Over.w σ) z₀ _ hm
  have h2 : σ.left ≫ τ.left = 𝟙 _ := congrArg CommaMorphism.left hστ
  rw [← hs f₀, h2] at h1
  exact h1

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FromSpecStalkComp

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.LevelVanishing

theorem fromSpecStalk_comp {R : Type} [CommRing R] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) (z : Y) :
    Y.fromSpecStalk z ≫ p =
      Spec.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appTop ≫ Y.presheaf.germ ⊤ z trivial) := by
  rw [Spec.map_comp, Spec.map_comp, ← Scheme.fromSpecStalk_toSpecΓ, Category.assoc, Category.assoc,
    ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

theorem sval_mem_map {R : Type} [CommRing R] (I : Ideal R) {X Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R))
    {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} (d : LB.Sec (LB.LinComb L φ ε))
    (H : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y), (∃ ρ : Z ⟶ Spec (CommRingCat.of (R ⧸ I)),
      ρ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) = r ≫ p) → ∀ (z : Z) (J), Good L z J → sval d r z J = 0)
    (z : Y) (J) (hJ : Good L z J) :
    sval d (𝟙 _) z J ∈ I.map ((Y.presheaf.germ ⊤ z trivial).hom.comp
      ((p.appTop.hom).comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)) := by
  set ψ := (Y.presheaf.germ ⊤ z trivial).hom.comp
      ((p.appTop.hom).comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) with hψ
  by_cases htop : I.map ψ = ⊤
  · rw [htop]; trivial
  have : Nontrivial (Y.presheaf.stalk z ⧸ I.map ψ) := Ideal.Quotient.nontrivial_iff.2 htop
  have : IsLocalRing (Y.presheaf.stalk z ⧸ I.map ψ) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  let Q : CommRingCat.{0} := CommRingCat.of (Y.presheaf.stalk z ⧸ I.map ψ)
  let q : Y.presheaf.stalk z ⟶ Q := CommRingCat.ofHom (R := Y.presheaf.stalk z) (Ideal.Quotient.mk (I.map ψ))
  have : IsLocalHom q.hom := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  let r : Spec Q ⟶ Y := Spec.map q ≫ Y.fromSpecStalk z
  let w : Spec Q := IsLocalRing.closedPoint Q
  have hw : r w = z := by
    rw [Scheme.Hom.comp_apply, Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]
  have hl : ∃ ρ : Spec Q ⟶ Spec (CommRingCat.of (R ⧸ I)),
      ρ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) = r ≫ p := by
    refine ⟨Spec.map (CommRingCat.ofHom (Ideal.quotientMap (I.map ψ) ψ Ideal.le_comap_map)), ?_⟩
    rw [Category.assoc, fromSpecStalk_comp, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
  choose I' hI' using fun χ : Spec Q ⟶ X => exists_chart hL (χ w)
  have hz : z ∈ LB.wchart L φ (fun k => J (𝟙 _ ≫ φ k)) := hJ.mem φ (𝟙 _)
  have hm : r w ∈ LB.wchart L φ (fun k => J (𝟙 _ ≫ φ k)) := hw ▸ hz
  have e := sec_trans d r w (j := fun k => J (𝟙 _ ≫ φ k)) hm (Good.mem hI' φ r)
  have e0 : gs r w (LB.wchart L φ (fun k => I' (r ≫ φ k))) (d.f (fun k => I' (r ≫ φ k))) = 0 := H _ r hl w I' hI'
  rw [e0, mul_zero] at e
  replace e := (Scheme.Hom.germ_stalkMap_apply r _ w hm _).trans ((gs_eq r w _ hm _).symm.trans e)
  have e1 := congrArg (fun t => t.hom (d.f (fun k => J (𝟙 _ ≫ φ k))))
    (Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk q _ hm)
  simp only [Scheme.stalkClosedPointTo, CommRingCat.hom_comp, RingHom.comp_apply] at e1
  refine Ideal.Quotient.eq_zero_iff_mem.1 ((congrArg _ (gs_eq (𝟙 Y) z _ hz _)).trans ?_)
  exact e1.symm.trans ((congrArg (stalkClosedPointIso Q).hom.hom e).trans (map_zero _))

theorem main : (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (k : ℕ) (σ : U.SecGT (𝟙_ _) k) f, U.ExpT (𝟙_ _) k σ f → ∀ e : ℕ, ∃ s : Finset D.X, ∀ α ∉ s, ∀ (z : (𝟙_ _ ⊗ D.P.A).left) (J), Good D.P.L z J → sval (f α) (𝟙 _) z J ∈ (IsLocalRing.maximalIdeal V ^ (e + 1)).map (((𝟙_ _ ⊗ D.P.A).left.presheaf.germ ⊤ z trivial).hom.comp (((𝟙_ _ ⊗ D.P.A).hom.appTop.hom).comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom))) := by
  intro V _ _ _ _ D A G _ _ U k σ f h e
  obtain ⟨s, hs⟩ := h e
  refine ⟨s, fun α hα z J hJ => sval_mem_map _ (𝟙_ _ ⊗ D.P.A).hom D.P.isLB (f α) ?_ z J hJ⟩
  refine GlobalTheory.LiftTest.main V _ D e G (U.gt e) (𝟙_ _ ⊗ D.P.A) (snd _ _) _ D.P.L D.P.isLB _ _ _ (f α) ?_
  intro Z x r hr z J hJ
  choose JG hJG using fun χ : Z ⟶ G.left => exists_chart U.P.L.isLB (χ z)
  have hb : r ≫ (𝟙_ _ ⊗ D.P.A).hom = x ≫ (fstG (IsLocalRing.maximalIdeal V) e G).left ≫ G.hom := by
    rw [← Over.w (snd (𝟙_ _) D.P.A), ← Category.assoc, hr, Category.assoc, Over.w, Over.w]
  let xG : Over.mk (r ≫ (𝟙_ _ ⊗ D.P.A).hom) ⟶ G :=
    Over.homMk (x ≫ (fstG (IsLocalRing.maximalIdeal V) e G).left) (by rw [Category.assoc]; exact hb.symm)
  let rB : Over.mk (r ≫ (𝟙_ _ ⊗ D.P.A).hom) ⟶ 𝟙_ _ ⊗ D.P.A := Over.homMk r
  refine (hs Z x (lift (rB ≫ fst _ _) xG).left r ?_ hr ?_ z JG J hJG hJ).1 α hα
  · exact congrArg CommaMorphism.left (lift_snd (rB ≫ fst _ _) xG)
  · exact (congrArg CommaMorphism.left (lift_fst (rB ≫ fst _ _) xG)).symm

end GlobalTheory.LevelVanishing
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiTendstoZero

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory

theorem psi_tendsto_zero : (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ f, U.Theta θ f → (∃ j, (f 0).f j ≠ 0) → PsiRel D (𝟙_ _) f → ∀ n : ℕ, {χ : D.X | ¬ D.PsiIn χ (IsLocalRing.maximalIdeal V ^ n)}.Finite) := by
  intro V _ _ _ hV D A G _ _ U θ f hθ h0 hR n
  haveI := hV.1
  obtain ⟨ga, a, hS⟩ := exists_psiScal V D
  obtain ⟨m, hm⟩ := exists_order_translates V hV D 1 (f 0) h0
  obtain ⟨s, hs⟩ := LevelVanishing.main V hV D A G U 1 θ f hθ.1 (m + n)
  refine s.finite_toSet.subset fun χ hχ => ?_
  by_contra hn
  apply hχ
  have hne : IsLocalRing.maximalIdeal V ^ n ≠ ⊥ := pow_ne_zero n (IsDiscreteValuationRing.not_a_field V)
  refine (psiIn_iff_scalar_mem V D ga a hS χ _ hne).2 ?_
  obtain ⟨⟨p, q⟩, hpq⟩ := IsLocalization.surj (nonZeroDivisors V) (a χ).val
  obtain ⟨z, J, hJ, hz⟩ := hm χ
  have hq : (q : V) ≠ 0 := nonZeroDivisors.coe_ne_zero q
  have e := PsiInt.psiRel_integral V D ga a f hS hR χ p q (by rw [mul_comm]; exact hpq) (𝟙_ _ ⊗ D.P.A) (snd _ _) z J hJ
  have e₁ : lift (toUnit (𝟙_ _ ⊗ D.P.A)) (snd (𝟙_ _) D.P.A) = 𝟙 _ := by
    ext1
    · exact toUnit_unique _ _
    · simp
  have e₂ : toUnit (𝟙_ _ ⊗ D.P.A) = fst (𝟙_ _) D.P.A := toUnit_unique _ _
  haveI : Flat D.P.A.hom := by
    haveI := D.P.isAb.smooth
    infer_instance
  haveI : Flat (𝟙_ _ ⊗ D.P.A).hom := by
    have h : (𝟙_ _ ⊗ D.P.A).hom = (λ_ D.P.A).hom.left ≫ D.P.A.hom := (Over.w _).symm
    haveI : IsIso (λ_ D.P.A).hom.left := inferInstanceAs (IsIso ((Over.forget _).map (λ_ D.P.A).hom))
    rw [h]
    infer_instance
  let io := (((𝟙_ _ ⊗ D.P.A).left.presheaf.germ ⊤ z trivial).hom.comp (((𝟙_ _ ⊗ D.P.A).hom.appTop.hom).comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom))
  have hio : ∀ v : V, gs (𝟙 _) z ⊤ (scal (𝟙_ _ ⊗ D.P.A).hom v) = io v := fun v => gs_eq _ _ ⊤ trivial _
  have hio' : ∀ v : V, cst (𝟙_ _ ⊗ D.P.A).hom z v = io v := fun v => gs_eq _ _ ⊤ trivial _
  rw [hio, hio, e₁] at e
  have hf := hs χ hn z J hJ
  have hf' := Ideal.map_mono (f := io) (Ideal.pow_le_pow_right (Nat.le_succ (m + n))) hf
  obtain ⟨r, hr, hp⟩ := exists_mem_pow_of_ratio_of_torsionFree V _ io
    (fun v hv x hx => by
      have := cst_regular (𝟙_ _ ⊗ D.P.A).hom z hv
      rw [hio'] at this
      exact this (hx.trans (mul_zero _).symm))
    _ _ p q m n hq e hf' (fun h => hz (by
      rw [← e₂]
      exact (Ideal.unit_mul_mem_iff_mem _ (Units.isUnit _)).1 h))
  refine ⟨r, hr, ?_⟩
  have hq' : algebraMap V (FractionRing V) q ≠ 0 := (IsLocalization.map_units _ q).ne_zero
  apply mul_right_cancel₀ hq'
  rw [← map_mul, ← hp]
  exact hpq.symm

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiTendstoZeroStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
theorem _root_.GlobalTheory.T.finite_not_psiIn_maximalIdeal_pow : (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ f, U.Theta θ f → (∃ j, (f 0).f j ≠ 0) → PsiRel D (𝟙_ _) f → ∀ n : ℕ, {χ : D.X | ¬ D.PsiIn χ (IsLocalRing.maximalIdeal V ^ n)}.Finite) := by
  first | exact @GlobalTheory.psi_tendsto_zero | exact GlobalTheory.psi_tendsto_zero | (intros; apply GlobalTheory.psi_tendsto_zero <;> assumption)
end
end
