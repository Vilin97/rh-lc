module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CardEqMapMulKer
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianSchemeIdPowFiniteEtaleSurjective
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsHeckeIsog
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueFactorThroughEtaleIsogenyReducedStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsFiniteAndEtaleOfCompOfFiniteEtaleCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TrivOfAxesTrivPullbackEtaleIsogenyStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckeKernelSchemeGeometricPointsEqKernelsStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyHeckeCorrespondenceSchemeStatement
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDualIsogeny

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkFam

open GlobalTheory.CechPic

theorem pow_eq_of_map_add {A Q : Type} [AddCommGroup A] [Group Q] (f : A → Q)
    (hf : ∀ a c, f (a + c) = f a * f c) (n : ℕ) (a : A) : f a ^ n = f (n • a) := by
  induction n with
  | zero =>
    have h := hf 0 0
    rw [add_zero] at h
    rw [pow_zero, zero_nsmul, left_eq_mul.1 h]
  | succ n ih => rw [pow_succ, ih, succ_nsmul, hf]

theorem exists_dual_isogeny : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (p : ℕ) (S : Scheme.{0}) [IsReduced S] (s : S ⟶ Sp (KA l)) (o o' : Ob D l s) (ψ : o.t.G ⟶ o'.t.G), p.Prime → ¬ p ∣ l.M' → IsIsog o o' p ψ → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (z : Over.mk x ⟶ o.t.G), z ≫ ψ = 1 → z ^ p ^ 2 = 1) → ∃ ψ' : o'.t.G ⟶ o.t.G, ψ ≫ ψ' = 𝟙 o.t.G ^ p ^ 2 ∧ ψ' ≫ ψ = 𝟙 o'.t.G ^ p ^ 2 ∧ IsIsog o' o p ψ' := by
  intro E _ _ _ H D l p S _ s o o' ψ hp _ ⟨⟨hψ, hf, he, hs, hact, hiso⟩, hlev⟩ hker
  have hA : IsAbelianScheme o.t.G := ⟨o.t.semi.comm, o.t.semi.smooth, o.proper, o.t.semi.geomConnected⟩
  have hB : IsAbelianScheme o'.t.G := ⟨o'.t.semi.comm, o'.t.semi.smooth, o'.proper, o'.t.semi.geomConnected⟩
  have hn : 0 < p ^ 2 := pow_pos hp.pos 2
  have hu : IsUnit ((p ^ 2 : ℕ) : Γ(S, ⊤)) := by
    have h0 : IsUnit ((p ^ 2 : ℕ) : Γ(Sp (KA l), ⊤)) := by
      have := ((baseKA l).unit _ hn).map (Scheme.ΓSpecIso (CommRingCat.of (KA l))).inv.hom
      rwa [map_natCast] at this
    have := h0.map s.appTop.hom
    rwa [map_natCast] at this
  obtain ⟨m1, m2, m3, m4⟩ := abelianScheme_id_pow_finite_etale_surjective S o.t.G (p ^ 2) hA hu
  have := hA.proper
  have := hB.proper
  have := hA.smooth
  have := hB.smooth
  obtain ⟨π, hπ, hψπ, -⟩ := GlobalTheory.T.exists_unique_factor_through_etale_isogeny_reduced S o.t.G o'.t.G o.t.G ψ (𝟙 o.t.G ^ p ^ 2) hA hB inferInstance hψ hf he hs m1
    fun k _ _ x z hz => by rw [MonObj.comp_pow, Category.comp_id, hker k x z hz]
  have hepi : Epi ψ.left := Flat.epi_of_flat_of_surjective _
  have canc : ∀ (Y : Over S) (f f' : o'.t.G ⟶ Y), ψ ≫ f = ψ ≫ f' → f = f' := fun Y f f' h =>
    Over.OverMorphism.ext ((cancel_epi ψ.left).1 (congrArg (·.left) h))
  have hπψ : π ≫ ψ = 𝟙 o'.t.G ^ p ^ 2 := canc _ _ _ (by
    rw [← Category.assoc, hψπ, MonObj.pow_comp, MonObj.comp_pow, Category.id_comp, Category.comp_id])
  have hl : ψ.left ≫ π.left = (𝟙 o.t.G ^ p ^ 2).left := congrArg (·.left) hψπ
  have hw : π.left ≫ o.t.G.hom = o'.t.G.hom := Over.w π
  have hsep : IsSeparated π.left := by
    have : IsSeparated (π.left ≫ o.t.G.hom) := by rw [hw]; infer_instance
    exact IsSeparated.of_comp _ o.t.G.hom
  have hlfp : LocallyOfFinitePresentation π.left := by
    have : LocallyOfFinitePresentation (π.left ≫ o.t.G.hom) := by rw [hw]; infer_instance
    exact TangentCrit.locallyOfFinitePresentation_of_comp _ o.t.G.hom
  obtain ⟨hf', he'⟩ := isFinite_and_etale_of_comp_of_finite_etale_cover _ _ _ ψ.left π.left hf he hs
    (hl ▸ m2) (hl ▸ m3) hsep hlfp
  have hs' : Surjective π.left := by
    have : Surjective (ψ.left ≫ π.left) := hl ▸ m4
    exact Surjective.of_comp ψ.left π.left
  have hact' : ∀ a, o'.t.act.act a ≫ π = π ≫ o.t.act.act a := fun a => canc _ _ _ (by
    have := o.t.act.hom a
    rw [← Category.assoc, ← hact, Category.assoc, hψπ, ← Category.assoc, hψπ, MonObj.pow_comp, MonObj.comp_pow,
      Category.id_comp, Category.comp_id])
  refine ⟨π, hψπ, hπψ, ⟨hπ, hf', he', hs', hact', ?_⟩, fun p' hp' a => ?_⟩
  · have hL := o.t.PP.isLB
    have hM := o'.t.PP.isLB
    have hΘ : ∃ t : LB.Gen (Theta o.t.G o.t.PP.L), t.IsGen := ⟨o.t.cub.t, o.t.cub.isGen⟩
    have hn' : (lbPow o'.t.PP.L (p ^ 2)).IsLB := LB.isLB_linComb hM _ _
    have hψm : pull ψ.left (cls _ hM) = (p ^ 2) • cls _ hL := by
      rw [← cls_lbPow hL (p ^ 2) (LB.isLB_linComb hL _ _)]
      exact ((cls_eq_iff _ (pull_isLB hM _)).2 hiso).symm
    have h₁ : (cubeLB o.t.G ![fst o'.t.G o'.t.G ≫ π, snd o'.t.G o'.t.G ≫ π] o.t.PP.L).IsLB :=
      LB.isLB_linComb hL _ _
    have h₂ : (cubeLB o'.t.G ![fst o'.t.G o'.t.G, snd o'.t.G o'.t.G] (lbPow o'.t.PP.L (p ^ 2))).IsLB :=
      LB.isLB_linComb hn' _ _
    have hN := LB.isLB_div h₁ h₂
    have val : ∀ {T : Over S} (x y : T ⟶ o'.t.G), pull (lift x y).left (cls _ hN) =
        lam (cls _ hL) (x ≫ π) (y ≫ π) - (p ^ 2) • lam (cls _ hM) x y := by
      intro T x y
      rw [cls_div h₁ h₂, cls_cube_two hL, cls_cube_two hn', map_sub, pull_lam, pull_lam, lift_fst,
        lift_snd, lift_fst_assoc, lift_snd_assoc, cls_lbPow hM, lam_nsmul]
    have hN0 : cls _ hN = 0 := by
      refine (cls_eq_zero_iff hN).2 (GlobalTheory.T.triv_of_axes_triv_pullback_etale_isogeny S o.t.G o'.t.G ψ o'.t.PP.L _ (p ^ 2) hA hB hM o'.ample hN hψ hf he hs
        hn hu hker ?_ ?_ ?_)
      · refine (cls_eq_zero_iff (pull_isLB hN _)).1 ?_
        rw [cls_pull hN, val, MonObj.one_comp, lam_one_left, lam_one_left, nsmul_zero, sub_self]
      · refine (cls_eq_zero_iff (pull_isLB hN _)).1 ?_
        rw [cls_pull hN, val, MonObj.one_comp, lam_one_right, lam_one_right, nsmul_zero, sub_self]
      · refine (cls_eq_zero_iff (pull_isLB hN _)).1 ?_
        have e : ψ ⊗ₘ ψ = lift (fst _ _ ≫ ψ) (snd _ _ ≫ ψ) := by ext1 <;> simp
        rw [cls_pull hN, e, val, Category.assoc, Category.assoc, hψπ, MonObj.comp_pow, MonObj.comp_pow,
          Category.comp_id, Category.comp_id, lam_pow_left hL hΘ, lam_pow_right hL hΘ, ← lam_pull, hψm,
          lam_nsmul, sub_self]
    have e : cls _ hL = lam (cls _ hL) (𝟙 _) (o.t.act.act H.w0) :=
      ((cls_eq_iff hL (LB.isLB_linComb hL _ _)).2 o.t.prim).trans (cls_cube_two hL _ _ _)
    have e' : cls _ hM = lam (cls _ hM) (𝟙 _) (o'.t.act.act H.w0) :=
      ((cls_eq_iff hM (LB.isLB_linComb hM _ _)).2 o'.t.prim).trans (cls_cube_two hM _ _ _)
    have key := val (𝟙 _) (o'.t.act.act H.w0)
    rw [hN0, map_zero, ← e', hact', Category.id_comp, eq_comm, sub_eq_zero] at key
    rw [← cls_eq_iff hn' (pull_isLB hL _), cls_lbPow hM, cls_pull hL, ← key]
    conv_rhs => rw [e, pull_lam, Category.comp_id]
  · have hM : ∀ a, o.eta (l.M • a) = 1 := fun a => o.eta_ker _ (by
      rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
      exact Submodule.smul_mem_smul (HeckePoint.natCast_M_mem l) Submodule.mem_top)
    have h2 : p ^ 2 * (p' * p') ≡ 1 [MOD l.M'] := by
      have := hp'.mul hp'
      rwa [show p * p' * (p * p') = p ^ 2 * (p' * p') by ring] at this
    rw [← (hlev p' hp' (p' • a)).1, ← (hlev p' hp' (p' • a)).2, Category.assoc, Category.assoc, hψπ,
      MonObj.comp_pow, MonObj.comp_pow, Category.comp_id, Category.comp_id, pow_eq_of_map_add _ o.eta_add,
      pow_eq_of_map_add _ o.etaA_add, smul_smul, smul_smul, _root_.mul_assoc,
      HeckePoint.eq_of_modEq _ o.eta_add hM (h2.of_dvd (Nat.dvd_lcm_left _ _)),
      HeckePoint.eq_of_modEq _ o.etaA_add o.etaA_ker (h2.of_dvd (Nat.dvd_lcm_right _ _)), one_nsmul]
    exact ⟨rfl, rfl⟩

end GlobalTheory.HkFam
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckeCorrespondenceSecondProjectionFiniteEtale

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

noncomputable section

namespace GlobalTheory.HkFam.Swap

theorem id_pow_left_comp {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (n : ℕ) :
    (𝟙 G' ^ n).left ≫ φ = φ ≫ (𝟙 G ^ n).left := by
  have hw : φ ≫ G.hom = G'.hom ≫ f := h.1.w
  let Φ : Over.mk (G'.hom ≫ f) ⟶ G := Over.homMk φ hw
  have key : ∀ m : ℕ, (Φ ^ m).left = (𝟙 G' ^ m).left ≫ φ := by
    intro m
    induction m with
    | zero =>
      let Ψ : Over.mk (G'.hom ≫ f) ⟶ G := Over.homMk ((1 : G' ⟶ G').left ≫ φ) (by
        rw [Category.assoc, hw, ← Category.assoc, Over.w]; rfl)
      have hΨ : Ψ * Ψ = Ψ * 1 := by
        rw [_root_.mul_one]
        apply Over.OverMorphism.ext
        have := h.2 G' 1 1 Ψ Ψ rfl rfl
        rw [this, _root_.mul_one]
        rfl
      have h1 : Ψ = 1 := mul_left_cancel hΨ
      simp only [pow_zero]
      rw [← h1]
      rfl
    | succ m ih =>
      rw [pow_succ, pow_succ]
      exact h.2 G' (𝟙 G' ^ m) (𝟙 G') (Φ ^ m) Φ ih (by simp [Φ])
  have hc : Φ ≫ 𝟙 G ^ n = Φ ^ n := by rw [MonObj.comp_pow, Category.comp_id]
  calc (𝟙 G' ^ n).left ≫ φ = (Φ ^ n).left := (key n).symm
    _ = (Φ ≫ 𝟙 G ^ n).left := by rw [hc]
    _ = φ ≫ (𝟙 G ^ n).left := by simp [Φ]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {P P' : Ideal (𝓞 E)} {p i : ℕ}

theorem isAdmissibleSplitHeckePrime_conj (h : admitted l P p) : admitted l (P.map (H.bar : 𝓞 E →+* 𝓞 E)) p := by
  obtain ⟨hmax, hcop, hp, hpP, hl⟩ := h
  refine ⟨?_, ?_, hp, ?_, hl⟩
  · exact Ideal.map_isMaximal_of_equiv H.bar (p := P)
  · rw [GlobalTheory.HeckeDual.map_bar_map_bar, sup_comm]
    exact hcop
  · have := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hpP
    rwa [map_natCast] at this

theorem isReduced_Hk (Z : Corr Xo P p i) : IsReduced Z.Hk := by
  have : Etale Z.π₁ := Z.et₁
  have : SmoothOfRelativeDimension D.dim Xo.s := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  exact (GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field (KA l) Z.Hk
    (Z.π₁ ≫ Xo.s) inferInstance).1

theorem isHecke (Z : Corr Xo P p i) : IsHecke Z.o₁ Z.o₂ P p i Z.ψ := ⟨Z.isog, Z.K, Z.ker, Z.hecke⟩

private theorem oAct_act_natCast {S : Scheme.{0}} {G : Over S} [GrpObj G] (A : OAct (𝓞 E) G) (n : ℕ) :
    A.act (n : 𝓞 E) = 𝟙 G ^ n := by
  induction n with
  | zero =>
    have h0 := A.5 0 0
    rw [add_zero] at h0
    have h1 : A.act 0 * A.act 0 = A.act 0 * 1 := by rw [_root_.mul_one]; exact h0.symm
    rw [Nat.cast_zero, pow_zero]
    exact mul_left_cancel h1
  | succ n ih => rw [Nat.cast_succ, A.5, ih, A.3, pow_succ]

theorem exists_dual (Z : Corr Xo P p i) (h : admitted l P p) : ∃ χ : Z.o₂.t.G ⟶ Z.o₁.t.G,
    Z.ψ ≫ χ = 𝟙 Z.o₁.t.G ^ p ^ 2 ∧ χ ≫ Z.ψ = 𝟙 Z.o₂.t.G ^ p ^ 2 ∧
      IsHecke Z.o₂ Z.o₁ (P.map (H.bar : 𝓞 E →+* 𝓞 E)) p i χ := by
  have hh := h
  obtain ⟨-, -, hp, -, hl⟩ := hh
  have := isReduced_Hk Z
  have hpb : (p : 𝓞 E) ∈ P.map (H.bar : 𝓞 E →+* 𝓞 E) := (isAdmissibleSplitHeckePrime_conj h).2.2.2.1
  have hker : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Z.Hk) (z : Over.mk x ⟶ Z.o₁.t.G),
      z ≫ Z.ψ = 1 → z ^ p ^ 2 = 1 := by
    intro k _ _ x z hz
    obtain ⟨C, hC, hK⟩ := Z.hecke k x
    have hzC : z ∈ C := (hC z).2 ((Z.ker k x z).1 hz)
    have hmem : ((p : 𝓞 E) * p) ∈ Ideal.span {(p : 𝓞 E)} * P.map (H.bar : 𝓞 E →+* 𝓞 E) :=
      Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hpb
    have h1 : z ≫ Z.o₁.t.act.act ((p : 𝓞 E) * p) = 1 := hK.2.2.1 hzC _ hmem
    rw [← Nat.cast_mul, oAct_act_natCast, MonObj.comp_pow, Category.comp_id, ← sq] at h1
    exact h1
  obtain ⟨χ, h1, h2, h3⟩ :=
    exists_dual_isogeny E H D l p Z.Hk (Z.π₁ ≫ Xo.s) Z.o₁ Z.o₂ Z.ψ hp hl Z.isog hker
  exact ⟨χ, h1, h2, GlobalTheory.isHecke_dual E H D l P p i Z.Hk _ Z.o₁ Z.o₂ Z.ψ χ h (isHecke Z) h3 h1⟩

def Exch (Z : Corr Xo P p i) (Z' : Corr Xo P' p i) (χ : Z.o₂.t.G ⟶ Z.o₁.t.G) (χ' : Z'.o₂.t.G ⟶ Z'.o₁.t.G)
    (a : Z.Hk ⟶ Z'.Hk) : Prop :=
  a ≫ Z'.π₁ ≫ Xo.s = Z.π₁ ≫ Xo.s ∧ ∃ (n₁ : ObjMap Z.o₂ Z'.o₁ a) (n₂ : ObjMap Z.o₁ Z'.o₂ a),
    χ.left ≫ n₂.toSABMap.φ = n₁.toSABMap.φ ≫ Z'.ψ.left ∧ Z.ψ.left ≫ n₁.toSABMap.φ = n₂.toSABMap.φ ≫ χ'.left

theorem exists_exch (Z : Corr Xo P p i) (Z' : Corr Xo P' p i) (χ : Z.o₂.t.G ⟶ Z.o₁.t.G) (χ' : Z'.o₂.t.G ⟶ Z'.o₁.t.G)
    (h : χ ≫ Z.ψ = 𝟙 Z.o₂.t.G ^ p ^ 2) (h' : Z'.ψ ≫ χ' = 𝟙 Z'.o₁.t.G ^ p ^ 2) (hχ : IsHecke Z.o₂ Z.o₁ P' p i χ) :
    ∃ a, Exch Z Z' χ χ' a := by
  have := isReduced_Hk Z
  obtain ⟨a, ⟨ha1, n₁, n₂, hn⟩, -⟩ := Z'.univ Z.Hk (Z.π₁ ≫ Xo.s) inferInstance Z.o₂ Z.o₁ χ hχ
  refine ⟨a, ha1, n₁, n₂, hn, ?_⟩
  obtain ⟨⟨⟨-, hfin, het, hsurj, -⟩, -⟩, -⟩ := hχ
  have : Epi χ.left := Flat.epi_of_flat_of_surjective _
  rw [← cancel_epi χ.left]
  have hp1 : IsGrpPullback Z.o₂.t.G Z'.o₁.t.G a n₁.toSABMap.φ := n₁.toSABMap.2
  calc χ.left ≫ Z.ψ.left ≫ n₁.toSABMap.φ = (χ ≫ Z.ψ).left ≫ n₁.toSABMap.φ := by simp
    _ = (𝟙 Z.o₂.t.G ^ p ^ 2).left ≫ n₁.toSABMap.φ := by rw [h]
    _ = n₁.toSABMap.φ ≫ (𝟙 Z'.o₁.t.G ^ p ^ 2).left := id_pow_left_comp hp1 (p ^ 2)
    _ = n₁.toSABMap.φ ≫ (Z'.ψ ≫ χ').left := by rw [h']
    _ = χ.left ≫ n₂.toSABMap.φ ≫ χ'.left := by rw [Over.comp_left, ← Category.assoc, ← hn, Category.assoc]

theorem Exch.comp_eq_id {Z : Corr Xo P p i} {Z' : Corr Xo P' p i} {χ : Z.o₂.t.G ⟶ Z.o₁.t.G}
    {χ' : Z'.o₂.t.G ⟶ Z'.o₁.t.G} {a : Z.Hk ⟶ Z'.Hk} {b : Z'.Hk ⟶ Z.Hk} (ha : Exch Z Z' χ χ' a)
    (hb : Exch Z' Z χ' χ b) : a ≫ b = 𝟙 _ := by
  obtain ⟨ha1, n₁, n₂, -, hn2⟩ := ha
  obtain ⟨hb1, m₁, m₂, hm1, -⟩ := hb
  have := isReduced_Hk Z
  obtain ⟨_, -, huniq⟩ := Z.univ Z.Hk (Z.π₁ ≫ Xo.s) inferInstance Z.o₁ Z.o₂ Z.ψ (isHecke Z)
  obtain ⟨c₁, hc₁⟩ := ((GlobalTheory.ObjMaps.id_comp_cancel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Z.o₁ Z'.o₂ Z.o₁).2
    b a m₁).1 n₂
  obtain ⟨c₂, hc₂⟩ := ((GlobalTheory.ObjMaps.id_comp_cancel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Z.o₂ Z'.o₁ Z.o₂).2
    b a m₂).1 n₁
  obtain ⟨i₁, hi₁⟩ := (GlobalTheory.ObjMaps.id_comp_cancel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Z.o₁ Z.o₁ Z.o₁).1
  obtain ⟨i₂, hi₂⟩ := (GlobalTheory.ObjMaps.id_comp_cancel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Z.o₂ Z.o₂ Z.o₂).1
  have e1 := huniq (a ≫ b) ⟨by rw [Category.assoc, hb1, ha1], c₁, c₂, by
    rw [hc₁, hc₂, ← Category.assoc, hn2, Category.assoc, hm1, Category.assoc]⟩
  have e2 := huniq (𝟙 _) ⟨by rw [Category.id_comp], i₁, i₂, by rw [hi₁, hi₂, Category.id_comp, Category.comp_id]⟩
  exact e1.trans e2.symm

theorem Exch.comp_π₁ {Z : Corr Xo P p i} {Z' : Corr Xo P' p i} {χ : Z.o₂.t.G ⟶ Z.o₁.t.G}
    {χ' : Z'.o₂.t.G ⟶ Z'.o₁.t.G} {a : Z.Hk ⟶ Z'.Hk} (ha : Exch Z Z' χ χ' a) : a ≫ Z'.π₁ = Z.π₂ := by
  obtain ⟨ha1, n₁, n₂, -, -⟩ := ha
  have := isReduced_Hk Z
  obtain ⟨_, -, huniq⟩ := Xo.rep Z.Hk (Z.π₁ ≫ Xo.s) inferInstance Z.o₂
  obtain ⟨c, -⟩ := ((GlobalTheory.ObjMaps.id_comp_cancel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ Z'.o₁ Z.o₂).2
    Z'.π₁ a Z'.m₁).1 n₁
  have e1 := huniq (a ≫ Z'.π₁) ⟨by rw [Category.assoc]; exact ha1, ⟨c⟩⟩
  have e2 := huniq Z.π₂ ⟨Z.base₂, ⟨Z.m₂⟩⟩
  exact e1.trans e2.symm

end GlobalTheory.HkFam.Swap

namespace GlobalTheory.HkFam

open Swap

theorem second_projection_finite_etale : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) (Z : Corr Xo 𝔓 p i), 1 ≤ D.p + D.q → admitted l 𝔓 p → IsFinite Z.π₂ ∧ Etale Z.π₂ ∧ (i ≤ D.p + D.q → Surjective Z.π₂) := by
  intro E _ _ _ H D l Xo P p i Z hpq h
  have h' : admitted l (P.map (H.bar : 𝓞 E →+* 𝓞 E)) p := isAdmissibleSplitHeckePrime_conj h
  obtain ⟨Z'⟩ := GlobalTheory.T.nonempty_heckeCorrespondenceScheme E H D l Xo (P.map (H.bar : 𝓞 E →+* 𝓞 E)) p i hpq h'
  obtain ⟨χ, hχ1, hχ2, hχ3⟩ := exists_dual Z h
  obtain ⟨χ', hχ'1, hχ'2, hχ'3⟩ := exists_dual Z' h'
  rw [GlobalTheory.HeckeDual.map_bar_map_bar] at hχ'3
  obtain ⟨a, ha⟩ := exists_exch Z Z' χ χ' hχ2 hχ'1 hχ3
  obtain ⟨b, hb⟩ := exists_exch Z' Z χ' χ hχ'2 hχ1 hχ'3
  have : IsIso a := ⟨b, Exch.comp_eq_id ha hb, Exch.comp_eq_id hb ha⟩
  have := Z'.fin₁
  have := Z'.et₁
  rw [← Exch.comp_π₁ ha]
  refine ⟨inferInstance, inferInstance, fun hi => ?_⟩
  have := (GlobalTheory.T.heckeKernelScheme_geometric_points_eq_kernels E H D l Xo _ p i Z'.toKerScheme h').2 hi
  infer_instance

end GlobalTheory.HkFam

end
end
end
