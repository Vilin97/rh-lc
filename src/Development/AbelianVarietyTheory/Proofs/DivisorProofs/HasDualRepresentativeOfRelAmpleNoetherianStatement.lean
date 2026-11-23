module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatCoverAdditiveFamilyEqLambda
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientKernelPolarisationDescendedBundleStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SameLineBundleFamilyDescendsFlatSurjectiveQuasiCStatement
import Mathlib.AlgebraicGeometry.Sites.Fpqc

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualPointEqOfQuotientFamilyIso

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon

section

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left}

theorem memKL_mul_inv_of_eq (hL : L.IsLB) {Z : Over S} (x x' : Z ⟶ A)
    (h : ∀ (W : Over S) (a : W ⟶ A) (z : W ⟶ Z),
      CechPic.pull (a * (z ≫ x)).left (cls L hL) - CechPic.pull (z ≫ x).left (cls L hL) =
        CechPic.pull (a * (z ≫ x')).left (cls L hL) - CechPic.pull (z ≫ x').left (cls L hL)) :
    GlobalTheory.MemKL A L (x * x'⁻¹) := by
  intro p
  have hD : (Out.translDiff A L (x * x'⁻¹)).IsLB := LB.isLB_linComb hL _ _
  obtain ⟨V, hV, hc⟩ := exists_pull_eq_zero
    (CechPic.pull x.left (cls L hL) - CechPic.pull x'.left (cls L hL)) p
  refine ⟨V, hV, (cls_eq_zero_iff (pull_isLB hD _)).1 ?_⟩
  have e₁ := pull_translDiff hL (x * x'⁻¹) hD (fst Z A) (snd Z A)
  rw [lift_fst_snd, Over.id_left, pull_id] at e₁
  have k₁ : ((fst Z A ≫ x')⁻¹ * snd Z A) * (fst Z A ≫ x) = (fst Z A ≫ (x * x'⁻¹)) * snd Z A := by
    rw [MonObj.comp_mul, GrpObj.comp_inv, mul_comm _ (fst Z A ≫ x)]
    exact (_root_.mul_assoc _ _ _).symm
  have k₂ : ((fst Z A ≫ x')⁻¹ * snd Z A) * (fst Z A ≫ x') = snd Z A := by
    rw [mul_comm, mul_inv_cancel_left]
  have e₃ := h (Z ⊗ A) ((fst Z A ≫ x')⁻¹ * snd Z A) (fst Z A)
  rw [k₁, k₂] at e₃
  have e₂ : cls _ hD = CechPic.pull (fst Z A).left
      (CechPic.pull x.left (cls L hL) - CechPic.pull x'.left (cls L hL)) := by
    rw [e₁, map_sub, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left]
    exact sub_eq_sub_iff_sub_eq_sub.1 e₃
  rw [cls_pull hD, e₂, ← pull_comp]
  exact pull_eq_zero_of_mem V (((fst Z A).left ⁻¹ᵁ V).ι ≫ (fst Z A).left) (fun z ↦ z.2) hc

end

theorem inj_of_quotient : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (L : LB A.left) (hL : L.IsLB), Out.RelAmple A L → ∀ (B : Over (Sp R)) (P : LB (A ⊗ B).left) (q : A ⟶ B) (hP : Fam A P), IsFinite q.left → Flat q.left → Surjective q.left → (∀ (Y : Over (Sp R)) (a x : Y ⟶ A), evc hP.isLB a (x ≫ q) = GlobalTheory.CechPic.pull (a * x).left (cls L hL) - GlobalTheory.CechPic.pull a.left (cls L hL) - GlobalTheory.CechPic.pull x.left (cls L hL) + GlobalTheory.CechPic.pull (1 : Y ⟶ A).left (cls L hL)) → (∀ (Y : Over (Sp R)) (x y : Y ⟶ A), x ≫ q = y ≫ q ↔ GlobalTheory.MemKL A L (x * y⁻¹)) → Inj A P := by
  intro R _ _ A _ g hA _ L hL _ B P q hP _ hflat hsurj hev hKL
  haveI : IsCommMonObj A := hA.comm
  haveI : Flat q.left := hflat
  haveI : Surjective q.left := hsurj
  intro Y u u' hs
  rw [same_iff hP.isLB hP.isLB] at hs
  let s₁ := pullback.snd q.left u.left
  let f₁ := pullback.fst q.left u.left
  let s₂ := pullback.snd q.left (s₁ ≫ u'.left)
  let f₂ := pullback.fst q.left (s₁ ≫ u'.left)
  let Z : Over (Sp R) := Over.mk (s₂ ≫ s₁ ≫ Y.hom)
  let c : Z ⟶ Y := Over.homMk (s₂ ≫ s₁) (by simp [Z])
  have w₁ : f₁ ≫ A.hom = s₁ ≫ Y.hom := by
    rw [← Over.w q, pullback.condition_assoc, Over.w u]
  have w₂ : f₂ ≫ A.hom = s₂ ≫ s₁ ≫ Y.hom := by
    rw [← Over.w q, pullback.condition_assoc, Category.assoc, Over.w u']
  let x : Z ⟶ A := Over.homMk (s₂ ≫ f₁) (by simp [Z, w₁])
  let x' : Z ⟶ A := Over.homMk f₂ (by simpa [Z] using w₂)
  have hx : c ≫ u = x ≫ q := by
    ext1
    simp only [Over.comp_left, c, x, Over.homMk_left, Category.assoc]
    rw [pullback.condition]
  have hx' : c ≫ u' = x' ≫ q := by
    ext1
    simp only [Over.comp_left, c, x', Over.homMk_left, Category.assoc]
    rw [pullback.condition]
  have hK : GlobalTheory.MemKL A L (x * x'⁻¹) := by
    refine memKL_mul_inv_of_eq hL x x' fun W a z ↦ ?_
    have e := congrArg (CechPic.pull (lift a (z ≫ c)).left) hs
    rw [pull_evc, pull_evc, lift_fst, lift_snd_assoc, lift_snd_assoc] at e
    simp only [Category.assoc] at e
    rw [hx, hx', ← Category.assoc, ← Category.assoc, hev, hev] at e
    rw [← sub_eq_zero] at e ⊢
    convert e using 1
    abel
  have hq : x ≫ q = x' ≫ q := (hKL Z x x').2 hK
  have : Epi c.left := by
    have : Flat c.left := by simp only [c, Over.homMk_left]; infer_instance
    have : Surjective c.left := by simp only [c, Over.homMk_left]; infer_instance
    exact Flat.epi_of_flat_of_surjective _
  have : Epi c := Over.epi_of_epi_left c
  rw [← cancel_epi c, hx, hx', hq]

end GlobalTheory.DualCon
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualPointEqOfQuotientFamilyIsoStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.dualPoint_eq_of_quotient_family_iso : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (L : LB A.left) (hL : L.IsLB), Out.RelAmple A L → ∀ (B : Over (Sp R)) (P : LB (A ⊗ B).left) (q : A ⟶ B) (hP : Fam A P), IsFinite q.left → Flat q.left → Surjective q.left → (∀ (Y : Over (Sp R)) (a x : Y ⟶ A), evc hP.isLB a (x ≫ q) = GlobalTheory.CechPic.pull (a * x).left (cls L hL) - GlobalTheory.CechPic.pull a.left (cls L hL) - GlobalTheory.CechPic.pull x.left (cls L hL) + GlobalTheory.CechPic.pull (1 : Y ⟶ A).left (cls L hL)) → (∀ (Y : Over (Sp R)) (x y : Y ⟶ A), x ≫ q = y ≫ q ↔ GlobalTheory.MemKL A L (x * y⁻¹)) → Inj A P := by
  first | exact @GlobalTheory.DualCon.inj_of_quotient | exact GlobalTheory.DualCon.inj_of_quotient | (intros; apply GlobalTheory.DualCon.inj_of_quotient <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatCoverAdditiveFamilyEqLambdaStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_flatCover_additiveFamily_eq_lambda : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (L : LB A.left) (hL : L.IsLB), Out.RelAmple A L → ∀ (T : Over (Sp R)) (N : LB (A ⊗ T).left) (hN : Fam A N), ∃ (H : Over (Sp R)) (h : H ⟶ T) (x : H ⟶ A), Flat h.left ∧ Surjective h.left ∧ QuasiCompact h.left ∧ (∀ (Y : Over (Sp R)) (a : Y ⟶ A) (y : Y ⟶ H), evc hN.isLB a (y ≫ h) = GlobalTheory.CechPic.pull (a * (y ≫ x)).left (cls L hL) - GlobalTheory.CechPic.pull a.left (cls L hL) - GlobalTheory.CechPic.pull (y ≫ x).left (cls L hL) + GlobalTheory.CechPic.pull (1 : Y ⟶ A).left (cls L hL)) := by
  first | exact @GlobalTheory.DualCover.exists_cover | exact GlobalTheory.DualCover.exists_cover | (intros; apply GlobalTheory.DualCover.exists_cover <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDualRepresentativeOfRelAmpleNoetherian

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualPol

theorem hasRepAF_of_relAmple : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ L : LB A.left, L.IsLB → Out.RelAmple A L → HasRepAF A g (𝟙_ _) := by
  intro R _ _ A _ g hA hg L hL ha
  obtain ⟨B, P, q, hP, hgood, hfa, hfin, hfl, hsu, hF, hK⟩ := GlobalTheory.T.exists_quotient_kernel_polarisation_descended_bundle R A g hA hg L hL ha
  have hinj : Inj A P := GlobalTheory.T.dualPoint_eq_of_quotient_family_iso R A g hA hg L hL ha B P q hP hfin hfl hsu hF hK
  have hex : ∀ (T : Over (Sp R)) (N : LB (A ⊗ T).left), Fam A N →
      ∃ x : T ⟶ B, LBIso N (ev P (fst A T) (snd A T ≫ x)) := by
    intro T N hN
    obtain ⟨H, h, x, hhf, hhs, hhq, hx⟩ := GlobalTheory.T.exists_flatCover_additiveFamily_eq_lambda R A g hA hg L hL ha T N hN
    have key : ∀ (Y : Over (Sp R)) (a : Y ⟶ A) (y : Y ⟶ H),
        evc hP.isLB a (y ≫ x ≫ q) = evc hN.isLB a (y ≫ h) := by
      intro Y a y
      rw [hx, ← Category.assoc, hF]
    have hc : ∀ {Z : Scheme} (g₁ g₂ : Z ⟶ H.left), g₁ ≫ h.left = g₂ ≫ h.left →
        g₁ ≫ (x ≫ q).left = g₂ ≫ (x ≫ q).left := by
      intro Z g₁ g₂ e
      let Z' : Over (Sp R) := Over.mk (g₁ ≫ H.hom)
      have e2 : g₂ ≫ H.hom = g₁ ≫ H.hom := by
        rw [← Over.w h, ← Category.assoc, ← e, Category.assoc]
      let k₁ : Z' ⟶ H := Over.homMk g₁ rfl
      let k₂ : Z' ⟶ H := Over.homMk g₂ e2
      have hkh : k₁ ≫ h = k₂ ≫ h := Over.OverMorphism.ext e
      have hs : Same A P P (k₁ ≫ x ≫ q) (k₂ ≫ x ≫ q) := by
        rw [same_iff hP.isLB hP.isLB]
        have e₁ := key (A ⊗ Z') (fst A Z') (snd A Z' ≫ k₁)
        have e₂ := key (A ⊗ Z') (fst A Z') (snd A Z' ≫ k₂)
        simp only [Category.assoc] at e₁ e₂
        rw [e₁, e₂, hkh]
      have := congrArg (fun t => t.left) (hinj Z' _ _ hs)
      simpa [k₁, k₂] using this
    haveI : Flat h.left := hhf
    haveI : Surjective h.left := hhs
    haveI : QuasiCompact h.left := hhq
    let d : T.left ⟶ B.left := EffectiveEpi.desc h.left (x ≫ q).left hc
    have hd : h.left ≫ d = (x ≫ q).left := EffectiveEpi.fac h.left (x ≫ q).left hc
    have hdB : d ≫ B.hom = T.hom := by
      rw [← cancel_epi h.left, ← Category.assoc, hd, Over.w (x ≫ q), Over.w h]
    let xT : T ⟶ B := Over.homMk d hdB
    have hxT : h ≫ xT = x ≫ q := Over.OverMorphism.ext hd
    refine ⟨xT, (same_id_iff hN.isLB hP.isLB xT).1 ?_⟩
    refine GlobalTheory.T.sameLineBundleFamily_descends_flat_surjective_quasiCompact (Sp R) A hA T B T H N P hN hP (𝟙 T) xT h hhf hhs hhq ?_
    rw [same_iff hN.isLB hP.isLB, Category.comp_id, hxT, key]
  refine ⟨B, toUnit B, P, ⟨hP, fun T t N hN ↦ ?_⟩, hgood, hfa⟩
  obtain ⟨x, hx⟩ := hex T N hN
  refine ⟨x, ⟨toUnit_unique _ _, hx⟩, fun y hy ↦ hinj T y x ?_⟩
  have h1 := (cls_eq_iff hN.isLB (pull_isLB hP.isLB _)).2 hy.2
  have h2 := (cls_eq_iff hN.isLB (pull_isLB hP.isLB _)).2 hx
  exact (cls_eq_iff (pull_isLB hP.isLB _) (pull_isLB hP.isLB _)).1 (h1.symm.trans h2)

end GlobalTheory.DualPol
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDualRepresentativeOfRelAmpleNoetherianStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.hasDualRepresentative_of_relAmple_noetherian : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ L : LB A.left, L.IsLB → Out.RelAmple A L → HasRepAF A g (𝟙_ _) := by
  first | exact @GlobalTheory.DualPol.hasRepAF_of_relAmple | exact GlobalTheory.DualPol.hasRepAF_of_relAmple | (intros; apply GlobalTheory.DualPol.hasRepAF_of_relAmple <;> assumption)
end
end
