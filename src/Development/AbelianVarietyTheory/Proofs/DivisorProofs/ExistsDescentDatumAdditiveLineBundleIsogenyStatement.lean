module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescCocycle
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZbLeftWhiskerRight
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
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleDescentToSubfield
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentCocycleDefectOfCompatibleStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentDatumCompatibleOfLineBundleIso
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZbLeftWhiskerRight
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalUnitTwistNormaliseDescentFamilyStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalUnitTripleFibreProductInvariantSetGroupCooStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescentCocycleDefectNormalisedEqOne

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open GlobalTheory.LBDescent GlobalTheory.DescNorm
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DescNorm

theorem tripleFibreProductProjOneThree_comp_fst {X Y : Scheme.{0}} (f : X ⟶ Y) :
    pr13 f ≫ pullback.fst f f = pullback.fst (pullback.snd f f) (pullback.fst f f) ≫ pullback.fst f f :=
  pullback.lift_fst _ _ _

theorem tripleFibreProductProjOneThree_comp_snd {X Y : Scheme.{0}} (f : X ⟶ Y) :
    pr13 f ≫ pullback.snd f f = pullback.snd (pullback.snd f f) (pullback.fst f f) ≫ pullback.snd f f :=
  pullback.lift_snd _ _ _

theorem defect_eq_one_of_coboundary {X Y Z : Scheme.{0}} (f : X ⟶ Y) (L : LB X) (hL : L.IsLB)
    (φ : ∀ i j, Γ(pullback f f, chart f L i j)ˣ) (D : Γ(Triple f, ⊤)ˣ) (z : X ⟶ X)
    (ρ : pullback f f ⟶ pullback f f) (σ : Triple f ⟶ Triple f)
    (h₁ : ρ ≫ pullback.fst f f = pullback.fst f f ≫ z) (h₂ : ρ ≫ pullback.snd f f = pullback.snd f f ≫ z)
    (k₁ : σ ≫ pullback.fst (pullback.snd f f) (pullback.fst f f) =
      pullback.fst (pullback.snd f f) (pullback.fst f f) ≫ ρ)
    (k₂ : σ ≫ pullback.snd (pullback.snd f f) (pullback.fst f f) =
      pullback.snd (pullback.snd f f) (pullback.fst f f) ≫ ρ)
    (g : X ⟶ Z) (U : L.ι → Z.Opens) (s : ∀ i, Γ(Z, U i)ˣ)
    (hN : ∀ (T : Scheme.{0}) (r : T ⟶ pullback f f) (t : T) (i j : L.ι),
      pullback.fst f f (ρ (r t)) ∈ L.U i → pullback.snd f f (ρ (r t)) ∈ L.U j →
      gm (r ≫ ρ) t _ (φ i j) =
        (gm (r ≫ pullback.fst f f ≫ g) t _ (s i))⁻¹ * gm (r ≫ pullback.snd f f ≫ g) t _ (s j))
    (hD : Defect f L φ D) (w : Triple f) : gm σ w ⊤ D = 1 := by
  have c : pullback.fst (pullback.snd f f) (pullback.fst f f) ≫ pullback.snd f f =
      pullback.snd (pullback.snd f f) (pullback.fst f f) ≫ pullback.fst f f := pullback.condition
  have k₃ : σ ≫ pr13 f = pr13 f ≫ ρ := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, tripleFibreProductProjOneThree_comp_fst, h₁, ← Category.assoc, k₁, Category.assoc, h₁,
        ← Category.assoc, ← Category.assoc, tripleFibreProductProjOneThree_comp_fst]
    · rw [Category.assoc, Category.assoc, tripleFibreProductProjOneThree_comp_snd, h₂, ← Category.assoc, k₂, Category.assoc, h₂,
        ← Category.assoc, ← Category.assoc, tripleFibreProductProjOneThree_comp_snd]
  obtain ⟨i, hi⟩ := exists_chart hL (pullback.fst f f (pullback.fst (pullback.snd f f) (pullback.fst f f) (σ w)))
  obtain ⟨j, hj⟩ := exists_chart hL (pullback.snd f f (pullback.fst (pullback.snd f f) (pullback.fst f f) (σ w)))
  obtain ⟨k, hk⟩ := exists_chart hL (pullback.snd f f (pullback.snd (pullback.snd f f) (pullback.fst f f) (σ w)))
  have e := hD _ σ w i j k hi hj hk
  have p₁ : ρ (pullback.fst (pullback.snd f f) (pullback.fst f f) w) =
      pullback.fst (pullback.snd f f) (pullback.fst f f) (σ w) := congrArg (fun m => m w) k₁.symm
  have p₂ : ρ (pullback.snd (pullback.snd f f) (pullback.fst f f) w) =
      pullback.snd (pullback.snd f f) (pullback.fst f f) (σ w) := congrArg (fun m => m w) k₂.symm
  have p₃ : ρ (pr13 f w) = pr13 f (σ w) := congrArg (fun m => m w) k₃.symm
  have pc : pullback.fst f f (pullback.snd (pullback.snd f f) (pullback.fst f f) (σ w)) =
      pullback.snd f f (pullback.fst (pullback.snd f f) (pullback.fst f f) (σ w)) :=
    congrArg (fun m => m (σ w)) c.symm
  have q₁ : pullback.fst f f (pr13 f (σ w)) =
      pullback.fst f f (pullback.fst (pullback.snd f f) (pullback.fst f f) (σ w)) :=
    congrArg (fun m => m (σ w)) (tripleFibreProductProjOneThree_comp_fst f)
  have q₂ : pullback.snd f f (pr13 f (σ w)) =
      pullback.snd f f (pullback.snd (pullback.snd f f) (pullback.fst f f) (σ w)) :=
    congrArg (fun m => m (σ w)) (tripleFibreProductProjOneThree_comp_snd f)
  have a := hN _ (pullback.fst (pullback.snd f f) (pullback.fst f f)) w i j (by rw [p₁]; exact hi)
    (by rw [p₁]; exact hj)
  have b := hN _ (pullback.snd (pullback.snd f f) (pullback.fst f f)) w j k (by rw [p₂, pc]; exact hj)
    (by rw [p₂]; exact hk)
  have d := hN _ (pr13 f) w i k (by rw [p₃, q₁]; exact hi) (by rw [p₃, q₂]; exact hk)
  simp only [← Category.assoc] at a b d
  rw [tripleFibreProductProjOneThree_comp_fst, tripleFibreProductProjOneThree_comp_snd] at d
  rw [← c] at b
  rw [k₁, k₂, k₃, a, b, d, _root_.mul_assoc, mul_inv_cancel_left] at e
  exact mul_eq_right.1 e

theorem defect_normalised : ∀ (K : Type) [Field K] (A A' B : Over (Sp K)) [GrpObj A] [GrpObj B] (q : A ⟶ A') (P : LB (A ⊗ B).left) (τ : LB.Gen (ev P (𝟙 A) (1 : A ⟶ B))), P.IsLB → ∀ (φ : ∀ i j, Γ(pullback (q ▷ B).left (q ▷ B).left, chart (q ▷ B).left P i j)ˣ) (D : Γ(Triple (q ▷ B).left, ⊤)ˣ), NormAlong q P τ φ → Defect (q ▷ B).left P φ D → ∀ w : Triple (q ▷ B).left, gm (rhoW q) w ⊤ D = 1 := by
  intro K _ A A' B _ _ q P τ hP φ D hN hD w
  exact defect_eq_one_of_coboundary (q ▷ B).left P hP φ D (zb A B).left (rhoZ q) (rhoW q) (rhoZ_fst q) (rhoZ_snd q)
    (rhoW_fst q) (rhoW_snd q) (fst A B).left _ (fun i => τ.s fun _ => i) hN hD w

end GlobalTheory.DescNorm
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescentCocycleDefectNormalisedEqOneStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open GlobalTheory.LBDescent GlobalTheory.DescNorm
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.descentCocycleDefect_normalised_eq_one : ∀ (K : Type) [Field K] (A A' B : Over (Sp K)) [GrpObj A] [GrpObj B] (q : A ⟶ A') (P : LB (A ⊗ B).left) (τ : LB.Gen (ev P (𝟙 A) (1 : A ⟶ B))), P.IsLB → ∀ (φ : ∀ i j, Γ(pullback (q ▷ B).left (q ▷ B).left, chart (q ▷ B).left P i j)ˣ) (D : Γ(Triple (q ▷ B).left, ⊤)ˣ), NormAlong q P τ φ → Defect (q ▷ B).left P φ D → ∀ w : Triple (q ▷ B).left, gm (rhoW q) w ⊤ D = 1 := by
  first | exact @GlobalTheory.DescNorm.defect_normalised | exact GlobalTheory.DescNorm.defect_normalised | (intros; apply GlobalTheory.DescNorm.defect_normalised <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentDatumCompatibleOfLineBundleIsoStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open GlobalTheory.LBDescent GlobalTheory.DescNorm
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_descentDatumCompatible_of_lineBundle_iso : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) (L : LB X), L.IsLB → LBIso (L.pull (pullback.fst f f)) (L.pull (pullback.snd f f)) → ∃ φ : ∀ i j, Γ(pullback f f, chart f L i j)ˣ, DescCompat f L φ := by
  first | exact @GlobalTheory.LBDescent.descCompat_of_lbIso | exact GlobalTheory.LBDescent.descCompat_of_lbIso | (intros; apply GlobalTheory.LBDescent.descCompat_of_lbIso <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoPullbackFstSndOfAdditiveTrivialKern

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open GlobalTheory.LBDescent GlobalTheory.DescNorm
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DescIsoExists

theorem lbIso_pull_fst_snd : ∀ (K : Type) [Field K] [IsAlgClosed K] (A A' B : Over (Sp K)) [GrpObj A] [GrpObj A'] [GrpObj B] (q : A ⟶ A') (P : LB (A ⊗ B).left), IsAbelianScheme A → IsAbelianScheme A' → IsAbelianScheme B → IsMonHom q → P.IsLB → IsAdditive P → (∀ (T : Over (Sp K)) (x : T ⟶ A), x ≫ q = 1 → Triv (ev P (fst T B ≫ x) (snd T B))) → LBIso (P.pull (pullback.fst (q ▷ B).left (q ▷ B).left)) (P.pull (pullback.snd (q ▷ B).left (q ▷ B).left)) := by
  intro K _ _ A A' B _ _ _ q P _ _ _ hq hP hadd hker
  let f := (q ▷ B).left
  have hw : f ≫ (A' ⊗ B).hom = (A ⊗ B).hom := Over.w (q ▷ B)
  let Z : Over (Sp K) := Over.mk (pullback.fst f f ≫ (A ⊗ B).hom)
  have hsnd : pullback.snd f f ≫ (A ⊗ B).hom = pullback.fst f f ≫ (A ⊗ B).hom := by
    rw [← hw, ← Category.assoc, ← pullback.condition, Category.assoc]
  have hB : (q ▷ B) ≫ snd A' B = snd A B := whiskerRight_snd q B
  have hA : (q ▷ B) ≫ fst A' B = fst A B ≫ q := whiskerRight_fst q B
  have hBl : f ≫ (snd A' B).left = (snd A B).left := by rw [← Over.comp_left, hB]
  have hAl : f ≫ (fst A' B).left = (fst A B).left ≫ q.left := by
    rw [← Over.comp_left, hA, Over.comp_left]
  let a : Z ⟶ A := Over.homMk (pullback.fst f f ≫ (fst A B).left) (by
    simp only [Z, Over.mk_hom, Category.assoc, Over.w])
  let a' : Z ⟶ A := Over.homMk (pullback.snd f f ≫ (fst A B).left) (by
    simp only [Z, Over.mk_hom, Category.assoc, Over.w]; exact hsnd)
  let b : Z ⟶ B := Over.homMk (pullback.fst f f ≫ (snd A B).left) (by
    simp only [Z, Over.mk_hom, Category.assoc, Over.w])
  let u : Z ⟶ A ⊗ B := Over.homMk (pullback.fst f f) rfl
  let u' : Z ⟶ A ⊗ B := Over.homMk (pullback.snd f f) hsnd
  have hu : lift a b = u := by
    ext1
    · ext; simp [a, u]
    · ext; simp [b, u]
  have hu' : lift a' b = u' := by
    ext1
    · ext; simp [a', u']
    · ext
      simp only [b, u', lift_snd, Over.homMk_left, Over.comp_left]
      rw [← hBl, ← Category.assoc, pullback.condition, Category.assoc]
  have hq' : a ≫ q = a' ≫ q := by
    ext
    simp only [a, a', Over.comp_left, Over.homMk_left, Category.assoc]
    rw [← hAl, ← Category.assoc, pullback.condition, Category.assoc]

  have e1 : (pullback.fst f f : pullback f f ⟶ _) = (lift a b).left := by rw [hu]; rfl
  have e2 : (pullback.snd f f : pullback f f ⟶ _) = (lift a' b).left := by rw [hu']; rfl
  refine (cls_eq_iff (pull_isLB hP _) (pull_isLB hP _)).1 ?_
  have c1 : cls _ (pull_isLB hP (pullback.fst f f)) = evc hP a b := by
    rw [cls_pull hP]; simp only [evc]; rw [e1]
  have c2 : cls _ (pull_isLB hP (pullback.snd f f)) = evc hP a' b := by
    rw [cls_pull hP]; simp only [evc]; rw [e2]
  rw [c1, c2]
  let k : Z ⟶ A := a' * a⁻¹
  have hinv : a⁻¹ ≫ q = (a ≫ q)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← MonObj.mul_comp, inv_mul_cancel, MonObj.one_comp]
  have hk : k ≫ q = 1 := by
    simp only [k]
    rw [MonObj.mul_comp, hinv, ← hq', mul_inv_cancel]
  have h0 : evc hP k b = 0 := by
    have e := congrArg (CechPic.pull (lift (𝟙 Z) b).left) ((triv_ev_iff hP _ _).1 (hker Z k hk))
    rwa [pull_evc, map_zero, lift_fst_assoc, Category.id_comp, lift_snd] at e
  have ha : a' = k * a := by simp only [k, inv_mul_cancel_right]
  rw [ha, (isAdditive_iff hP).1 hadd, h0, zero_add]

end GlobalTheory.DescIsoExists
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoPullbackFstSndOfAdditiveTrivialKernStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open GlobalTheory.LBDescent GlobalTheory.DescNorm
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.lineBundle_iso_pullback_fst_snd_of_additive_trivial_kernel : ∀ (K : Type) [Field K] [IsAlgClosed K] (A A' B : Over (Sp K)) [GrpObj A] [GrpObj A'] [GrpObj B] (q : A ⟶ A') (P : LB (A ⊗ B).left), IsAbelianScheme A → IsAbelianScheme A' → IsAbelianScheme B → IsMonHom q → P.IsLB → IsAdditive P → (∀ (T : Over (Sp K)) (x : T ⟶ A), x ≫ q = 1 → Triv (ev P (fst T B ≫ x) (snd T B))) → LBIso (P.pull (pullback.fst (q ▷ B).left (q ▷ B).left)) (P.pull (pullback.snd (q ▷ B).left (q ▷ B).left)) := by
  first | exact @GlobalTheory.DescIsoExists.lbIso_pull_fst_snd | exact GlobalTheory.DescIsoExists.lbIso_pull_fst_snd | (intros; apply GlobalTheory.DescIsoExists.lbIso_pull_fst_snd <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentDatumAdditiveLineBundleIsogeny

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open GlobalTheory.LBDescent GlobalTheory.DescNorm
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.DescNorm

theorem twist_descCompat : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) (L : LB X) (φ : ∀ i j, Γ(pullback f f, chart f L i j)ˣ) (u : Γ(pullback f f, ⊤)ˣ), DescCompat f L φ → DescCompat f L (twist f L φ u) := by
  intro X Y f L φ u hφ z i i' j j' hi hi' hj hj'
  have m : ∀ a b, pullback.fst f f z ∈ L.U a → pullback.snd f f z ∈ L.U b → (𝟙 (pullback f f)) z ∈ chart f L a b :=
    fun a b ha hb => ⟨ha, hb⟩
  simp only [twist, map_mul]
  rw [gm_res (𝟙 _) z le_top (m i' j' hi' hj'), gm_res (𝟙 _) z le_top (m i j hi hj), hφ z i i' j j' hi hi' hj hj']
  ac_rfl

theorem descentDatum_of_additive : ∀ (K : Type) [Field K] [IsAlgClosed K] (A A' B : Over (Sp K)) [GrpObj A] [GrpObj A'] [GrpObj B] (q : A ⟶ A') (P : LB (A ⊗ B).left), IsAbelianScheme A → IsAbelianScheme A' → IsAbelianScheme B → IsMonHom q → IsFinite q.left → Flat q.left → Surjective q.left → P.IsLB → IsAdditive P → Triv (ev P (𝟙 A) (1 : A ⟶ B)) → (∀ (T : Over (Sp K)) (x : T ⟶ A), x ≫ q = 1 → Triv (ev P (fst T B ≫ x) (snd T B))) → ∃ φ : ∀ i j, Γ(pullback (q ▷ B).left (q ▷ B).left, GlobalTheory.LBDescent.chart (q ▷ B).left P i j)ˣ, GlobalTheory.LBDescent.DescCompat (q ▷ B).left P φ ∧ GlobalTheory.LBDescent.DescCocycle (q ▷ B).left P φ := by
  intro K _ _ A A' B _ _ _ q P hA hA' hB hq _ _ _ hP hadd hzero hker
  obtain ⟨φ₀, hφ₀⟩ := GlobalTheory.T.exists_descentDatumCompatible_of_lineBundle_iso _ P hP (GlobalTheory.T.lineBundle_iso_pullback_fst_snd_of_additive_trivial_kernel K A A' B q P hA hA' hB hq hP hadd hker)
  obtain ⟨τ, hτ⟩ := hzero
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_globalUnit_twist_normalise_descent_family K A A' B q P τ hP hτ φ₀ hφ₀
  have hc : DescCompat (q ▷ B).left P (twist (q ▷ B).left P φ₀ u) := twist_descCompat _ P φ₀ u hφ₀
  obtain ⟨D, hD⟩ := GlobalTheory.T.exists_descentCocycleDefect_of_compatible _ P _ hP hc
  have h1 := GlobalTheory.T.descentCocycleDefect_normalised_eq_one K A A' B q P τ hP _ D hu hD
  have h2 := GlobalTheory.T.globalUnit_tripleFibreProduct_invariant_setGroupCoordZero K A A' B q hB D
  refine ⟨twist (q ▷ B).left P φ₀ u, hc, fun w i j k hi hj hk => ?_⟩
  have e := hD _ (𝟙 _) w i j k hi hj hk
  rw [← h2 w, h1 w, _root_.one_mul, Category.id_comp, Category.id_comp, Category.id_comp] at e
  exact e.symm

end GlobalTheory.DescNorm
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentDatumAdditiveLineBundleIsogenyStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_descentDatum_additive_lineBundle_isogeny : ∀ (K : Type) [Field K] [IsAlgClosed K] (A A' B : Over (Sp K)) [GrpObj A] [GrpObj A'] [GrpObj B] (q : A ⟶ A') (P : LB (A ⊗ B).left), IsAbelianScheme A → IsAbelianScheme A' → IsAbelianScheme B → IsMonHom q → IsFinite q.left → Flat q.left → Surjective q.left → P.IsLB → IsAdditive P → Triv (ev P (𝟙 A) (1 : A ⟶ B)) → (∀ (T : Over (Sp K)) (x : T ⟶ A), x ≫ q = 1 → Triv (ev P (fst T B ≫ x) (snd T B))) → ∃ φ : ∀ i j, Γ(pullback (q ▷ B).left (q ▷ B).left, GlobalTheory.LBDescent.chart (q ▷ B).left P i j)ˣ, GlobalTheory.LBDescent.DescCompat (q ▷ B).left P φ ∧ GlobalTheory.LBDescent.DescCocycle (q ▷ B).left P φ := by
  first | exact @GlobalTheory.DescNorm.descentDatum_of_additive | exact GlobalTheory.DescNorm.descentDatum_of_additive | (intros; apply GlobalTheory.DescNorm.descentDatum_of_additive <;> assumption)
end
end
