module

public import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CocycleDefinesDescendedLineBundleStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FlatCoverBaseChangeProductStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.GeneratorCompatibilityCompositePullbackStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LineBundleTrivialAfterFlatCoverStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LineBundleTrivialOfDescendedGeneratorStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LinearCombinationGeneratorSectionExistsStatement
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TheoremOfCubeGeneratorExistsStatement
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.TypeStar

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.GeneratorDescentUnitExists

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.RigDesc

theorem exists_unit_of_gen : ∀ {Z P Q : Scheme.{0}} (g : Z ⟶ P) (f : P ⟶ Q) (M : LB P), M.IsLB →
    ∀ (c : LB.Gen (LB.LinComb M (K := Fin 2) ![pullback.fst f f, pullback.snd f f] ![-1, 1])), c.IsGen →
    ∀ (τ : LB.Gen (M.pull g)), τ.IsGen →
    ∃ (u : Γ(pullback (g ≫ f) (g ≫ f), ⊤)) (hu : IsUnit u),
      ∀ (W : Scheme.{0}) (a b : W ⟶ Z) (hab : a ≫ g ≫ f = b ≫ g ≫ f) (w : W) (J : (W ⟶ P) → M.ι), Good M w J →
        gm (pullback.lift a b hab) w ⊤ hu.unit =
          val τ a w J * val c (pullback.lift (a ≫ g) (b ≫ g) (by simpa using hab)) w J * (val τ b w J)⁻¹ := by
  intro Z P Q g f M hM c hc τ hτ
  have hm : (pullback.fst (g ≫ f) (g ≫ f) ≫ g) ≫ f = (pullback.snd (g ≫ f) (g ≫ f) ≫ g) ≫ f := by
    simpa using pullback.condition (f := g ≫ f) (g := g ≫ f)
  let m : pullback (g ≫ f) (g ≫ f) ⟶ pullback f f := pullback.lift _ _ hm
  have m₁ : m ≫ pullback.fst f f = pullback.fst (g ≫ f) (g ≫ f) ≫ g := pullback.lift_fst _ _ hm
  have m₂ : m ≫ pullback.snd f f = pullback.snd (g ≫ f) (g ≫ f) ≫ g := pullback.lift_snd _ _ hm
  obtain ⟨t, -, hv⟩ := exists_gen hM (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      simp only [Fintype.prod_sum_type, Fintype.prod_unique, Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, m₁, m₂]
      simp)
    (LB.mulGen M _ _ _ _ (LB.mulGen M _ _ _ _ (LB.pullGen M _ _ τ (pullback.fst (g ≫ f) (g ≫ f))) (LB.pullGen M _ _ c m))
      (LB.invGen M _ _ (LB.pullGen M _ _ τ (pullback.snd (g ≫ f) (g ≫ f)))))
    (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hτ _) (DVR.pullGen_isGen _ _ _ _ hc _))
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hτ _)))
  have le : (⊤ : (pullback (g ≫ f) (g ≫ f)).Opens) ≤
      LB.wchart M (PEmpty.elim : PEmpty → (pullback (g ≫ f) (g ≫ f) ⟶ P)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨(res le (t.s PEmpty.elim)).val, Units.isUnit _, fun W a b hab w J hJ => ?_⟩
  have e₁ : pullback.lift a b hab ≫ pullback.fst (g ≫ f) (g ≫ f) = a := pullback.lift_fst _ _ _
  have e₂ : pullback.lift a b hab ≫ pullback.snd (g ≫ f) (g ≫ f) = b := pullback.lift_snd _ _ _
  have e₃ : pullback.lift a b hab ≫ m = pullback.lift (a ≫ g) (b ≫ g) (by simpa using hab) := by
    apply pullback.hom_ext
    · rw [Category.assoc, m₁, ← Category.assoc, e₁, pullback.lift_fst]
    · rw [Category.assoc, m₂, ← Category.assoc, e₂, pullback.lift_snd]
  rw [IsUnit.unit_of_val_units]
  refine ((gm_res _ w le trivial _).trans (val_of t _ w J PEmpty.elim (fun k => k.elim)).symm).trans ?_
  rw [hv W _ w J hJ, val_mul hJ, val_mul hJ, val_inv, val_pull hJ, val_pull hJ, val_pull hJ, e₁, e₂, e₃]

end GlobalTheory.CompanionTheory.RigDesc
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.GeneratorDescentUnitExistsStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.generator_descent_unit_exists : ∀ {Z P Q : Scheme.{0}} (g : Z ⟶ P) (f : P ⟶ Q) (M : LB P), M.IsLB →
    ∀ (c : LB.Gen (LB.LinComb M (K := Fin 2) ![pullback.fst f f, pullback.snd f f] ![-1, 1])), c.IsGen →
    ∀ (τ : LB.Gen (M.pull g)), τ.IsGen →
    ∃ (u : Γ(pullback (g ≫ f) (g ≫ f), ⊤)) (hu : IsUnit u),
      ∀ (W : Scheme.{0}) (a b : W ⟶ Z) (hab : a ≫ g ≫ f = b ≫ g ≫ f) (w : W) (J : (W ⟶ P) → M.ι), Good M w J →
        gm (pullback.lift a b hab) w ⊤ hu.unit =
          val τ a w J * val c (pullback.lift (a ≫ g) (b ≫ g) (by simpa using hab)) w J * (val τ b w J)⁻¹ := by
  first | exact @GlobalTheory.CompanionTheory.RigDesc.exists_unit_of_gen | exact GlobalTheory.CompanionTheory.RigDesc.exists_unit_of_gen | (intros; apply GlobalTheory.CompanionTheory.RigDesc.exists_unit_of_gen <;> assumption)
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SeesawTrivialityAbelianScheme

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.RigDesc

variable {S : Scheme.{0}} {A X Y : Over S} [GrpObj A]

theorem val_lift_eq_of_comp_eq (hA : IsAbelianScheme A) (q : X ⟶ Y) {N : LB (A ⊗ Y).left} (hN : N.IsLB)
    (r : LB.Gen (ev N (1 : Y ⟶ A) (𝟙 Y)))
    (t : LB.Gen (ev N (fst A X) (snd A X ≫ q))) (ht : t.IsGen)
    (hn : ∀ (Z : Scheme.{0}) (s : Z ⟶ X.left) (z : Z) (J : (Z ⟶ (A ⊗ Y).left) → N.ι), Good N z J →
      val t (s ≫ (lift (1 : X ⟶ A) (𝟙 X)).left) z J = val r (s ≫ q.left) z J)
    {T : Over S} (α : T ⟶ A) (x x' : T ⟶ X) (h : x ≫ q = x' ≫ q)
    (z : T.left) (J : (T.left ⟶ (A ⊗ Y).left) → N.ι) (hJ : Good N z J) :
    val t (lift α x).left z J = val t (lift α x').left z J := by
  have hc : ∀ x₁ : T ⟶ X, lift (fst A T) (snd A T ≫ x₁) ≫ lift (fst A X) (snd A X ≫ q) =
      lift (fst A T) (snd A T ≫ x₁ ≫ q) := fun x₁ => by
    ext <;> simp
  have hc' : (lift (fst A T) (snd A T ≫ x)).left ≫ (lift (fst A X) (snd A X ≫ q)).left =
      (lift (fst A T) (snd A T ≫ x')).left ≫ (lift (fst A X) (snd A X ≫ q)).left := by
    rw [← Over.comp_left, ← Over.comp_left, hc, hc, h]
  have he : (lift (1 : T ⟶ A) (𝟙 T)).left ≫ (snd A T).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_snd]; rfl
  have hs : ∀ x₁ : T ⟶ X, (lift (1 : T ⟶ A) (𝟙 T)).left ≫ (lift (fst A T) (snd A T ≫ x₁)).left =
      x₁.left ≫ (lift (1 : X ⟶ A) (𝟙 X)).left := fun x₁ => by
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    ext <;> simp
  have hv : ∀ x₁ : T ⟶ X, ∀ (y : T.left) (I : (T.left ⟶ (A ⊗ Y).left) → N.ι), Good N y I →
      val (LB.pullGen N _ _ t (lift (fst A T) (snd A T ≫ x₁)).left) (lift (1 : T ⟶ A) (𝟙 T)).left y I =
        val r (x₁ ≫ q).left y I := fun x₁ y I hI => by
    rw [val_pull hI, hs, hn _ _ _ _ hI, Over.comp_left]
  have key := gen_unique' hN (u := LB.pullGen N _ _ t (lift (fst A T) (snd A T ≫ x)).left)
    (u' := LB.pullGen N _ _ t (lift (fst A T) (snd A T ≫ x')).left)
    (fun U _ k => by simp only [hc']) (snd A T).left (lift (1 : T ⟶ A) (𝟙 T)).left he
    (surj_snd GlobalTheory.globalFns_holds hA T)
    (DVR.pullGen_isGen _ _ _ _ ht _) (DVR.pullGen_isGen _ _ _ _ ht _)
    (fun y I hI => by rw [hv x y I hI, hv x' y I hI, h]) T.left (lift α (𝟙 T)).left z J hJ
  have hl : ∀ x₁ : T ⟶ X, (lift α (𝟙 T)).left ≫ (lift (fst A T) (snd A T ≫ x₁)).left = (lift α x₁).left := fun x₁ => by
    rw [← Over.comp_left]
    congr 1
    ext <;> simp
  rw [val_pull hJ, val_pull hJ, hl, hl] at key
  exact key

end GlobalTheory.CompanionTheory.RigDesc

namespace GlobalTheory.CompanionTheory.RigDesc

theorem triv_of_triv_of_flat_cover : ∀ (S : Scheme.{0}) (A X Y : Over S) [GrpObj A], IsAbelianScheme A → ∀ q : X ⟶ Y, Flat q.left →
    LocallyOfFinitePresentation q.left → Surjective q.left →
    ∀ N : LB (A ⊗ Y).left, N.IsLB → Triv (ev N (1 : Y ⟶ A) (𝟙 Y)) → Triv (ev N (fst A X) (snd A X ≫ q)) → Triv N := by
  rintro S A X Y _ hA q hfl hlfp hsj N hN ⟨r, hr⟩ ⟨t₀, ht₀⟩
  obtain ⟨f₁, f₂, f₃⟩ := GlobalTheory.T.flat_cover_base_change_product S A X Y hA q hfl hlfp hsj
  have he : (lift (1 : X ⟶ A) (𝟙 X)).left ≫ (snd A X).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_snd]; rfl
  have hef : (lift (1 : X ⟶ A) (𝟙 X)).left ≫ (lift (fst A X) (snd A X ≫ q)).left =
      q.left ≫ (lift (1 : Y ⟶ A) (𝟙 Y)).left := by
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    ext <;> simp
  obtain ⟨t, ht, hn⟩ := GlobalTheory.T.linear_combination_generator_section_exists hN (fun _ => (lift (fst A X) (snd A X ≫ q)).left) (fun _ => 1)
    (fun _ => q.left ≫ (lift (1 : Y ⟶ A) (𝟙 Y)).left) (fun _ => 1) (snd A X).left (lift (1 : X ⟶ A) (𝟙 X)).left he
    (fun U _ k => by simp only [hef]) t₀ ht₀ (LB.pullGen N _ _ r q.left) (DVR.pullGen_isGen _ _ _ _ hr _)
  refine GlobalTheory.T.line_bundle_trivial_of_descended_generator _ f₁ f₂ f₃ N hN t ht ?_
  intro W a b hab w i hi
  have hw : a ≫ (A ⊗ X).hom = b ≫ (A ⊗ X).hom := by
    have e := congrArg (· ≫ (A ⊗ Y).hom) hab
    simpa only [Category.assoc, Over.w] using e
  let T : Over S := Over.mk (a ≫ (A ⊗ X).hom)
  let a' : T ⟶ A ⊗ X := Over.homMk a rfl
  let b' : T ⟶ A ⊗ X := Over.homMk b hw.symm
  have hab' : a' ≫ lift (fst A X) (snd A X ≫ q) = b' ≫ lift (fst A X) (snd A X ≫ q) := by
    exact Over.OverMorphism.ext hab
  have h₁ : a' ≫ fst A X = b' ≫ fst A X := by
    have e := congrArg (· ≫ fst A Y) hab'
    simpa using e
  have h₂ : (a' ≫ snd A X) ≫ q = (b' ≫ snd A X) ≫ q := by
    have e := congrArg (· ≫ snd A Y) hab'
    simpa using e
  obtain ⟨J, hJ, hJi⟩ := exists_good N hN w (K := PUnit.{1}) (fun _ => a ≫ (lift (fst A X) (snd A X ≫ q)).left)
    (fun _ => i) (fun _ _ _ => rfl) (fun _ => hi)
  have hJi' : J (a ≫ (lift (fst A X) (snd A X ≫ q)).left) = i := hJi PUnit.unit
  have key := val_lift_eq_of_comp_eq hA q hN r t ht (fun Z s z I hI => (hn Z s z I hI).trans (val_pull hI _ _ _))
    (a' ≫ fst A X) (a' ≫ snd A X) (b' ≫ snd A X) h₂ w J hJ
  have ea : (lift (a' ≫ fst A X) (a' ≫ snd A X)).left = a := by
    rw [← comp_lift, lift_fst_snd]; simp [a']
  have eb : (lift (a' ≫ fst A X) (b' ≫ snd A X)).left = b := by
    rw [h₁, ← comp_lift, lift_fst_snd]; simp [b']
  rw [ea, eb, val_of t a w J (fun _ => i) (fun _ => hJi'), val_of t b w J (fun _ => i) (fun _ => by rw [← hab]; exact hJi')] at key
  exact key


end GlobalTheory.CompanionTheory.RigDesc
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SeesawTrivialityAbelianSchemeStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.seesaw_triviality_abelian_scheme : ∀ (S : Scheme.{0}) (A X Y : Over S) [GrpObj A], IsAbelianScheme A → ∀ q : X ⟶ Y, Flat q.left →
    LocallyOfFinitePresentation q.left → Surjective q.left →
    ∀ N : LB (A ⊗ Y).left, N.IsLB → Triv (ev N (1 : Y ⟶ A) (𝟙 Y)) → Triv (ev N (fst A X) (snd A X ≫ q)) → Triv N := by
  first | exact @GlobalTheory.CompanionTheory.RigDesc.triv_of_triv_of_flat_cover | exact GlobalTheory.CompanionTheory.RigDesc.triv_of_triv_of_flat_cover | (intros; apply GlobalTheory.CompanionTheory.RigDesc.triv_of_triv_of_flat_cover <;> assumption)
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.RigDescent

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.RigDesc

theorem mul_mid {G : Type*} [CommGroup G] (x y z p q : G) : x * (p * q) * z⁻¹ = (x * p * y⁻¹) * (y * q * z⁻¹) := by
  simp only [_root_.mul_assoc, inv_mul_cancel_left]

theorem mul_fix {G : Type*} [CommGroup G] (x y t : G) : (x * y⁻¹ * t) * x⁻¹ = t * y⁻¹ := by
  rw [_root_.mul_comm x, _root_.mul_assoc, _root_.mul_assoc, _root_.mul_comm x, _root_.mul_assoc, inv_mul_cancel, _root_.mul_one, _root_.mul_comm]

theorem gs_appTop {W Y : Scheme.{0}} (φ : W ⟶ Y) (u : Γ(Y, ⊤)ˣ) (x : W) :
    gs (𝟙 W) x ⊤ (φ.appTop.hom u.val) = (gm φ x ⊤ u).val := by
  have e := gs_pull (𝟙 W) φ x ⊤ trivial u.val
  rw [Category.id_comp] at e
  exact e.trans (gs_unit φ x ⊤ trivial u)

theorem lbDescent (hH : H90) {P Q : Scheme.{0}} (f : P ⟶ Q) (hf : Flat f) (hl : LocallyOfFinitePresentation f)
    (hs : Surjective f) (M : LB P) (hM : M.IsLB)
    (c : LB.Gen (LB.LinComb M (K := Fin 2) ![pullback.fst f f, pullback.snd f f] ![-1, 1])) (hc : c.IsGen)
    (coc : ∀ (W : Scheme.{0}) (a b d : W ⟶ P) (hab : a ≫ f = b ≫ f) (hbd : b ≫ f = d ≫ f) (w : W)
      (J : (W ⟶ P) → M.ι), Good M w J →
      val c (pullback.lift a b hab) w J * val c (pullback.lift b d hbd) w J = val c (pullback.lift a d (hab.trans hbd)) w J) :
    ∃ N : LB Q, N.IsLB ∧ LBIso M (N.pull f) := by
  obtain ⟨Z, g, hg, hgl, hgs, τ, hτ⟩ := GlobalTheory.T.line_bundle_trivial_after_flat_cover M hM
  have h₁ : Flat (g ≫ f) := inferInstance
  have h₂ : LocallyOfFinitePresentation (g ≫ f) := inferInstance
  have h₃ : Surjective (g ≫ f) := inferInstance
  obtain ⟨u, hu, hv⟩ := GlobalTheory.T.generator_descent_unit_exists g f M hM c hc τ hτ
  have good : ∀ {W : Scheme.{0}} (w : W), ∃ J : (W ⟶ P) → M.ι, Good M w J := fun w =>
    ⟨fun χ => (exists_chart hM (χ w)).choose, fun χ => (exists_chart hM (χ w)).choose_spec⟩
  have cocu : ∀ (W : Scheme.{0}) (a b d : W ⟶ Z) (hab : a ≫ g ≫ f = b ≫ g ≫ f) (hbd : b ≫ g ≫ f = d ≫ g ≫ f),
      (pullback.lift a d (hab.trans hbd)).appTop u =
        (pullback.lift a b hab).appTop u * (pullback.lift b d hbd).appTop u := by
    intro W a b d hab hbd
    have e₀ : ∀ φ : W ⟶ pullback (g ≫ f) (g ≫ f), φ.appTop u = φ.appTop.hom hu.unit.val := fun _ => rfl
    refine fn_ext fun x _ => ?_
    obtain ⟨J, hJ⟩ := good x
    have hab' : (a ≫ g) ≫ f = (b ≫ g) ≫ f := by simpa using hab
    have hbd' : (b ≫ g) ≫ f = (d ≫ g) ≫ f := by simpa using hbd
    have key : gm (pullback.lift a d (hab.trans hbd)) x ⊤ hu.unit =
        gm (pullback.lift a b hab) x ⊤ hu.unit * gm (pullback.lift b d hbd) x ⊤ hu.unit := by
      rw [hv _ _ _ _ _ _ hJ, hv _ _ _ _ _ _ hJ, hv _ _ _ _ _ _ hJ]
      rw [← coc W (a ≫ g) (b ≫ g) (d ≫ g) hab' hbd' x J hJ]
      exact mul_mid _ _ _ _ _
    rw [gs_mul (𝟙 W) x ⊤ trivial, e₀, e₀, e₀, gs_appTop, gs_appTop, gs_appTop, key, Units.val_mul]
  obtain ⟨N, hN, T, hT, hTv⟩ := GlobalTheory.T.cocycle_defines_descended_line_bundle hH (g ≫ f) h₁ h₂ h₃ u hu cocu
  refine ⟨N, hN, GlobalTheory.T.lbIso_pull_of_generator_ratio_eq g f hg hgl hgs M hM N hN τ hτ T hT fun W a b hab w i k hi hk => ?_⟩
  have hab' : a ≫ g ≫ f = b ≫ g ≫ f := by rw [← Category.assoc, hab, Category.assoc]
  obtain ⟨J, hJ, hJk⟩ := exists_good M hM w (K := PUnit) (fun _ => a ≫ g) (fun _ => k) (fun _ _ _ => rfl) (fun _ => hk)
  have hJk' : J (a ≫ g) = k := hJk PUnit.unit
  have one : ∀ (x y : W ⟶ P) (h : x ≫ f = y ≫ f), x = y → val c (pullback.lift x y h) w J = 1 := by
    rintro x _ h rfl
    exact mul_eq_left.1 (coc W x x x h h w J hJ)
  have va : val τ a w J = gm a w ((M.pull g).U fun _ => k) (τ.s fun _ => k) := val_of τ a w J _ fun _ => hJk'
  have vb : val τ b w J = gm b w ((M.pull g).U fun _ => k) (τ.s fun _ => k) := val_of τ b w J _ fun _ => by rw [← hab]; exact hJk'
  have e := hTv W a b hab' w i hi
  rw [hv _ _ _ _ _ _ hJ, one _ _ _ hab, va, vb, _root_.mul_one] at e
  rw [e]
  exact mul_fix _ _ _

theorem rigDescent : H90 → RigDescent := by
  intro hH S A X Y _ hA q hq hl hs
  refine ⟨GlobalTheory.T.seesaw_triviality_abelian_scheme S A X Y hA q hq hl hs, fun M hM hr hinv => ?_⟩
  obtain ⟨hf, hfl, hfs⟩ := GlobalTheory.T.flat_cover_base_change_product S A X Y hA q hq hl hs
  obtain ⟨c, hc, coc⟩ := GlobalTheory.T.theorem_of_cube_generator_exists S A X Y hA q M hM hr hinv
  obtain ⟨N₀, hN₀, iso⟩ := lbDescent hH _ hf hfl hfs M hM c hc coc
  let eY := (lift (1 : Y ⟶ A) (𝟙 Y)).left
  let eX := (lift (1 : X ⟶ A) (𝟙 X)).left
  let pY := (snd A Y).left
  let pX := (snd A X).left
  let f := (lift (fst A X) (snd A X ≫ q)).left
  have e₁ : eY ≫ pY = 𝟙 _ := by
    rw [← Over.comp_left, lift_snd]; rfl
  have e₂ : f ≫ pY ≫ eY = pX ≫ eX ≫ f := by
    rw [← Over.comp_left, ← Over.comp_left, ← Over.comp_left, ← Over.comp_left]
    congr 1
    ext1 <;> simp
  obtain ⟨N, hN, hc'⟩ := cls_surj (cls N₀ hN₀ - CechPic.pull pY (CechPic.pull eY (cls N₀ hN₀)))
  have hm : cls M hM = CechPic.pull f (cls N₀ hN₀) := (cls_eq_iff hM (pull_isLB hN₀ _)).2 iso
  have z : CechPic.pull eX (cls M hM) = 0 := (triv_ev_iff hM _ _).1 hr
  refine' ⟨N, hN, (triv_ev_iff hN _ _).2 ?_, (cls_eq_iff hM (pull_isLB hN _)).1 ?_⟩
  · show CechPic.pull eY (cls N hN) = 0
    rw [hc', map_sub, ← pull_comp, e₁, pull_id, sub_self]
  · show cls M hM = CechPic.pull f (cls N hN)
    rw [hc', map_sub, ← pull_comp f pY, ← pull_comp (f ≫ pY) eY, Category.assoc, e₂, pull_comp pX, pull_comp eX, ← hm, z, map_zero,
      sub_zero, hm]

end GlobalTheory.CompanionTheory.RigDesc
end
end
