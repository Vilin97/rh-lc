module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSumPolAV
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinHomIffLinEnd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProdUnif
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EndoLbIsoSymmetryHypothesisExtendNormalModel
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOneOfTorusHomOfZero
import Mathlib.Tactic.Basify
import Mathlib.Tactic.TypeStar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubeFaceMiddleProjProd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinHomLiftOneId
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationProductOfUniformisedGroupsStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeClsPullHom

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

noncomputable section

namespace GlobalTheory.MumProd.GAdjFst

open GlobalTheory.CechPic

variable {S : Scheme.{0}}

theorem psum_comp_hom {G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] [IsCommMonObj H] (f : G ⟶ H) [IsMonHom f]
    {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ G)) (I : Finset (Fin n)) :
    psum G x I ≫ f = psum H (fun i => x i ≫ f) I :=
  psum_hom (MonoidHom.mk' (fun z : T ⟶ G => z ≫ f) fun a b => MonObj.mul_comp a b f) x I

theorem cubeCls_pull_hom {G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] [IsCommMonObj H] (f : G ⟶ H)
    [IsMonHom f] {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ G)) (c : Pic H.left) :
    GlobalTheory.ZH.EndoExtend.cubeCls G x (pull f.left c) = GlobalTheory.ZH.EndoExtend.cubeCls H (fun i => x i ≫ f) c := by
  unfold GlobalTheory.ZH.EndoExtend.cubeCls
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [← pull_comp, ← Over.comp_left, psum_comp_hom]

theorem cubeCls_add {G : Over S} [GrpObj G] [IsCommMonObj G] {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ G))
    (a b : Pic G.left) :
    GlobalTheory.ZH.EndoExtend.cubeCls G x (a + b) = GlobalTheory.ZH.EndoExtend.cubeCls G x a + GlobalTheory.ZH.EndoExtend.cubeCls G x b := by
  unfold GlobalTheory.ZH.EndoExtend.cubeCls
  simp only [map_add (f := _), smul_add, Finset.sum_add_distrib]

theorem cubeCls_one_left {G : Over S} [GrpObj G] [IsCommMonObj G] {T : Over S} (y : T ⟶ G) (c : Pic G.left) :
    GlobalTheory.ZH.EndoExtend.cubeCls G ![1, y] c = 0 := by
  classical
  unfold GlobalTheory.ZH.EndoExtend.cubeCls
  refine (Fintype.sum_equiv (Equiv.ulift : ULift.{0} (Finset (Fin 2)) ≃ Finset (Fin 2)) _
    (fun I => ((-1 : ℤ) ^ (2 - I.card)) • pull (psum G ![1, y] I).left c) (fun _ => rfl)).trans ?_
  have u : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by decide
  have p₀ : psum G ![1, y] ∅ = 1 := rfl
  have p₁ : psum G ![1, y] {0} = 1 := _root_.mul_one 1
  have p₂ : psum G ![1, y] {1} = y := _root_.mul_one y
  have p₄ : psum G ![1, y] {0, 1} = 1 * y := congrArg (1 * ·) (_root_.mul_one y)
  rw [u, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, p₀, p₁, p₂, p₄, _root_.one_mul]
  have c₁ : ({0, 1} : Finset (Fin 2)).card = 2 := by decide
  simp only [c₁, Finset.card_singleton, Finset.card_empty]
  norm_num

end GlobalTheory.MumProd.GAdjFst

theorem GlobalTheory.MumProd.gAdj_prod_fst : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D₁ : DegData R I) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : UnifPre I D₁ A₁ G₁) (D₂ : DegData R I) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : UnifPre I D₂ A₂ G₂) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (U : UnifPre I D A (G₁ ⊗ G₂)) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X) (a₁ : A.A ⟶ A₁.A) (a₂ : A.A ⟶ A₂.A), IsProdUnif U₁ U₂ U p₁ p₂ q₁ q₂ a₁ a₂ → GAdj U₁.LG.L U.LG.L (lift (𝟙 G₁) 1) (fst G₁ G₂) := by
  intro R _ _ I D₁ A₁ G₁ _ _ U₁ D₂ A₂ G₂ _ _ U₂ D A U p₁ p₂ q₁ q₂ a₁ a₂ hU
  obtain ⟨w, hw⟩ := hU.wL
  have hL := U.LG.isLB
  have hL₁ := U₁.LG.isLB
  have hL₂ := U₂.LG.isLB
  have hE : (extLB U₁.LG.L U₂.LG.L (fst G₁ G₂).left (snd G₁ G₂).left).IsLB :=
    GlobalTheory.CechPic.isLB_tens (pull_isLB hL₁ _) (pull_isLB hL₂ _)
  have e0 : GlobalTheory.CechPic.cls _ hL = GlobalTheory.CechPic.pull (fst G₁ G₂).left (GlobalTheory.CechPic.cls _ hL₁) +
      GlobalTheory.CechPic.pull (snd G₁ G₂).left (GlobalTheory.CechPic.cls _ hL₂) :=
    (GlobalTheory.CechPic.cls_eq_iff hL hE).2 ⟨w, hw⟩
  unfold GAdj
  refine (GlobalTheory.CechPic.cls_eq_iff _ _).1 ((GlobalTheory.ZH.EndoExtend.cls_cubeLB (G₁ ⊗ G₂) _ hL).trans
    (Eq.trans ?_ (GlobalTheory.ZH.EndoExtend.cls_cubeLB G₁ _ hL₁).symm))
  rw [e0,
    GlobalTheory.MumProd.GAdjFst.cubeCls_add, GlobalTheory.MumProd.GAdjFst.cubeCls_pull_hom,
    GlobalTheory.MumProd.GAdjFst.cubeCls_pull_hom]
  have h₁ : (fun i => (![fst G₁ (G₁ ⊗ G₂) ≫ lift (𝟙 G₁) 1, snd G₁ (G₁ ⊗ G₂)] : Fin 2 → _) i ≫ fst G₁ G₂) =
      ![fst G₁ (G₁ ⊗ G₂), snd G₁ (G₁ ⊗ G₂) ≫ fst G₁ G₂] := by
    funext i; fin_cases i <;> simp
  have h₂ : (fun i => (![fst G₁ (G₁ ⊗ G₂) ≫ lift (𝟙 G₁) 1, snd G₁ (G₁ ⊗ G₂)] : Fin 2 → _) i ≫ snd G₁ G₂) =
      ![1, snd G₁ (G₁ ⊗ G₂) ≫ snd G₁ G₂] := by
    funext i; fin_cases i <;> simp
  rw [h₁, h₂, GlobalTheory.MumProd.GAdjFst.cubeCls_one_left, add_zero]
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GAdjSndOfIsProdUnif

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

namespace GlobalTheory.MumProd.SndAdj

open GlobalTheory.CechPic

theorem psum_comp_hom {S : Scheme.{0}} {T H H' : Over S} [GrpObj H] [IsCommMonObj H] [GrpObj H'] [IsCommMonObj H']
    (f : H ⟶ H') [IsMonHom f] {n : ℕ} (x : Fin n → (T ⟶ H)) (I : Finset (Fin n)) :
    psum H x I ≫ f = psum H' (fun i => x i ≫ f) I :=
  psum_hom (MonoidHom.mk' (· ≫ f) fun a b => MonObj.mul_comp a b f) x I

theorem sum_cube_zero {S : Scheme.{0}} {T H : Over S} [GrpObj H] [IsCommMonObj H] {M : Type*} [AddCommGroup M]
    (F : (T ⟶ H) → M) (y : Fin 2 → (T ⟶ H)) (hy : y 0 = 1) :
    ∑ I : ULift.{0} (Finset (Fin 2)), ((-1 : ℤ) ^ (2 - I.down.card)) • F (psum H y I.down) = 0 := by
  refine (Fintype.sum_equiv Equiv.ulift _ (fun I : Finset (Fin 2) => ((-1 : ℤ) ^ (2 - I.card)) • F (psum H y I))
    (fun _ => rfl)).trans ?_
  rw [show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide]
  simp only [ReciprocityTheory.ChartRestriction.G.Out.CubePf.CubeCoordinateSums.psum_eq_prod]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp [hy]

theorem gAdj_snd_of_isProdUnif : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D₁ : DegData R I) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : UnifPre I D₁ A₁ G₁) (D₂ : DegData R I) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : UnifPre I D₂ A₂ G₂) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (U : UnifPre I D A (G₁ ⊗ G₂)) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X) (a₁ : A.A ⟶ A₁.A) (a₂ : A.A ⟶ A₂.A), IsProdUnif U₁ U₂ U p₁ p₂ q₁ q₂ a₁ a₂ → GAdj U₂.LG.L U.LG.L (lift 1 (𝟙 G₂)) (snd G₁ G₂) := by
  intro R _ _ I D₁ A₁ G₁ _ _ U₁ D₂ A₂ G₂ _ _ U₂ D A U p₁ p₂ q₁ q₂ a₁ a₂ hU
  obtain ⟨w, hw⟩ := hU.wL
  have hL := U.LG.isLB
  have hL₁ := U₁.LG.isLB
  have hL₂ := U₂.LG.isLB
  have hE : (extLB U₁.LG.L U₂.LG.L (fst G₁ G₂).left (snd G₁ G₂).left).IsLB :=
    isLB_tens (pull_isLB hL₁ _) (pull_isLB hL₂ _)
  have cL : cls _ hL = CechPic.pull (fst G₁ G₂).left (cls _ hL₁) + CechPic.pull (snd G₁ G₂).left (cls _ hL₂) :=
    (cls_eq_iff hL hE).2 ⟨w, hw⟩
  unfold GAdj cubeLB
  refine (cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hL₂ _ _)).1 ?_
  rw [cls_linComb hL, cls_linComb hL₂, cL]
  simp only [map_add (f := _), ← CechPic.pull_comp, smul_add, Finset.sum_add_distrib]
  have h₁ : ∀ J : Finset (Fin 2), (psum (G₁ ⊗ G₂) ![fst G₂ (G₁ ⊗ G₂) ≫ lift 1 (𝟙 G₂), snd G₂ (G₁ ⊗ G₂)] J).left ≫
      (fst G₁ G₂).left = (psum G₁ ![1, snd G₂ (G₁ ⊗ G₂) ≫ fst G₁ G₂] J).left := fun J => by
    rw [← Over.comp_left, psum_comp_hom]
    congr 2
    funext i
    fin_cases i <;> simp
  have h₂ : ∀ J : Finset (Fin 2), (psum (G₁ ⊗ G₂) ![fst G₂ (G₁ ⊗ G₂) ≫ lift 1 (𝟙 G₂), snd G₂ (G₁ ⊗ G₂)] J).left ≫
      (snd G₁ G₂).left = (psum G₂ ![fst G₂ (G₁ ⊗ G₂), snd G₂ (G₁ ⊗ G₂) ≫ snd G₁ G₂] J).left := fun J => by
    rw [← Over.comp_left, psum_comp_hom]
    congr 2
    funext i
    fin_cases i <;> simp
  simp only [h₁, h₂]
  exact add_eq_right.2 (sum_cube_zero
    (fun u : G₂ ⊗ G₁ ⊗ G₂ ⟶ G₁ => CechPic.pull u.left (cls _ hL₁)) ![1, snd G₂ (G₁ ⊗ G₂) ≫ fst G₁ G₂] rfl)

end GlobalTheory.MumProd.SndAdj
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductUniformisedGroupsUniformisedBySum

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

namespace GlobalTheory.MumProdUnifSum

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₁ : DegData R (maximalIdeal R)) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : Unif (maximalIdeal R) D₁ A₁ G₁) (D₂ : DegData R (maximalIdeal R)) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : Unif (maximalIdeal R) D₂ A₂ G₂) (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X) (a₁ : A.A ⟶ A₁.A) (a₂ : A.A ⟶ A₂.A), IsSumDeg D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂ → IsSumPolAV A A₁ A₂ a₁ a₂ → ∃ U : Unif (maximalIdeal R) D A (G₁ ⊗ G₂), GAdj U₁.LG.L U.LG.L (lift (𝟙 G₁) 1) (fst G₁ G₂) ∧ GAdj U₂.LG.L U.LG.L (lift 1 (𝟙 G₂)) (snd G₁ G₂) ∧ ∀ (i₁ : D₁.toPre.P.A ⟶ D.toPre.P.A) (i₂ : D₂.toPre.P.A ⟶ D.toPre.P.A) (j₁ : D₁.toPre.X →+ D.toPre.X) (j₂ : D₂.toPre.X →+ D.toPre.X), i₁ ≫ p₁ = 𝟙 _ → i₁ ≫ p₂ = toUnit _ ≫ η[D₂.toPre.P.A] → i₂ ≫ p₁ = toUnit _ ≫ η[D₁.toPre.P.A] → i₂ ≫ p₂ = 𝟙 _ → (∀ y, q₁ (j₁ y) = y) → (∀ y, q₂ (j₁ y) = 0) → (∀ y, q₁ (j₂ y) = 0) → (∀ y, q₂ (j₂ y) = y) → LinHom U₁.toUnifPre U.toUnifPre i₁ q₁ (lift (𝟙 G₁) 1) ∧ LinHom U.toUnifPre U₁.toUnifPre p₁ j₁ (fst G₁ G₂) ∧ LinHom U₂.toUnifPre U.toUnifPre i₂ q₂ (lift 1 (𝟙 G₂)) ∧ LinHom U.toUnifPre U₂.toUnifPre p₂ j₂ (snd G₁ G₂) := by
  intro R _ _ _ hB D₁ A₁ G₁ _ _ U₁ D₂ A₂ G₂ _ _ U₂ D A p₁ p₂ q₁ q₂ a₁ a₂ hD hA
  obtain ⟨U, hU⟩ := GlobalTheory.T.uniformisation_product_of_uniformisedGroups R hB D₁ A₁ G₁ U₁ D₂ A₂ G₂ U₂ D A p₁ p₂ q₁ q₂ a₁ a₂ hD hA
  refine ⟨U, GlobalTheory.MumProd.gAdj_prod_fst R _ D₁ A₁ G₁ U₁.toUnifPre D₂ A₂ G₂ U₂.toUnifPre D A U.toUnifPre p₁ p₂ q₁ q₂ a₁ a₂ hU,
    GlobalTheory.MumProd.SndAdj.gAdj_snd_of_isProdUnif R _ D₁ A₁ G₁ U₁.toUnifPre D₂ A₂ G₂ U₂.toUnifPre D A U.toUnifPre p₁ p₂ q₁ q₂ a₁ a₂ hU,
    fun i₁ i₂ j₁ j₂ h1 h2 h3 h4 h5 h6 h7 h8 => ⟨?_, hU.linHom_fst j₁ h5 h6, ?_, hU.linHom_snd j₂ h7 h8⟩⟩
  · exact GlobalTheory.MumProd.IsProdUnif.linHom_inl R _ D₁ A₁ G₁ U₁.toUnifPre D₂ A₂ G₂ U₂.toUnifPre D A U.toUnifPre p₁ p₂ q₁ q₂ a₁ a₂ hD hU i₁ h1 h2
  · exact GlobalTheory.MumProd.linHom_lift_one_id R _ D₁ A₁ G₁ U₁.toUnifPre D₂ A₂ G₂ U₂.toUnifPre D A U.toUnifPre p₁ p₂ q₁ q₂ a₁ a₂ hD hU i₂ h3 h4

end GlobalTheory.MumProdUnifSum
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductUniformisedGroupsUniformisedBySumStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

theorem _root_.GlobalTheory.T.product_uniformised_groups_uniformised_by_sum : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₁ : DegData R (maximalIdeal R)) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : Unif (maximalIdeal R) D₁ A₁ G₁) (D₂ : DegData R (maximalIdeal R)) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : Unif (maximalIdeal R) D₂ A₂ G₂) (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X) (a₁ : A.A ⟶ A₁.A) (a₂ : A.A ⟶ A₂.A), IsSumDeg D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂ → IsSumPolAV A A₁ A₂ a₁ a₂ → ∃ U : Unif (maximalIdeal R) D A (G₁ ⊗ G₂), GAdj U₁.LG.L U.LG.L (lift (𝟙 G₁) 1) (fst G₁ G₂) ∧ GAdj U₂.LG.L U.LG.L (lift 1 (𝟙 G₂)) (snd G₁ G₂) ∧ ∀ (i₁ : D₁.toPre.P.A ⟶ D.toPre.P.A) (i₂ : D₂.toPre.P.A ⟶ D.toPre.P.A) (j₁ : D₁.toPre.X →+ D.toPre.X) (j₂ : D₂.toPre.X →+ D.toPre.X), i₁ ≫ p₁ = 𝟙 _ → i₁ ≫ p₂ = toUnit _ ≫ η[D₂.toPre.P.A] → i₂ ≫ p₁ = toUnit _ ≫ η[D₁.toPre.P.A] → i₂ ≫ p₂ = 𝟙 _ → (∀ y, q₁ (j₁ y) = y) → (∀ y, q₂ (j₁ y) = 0) → (∀ y, q₁ (j₂ y) = 0) → (∀ y, q₂ (j₂ y) = y) → LinHom U₁.toUnifPre U.toUnifPre i₁ q₁ (lift (𝟙 G₁) 1) ∧ LinHom U.toUnifPre U₁.toUnifPre p₁ j₁ (fst G₁ G₂) ∧ LinHom U₂.toUnifPre U.toUnifPre i₂ q₂ (lift 1 (𝟙 G₂)) ∧ LinHom U.toUnifPre U₂.toUnifPre p₂ j₂ (snd G₁ G₂) := by
  first | exact @GlobalTheory.MumProdUnifSum.main | exact GlobalTheory.MumProdUnifSum.main | (intros; apply GlobalTheory.MumProdUnifSum.main <;> assumption)
end
end
