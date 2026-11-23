module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsTranslSum
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsPullByEndOfPullRel
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.VGeIffExtended
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.NuChainPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NuChain
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGenGeneric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ExpansionNonnegRegular
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.RegTiePfA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.RegTie
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.VtMove
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.MixEnd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaPt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.ThetaMove
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.Linter.Style
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.GenMove
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.Divisibility.WeightAlgebra
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ThetaNuPf

section

@[expose] public section

set_option autoImplicit false


noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

attribute [local instance] Over.cartesianMonoidalCategory

theorem cast_cancel {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (k : ℕ) {L1 L2 : RigLB G}
    (e : L1 = L2) (θ : LB.Sec (LB.LinComb L2.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ)))) :
    (e ▸ (e.symm ▸ θ : LB.Sec (LB.LinComb L1.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))))) = θ := by
  subst e; rfl

theorem thetaNu : ThetaNuSt := by
  intro E _ _ _ H V _ _ _ _ _ t P _ ϖ hϖ Q hQ vK hvK tK m w _ θ θK htie
  haveI := t.semi.smooth
  haveI := t.semi.separated
  haveI := t.semi.quasiCompact
  let σ' : LB.Sec (LB.LinComb P.U.LG.L (K := Fin 1) (fun _ => 𝟙 t.G.left) (fun _ => ((1 : ℕ) : ℤ))) :=
    P.bundle.symm ▸ θ
  let s : P.U.SecK 1 := TG.secK P.U.toUnifPre σ'
  have hs := TG.secK_rel P.U.toUnifPre σ'
  obtain ⟨Ex, hEx, -⟩ := (P.U.expand 1 le_rfl).1 s
  have hnu := expansion_nonneg_regular V ϖ hϖ P.D Q hQ vK hvK P.A t.G P.U 1 rfl σ' s hs Ex hEx
  refine ⟨s, Ex, fun Z r zp hzp z J J' hJ hJ' => ?_, hEx, hnu⟩
  have hsc := secScal_cast (pullback.fst t.G.hom (Out.jK V)) 1 P.bundle s σ' hs
  have e1 := ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation.secScal_sval hsc (r ≫ iotaK m) z hJ
  rw [Category.assoc, iotaK, pullback.lift_fst, cast_cancel 1 P.bundle θ] at e1
  exact e1.symm.trans (htie Z r zp hzp z J J' hJ hJ')

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.VtMoveSym

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.VtMove

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1

section Transl

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {T : Over S}

theorem translPt_one' : translPt A (1 : T ⟶ A) = snd T A := by
  rw [translPt_eq, MonObj.comp_one, _root_.one_mul]

theorem transl_translPt (y x : T ⟶ A) :
    (translT A y).left ≫ (translPt A x).left = (translPt A (y * x)).left := by
  rw [← Over.comp_left]
  congr 1
  simp only [translPt_eq, translT, MonObj.comp_mul, lift_snd, lift_fst_assoc]
  rw [_root_.mul_left_comm, ← _root_.mul_assoc]

theorem transl_pow_succ (x : T ⟶ A) (j : ℕ) :
    (translT A (x ^ j)).left ≫ (translPt A x).left = (translPt A (x ^ (j + 1))).left := by
  rw [transl_translPt, pow_succ]

theorem transl_inv_translPt (x : T ⟶ A) : (translT A x⁻¹).left ≫ (translPt A x).left = (snd T A).left := by
  rw [transl_translPt, inv_mul_cancel, translPt_one']

theorem negT_snd' : (negT A T).left ≫ (snd T A).left = (snd T A ≫ (GrpObj.inv : A ⟶ A)).left := by
  rw [← Over.comp_left, negT, lift_snd]

theorem negT_translPt (x : T ⟶ A) :
    (negT A T).left ≫ (translPt A x).left = (translT A x⁻¹).left ≫ (snd T A ≫ (GrpObj.inv : A ⟶ A)).left := by
  rw [← Over.comp_left, ← Over.comp_left]
  congr 1
  have e1 : negT A T ≫ translPt A x = (fst T A ≫ x) * (snd T A)⁻¹ := by
    rw [translPt_eq, MonObj.comp_mul, negT, lift_fst_assoc, lift_snd]
    rfl
  have e2 : translT A x⁻¹ ≫ snd T A ≫ (GrpObj.inv : A ⟶ A) = (fst T A ≫ x) * (snd T A)⁻¹ := by
    rw [← Category.assoc, translT, lift_snd, translPt_eq]
    show ((fst T A ≫ x⁻¹) * snd T A)⁻¹ = _
    rw [mul_inv, GrpObj.comp_inv, inv_inv]
  rw [e1, e2]

end Transl

section Move

variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A] [IsCommMonObj A]
  {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
  {L₀ : LB G.left} {L₁ : LB A.left}

include hp hτ in
theorem inv_rel {x : T ⟶ A} {x₀ : T₀ ⟶ G} (hx : x.left ≫ φ = τ ≫ x₀.left) :
    (x⁻¹).left ≫ φ = τ ≫ (x₀⁻¹).left := by
  show (x ≫ GrpObj.inv).left ≫ φ = τ ≫ (x₀ ≫ GrpObj.inv).left
  rw [push_inv hp x, push_eq hp τ hτ hx]
  try rfl

theorem symLift_move (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (w : LB.Iso L₁ (L₀.pull φ)) (hw : w.IsGen) {k : ℤ} {n : ℕ}
    {x₀ : T₀ ⟶ G} {θ₀ : ThetaGrp G L₀ k T₀} (h₀ : SymLift G L₀ k n x₀ θ₀) (hn : x₀ ^ n = 1) {x : T ⟶ A}
    (hx : x.left ≫ φ = τ ≫ x₀.left) :
    ∃ θ : ThetaGrp A L₁ k T, SymLift A L₁ k n x θ ∧
      PMaps w ![(snd T A).left, (translPt A θ.pt).left] ![(snd T₀ G).left, (translPt G θ₀.pt).left] ![k, -k]
        θ.φ θ₀.φ (psiO hp τ hτ).left := by
  obtain rfl := h₀.pt_eq
  obtain ⟨θ, rfl, hm⟩ := exists_theta_move hp τ hτ hL₀ hL₁ w hw k x θ₀ hx.symm
  have hxn : θ.pt ^ n = 1 := pow_eq_one hp τ hτ hx hn
  have hc : ∀ i, (![(snd T A).left, (translPt A θ.pt).left] : Fin 2 → _) i ≫ φ =
      (psiO hp τ hτ).left ≫ (![(snd T₀ G).left, (translPt G θ₀.pt).left] : Fin 2 → _) i := fun i => by
    fin_cases i
    · exact (psi_snd hp τ hτ).symm
    · exact (psi_tr hp τ hτ θ.pt θ₀.pt hx.symm).symm
  obtain ⟨nu₀, gnu₀, cnu₀⟩ := h₀.sym
  have hcn : ∀ i, (![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left] : Fin 2 → _) i ≫ φ =
      (psiO hp τ hτ).left ≫ (![(snd T₀ G).left, (snd T₀ G ≫ (GrpObj.inv : G ⟶ G)).left] : Fin 2 → _) i := fun i => by
    fin_cases i
    · exact (psi_snd hp τ hτ).symm
    · exact snd_inv_push hp τ hτ
  obtain ⟨nu, gnu, hmn⟩ := exists_gen_move hL₀ hL₁ w ((isGen_iff w).1 hw) _ _ ![k, -k] (psiO hp τ hτ).left hcn nu₀ gnu₀
  refine ⟨θ, ⟨rfl, ?_, nu, gnu, ?_⟩, hm⟩
  · refine corr_of_val hL₁ fun y J hJ => ?_
    choose J₀ hJ₀ using fun χ : (T ⊗ A).left ⟶ G.left => exists_chart hL₀ (χ y)
    have hG : Good L₀ y J₀ := hJ₀
    obtain ⟨g, hg⟩ : ∃ g : ℕ → ((T ⊗ A).left.presheaf.stalk y)ˣ, ∀ j, g j =
        gw w (translPt A (θ.pt ^ j)).left y (J₀ ((translPt A (θ.pt ^ j)).left ≫ φ)) (J (translPt A (θ.pt ^ j)).left) ^ k :=
      ⟨_, fun _ => rfl⟩
    have key : ∀ j : ℕ, val θ₀.φ ((psiO hp τ hτ).left ≫ (translT G (θ₀.pt ^ j)).left) y J₀ =
        g j / g (j + 1) * val θ.φ (𝟙 _ ≫ (translT A (θ.pt ^ j)).left) y J := fun j => by
      rw [← psi_transl hp τ hτ _ _ (pow_rel hp τ hτ hx j).symm, val_pmaps w hc hm _ y J₀ J hG hJ, Category.id_comp]
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [transl_snd, transl_pow_succ, zpow_neg, div_eq_mul_inv, hg, hg]
    have c := val_corr hG h₀.pow_eq (psiO hp τ hτ).left
    rw [val_powGenT θ₀ n _ y hG, val_one] at c
    rw [val_powGenT θ n _ y hJ, val_one]
    rw [Fin.prod_univ_eq_prod_range (fun j => val θ₀.φ ((psiO hp τ hτ).left ≫ (translT G (θ₀.pt ^ j)).left) y J₀)] at c
    rw [Fin.prod_univ_eq_prod_range (fun j => val θ.φ (𝟙 _ ≫ (translT A (θ.pt ^ j)).left) y J)]
    simp only [key, Finset.prod_mul_distrib, Finset.prod_range_div'] at c
    have gn : g n = g 0 := by rw [hg, hg, hxn, pow_zero]
    rwa [gn, div_self', _root_.one_mul] at c
  · refine corr_of_val hL₁ fun y J hJ => ?_
    choose J₀ hJ₀ using fun χ : (T ⊗ A).left ⟶ G.left => exists_chart hL₀ (χ y)
    have hG : Good L₀ y J₀ := hJ₀
    have c := val_corr hG cnu₀ (psiO hp τ hτ).left
    rw [val_symGen θ₀ nu₀ _ y hG, val_one] at c
    rw [val_symGen θ nu _ y hJ, val_one]
    have v1 := val_pmaps w hc hm (translT A θ.pt⁻¹).left y J₀ J hG hJ
    have v2 := val_pmaps w hcn hmn (𝟙 _) y J₀ J hG hJ
    have v3 := val_pmaps w hc hm (negT A T).left y J₀ J hG hJ
    have v4 := val_pmaps w hcn hmn (translT A θ.pt⁻¹).left y J₀ J hG hJ
    simp only [Category.id_comp] at v2 ⊢
    rw [← psi_transl hp τ hτ θ.pt⁻¹ θ₀.pt⁻¹ (inv_rel hp τ hτ hx).symm, ← negT_push hp τ hτ, v1, v2, v3, v4] at c
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at c
    rw [transl_inv_translPt, negT_snd', negT_translPt] at c
    apply Additive.ofMul.injective
    have b := congrArg Additive.ofMul c
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_one, zpow_neg] at b ⊢
    linear_combination (norm := abel) b

end Move

end ReciprocityTheory.ChartRestriction.G.PullbackSections.VtMove
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.VtMoveSt

section

@[expose] public section

set_option autoImplicit false


noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.VtMove

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1 ReciprocityTheory.ChartRestriction.G.PullbackSections
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.DVR

theorem snd_pow_left {S : Scheme.{0}} (A : Over S) [GrpObj A] (T : Over S) (N : ℕ) :
    (snd T A ^ N).left = (snd T A).left ≫ (mulA A N).left := by
  rw [← Over.comp_left, mulA, MonObj.comp_pow, Category.comp_id]

theorem sval_zc {S : Scheme.{0}} (A : Over S) {L : LB A.left} {T : Over S} {k₁ k₂ : ℤ} (h : k₁ = k₂)
    (F : LB.Sec (LPow A L k₁ T)) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) (J : (Z ⟶ A.left) → L.ι) :
    sval (zCast A h F) r z J = sval F r z J := by
  subst h; rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem vtOver_move {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f)
    (w : LB.Iso t'.PP.L (t.PP.L.pull m.φ)) (hw : RigIso m w) {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left)
    (hτ : τ ≫ T₀.hom = T.hom ≫ f) (N : ℕ) {ok : (T₀ ⟶ t.G) → Prop} (hok : ∀ u, ok u → u ^ (N ^ 2) = 1)
    {s₀ : LB.Sec (LPow t.G t.PP.L 1 T₀)} {tt : T₀ ⟶ t.G} {F : LB.Sec (LPow t.G t.PP.L ((N : ℤ) ^ 2) T₀)}
    (h : IsVtOver t.G t.PP N ok s₀ tt F) {s : LB.Sec (LPow t'.G t'.PP.L 1 T)} (hs : TieT m.cart τ hτ w 1 s₀ s) :
    ∃ F' : LB.Sec (LPow t'.G t'.PP.L ((N : ℤ) ^ 2) T),
      IsVtOver t'.G t'.PP N (fun u => u ^ (N ^ 2) = 1) s (liftPt m.cart τ hτ tt) F' ∧
        TieT m.cart τ hτ w ((N : ℤ) ^ 2) F F' := by
  obtain ⟨t₀', α₀, α, s₁, U, ht, o, g₀, n₀, cα, tw, sl, ac⟩ := h
  have h1 : (liftPt m.cart τ hτ t₀').left ≫ m.φ = τ ≫ t₀'.left := liftPt_left m.cart τ hτ t₀'
  have ht1 : liftPt m.cart τ hτ t₀' ^ N = liftPt m.cart τ hτ tt :=
    pt_ext m.cart ((pow_rel m.cart τ hτ h1 N).trans (by rw [ht]; exact (liftPt_left m.cart τ hτ tt).symm))
  have o1 : liftPt m.cart τ hτ t₀' ^ (N ^ 2) = 1 := pow_eq_one m.cart τ hτ h1 (hok _ o)
  obtain ⟨α₀', g₀', pm₀, n₀'⟩ := mulGen_move m w hw N α₀ g₀ n₀
  have eα : ∀ k, (![(snd T₀ t.G).left, (snd T₀ t.G ^ N).left] : Fin 2 → _) k =
      (snd T₀ t.G).left ≫ (![𝟙 t.G.left, (mulA t.G N).left] : Fin 2 → _) k := fun k => by
    fin_cases k
    · exact (Category.comp_id _).symm
    · exact snd_pow_left _ _ _
  obtain ⟨α₁, gα₁, Hα₁⟩ := exists_gen_pull (L := t.PP.L) ![𝟙 t.G.left, (mulA t.G N).left] ![(N : ℤ) ^ 2, -1] α₀
    (snd T₀ t.G).left _ eα
  have gα := gα₁ g₀
  have vα : ∀ y J, Good t.PP.L y J → val α (𝟙 _) y J = val α₁ (𝟙 _) y J := fun y J hJ =>
    (val_corr hJ cα _).trans ((val_pull hJ _ _ _).trans (val_of_pull eα Hα₁ _ y hJ).symm)
  have tw' : IsTwistPull t.G t.PP.L (mulT t.G T₀ N) (snd T₀ t.G ^ N) (lift_snd _ _) ((N : ℤ) ^ 2) 1 α₁ s₀ s₁ :=
    twist_of_val t.PP.isLB gα fun y J hJ => (twist_val tw (𝟙 _) y hJ).trans (by rw [vα y J hJ, Category.id_comp])
  obtain ⟨α', gα', pmα, cα'⟩ := MixEnd.genSnd_move m.cart τ hτ t.PP.isLB t'.PP.isLB w ((isGen_iff w).1 hw.1)
    (mulA t'.G N).left (mulA t.G N).left (mulA_push m.cart N) ![(N : ℤ) ^ 2, -1] α₀' α₀ pm₀ (snd T t'.G ^ N)
    (snd T₀ t.G ^ N) (snd_pow_left _ _ _) (snd_pow_left _ _ _) _ gα
    (corr_of_val t.PP.isLB fun y J hJ => (val_of_pull eα Hα₁ _ y hJ).trans (val_pull hJ _ _ _).symm)
  obtain ⟨s₁', tw1, hs1⟩ := twist_move m.cart τ hτ t'.PP.isLB w (ψA := mulT t'.G T N) (mA := snd T t'.G ^ N)
    (lift_snd _ _) (mulT_push m.cart τ hτ N) (snd_pow_push m.cart τ hτ N) gα' pmα tw' hs
  obtain ⟨U', sl', pmU⟩ := symLift_move m.cart τ hτ t.PP.isLB t'.PP.isLB w hw.1 sl (hok _ o) h1
  have hxU : τ ≫ U.pt.left = U'.pt.left ≫ m.φ := by rw [sl.pt_eq, sl'.pt_eq]; exact h1.symm
  obtain ⟨F', ac', hF⟩ := twist_move m.cart τ hτ t'.PP.isLB w (ψA := translT t'.G U'.pt)
    (mA := translPt t'.G U'.pt) (lift_snd _ _) (psi_transl m.cart τ hτ U'.pt U.pt hxU)
    (psi_tr m.cart τ hτ U'.pt U.pt hxU).symm U'.isGen pmU ac hs1
  exact ⟨F', ⟨liftPt m.cart τ hτ t₀', α₀', α', s₁', U', ht1, o1, g₀', n₀', cα', tw1, sl', ac'⟩, hF⟩

theorem vtMoveSt : VtMoveSt := by
  intro E _ _ _ H X₀ t₀ K _ x tK m1 w1 hw N ok s tt F hF hok sK hsK
  have hfst : ∀ {Z : Scheme.{0}} (r : Z ⟶ (𝟙_ (Over (Sp K)) ⊗ tK.G).left),
      r ≫ (fst (𝟙_ (Over (Sp K))) tK.G).left ≫ (𝟙_ (Over (Sp K))).hom = (r ≫ (snd _ tK.G).left) ≫ tK.G.hom := by
    intro Z r
    rw [Over.w (fst _ _), Category.assoc, Over.w (snd _ _)]
  have hs : TieT m1.cart (T₀ := Over.mk x) (𝟙_ (Over (Sp K))).hom rfl w1 1 s (zCast tK.G Nat.cast_one sK) := by
    intro Z r z J₀ J hJ₀ hJ
    have e := hsK Z (r ≫ (snd _ tK.G).left) (r ≫ (psiO m1.cart (T₀ := Over.mk x) (𝟙_ (Over (Sp K))).hom rfl).left) r
      (by rw [Category.assoc, psi_snd, Category.assoc])
      (by rw [Category.assoc, psi_fst]; exact hfst r) rfl z J₀ J hJ₀ hJ
    rw [sval_zc, Category.comp_id] at e
    rw [sval_zc, e, zpow_one, pow_one]
    rfl
  obtain ⟨F', hV, hT⟩ := vtOver_move m1 w1 hw (T₀ := Over.mk x) (𝟙_ (Over (Sp K))).hom rfl N hok hF hs
  refine ⟨_, F', hV, fun Z r zp zp' h1 h2 h3 z J J' hJ hJ' => ?_⟩
  subst h3
  obtain rfl : zp = zp' ≫ (psiO m1.cart (T₀ := Over.mk x) (𝟙_ (Over (Sp K))).hom rfl).left := by
    refine hom_ext₀ ?_ ?_
    · rw [Category.assoc, psi_fst, h2, hfst]
    · rw [Category.assoc, psi_snd, h1, Category.assoc]
  rw [sval_zc, sval_zc, hT Z zp' z J J' hJ hJ', Category.comp_id]
  congr 1

end ReciprocityTheory.ChartRestriction.G.PullbackSections.VtMove
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumSymmetricTranslatesThetaPullbackExtends

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

namespace GlobalTheory.HkIntegral.RegSum

def secSum {X : Scheme.{0}} {N : LB X} {n : ℕ} (F : Fin n → LB.Sec N) : LB.Sec N :=
  ⟨fun j => ∑ i, (F i).f j, fun a b => by

    simp only [map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => (F i).compat a b⟩

theorem sval_sum {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {n : ℕ}
    {a : LB.Sec (LB.LinComb L φ ε)} {F : Fin n → LB.Sec (LB.LinComb L φ ε)} (h : ∀ j, a.f j = ∑ i, (F i).f j)
    (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) : sval a r z J = ∑ i, sval (F i) r z J := by
  have hm := hJ.mem φ r
  refine (congrArg (gs r z _) (h _)).trans ((gs_eq r z _ hm _).trans ?_)
  exact ((congrArg _ (map_sum _ _ _)).trans (map_sum _ _ _)).trans
    (Finset.sum_congr rfl fun i _ => (gs_eq r z _ hm _).symm)

theorem zCast_sum {S : Scheme.{0}} (A : Over S) {L : LB A.left} {T : Over S} {a b : ℤ} (e : a = b) {n : ℕ}
    {t : LB.Sec (LPow A L a T)} {F : Fin n → LB.Sec (LPow A L a T)} (h : ∀ j, t.f j = ∑ i, (F i).f j) (j) :
    (PullbackSections.zCast A e t).f j = ∑ i, (PullbackSections.zCast A e (F i)).f j := by
  subst e
  exact h j

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}

theorem reg_sum (I : IntData Xo c T io y.1) (M : ℕ) {n : ℕ}
    {t : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((M : ℤ) ^ 2) (Over.mk (xOf y)))}
    {F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((M : ℤ) ^ 2) (Over.mk (xOf y)))}
    (h : ∀ j, t.f j = ∑ i, (F i).f j) (hF : ∀ i, Reg I M (F i)) : Reg I M t := by
  choose σ σt h1 h2 using hF
  refine ⟨secSum σ, secSum σt, fun Z r zp e1 e2 z J J' hJ hJ' => ?_, fun Z r z J J' hJ hJ' => ?_⟩
  · refine (sval_sum (zCast_sum _ _ h) zp z hJ).trans ?_
    rw [sval_sum (a := secSum σt) (F := σt) (fun _ => rfl) r z hJ', Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => h1 i Z r zp e1 e2 z J J' hJ hJ'
  · rw [sval_sum (a := secSum σt) (F := σt) (fun _ => rfl) r z hJ',
      sval_sum (a := secSum σ) (F := σ) (fun _ => rfl) _ z hJ, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => h2 i Z r z J J' hJ hJ'

theorem reg_of_isTransl (I : IntData Xo c T io y.1) (M : ℕ)
    (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((M : ℤ) ^ 2) (Over.mk (xOf y))))
    (P : PELUnif (IsLocalRing.maximalIdeal T.V) I.G) (hP : P.TorsionIso) (hM : IsUnit (M : T.V))
    (hF : letI := io.toAlgebra; IsTransl M y.1.s F) : Reg I M F := by
  let _ := io.toAlgebra
  obtain ⟨a, hVt⟩ := hF
  obtain ⟨θ, hθ, θK, hθ1, hθ2⟩ := PullbackSections.thetaTie _ _ _ _ _ _ T io y.1 I
  obtain ⟨ttK, FK, hVK, hFK⟩ := PullbackSections.VtMove.vtMoveSt _ _ _ _ _ y.1.x I.t' I.m1 I.w1 I.rig1 M _ y.1.s _ F hVt
    (fun u hu => hu) θK hθ1
  obtain ⟨σ, hσ⟩ := PullbackSections.regUnif_of' PullbackSections.thetaNu GlobalTheory.EndPullNu.main.2 GlobalTheory.FiniteLiftNu.finNu _ _ T.V I.G P hP θ hθ M hM
    I.t' I.m2 I.w2 I.rig2 θK hθ2 ttK FK hVK
  obtain ⟨σt, hσt⟩ := PullbackSections.exists_restrict I.t' _ (PullbackSections.zCast I.t'.G (PullbackSections.natCast_sq M) FK)
  have hg : ∀ {Z : Scheme.{0}} (r : Z ⟶ I.t'.G.left),
      (r ≫ PullbackSections.gsec I.t'.G) ≫ (snd (𝟙_ (Over (Sp T.Fr))) I.t'.G).left = r := fun r => by
    rw [Category.assoc, PullbackSections.gsec_snd, Category.comp_id]
  refine ⟨σ, σt, fun Z r zp h1 h2 z J J' hJ hJ' => ?_, fun Z r z J J' hJ hJ' => ?_⟩
  · rw [hσt Z r z J' hJ']
    exact hFK Z r zp (r ≫ PullbackSections.gsec I.t'.G) h1 h2 (hg r) z J J' hJ hJ'
  · rw [hσt Z r z J' hJ']
    exact hσ Z r (r ≫ PullbackSections.gsec I.t'.G) (hg r) z J J' hJ hJ'

theorem reg_of_isTranslSum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (I : IntData Xo c T io y.1) (M : ℕ) (t : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((M : ℤ) ^ 2) (Over.mk (xOf y)))), (∃ U : PELUnif (IsLocalRing.maximalIdeal T.V) I.G, U.TorsionIso) → IsUnit (M : T.V) → letI := io.toAlgebra; IsTranslSum M y.1.s t → Reg I M t := by
  intro E _ _ _ H Dw l Xo c T io y I M t ⟨P, hP⟩ hM ⟨n, F, hF, h⟩
  exact reg_sum I M h fun i => reg_of_isTransl I M (F i) P hP hM (hF i)

end GlobalTheory.HkIntegral.RegSum
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumSymmetricTranslatesThetaPullbackExtendsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

theorem _root_.GlobalTheory.T.sum_symmetricTranslates_thetaPullback_extends : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (I : IntData Xo c T io y.1) (M : ℕ) (t : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((M : ℤ) ^ 2) (Over.mk (xOf y)))), (∃ U : PELUnif (IsLocalRing.maximalIdeal T.V) I.G, U.TorsionIso) → IsUnit (M : T.V) → letI := io.toAlgebra; IsTranslSum M y.1.s t → Reg I M t := by
  first | exact @GlobalTheory.HkIntegral.RegSum.reg_of_isTranslSum | exact GlobalTheory.HkIntegral.RegSum.reg_of_isTranslSum | (intros; apply GlobalTheory.HkIntegral.RegSum.reg_of_isTranslSum <;> assumption)
end
end
