module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdditionFormulaAlgClosureWithExpansionsStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniquePullB
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpansionComponentsProportionalShiftMultipleStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiMulPsiOfAdditionFirstVariable
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsIntegralTensorLeftOfSmoothGrpObj
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalNeZeroOfIsIso
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValuesNatural
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
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PullbackSectionFamilyNeZeroIff
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TauBimultPsiEvenOverExtensionField
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaPsiRelationOfPullbackExtensionField
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaSectionSupportEqUnivStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiZeroMulRigV

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory

theorem psi_zero_mul_rigV : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (s₀ : Raw D F 1), PsiRel D (TF (R := R) F) s₀ → (∃ j, (s₀ 0).f j ≠ 0) → ∀ (z : (TF (R := R) F).left) J, Good D.P.L z J → val (Z := (TF (R := R) F).left) (D.psi (0)) (jFK (R := R) F) z J * rigV D z J = 1 := by
  intro R _ _ D F _ _ s₀ H hs z J hJ
  have hc : cT D (DegPre.BF D F) 0 = 1 := by
    have h := DVR.cPoint_add D (DegPre.BF D F) 0 0
    rw [add_zero] at h
    exact mul_eq_left.1 h.symm
  have := D.P.isAb.smooth
  have := D.P.isAb.geomConnected
  have : IsIntegral (TF (R := R) F).left := inferInstanceAs (IsIntegral (Spec (CommRingCat.of F)))
  have : IsIntegral (DegPre.BF D F).left :=
    isIntegral_tensor_left_of_smooth_grpObj _ D.P.A (TF (R := R) F)
  let ζ : (TF (R := R) F).left ⟶ (DegPre.BF D F).left := (DegPre.zF D F).left
  let p : DegPre.BF D F ⟶ TF (R := R) F := fst _ _
  have hζ : ζ ≫ p.left = 𝟙 _ := by
    show (DegPre.zF D F ≫ p).left = _
    rw [show DegPre.zF D F ≫ p = 𝟙 _ from lift_fst _ _]
    rfl
  let κ₀ : TF (R := R) F ⟶ TK R := Over.homMk (jFK (R := R) F) rfl
  let J' : ((DegPre.BF D F).left ⟶ D.P.A.left) → D.P.L.ι := fun ψ => J (ζ ≫ ψ)
  have hJ' : Good D.P.L (ζ z) J' := fun ψ => hJ (ζ ≫ ψ)
  have e := H 0 (DegPre.BF D F) p (p ≫ κ₀) (snd _ _) (ζ z) J' hJ'
  rw [hc, _root_.mul_one, show lift p (snd _ _) = 𝟙 (DegPre.BF D F) from lift_fst_snd] at e
  have hne : sval (s₀ 0) (𝟙 (DegPre.BF D F).left) (ζ z) J' ≠ 0 :=
    sval_ne_zero_of_isIso _ _ D.P.L D.P.isLB _ _ _ (s₀ 0) hs _ (𝟙 _) (ζ z) J' hJ'
  have e1 : (val (D.psi 0) (p ≫ κ₀).left (ζ z) J' * rigV D (ζ z) J').val = 1 :=
    (mul_eq_right₀ hne).1 e.symm
  have n1 := (values_natural _ _ _ _ D.P.L _ _ _ (p ≫ κ₀).left ζ z J hJ).2.2.1 (D.psi 0)
  have n2 := (values_natural _ _ _ _ D.P.L PUnit (fun _ => eSec D.P.A) (fun _ => 1)
    (DegPre.BF D F).hom ζ z J hJ).2.2.1 D.rig
  have a1 : ζ ≫ (p ≫ κ₀).left = jFK (R := R) F := by
    show ζ ≫ p.left ≫ jFK (R := R) F = _
    rw [← Category.assoc, hζ, Category.id_comp]
  have a2 : ζ ≫ (DegPre.BF D F).hom = (TF (R := R) F).hom := Over.w (DegPre.zF D F)
  rw [a1] at n1
  rw [a2] at n2
  apply Units.ext
  have e2 := congrArg (ζ.stalkMap z).hom e1
  rw [map_one, Units.val_mul, map_mul] at e2
  rw [Units.val_mul, Units.val_one]
  exact (congrArg₂ (· * ·) n1 n2).trans e2

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TauBimultPsiEvenOverExtensionFieldStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
theorem _root_.GlobalTheory.T.tau_bimult_psi_even_over_extension_field : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F], ((∀ (z : (TF (R := R) F).left) J, Good D.P.L z J → ∀ a b m : D.X, val (Z := (TF (R := R) F).left) (D.psi (a + b + m)) (jFK (R := R) F) z J * val (Z := (TF (R := R) F).left) (D.psi (a)) (jFK (R := R) F) z J * val (Z := (TF (R := R) F).left) (D.psi (b)) (jFK (R := R) F) z J * val (Z := (TF (R := R) F).left) (D.psi (m)) (jFK (R := R) F) z J * rigV D z J * cubV D.cub z J (cT D _ a) (cT D _ b) (cT D _ m) = val (Z := (TF (R := R) F).left) (D.psi (a + b)) (jFK (R := R) F) z J * val (Z := (TF (R := R) F).left) (D.psi (a + m)) (jFK (R := R) F) z J * val (Z := (TF (R := R) F).left) (D.psi (b + m)) (jFK (R := R) F) z J) ↔ D.TauBimult) ∧ ((∀ (z : (TF (R := R) F).left) J, Good D.P.L z J → ∀ m : D.X, val (Z := (TF (R := R) F).left) (D.psi (-m)) (jFK (R := R) F) z J * val D.sym (cT D (TF (R := R) F) m).left z J = val (Z := (TF (R := R) F).left) (D.psi (m)) (jFK (R := R) F) z J) ↔ D.PsiEven) := by
  first | exact @GlobalTheory.TauValues.main | exact GlobalTheory.TauValues.main | (intros; apply GlobalTheory.TauValues.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.BimultiplicativeTauOfThetaExpansionPsiRelation

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory

theorem cubeRel_of_two_comparisons {S : Type} [CommRing S] (c : S) (u k k' r pa pb pm p0 pab pam pbm pabm : Sˣ)
    (h₁ : (pam * pbm).val = c * (u * k * pa * pb).val) (h₂ : (pabm * pm).val = c * (u * k' * pab * p0).val)
    (hk : k' = 1) (h₀ : p0 * r = 1) : pabm * pa * pb * pm * r * k = pab * pam * pbm := by
  subst hk
  have h0 : (p0 : S) * r = 1 := by rw [← Units.val_mul, h₀, Units.val_one]
  ext
  simp only [Units.val_mul, Units.val_one] at h₁ h₂ ⊢
  linear_combination ((pa : S) * pb * k * r) * h₂ + (c * u * pab * pa * pb * k) * h0 - (pab : S) * h₁

theorem tauBimult_of_psiRel : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ f, U.Theta θ f → PsiRel D (𝟙_ _) f → D.TauBimult) := by
  intro hL hL2 V _ _ _ hV D A G _ _ U θ f hθ hψ
  have hG : GlobalFnsSt := hL.globalFns
  obtain ⟨th, hth, -⟩ := (GlobalTheory.UU.PullSec.pullEx V hV D A G U (Kbar V) (𝟙_ _) (toUnit _) 1).1 θ
  obtain ⟨s₀, hs₀, -⟩ := (GlobalTheory.UU.PullSec.pullEx V hV D A G U (Kbar V) (𝟙_ _) (toUnit _) 1).2 f
  obtain ⟨r, n, t, t', s, s', hr, hexp, -, hadd⟩ := GlobalTheory.T.additionFormula_algClosure_with_expansions hL hL2 V hV D A G U θ f hθ th s₀ hth hs₀
  have hP : PsiRel D (TF (R := V) (Kbar V)) s₀ := psiRel_of_pullB V D (Kbar V) f s₀ hs₀ hψ
  obtain ⟨hf, hsupp⟩ := GlobalTheory.T.thetaSection_support_eq_univ hL hL2 V hV D A G U θ f hθ
  have hne : ∃ j, (s₀ 0).f j ≠ 0 := (pullB_ne_zero_iff V D (Kbar V) 1 f s₀ hs₀ 0).2 (hf 0)
  refine (GlobalTheory.T.tau_bimult_psi_even_over_extension_field V D (Kbar V)).1.1 ?_
  intro z J hJ a b m
  obtain ⟨⟨u, hu, -⟩, -⟩ := ReciprocityTheory.ChartRestriction.G.DVR.gen_fe (D := D) (F := Kbar V) hG 2 m (a + b)
  obtain ⟨c, hc⟩ := GlobalTheory.T.expansionComponents_proportional_shift_multiple hL hL2 V hV D A G U 2 (by norm_num) (a + b) m u hu (hsupp (a + b))
  have hs : ∀ i z J, Good D.P.L z J → sval (s i (a + b + 2 • m)) (𝟙 _) z J =
      gs (𝟙 _) z ⊤ (DegPre.constBF D (Kbar V) c ⊤) *
        (sval (s i (a + b)) (DegPre.trF D (Kbar V) m).left z J * (val u (𝟙 _) z J).val) :=
    fun i => hc (t i) (s i) (hexp i).1
  have h₁ := psi_mul_psi_of_addition_first_variable V D (Kbar V) s₀ r n s s' hr hadd hP hne a b m (a + b) rfl c u hs z J hJ
  have h₂ := psi_mul_psi_of_addition_first_variable V D (Kbar V) s₀ r n s s' hr hadd hP hne (a + b) 0 m (a + b)
    (add_zero _).symm c u hs z J hJ
  rw [zero_add] at h₂
  have h₀ := psi_zero_mul_rigV V D (Kbar V) s₀ hP hne z J hJ
  have hc0 : cT D (TF (R := V) (Kbar V)) 0 = 1 := by
    have h := FirstSlot.cT_add D (TF (R := V) (Kbar V)) 0 0
    rw [add_zero] at h
    exact mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)
  have hk : cubV D.cub z J (cT D _ (a + b)) (cT D _ 0) (cT D _ m) = 1 := by
    rw [hc0]
    exact (isCub_cubV D.cub hJ).face₂ _ _
  exact cubeRel_of_two_comparisons _ _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ hk h₀

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.BimultiplicativeTauOfThetaExpansionPsiRelationStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

theorem _root_.GlobalTheory.T.bimultiplicative_tau_of_thetaExpansionPsiRelation : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ f, U.Theta θ f → PsiRel D (𝟙_ _) f → D.TauBimult) := by
  first | exact @GlobalTheory.tauBimult_of_psiRel | exact GlobalTheory.tauBimult_of_psiRel | (intros; apply GlobalTheory.tauBimult_of_psiRel <;> assumption)
end
end
