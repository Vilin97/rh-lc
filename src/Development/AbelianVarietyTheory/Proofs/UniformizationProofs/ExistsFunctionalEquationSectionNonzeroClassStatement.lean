module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueFamOfReps
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CombBijective
public import Development.AbelianVarietyTheory.Definitions.Uniformization.SvalTwistOne
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RedIffReduction
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullUUnitsCompatGeneric
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPullSecSval
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSubSum
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTwistConvNeZero
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniquePullB
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.StalkMapInjectiveOfFlat
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpFOfExpT
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProdExpOppositeTranslates
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SecEqZeroOfSvalWhiskerRightEqZero
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalSecScale
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsFamRep

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGtPt

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.UU.TorPtEx

theorem exists_gtPt {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (T : Over (Spec (CommRingCat.of R)))
    (a : Multiplicative D.X →* Γ(T.left, ⊤)ˣ) : ∃ g : GtPt D T, g.b = 1 ∧
      ∀ (χ : D.X) (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) (J), Good D.P.L z J →
        val (g.s χ) r z J = gm r z ⊤ (a (Multiplicative.ofAdd χ)) := by
  have h1 : (LB.oneGen D.P.L (Y := T.left)).IsGen := fun _ _ =>
    (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm
  have key : ∀ χ : D.X, ∃ t : LB.Gen (LB.LinComb D.P.L (DegPre.gtφT D T 1 χ) DegPre.gtε), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) (J), Good D.P.L z J →
        val t r z J = gm r z ⊤ (a (Multiplicative.ofAdd χ)) := by
    intro χ
    obtain ⟨t, ht, hv⟩ := exists_gen D.P.isLB (φ' := DegPre.gtφT D T 1 χ) (ε' := DegPre.gtε) (fun U _ h => by
        have e₁ : padd D.P.A (DegPre.cT D T χ) 1 = DegPre.cT D T χ := _root_.mul_one (DegPre.cT D T χ)
        have e₂ : DegPre.zeroT D T = 1 := rfl
        simp [DegPre.gtφT, DegPre.gtε, Fin.prod_univ_succ, e₁, e₂])
      (DVR.scaleGen (a (Multiplicative.ofAdd χ)) (LB.oneGen D.P.L)) (DVR.scaleGen_isGen _ _ h1)
    refine ⟨t, ht, fun Z r z J hJ => (hv Z r z J hJ).trans ?_⟩
    exact ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z le_top (hJ.mem PEmpty.elim r) _) (val_one r))).trans
      (_root_.mul_one _)
  choose s hs hv using key
  refine ⟨⟨1, s, hs, corr_of_val D.P.isLB fun y J hJ => ?_, fun χ χ' => corr_of_val D.P.isLB fun y J hJ => ?_⟩, rfl, hv⟩
  · rw [hv 0 _ _ y J hJ, val_one, ofAdd_zero, map_one, map_one]
  · have c := (val_cub D.cub (𝟙 T) hJ (DegPre.cT D T χ) (DegPre.cT D T χ') 1).trans
      ((congrArg (cubV D.cub y J _ _) (Category.id_comp (1 : T ⟶ D.P.A))).trans ((isCub_cubV D.cub hJ).face₃ _ _))
    refine ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (hv _ _ _ y J hJ) c)).trans
      (Eq.trans ?_ ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (hv _ _ _ y J hJ) (hv _ _ _ y J hJ))).symm)
    rw [_root_.mul_one, ofAdd_add, map_mul, map_mul]; rfl

theorem main : AllPre fun {V} _ _ _ {D} {_} {G} _ _ U => ∀ (W : Type) [CommRing W] [IsLocalRing W] [Algebra V W], FinExt V W → ∀ a : Multiplicative D.X →* Wˣ, ∃ x : TA V W ⟶ G, U.TorPt a x := by
  intro V _ _ _ hV D A G _ _ U W _ _ _ hW a
  obtain ⟨g, hb, hv⟩ := exists_gtPt D (TA V W)
    ((Units.map (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom.toMonoidHom).comp a)
  obtain ⟨x, hx, -⟩ := RedOnto.main V hV D A G U W hW g
  refine ⟨x, fun e Z r xe h => ?_⟩
  obtain ⟨h₁, h₂⟩ := hx e Z r xe h
  refine ⟨hb ▸ h₁, fun χ z J hJ => ?_⟩
  rw [h₂ χ z J hJ, hv χ Z r z J hJ, gm_val r z ⊤ trivial, gs_eq _ z ⊤ trivial]
  rfl

end GlobalTheory.UU.TorPtEx

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Imports

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.NullExp

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (T : Over (Spec (CommRingCat.of R))) (k : ℕ) (σ : U.SecGT T k) (f : ∀ α, SecBT D T k α), U.ExpT T k σ f → NullFam I f := by
  intro R _ _ I D A G _ _ U T k σ f H e
  obtain ⟨s, hs⟩ := H e
  refine ⟨s, fun α hα Z r hr z J hJ => ?_⟩
  refine GlobalTheory.LiftTest.main R I D e G (U.gt e) (T ⊗ D.P.A) (snd T D.P.A) _ D.P.L D.P.isLB _ _ _ (f α)
    ?_ Z r hr z J hJ
  intro Z x r hx z J hJ
  have hc : (r ≫ (fst T D.P.A).left) ≫ T.hom = (x ≫ (fstG I e G).left) ≫ G.hom := by
    rw [Category.assoc, Category.assoc, Over.w (fst T D.P.A), Over.w (fstG I e G), ← Over.w (snd T D.P.A),
      ← Category.assoc, hx, Category.assoc, Over.w (U.gt e).pG]
  let rG : Z ⟶ (T ⊗ G).left := pullback.lift (r ≫ (fst T D.P.A).left) (x ≫ (fstG I e G).left) hc
  choose JG hJG using fun χ : Z ⟶ G.left => exists_chart U.P.L.isLB (χ z)
  exact (hs Z x rG r (pullback.lift_snd _ _ _) hx (pullback.lift_fst _ _ _).symm z JG J hJG hJ).1 α hα

end GlobalTheory.NullExp
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IntegralWitness

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
namespace GlobalTheory.UU.IntWit

theorem gs_zero {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) : gs f y U 0 = 0 := by
  unfold gs
  split_ifs
  · simp only [map_zero]
  · rfl

theorem sval_eq_zero {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (h : ∀ j, s.f j = 0) (r : Z ⟶ Y) (z : Z) (J) : sval s r z J = 0 :=
  (congrArg (gs r z _) (h _)).trans (gs_zero r z _)

theorem eq_zero_of_sval {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (h : ∀ y J, Good L y J → sval s (𝟙 Y) y J = 0) (j : K → L.ι) :
    s.f j = 0 := by
  refine fn_ext (V := LB.wchart L φ j) fun y hy => ?_
  obtain ⟨J, hJ, e⟩ := sval_trans hL s y j hy
  rw [h y J hJ, mul_zero] at e
  exact e.trans (gs_zero _ _ _).symm

theorem integral_witness : AllPre fun {V} _ _ _ {D} {_} {_} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ) (β : D.X), U.FE F k → U.Supp F k β → ∃ (σ : U.SecGT (𝟙_ _) k) (f : ∀ α, SecBT D (𝟙_ _) k α) (s : Raw D F k), U.ExpT (𝟙_ _) k σ f ∧ PullB D F (toUnit _) k f s ∧ DegPre.FamFE D F k s ∧ (∃ j, (s β).f j ≠ 0) ∧ ∃ j, (f β).f j ≠ 0 := by
  intro V _ _ _ hV D A G _ _ U F _ _ k β hFE hS
  obtain ⟨t, s, ⟨n, c, σ, f, hE, -, hB⟩, j₀, hj₀⟩ := hS
  obtain ⟨hG, hP⟩ := GlobalTheory.UU.PullSec.pullEx V hV D A G U F (𝟙_ _) (toUnit _) k
  choose s' hs' using fun i => (hP (f i)).exists
  have hex : ∃ i, ∃ j, (s' i β).f j ≠ 0 := by
    by_contra hn
    push Not at hn
    refine hj₀ (eq_zero_of_sval D.P.isLB (s β) (fun y J hJ => ?_) j₀)
    have w : (toUnit (TF (R := V) F) ▷ D.P.A).left ≫ (snd (𝟙_ _) D.P.A).left = (snd _ D.P.A).left :=
      congrArg CommaMorphism.left (whiskerRight_snd (toUnit (TF (R := V) F)) D.P.A)
    refine (hB β _ (𝟙 _) (toUnit (TF (R := V) F) ▷ D.P.A).left (w.trans (Category.id_comp _).symm) y J hJ).trans ?_
    refine Finset.sum_eq_zero fun i _ => ?_
    exact (congrArg (_ * ·) ((hs' i β y J hJ).symm.trans (sval_eq_zero _ (hn i) _ _ _))).trans (mul_zero _)
  obtain ⟨i, j, hj⟩ := hex
  obtain ⟨t', ht'⟩ := (hG (σ i)).exists
  refine ⟨σ i, f i, s' i, hE i, hs' i,
    hFE t' (s' i) (IntExp.expF_of_expT V _ D A G U F k (σ i) (f i) t' (s' i) (hE i) ht' (hs' i)), ⟨j, hj⟩, ?_⟩
  by_contra hn
  push Not at hn
  exact hj (eq_zero_of_sval D.P.isLB (s' i β)
    (fun y J hJ => (hs' i β y J hJ).trans (sval_eq_zero _ hn _ _ _)) j)

end GlobalTheory.UU.IntWit
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFunctionalEquationSectionNonzeroClass

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU.FESection

theorem main : Laws → Laws2 → AllPre fun {V} _ _ _ {D} {_} {_} _ _ U => D.TauBimult → ∀ k : ℕ, 1 ≤ k → U.FE (Kbar V) 1 → U.FE (Kbar V) k → (∃ β, U.Supp (Kbar V) 1 β) → (∃ β, U.Supp (Kbar V) k β) → ∀ α, ∃ t s, U.ExpF (Kbar V) (k + 1) t s ∧ DegPre.FamFE D (Kbar V) (k + 1) s ∧ ∃ j, (s α).f j ≠ 0 := by
  intro hL hL2 V _ _ _ hV D A G _ _ U hB k hk hF1 hFk ⟨β₁, hβ₁⟩ ⟨β₀, hβ₀⟩ α
  have hG := hL.globalFns
  obtain ⟨σ, f, sf, hσ, hpf, hfef, -, hf0⟩ := IntWit.integral_witness V hV D A G U (Kbar V) k β₀ hFk hβ₀
  obtain ⟨ϑ, g, sg, hϑ, hpg, hfeg, ⟨j₁, hs1⟩, -⟩ := IntWit.integral_witness V hV D A G U (Kbar V) 1 β₁ hF1 hβ₁
  have hg0 : ∃ j, (g (α - β₀)).f j ≠ 0 := by
    by_contra hn
    push_neg at hn
    have h1 : ∀ j, (sg (α - β₀)).f j = 0 := fun j =>
      sec_ext_val (s' := DVR.SecOps.secZero) D.P.isLB (fun y J hJ => by
        rw [hpg _ y J hJ, DVR.UUA.sval_zero_of hn _ y J (hJ.mem _ _),
          DVR.UUA.sval_zero_of (s := DVR.SecOps.secZero) (fun _ => rfl) _ y J (hJ.mem _ _)]) j
    exact hs1 (FamFree.zero_of_eq_add_nsmul hG (⟨sg, hfeg⟩ : Fam D (Kbar V) 1)
      ⟨β₁ - (α - β₀), by rw [one_smul, add_sub_cancel]⟩ h1 j₁)
  obtain ⟨W, _, _, _, φ, a, hW, hφ, hnv⟩ := GlobalTheory.UU.exists_twist_conv_ne_zero V hV D k f g α β₀
    (GlobalTheory.NullExp.main V _ D A G U _ k σ f hσ) hf0 hg0
  obtain ⟨σ', f', hσ', hff, hpf'⟩ := expT_pull V _ D A G U _ (TA V W) (toUnit _) k σ f hσ
  obtain ⟨ϑ', g', hϑ', hgg, hpg'⟩ := expT_pull V _ D A G U _ (TA V W) (toUnit _) 1 ϑ g hϑ
  have hu : φ ≫ toUnit _ = toUnit _ := toUnit_unique _ _
  obtain ⟨x, hx⟩ := TorPtEx.main V hV D A G U W hW a
  obtain ⟨σ'', hprod⟩ := GlobalTheory.UU.prodExp_opposite_translates hG V hV D A G U W hW a x hx k σ' ϑ' f' g' hσ' hϑ'
  obtain ⟨h, hh, hext⟩ := GlobalTheory.UU.ExpExt.main hL hL2 V hV D A G U W hW (k + 1) (by omega) σ''
  have hconv := GlobalTheory.ConvOfProd.main V _ D A G U _ k 1 _ _ h σ'' hprod hh
  obtain ⟨ht, hs⟩ := PullSec.pullEx V hV D A G U (Kbar V) (TA V W) φ (k + 1)
  obtain ⟨t, ht, -⟩ := ht σ''
  obtain ⟨s, hs, -⟩ := hs h
  refine ⟨t, s, hext _ φ t s ht hs, ?_, ?_⟩
  · refine GlobalTheory.ConvFE.conv_famFE hG V hV D hB W hW (Kbar V) φ hφ k 1 f' g' h sf sg s a (a ^ k)⁻¹ (fun mu => ?_)
      ((hpf' _ φ sf).2 (hu ▸ hpf)) ((hpg' _ φ sg).2 (hu ▸ hpg)) hs hfef hfeg hconv
    rw [one_smul, ofAdd_nsmul, map_pow, MonoidHom.inv_apply, MonoidHom.pow_apply, mul_inv_cancel]
  · obtain ⟨j, hj⟩ := hnv f' g' h hff hgg hconv
    by_contra hn
    push_neg at hn
    haveI := D.P.isAb.smooth
    haveI : Flat D.P.A.hom := inferInstance
    haveI : IsAffine (TA V W).left := inferInstanceAs (IsAffine (Spec _))
    haveI : IsAffine (TF (R := V) (Kbar V)).left := inferInstanceAs (IsAffine (Spec _))
    refine hj (sec_eq_zero_of_sval_whiskerRight_eq_zero _ D.P.A _ _ φ hφ _ D.P.L D.P.isLB _ _ _ (h α)
      (fun z J hJ => ?_) j)
    exact (hs α z J hJ).symm.trans (DVR.UUA.sval_zero_of hn _ z J (hJ.mem _ _))

end GlobalTheory.UU.FESection
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFunctionalEquationSectionNonzeroClassStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

theorem _root_.GlobalTheory.T.exists_functionalEquation_section_nonzero_class : Laws → Laws2 → AllPre fun {V} _ _ _ {D} {_} {_} _ _ U => D.TauBimult → ∀ k : ℕ, 1 ≤ k → U.FE (Kbar V) 1 → U.FE (Kbar V) k → (∃ β, U.Supp (Kbar V) 1 β) → (∃ β, U.Supp (Kbar V) k β) → ∀ α, ∃ t s, U.ExpF (Kbar V) (k + 1) t s ∧ DegPre.FamFE D (Kbar V) (k + 1) s ∧ ∃ j, (s α).f j ≠ 0 := by
  first | exact @GlobalTheory.UU.FESection.main | exact GlobalTheory.UU.FESection.main | (intros; apply GlobalTheory.UU.FESection.main <;> assumption)
end
end
