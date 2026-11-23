module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralRelationUniformisedHomConvolutionExpansiAlt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CrossRelationGivesConvolutionRelation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenOfIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegUnif
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalEqZeroOfSumMulCoord
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTorsionLift
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFrameRatio
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.StalkMapInjectiveOfFlat

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueEqZeroWeightIndependenceLevel

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.FieldBaseChange

noncomputable section

namespace GlobalTheory

namespace WeightValPart

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)

theorem coeff_eq_zero_over {Y : Over (Spec (CommRingCat.of R))} (p : Y ⟶ D.P.A) {X : Scheme.{0}} {N : LB X}
    (hN : N.IsLB) {ι₀ : D.P.A.left ⟶ X} {π : N.ι → D.P.L.ι} (hP : IsPart N D.P.L ι₀ π) {K : Type} [Fintype K]
    {φ : D.X → K → (Y.left ⟶ X)} {ε : K → ℤ} (d : ∀ α, LB.Sec (LB.LinComb N (φ α) ε)) (s : Finset D.X)
    (H : ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (r : Z ⟶ Y.left), r ≫ p.left = x ≫ g.pG.left →
      ∀ (z : Z) (J), Good N z J → ∑ α ∈ s, sval (d α) r z J * (val (g.t α) x z (rs ι₀ π J)).val = 0)
    (α : D.X) (hα : α ∈ s) (Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (x : Z ⟶ thickObj R I e G)
    (r : Z.left ⟶ Y.left) (hr : r ≫ p.left = x.left ≫ g.pG.left) (z : Z.left) (J) (hJ : Good N z J) :
    sval (d α) r z J = 0 := by
  classical
  let jf : D.X → K → N.ι := fun β a => J (r ≫ φ β a)
  let jt : D.X → Fin 4 → D.P.L.ι := fun β a => rs ι₀ π J (x.left ≫ D.Oφ g.pG β a)
  let V : Z.left.Opens := s.inf (fun β => r ⁻¹ᵁ LB.wchart N (φ β) (jf β) ⊓
      x.left ⁻¹ᵁ LB.wchart D.P.L (D.Oφ g.pG β) (jt β))
  have hz : z ∈ V := DVR.mem_finf s _ _ fun β _ => ⟨hJ.mem (φ β) r, (hP.good hJ).mem (D.Oφ g.pG β) x.left⟩
  have hVf : ∀ β ∈ s, V ≤ r ⁻¹ᵁ LB.wchart N (φ β) (jf β) :=
    fun β hβ => (Finset.inf_le hβ).trans inf_le_left
  have hVt : ∀ β ∈ s, V ≤ x.left ⁻¹ᵁ LB.wchart D.P.L (D.Oφ g.pG β) (jt β) :=
    fun β hβ => (Finset.inf_le hβ).trans inf_le_right
  have ex : ∀ β ∈ s, ∃ c : Γ(Z.left, V), ∀ (W : Scheme.{0}) (ρ : W ⟶ Z.left) (w : W),
      ρ w ∈ V → gs ρ w V c = gs (ρ ≫ r) w (LB.wchart N (φ β) (jf β)) ((d β).f (jf β)) *
        (gm (ρ ≫ x.left) w (LB.wchart D.P.L (D.Oφ g.pG β) (jt β)) ((g.t β).s (jt β))).val := fun β hβ =>
    ⟨(r.appLE _ V (hVf β hβ)).hom ((d β).f (jf β)) * (x.left.appLE _ V (hVt β hβ)).hom ((g.t β).s (jt β)).val,
      fun W ρ w hw => (gs_mul ρ w V hw _ _).trans (congrArg₂ (· * ·) (gs_appLE _ _ V _ ρ w hw _)
        ((gs_appLE _ _ V _ ρ w hw _).trans (gs_unit (ρ ≫ x.left) w _ (hVt β hβ hw) _)))⟩
  choose! c hc using ex
  have hsn : (WeightPf.Te D I e ◁ x).left ≫ (snd (WeightPf.Te D I e) (thickObj R I e G)).left =
      (snd (WeightPf.Te D I e) Z).left ≫ x.left := by
    rw [← Over.comp_left, ← Over.comp_left, whiskerLeft_snd]
  let σ : Z ⟶ WeightPf.Te D I e ⊗ Z := lift (toUnit _ ≫ η[WeightPf.Te D I e]) (𝟙 _)
  have hσ : σ.left ≫ (snd (WeightPf.Te D I e) Z).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_snd, Over.id_left]
  have H0 := WeightVal.eq_zero_of_stalk_sum D.X Z s c (fun w hw => by
    choose j hj using fun ψ : (WeightPf.Te D I e ⊗ Z).left ⟶ X => exists_chart hN (ψ w)
    let J₂ : ((WeightPf.Te D I e ⊗ Z).left ⟶ X) → N.ι := fun ψ =>
      if ψ w ∈ N.U (J (σ.left ≫ ψ)) then J (σ.left ≫ ψ) else j ψ
    have hJ₂ : Good N w J₂ := fun ψ => by
      by_cases h : ψ w ∈ N.U (J (σ.left ≫ ψ))
      · simpa only [J₂, if_pos h] using h
      · simpa only [J₂, if_neg h] using hj ψ
    have eJ : ∀ ψ : Z.left ⟶ X, ψ ((snd (WeightPf.Te D I e) Z).left w) ∈ N.U (J ψ) →
        J₂ ((snd (WeightPf.Te D I e) Z).left ≫ ψ) = J ψ := fun ψ h => by
      have e₁ : σ.left ≫ (snd (WeightPf.Te D I e) Z).left ≫ ψ = ψ := by
        rw [← Category.assoc, hσ, Category.id_comp]
      simp only [J₂, e₁]
      exact if_pos h
    have E := H _ ((WeightPf.Te D I e ◁ x).left ≫ (WeightPf.act g).left) ((snd (WeightPf.Te D I e) Z).left ≫ r)
      (by rw [Category.assoc, Category.assoc, hr, WeightPf.act_left_pG, ← Category.assoc, ← Category.assoc, hsn])
      w J₂ hJ₂
    refine Eq.trans (Finset.sum_congr rfl fun β hβ => ?_) E
    rw [hc β hβ _ _ w hw, WeightVal.val_act g β _ w (hP.good hJ₂), mul_left_comm, hsn, WeightVal.gs_chiP_whisker,
      sval_of (d β) _ w J₂ (jf β) (fun a => by
        rw [Category.assoc]; exact eJ _ (Set.mem_iInter.1 (hVf β hβ hw) a)),
      val_of (g.t β) _ w (rs ι₀ π J₂) (jt β) (fun a => by
        have m : ((x.left ≫ D.Oφ g.pG β a) ≫ ι₀) ((snd (WeightPf.Te D I e) Z).left w) ∈
            N.U (J ((x.left ≫ D.Oφ g.pG β a) ≫ ι₀)) := (hP.mem _ _).2 (Set.mem_iInter.1 (hVt β hβ hw) a)
        show π (J₂ ((((snd (WeightPf.Te D I e) Z).left ≫ x.left) ≫ D.Oφ g.pG β a) ≫ ι₀)) =
          π (J ((x.left ≫ D.Oφ g.pG β a) ≫ ι₀))
        rw [show (((snd (WeightPf.Te D I e) Z).left ≫ x.left) ≫ D.Oφ g.pG β a) ≫ ι₀ =
          (snd (WeightPf.Te D I e) Z).left ≫ ((x.left ≫ D.Oφ g.pG β a) ≫ ι₀) by simp only [Category.assoc], eJ _ m])]) α hα
  have E := hc α hα _ (𝟙 _) z hz
  rw [H0, gs_eq _ z V hz, map_zero, map_zero, Category.id_comp, Category.id_comp] at E
  exact (Units.mul_left_eq_zero _).1 E.symm

end WeightValPart

theorem sval_eq_zero_of_sum_mul_coord_part : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (Y : Over (Spec (CommRingCat.of R))) (p : Y ⟶ D.P.A) (X : Scheme.{0}) (N : LB X), N.IsLB → ∀ (ι₀ : D.P.A.left ⟶ X) (π : N.ι → D.P.L.ι), IsPart N D.P.L ι₀ π → ∀ (K : Type) [Fintype K] (φ : D.X → K → (Y.left ⟶ X)) (ε : K → ℤ) (d : ∀ α, LB.Sec (LB.LinComb N (φ α) ε)) (s : Finset D.X), (∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (r : Z ⟶ Y.left), r ≫ p.left = x ≫ g.pG.left → ∀ (z : Z) (J), Good N z J → ∑ α ∈ s, sval (d α) r z J * (val (g.t α) x z (rs ι₀ π J)).val = 0) → ∀ α ∈ s, ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (r : Z ⟶ Y.left), r ≫ p.left = x ≫ g.pG.left → ∀ (z : Z) (J), Good N z J → sval (d α) r z J = 0 := by
  intro R _ _ I D e G _ _ g Y p X N hN ι₀ π hP K _ φ ε d s H α hα Z x r hr z J hJ
  exact WeightValPart.coeff_eq_zero_over g p hN hP d s H α hα (Over.mk (x ≫ (thickObj R I e G).hom))
    (Over.homMk x rfl) r hr z J hJ

end GlobalTheory
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueEqZeroWeightIndependenceLevelStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.FieldBaseChange

theorem _root_.GlobalTheory.T.sectionValue_eq_zero_weightIndependence_level : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (Y : Over (Spec (CommRingCat.of R))) (p : Y ⟶ D.P.A) (X : Scheme.{0}) (N : LB X), N.IsLB → ∀ (ι₀ : D.P.A.left ⟶ X) (π : N.ι → D.P.L.ι), IsPart N D.P.L ι₀ π → ∀ (K : Type) [Fintype K] (φ : D.X → K → (Y.left ⟶ X)) (ε : K → ℤ) (d : ∀ α, LB.Sec (LB.LinComb N (φ α) ε)) (s : Finset D.X), (∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (r : Z ⟶ Y.left), r ≫ p.left = x ≫ g.pG.left → ∀ (z : Z) (J), Good N z J → ∑ α ∈ s, sval (d α) r z J * (val (g.t α) x z (rs ι₀ π J)).val = 0) → ∀ α ∈ s, ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (r : Z ⟶ Y.left), r ≫ p.left = x ≫ g.pG.left → ∀ (z : Z) (J), Good N z J → sval (d α) r z J = 0 := by
  first | exact @GlobalTheory.sval_eq_zero_of_sum_mul_coord_part | exact GlobalTheory.sval_eq_zero_of_sum_mul_coord_part | (intros; apply GlobalTheory.sval_eq_zero_of_sum_mul_coord_part <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralRelationKillsMixedSectionSumsLevel

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.FieldBaseChange GlobalTheory.Mum.Two.Mix

noncomputable section
namespace GlobalTheory.Mum.Two.Mix



theorem level : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (a : G₁ ⟶ G₂) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (h : D₂.toPre.X →+ D₁.toPre.X), Over₀ U₁ U₂ a b → ∀ (u : ∀ χ, LB.Gen (CmpLB D₁.toPre D₂.toPre b (h χ) χ)), (∀ χ (e : ℕ) (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G₁).left) (z : Z) (J), Good (JN D₁.toPre D₂.toPre) z J → val ((U₂.gt e).t χ) (x ≫ ((Over.pullback (thick R I e)).map a).left) z (rr J) = val ((U₁.gt e).t (h χ)) x z (rl J) * val (u χ) (x ≫ (U₁.gt e).pG.left) z J) → ∀ (j j' e : ℕ) (N : Type) [Fintype N] (ρ : N → R) (σ : N → H0 U₂.LG.L j) (σ' : N → H0 U₁.LG.L j') (f : N → ∀ α : D₂.toPre.X, D₂.toPre.SecB j α) (f' : N → ∀ α : D₁.toPre.X, D₁.toPre.SecB j' α), (∀ ν, U₂.ExpandsAt e j (σ ν) (f ν)) → (∀ ν, U₁.ExpandsAt e j' (σ' ν) (f' ν)) → (∀ (Z : Scheme.{0}) (r : Z ⟶ G₁.left) (z : Z) (J₁ J₂), Good U₁.LG.L z J₁ → Good U₂.LG.L z J₂ → ∑ ν, constVal (r ≫ G₁.hom) z (ρ ν) * (sval (σ ν) (r ≫ a.left) z J₂ * sval (σ' ν) r z J₁) = 0) → ∀ (m : ∀ α, {p : D₂.toPre.X × D₁.toPre.X // h p.1 + p.2 = α} → LB.Sec (LB.LinComb (JN D₁.toPre D₂.toPre) (mixφ D₁.toPre D₂.toPre b α) (MixedConv.mixε j j'))), (∀ α p (Z : Scheme.{0}) (r : Z ⟶ D₁.toPre.P.A.left) (z : Z) (J), Good (JN D₁.toPre D₂.toPre) z J → sval (m α p) r z J = ∑ ν, constVal (r ≫ D₁.toPre.P.A.hom) z (ρ ν) * (sval (f ν p.1.1) (r ≫ b.left) z (rr J) * sval (f' ν p.1.2) r z (rl J) * (val (u p.1.1) r z J * val (MixedConv.cubB D₁.toPre (h p.1.1) p.1.2) r z (rl J)).val)) → ∀ (α : D₁.toPre.X), ∃ S : Finset {p : D₂.toPre.X × D₁.toPre.X // h p.1 + p.2 = α}, ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e D₁.toPre.P.A).left) (z : Z) (J), Good (JN D₁.toPre D₂.toPre) z J → (∀ i ∉ S, sval (m α i) (r ≫ (D₁.toPre.prBe I e).left) z J = 0) ∧ ∑ i ∈ S, sval (m α i) (r ≫ (D₁.toPre.prBe I e).left) z J = 0 := by
  intro R _ _ I D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ U₁ U₂ a b h hO u hu j j' e N _ ρ σ σ' f f' hE hE' hrel m hm α
  classical
  obtain ⟨S, hS⟩ := MixedConv.expand_common U₂ e j σ f hE
  obtain ⟨S', hS'⟩ := MixedConv.expand_common U₁ e j' σ' f' hE'
  have pl := isPart_inl D₁.toPre.P.L D₂.toPre.P.L
  have pr := isPart_inr D₁.toPre.P.L D₂.toPre.P.L
  let ae := ((Over.pullback (thick R I e)).map a).left
  have hpe : ae ≫ pGl U₂ e = pGl U₁ e ≫ b.left := by
    have h₁ := congrArg (fun q => q.left) (hO e)
    have h₂ : ((Over.pullback (thick R I e)).map b).left ≫ pullback.fst _ _ = pullback.fst _ _ ≫ b.left :=
      pullback.lift_fst _ _ _
    show _ ≫ (U₂.gt e).q.left ≫ pullback.fst _ _ = ((U₁.gt e).q.left ≫ pullback.fst _ _) ≫ _
    rw [← Category.assoc]
    exact (congrArg (· ≫ pullback.fst _ _) h₁).trans ((Category.assoc _ _ _).trans
      ((congrArg ((U₁.gt e).q.left ≫ ·) h₂).trans (Category.assoc _ _ _).symm))
  have hfe : ae ≫ fGl I G₂ e = fGl I G₁ e ≫ a.left := pullback.lift_fst _ _ _
  have hp : ∀ {Z : Scheme.{0}} (x : Z ⟶ (thickObj R I e G₁).left),
      (x ≫ ae) ≫ pGl U₂ e = (x ≫ pGl U₁ e) ≫ b.left :=
    fun x => by rw [Category.assoc, Category.assoc, hpe]
  have hf : ∀ {Z : Scheme.{0}} (x : Z ⟶ (thickObj R I e G₁).left),
      (x ≫ ae) ≫ fGl I G₂ e = (x ≫ fGl I G₁ e) ≫ a.left :=
    fun x => by rw [Category.assoc, Category.assoc, hfe]
  let d : ∀ α, SecOver D₁.toPre.P.A.hom
      (LB.LinComb (JN D₁.toPre D₂.toPre) (mixφ D₁.toPre D₂.toPre b α) (MixedConv.mixε j j')) := fun α =>
    ∑ p ∈ (S ×ˢ S').subtype (fun p => h p.1 + p.2 = α), (m α p : SecOver D₁.toPre.P.A.hom _)
  have lift : ∀ n : LB.Sec (LB.LinComb (JN D₁.toPre D₂.toPre) (mixφ D₁.toPre D₂.toPre b α) (MixedConv.mixε j j')),
      (∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G₁).left) (z : Z) (J), Good (JN D₁.toPre D₂.toPre) z J →
        sval n (x ≫ pGl U₁ e) z J = 0) → ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e D₁.toPre.P.A).left) (z : Z) (J),
        Good (JN D₁.toPre D₂.toPre) z J → sval n (r ≫ (D₁.toPre.prBe I e).left) z J = 0 := fun n hn Z r z J hJ =>
    GlobalTheory.LiftTest.main R I D₁.toPre e G₁ (U₁.gt e) D₁.toPre.P.A (𝟙 _) _ (JN D₁.toPre D₂.toPre)
      (jn_isLB D₁.toPre D₂.toPre) _ _ _ n
      (fun Z x r hr z J hJ => by
        obtain rfl : r = x ≫ pGl U₁ e := (Category.comp_id r).symm.trans hr
        exact hn Z x z J hJ) Z _
      ⟨r ≫ pullback.snd _ _, by
        rw [Category.assoc, Category.assoc]; exact congrArg (r ≫ ·) pullback.condition.symm⟩ z J hJ
  refine ⟨(S ×ˢ S').subtype (fun p => h p.1 + p.2 = α), fun Z r z J hJ => ⟨fun i hi => ?_, ?_⟩⟩
  · refine lift _ (fun Z x z J hJ => ?_) Z r z J hJ
    rw [hm α i _ _ z J hJ]
    refine Finset.sum_eq_zero fun ν _ => ?_
    rw [Finset.mem_subtype, Finset.mem_product, not_and_or] at hi
    rcases hi with hi | hi
    · rw [← hp, (hS ν Z (x ≫ ae) z (rr J) (pr.good hJ)).1 _ hi, zero_mul, zero_mul, mul_zero]
    · rw [(hS' ν Z x z (rl J) (pl.good hJ)).1 _ hi, mul_zero, zero_mul, mul_zero]
  · refine (sval_sum' (π := D₁.toPre.P.A.hom) hJ _ _ _).symm.trans (lift (d α) (fun Z x z J hJ => ?_) Z r z J hJ)
    refine GlobalTheory.T.sectionValue_eq_zero_weightIndependence_level R I D₁.toPre e G₁ (U₁.gt e) D₁.toPre.P.A (𝟙 _) _ (JN D₁.toPre D₂.toPre)
      (jn_isLB D₁.toPre D₂.toPre) coprod.inl Prod.fst pl _
      (mixφ D₁.toPre D₂.toPre b) (MixedConv.mixε j j') d (insert α ((S ×ˢ S').image fun p => h p.1 + p.2)) ?_ α
      (Finset.mem_insert_self _ _) Z x _ (Category.comp_id _) z J hJ
    intro Z x r hr z J hJ
    obtain rfl : r = x ≫ pGl U₁ e := (Category.comp_id r).symm.trans hr
    have hJl : Good D₁.toPre.P.L z (rl J) := pl.good hJ
    have hJr : Good D₂.toPre.P.L z (rr J) := pr.good hJ
    obtain ⟨J₁, hJ₁⟩ := CoefBasic.exists_good' U₁.LG.isLB z
    obtain ⟨J₂, hJ₂⟩ := CoefBasic.exists_good' U₂.LG.isLB z
    let T : D₂.toPre.X × D₁.toPre.X → Z.presheaf.stalk z := fun p =>
      ∑ ν, constVal ((x ≫ pGl U₁ e) ≫ D₁.toPre.P.A.hom) z (ρ ν) *
      ((sval (f ν p.1) ((x ≫ ae) ≫ pGl U₂ e) z (rr J) * (val (tG U₂ e p.1) (x ≫ ae) z (rr J)).val) *
        (sval (f' ν p.2) (x ≫ pGl U₁ e) z (rl J) * (val (tG U₁ e p.2) x z (rl J)).val))
    have k₁ : ∀ β, sval (d β) (x ≫ pGl U₁ e) z J * (val ((U₁.gt e).t β) x z (rs coprod.inl Prod.fst J)).val =
        ∑ p ∈ (S ×ˢ S').filter (fun p => h p.1 + p.2 = β), T p := fun β => by
      refine (congrArg (· * _) (sval_sum' (π := D₁.toPre.P.A.hom) hJ _ _ _)).trans ?_
      rw [← Finset.sum_subtype_eq_sum_filter, Finset.sum_mul]
      refine Finset.sum_congr rfl fun p _ => ?_
      obtain ⟨⟨χ, δ⟩, rfl⟩ := p
      rw [hm _ _ _ _ z J hJ, Finset.sum_mul]
      refine Finset.sum_congr rfl fun ν _ => ?_
      have a₁ := congrArg Units.val (MixedConv.t_mul_val U₁ e (h χ) δ x z hJl)
      have a₂ := congrArg Units.val (hu χ e Z x z J hJ)
      simp only [Units.val_mul] at a₁ a₂ ⊢
      rw [hp]
      linear_combination (constVal ((x ≫ pGl U₁ e) ≫ D₁.toPre.P.A.hom) z (ρ ν) *
        sval (f ν χ) ((x ≫ pGl U₁ e) ≫ b.left) z (rr J) * sval (f' ν δ) (x ≫ pGl U₁ e) z (rl J) *
        (val (u χ) (x ≫ pGl U₁ e) z J).val) * a₁ -
        (constVal ((x ≫ pGl U₁ e) ≫ D₁.toPre.P.A.hom) z (ρ ν) *
        sval (f ν χ) ((x ≫ pGl U₁ e) ≫ b.left) z (rr J) * sval (f' ν δ) (x ≫ pGl U₁ e) z (rl J) *
        (val (tG U₁ e δ) x z (rl J)).val) * a₂
    refine (Finset.sum_congr rfl fun β _ => k₁ β).trans ((Finset.sum_fiberwise_of_maps_to (fun p hp =>
      Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hp)) T).trans ?_)
    have hc : (x ≫ pGl U₁ e) ≫ D₁.toPre.P.A.hom = (x ≫ fGl I G₁ e) ≫ G₁.hom := by
      rw [Category.assoc, Category.assoc]
      exact congrArg (x ≫ ·) ((Over.w (U₁.gt e).pG).trans (Over.w (fstG I e G₁)).symm)
    have k₂ := hrel Z (x ≫ fGl I G₁ e) z J₁ J₂ hJ₁ hJ₂
    rw [Finset.sum_comm]
    refine Eq.trans (Finset.sum_congr rfl fun ν _ => ?_) ((Finset.mul_sum _ _ _).symm.trans
      ((congrArg (((wv U₂ e (x ≫ ae) z (rr J ((x ≫ ae) ≫ pGl U₂ e)) (J₂ (((x ≫ ae) ≫ fGl I G₂ e) ≫ 𝟙 _)) ^ j).val *
        (wv U₁ e x z (rl J (x ≫ pGl U₁ e)) (J₁ ((x ≫ fGl I G₁ e) ≫ 𝟙 _)) ^ j').val) * ·) k₂).trans (mul_zero _)))
    rw [← Finset.mul_sum, Finset.sum_product]
    dsimp only
    rw [← Finset.sum_mul_sum, ← (hS ν Z (x ≫ ae) z (rr J) hJr).2 J₂ hJ₂,
      ← (hS' ν Z x z (rl J) hJl).2 J₁ hJ₁, hc, ← hf]
    ring

end GlobalTheory.Mum.Two.Mix
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralRelationKillsMixedSectionSumsLevelStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.FieldBaseChange GlobalTheory.Mum.Two.Mix

theorem _root_.GlobalTheory.T.integral_relation_kills_mixed_section_sums_level : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (a : G₁ ⟶ G₂) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (h : D₂.toPre.X →+ D₁.toPre.X), Over₀ U₁ U₂ a b → ∀ (u : ∀ χ, LB.Gen (CmpLB D₁.toPre D₂.toPre b (h χ) χ)), (∀ χ (e : ℕ) (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G₁).left) (z : Z) (J), Good (JN D₁.toPre D₂.toPre) z J → val ((U₂.gt e).t χ) (x ≫ ((Over.pullback (thick R I e)).map a).left) z (rr J) = val ((U₁.gt e).t (h χ)) x z (rl J) * val (u χ) (x ≫ (U₁.gt e).pG.left) z J) → ∀ (j j' e : ℕ) (N : Type) [Fintype N] (ρ : N → R) (σ : N → H0 U₂.LG.L j) (σ' : N → H0 U₁.LG.L j') (f : N → ∀ α : D₂.toPre.X, D₂.toPre.SecB j α) (f' : N → ∀ α : D₁.toPre.X, D₁.toPre.SecB j' α), (∀ ν, U₂.ExpandsAt e j (σ ν) (f ν)) → (∀ ν, U₁.ExpandsAt e j' (σ' ν) (f' ν)) → (∀ (Z : Scheme.{0}) (r : Z ⟶ G₁.left) (z : Z) (J₁ J₂), Good U₁.LG.L z J₁ → Good U₂.LG.L z J₂ → ∑ ν, constVal (r ≫ G₁.hom) z (ρ ν) * (sval (σ ν) (r ≫ a.left) z J₂ * sval (σ' ν) r z J₁) = 0) → ∀ (m : ∀ α, {p : D₂.toPre.X × D₁.toPre.X // h p.1 + p.2 = α} → LB.Sec (LB.LinComb (JN D₁.toPre D₂.toPre) (mixφ D₁.toPre D₂.toPre b α) (MixedConv.mixε j j'))), (∀ α p (Z : Scheme.{0}) (r : Z ⟶ D₁.toPre.P.A.left) (z : Z) (J), Good (JN D₁.toPre D₂.toPre) z J → sval (m α p) r z J = ∑ ν, constVal (r ≫ D₁.toPre.P.A.hom) z (ρ ν) * (sval (f ν p.1.1) (r ≫ b.left) z (rr J) * sval (f' ν p.1.2) r z (rl J) * (val (u p.1.1) r z J * val (MixedConv.cubB D₁.toPre (h p.1.1) p.1.2) r z (rl J)).val)) → ∀ (α : D₁.toPre.X), ∃ S : Finset {p : D₂.toPre.X × D₁.toPre.X // h p.1 + p.2 = α}, ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e D₁.toPre.P.A).left) (z : Z) (J), Good (JN D₁.toPre D₂.toPre) z J → (∀ i ∉ S, sval (m α i) (r ≫ (D₁.toPre.prBe I e).left) z J = 0) ∧ ∑ i ∈ S, sval (m α i) (r ≫ (D₁.toPre.prBe I e).left) z J = 0 := by
  first | exact @GlobalTheory.Mum.Two.Mix.level | exact GlobalTheory.Mum.Two.Mix.level | (intros; apply GlobalTheory.Mum.Two.Mix.level <;> assumption)
end
end
