module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSiegelObjectOddLevelRigid
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FixTorsionOfForallGeometric
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIdCompCancel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenOfIso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointTorusPartEqOfEquivSameLatticeStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfPresentationsSamePolarisationLevel

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

noncomputable section

namespace GlobalTheory.LowSame

open GlobalTheory.SiegLev GlobalTheory.CechPic GlobalTheory.AmpleRigid GlobalTheory.SiegRigid

theorem eq_of_cls_lev {h n : ℕ} {B : Type} [CommRing B] {ζ : B} {S S' : Scheme.{0}} {s : S ⟶ Sp B}
    (c : SiegPre h n ζ s) (hζ : IsUnit ζ) (hnB : IsUnit (n : B)) (hn : 3 ≤ n) (hc : c.Principal)
    {A' : Over S'} [GrpObj A'] (hab' : IsAbelianScheme A') (f : S' ⟶ S) (φ φ' : A'.left ⟶ c.A.left)
    (g : IsGrpPullback A' c.A f φ) (g' : IsGrpPullback A' c.A f φ')
    (hcl : pull φ (cls c.diag (pull_isLB c.isLB _)) = pull φ' (cls c.diag (pull_isLB c.isLB _)))
    (lv : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S') ⟶ A'))
    (l : ∀ a, (lv a).left ≫ φ = f ≫ (c.lev a).left) (l' : ∀ a, (lv a).left ≫ φ' = f ≫ (c.lev a).left) :
    φ = φ' := by
  obtain ⟨σ, hσ, e⟩ := exists_aut g g'
  have key : σ.hom = 𝟙 _ := by
    refine eq_id_of_forall_geometric_fibre laws_without_cohomology.1 A' hab' σ.hom (IsMonHom.one_hom σ.hom)
      fun t => ?_
    let K : Type := AlgebraicClosure (S'.residueField t)
    let j : Sp K ⟶ S' := Spec.map (CommRingCat.ofHom (algebraMap (S'.residueField t) K)) ≫ S'.fromSpecResidueField t
    have hp := isGrpPullback_pullback A' j
    have := hab'.smooth
    have := hab'.proper
    have := hab'.geomConnected
    have := hab'.comm
    have hab : IsAbelianScheme ((Over.pullback j).obj A') :=
      { comm := Functor.isCommMonObj_obj
        smooth := by change Smooth (pullback.snd A'.hom j); infer_instance
        proper := by change IsProper (pullback.snd A'.hom j); infer_instance
        geomConnected := by change GeometricallyConnected (pullback.snd A'.hom j); infer_instance }
    have hNK : (n : K) ≠ 0 := by
      have hu := hnB.map (Spec.preimage ((j ≫ f) ≫ s)).hom
      rw [map_natCast] at hu
      exact hu.ne_zero
    have e' := eq_of_field (pull_isLB c.isLB _) hc.1 hab (hp.comp g) (hp.comp g')
      (by rw [pull_comp, pull_comp]; exact congrArg _ hcl) hn hNK
      fun Ω _ _ x y hy => by
        have hy₁ : pushHom hp (Over.mk x) y ^ n = 1 := by rw [← map_pow, hy, map_one]
        have e₁ := eq_on_torsion hζ c g lv l l' Ω (x ≫ j) _ hy₁
        rw [← Category.assoc, ← Category.assoc]
        exact e₁
    refine ⟨_, _, j, _, _, (default : PrimeSpectrum K), ?_, hp.1, ?_⟩
    · exact (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply t _)
    · apply g'.1.hom_ext
      · rw [Category.assoc, e]
        exact e'
      · rw [Category.assoc, Over.w]
  rw [← e, key, Over.id_left, Category.id_comp]

end GlobalTheory.LowSame

namespace GlobalTheory.LowSame

open GlobalTheory.SiegelPullComp

theorem eq_of_presentations : ∀ {o : Type} [CommRing o] {ζ : o} {h n : ℕ} (F' : SFam h n ζ), 3 ≤ n → IsUnit ζ → IsUnit (n : o) → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (A : Over (Sp V)) [GrpObj A] [IsCommMonObj A] (t₁ t₂ : Sp V ⟶ F'.X) (a₁ a₂ : A.left ⟶ F'.univ.A.left) (aa₁ aa₂ : (G2 A).left ⟶ (G2 F'.univ.A).left), IsGrpPullback A F'.univ.A t₁ a₁ → IsGrpPullback A F'.univ.A t₂ a₂ → IsSquare a₁ aa₁ → IsSquare a₂ aa₂ → LBIso (F'.univ.P.pull aa₁) (F'.univ.P.pull aa₂) → t₁ ≫ F'.s = t₂ ≫ F'.s → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F], (∀ l, ∃ x : TF (R := V) F ⟶ A, x.left ≫ a₁ = (TF (R := V) F).hom ≫ t₁ ≫ (F'.univ.lev l).left ∧ x.left ≫ a₂ = (TF (R := V) F).hom ≫ t₂ ≫ (F'.univ.lev l).left) → t₁ = t₂ ∧ a₁ = a₂ := by
  intro o _ ζ h n F' hn hζ hno V _ _ _ A _ _ t₁ t₂ a₁ a₂ aa₁ aa₂ ha₁ ha₂ sq₁ sq₂ hP hs F _ _ hlev
  let c' := GlobalTheory.LowChart.siegPull F'.univ t₁ (t₁ ≫ F'.s) rfl
  have m₁ : SiegPB c' F'.univ t₁ := GlobalTheory.LowChart.siegPB_siegPull _ _ _ _
  obtain ⟨pφ, pφ₂, gp, psq, pw, pl⟩ := id m₁
  let F₀ : c'.A.left ⟶ A.left := ha₁.1.lift pφ c'.A.hom gp.1.w
  have hF : F₀ ≫ a₁ = pφ := ha₁.1.lift_fst _ _ _
  have hFw : F₀ ≫ A.hom = c'.A.hom ≫ 𝟙 _ := (ha₁.1.lift_snd _ _ _).trans (Category.comp_id _).symm
  have hF₀ : IsGrpPullback c'.A A (𝟙 _) F₀ :=
    ha₁.cancel (gp.congr (Category.id_comp _).symm hF.symm) hFw
  have gφ : IsGrpPullback c'.A F'.univ.A t₂ (F₀ ≫ a₂) := (hF₀.comp ha₂).congr (Category.id_comp _) rfl
  let U : Over.mk ((c'.A ⊗ c'.A).hom ≫ 𝟙 _) ⟶ A ⊗ A :=
    lift (pushPt hFw (fst c'.A c'.A)) (pushPt hFw (snd c'.A c'.A))
  let F₂ : (c'.A ⊗ c'.A).left ⟶ (A ⊗ A).left := U.left
  have h₁ : F₂ ≫ (fst A A).left = (fst c'.A c'.A).left ≫ F₀ :=
    congrArg (fun q => q.left) (lift_fst (pushPt hFw (fst c'.A c'.A)) (pushPt hFw (snd c'.A c'.A)))
  have h₂ : F₂ ≫ (snd A A).left = (snd c'.A c'.A).left ≫ F₀ :=
    congrArg (fun q => q.left) (lift_snd (pushPt hFw (fst c'.A c'.A)) (pushPt hFw (snd c'.A c'.A)))
  have h₃ : F₂ ≫ aa₁ = pφ₂ := by
    apply pullback.hom_ext
    · show (_ ≫ _) ≫ (fst F'.univ.A F'.univ.A).left = _ ≫ (fst F'.univ.A F'.univ.A).left
      rw [Category.assoc, sq₁.1, ← Category.assoc, h₁, Category.assoc, hF, psq.1]
    · show (_ ≫ _) ≫ (snd F'.univ.A F'.univ.A).left = _ ≫ (snd F'.univ.A F'.univ.A).left
      rw [Category.assoc, sq₁.2, ← Category.assoc, h₂, Category.assoc, hF, psq.2]
  have sq : IsSquare (F₀ ≫ a₂) (F₂ ≫ aa₂) :=
    ⟨by rw [Category.assoc, sq₂.1, ← Category.assoc, h₁, Category.assoc],
     by rw [Category.assoc, sq₂.2, ← Category.assoc, h₂, Category.assoc]⟩
  have hU := F'.univ.isLB
  have iso : LBIso c'.P (F'.univ.P.pull (F₂ ≫ aa₂)) := by
    rw [← h₃] at pw
    refine pw.trans c'.isLB (pull_isLB hU _) (pull_isLB hU _) ?_
    refine (iso_pull_pull hU aa₁ F₂).symm.trans (pull_isLB hU _) (pull_isLB (pull_isLB hU _) _) (pull_isLB hU _) ?_
    refine (iso_pull F₂ hP).trans (pull_isLB (pull_isLB hU _) _) (pull_isLB (pull_isLB hU _) _) (pull_isLB hU _) ?_
    exact iso_pull_pull hU aa₂ F₂
  have lev : ∀ a, (c'.lev a).left ≫ (F₀ ≫ a₂) = t₂ ≫ (F'.univ.lev a).left := by
    intro a
    have hσ : ((c'.lev a).left ≫ F₀) ≫ A.hom = 𝟙 _ := by
      rw [Category.assoc, hFw, Category.comp_id]
      exact Over.w (c'.lev a)
    have hσ₁ : ((c'.lev a).left ≫ F₀) ≫ a₁ = t₁ ≫ (F'.univ.lev a).left := by
      rw [Category.assoc, hF]; exact pl a
    obtain ⟨x, hx₁, hx₂⟩ := hlev a
    have hx : x.left = (TF (R := V) F).hom ≫ (c'.lev a).left ≫ F₀ := by
      apply ha₁.1.hom_ext
      · rw [hx₁, Category.assoc, hσ₁]
      · rw [Over.w x, Category.assoc, hσ]
        exact (Category.comp_id _).symm
    have := F'.univ.ab.proper
    have : IsReduced (𝟙_ (Over (Sp V))).left := (inferInstance : IsReduced (Sp V))
    have := ReciprocityTheory.ChartRestriction.G.DVR.GC.isDominant_jFR (V := V) F
    refine ext_of_isDominant_of_isSeparated F'.univ.A.hom ?_ (DegPre.jFR (R := V) F) ?_
    · rw [Category.assoc, Category.assoc, ha₂.1.w, ← Category.assoc, ← Category.assoc, hσ, Category.id_comp,
        Category.assoc, Over.w (F'.univ.lev a)]
      rfl
    · rw [← Category.assoc]
      show ((TF (R := V) F).hom ≫ (c'.lev a).left ≫ F₀) ≫ a₂ = (TF (R := V) F).hom ≫ t₂ ≫ (F'.univ.lev a).left
      rw [← hx]
      exact hx₂
  have m₂ : SiegPB c' F'.univ t₂ := ⟨F₀ ≫ a₂, F₂ ≫ aa₂, gφ, sq, iso, lev⟩
  have ht : t₁ = t₂ := F'.inj V t₁ t₂ (t₁ ≫ F'.s) c' hs m₁ m₂
  subst ht
  refine ⟨rfl, ?_⟩
  have hcl := (GlobalTheory.SiegRigid.pull_cls_diag psq pw).trans (GlobalTheory.SiegRigid.pull_cls_diag sq iso).symm
  have e := eq_of_cls_lev F'.univ hζ hno hn F'.princ c'.ab t₁ pφ (F₀ ≫ a₂) gp gφ hcl c'.lev pl lev
  have : IsIso F₀ := hF₀.1.isIso_fst_of_isIso
  rw [← hF] at e
  exact (cancel_epi F₀).1 e

end GlobalTheory.LowSame

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfPresentationsSamePolarisationLevelStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

theorem _root_.GlobalTheory.T.eq_of_presentations_same_polarisation_level : ∀ {o : Type} [CommRing o] {ζ : o} {h n : ℕ} (F' : SFam h n ζ), 3 ≤ n → IsUnit ζ → IsUnit (n : o) → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (A : Over (Sp V)) [GrpObj A] [IsCommMonObj A] (t₁ t₂ : Sp V ⟶ F'.X) (a₁ a₂ : A.left ⟶ F'.univ.A.left) (aa₁ aa₂ : (G2 A).left ⟶ (G2 F'.univ.A).left), IsGrpPullback A F'.univ.A t₁ a₁ → IsGrpPullback A F'.univ.A t₂ a₂ → IsSquare a₁ aa₁ → IsSquare a₂ aa₂ → LBIso (F'.univ.P.pull aa₁) (F'.univ.P.pull aa₂) → t₁ ≫ F'.s = t₂ ≫ F'.s → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F], (∀ l, ∃ x : TF (R := V) F ⟶ A, x.left ≫ a₁ = (TF (R := V) F).hom ≫ t₁ ≫ (F'.univ.lev l).left ∧ x.left ≫ a₂ = (TF (R := V) F).hom ≫ t₂ ≫ (F'.univ.lev l).left) → t₁ = t₂ ∧ a₁ = a₂ := by
  first | exact @GlobalTheory.LowSame.eq_of_presentations | exact GlobalTheory.LowSame.eq_of_presentations | (intros; apply GlobalTheory.LowSame.eq_of_presentations <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFibrePowerPointEqOfMatchingLowerData

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

theorem GlobalTheory.TInj.low_eq_of_match : ∀ {o : Type} [CommRing o] {ζ : o} {n : ℕ} (L : LowBase ζ n), 3 ≤ n → IsUnit ζ → IsUnit (n : o) → ∀ {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin L.T.r → ℤ)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D₁ D₂ : DegPre V) (ω₁ : L.W →+* V) (s₁ : I → V) (e₁ : D₁.X ≃+ (Fin L.T.r → ℤ)) (β₁ : D₁.P.A.left ⟶ L.T.B.left) (ββ₁ : (G2 D₁.P.A).left ⟶ (G2 L.T.B).left) (w₁ : LB.Iso (abelian₂ D₁.P.A D₁.P.L) ((abelian₂ L.T.B L.T.M.L).pull ββ₁)) (ω₂ : L.W →+* V) (s₂ : I → V) (e₂ : D₂.X ≃+ (Fin L.T.r → ℤ)) (β₂ : D₂.P.A.left ⟶ L.T.B.left) (ββ₂ : (G2 D₂.P.A).left ⟶ (G2 L.T.B).left) (w₂ : LB.Iso (abelian₂ D₂.P.A D₂.P.L) ((abelian₂ L.T.B L.T.M.L).pull ββ₂)) (b : D₁.P.A ⟶ D₂.P.A) (φ : D₁.X ≃+ D₂.X) (F : Type) [Field F] [Algebra (FractionRing V) F], D₁.TauBimult → D₂.TauBimult → From L.T ω₁ s₁ ε n D₁ e₁ β₁ ββ₁ w₁ → From L.T ω₂ s₂ ε n D₂ e₂ β₂ ββ₂ w₂ → ω₁.comp L.T.b = ω₂.comp L.T.b → Match D₁ D₂ b φ F → (∀ y, e₂ (φ y) = e₁ y) → (∀ a : Fin L.T.r → ℤ, ∃ (p₁ : QkPt D₁ F n) (p₂ : QkPt D₂ F n), p₁.y = e₁.symm a ∧ TautPt L.T ω₁ s₁ ε n D₁ e₁ β₁ ββ₁ w₁ F a p₁.g ∧ p₂.y = e₂.symm a ∧ TautPt L.T ω₂ s₂ ε n D₂ e₂ β₂ ββ₂ w₂ F a p₂.g ∧ QImg b φ p₁ p₂) → (∀ l : Fin L.h ⊕ Fin L.h → ℤ, ∃ (p₁ : QkPt D₁ F n) (p₂ : QkPt D₂ F n), p₁.y = 0 ∧ p₁.g.b.left ≫ β₁ ≫ L.β = (TF (R := V) F).hom ≫ spMap ω₁ ≫ L.u ≫ (GlobalTheory.LowChart.powA L.F L.T.r).hom ≫ (L.F.univ.lev l).left ∧ p₂.y = 0 ∧ p₂.g.b.left ≫ β₂ ≫ L.β = (TF (R := V) F).hom ≫ spMap ω₂ ≫ L.u ≫ (GlobalTheory.LowChart.powA L.F L.T.r).hom ≫ (L.F.univ.lev l).left ∧ QImg b φ p₁ p₂) → spMap ω₁ ≫ L.u = spMap ω₂ ≫ L.u ∧ (ω₁ = ω₂ → b.left ≫ β₂ = β₁) := by
  intro o _ ζ n L hn hζ hnu I _ ε V _ _ _ D₁ D₂ ω₁ s₁ e₁ β₁ ββ₁ w₁ ω₂ s₂ e₂ β₂ ββ₂ w₂ b φ F _ _ hτ₁ hτ₂ hF₁ hF₂ hω hM he
    hco hlev
  have himg : ∀ (p₁ : QkPt D₁ F n) (p₂ : QkPt D₂ F n), QImg b φ p₁ p₂ → p₂.y = φ p₁.y →
      p₂.g.b.left = p₁.g.b.left ≫ b.left := by
    rintro p₁ p₂ ⟨p', hp'y, hact, heqv⟩ hy
    have hg : p'.g = p₂.g := GlobalTheory.T.torsionPoint_torusPart_eq_of_equiv_same_lattice V D₂ hτ₂ F n (by omega) p' p₂ (hp'y.trans hy.symm) heqv
    rw [← hg, hact.1, Over.comp_left]
  haveI := hM.2.1
  haveI : IsMonHom (asIso b).hom := hM.1
  set t₁ : Sp V ⟶ L.F.X := spMap ω₁ ≫ L.u ≫ (GlobalTheory.LowChart.powA L.F L.T.r).hom with ht₁
  set t₂ : Sp V ⟶ L.F.X := spMap ω₂ ≫ L.u ≫ (GlobalTheory.LowChart.powA L.F L.T.r).hom with ht₂
  let a₁ : D₁.P.A.left ⟶ L.F.univ.A.left := β₁ ≫ L.β
  let a₂ : D₁.P.A.left ⟶ L.F.univ.A.left := b.left ≫ β₂ ≫ L.β
  let bb : (G2 D₁.P.A).left ⟶ (G2 D₂.P.A).left :=
    (lift (fst D₁.P.A D₁.P.A ≫ b) (snd D₁.P.A D₁.P.A ≫ b) : G2 D₁.P.A ⟶ G2 D₂.P.A).left
  let aa₁ : (G2 D₁.P.A).left ⟶ (G2 L.F.univ.A).left := ββ₁ ≫ L.β₂
  let aa₂ : (G2 D₁.P.A).left ⟶ (G2 L.F.univ.A).left := bb ≫ ββ₂ ≫ L.β₂
  have hpb₁ : IsGrpPullback D₁.P.A L.F.univ.A t₁ a₁ := IsGrpPullback.comp hF₁.1 L.cart
  have hpb₂ : IsGrpPullback D₁.P.A L.F.univ.A t₂ a₂ :=
    (IsGrpPullback.comp (ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_of_iso (asIso b))
      (IsGrpPullback.comp hF₂.1 L.cart)).congr (Category.id_comp _) rfl
  have hbsq : IsSquare b.left bb :=
    ⟨by rw [← Over.comp_left, lift_fst, Over.comp_left], by rw [← Over.comp_left, lift_snd, Over.comp_left]⟩
  have hsq₁ : IsSquare a₁ aa₁ := GlobalTheory.PolDeg.isSquare_comp hF₁.2.1 L.sq
  have hsq₂ : IsSquare a₂ aa₂ := GlobalTheory.PolDeg.isSquare_comp hbsq (GlobalTheory.PolDeg.isSquare_comp hF₂.2.1 L.sq)
  have hLam : ∀ D : DegPre V, (abelian₂ D.P.A D.P.L).IsLB := fun D => LB.isLB_linComb D.P.isLB _ _
  have hLamT : (abelian₂ L.T.B L.T.M.L).IsLB := LB.isLB_linComb L.T.M.isLB _ _
  have hU := L.F.univ.isLB
  have hA₁ : LBIso (abelian₂ D₁.P.A D₁.P.L) (L.F.univ.P.pull aa₁) :=
    LBIso.trans (hLam D₁) (pull_isLB hLamT ββ₁) (pull_isLB hU _) ⟨w₁, hF₁.2.2.1⟩
      (GlobalTheory.PolDeg.lbIso_pull_comp L.lb ββ₁ rfl)
  have hA₂' : LBIso (abelian₂ D₂.P.A D₂.P.L) (L.F.univ.P.pull (ββ₂ ≫ L.β₂)) :=
    LBIso.trans (hLam D₂) (pull_isLB hLamT ββ₂) (pull_isLB hU _) ⟨w₂, hF₂.2.2.1⟩
      (GlobalTheory.PolDeg.lbIso_pull_comp L.lb ββ₂ rfl)
  have hA₂ : LBIso (abelian₂ D₁.P.A D₁.P.L) (L.F.univ.P.pull aa₂) :=
    LBIso.trans (hLam D₁) (pull_isLB (hLam D₂) bb) (pull_isLB hU _) hM.2.2.1
      (GlobalTheory.PolDeg.lbIso_pull_comp hA₂' bb rfl)
  have hP : LBIso (L.F.univ.P.pull aa₁) (L.F.univ.P.pull aa₂) :=
    LBIso.trans (pull_isLB hU _) (hLam D₁) (pull_isLB hU _) hA₁.symm hA₂
  have hs : t₁ ≫ L.F.s = t₂ ≫ L.F.s := by
    have hb : spMap ω₁ ≫ spMap L.T.b = spMap ω₂ ≫ spMap L.T.b := by
      simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hω]
    have e : ∀ ω : L.W →+* V, (spMap ω ≫ L.u ≫ (GlobalTheory.LowChart.powA L.F L.T.r).hom) ≫ L.F.s = spMap ω ≫ spMap L.T.b := by
      intro ω
      rw [Category.assoc, Category.assoc, ← L.u_base]
      rfl
    rw [ht₁, ht₂, e, e, hb]
  have hlev' : ∀ l, ∃ x : TF (R := V) F ⟶ D₁.P.A,
      x.left ≫ a₁ = (TF (R := V) F).hom ≫ t₁ ≫ (L.F.univ.lev l).left ∧
      x.left ≫ a₂ = (TF (R := V) F).hom ≫ t₂ ≫ (L.F.univ.lev l).left := by
    intro l
    obtain ⟨p₁, p₂, hy₁, hb₁, hy₂, hb₂, hQ⟩ := hlev l
    have h21 := himg p₁ p₂ hQ (by rw [hy₂, hy₁, map_zero])
    refine ⟨p₁.g.b, ?_, ?_⟩
    · simpa only [a₁, ht₁, Category.assoc] using hb₁
    · have : p₁.g.b.left ≫ a₂ = p₂.g.b.left ≫ β₂ ≫ L.β := by
        simp only [a₂, h21, Category.assoc]
      rw [this, hb₂]
      simp only [ht₂, Category.assoc]
  obtain ⟨ht, ha⟩ := GlobalTheory.T.eq_of_presentations_same_polarisation_level L.F hn hζ hnu V D₁.P.A t₁ t₂ a₁ a₂ aa₁ aa₂ hpb₁ hpb₂ hsq₁ hsq₂ hP hs F hlev'
  have hcoordEq : ∀ i, (spMap ω₁ ≫ L.u) ≫ (GlobalTheory.LowChart.coord L.F i).left =
      (spMap ω₂ ≫ L.u) ≫ (GlobalTheory.LowChart.coord L.F i).left := by
    intro i
    obtain ⟨p₁, p₂, hy₁, hT₁, hy₂, hT₂, hQ⟩ := hco (Pi.single i 1)
    have hφ : p₂.y = φ p₁.y := by
      rw [hy₂, hy₁]
      apply e₂.injective
      rw [he, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
    have h21 := himg p₁ p₂ hQ hφ
    have c1 : (TF (R := V) F).hom ≫ (spMap ω₁ ≫ L.u) ≫ (GlobalTheory.LowChart.coord L.F i).left = p₁.g.b.left ≫ a₁ := by
      simp only [a₁, Category.assoc, ← L.coord i]
      rw [← Category.assoc p₁.g.b.left, hT₁.1]
      simp only [Category.assoc]
    have c2 : (TF (R := V) F).hom ≫ (spMap ω₂ ≫ L.u) ≫ (GlobalTheory.LowChart.coord L.F i).left = p₁.g.b.left ≫ a₂ := by
      simp only [a₂, Category.assoc, ← L.coord i]
      rw [← Category.assoc p₁.g.b.left, ← h21, ← Category.assoc p₂.g.b.left, hT₂.1]
      simp only [Category.assoc]
    have hgen : (TF (R := V) F).hom ≫ (spMap ω₁ ≫ L.u) ≫ (GlobalTheory.LowChart.coord L.F i).left =
        (TF (R := V) F).hom ≫ (spMap ω₂ ≫ L.u) ≫ (GlobalTheory.LowChart.coord L.F i).left := by
      rw [c1, c2, ha]
    have : IsProper L.F.univ.A.hom := L.F.univ.ab.proper
    haveI : IsDominant (TF (R := V) F).hom := ReciprocityTheory.ChartRestriction.G.DVR.GC.isDominant_jFR (V := V) F
    refine ext_of_isDominant_of_isSeparated L.F.univ.A.hom ?_ (TF (R := V) F).hom hgen
    simp only [Category.assoc, Over.w]
    exact ht
  refine ⟨GlobalTheory.LowChart.hom_ext _ _ (by simpa only [Category.assoc] using ht) hcoordEq, ?_⟩
  rintro rfl
  apply L.cart.1.hom_ext
  · simpa only [a₁, a₂, Category.assoc] using ha.symm
  · rw [Category.assoc, hF₂.1.1.w, ← Category.assoc, Over.w b, hF₁.1.1.w]
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFibrePowerPointEqOfMatchingLowerDataStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

theorem _root_.GlobalTheory.T.siegelFibrePower_point_eq_of_matching_lower_data : ∀ {o : Type} [CommRing o] {ζ : o} {n : ℕ} (L : LowBase ζ n), 3 ≤ n → IsUnit ζ → IsUnit (n : o) → ∀ {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin L.T.r → ℤ)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D₁ D₂ : DegPre V) (ω₁ : L.W →+* V) (s₁ : I → V) (e₁ : D₁.X ≃+ (Fin L.T.r → ℤ)) (β₁ : D₁.P.A.left ⟶ L.T.B.left) (ββ₁ : (G2 D₁.P.A).left ⟶ (G2 L.T.B).left) (w₁ : LB.Iso (abelian₂ D₁.P.A D₁.P.L) ((abelian₂ L.T.B L.T.M.L).pull ββ₁)) (ω₂ : L.W →+* V) (s₂ : I → V) (e₂ : D₂.X ≃+ (Fin L.T.r → ℤ)) (β₂ : D₂.P.A.left ⟶ L.T.B.left) (ββ₂ : (G2 D₂.P.A).left ⟶ (G2 L.T.B).left) (w₂ : LB.Iso (abelian₂ D₂.P.A D₂.P.L) ((abelian₂ L.T.B L.T.M.L).pull ββ₂)) (b : D₁.P.A ⟶ D₂.P.A) (φ : D₁.X ≃+ D₂.X) (F : Type) [Field F] [Algebra (FractionRing V) F], D₁.TauBimult → D₂.TauBimult → From L.T ω₁ s₁ ε n D₁ e₁ β₁ ββ₁ w₁ → From L.T ω₂ s₂ ε n D₂ e₂ β₂ ββ₂ w₂ → ω₁.comp L.T.b = ω₂.comp L.T.b → Match D₁ D₂ b φ F → (∀ y, e₂ (φ y) = e₁ y) → (∀ a : Fin L.T.r → ℤ, ∃ (p₁ : QkPt D₁ F n) (p₂ : QkPt D₂ F n), p₁.y = e₁.symm a ∧ TautPt L.T ω₁ s₁ ε n D₁ e₁ β₁ ββ₁ w₁ F a p₁.g ∧ p₂.y = e₂.symm a ∧ TautPt L.T ω₂ s₂ ε n D₂ e₂ β₂ ββ₂ w₂ F a p₂.g ∧ QImg b φ p₁ p₂) → (∀ l : Fin L.h ⊕ Fin L.h → ℤ, ∃ (p₁ : QkPt D₁ F n) (p₂ : QkPt D₂ F n), p₁.y = 0 ∧ p₁.g.b.left ≫ β₁ ≫ L.β = (TF (R := V) F).hom ≫ spMap ω₁ ≫ L.u ≫ (GlobalTheory.LowChart.powA L.F L.T.r).hom ≫ (L.F.univ.lev l).left ∧ p₂.y = 0 ∧ p₂.g.b.left ≫ β₂ ≫ L.β = (TF (R := V) F).hom ≫ spMap ω₂ ≫ L.u ≫ (GlobalTheory.LowChart.powA L.F L.T.r).hom ≫ (L.F.univ.lev l).left ∧ QImg b φ p₁ p₂) → spMap ω₁ ≫ L.u = spMap ω₂ ≫ L.u ∧ (ω₁ = ω₂ → b.left ≫ β₂ = β₁) := by
  first | exact @GlobalTheory.TInj.low_eq_of_match | exact GlobalTheory.TInj.low_eq_of_match | (intros; apply GlobalTheory.TInj.low_eq_of_match <;> assumption)
end
end
