module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenSmoothOfRelativeDimensionOfGeneri
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFrameChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClsDivPullEqVPull
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMinAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationVectorBundleAbelianPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitPullbackSemiAbelianModelIdentificationStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeBundlePullbackGenOfFrameIsGen

section

@[expose] public section

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.HodgeFrameGen
open GlobalTheory.QCoh (pullbackSections)

namespace GlobalTheory.HodgeFrameGen

variable {S' T : Scheme.{0}} {G : Over S'} [GrpObj G] {H : Over T} [GrpObj H] {x : T ⟶ S'}
  {ψ : H.left ⟶ G.left} [QuasiSeparated G.hom] {g : ℕ}

theorem pulled_back_lineBundle_transition_unit_eq_restriction {X Y : Scheme.{0}} (L : LB X) (f : Y ⟶ X) (j j' : PUnit.{1} → L.ι) :
    (L.pull f).g j j' = res (le_inf (inf_le_left.trans (LB.wchart_le L (fun _ => f) j PUnit.unit))
      (inf_le_right.trans (LB.wchart_le L (fun _ => f) j' PUnit.unit)))
      (pullU f _ (L.g (j PUnit.unit) (j' PUnit.unit))) := by
  have e : ∀ u : Γ(Y, L.wchart (fun _ => f) j ⊓ L.wchart (fun _ => f) j')ˣ, (∏ _k : PUnit.{1}, u ^ (1 : ℤ)) = u :=
    fun u => by simp
  exact e _

theorem pull_g_eq (h : IsGrpPullback H G x ψ) (j j' : ((hodge G g).pull x).ι) :
    ((hodge G g).pull x).g j j' =
      (isFrame_chart h j).detUnit (isFrame_chart h j') inf_le_left inf_le_right := by
  have frame_pb {X Y : Scheme.{0}} {I : Type} [Fintype I] (f : Y ⟶ X)
      {F : X.Modules} [F.IsQuasicoherent] {U : X.Opens} {e : I → Γ(F, U)} (he : IsFrame e)
      {V : Y.Opens} (h : V ≤ f ⁻¹ᵁ U) : IsFrame fun i => pullbackSections f F h (e i) := by
    have k := (he.pullback f).res h
    exact (funext fun l => QCoh.res_pullbackSections f F le_rfl h (e l)) ▸ k
  have e₁ := IsFrame.detUnit_map_iso
    (frame_pb x (j PUnit.unit).isFrame (LB.wchart_le (hodge G g) (fun _ => x) j PUnit.unit))
    (frame_pb x (j' PUnit.unit).isFrame (LB.wchart_le (hodge G g) (fun _ => x) j' PUnit.unit))
    (omegaBase h) (inf_le_left : LB.wchart (hodge G g) (fun _ => x) j ⊓ LB.wchart (hodge G g) (fun _ => x) j' ≤ _)
    inf_le_right
  refine Eq.trans ?_ e₁.symm
  have hT : LB.wchart (hodge G g) (fun _ => x) j ⊓ LB.wchart (hodge G g) (fun _ => x) j' ≤
      x ⁻¹ᵁ ((j PUnit.unit).U ⊓ (j' PUnit.unit).U) :=
    le_inf (inf_le_left.trans (LB.wchart_le (hodge G g) (fun _ => x) j PUnit.unit))
      (inf_le_right.trans (LB.wchart_le (hodge G g) (fun _ => x) j' PUnit.unit))
  refine Eq.trans ?_ (GlobalTheory.Vert.DivPull.detUnit_congr _ _ ((j PUnit.unit).isFrame.pullback x)
    ((j' PUnit.unit).isFrame.pullback x) _ _ (hT.trans (x.preimage_mono inf_le_left))
    (hT.trans (x.preimage_mono inf_le_right))
    (fun i => (QCoh.res_pullbackSections _ _ _ _ _).trans (QCoh.res_pullbackSections _ _ _ _ _).symm)
    (fun i => (QCoh.res_pullbackSections _ _ _ _ _).trans (QCoh.res_pullbackSections _ _ _ _ _).symm)).symm
  refine Units.ext ?_
  refine (congrArg Units.val (pulled_back_lineBundle_transition_unit_eq_restriction (hodge G g) x j j')).trans (Eq.trans ?_
    (IsFrame.val_detUnit_pullback (j PUnit.unit).isFrame (j' PUnit.unit).isFrame x inf_le_left inf_le_right hT).symm)
  rfl

theorem gen_isGen : ∀ {S' T : Scheme.{0}} {G : Over S'} [GrpObj G] {H : Over T} [GrpObj H] {x : T ⟶ S'}
    {ψ : H.left ⟶ G.left} [QuasiSeparated G.hom] {g : ℕ} (h : IsGrpPullback H G x ψ)
    {a : Fin g → Γ(omega H, ⊤)} (ha : IsFrame a), (gen h ha).IsGen := by
  intro S' T G _ H _ x ψ _ g h a ha j j'
  refine (IsFrame.res_detUnit _ _ _ _ _).trans ?_
  refine Eq.trans ?_ (congrArg₂ (· * ·) (pull_g_eq h j j').symm (IsFrame.res_detUnit _ _ _ _ _).symm)
  exact (IsFrame.detUnit_mul _ _ _ _ _ _).symm

end GlobalTheory.HodgeFrameGen
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeBundlePullbackGenOfFrameIsGenStatement

section

@[expose] public section

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.HodgeFrameGen
open GlobalTheory.QCoh (pullbackSections)


theorem _root_.GlobalTheory.T.hodgeBundlePullbackGenOfFrame_isGen : ∀ {S' T : Scheme.{0}} {G : Over S'} [GrpObj G] {H : Over T} [GrpObj H] {x : T ⟶ S'}
    {ψ : H.left ⟶ G.left} [QuasiSeparated G.hom] {g : ℕ} (h : IsGrpPullback H G x ψ)
    {a : Fin g → Γ(omega H, ⊤)} (ha : IsFrame a), (gen h ha).IsGen := by
  first | exact @GlobalTheory.HodgeFrameGen.gen_isGen | exact GlobalTheory.HodgeFrameGen.gen_isGen | (intros; apply GlobalTheory.HodgeFrameGen.gen_isGen <;> assumption)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeFrameGeneratorValuePullback

section

@[expose] public section

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.HodgeFrameGen
open GlobalTheory.QCoh (pullbackSections)

namespace GlobalTheory.HodgeFrameGen

theorem gm_eq_of_appLE {T Z : Scheme.{0}} (r : Z ⟶ T) (z : Z) {U : T.Opens} {W : Z.Opens} (hW : W ≤ r ⁻¹ᵁ U)
    (hz : z ∈ W) (u : Γ(T, U)ˣ) (v : Γ(Z, W)ˣ) (e : v.val = (r.appLE U W hW).hom u.val) :
    gm r z U u = gm (𝟙 Z) z W v := by
  refine Units.ext ?_
  rw [gm_val r z U (hW hz), gm_val (𝟙 Z) z W hz, e]
  exact (TopCat.Presheaf.germ_res_apply Z.presheaf (homOfLE hW) z hz _).symm

theorem val_gen_pull : ∀ {S' T Z : Scheme.{0}} {G : Over S'} [GrpObj G] {H : Over T} [GrpObj H] {x : T ⟶ S'}
    {ψ : H.left ⟶ G.left} [QuasiSeparated G.hom] {g : ℕ} (h : IsGrpPullback H G x ψ)
    {a : Fin g → Γ(omega H, ⊤)} (ha : IsFrame a) (r : Z ⟶ T) {B : Over Z} [GrpObj B] {ρ : B.left ⟶ H.left}
    (q : IsGrpPullback B H r ρ) (x' : Z ⟶ S') (ψ' : B.left ⟶ G.left) (h' : IsGrpPullback B G x' ψ'),
    r ≫ x = x' → ρ ≫ ψ = ψ' → ∀ {b : Fin g → Γ(omega B, ⊤)} (hb : IsFrame b),
    (∀ i, b i = (omegaBase q).app ⊤ (pullbackSections r _ le_top (a i))) → ∀ (z : Z)
    (J : (Z ⟶ S') → (hodge G g).ι), Good (hodge G g) z J →
    val (L := hodge G g) (φ := fun _ : PUnit => x) (ε := fun _ => 1) (gen h ha) r z J =
      val (L := hodge G g) (φ := fun _ : PUnit => x') (ε := fun _ => 1) (gen h' hb) (𝟙 Z) z J := by
  intro S' T Z G _ H _ x ψ _ g h a ha r B _ ρ q x' ψ' h' e e' b hb hab z J hJ
  have : QuasiSeparated H.hom := MorphismProperty.of_isPullback h.1 ‹_›
  rw [val_of (L := hodge G g) (φ := fun _ : PUnit => x) (ε := fun _ => 1) (gen h ha) r z J (fun _ => J x')
      (fun _ => by rw [e]),
    val_of (L := hodge G g) (φ := fun _ : PUnit => x') (ε := fun _ => 1) (gen h' hb) (𝟙 Z) z J (fun _ => J x')
      (fun _ => by rw [Category.id_comp])]
  have hW : LB.wchart (hodge G g) (fun _ : PUnit => x') (fun _ => J x') ≤
      r ⁻¹ᵁ LB.wchart (hodge G g) (fun _ : PUnit => x) (fun _ => J x') := fun y hy =>
    Set.mem_iInter.2 fun k => by
      have := Set.mem_iInter.1 hy k
      rw [← e] at this ⊢
      exact this
  have hz : z ∈ LB.wchart (hodge G g) (fun _ : PUnit => x') (fun _ => J x') := Set.mem_iInter.2 fun _ => hJ x'
  have k {U : T.Opens} {V W : Z.Opens} (hV : V ≤ r ⁻¹ᵁ U) (h₁ : W ≤ V) (s : Γ(omega H, U)) :
      GlobalTheory.Twist.resM _ h₁ ((omegaBase q).app V (pullbackSections r _ hV s)) =
        (omegaBase q).app W (pullbackSections r _ (h₁.trans hV) s) := by
    rw [← GlobalTheory.QCoh.res_pullbackSections r _ hV h₁ s]
    exact congr($((omegaBase q).mapPresheaf.naturality (homOfLE h₁).op) (pullbackSections r _ hV s)).symm
  refine gm_eq_of_appLE r z hW hz _ _ ?_
  have hc := isFrame_chart h (fun _ => J x')
  refine Eq.trans ?_ (hc.val_detUnit_pullback ha r le_rfl le_top hW)
  refine congrArg Units.val ?_
  refine Eq.trans ?_ (IsFrame.detUnit_map_iso _ _ (omegaBase q) _ _)
  refine GlobalTheory.Vert.DivPull.detUnit_congr _ _ _ _ _ _ _ _ (fun i => ?_) (fun i => ?_)
  · refine Eq.trans (GlobalTheory.Twist.resM_self _ _) (Eq.trans ?_ (k _ _ _).symm)
    exact (GlobalTheory.BadPt.Fibre.omegaBase_comp h q h' e e' _ _ _ _).symm
  · rw [hab]
    exact (k _ _ _).trans (k _ _ _).symm

end GlobalTheory.HodgeFrameGen
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeFrameGeneratorValuePullbackStatement

section

@[expose] public section

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.HodgeFrameGen
open GlobalTheory.QCoh (pullbackSections)


theorem _root_.GlobalTheory.T.hodge_frame_generator_value_pullback : ∀ {S' T Z : Scheme.{0}} {G : Over S'} [GrpObj G] {H : Over T} [GrpObj H] {x : T ⟶ S'}
    {ψ : H.left ⟶ G.left} [QuasiSeparated G.hom] {g : ℕ} (h : IsGrpPullback H G x ψ)
    {a : Fin g → Γ(omega H, ⊤)} (ha : IsFrame a) (r : Z ⟶ T) {B : Over Z} [GrpObj B] {ρ : B.left ⟶ H.left}
    (q : IsGrpPullback B H r ρ) (x' : Z ⟶ S') (ψ' : B.left ⟶ G.left) (h' : IsGrpPullback B G x' ψ'),
    r ≫ x = x' → ρ ≫ ψ = ψ' → ∀ {b : Fin g → Γ(omega B, ⊤)} (hb : IsFrame b),
    (∀ i, b i = (omegaBase q).app ⊤ (pullbackSections r _ le_top (a i))) → ∀ (z : Z)
    (J : (Z ⟶ S') → (hodge G g).ι), Good (hodge G g) z J →
    val (L := hodge G g) (φ := fun _ : PUnit => x) (ε := fun _ => 1) (gen h ha) r z J =
      val (L := hodge G g) (φ := fun _ : PUnit => x') (ε := fun _ => 1) (gen h' hb) (𝟙 Z) z J := by
  first | exact @GlobalTheory.HodgeFrameGen.val_gen_pull | exact GlobalTheory.HodgeFrameGen.val_gen_pull | (intros; apply GlobalTheory.HodgeFrameGen.val_gen_pull <;> assumption)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralHodgeBundleGenerator

section

@[expose] public section

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.HodgeFrameGen
open GlobalTheory.QCoh (pullbackSections)

namespace GlobalTheory.HodgeFrameGen

theorem exists_isFrame_top_of_isLocalRing (R : Type) [CommRing R] [IsLocalRing R] (F : (Sp R).Modules) {r : ℕ}
    (h : IsVB F r) : ∃ e : Fin r → Γ(F, ⊤), IsFrame e := by
  obtain ⟨U, e, hx, he⟩ := h (IsLocalRing.closedPoint R)
  have hU : U = ⊤ := by
    refine top_le_iff.1 fun p _ => ?_
    exact (IsLocalRing.specializes_closedPoint p).mem_open U.isOpen hx
  subst hU
  exact ⟨e, he⟩

theorem spMap_jK {R W : Type} [CommRing R] [IsDomain R] [CommRing W] [IsDomain W] (φ : R →+* W)
    (gam : FractionRing R →+* FractionRing W) (hgam : ∀ r, gam (algebraMap R _ r) = algebraMap W _ (φ r)) :
    spMap gam ≫ jK R = jK W ≫ spMap φ := by
  have e : gam.comp (algebraMap R (FractionRing R)) = (algebraMap W (FractionRing W)).comp φ :=
    RingHom.ext hgam
  simp only [spMap, jK, ← Spec.map_comp, ← CommRingCat.ofHom_comp, e]

theorem relDim {S' : Scheme.{0}} {g : ℕ} {G : Over S'} [GrpObj G] (hGg : SmoothOfRelativeDimension g G.hom)
    {R : Type} [CommRing R] [IsDomain R] {G₁ : Over (Sp R)} [GrpObj G₁] (hG₁ : IsSemiAbelian G₁)
    {y : Sp (FractionRing R) ⟶ S'} {α : pullback G₁.hom (jK R) ⟶ G.left}
    (hα : IsGrpPullback ((Over.pullback (jK R)).obj G₁) G y α) : SmoothOfRelativeDimension g G₁.hom := by
  have := hG₁.smooth
  have h₁ : SmoothOfRelativeDimension g ((Over.pullback (jK R)).obj G₁).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback hα.1 hGg
  exact GlobalTheory.SmoothRelDim.smoothOfRelativeDimension_of_generic R G₁ (FractionRing R)
    (algebraMap R (FractionRing R)) (IsFractionRing.injective R (FractionRing R)) g h₁

theorem exists_integral_hodgeGen : ∀ (S' : Scheme.{0}) (g : ℕ) (G : Over S') [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → SmoothOfRelativeDimension g G.hom → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (y : Sp (FractionRing R) ⟶ S') (α : pullback G₁.hom (jK R) ⟶ G.left), IsGrpPullback ((Over.pullback (jK R)).obj G₁) G y α → ∃ e₀ : LB.Gen ((hodge G g).pull y), e₀.IsGen ∧ ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W) (gam : FractionRing R →+* FractionRing W), (∀ r, gam (algebraMap R _ r) = algebraMap W _ (φ r)) → ∀ χ' : Sp W ⟶ S', spMap gam ≫ y = jK W ≫ χ' → ∃ e₀' : LB.Gen ((hodge G g).pull χ'), e₀'.IsGen ∧ ∀ (z : Sp (FractionRing W)) (J : (Sp (FractionRing W) ⟶ S') → (hodge G g).ι), Good (hodge G g) z J → val (L := hodge G g) (φ := fun _ : PUnit => y) (ε := fun _ => 1) e₀ (spMap gam) z J = val (L := hodge G g) (φ := fun _ : PUnit => χ') (ε := fun _ => 1) e₀' (jK W) z J := by
  intro S' g G _ _ hG hGg R _ _ _ _ _ G₁ _ _ hG₁ y α hα
  haveI := hG; haveI := hG₁
  haveI : SmoothOfRelativeDimension g G₁.hom := relDim hGg hG₁ hα
  obtain ⟨ε, hε⟩ := exists_isFrame_top_of_isLocalRing R (omega G₁) (isVB_omega G₁ g)
  have p₁ := isGrpPullback_pullback G₁ (jK R)
  have ha : IsFrame fun i => (omegaBase p₁).app ⊤ (pullbackSections (jK R) _ le_top (ε i)) :=
    (GlobalTheory.BadPt.Fibre.frame_pb (jK R) hε le_top).map_iso _
  refine ⟨gen hα ha, GlobalTheory.T.hodgeBundlePullbackGenOfFrame_isGen hα ha, ?_⟩
  intro W _ _ _ hW φ gam hgam χ' hχ
  haveI : IsDiscreteValuationRing W := hW.1
  obtain ⟨ρ', ψ', hρ', hψ', e₁, e₂⟩ := GlobalTheory.T.traitPullback_semiAbelianModel_identification hG hG₁ hα φ gam hgam χ' hχ
  have pW := isGrpPullback_pullback G₁ (spMap φ)
  have ha' : IsFrame fun i => (omegaBase pW).app ⊤ (pullbackSections (spMap φ) _ le_top (ε i)) :=
    (GlobalTheory.BadPt.Fibre.frame_pb (spMap φ) hε le_top).map_iso _
  refine ⟨gen hψ' ha', GlobalTheory.T.hodgeBundlePullbackGenOfFrame_isGen hψ' ha', fun z J hJ => ?_⟩
  have q := isGrpPullback_pullback ((Over.pullback (jK R)).obj G₁) (spMap gam)
  have hA := q.comp hα
  have hq₁ := q.comp p₁
  have hb : IsFrame fun i => (omegaBase hq₁).app ⊤ (pullbackSections (spMap gam ≫ jK R) _ le_top (ε i)) :=
    (GlobalTheory.BadPt.Fibre.frame_pb _ hε le_top).map_iso _
  refine (GlobalTheory.T.hodge_frame_generator_value_pullback hα ha (spMap gam) q _ _ hA rfl rfl hb (fun i => ?_) z J hJ).trans
    (GlobalTheory.T.hodge_frame_generator_value_pullback hψ' ha' (jK W) hρ' _ _ hA hχ.symm e₁ hb (fun i => ?_) z J hJ).symm
  · exact (GlobalTheory.BadPt.Fibre.omegaBase_comp p₁ q hq₁ rfl rfl le_top le_top le_top (ε i)).symm
  · exact (GlobalTheory.BadPt.Fibre.omegaBase_comp pW hρ' hq₁ (spMap_jK φ gam hgam).symm e₂ le_top le_top le_top (ε i)).symm

end GlobalTheory.HodgeFrameGen
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralHodgeBundleGeneratorStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_integral_hodgeBundle_generator : ∀ (S' : Scheme.{0}) (g : ℕ) (G : Over S') [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → SmoothOfRelativeDimension g G.hom → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (y : Sp (FractionRing R) ⟶ S') (α : pullback G₁.hom (jK R) ⟶ G.left), IsGrpPullback ((Over.pullback (jK R)).obj G₁) G y α → ∃ e₀ : LB.Gen ((hodge G g).pull y), e₀.IsGen ∧ ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W) (gam : FractionRing R →+* FractionRing W), (∀ r, gam (algebraMap R _ r) = algebraMap W _ (φ r)) → ∀ χ' : Sp W ⟶ S', spMap gam ≫ y = jK W ≫ χ' → ∃ e₀' : LB.Gen ((hodge G g).pull χ'), e₀'.IsGen ∧ ∀ (z : Sp (FractionRing W)) (J : (Sp (FractionRing W) ⟶ S') → (hodge G g).ι), Good (hodge G g) z J → val (L := hodge G g) (φ := fun _ : PUnit => y) (ε := fun _ => 1) e₀ (spMap gam) z J = val (L := hodge G g) (φ := fun _ : PUnit => χ') (ε := fun _ => 1) e₀' (jK W) z J := by
  first | exact @GlobalTheory.HodgeFrameGen.exists_integral_hodgeGen | exact GlobalTheory.HodgeFrameGen.exists_integral_hodgeGen | (intros; apply GlobalTheory.HodgeFrameGen.exists_integral_hodgeGen <;> assumption)
end
end
