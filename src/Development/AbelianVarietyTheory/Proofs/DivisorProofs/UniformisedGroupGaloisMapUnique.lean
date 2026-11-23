module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GalMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecEqZeroAndHomEqOfThickenings
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegUnif
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValTorusPointAndTranslate
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.TorusInj
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicColimitOfFactor
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsoUniqueOfRig
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.GtPtsTor

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ReciprocityTheory.ChartRestriction.G.Semi.TorusPts

open TorusInj

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]

theorem charUnit_appTop {Z : Scheme.{0}} (τ : Z ⟶ (splitTorus S X).left) (χ : X) :
    τ.appTop.hom (charUnit S X χ).val =
      (τ ≫ tFst X).appTop.hom ((Scheme.ΓSpecIso (torusRing ZU X)).inv.hom (AddMonoidAlgebra.single χ 1)) := by
  rw [charUnit_val, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  congr 2
  first
  | (rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; simp only [Scheme.Hom.preimage_top])
  | (simp [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, Scheme.Hom.preimage_top])
  | (ext1; simp [Scheme.Hom.appLE, Scheme.Hom.appTop])

theorem ringHom_ext_ZU {A : Type} [CommRing A] {f g : AddMonoidAlgebra ZU.{0} X →+* A}
    (h : ∀ χ, f (AddMonoidAlgebra.single χ 1) = g (AddMonoidAlgebra.single χ 1)) : f = g := by
  refine AddMonoidAlgebra.ringHom_ext (fun b => ?_) h
  have e : (AddMonoidAlgebra.single 0 b : AddMonoidAlgebra ZU.{0} X) = ((b.down : ℤ) : AddMonoidAlgebra ZU.{0} X) := by
    rw [AddMonoidAlgebra.intCast_def]
    congr 1
  rw [e, map_intCast, map_intCast]

theorem torusPt_ext {Z : Over S} {τ₁ τ₂ : Z ⟶ splitTorus S X}
    (h : ∀ χ, τ₁.left.appTop.hom (charUnit S X χ).val = τ₂.left.appTop.hom (charUnit S X χ).val) :
    τ₁ = τ₂ := by
  have key : ∀ f g : Z.left ⟶ Spec (torusRing ZU X),
      (Scheme.ΓSpecIso (torusRing ZU X)).inv ≫ f.appTop = (Scheme.ΓSpecIso (torusRing ZU X)).inv ≫ g.appTop →
        f = g := by
    intro f g hfg
    have hh : ∀ f' : Z.left ⟶ Spec (torusRing ZU X), (Scheme.ΓSpecIso (torusRing ZU X)).inv ≫ f'.appTop =
        ((ΓSpec.adjunction.homEquiv Z.left (Opposite.op (torusRing ZU X))).symm f').unop := by
      intro f'
      have h0 := ΓSpecIso_inv_ΓSpec_adjunction_homEquiv
        ((ΓSpec.adjunction.homEquiv Z.left (Opposite.op (torusRing ZU X))).symm f').unop
      have hf : f' = ΓSpec.adjunction.homEquiv Z.left (Opposite.op (torusRing ZU X))
          ((ΓSpec.adjunction.homEquiv Z.left (Opposite.op (torusRing ZU X))).symm f').unop.op :=
        ((ΓSpec.adjunction.homEquiv Z.left (Opposite.op (torusRing ZU X))).apply_symm_apply f').symm
      conv_lhs => rw [hf]
      exact h0
    have hψ := (hh f).symm.trans (hfg.trans (hh g))
    exact (ΓSpec.adjunction.homEquiv Z.left (Opposite.op (torusRing ZU X))).symm.injective
      (congrArg Quiver.Hom.op hψ)
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · apply key
    apply CommRingCat.hom_ext
    apply ringHom_ext_ZU
    intro χ
    have e1 := charUnit_appTop τ₁.left χ
    have e2 := charUnit_appTop τ₂.left χ
    simp only [CommRingCat.hom_comp, RingHom.comp_apply]
    erw [← e1, ← e2]
    exact h χ
  · exact (Over.w τ₁).trans (Over.w τ₂).symm

end ReciprocityTheory.ChartRestriction.G.Semi.TorusPts
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickenedUniformisedGroupPointExt

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

theorem gtCoord_overPoint_ext {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)
    {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (a a' : Z ⟶ thickObj R I e G)
    (hp : a.left ≫ g.pG.left = a'.left ≫ g.pG.left)
    (hv : ∀ (z : Z.left) (J : (Z.left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
      ∀ χ : D.X, val (g.t χ) a.left z J = val (g.t χ) a'.left z J) : a = a' := by
  have := g.i_hom
  have := g.q_hom
  have hq : a ≫ g.q = a' ≫ g.q := by
    refine Over.OverMorphism.ext (pullback.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
    exact (Category.assoc _ _ _).trans (hp.trans (Category.assoc _ _ _).symm)
  have hd : (a' * a⁻¹) ≫ g.q = toUnit _ ≫ η[thickObj R I e D.P.A] := by
    rw [MonObj.mul_comp, GrpObj.inv_comp, hq, mul_inv_cancel]
    rfl
  let τ := g.isKernel.lift (a' * a⁻¹) (toUnit _) hd
  have hτ : τ ≫ g.i = a' * a⁻¹ := g.isKernel.lift_fst _ _ _
  have h1 : τ = 1 := by
    refine TorusPts.torusPt_ext fun χ => ?_
    refine congrArg Units.val (show pullU τ.left ⊤ (charUnit _ D.X χ) =
      pullU (1 : Z ⟶ splitTorus _ D.X).left ⊤ (charUnit _ D.X χ) from unit_ext fun z _ => ?_)
    choose J hJ using fun ψ : Z.left ⟶ D.P.A.left => exists_chart D.P.isLB (ψ z)
    have k := (TorusCoord.val_torus_point_and_translate R I D e G g Z τ a z J hJ χ).2
    have k' := (TorusCoord.val_torus_point_and_translate R I D e G g Z 1 a z J hJ χ).2
    rw [hτ, inv_mul_cancel_right] at k
    rw [MonObj.one_comp, _root_.one_mul] at k'
    have k2 := mul_right_cancel (k.symm.trans ((hv z J hJ χ).symm.trans k'))
    exact (gm_pull (𝟙 Z.left) τ.left z ⊤ trivial _).trans (k2.trans
      (gm_pull (𝟙 Z.left) (1 : Z ⟶ splitTorus _ D.X).left z ⊤ trivial _).symm)
  rw [h1, MonObj.one_comp] at hτ
  exact (mul_inv_eq_one.1 hτ.symm).symm

theorem gtCoord_point_ext : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) {Z : Scheme.{0}} (r r' : Z ⟶ (thickObj R I e G).left), r ≫ (thickObj R I e G).hom = r' ≫ (thickObj R I e G).hom → r ≫ g.pG.left = r' ≫ g.pG.left → (∀ (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → ∀ χ : D.X, val (g.t χ) r z J = val (g.t χ) r' z J) → r = r' := by
  intro R _ _ I D e G _ _ g Z r r' hb hp hv
  let FinalForm : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) :=
    Over.mk (r ≫ (thickObj R I e G).hom)
  exact congrArg (fun φ => φ.left) (gtCoord_overPoint_ext g (Z := FinalForm) (Over.homMk r rfl) (Over.homMk r' hb.symm) hp hv)

end GlobalTheory.Mum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickenedUniformisedGroupPointExtStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.thickenedUniformisedGroup_point_ext : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) {Z : Scheme.{0}} (r r' : Z ⟶ (thickObj R I e G).left), r ≫ (thickObj R I e G).hom = r' ≫ (thickObj R I e G).hom → r ≫ g.pG.left = r' ≫ g.pG.left → (∀ (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → ∀ χ : D.X, val (g.t χ) r z J = val (g.t χ) r' z J) → r = r' := by
  first | exact @GlobalTheory.Mum.gtCoord_point_ext | exact GlobalTheory.Mum.gtCoord_point_ext | (intros; apply GlobalTheory.Mum.gtCoord_point_ext <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusCoordinateValueEqOfMaps

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

theorem val_eq_of_maps_pullAlong {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] (F : X ⟶ X) (φ : K → (Y ⟶ X))
    (ε : K → ℤ) (W : LB.Iso (LB.LinComb L φ ε) (LB.LinComb (L.pull F) φ ε)) (a t : LB.Gen (LB.LinComb L φ ε))
    (f f' : Y ⟶ Y) (hψ : ∀ k, φ k ≫ F = f ≫ φ k) (hψ' : ∀ k, φ k ≫ F = f' ≫ φ k)
    (h : LB.Gen.Maps W a (GeneratorPullback.pullAlong L F f φ ε φ hψ t)) (h' : LB.Gen.Maps W a (GeneratorPullback.pullAlong L F f' φ ε φ hψ' t))
    (z : Y) (J : (Y ⟶ X) → L.ι) (hJ : Good L z J) : val t f z J = val t f' z J := by
  let jj : K → (L.pull F).ι := fun k _ => J (φ k ≫ F)
  let q : K → L.ι := fun k => J (φ k)
  have m₁ : (𝟙 Y : Y ⟶ Y) z ∈ LB.wchart (L.pull F) φ jj :=
    Set.mem_iInter.2 fun k => Set.mem_iInter.2 fun _ => hJ (φ k ≫ F)
  have m₂ : (𝟙 Y : Y ⟶ Y) z ∈ LB.wchart L φ q := Set.mem_iInter.2 fun k => hJ (φ k)
  have m : (𝟙 Y : Y ⟶ Y) z ∈ LB.wchart (L.pull F) φ jj ⊓ LB.wchart L φ q := ⟨m₁, m₂⟩
  have key : ∀ (f : Y ⟶ Y) (hψ : ∀ k, φ k ≫ F = f ≫ φ k),
      val t f z J = gm (𝟙 Y) z _ (res (inf_le_left : LB.wchart (L.pull F) φ jj ⊓ LB.wchart L φ q ≤ _)
        ((GeneratorPullback.pullAlong L F f φ ε φ hψ t).s jj)) := by
    intro f hψ
    rw [val_of t f z J (fun k => J (φ k ≫ F)) (fun k => by rw [hψ k])]
    exact ((gm_res (𝟙 Y) z _ m _).trans ((gm_res (𝟙 Y) z _ m₁ _).trans
      (gm_pull (𝟙 Y) f z _ (@GeneratorPullback.pullAlong_le _ _ _ _ L _ _ F f φ φ hψ jj z m₁) _))).symm
  rw [key f hψ, key f' hψ']
  exact congrArg (gm (𝟙 Y) z _) ((h (jj, q)).trans (h' (jj, q)).symm)

theorem gtCoord_val_eq_of_maps : ∀ {R' : Type} [CommRing R'] [IsDomain R'] {I' : Ideal R'} {D' : DegPre R'} {e : ℕ} {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G'] [IsCommMonObj G'] (g : GtCoord I' D' e G') (F : D'.P.A.left ⟶ D'.P.A.left) (w : LB.Iso D'.P.L (D'.P.L.pull F)) (f f' : (thickObj R' I' e G').left ⟶ (thickObj R' I' e G').left) (x : D'.X) (hψ : ∀ k : Fin 4, D'.Oφ g.pG x k ≫ F = f ≫ D'.Oφ g.pG x k) (hψ' : ∀ k : Fin 4, D'.Oφ g.pG x k ≫ F = f' ≫ D'.Oφ g.pG x k), LB.Gen.Maps (LB.linCombIso w _ Oinvε) (g.t x) (GeneratorPullback.pullAlong D'.P.L F f _ Oinvε _ hψ (g.t x)) → LB.Gen.Maps (LB.linCombIso w _ Oinvε) (g.t x) (GeneratorPullback.pullAlong D'.P.L F f' _ Oinvε _ hψ' (g.t x)) → ∀ (z : (thickObj R' I' e G').left) (J : ((thickObj R' I' e G').left ⟶ D'.P.A.left) → D'.P.L.ι), Good D'.P.L z J → val (g.t x) f z J = val (g.t x) f' z J :=
  fun g F _ f f' x hψ hψ' h h' z J hJ => val_eq_of_maps_pullAlong F _ Oinvε _ (g.t x) (g.t x) f f' hψ hψ' h h' z J hJ

end GlobalTheory.Mum
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusCoordinateValueEqOfMapsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.torusCoordinate_value_eq_of_maps : ∀ {R' : Type} [CommRing R'] [IsDomain R'] {I' : Ideal R'} {D' : DegPre R'} {e : ℕ} {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G'] [IsCommMonObj G'] (g : GtCoord I' D' e G') (F : D'.P.A.left ⟶ D'.P.A.left) (w : LB.Iso D'.P.L (D'.P.L.pull F)) (f f' : (thickObj R' I' e G').left ⟶ (thickObj R' I' e G').left) (x : D'.X) (hψ : ∀ k : Fin 4, D'.Oφ g.pG x k ≫ F = f ≫ D'.Oφ g.pG x k) (hψ' : ∀ k : Fin 4, D'.Oφ g.pG x k ≫ F = f' ≫ D'.Oφ g.pG x k), LB.Gen.Maps (LB.linCombIso w _ Oinvε) (g.t x) (GeneratorPullback.pullAlong D'.P.L F f _ Oinvε _ hψ (g.t x)) → LB.Gen.Maps (LB.linCombIso w _ Oinvε) (g.t x) (GeneratorPullback.pullAlong D'.P.L F f' _ Oinvε _ hψ' (g.t x)) → ∀ (z : (thickObj R' I' e G').left) (J : ((thickObj R' I' e G').left ⟶ D'.P.A.left) → D'.P.L.ι), Good D'.P.L z J → val (g.t x) f z J = val (g.t x) f' z J := by
  first | exact @GlobalTheory.Mum.gtCoord_val_eq_of_maps | exact GlobalTheory.Mum.gtCoord_val_eq_of_maps | (intros; apply GlobalTheory.Mum.gtCoord_val_eq_of_maps <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupGaloisMapUnique

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.GalUniq

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

theorem abPart_eq {ρ : R →+* R'} {s : R' →+* R'} {D : DegPre R} {D' : DegPre R'}
    (hD : IsPullDeg ρ D D') (h h' : IsPullDeg s D' D') (H : PullOver hD h) (H' : PullOver hD h') :
    h.e.hom.left ≫ pullback.fst D'.P.A.hom (specOf s) =
      h'.e.hom.left ≫ pullback.fst D'.P.A.hom (specOf s) := by
  have hcb := H.2 _ _ rfl rfl
  have hcb' := H'.2 _ _ rfl rfl
  have hov : ∀ k : IsPullDeg s D' D', (k.e.hom.left ≫ pullback.fst D'.P.A.hom (specOf s)) ≫ D'.P.A.hom =
      D'.P.A.hom ≫ specOf s := by
    intro k
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    congr 1
    exact Over.w k.e.hom
  have : IsIso hD.e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map hD.e.hom))
  rw [← cancel_mono hD.e.hom.left]
  refine pullback.hom_ext ?_ ?_
  · simp only [Category.assoc]
    simp only [Category.assoc] at hcb hcb'
    rw [hcb, hcb']
  · simp only [Category.assoc]
    have w0 : hD.e.hom.left ≫ pullback.snd D.P.A.hom (specOf ρ) = D'.P.A.hom := Over.w hD.e.hom
    rw [w0, ← Category.assoc, hov h, ← Category.assoc, hov h']

theorem iso_eq_of_rig {s : R' →+* R'} {D' : DegPre R'} (F : D'.P.A.left ⟶ D'.P.A.left)
    (he : eSec D'.P.A ≫ F = specOf s ≫ eSec D'.P.A)
    (w w' : LB.Iso D'.P.L (D'.P.L.pull F)) (hw : w.IsGen) (hw' : w'.IsGen)
    (hr : LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => 1)) D'.rig
      (rigPullOf F (specOf s) he D'.P.L D'.rig))
    (hr' : LB.Gen.Maps (LB.linCombIso w' (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => 1)) D'.rig
      (rigPullOf F (specOf s) he D'.P.L D'.rig)) : w = w' :=
  iso_unique_of_rig GlobalTheory.globalFns_holds D'.P.A D'.P.isAb D'.P.isLB D'.P.isLB hw hw' hr hr'

theorem level_eq {I' : Ideal R'} {D' : DegPre R'} {e : ℕ} {G' : Over (Sp R')} [GrpObj G']
    [IsCommMonObj G'] (g : GtCoord I' D' e G') (F : D'.P.A.left ⟶ D'.P.A.left)
    (w : LB.Iso D'.P.L (D'.P.L.pull F)) (hw : w.IsGen)
    (f f' : (thickObj R' I' e G').left ⟶ (thickObj R' I' e G').left)
    (hb : f ≫ pullback.snd G'.hom (thick R' I' e) = f' ≫ pullback.snd G'.hom (thick R' I' e))
    (hp : g.pG.left ≫ F = f ≫ g.pG.left) (hp' : g.pG.left ≫ F = f' ≫ g.pG.left)
    (ht : ∀ x : D'.X, ∃ hψ : ∀ k : Fin 4, D'.Oφ g.pG x k ≫ F = f ≫ D'.Oφ g.pG x k,
      LB.Gen.Maps (LB.linCombIso w _ Oinvε) (g.t x)
        (GeneratorPullback.pullAlong D'.P.L F f _ Oinvε _ hψ (g.t x)))
    (ht' : ∀ x : D'.X, ∃ hψ : ∀ k : Fin 4, D'.Oφ g.pG x k ≫ F = f' ≫ D'.Oφ g.pG x k,
      LB.Gen.Maps (LB.linCombIso w _ Oinvε) (g.t x)
        (GeneratorPullback.pullAlong D'.P.L F f' _ Oinvε _ hψ (g.t x))) : f = f' := by
  exact GlobalTheory.T.thickenedUniformisedGroup_point_ext g f f' hb (hp.symm.trans hp') fun z J hJ χ => by
    obtain ⟨hψ, hm⟩ := ht χ
    obtain ⟨hψ', hm'⟩ := ht' χ
    exact GlobalTheory.T.torusCoordinate_value_eq_of_maps g F w f f' χ hψ hψ' hm hm' z J hJ

end GlobalTheory.Mum.GalUniq

namespace GlobalTheory.Mum.GalUniq

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

theorem level_eq_two {s : R' →+* R'} {I' : Ideal R'} {D' : DegPre R'} {e : ℕ} {G' : Over (Sp R')} [GrpObj G']
    [IsCommMonObj G'] (g : GtCoord I' D' e G') (F F' : D'.P.A.left ⟶ D'.P.A.left) (hF : F = F')
    (he : eSec D'.P.A ≫ F = specOf s ≫ eSec D'.P.A) (he' : eSec D'.P.A ≫ F' = specOf s ≫ eSec D'.P.A)
    (w : LB.Iso D'.P.L (D'.P.L.pull F)) (hw : w.IsGen)
    (w' : LB.Iso D'.P.L (D'.P.L.pull F')) (hw' : w'.IsGen)
    (hr : LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => 1)) D'.rig
      (rigPullOf F (specOf s) he D'.P.L D'.rig))
    (hr' : LB.Gen.Maps (LB.linCombIso w' (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => 1)) D'.rig
      (rigPullOf F' (specOf s) he' D'.P.L D'.rig))
    (xe xe' : D'.X → D'.X) (hxe : xe = id) (hxe' : xe' = id)
    (f f' : (thickObj R' I' e G').left ⟶ (thickObj R' I' e G').left)
    (hb : f ≫ pullback.snd G'.hom (thick R' I' e) = f' ≫ pullback.snd G'.hom (thick R' I' e))
    (hp : g.pG.left ≫ F = f ≫ g.pG.left) (hp' : g.pG.left ≫ F' = f' ≫ g.pG.left)
    (ht : ∀ x : D'.X, ∃ hψ : ∀ k : Fin 4, D'.Oφ g.pG x k ≫ F = f ≫ D'.Oφ g.pG (xe x) k,
      LB.Gen.Maps (LB.linCombIso w _ Oinvε) (g.t x)
        (GeneratorPullback.pullAlong D'.P.L F f _ Oinvε _ hψ (g.t (xe x))))
    (ht' : ∀ x : D'.X, ∃ hψ : ∀ k : Fin 4, D'.Oφ g.pG x k ≫ F' = f' ≫ D'.Oφ g.pG (xe' x) k,
      LB.Gen.Maps (LB.linCombIso w' _ Oinvε) (g.t x)
        (GeneratorPullback.pullAlong D'.P.L F' f' _ Oinvε _ hψ (g.t (xe' x)))) : f = f' := by
  subst hF hxe hxe'
  obtain rfl := iso_eq_of_rig F he w w' hw hw' hr hr'
  exact level_eq g F w hw f f' hb hp hp' ht ht'

end GlobalTheory.Mum.GalUniq


open GlobalTheory.Mum.GalUniq in
theorem GlobalTheory.Mum.galMap_unique : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (σ : Gal ρ) (a a' : G'.left ⟶ G'.left), GalMap hD U' σ a → GalMap hD U' σ a' → a = a' := by
  intro R _ _ _ _ R' _ _ _ ρ hρ D D' hD A' G' _ _ hG U' σ a a' ha ha'
  obtain ⟨-, h, bc, rfl, P, PO⟩ := ha
  obtain ⟨-, h', bc', rfl, P', PO'⟩ := ha'
  have hc := abPart_eq hD h h' PO PO'
  have hxe : (⇑h.xe : D'.toPre.X → D'.toPre.X) = id := funext PO.1
  have hxe' : (⇑h'.xe : D'.toPre.X → D'.toPre.X) = id := funext PO'.1
  have hov : ∀ (b : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'),
      b.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) ≫ G'.hom = G'.hom ≫ specOf (Gal.hom σ) := by
    intro b
    rw [pullback.condition, ← Category.assoc]
    congr 1
    exact Over.w b.hom
  have lev : ∀ n : ℕ, (fstG (maximalIdeal R') n G').left ≫ bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) =
      (fstG (maximalIdeal R') n G').left ≫ bc'.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) := by
    intro n
    obtain ⟨wL, -, he1, -, hl⟩ := P.lg
    obtain ⟨wL', -, he1', -, hl'⟩ := P'.lg
    obtain ⟨f, hf, hpG, hT, -⟩ := hl n
    obtain ⟨f', hf', hpG', hT', -⟩ := hl' n
    have hb : f ≫ pullback.snd G'.hom (thick R' (maximalIdeal R') n) =
        f' ≫ pullback.snd G'.hom (thick R' (maximalIdeal R') n) := by
      have : IsClosedImmersion (thick R' (maximalIdeal R') n) :=
        IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
      rw [← cancel_mono (thick R' (maximalIdeal R') n), Category.assoc, Category.assoc,
        ← pullback.condition]
      have e1 : f ≫ (fstG (maximalIdeal R') n G').left ≫ G'.hom =
          (fstG (maximalIdeal R') n G').left ≫ G'.hom ≫ specOf (Gal.hom σ) := by
        rw [← Category.assoc, hf]; simp only [Category.assoc]; rw [hov bc]
      have e2 : f' ≫ (fstG (maximalIdeal R') n G').left ≫ G'.hom =
          (fstG (maximalIdeal R') n G').left ≫ G'.hom ≫ specOf (Gal.hom σ) := by
        rw [← Category.assoc, hf']; simp only [Category.assoc]; rw [hov bc']
      exact e1.trans e2.symm
    have := level_eq_two (U'.gt n) _ _ hc h.he h'.he h.w h.w_gen h'.w h'.w_gen h.w_rig h'.w_rig _ _ hxe hxe' f f' hb hpG hpG' hT hT'
    rw [← hf, ← hf', this]
  have hI : maximalIdeal R' ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
  have : IsNoetherianRing R' := hρ.1.1
  have : Smooth G'.hom := hG.smooth
  have : GeometricallyConnected G'.hom := hG.geomConnected
  have : IsSeparated G'.hom := hG.separated
  have : IsIso (CommRingCat.ofHom (Gal.hom σ)) := σ.1.toCommRingCatIso.isIso_hom
  have : IsIso (specOf (Gal.hom σ)) := inferInstanceAs (IsIso (Spec.map _))
  let Y : Over (Sp R') := Over.mk (G'.hom ≫ inv (specOf (Gal.hom σ)))
  have : IsSeparated Y.hom := inferInstanceAs (IsSeparated (G'.hom ≫ inv (specOf (Gal.hom σ))))
  have hov2 : ∀ (b : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'),
      (b.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ))) ≫ Y.hom = G'.hom := by
    intro b
    change _ ≫ G'.hom ≫ inv (specOf (Gal.hom σ)) = _
    simp only [Category.assoc]
    rw [reassoc_of% (hov b), IsIso.hom_inv_id, Category.comp_id]
  have key := (sec_eq_zero_and_hom_eq_of_thickenings R' (maximalIdeal R') hI G').2 Y
    (Over.homMk (bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ))) (hov2 bc))
    (Over.homMk (bc'.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ))) (hov2 bc')) lev
  exact congrArg CommaMorphism.left key
end
end
end
