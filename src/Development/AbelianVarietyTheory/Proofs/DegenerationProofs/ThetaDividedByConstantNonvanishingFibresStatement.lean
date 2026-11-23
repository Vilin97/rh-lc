module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FrameUnit
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ClassicalPointsAndLocalRegularity
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsClassicalPointFactorLargeModelStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGeneratorNormalisedMulByNIsoStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGenericFibreSectionOfModelSectionStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGlueSectionsSameThetaMultipleStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLocalThetaSectionFibreNonzero
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
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPadicLiftTorsionPointInvertibleOrderStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionPointSpecialFibreSectionNeZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IntegralTorsionPointDescendsToModelStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsLocalHomOfTest
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleIsoPullbackUniformisedThetaModelStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemSupIIffAndHHEqKer
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EqOfValFGeneric
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecGenericEqMulThetaStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaMulRegularAndUnitAlongTorsion
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSectionRestrictionUnitTwistStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSystemHasTestsOfRealPointStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionFrameIsUnitAlongSection
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionSectionEqIntegralPointAtTestStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedModelEqPullbackGroupSchemeStatement
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLocalThetaSectionFibreNonzeroStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_localThetaSection_fibreNonzero : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), Q.LocTheta → ∀ z : M.Z, ∃ (N : M.Z.Opens) (σ : Q.SecFam N), z ∈ N ∧ σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ N) ∧ Q.FibNe N σ := by
  first | exact @GlobalTheory.ZH.LocThetaConv.exists_secFam_fibNe | exact GlobalTheory.ZH.LocThetaConv.exists_secFam_fibNe | (intros; apply GlobalTheory.ZH.LocThetaConv.exists_secFam_fibNe <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RestrictEqOfSameThetaMultiple

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH
open GlobalTheory.Points

theorem ZHPre.resG_eq_of_thMul : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), S.Over₀ M U₀ → ∀ (N N' : M.Z.Opens) (σ : Q.SecFam N) (σ' : Q.SecFam N') (c : Ω), Q.ThMul c N σ → Q.ThMul c N' σ' → ∀ (j : Q.LOne.ι) (O : Q.G.left.Opens) (h : O ≤ Q.G.hom ⁻¹ᵁ N ⊓ Q.LOne.U j) (h' : O ≤ Q.G.hom ⁻¹ᵁ N' ⊓ Q.LOne.U j), resG _ h (σ j) = resG _ h' (σ' j) := by
  intro o Ω _ _ _ _ S ρ M U₀ Q hO N N' σ σ' c hσ hσ' j O h h'
  obtain ⟨K, _, β, g, r, jP, h1, h2, h3, h4⟩ := Q.exists_generic hO.ne
  obtain ⟨jL, rfl⟩ : ∃ jL, j = fun _ => jL := ⟨j 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
  refine eq_of_valF_generic (g ≫ Q.φ) h4 fun hm => ?_
  have hm' := (top_le_preimage_iff _ _).1 hm
  have hV : Set.range (g ≫ Q.φ) ⊆ (Q.G.hom ⁻¹ᵁ N : Q.G.left.Opens) := fun y hy => (h (hm' hy)).1
  have hV' : Set.range (g ≫ Q.φ) ⊆ (Q.G.hom ⁻¹ᵁ N' : Q.G.left.Opens) := fun y hy => (h' (hm' hy)).1
  have hL : Set.range (g ≫ Q.φ) ⊆ Q.L.L.U jL := fun y hy => Set.mem_iInter.1 (h (hm' hy)).2 0
  have e := (hσ K β g r jP jL h1 h2 h3 hL hV).symm.trans (hσ' K β g r jP jL h1 h2 h3 hL hV')
  refine (valR_res _ h hm _).trans (Eq.trans ?_ (valR_res _ h' hm _).symm)
  refine mul_left_cancel₀ (zpow_ne_zero _ ?_) e
  refine IsUnit.ne_zero ?_
  have hw : ⊤ ≤ g ⁻¹ᵁ (LB.div (ρ.P.L.pull (pullback.fst ρ.P.A.hom Q.u₀)) (Q.L.L.pull Q.φ)).U
      (fun _ => jP, fun _ => jL) := fun w _ =>
    ⟨Set.mem_iInter.2 fun _ => h3 ⟨w, Scheme.Hom.comp_apply _ _ _⟩,
      Set.mem_iInter.2 fun _ => hL ⟨w, Scheme.Hom.comp_apply _ _ _⟩⟩
  rw [valF_eq_valR, valR_eq g _ hw]
  exact (Units.isUnit _).map _

end GlobalTheory.ZH
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RestrictEqOfSameThetaMultipleStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.restrict_eq_of_same_theta_multiple : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), S.Over₀ M U₀ → ∀ (N N' : M.Z.Opens) (σ : Q.SecFam N) (σ' : Q.SecFam N') (c : Ω), Q.ThMul c N σ → Q.ThMul c N' σ' → ∀ (j : Q.LOne.ι) (O : Q.G.left.Opens) (h : O ≤ Q.G.hom ⁻¹ᵁ N ⊓ Q.LOne.U j) (h' : O ≤ Q.G.hom ⁻¹ᵁ N' ⊓ Q.LOne.U j), resG _ h (σ j) = resG _ h' (σ' j) := by
  first | exact @GlobalTheory.ZH.ZHPre.resG_eq_of_thMul | exact GlobalTheory.ZH.ZHPre.resG_eq_of_thMul | (intros; apply GlobalTheory.ZH.ZHPre.resG_eq_of_thMul <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaMulRegularAndUnitAlongTorsionStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.theta_mul_regular_and_unit_along_torsion : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), S.Over₀ M U₀ → ∀ (N : M.Z.Opens) (σ : Q.SecFam N) (c : Ω), σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ N) → Q.ThMul c N σ → ∀ (a : S.Gam) (W : M.Z.Opens) (h : W.toScheme ⟶ Q.G.left) (w : W.toScheme), Q.ExtPt a W h → Q.FrameUnit a W h w → W.ι w ∈ N → c * S.th a ∈ M.O (W.ι w) ∧ ∀ (K : Type) [Field K] (x : Sp K ⟶ W.toScheme) (j : Q.LOne.ι), Set.range x = {w} → valF (x ≫ h) _ (σ j) ≠ 0 → c * S.th a ≠ 0 ∧ (c * S.th a)⁻¹ ∈ M.O (W.ι w) := by
  first | exact @GlobalTheory.ZH.mul_theta_regular_and_unit | exact GlobalTheory.ZH.mul_theta_regular_and_unit | (intros; apply GlobalTheory.ZH.mul_theta_regular_and_unit <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionFrameIsUnitAlongSectionStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.torsionFrame_isUnit_along_section : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), S.Over₀ M U₀ → (∀ (α : LB.Gen (LB.LinComb ρ.P.L (K := Fin 2) ![𝟙 ρ.P.A.left, (mulA ρ.P.A (S.r * S.N)).left] ![(((S.r * S.N) : ℕ) : ℤ) ^ 2, -1])), α.IsGen → IsNormMul ρ.P.A ρ.P.L ρ.rig (S.r * S.N) α → ∃ κ, κ.IsGen ∧ Q.MulRel (S.r * S.N) α κ) → ∀ (a : S.Gam) (W : M.Z.Opens) (h : W.toScheme ⟶ Q.G.left) (w : W.toScheme), Q.ExtPt a W h → Q.FrameUnit a W h w := by
  first | exact @GlobalTheory.ZH.TorsFrame.frameUnit | exact GlobalTheory.ZH.TorsFrame.frameUnit | (intros; apply GlobalTheory.ZH.TorsFrame.frameUnit <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaDividedByConstantNonvanishingFibres

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.ZHPre
open GlobalTheory.Points
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω]
variable {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω} {U₀ : M.Z.Opens} (Q : ZHPre ρ M U₀)

theorem exists_thMul (h1 : Laws) (h2 : Laws2) (ov : S.Over₀ M U₀) (N : M.Z.Opens) (σ : Q.SecFam N)
    (hσ : σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ N)) (hN : (N : Set M.Z).Nonempty) : ∃ c, Q.ThMul c N σ := by
  have hpt : Set.range M.pt ⊆ Set.range U₀.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    exact (top_le_preimage_iff M.pt U₀).1 (M.top_le_preimage_pt ov.ne) ⟨w, rfl⟩
  have heta : IsOpenImmersion.lift U₀.ι M.pt hpt ≫ U₀.ι = M.pt := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_genericFibre_section_of_model_section o Ω S ρ M U₀ Q N σ _ hσ hN heta
  obtain ⟨c, hc⟩ := GlobalTheory.T.sec_generic_eq_mul_theta_alt h1 h2 o Ω S ρ s
  refine ⟨c, ?_⟩
  intro K _ β g r jP jL hg hr hP hL _
  have hg' : g ≫ pullback.snd _ _ = spMap β ≫ IsOpenImmersion.lift U₀.ι M.pt hpt := by
    rw [← cancel_mono U₀.ι, Category.assoc, Category.assoc, heta]
    exact hg
  have hcomm : spMap β ≫ spMap S.R.val.toRingHom = (g ≫ pullback.fst ρ.P.A.hom Q.u₀) ≫ ρ.P.A.hom := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hg', Category.assoc, Q.u₀_gen _ heta]
  let q : Sp K ⟶ ((Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ⊗ ρ.P.A).left :=
    pullback.lift (spMap β) (g ≫ pullback.fst _ _) hcomm
  have hq1 : q ≫ (fst (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ρ.P.A).left = spMap β :=
    pullback.lift_fst _ _ _
  have hq2 : q ≫ (snd (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ρ.P.A).left =
      g ≫ pullback.fst _ _ :=
    pullback.lift_snd _ _ _
  have e1 := hs K β q g jP jL hq1 hq2.symm hg' hP hL
  have e2 := hc K β q r jP hq1 (hr.trans hq2.symm) (by rw [hq2]; exact hP)
  simp only [Finset.univ_unique, Finset.sum_singleton, zpow_one]
  rw [← e2, e1]

theorem exists_good_label (h0 : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f)) (hs : GlobalTheory.Published.SemistableReductionSt) (hU : ThmUSt) (h1 : Laws) (h2 : Laws2)
    (hT : UTorsSt) (big : S.Big) (ov : S.Over₀ M U₀) (N : M.Z.Opens) (σ : Q.SecFam N)
    (hσ : σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ N)) (hne : Q.FibNe N σ) (z : M.Z) (hz : IsClosed ({z} : Set M.Z))
    (hzN : z ∈ N) : ∃ a ∈ S.HH M z, ∀ (W : M.Z.Opens) (h : W.toScheme ⟶ Q.G.left) (w : W.toScheme),
      Q.ExtPt a W h → W.ι w = z → ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ W.toScheme) (j : Q.LOne.ι),
        Set.range x = {w} ∧ valF (x ≫ h) _ (σ j) ≠ 0 := by
  haveI : Algebra.FiniteType ℤ o := ArithBase.ft (Ω := Ω)
  haveI : CharZero Ω := ArithBase.char (o := o)
  obtain ⟨⟨p, hp, y, hy⟩, -⟩ := (classical_points_and_local_regularity o Ω M U₀ ov.normal).1 U₀ le_rfl ov.ne z hz
  obtain ⟨y₀, Fs, hAt, hint, hfac⟩ := GlobalTheory.T.exists_classical_point_factor_large_model o Ω S ρ M U₀ Q ov z p y hy
  obtain ⟨u, l, τ, hmatch, hFs⟩ := (GlobalTheory.T.thetaSystem_hasTests_of_real_point hs hU h1 h2 hT o Ω S ρ).2 p y₀ Fs hint
  obtain ⟨jV, yV, yK, hTF⟩ := hfac u hFs
  obtain ⟨F, ψ, hTM⟩ := GlobalTheory.T.exists_testMap_of_testFac h0 o Ω S ρ M U₀ Q p y y₀ u jV yV yK hTF
  have hLB := GlobalTheory.T.lineBundleIso_pullback_uniformisedThetaModel o Ω S ρ M U₀ Q p y y₀ u jV yV yK hTF F ψ hTM
  have hyN : y (cPt p) ∈ N := by rw [hy.1]; exact hzN
  obtain ⟨t, ht, j, hj⟩ := GlobalTheory.T.exists_torsionPoint_specialFibre_section_ne_zero h1 h2 o Ω S ρ M U₀ Q big p y y₀ u jV yV yK hTF F ψ hTM hLB N σ hσ hne hyN
  have hn : IsUnit ((S.r * S.N : ℕ) : Γ(Sp u.V, ⊤)) := by
    have hv : IsUnit ((S.r * S.N : ℕ) : u.V) := by
      have he : ((S.r * S.N : ℕ) : o) * ↑(S.unit.unit⁻¹) = 1 := S.unit.mul_val_inv
      have hnorm : ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (u.yK (algebraMap o S.R ↑(S.unit.unit⁻¹)))‖ ≤ 1 := by
        have hf := RingHom.congr_fun u.fac (algebraMap o S.R ↑(S.unit.unit⁻¹))
        rw [RingHom.comp_apply] at hf
        rw [hf]
        exact hint _
      obtain ⟨v, hvE⟩ := (u.norm_le _).1 hnorm
      have hmul : ((S.r * S.N : ℕ) : u.V) * v = 1 := by
        apply IsFractionRing.injective u.V (FractionRing u.V)
        rw [map_mul, map_one, hvE, map_natCast, ← map_natCast u.yK, ← map_natCast (algebraMap o S.R),
          ← map_mul, ← map_mul, he, map_one, map_one]
      exact ⟨⟨_, v, hmul, by rw [mul_comm]; exact hmul⟩, rfl⟩
    simpa using hv.map (Scheme.ΓSpecIso (CommRingCat.of u.V)).inv.hom
  obtain ⟨b, hb, hbt⟩ := GlobalTheory.T.exists_padicLift_torsionPoint_invertibleOrder p (Sp u.V) u.G u.semi (spMap jV) (S.r * S.N) hn t ht
  obtain ⟨a, hV, x, ⟨hV1, hx1, hx2, hx3⟩, hbV⟩ := GlobalTheory.T.integral_torsion_point_descends_to_model o Ω S ρ p y₀ u jV hTF.1 b hb
  have hker : a ∈ τ.yy.ker := by
    obtain ⟨e, -, he⟩ := hmatch
    have hl : l.yy a = 0 := (AddMonoidHom.mem_ker).1 ((l.ker_iff a).2 ⟨hV, x, hV1, hx1, hx2, hx3⟩)
    have h0' : τ.yy a = QuotientAddGroup.mk 0 := (he a 0).2 (by rw [hl, map_zero]; rfl)
    rw [AddMonoidHom.mem_ker, h0']
    rfl
  have hHH := (ThetaSys.mem_supI_iff_and_HH_eq_ker o Ω S M U₀ ov z p y y₀ τ hy hAt).2
  refine ⟨a, by rw [hHH]; exact hker, ?_⟩
  intro W h w hExt hwz
  haveI := isLocalHom_of_test u jV hTF.1
  have hzW : z ∈ W := by
    have hr : z ∈ Set.range W.ι := ⟨w, hwz⟩
    rwa [Scheme.Opens.range_ι] at hr
  have hVz : yV (IsLocalRing.closedPoint u.V) = z := by
    rw [← hy.1, ← hTF.2.1, Scheme.Hom.comp_apply]
    congr 1
    exact (IsLocalRing.comap_closedPoint jV).symm
  have hsp : ∀ v, yV v ⤳ z := fun v => hVz ▸ (IsLocalRing.specializes_closedPoint v).map yV.continuous
  have hrange : Set.range yV ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]
    exact (top_le_preimage_iff yV W).1 (top_le_preimage_of_specializes hsp hzW)
  have hyW : IsOpenImmersion.lift W.ι yV hrange ≫ W.ι = yV := IsOpenImmersion.lift_fac _ _ _
  have hcomp := GlobalTheory.T.torsionSection_eq_integral_point_at_test o Ω S ρ M U₀ Q p y y₀ u jV yV yK hTF F ψ hTM a W h hExt hV x
    ⟨hV1, hx1, hx2, hx3⟩ _ hyW
  refine ⟨IsLocalRing.ResidueField (OO p), inferInstance,
    spMap (IsLocalRing.residue (OO p)) ≫ spMap jV ≫ IsOpenImmersion.lift W.ι yV hrange, j, ?_, ?_⟩
  · rw [Set.range_unique]
    congr 1
    apply W.ι.isOpenEmbedding.injective
    rw [hwz, ← Scheme.Hom.comp_apply]
    simp only [Category.assoc, hyW, hTF.2.1]
    rw [Scheme.Hom.comp_apply, ← hy.1]
    congr 1
    rw [show (default : Sp (IsLocalRing.ResidueField (OO p))) = IsLocalRing.closedPoint _ from
      Subsingleton.elim _ _]
    exact IsLocalRing.comap_closedPoint (IsLocalRing.residue (OO p))
  · have hx : (spMap (IsLocalRing.residue (OO p)) ≫ spMap jV ≫ IsOpenImmersion.lift W.ι yV hrange) ≫ h =
        t.left ≫ F := by
      rw [Category.assoc, Category.assoc, hcomp, ← Category.assoc (spMap jV), hbV, ← Category.assoc, hbt]
    rw [hx]
    exact hj

theorem exists_theta_div : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → GlobalTheory.Published.SemistableReductionSt → ThmUSt → Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), S.Big → S.Over₀ M U₀ → Q.Sec → Q.LocTheta → ∀ (W : M.Z.Opens) (x₀ : S.Gam), (∀ z ∈ W, x₀ ∈ S.supI M z) → ∃ σ ∈ secOn (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => 1)) (Q.G.hom ⁻¹ᵁ W), GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w 1 (fun _ : Unit => ρ.th₁) (fun _ => (S.th x₀)⁻¹) _ σ ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ M.Z), Set.range x ⊆ W → ∃ (g : Sp K ⟶ Q.G.left) (j : _), g ≫ Q.G.hom = x ∧ valF g _ (σ j) ≠ 0 := by
  intro h0 hs hU h1 h2 hT o Ω _ _ _ _ S ρ M U₀ Q big ov hSec hLoc W x₀ hx₀
  refine GlobalTheory.T.exists_glue_sections_same_theta_multiple o Ω S ρ M U₀ Q (S.th x₀)⁻¹
    (fun N N' σ σ' hσ hσ' j O h h' => GlobalTheory.T.restrict_eq_of_same_theta_multiple o Ω S ρ M U₀ Q ov N N' σ σ' _ hσ hσ' j O h h') W ?_
  intro z hzW
  haveI : Algebra.FiniteType ℤ o := ArithBase.ft (Ω := Ω)
  haveI : CharZero Ω := ArithBase.char (o := o)
  haveI : JacobsonSpace M.Z := (classical_points_and_local_regularity o Ω M U₀ ov.normal).2
  obtain ⟨N₀, σ₀, hzN₀, hσ₀, hne₀⟩ := GlobalTheory.T.exists_localThetaSection_fibreNonzero o Ω S ρ M U₀ Q hLoc z
  obtain ⟨c₀, hc₀⟩ := Q.exists_thMul h1 h2 ov N₀ σ₀ hσ₀ ⟨z, hzN₀⟩
  have hext : ∀ (z' : M.Z), ∀ b ∈ S.HH M z', ∃ (Wb : M.Z.Opens) (hb : Wb.toScheme ⟶ Q.G.left) (wb : Wb.toScheme),
      Q.ExtPt b Wb hb ∧ Wb.ι wb = z' ∧ Q.FrameUnit b Wb hb wb := by
    intro z' b hb
    obtain ⟨Wb, hb', hz'Wb, hb1, hb2⟩ := hSec z' b hb
    obtain ⟨wb, hwb⟩ : z' ∈ Set.range Wb.ι := by rw [Scheme.Opens.range_ι]; exact hz'Wb
    have hE : Q.ExtPt b Wb hb' := ⟨hb1, hb2⟩
    exact ⟨Wb, hb', wb, hE, hwb, GlobalTheory.T.torsionFrame_isUnit_along_section o Ω S ρ M U₀ Q ov
      (fun α hα hn => GlobalTheory.T.exists_generator_normalised_mulByN_iso o Ω S ρ M U₀ Q ov (S.r * S.N) α hα hn) b Wb hb' wb hE⟩
  have hcl : ∀ z' : M.Z, IsClosed ({z'} : Set M.Z) → z' ∈ N₀ → z' ∈ W →
      c₀ * S.th x₀ ≠ 0 ∧ c₀ * S.th x₀ ∈ M.O z' ∧ (c₀ * S.th x₀)⁻¹ ∈ M.O z' := by
    intro z' hz' hz'N hz'W
    obtain ⟨a, ha, hgood⟩ := Q.exists_good_label h0 hs hU h1 h2 hT big ov N₀ σ₀ hσ₀ hne₀ z' hz' hz'N
    obtain ⟨Wa, ha', wa, hEa, hwa, hFa⟩ := hext z' a ha
    have hwaN : Wa.ι wa ∈ N₀ := by rw [hwa]; exact hz'N
    have hxa := GlobalTheory.T.theta_mul_regular_and_unit_along_torsion o Ω S ρ M U₀ Q ov N₀ σ₀ c₀ hσ₀ hc₀ a Wa ha' wa hEa hFa hwaN
    obtain ⟨K, _, x, j, hx, hv⟩ := hgood Wa ha' wa hEa hwa
    obtain ⟨hne, hinv⟩ := hxa.2 K x j hx hv
    have hx₀' : x₀ ∈ S.supI M z' := hx₀ z' hz'W
    obtain ⟨Wb, hb', wb, hEb, hwb, hFb⟩ := hext z' x₀ (AddSubgroup.subset_closure hx₀')
    have hwbN : Wb.ι wb ∈ N₀ := by rw [hwb]; exact hz'N
    have hxb := (GlobalTheory.T.theta_mul_regular_and_unit_along_torsion o Ω S ρ M U₀ Q ov N₀ σ₀ c₀ hσ₀ hc₀ x₀ Wb hb' wb hEb hFb hwbN).1
    rw [hwa] at hinv
    rw [hwb] at hxb
    have hdiv : M.Div S.th x₀ z' := hx₀'
    obtain ⟨hth, hdivs⟩ := hdiv
    have hc : c₀ ≠ 0 := left_ne_zero_of_mul hne
    have hta : S.th a ≠ 0 := right_ne_zero_of_mul hne
    refine ⟨mul_ne_zero hc hth, hxb, ?_⟩
    have heq : (c₀ * S.th x₀)⁻¹ = S.th a / S.th x₀ * (c₀ * S.th a)⁻¹ := by
      field_simp
    rw [heq]
    exact Subalgebra.mul_mem _ (hdivs a) hinv
  have hopen : IsOpen {z' : M.Z | c₀ * S.th x₀ ∈ M.O z' ∧ (c₀ * S.th x₀)⁻¹ ∈ M.O z'} :=
    (M.isOpen_setOf_mem_O _).inter (M.isOpen_setOf_mem_O _)
  have hall : ∀ z' : M.Z, z' ∈ N₀ → z' ∈ W → c₀ * S.th x₀ ∈ M.O z' ∧ (c₀ * S.th x₀)⁻¹ ∈ M.O z' := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨z₂, hz₂N, hz₂W, hbad⟩ := hcon
    have hZ : (((N₀ : Set M.Z) ∩ (W : Set M.Z)) ∩
        {z' : M.Z | c₀ * S.th x₀ ∈ M.O z' ∧ (c₀ * S.th x₀)⁻¹ ∈ M.O z'}ᶜ).Nonempty :=
      ⟨z₂, ⟨hz₂N, hz₂W⟩, fun h => hbad h.1 h.2⟩
    obtain ⟨z', ⟨⟨hz'N, hz'W⟩, hz'bad⟩, hz'c⟩ := nonempty_inter_closedPoints hZ
      ⟨_, _, N₀.isOpen.inter W.isOpen, hopen.isClosed_compl, rfl⟩
    obtain ⟨-, h1', h2'⟩ := hcl z' hz'c hz'N hz'W
    exact hz'bad ⟨h1', h2'⟩
  obtain ⟨z₁, ⟨hz₁N, hz₁W⟩, hz₁c⟩ := nonempty_inter_closedPoints
    (⟨z, hzN₀, hzW⟩ : ((N₀ : Set M.Z) ∩ (W : Set M.Z)).Nonempty) (N₀.isOpen.inter W.isOpen).isLocallyClosed
  have hf0 : c₀ * S.th x₀ ≠ 0 := (hcl z₁ hz₁c hz₁N hz₁W).1
  obtain ⟨σ', hσ', hth', hne'⟩ := GlobalTheory.T.theta_section_restriction_unit_twist o Ω S ρ M U₀ Q N₀ (N₀ ⊓ W) σ₀ c₀ (c₀ * S.th x₀)⁻¹ inf_le_left
    (fun z' hz' => by
      obtain ⟨hz'N, hz'W⟩ := hz'
      obtain ⟨h1', h2'⟩ := hall z' hz'N hz'W
      exact ⟨inv_ne_zero hf0, h2', by rw [inv_inv]; exact h1'⟩) hσ₀ hc₀ hne₀
  have hc₀0 : c₀ ≠ 0 := left_ne_zero_of_mul hf0
  have hth0 : S.th x₀ ≠ 0 := right_ne_zero_of_mul hf0
  have hfc : (c₀ * S.th x₀)⁻¹ * c₀ = (S.th x₀)⁻¹ := by
    field_simp
  rw [hfc] at hth'
  exact ⟨N₀ ⊓ W, σ', ⟨hzN₀, hzW⟩, inf_le_right, hσ', hth', hne'⟩

end GlobalTheory.ZH.ZHPre
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaDividedByConstantNonvanishingFibresStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.thetaDividedByConstant_nonvanishing_fibres : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → GlobalTheory.Published.SemistableReductionSt → ThmUSt → Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), S.Big → S.Over₀ M U₀ → Q.Sec → Q.LocTheta → ∀ (W : M.Z.Opens) (x₀ : S.Gam), (∀ z ∈ W, x₀ ∈ S.supI M z) → ∃ σ ∈ secOn (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => 1)) (Q.G.hom ⁻¹ᵁ W), GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w 1 (fun _ : Unit => ρ.th₁) (fun _ => (S.th x₀)⁻¹) _ σ ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ M.Z), Set.range x ⊆ W → ∃ (g : Sp K ⟶ Q.G.left) (j : _), g ≫ Q.G.hom = x ∧ valF g _ (σ j) ≠ 0 := by
  first | exact @GlobalTheory.ZH.ZHPre.exists_theta_div | exact GlobalTheory.ZH.ZHPre.exists_theta_div | (intros; apply GlobalTheory.ZH.ZHPre.exists_theta_div <;> assumption)
end
end
