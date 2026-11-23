module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullData
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGenericIsoOfUniformisationsIsoData
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordBundlePullbackGrpPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullDegIdentitySelfAdmissible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSemiAbelianOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalMumfordFamilyPullbackLocalUniformised
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
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoCompValuesMulStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalBaseDataPullbackAlongMap
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SplitsAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalMumfordFamilyPullbackLocalUniformisedStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

theorem _root_.GlobalTheory.T.canonical_mumford_family_pullback_local_uniformised : ∀ (R V' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing V'] [IsDomain V'] [IsLocalRing V'] (θ : R →+* V'), IsCN R → IsCN V' → IsLocalHom θ → ∀ (Q : Data R) (W : (Sp R).Opens) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (P : LB (G2 G₁).left), IsSemiAbelian G₁ → CanonOn Q W G₁ P → spMap θ (genericPoint (Sp V')) ∈ W → ∀ (D' : DegData V' (maximalIdeal V')) (ex : D'.toPre.X ≃+ Q.X), PullData Q θ (GlobalTheory.PolDeg.Wit.ofDeg D'.toPre D'.tau_bimult) ex → ∃ (G' : Over (Sp V')) (_ : GrpObj G') (_ : IsCommMonObj G') (π : G'.left ⟶ G₁.left) (π₂ : (G2 G').left ⟶ (G2 G₁).left) (A : PolAV (Sp (FractionRing V'))) (U : Unif (maximalIdeal V') D' A G'), IsGrpPullback G' G₁ (spMap θ) π ∧ IsSquare π π₂ ∧ LBIso (abelian₂ G' U.LG.L) (P.pull π₂) := by
  first | exact @GlobalTheory.Mum.canon_pull_unif | exact GlobalTheory.Mum.canon_pull_unif | (intros; apply GlobalTheory.Mum.canon_pull_unif <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullDataRefines

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem pullData_refines : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (θ : R →+* V) (Q : Data R) (Q' : Data V) (e : Q'.X ≃+ Q.X) (D : DegPre V) (hB : D.TauBimult) (e' : D.X ≃+ Q'.X), PullData Q θ Q' e → Refines Q' (RingHom.id V) D e' → PullData Q θ (GlobalTheory.PolDeg.Wit.ofDeg D hB) (e'.trans e) := by
  intro R V _ _ _ _ θ Q Q' e D hB e' hP hR
  obtain ⟨β, β₂, w, hpb, hsq, hw, hc, ht⟩ := hP
  obtain ⟨β', β'₂, w', hpb', hsq', hw', hc', ht'⟩ := hR
  have hs : spMap (RingHom.id V) = 𝟙 (Sp V) := Spec.map_id _
  letI := D.P.isAb.comm
  obtain ⟨w'', hw'', hv⟩ := GlobalTheory.T.mumfordBundleIso_comp_values_mul _ _ _ D.P.A Q'.B Q.B D.P.L Q'.M.L Q.M.L
    D.P.isLB Q'.M.isLB Q.M.isLB β'₂ β₂ _ rfl w hw w' hw'
  refine ⟨β' ≫ β, β'₂ ≫ β₂, w'', ?_, ?_, hw'', fun a => ?_, fun a b => ?_⟩
  · exact (hpb'.comp hpb).congr (by rw [hs, Category.id_comp]) rfl
  · refine ⟨?_, ?_⟩
    · erw [Category.assoc, hsq.1, ← Category.assoc, hsq'.1, Category.assoc]
    · erw [Category.assoc, hsq.2, ← Category.assoc, hsq'.2, Category.assoc]
  · have h₁ : (D.c a).left ≫ β' = (Q'.c (e' a)).left := (hc' a).trans (by rw [hs, Category.id_comp])
    show (D.c a).left ≫ β' ≫ β = _
    rw [← Category.assoc, h₁]
    exact hc (e' a)
  · obtain ⟨u, x, y, k, k', hu, hy, hk, hk', h1, h2⟩ := ht (e' a) (e' b)
    refine ⟨u, x, y, k, k', hu, hy, hk, hk', h1, fun z J J' hJ hJ' => ?_⟩
    obtain ⟨I, hI⟩ := GlobalTheory.DegPull.exists_good' Q'.M.isLB z
    have hκ : 𝟙 (TK V).left ≫ jK V = jK V ≫ spMap (RingHom.id V) := by rw [hs, Category.id_comp, Category.comp_id]
    have hca : ∀ a, (D.c a).left ≫ β' = (Q'.c (e' a)).left := fun a => (hc' a).trans (by rw [hs, Category.id_comp])
    have t1 := ht' (𝟙 _) hκ a b z I J' hI hJ'
    have hp : (lift (toUnit (TK V) ≫ D.c a) (toUnit (TK V) ≫ D.c b)).left ≫ β'₂ =
        (lift (toUnit (TK V) ≫ Q'.c (e' a)) (toUnit (TK V) ≫ Q'.c (e' b))).left := by
      apply pullback.hom_ext
      · show _ ≫ (fst Q'.B Q'.B).left = _ ≫ (fst Q'.B Q'.B).left
        rw [Category.assoc, hsq'.1, ← Category.assoc, ← Over.comp_left, lift_fst, ← Over.comp_left, lift_fst,
          Over.comp_left, Over.comp_left, Category.assoc]
        exact congrArg (_ ≫ ·) (hca _)
      · show _ ≫ (snd Q'.B Q'.B).left = _ ≫ (snd Q'.B Q'.B).left
        rw [Category.assoc, hsq'.2, ← Category.assoc, ← Over.comp_left, lift_snd, ← Over.comp_left, lift_snd,
          Over.comp_left, Over.comp_left, Category.assoc]
        exact congrArg (_ ≫ ·) (hca _)
    have t2 := h2 z J I hJ hI
    have t3 := hv _ (lift (toUnit (TK V) ≫ D.c a) (toUnit (TK V) ≫ D.c b)).left z J' I J hJ' hI hJ
    rw [hp] at t3
    have t0 := (Wit.exists_tau D a b).choose_spec.2 _ (𝟙 _) z J' hJ'
    show val (Wit.exists_tau D a b).choose (𝟙 _) z J' = _
    rw [t0, t1, t2]
    erw [t3]
    exact (mul_left_comm _ _ _).trans (congrArg _ (_root_.mul_assoc _ _ _).symm)

end GlobalTheory.Mum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalBaseDataPullbackAlongMapStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

theorem _root_.GlobalTheory.T.tautological_base_data_pullback_along_map : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (θ : R →+* V) (iw : W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (Q : Data R) (e : Q.X ≃+ (Fin T.r → ℤ)) (Q' : Data V) (e' : Q'.X ≃+ (Fin T.r → ℤ)), (∀ i, θ (s i) ≠ 0) → DataFrom T iw s ε n Q e → DataFrom T (θ.comp iw) (fun i => θ (s i)) ε n Q' e' → PullData Q θ Q' (e'.trans e.symm) := by
  first | exact @GlobalTheory.PullFrom.pullData_of_dataFrom | exact GlobalTheory.PullFrom.pullData_of_dataFrom | (intros; apply GlobalTheory.PullFrom.pullData_of_dataFrom <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnifPullbackOfCanonicalOn

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.TChart.Taut

theorem unif_pull_of_canonOn : ∀ {g n : ℕ} {φ : InvFun ℤ} (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (P : LB (G2 G₁).left), IsMumPol C.Q G₁ P → GlobalTheory.Mum.CanonOn C.Q (PrimeSpectrum.basicOpen (∏ k, C.t k)) G₁ P → ∀ (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (θ : C.R →+* V'), IsCN V' → IsLocalHom θ → (∀ k, θ (C.s k) ≠ 0) → ∀ (D' : DegData V' (maximalIdeal V')) (e : D'.toPre.X ≃+ (Fin C.T.r → ℤ)), DegFrom C.T (θ.comp C.iw) (fun k => θ (C.s k)) C.form n D'.toPre e → ∃ (G' : Over (Sp V')) (_ : GrpObj G') (_ : IsCommMonObj G') (π : G'.left ⟶ G₁.left) (π₂ : (G2 G').left ⟶ (G2 G₁).left) (A : PolAV (Sp (FractionRing V'))) (U : Unif (maximalIdeal V') D' A G'), IsGrpPullback G' G₁ (spMap θ) π ∧ IsSquare π π₂ ∧ LBIso (abelian₂ G' U.LG.L) (P.pull π₂) := by
  intro g n φ C G₁ _ _ P hM hC V' _ _ _ θ hV hθ hs D' e hD
  obtain ⟨Q', e', hr, hd⟩ := hD
  have h₁ := GlobalTheory.T.tautological_base_data_pullback_along_map C.T C.R V' θ C.iw C.s C.form n C.Q C.e Q' _ hs C.data hd
  have h₂ := GlobalTheory.Mum.pullData_refines C.R V' θ C.Q Q' _ D'.toPre D'.tau_bimult e' h₁ hr
  refine GlobalTheory.T.canonical_mumford_family_pullback_local_uniformised C.R V' θ hM.1 hV hθ C.Q _ G₁ P hM.2.2.1 hC ?_ D' _ h₂
  rw [genericPoint_eq_bot_of_affine]
  show (∏ k, C.t k) ∉ Ideal.comap θ (⊥ : PrimeSpectrum V').asIdeal
  rw [Ideal.mem_comap, map_prod]
  exact Finset.prod_ne_zero_iff.2 fun k _ => hs (.inl k)

end GlobalTheory.TChart.Taut
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnifPullbackOfCanonicalOnStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.unif_pullback_of_canonical_on : ∀ {g n : ℕ} {φ : InvFun ℤ} (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (P : LB (G2 G₁).left), IsMumPol C.Q G₁ P → GlobalTheory.Mum.CanonOn C.Q (PrimeSpectrum.basicOpen (∏ k, C.t k)) G₁ P → ∀ (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (θ : C.R →+* V'), IsCN V' → IsLocalHom θ → (∀ k, θ (C.s k) ≠ 0) → ∀ (D' : DegData V' (maximalIdeal V')) (e : D'.toPre.X ≃+ (Fin C.T.r → ℤ)), DegFrom C.T (θ.comp C.iw) (fun k => θ (C.s k)) C.form n D'.toPre e → ∃ (G' : Over (Sp V')) (_ : GrpObj G') (_ : IsCommMonObj G') (π : G'.left ⟶ G₁.left) (π₂ : (G2 G').left ⟶ (G2 G₁).left) (A : PolAV (Sp (FractionRing V'))) (U : Unif (maximalIdeal V') D' A G'), IsGrpPullback G' G₁ (spMap θ) π ∧ IsSquare π π₂ ∧ LBIso (abelian₂ G' U.LG.L) (P.pull π₂) := by
  first | exact @GlobalTheory.TChart.Taut.unif_pull_of_canonOn | exact GlobalTheory.TChart.Taut.unif_pull_of_canonOn | (intros; apply GlobalTheory.TChart.Taut.unif_pull_of_canonOn <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitChartGenericFibresSame

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChart

theorem sameFib_trait_chart : ∀ {g n : ℕ} {φ : InvFun ℤ} (F : SFam g n (zetaAway n)) (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (P : LB (G2 G₁).left), IsMumPol C.Q G₁ P → GlobalTheory.Mum.CanonOn C.Q (PrimeSpectrum.basicOpen (∏ k, C.t k)) G₁ P → ∀ (T : GlobalTheory.Poinc.Trait F) (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (θ : C.R →+* V') (f : T.V →+* V') (fK : FractionRing T.V →+* FractionRing V'), IsCN V' → IsLocalHom θ → (∀ k, θ (C.s k) ≠ 0) → (∀ a, fK (algebraMap T.V _ a) = algebraMap V' _ (f a)) → ∀ (D' : DegData V' (maximalIdeal V')) (e : D'.toPre.X ≃+ (Fin C.T.r → ℤ)), DegFrom C.T (θ.comp C.iw) (fun k => θ (C.s k)) C.form n D'.toPre e → ∀ (G' : Over (Sp V')) [GrpObj G'] [IsCommMonObj G'] (πG : G'.left ⟶ T.G.left) (A' : PolAV (Sp (FractionRing V'))) (U' : Unif (maximalIdeal V') D' A' G'), IsUnifAlong F T.y (T.U.gen.hom.left ≫ T.α) f πG U' → SameFib F.univ.A F.univ.P (spMap fK ≫ T.y) G₁ P (spMap ((algebraMap V' (FractionRing V')).comp θ)) := by
  intro g n φ F C G₁ _ _ P hP hC T V' _ _ _ θ f fK hV' hθ hs hfK D' e hDF G' _ _ πG A' U' hU
  obtain ⟨G'', _, _, π, π₂, A'', U'', hπ, hπ₂, hΛ''⟩ := GlobalTheory.T.unif_pullback_of_canonical_on C G₁ P hP hC V' θ hV' hθ hs D' e hDF
  obtain ⟨hG', κ, πK, α, α₂, hκ, -, hα, hα₂, hΛ', -⟩ := hU

  have hκ' : κ = spMap fK := by
    haveI := GlobalTheory.Mum.EvenDesc.mono_jK T.V
    rw [← cancel_mono (jK T.V), hκ]
    have e₁ : (algebraMap V' (FractionRing V')).comp f = fK.comp (algebraMap T.V (FractionRing T.V)) :=
      RingHom.ext fun a => (hfK a).symm
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun r => Spec.map (CommRingCat.ofHom r)) e₁
  subst hκ'
  have hsG'' : IsSemiAbelian G'' := GlobalTheory.Mum.EvenDesc.isSemiAbelian_of_isGrpPullback hπ hP.2.2.1
  have hsG' : IsSemiAbelian G' := GlobalTheory.Mum.EvenDesc.isSemiAbelian_of_isGrpPullback hG' T.semi
  have hAdm : AdmBase V' (maximalIdeal V') := ⟨hV'.1, inferInstance, hV'.2.1, hV'.2.2.1⟩
  obtain ⟨hD, -⟩ := GlobalTheory.DegPullId.exists_isPullDeg_id_self V' _ hAdm D'
  obtain ⟨ψ, hψm, hψL, -⟩ := GlobalTheory.exists_generic_iso_of_unif GlobalTheory.firstFiveLaws.1 GlobalTheory.firstFiveLaws.2.1 V'
    (maximalIdeal V') hAdm (maximalIdeal.isMaximal V').ne_top D' D' A'' A' G'' G' hsG'' hsG' U'' U' hD
  haveI := hψm
  haveI := U''.gen_hom
  haveI : IsMonHom U''.gen.symm.hom := inferInstanceAs (IsMonHom U''.gen.inv)

  let b : A'.A.left ⟶ G''.left := ψ.hom.left ≫ U''.gen.inv.left ≫ pullback.fst G''.hom (jK V')
  have hb : IsGrpPullback A'.A G'' (jK V') b :=
    ((isGrpPullback_of_iso ψ).comp ((isGrpPullback_of_iso U''.gen.symm).comp
      (isGrpPullback_pullback G'' (jK V')))).congr (by simp only [Category.id_comp]) rfl
  obtain ⟨b₂, hb₂, hΛb⟩ := GlobalTheory.Mum.lbIso_lam_pull_of_isGrpPullback _ _ (jK V') G'' A'.A b hb
  have hPLB : P.IsLB := hP.2.2.2.1.1
  have hL : LBIso A'.L (U''.LG.L.pull b) :=
    LBIso.trans A'.isLB (pull_isLB A''.isLB _) (pull_isLB U''.LG.isLB _) hψL
      (GlobalTheory.GenSpread.lbIso_pull_comp (ψ.hom.left ≫ U''.gen.inv.left)
        (by rw [Category.assoc, ← Over.comp_left, Iso.inv_hom_id, Over.id_left, Category.comp_id])
        (by simp only [b, Category.assoc]) U''.ext)
  have hΛA : LBIso (abelian₂ A'.A A'.L) (P.pull (b₂ ≫ π₂)) :=
    hΛb U''.LG.L A'.L _ P π₂ U''.LG.isLB A'.isLB hPLB hL hΛ''
  have hθK : spMap ((algebraMap V' (FractionRing V')).comp θ) = jK V' ≫ spMap θ := by
    show Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp]; rfl
  refine ⟨A'.A, inferInstance, inferInstance, α, α₂, b ≫ π, b₂ ≫ π₂, hα, hα₂,
    (hb.comp hπ).congr hθK.symm rfl, ⟨?_, ?_⟩, ?_⟩
  · rw [Category.assoc, hπ₂.1, ← Category.assoc, hb₂.1, Category.assoc]
  · rw [Category.assoc, hπ₂.2, ← Category.assoc, hb₂.2, Category.assoc]
  · exact LBIso.trans (pull_isLB F.univ.isLB _) (DVR.linComb_isLB _ A'.isLB _ _) (pull_isLB hPLB _) hΛ'.symm hΛA

end GlobalTheory.TChart
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitChartGenericFibresSameStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.trait_chart_generic_fibres_same : ∀ {g n : ℕ} {φ : InvFun ℤ} (F : SFam g n (zetaAway n)) (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (P : LB (G2 G₁).left), IsMumPol C.Q G₁ P → GlobalTheory.Mum.CanonOn C.Q (PrimeSpectrum.basicOpen (∏ k, C.t k)) G₁ P → ∀ (T : GlobalTheory.Poinc.Trait F) (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (θ : C.R →+* V') (f : T.V →+* V') (fK : FractionRing T.V →+* FractionRing V'), IsCN V' → IsLocalHom θ → (∀ k, θ (C.s k) ≠ 0) → (∀ a, fK (algebraMap T.V _ a) = algebraMap V' _ (f a)) → ∀ (D' : DegData V' (maximalIdeal V')) (e : D'.toPre.X ≃+ (Fin C.T.r → ℤ)), DegFrom C.T (θ.comp C.iw) (fun k => θ (C.s k)) C.form n D'.toPre e → ∀ (G' : Over (Sp V')) [GrpObj G'] [IsCommMonObj G'] (πG : G'.left ⟶ T.G.left) (A' : PolAV (Sp (FractionRing V'))) (U' : Unif (maximalIdeal V') D' A' G'), IsUnifAlong F T.y (T.U.gen.hom.left ≫ T.α) f πG U' → SameFib F.univ.A F.univ.P (spMap fK ≫ T.y) G₁ P (spMap ((algebraMap V' (FractionRing V')).comp θ)) := by
  first | exact @GlobalTheory.TChart.sameFib_trait_chart | exact GlobalTheory.TChart.sameFib_trait_chart | (intros; apply GlobalTheory.TChart.sameFib_trait_chart <;> assumption)
end
end
