module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSinglePolarisationGeneratorAllTraits
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisationGenericFibreCartesianToModelBundle
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNzOfPolAt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsThetaSectionNonzeroFibresLocalRing
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiRelOfExpT
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaConstantsIntegralUnitOfClosedFibreNonvanish
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SvalUpSec
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsExpandsAtOfIntegral
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.NotSymEOfNe
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasThetaConstantsTwoLevelsMoveCartesian
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNeronNeutralComponentFiniteLevel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaConstantListAlgClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralElemOfValNonnegOverCompleteDVRStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaConstantListOfFibrePullbackFieldExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolFibOfPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipallyPolarisedFibreIffOfGrpPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantUniqueAndLinearInSection
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemeGlueAffineCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThValAtAndNotIsThValue
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValExt
import Mathlib.AlgebraicGeometry.Modules.Sheaf

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionNonzeroUniformisedModelDvr

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Ex.OneGen
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin.ModelNZ

theorem exists_sec_nz : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CharZero W], IsAdicComplete (IsLocalRing.maximalIdeal W) W → ∀ (D : DegData W (IsLocalRing.maximalIdeal W)) (A : PolAV (Sp (FractionRing W))) (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (IsLocalRing.maximalIdeal W) D A G), ∃ σ : SecAt G U.LG.L (𝟙 (Sp W)), NZ G U.LG.L (𝟙 (Sp W)) σ := by
  intro R _ _ _ _ _ D A G _ _ hsemi U
  haveI : GeometricallyConnected G.hom := hsemi.geomConnected
  have hLaws := GlobalTheory.abelianSchemeLaws_all

  obtain ⟨th, hth, -⟩ := GlobalTheory.PsiRing.exists_basis_fibNZ hLaws.2.secTwist R D.toPre
  obtain ⟨f₀, hf₀⟩ : ∃ f₀ : D.toPre.SecB 1 0, ∀ (Z : Scheme.{0}) (r : Z ⟶ _) (z : Z) (J), Good D.toPre.P.L z J →
      sval th r z J = sval f₀ (r ≫ (snd (𝟙_ _) D.toPre.P.A).left) z J := by
    refine GlobalTheory.PsiExpansion.exists_sec_of_retract D.toPre.P.isLB _ _
      (GlobalTheory.PsiExpansion.snd_lift_unit D.toPre.P.A) (fun i => ?_) th
    fin_cases i
    · exact congrArg CommaMorphism.left (lift_snd (toUnit D.toPre.P.A) (𝟙 D.toPre.P.A))
    · refine congrArg CommaMorphism.left (show lift (toUnit D.toPre.P.A) (𝟙 D.toPre.P.A) ≫
        padd D.toPre.P.A (snd _ _) (toUnit _ ≫ D.toPre.c 0) = padd D.toPre.P.A (𝟙 _) (toUnit _ ≫ D.toPre.c 0) from ?_)
      simp only [padd, ← Category.assoc, comp_lift, lift_snd, comp_toUnit]
    · refine congrArg CommaMorphism.left
        (show lift (toUnit D.toPre.P.A) (𝟙 D.toPre.P.A) ≫ toUnit _ ≫ D.toPre.c 0 = toUnit _ ≫ D.toPre.c 0 from ?_)
      rw [← Category.assoc, comp_toUnit]
    · refine congrArg CommaMorphism.left
        (show lift (toUnit D.toPre.P.A) (𝟙 D.toPre.P.A) ≫ toUnit _ ≫ η[D.toPre.P.A] = toUnit _ ≫ η[D.toPre.P.A] from ?_)
      rw [← Category.assoc, comp_toUnit]
  obtain ⟨z₀, hz₀, hn₀⟩ := hth (IsLocalRing.closedPoint R)
  have hx : D.toPre.P.A.hom ((snd (𝟙_ (Over (Sp R))) D.toPre.P.A).left z₀) = IsLocalRing.closedPoint R :=
    (congrArg (fun q => q z₀) (Over.w (snd (𝟙_ (Over (Sp R))) D.toPre.P.A))).trans hz₀
  obtain ⟨J, hJ⟩ := GlobalTheory.ConstFam.exists_good' D.toPre.P.isLB z₀
  have hu : IsUnit (sval th (𝟙 _) z₀ J) := (isUnit_sval_iff th (𝟙 _) z₀ hJ).2 hn₀
  rw [hf₀ _ _ z₀ J hJ, Category.id_comp] at hu
  have hxn := (isUnit_sval_iff f₀ _ z₀ hJ).1 hu

  obtain ⟨σ, fam, hfam0, hσ, hmem, -⟩ := GlobalTheory.ThetaUnit.exists_theta hLaws.1.globalFns hLaws.1.secBaseChange
    le_rfl U f₀ ⟨_, hx, hxn⟩
  obtain ⟨g, hg, hn⟩ : ∃ g, G.hom g = IsLocalRing.closedPoint R ∧ g ∈ nonzeroLocus σ :=
    GlobalTheory.ThetaUnit.exists_mem_nonzeroLocus le_rfl U.toUnifPre (hσ 0)
      (by rw [hfam0]; exact ⟨_, hx, hxn⟩) hmem
  refine ⟨GlobalTheory.TorRef.upSec G σ, GlobalTheory.Ex.OnModel.toBase G g, ?_, ?_⟩
  · have a : GlobalTheory.Ex.OnModel.toBase G ≫ (fst (Over.mk (𝟙 (Sp R))) G).left = G.hom := by
      rw [GlobalTheory.Ex.OnModel.toBase, ← Over.comp_left, lift_fst]; rfl
    rw [← Scheme.Hom.comp_apply, a]
    exact hg
  · refine GlobalTheory.Ex.OnModel.mem_nonzeroLocus_pullTo σ _ _ ?_
    rw [← Scheme.Hom.comp_apply, GlobalTheory.Ex.OnModel.toBase_snd]
    exact hn

end GlobalTheory.UMin.ModelNZ
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionNonzeroUniformisedModelDvrStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Ex.OneGen
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_section_nonzero_uniformised_model_dvr : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CharZero W], IsAdicComplete (IsLocalRing.maximalIdeal W) W → ∀ (D : DegData W (IsLocalRing.maximalIdeal W)) (A : PolAV (Sp (FractionRing W))) (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (IsLocalRing.maximalIdeal W) D A G), ∃ σ : SecAt G U.LG.L (𝟙 (Sp W)), NZ G U.LG.L (𝟙 (Sp W)) σ := by
  first | exact @GlobalTheory.UMin.ModelNZ.exists_sec_nz | exact GlobalTheory.UMin.ModelNZ.exists_sec_nz | (intros; apply GlobalTheory.UMin.ModelNZ.exists_sec_nz <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsIntegralUnitMemberUniformisedTrait

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Ex.OneGen
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin.PrimModel

theorem spMap_comp' {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp [spMap, ← Spec.map_comp]

theorem spMap_id' (R : Type) [CommRing R] : spMap (RingHom.id R) = 𝟙 _ := by
  simp [spMap]

section
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left}

theorem heq_pullS {R : Type} [CommRing R] {x₁ x₂ : Sp R ⟶ S} (h : x₁ = x₂) {T : Over S}
    (f₁ : Over.mk x₁ ⟶ T) (f₂ : Over.mk x₂ ⟶ T) (hf : f₁.left = f₂.left)
    (s : LB.Sec (LPow G L ((1 : ℕ) : ℤ) T)) :
    HEq (VVRank.pullS G _ f₁ s) (VVRank.pullS G _ f₂ s) := by
  subst h
  obtain rfl : f₁ = f₂ := Over.OverMorphism.ext hf
  rfl

theorem thList_of_eq (ρ : LB.Gen (L.pull (eSec G))) (m : ℕ) {K : Type} [Field K] {x₁ x₂ : Sp K ⟶ S}
    (h : x₁ = x₂) {θ₁ : SecAt G L x₁} {θ₂ : SecAt G L x₂} (hθ : HEq θ₁ θ₂) {N : ℕ}
    {pt : Fin N → (Over.mk x₁ ⟶ G)} {c : Fin N → K} (H : ThList G L ρ m x₁ θ₁ pt c) :
    ∃ pt₂ : Fin N → (Over.mk x₂ ⟶ G), (∀ a, (pt₂ a).left = (pt a).left) ∧ ThList G L ρ m x₂ θ₂ pt₂ c := by
  subst h
  cases hθ
  exact ⟨pt, fun _ => rfl, H⟩

theorem pt_of_eq {R : Type} [CommRing R] {x₁ x₂ : Sp R ⟶ S} (h : x₁ = x₂) (p : Over.mk x₁ ⟶ G) :
    ∃ p₂ : Over.mk x₂ ⟶ G, p₂.left = p.left ∧ ∀ n : ℕ, p ^ n = 1 → p₂ ^ n = 1 := by
  subst h
  exact ⟨p, rfl, fun _ h => h⟩

theorem thG_unique [IsCommMonObj G] (ρ : LB.Gen (L.pull (eSec G))) (hL : L.IsLB) (hρ : ρ.IsGen) {g m : ℕ}
    {K : Type} [Field K] {x : Sp K ⟶ S} (θ : SecAt G L x) (p : Over.mk x ⟶ G) {c c' : K} (hm : Odd m)
    (hm0 : (m : K) ≠ 0) (hP : PolFib G L g x) (h₁ : ThG G L ρ m θ p (GlobalTheory.ZH.fn c))
    (h₂ : ThG G L ρ m θ p (GlobalTheory.ZH.fn c')) : c' = c := by
  have := (GlobalTheory.UMin.thG_smul_iff S G L ρ hL hρ g m K x θ θ p 1 c c' hm hm0 hP (by simp) h₁).1 h₂
  simpa using this
end

theorem isIntegralElem_of_sq {V F K Kb : Type} [CommRing V] [Field F] [Field K] [Field Kb] (φ : V →+* F) (i : V →+* K)
    (i' : K →+* Kb) (j : F →+* Kb) (hsq : i'.comp i = j.comp φ) {z : F} {w : K} (h : j z = i' w)
    (hz : φ.IsIntegralElem z) : i.IsIntegralElem w := by
  obtain ⟨p, hp, hp0⟩ := hz
  refine ⟨p, hp, i'.injective ?_⟩
  rw [Polynomial.hom_eval₂, ← h, hsq, ← Polynomial.hom_eval₂, hp0, map_zero, map_zero]

theorem polFib_unif {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] {D : DegData W (IsLocalRing.maximalIdeal W)}
    {A : PolAV (Sp (FractionRing W))} {G : Over (Sp W)} [GrpObj G] [IsCommMonObj G]
    (U : Unif (IsLocalRing.maximalIdeal W) D A G) (R : Type) [CommRing R] (y : Sp R ⟶ Sp (FractionRing W)) :
    PolFib G U.LG.L A.g (y ≫ jK W) := by
  have hα : IsGrpPullback A.A G (jK W) (U.gen.inv.left ≫ pullback.fst G.hom (jK W)) :=
    GlobalTheory.NeutralLevel.isGrpPullback_of_iso_inv (jK W) G U.gen U.gen_hom
  have hA := A.isLB
  have hLG : U.LG.L.IsLB := RigLB.isLB _
  have hLα : LBIso A.L (U.LG.L.pull (U.gen.inv.left ≫ pullback.fst G.hom (jK W))) := by
    obtain ⟨w, hw⟩ := U.ext
    have hB : LBIso A.L ((A.L.pull U.gen.hom.left).pull U.gen.inv.left) := by
      have e : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by
        rw [← Over.comp_left, U.gen.inv_hom_id, Over.id_left]
      have h1 := GlobalTheory.UMin.FibMove.lbIso_pull_comp hA U.gen.hom.left U.gen.inv.left
      rw [e] at h1
      exact LBIso.trans hA (pull_isLB hA _) (pull_isLB (pull_isLB hA _) _)
        (GlobalTheory.ThetaAffineGlue.lbIso_pull_id hA) h1
    exact GlobalTheory.ThetaAffineGlue.lbIso_comp hA (pull_isLB hA _) hLG hB ⟨w, hw⟩
  exact (GlobalTheory.UMin.FibMove.polFib_move (Sp W) (Sp (FractionRing W)) G U.LG.L A.A A.L (jK W) _ hLG hA hα hLα A.g R
    y).1.mp (GlobalTheory.UMin.FibExist.polFib_of_point _ A R y)

theorem main : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CharZero W], IsAdicComplete (IsLocalRing.maximalIdeal W) W → ∀ (D : DegData W (IsLocalRing.maximalIdeal W)) (A : PolAV (Sp (FractionRing W))) (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (IsLocalRing.maximalIdeal W) D A G) (σ : SecAt G U.LG.L (𝟙 (Sp W))), NZ G U.LG.L (𝟙 (Sp W)) σ → ∀ (m N : ℕ), Odd m → 3 ≤ m → IsUnit (m : W) → ∀ (K : Type) [Field K] [IsAlgClosed K] (i : W →+* K) (pt : Fin N → (Over.mk (spMap i ≫ 𝟙 (Sp W)) ⟶ G)) (c : Fin N → K), Function.Injective i → ThList G U.LG.L U.LG.rig m (spMap i ≫ 𝟙 (Sp W)) (SecAt.pull G U.LG.L σ i) pt c → Prim i c := by
  intro W _ _ _ _ hc D A G _ _ hG U σ hσ m N hodd h3 hmu K _ _ i pt c hi hL
  have hV : GlobalTheory.LN.CDvr W := ⟨inferInstance, hc, inferInstance⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
  let F := AlgebraicClosure (FractionRing W)
  obtain ⟨v, hv⟩ := ReciprocityTheory.ChartRestriction.G.DVR.exists_valOver hϖ F
  choose Q hQ using ReciprocityTheory.ChartRestriction.G.DVR.QForm.exists_QVal hϖ D
  let g := A.g
  set x' : Sp F ⟶ Sp W := jFK (R := W) F ≫ jK W with hx'
  let ξ : Over.mk x' ⟶ Over.mk (𝟙 (Sp W)) := Over.homMk x' (Category.comp_id _)
  set θF : SecAt G U.LG.L x' := VVRank.pullS G _ ξ σ with hθF
  obtain ⟨hA, x0, c0, hx0, hv0⟩ := (GlobalTheory.Ex.OnModel.theta_on_model GlobalTheory.lawsAndExpansions W hc ϖ hϖ D Q hQ F v hv A G hG U
    σ hσ).2 m hodd hmu h3 ξ
  let φF : W →+* F := (algebraMap (FractionRing W) F).comp (algebraMap W (FractionRing W))
  have hPF : PolFib G U.LG.L g x' := polFib_unif U F (jFK (R := W) F)
  have hmF : (m : F) ≠ 0 := by
    have := hmu.map φF
    rw [map_natCast] at this
    exact this.ne_zero
  obtain ⟨ptF, cF, hLF⟩ := GlobalTheory.UMin.exists_thList (Sp W) G U.LG.L U.LG.rig U.LG.isLB U.LG.rigGen g m (m ^ (4 * g)) F x'
    θF hodd hmF rfl hPF
  let Kb := AlgebraicClosure K
  let i' : K →+* Kb := algebraMap K Kb
  have hii : Function.Injective (i'.comp i) := i'.injective.comp hi
  let e : FractionRing W →+* Kb := IsFractionRing.lift hii
  letI : Algebra (FractionRing W) Kb := e.toAlgebra
  let j : F →+* Kb := (IsAlgClosed.lift : F →ₐ[FractionRing W] Kb).toRingHom
  have hsq : i'.comp i = j.comp φF := by
    ext r
    change _ = (IsAlgClosed.lift : F →ₐ[FractionRing W] Kb) (algebraMap (FractionRing W) F _)
    rw [AlgHom.commutes]
    exact (IsFractionRing.lift_algebraMap hii r).symm
  have hy : spMap i' ≫ spMap i ≫ 𝟙 (Sp W) = spMap j ≫ x' := by
    rw [Category.comp_id]
    change _ = spMap j ≫ (spMap (algebraMap (FractionRing W) F) ≫ spMap (algebraMap W (FractionRing W)))
    rw [← Category.assoc, spMap_comp', spMap_comp', spMap_comp', hsq]
  have hPy : PolFib G U.LG.L g (spMap j ≫ x') := by
    have := polFib_unif U Kb (spMap j ≫ jFK (R := W) F)
    simpa only [hx', Category.assoc] using this
  have hmKb : (m : Kb) ≠ 0 := by
    have := hmu.map (i'.comp i)
    rw [map_natCast] at this
    exact this.ne_zero
  obtain ⟨pt1, hpt1, hL1⟩ := GlobalTheory.UMin.ThPull.thList_pull (Sp W) G U.LG.L U.LG.rig U.LG.isLB U.LG.rigGen m N K Kb i'
    (spMap i ≫ 𝟙 (Sp W)) (SecAt.pull G U.LG.L σ i) pt c hL
  have hθ : HEq (SecAt.pull G U.LG.L (SecAt.pull G U.LG.L σ i) i') (SecAt.pull G U.LG.L θF j) := by
    simp only [SecAt.pull, hθF, GlobalTheory.ThetaRuleCompare.pullS_comp]
    refine heq_pullS hy _ _ ?_ σ
    simp only [Over.comp_left, Over.homMk_left]
    change spMap i' ≫ spMap i = spMap j ≫ (spMap (algebraMap (FractionRing W) F) ≫ spMap (algebraMap W (FractionRing W)))
    rw [spMap_comp', spMap_comp', spMap_comp', hsq]
  obtain ⟨ptK, hptK, hLK⟩ := thList_of_eq U.LG.rig m hy hθ hL1
  obtain ⟨ptF', hptF', hLF'⟩ := GlobalTheory.UMin.ThPull.thList_pull (Sp W) G U.LG.L U.LG.rig U.LG.isLB U.LG.rigGen m (m ^ (4 * g))
    F Kb j x' θF ptF cF hLF
  have hint : ∀ b, φF.IsIntegralElem (cF b) := fun b =>
    GlobalTheory.T.isIntegralElem_of_val_nonneg_over_completeDVR W hV ϖ hϖ F v hv (cF b) (hA (ptF b) (cF b) (hLF.2.1 b))
  refine ⟨fun a => ?_, ?_⟩
  · obtain ⟨b, hb⟩ := hLF.2.2 Kb j (ptK a) (hLK.2.1 a).1
    have heq : ptK a = ptF' b := Over.OverMorphism.ext (hb.trans (hptF' b).symm)
    have h1 := hLK.2.1 a
    rw [heq] at h1
    have hab : j (cF b) = i' (c a) :=
      thG_unique U.LG.rig U.LG.isLB U.LG.rigGen _ (ptF' b) hodd hmKb hPy h1 (hLF'.2.1 b)
    exact isIntegralElem_of_sq φF i i' j hsq hab (hint b)
  · obtain ⟨x0', hx0'l, hx0't⟩ := pt_of_eq (show x' = spMap (RingHom.id F) ≫ x' by rw [spMap_id', Category.id_comp]) x0
    obtain ⟨b0, hb0⟩ := hLF.2.2 F (RingHom.id F) x0' (hx0't _ hx0.1)
    have hx0b : x0 = ptF b0 := Over.OverMorphism.ext (by rw [← hx0'l, hb0, spMap_id', Category.id_comp])
    subst hx0b
    have hc0b : cF b0 = c0 :=
      thG_unique U.LG.rig U.LG.isLB U.LG.rigGen θF (ptF b0) hodd hmF hPF hx0 (hLF.2.1 b0)
    obtain ⟨q, hql, hqt⟩ := pt_of_eq hy.symm (ptF' b0)
    obtain ⟨a0, ha0⟩ := hL.2.2 Kb i' q (hqt _ (hLF'.2.1 b0).1)
    have heq : ptK a0 = ptF' b0 := Over.OverMorphism.ext (by rw [hptK, hpt1, ← ha0, hql])
    have h1 := hLK.2.1 a0
    rw [heq] at h1
    have hab : j c0 = i' (c a0) := by
      rw [← hc0b]
      exact thG_unique U.LG.rig U.LG.isLB U.LG.rigGen _ (ptF' b0) hodd hmKb hPy h1 (hLF'.2.1 b0)
    have hc0 : c0 ≠ 0 := by
      rintro rfl
      simp at hv0
    have hca : c a0 ≠ 0 := by
      intro h
      rw [h, map_zero] at hab
      exact hc0 (j.injective (hab.trans (map_zero j).symm))
    refine ⟨a0, hca, isIntegralElem_of_sq φF i i' j hsq (z := c0⁻¹) (by rw [map_inv₀, map_inv₀, hab]) ?_⟩
    refine GlobalTheory.T.isIntegralElem_of_val_nonneg_over_completeDVR W hV ϖ hϖ F v hv _ ?_
    have h01 : v c0 + v c0⁻¹ = 0 := by
      rw [← AddValuation.map_mul, mul_inv_cancel₀ hc0, AddValuation.map_one]
    rw [hv0, zero_add] at h01
    rw [h01]

end GlobalTheory.UMin.PrimModel
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsIntegralUnitMemberUniformisedTraitStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Ex.OneGen
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.theta_constants_integral_unit_member_uniformised_trait : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CharZero W], IsAdicComplete (IsLocalRing.maximalIdeal W) W → ∀ (D : DegData W (IsLocalRing.maximalIdeal W)) (A : PolAV (Sp (FractionRing W))) (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (IsLocalRing.maximalIdeal W) D A G) (σ : SecAt G U.LG.L (𝟙 (Sp W))), NZ G U.LG.L (𝟙 (Sp W)) σ → ∀ (m N : ℕ), Odd m → 3 ≤ m → IsUnit (m : W) → ∀ (K : Type) [Field K] [IsAlgClosed K] (i : W →+* K) (pt : Fin N → (Over.mk (spMap i ≫ 𝟙 (Sp W)) ⟶ G)) (c : Fin N → K), Function.Injective i → ThList G U.LG.L U.LG.rig m (spMap i ≫ 𝟙 (Sp W)) (SecAt.pull G U.LG.L σ i) pt c → Prim i c := by
  first | exact @GlobalTheory.UMin.PrimModel.main | exact GlobalTheory.UMin.PrimModel.main | (intros; apply GlobalTheory.UMin.PrimModel.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedTraitThetaConstantsTwoLevelsIntegral

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Ex.OneGen
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SiegTh.CmpUnif

theorem thList_smul {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : LB G.left}
    {ρ : LB.Gen (L.pull (eSec G))} (hL : L.IsLB) {m : ℕ} {K : Type} [Field K] {x : Sp K ⟶ S} {θ θ' : SecAt G L x}
    {a : K} (hθ : SecM.ofSec G θ' = @id Γ((Over.mk x).left, ⊤) (GlobalTheory.ZH.fn a) • SecM.ofSec G θ) {N : ℕ}
    {pt : Fin N → (Over.mk x ⟶ G)} {c : Fin N → K} (h : ThList G L ρ m x θ pt c) :
    ThList G L ρ m x θ' pt (fun b => a * c b) := by
  have hfn : ∀ u v : K, GlobalTheory.ZH.fn (u * v) = GlobalTheory.ZH.fn u * GlobalTheory.ZH.fn v := fun u v => map_mul _ u v
  refine ⟨h.1, fun b => ?_, h.2.2⟩
  rw [hfn]
  exact ThG.smul hL hθ (h.2.1 b)

theorem cmp_unif : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CharZero W], IsAdicComplete (IsLocalRing.maximalIdeal W) W → ∀ (D : DegData W (IsLocalRing.maximalIdeal W)) (A : PolAV (Sp (FractionRing W))) (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (_ : Unif (IsLocalRing.maximalIdeal W) D A G) (ρ : LB.Gen (A.L.pull (eSec A.A))), ρ.IsGen → ∀ (K : Type) [Field K] [IsAlgClosed K] (io : FractionRing W →+* K) (m m' N N' : ℕ) (d : Fin N → K) (d' : Fin N' → K), Odd m → 3 ≤ m → IsUnit (m : W) → Odd m' → 3 ≤ m' → IsUnit (m' : W) → (letI := A.isAb.comm; HasTh₂ A.A A.L ρ m m' (spMap io) d d') → ∃ a : K, a ≠ 0 ∧ Prim (io.comp (algebraMap W (FractionRing W))) (fun b => d b / a) ∧ Prim (io.comp (algebraMap W (FractionRing W))) (fun b => d' b / a) := by
  intro W _ _ _ _ hW D A G _ _ hG U ρ hρ K _ _ io m m' N N' d d' hm hm3 hmu hm' hm3' hmu' hd
  letI := A.isAb.comm
  obtain ⟨-, -, w, hp, -, hw, -⟩ := GlobalTheory.Ex.GenericFibre.exists_isoData W _ D A G U.toUnifPre
  have h₁ := (GlobalTheory.UMin.ThMove.hasTh₂_move _ G U.LG.L U.LG.rig U.LG.isLB U.LG.rigGen _ A.A A.L ρ (jK W) _ A.isLB hρ hp
    ⟨w, hw⟩ m m' N N' K (spMap io) d d').1 hd
  set i : W →+* K := io.comp (algebraMap W (FractionRing W)) with hi
  have hinj : Function.Injective i := io.injective.comp (IsFractionRing.injective W (FractionRing W))
  have ex : spMap io ≫ jK W = spMap i ≫ 𝟙 (Sp W) := by
    rw [Category.comp_id, hi, ← Spec.map_comp]; rfl
  rw [ex] at h₁
  obtain ⟨θ, pt, pt', hθ, hl, hl'⟩ := h₁
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_section_nonzero_uniformised_model_dvr W hW D A G hG U
  obtain ⟨r, hr⟩ := (isGenSec_iff θ).1 hθ (SecM.ofSec G (SecAt.pull G U.LG.L σ i))
  obtain ⟨u, rfl⟩ := (fnR (spMap i ≫ 𝟙 (Sp W))).surjective r
  have hP := GlobalTheory.T.theta_constants_integral_unit_member_uniformised_trait W hW D A G hG U σ hσ m N hm hm3 hmu K i pt _ hinj (thList_smul U.LG.isLB (a := u) hr hl)
  have hP' := GlobalTheory.T.theta_constants_integral_unit_member_uniformised_trait W hW D A G hG U σ hσ m' N' hm' hm3' hmu' K i pt' _ hinj
    (thList_smul U.LG.isLB (a := u) hr hl')
  have hu : u ≠ 0 := by
    obtain ⟨-, b, hb, -⟩ := hP
    exact left_ne_zero_of_mul hb
  refine ⟨u⁻¹, inv_ne_zero hu, ?_, ?_⟩
  · simpa only [div_inv_eq_mul, _root_.mul_comm] using hP
  · simpa only [div_inv_eq_mul, _root_.mul_comm] using hP'

end GlobalTheory.SiegTh.CmpUnif
end
end
end
