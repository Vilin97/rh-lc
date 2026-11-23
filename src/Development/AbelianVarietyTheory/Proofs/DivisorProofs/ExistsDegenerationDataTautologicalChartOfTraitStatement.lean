module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimAddRank
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLowerBaseOfTraitAbelianPartStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPulledBackPeriodsBasePeriodsConstFormStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRootsOfPeriods
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsMumfordFamOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordBundlePullbackGrpPullback
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
public import Development.AbelianVarietyTheory.Counterexamples.UniformisationSurvey.MapPowLeOfIsPullUnif
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFiniteCubeInduction
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkBaseChange
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.GeneratorPullback.PullAlong
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMinAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnifAlongFinite

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
open Formalism.L2.Pj

noncomputable section

namespace GlobalTheory.TraitExt


open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT GlobalTheory.ArcPull GlobalTheory.PullLinear in
theorem exists_pull_gen {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {I : Ideal R} {I' : Ideal R'}
    (hR : AdmBase R I) (hR' : AdmBase R' I') (g : R →+* R') (hg : Function.Injective g) (hI : I.map g ≤ I')
    {D : DegData R I} {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)}
    [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (U : Unif I D A G) :
    ∃ (D' : DegData R' I') (_ : IsPullDeg g D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R')))
      (U' : Unif I' D' A' ((Over.pullback (spMap g)).obj G)) (gA : A'.A.left ⟶ A.A.left)
      (πK : pullback ((Over.pullback (spMap g)).obj G).hom (jK R') ⟶ pullback G.hom (jK R)),
      IsGrpPullback A'.A A.A (spMap (fracMap hg)) gA ∧ LBIso A'.L (A.L.pull gA) ∧
      πK ≫ pullback.fst G.hom (jK R) =
        pullback.fst ((Over.pullback (spMap g)).obj G).hom (jK R') ≫ pullback.fst G.hom (spMap g) ∧
      U'.gen.hom.left ≫ gA = πK ≫ U.gen.hom.left := by
  have hP : PolBaseChangeSt := polBaseChange_holds
  have hU : UnifBaseChangeSt := GlobalTheory.UnifPullGuards.unifBaseChange_holds
  have hψ : PsiOnExistsSt := psiOnExists
  have sq : spMap (fracMap hg) ≫ jK R = jK R' ≫ spMap g := (fracMap_sq hg).symm.trans (Category.id_comp _)
  obtain ⟨A', gA, pA, dA, mA, tA⟩ := hP _ _ (spMap (fracMap hg)) A
  have gpA : IsGrpPullback A'.A A.A (spMap (fracMap hg)) gA := ⟨pA, fun T x y x₀ y₀ hx hy => by
    have e₁ : x₀ = Out.toBase pA.w x := Over.OverMorphism.ext hx
    have e₂ : y₀ = Out.toBase pA.w y := Over.OverMorphism.ext hy
    rw [e₁, e₂, ← mA]; rfl⟩
  have gpG := ThetaBaseChange.grp_generic U.toUnifPre
  have gp' : IsGrpPullback ((Over.pullback (jK R')).obj ((Over.pullback (specOf g)).obj G)) G (spMap (fracMap hg) ≫ jK R)
      (pullback.fst ((Over.pullback (specOf g)).obj G).hom (jK R') ≫ pullback.fst G.hom (spMap g)) :=
    ((isGrpPullback_pullback ((Over.pullback (specOf g)).obj G) (jK R')).comp
      (isGrpPullback_pullback G (spMap g))).congr sq.symm rfl
  obtain ⟨eA, mE, heA⟩ := grpPullback_iso gp' (gpA.comp gpG)
  have hgi : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have hbc : (Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g) =
      pullback.fst G.hom (spMap g) := Category.id_comp _
  have wA : LBIso (A'.L.pull eA.hom.left) (U.LG.L.pull (pullback.fst ((Over.pullback (specOf g)).obj G).hom (jK R') ≫
      (Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g))) := by
    refine LBIso.trans (pull_isLB A'.isLB _) (pull_isLB (pull_isLB A.isLB gA) eA.hom.left)
      (pull_isLB U.LG.isLB _)
      ((LBIso.symm tA).chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull A'.L _ _ rfl)
        (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (A.L.pull gA) _ _ rfl)) ?_
    refine LBIso.chartPull (h := eA.hom.left ≫ gA ≫ U.gen.inv.left)
      (chartPullLinComb A.L gA (fun _ => eA.hom.left) (fun _ => U.gen.hom.left) _ _ fun _ => ?_)
      (chartPullSame U.LG.L _ (fun _ => pullback.fst G.hom (jK R)) _ _ fun _ => ?_) U.ext
    · rw [Category.assoc, Category.assoc, hgi, Category.comp_id]
    · rw [hbc, ← heA]; simp only [Category.assoc]
  have he : eSec ((Over.pullback (specOf g)).obj G) ≫ (Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫
      pullback.fst G.hom (specOf g) = specOf g ≫ eSec G := by
    rw [hbc]; exact (cubeMapOf (isGrpPullback_pullback G (spMap g))).e_comm
  have hr : (rigPullOf (G := G) (G' := (Over.pullback (specOf g)).obj G) _ (specOf g) he U.LG.L U.LG.rig).IsGen :=
    LBxP.isGen_pullAlong U.LG.L _ (specOf g) (fun _ : PUnit => eSec G) (fun _ => 1)
      (fun _ => eSec ((Over.pullback (specOf g)).obj G)) (fun _ => he) U.LG.rig U.LG.rigGen
  let L' : RigLB ((Over.pullback (specOf g)).obj G) :=
    ⟨U.LG.L.pull ((Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g)),
      rigPullOf (G := G) (G' := (Over.pullback (specOf g)).obj G) _ (specOf g) he U.LG.L U.LG.rig,
      pull_isLB U.LG.isLB _, hr⟩
  obtain ⟨Wo, hWo, hψ⟩ := hψ R I hR D
  have hgen : (specOf g).base (genericPoint (Spec (CommRingCat.of R'))) ∈ Wo := by
    have : (specOf g).base (genericPoint (Spec (CommRingCat.of R'))) = genericPoint (Spec (CommRingCat.of R)) := by
      rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
      exact PrimeSpectrum.ext (Ideal.comap_bot_of_injective g hg)
    rw [this]; exact hWo
  have mR : IsMonHom (Iso.refl ((Over.pullback (specOf g)).obj G)).hom := by show IsMonHom (𝟙 _); infer_instance
  obtain ⟨D', hD, U', -, hU', -⟩ := hU R R' I I' hR hR' g hI D A G hG U Wo hψ hgen ((Over.pullback (specOf g)).obj G)
    (Iso.refl _) mR A' dA eA mE wA L' (idIso _) he (idIso_isGen L'.isLB) (fun p => hr p.1 p.2)
  refine ⟨D', hD, A', U', gA, eA.hom.left ≫ gA ≫ U.gen.inv.left, gpA, LBIso.symm tA, ?_, ?_⟩
  · simpa only [Category.assoc] using heA
  · rw [hU']; simp only [Category.assoc, hgi, Category.comp_id]

end GlobalTheory.TraitExt

namespace GlobalTheory.TraitExt

end GlobalTheory.TraitExt
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnifAlongPullTo

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT GlobalTheory.ArcPull GlobalTheory.PullLinear

noncomputable section

namespace GlobalTheory.TraitExt


open GlobalTheory.ArcPull in
theorem exists_unifAlong_pullTo : ∀ {g n : ℕ} (F : SFam g n (zetaAway n)) (T : GlobalTheory.Poinc.Trait F) (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂] (f : T.V →+* V₂), IsCN V₂ → IsDiscreteValuationRing V₂ → Function.Injective f → f.Finite → IsLocalHom f → ∃ (D' : DegData V₂ (maximalIdeal V₂)) (_ : IsPullDeg f T.D.toPre D'.toPre) (G' : Over (Sp V₂)) (_ : GrpObj G') (_ : IsCommMonObj G') (π : G'.left ⟶ T.G.left) (A' : PolAV (Sp (FractionRing V₂))) (U' : Unif (maximalIdeal V₂) D' A' G'), IsUnifAlong F T.y (T.U.gen.hom.left ≫ T.α) f π U' := by
  intro g n F T V₂ _ _ _ f hCN _ hinj hfin hloc
  obtain ⟨hN, hIC, hW, hC⟩ := hCN
  have hR : AdmBase T.V (maximalIdeal T.V) := ⟨inferInstance, inferInstance, inferInstance, T.complete⟩
  have hR' : AdmBase V₂ (maximalIdeal V₂) := ⟨hN, inferInstance, hIC, hW⟩
  have hI : (maximalIdeal T.V).map f ≤ maximalIdeal V₂ :=
    Ideal.map_le_iff_le_comap.2 fun a ha => map_nonunit f a ha
  obtain ⟨D', hD, A', U', gA, πK, gpA, tA, hK, hgen⟩ := exists_pull_gen hR hR' f hinj hI T.semi T.U
  obtain ⟨β₂, hβ₂, hΛ⟩ := GlobalTheory.Mum.lbIso_lam_pull_of_isGrpPullback _ _ _ T.A.A A'.A gA gpA
  have sq : spMap (fracMap hinj) ≫ jK T.V = jK V₂ ≫ spMap f :=
    (fracMap_sq hinj).symm.trans (Category.id_comp _)
  refine ⟨D', hD, (Over.pullback (spMap f)).obj T.G, inferInstance, inferInstance, pullback.fst T.G.hom (spMap f),
    A', U', ?_⟩
  refine ⟨isGrpPullback_pullback T.G (spMap f), spMap (fracMap hinj), πK, gA ≫ T.α, β₂ ≫ T.α₂, sq, hK,
    gpA.comp T.cart, isSquare_comp hβ₂ T.sq, hΛ T.A.L A'.L _ F.univ.P T.α₂ T.A.isLB A'.isLB F.univ.isLB tA T.lb, ?_⟩
  rw [← Category.assoc, hgen, Category.assoc]

end GlobalTheory.TraitExt
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegenerationDataTautologicalChartOfTrait

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChart

theorem exists_degFrom_of_trait : ∀ (g : ℕ), 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (T : GlobalTheory.Poinc.Trait F) (b : cycAway n →+* T.V), T.y ≫ F.s = jK T.V ≫ spMap b → ∃ (L : LowBase (zetaAway n) n) (m N : ℕ) (ε : Module.Basis (Fin m ⊕ Fin N) ℤ (balForms (id : ℤ → ℤ) (Fin L.T.r → ℤ))) (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (f : T.V →+* V') (κ : L.W →+* V') (s : Fin m ⊕ Fin N → V') (D' : DegData V' (maximalIdeal V')) (e : D'.toPre.X ≃+ (Fin L.T.r → ℤ)) (G' : Over (Sp V')) (_ : GrpObj G') (_ : IsCommMonObj G') (π : G'.left ⟶ T.G.left) (A' : PolAV (Sp (FractionRing V'))) (U' : Unif (maximalIdeal V') D' A' G'), L.h + L.T.r = g ∧ IsCone id φ (fun k => (ε (.inl k) : LinearMap.BilinForm ℤ (Fin L.T.r → ℤ))) ∧ (∀ x, x ≠ 0 → ∃ k, 0 < (ε (.inl k) : LinearMap.BilinForm ℤ (Fin L.T.r → ℤ)) x x) ∧ IsCN V' ∧ IsDiscreteValuationRing V' ∧ Function.Injective f ∧ f.Finite ∧ IsLocalHom f ∧ IsLocalHom κ ∧ κ.comp L.T.b = f.comp b ∧ (∀ k, s (.inl k) ∈ maximalIdeal V' ∧ s (.inl k) ≠ 0) ∧ (∀ k, IsUnit (s (.inr k))) ∧ IsUnifAlong F T.y (T.U.gen.hom.left ≫ T.α) f π U' ∧ DegFrom L.T κ s (fun k => (ε k : LinearMap.BilinForm ℤ (Fin L.T.r → ℤ))) n D'.toPre e := by
  intro g hg φ hφ n hn hodd F T b hb
  have hV : IsCN T.V := ⟨inferInstance, inferInstance, T.complete, inferInstance⟩
  let e₀ : (Fin (Module.finrank ℤ T.D.toPre.X) → ℤ) ≃+ T.D.toPre.X :=
    (Module.finBasis ℤ T.D.toPre.X).equivFun.symm.toAddEquiv
  have hc : ∀ a a', T.D.toPre.c (e₀ (a + a')) = T.D.toPre.c (e₀ a) * T.D.toPre.c (e₀ a') := fun a a' => by
    rw [map_add (f := _)]; exact T.D.toPre.c_add _ _
  obtain ⟨L, V₁, _, _, _, f₁, κ₁, e, hLh, hCN₁, hDVR₁, hi₁, hf₁, hl₁, hκ₁, hb₁, B', _, β', β'', β₂, β₂', p₁, p₂, s₁, s₂,
    lb, pts⟩ := GlobalTheory.T.exists_lower_base_of_trait_abelian_part n hn hodd T.V hV inferInstance b T.D.toPre.P _ (fun a => T.D.toPre.c (e₀ a)) hc
  have hr : L.T.r = Module.finrank ℤ T.D.toPre.X := by
    simpa using LinearEquiv.finrank_eq e.toIntLinearEquiv
  have hgen : L.h + L.T.r = g := by rw [hLh, hr]; exact GlobalTheory.Poinc.Trait.dim_add_rank (by omega) F T
  obtain ⟨q, hqs, hqa, hqp, hq⟩ := GlobalTheory.T.exists_pulledBack_periods_basePeriods_constForm n T.V T.D _ e₀ L V₁ f₁ κ₁ e B' β' β'' β₂ β₂' hV inferInstance hCN₁ hDVR₁ hi₁ hf₁
    hl₁ hκ₁ p₁ p₂ s₁ s₂ lb pts
  obtain ⟨m, N, ε, hcone, hdef, V₂, _, _, _, f₂, fK, s, hCN₂, hDVR₂, hi₂, hf₂, hl₂, hfK, hs₁, hs₂, hqs'⟩ :=
    GlobalTheory.PerRoot.exists_roots_of_periods g n φ hφ (by omega) V₁ hCN₁ hDVR₁ L.T.r (by omega) q hqs hqa hqp
  have hl : IsLocalHom (f₂.comp f₁) := RingHom.isLocalHom_comp f₂ f₁
  have hlκ : IsLocalHom (f₂.comp κ₁) := RingHom.isLocalHom_comp f₂ κ₁
  obtain ⟨D', hD, G', _, _, π, A', U', hU⟩ :=
    GlobalTheory.TraitExt.exists_unifAlong_pullTo F T V₂ (f₂.comp f₁) hCN₂ hDVR₂ (hi₂.comp hi₁) (hf₂.comp hf₁) hl
  refine ⟨L, m, N, ε, V₂, inferInstance, inferInstance, inferInstance, f₂.comp f₁, f₂.comp κ₁, s, D',
    hD.xe.trans (e₀.symm.trans e.symm), G', inferInstance, inferInstance, π, A', U', hgen, hcone, hdef, hCN₂, hDVR₂,
    hi₂.comp hi₁, hf₂.comp hf₁, hl, hlκ, ?_, hs₁, hs₂, hU, ?_⟩
  · rw [RingHom.comp_assoc, hb₁, ← RingHom.comp_assoc]
  · exact hq V₂ f₂ fK s (fun k => (ε k : LinearMap.BilinForm ℤ (Fin L.T.r → ℤ))) hCN₂ hi₂ hf₂ hl₂ hfK hqs' D' hD

end GlobalTheory.TChart
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegenerationDataTautologicalChartOfTraitStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_degeneration_data_tautologicalChart_of_trait : ∀ (g : ℕ), 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (T : GlobalTheory.Poinc.Trait F) (b : cycAway n →+* T.V), T.y ≫ F.s = jK T.V ≫ spMap b → ∃ (L : LowBase (zetaAway n) n) (m N : ℕ) (ε : Module.Basis (Fin m ⊕ Fin N) ℤ (balForms (id : ℤ → ℤ) (Fin L.T.r → ℤ))) (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (f : T.V →+* V') (κ : L.W →+* V') (s : Fin m ⊕ Fin N → V') (D' : DegData V' (maximalIdeal V')) (e : D'.toPre.X ≃+ (Fin L.T.r → ℤ)) (G' : Over (Sp V')) (_ : GrpObj G') (_ : IsCommMonObj G') (π : G'.left ⟶ T.G.left) (A' : PolAV (Sp (FractionRing V'))) (U' : Unif (maximalIdeal V') D' A' G'), L.h + L.T.r = g ∧ IsCone id φ (fun k => (ε (.inl k) : LinearMap.BilinForm ℤ (Fin L.T.r → ℤ))) ∧ (∀ x, x ≠ 0 → ∃ k, 0 < (ε (.inl k) : LinearMap.BilinForm ℤ (Fin L.T.r → ℤ)) x x) ∧ IsCN V' ∧ IsDiscreteValuationRing V' ∧ Function.Injective f ∧ f.Finite ∧ IsLocalHom f ∧ IsLocalHom κ ∧ κ.comp L.T.b = f.comp b ∧ (∀ k, s (.inl k) ∈ maximalIdeal V' ∧ s (.inl k) ≠ 0) ∧ (∀ k, IsUnit (s (.inr k))) ∧ IsUnifAlong F T.y (T.U.gen.hom.left ≫ T.α) f π U' ∧ DegFrom L.T κ s (fun k => (ε k : LinearMap.BilinForm ℤ (Fin L.T.r → ℤ))) n D'.toPre e := by
  first | exact @GlobalTheory.TChart.exists_degFrom_of_trait | exact GlobalTheory.TChart.exists_degFrom_of_trait | (intros; apply GlobalTheory.TChart.exists_degFrom_of_trait <;> assumption)
end
end
