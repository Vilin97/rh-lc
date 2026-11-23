module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfLocalOnBase
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianSchemeProperClosureDataBasicProperties
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianTorsionFiniteAndMulNSurjective
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLineBundleExtensionThetaSectionSemiAbelianStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRigidifiedCubicalSymmetricExtensionNormalB
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleIsoExtendOfNormalBaseStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyLawOfHasTestsOfIndep
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CoordOfHasWeight
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitExtIsGtOfTorusExtension
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDenseClosedPointsChartSplitting
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsSemiAbelianOfSplitAll
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitChartsTorusExtensionOverFieldStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WeightedProjectiveChartsSplitGenericPointStatement
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
import Mathlib.RingTheory.TotallySplit
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleSymmetryHypothesisBaseChange
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NatCastNeZeroOfIsUnit
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolPull
import Mathlib.Algebra.Order.Star.Int
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitAllAndIsSemiAbelian

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ.FibreSplit

theorem exists_residue_factor {K : Type} [Field K] {Z : Scheme.{0}} (s : Sp K ⟶ Z) [SurjectiveOnStalks s]
    (z : Z) (hz : s (IsLocalRing.closedPoint K) = z) :
    ∃ f : Sp (Z.residueField z) ⟶ Sp K, f ≫ s = Z.fromSpecResidueField z := by
  subst hz
  let ρ := Z.descResidueField (Scheme.stalkClosedPointTo s)
  have hs : Function.Surjective (Scheme.stalkClosedPointTo s).hom := by
    unfold Scheme.stalkClosedPointTo
    exact (ConcreteCategory.bijective_of_isIso (stalkClosedPointIso (.of K)).hom).2.comp (s.stalkMap_surjective _)
  have hρ : Function.Surjective ρ.hom := by
    have h := congrArg CommRingCat.Hom.hom (Z.residue_descResidueField (Scheme.stalkClosedPointTo s))
    rw [← h] at hs
    rw [CommRingCat.hom_comp, RingHom.coe_comp] at hs
    exact Function.Surjective.of_comp hs
  have : IsIso ρ := (ConcreteCategory.isIso_iff_bijective ρ).2 ⟨ρ.hom.injective, hρ⟩
  refine ⟨inv (Spec.map ρ), ?_⟩
  rw [IsIso.inv_comp_eq]
  exact (Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K Z s).symm

theorem exists_splitExt_of_split (K : Type) [Field K] (H : Over (Sp K)) [GrpObj H] [IsCommMonObj H] [Smooth H.hom]
    [IsSeparated H.hom] [QuasiCompact H.hom] (C : Charts H.left) (d : ℕ) (c : Fin d → C.Cl) (h : C.Split c) :
    ∃ E : SplitExt (Sp K), E.IsGt H := by
  obtain ⟨hc, i, hT⟩ := h
  obtain ⟨B, gB, q, hB, hq, hf, hs, ha, hk, -⟩ := GlobalTheory.T.splitCharts_torus_extension_over_field K H C d c i hc hT
  exact GlobalTheory.exists_splitExt_isGt_of_torusExtension K H ⟨{
    X := Fin d → ℤ, B := B, grpB := gB, isAbelian := hB, i := i, q := q, i_hom := hT.hom, q_hom := hq,
    q_flat := hf, q_surjective := hs, q_quasiCompact := inferInstance, isKernel := hk }⟩

theorem splitAll_and_isSemiAbelian : ∀ (C : Core) (L : C.Law), C.HasTests → C.HasCharts → letI := L.grp; letI := L.comm; SplitAll C.GG ∧ IsSemiAbelian C.GG := by
  intro C L hT hC
  let := L.grp
  let := L.comm
  obtain ⟨hsep, -, hqc, -⟩ := core_basic C
  have := L.smooth
  have hsm : Smooth C.GG.hom := SmoothOfRelativeDimension.smooth C.g _
  have h : SplitAll C.GG := by
    intro z
    obtain ⟨R, _, _, _, t, _, ht, Ch, d, c, Sg, hd, hS, -⟩ := DenseSplit.exists_dense_splitOn C L hT hC z
    have : Smooth ((Over.pullback t).obj C.GG).hom := inferInstanceAs (Smooth (pullback.snd C.GG.hom t))
    have : IsSeparated ((Over.pullback t).obj C.GG).hom := inferInstanceAs (IsSeparated (pullback.snd C.GG.hom t))
    have : QuasiCompact ((Over.pullback t).obj C.GG).hom := inferInstanceAs (QuasiCompact (pullback.snd C.GG.hom t))
    have : Smooth ((Over.pullback (Out.jK R)).obj ((Over.pullback t).obj C.GG)).hom :=
      inferInstanceAs (Smooth (pullback.snd ((Over.pullback t).obj C.GG).hom _))
    have : IsSeparated ((Over.pullback (Out.jK R)).obj ((Over.pullback t).obj C.GG)).hom :=
      inferInstanceAs (IsSeparated (pullback.snd ((Over.pullback t).obj C.GG).hom _))
    have : QuasiCompact ((Over.pullback (Out.jK R)).obj ((Over.pullback t).obj C.GG)).hom :=
      inferInstanceAs (QuasiCompact (pullback.snd ((Over.pullback t).obj C.GG).hom _))
    have : IsAffineHom (pullback.fst ((Over.pullback t).obj C.GG).hom (Out.jK R)) :=
      isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _).flip inferInstance
    obtain ⟨E, hE⟩ := exists_splitExt_of_split (FractionRing R) _ _ d _
      (GlobalTheory.T.weightedProjectiveCharts_split_generic_point R ((Over.pullback t).obj C.GG) Ch d c Sg hd hS)
    have : IsPreimmersion (Out.jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
    obtain ⟨f, hf⟩ := exists_residue_factor (Out.jK R ≫ t) z (by
      rw [← ht]
      refine (Scheme.Hom.comp_apply (Out.jK R) t _).trans (congrArg t (PrimeSpectrum.ext ?_))
      change Ideal.comap (algebraMap R (FractionRing R)) (IsLocalRing.maximalIdeal _) = ⊥
      rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.comap_bot_of_injective _ (IsFractionRing.injective R _)])
    have : IsMonHom (pullCompIso (Out.jK R) t C.GG).symm.hom :=
      inferInstanceAs (IsMonHom (pullCompIso (Out.jK R) t C.GG).inv)
    obtain ⟨D⟩ := isGt_of_iso (pullCompIso (Out.jK R) t C.GG).symm hE
    have : IsMonHom (pullCompIso f (Out.jK R ≫ t) C.GG).symm.hom :=
      inferInstanceAs (IsMonHom (pullCompIso f (Out.jK R ≫ t) C.GG).inv)
    have key : ∀ s : Sp (C.Z.residueField z) ⟶ C.Z, f ≫ Out.jK R ≫ t = s →
        ∃ E : SplitExt (Sp (C.Z.residueField z)), E.IsGt ((Over.pullback s).obj C.GG) := by
      rintro _ rfl
      exact ⟨_, isGt_of_iso (pullCompIso f (Out.jK R ≫ t) C.GG).symm (GtBaseChange.isGt_extBC f E _ D)⟩
    exact key _ hf
  exact ⟨h, (isSemiAbelian_of_splitAll C.Z C.GG h).1⟩

end GlobalTheory.ZJ.FibreSplit
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSemiAbelianSplitCubicalExtensionClosure

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ.Assembly

theorem exists_sec_of_lbIso_pull {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (hL : L.IsLB)
    (hL' : L'.IsLB) (H : LBIso L' (L.pull F)) (s : LB.Sec L) :
    ∃ s' : LB.Sec L', ∀ y : X', F y ∈ Out.nonzeroLocus s → y ∈ Out.nonzeroLocus s' := by
  obtain ⟨W, hW⟩ := H
  obtain ⟨s', hs'⟩ := sec_pull_down ((isGen_iff W).1 hW) hL hL' s
  refine ⟨s', fun y hy => ?_⟩
  obtain ⟨j, hj, u⟩ := (mem_nonzeroLocus _ _).1 hy
  obtain ⟨k, hk⟩ := exists_chart hL' y
  have e := hs' _ (𝟙 _) y j k hj hk
  rw [Category.id_comp, gs_stalkMap F y _ hj] at e
  refine (mem_nonzeroLocus _ _).2 ⟨k, hk, ?_⟩
  exact isUnit_of_mul_isUnit_right ((congrArg IsUnit e).mp (u.map (F.stalkMap y).hom))

theorem mulN_eq_pow' {S : Scheme.{0}} (G : Over S) [GrpObj G] (n : ℕ) : mulN G n = (𝟙 G) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, ← ih]; rfl

theorem mulN_comm_of_isGrpPullback {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G]
    [GrpObj G'] [IsCommMonObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (n : ℕ) :
    (mulN G' n).left ≫ φ = φ ≫ (mulN G n).left := by
  have e := congrArg (fun q => q.left) (map_pow (pushHom h G') (𝟙 G') n)
  have e₂ : pushHom h G' (𝟙 G') ≫ mulN G n = pushHom h G' (𝟙 G') ^ n := by
    rw [mulN_eq_pow', MonObj.comp_pow, Category.comp_id]
  rw [← e₂, ← mulN_eq_pow'] at e
  refine Eq.trans e ?_
  change (𝟙 _ ≫ φ) ≫ _ = _
  rw [Category.id_comp]

theorem exists_sec_fibres {H S : Scheme.{0}} (p : H ⟶ S) {L M : LB H} (hL : L.IsLB) (hM : M.IsLB) (z : S)
    (h₁ : ∃ N : S.Opens, z ∈ N ∧ LBIso (L.pull (p ⁻¹ᵁ N).ι) (M.pull (p ⁻¹ᵁ N).ι))
    (h₂ : ∃ (N : S.Opens) (σ : LB.Sec (M.pull (p ⁻¹ᵁ N).ι)), z ∈ N ∧
      ∀ z' ∈ N, ∃ x ∈ Out.nonzeroLocus σ, p ((p ⁻¹ᵁ N).ι x) = z') :
    ∃ (N : S.Opens) (σ : LB.Sec (L.pull (p ⁻¹ᵁ N).ι)), z ∈ N ∧
      ∀ z' ∈ N, ∃ x ∈ Out.nonzeroLocus σ, p ((p ⁻¹ᵁ N).ι x) = z' := by
  obtain ⟨N₁, hz₁, H₁⟩ := h₁
  obtain ⟨N₂, σ, hz₂, H₂⟩ := h₂
  have l₁ : p ⁻¹ᵁ (N₁ ⊓ N₂) ≤ p ⁻¹ᵁ N₁ := fun _ hx => hx.1
  have l₂ : p ⁻¹ᵁ (N₁ ⊓ N₂) ≤ p ⁻¹ᵁ N₂ := fun _ hx => hx.2
  have I : LBIso (L.pull (p ⁻¹ᵁ (N₁ ⊓ N₂)).ι) ((M.pull (p ⁻¹ᵁ N₂).ι).pull (H.homOfLE l₂)) :=
    H₁.chartPull (h := H.homOfLE l₁)
      (chartPullSame L _ _ _ _ fun _ => (H.homOfLE_ι l₁).symm)
      (chartPullLinComb M _ _ _ _ _ fun _ => (H.homOfLE_ι l₂).trans (H.homOfLE_ι l₁).symm)
  obtain ⟨σ', hσ'⟩ := exists_sec_of_lbIso_pull (pull_isLB hM _) (pull_isLB hL _) I σ
  refine ⟨N₁ ⊓ N₂, σ', ⟨hz₁, hz₂⟩, fun z' hz' => ?_⟩
  obtain ⟨x, hx, e⟩ := H₂ z' hz'.2
  have hm : x.1 ∈ p ⁻¹ᵁ (N₁ ⊓ N₂) := by
    change p x.1 ∈ N₁ ⊓ N₂
    exact (show p x.1 = z' from e) ▸ hz'
  refine ⟨⟨x.1, hm⟩, hσ' _ ?_, e⟩
  have : H.homOfLE l₂ ⟨x.1, hm⟩ = x := Subtype.ext (Scheme.homOfLE_apply l₂ _)
  rwa [this]

theorem exists_law_splitAll_cubical : Out.Laws → ∀ (C : Core) (T : C.Theta) (n : ℕ), C.HasTests → C.Indep → C.HasCharts → C.TorsSec n → T.Few n → ∃ L : C.Law, letI := L.grp; letI := L.comm; SplitAll C.GG ∧ IsSemiAbelian C.GG ∧ ∃ (PP : RigLB C.GG) (cub : CubicalStr C.GG PP) (m : CubeMap C.A C.GG), m.F = C.a ∧ m.e = C.U.ι ∧ m.IsPullCubical T.cub cub ∧ (T.L.IsSymmetric → PP.IsSymmetric) ∧ (∀ z : C.Z, ∃ (N : C.Z.Opens) (σ : LB.Sec (PP.L.pull (C.GG.hom ⁻¹ᵁ N).ι)), z ∈ N ∧ ∀ z' ∈ N, ∃ x ∈ Out.nonzeroLocus σ, C.GG.hom ((C.GG.hom ⁻¹ᵁ N).ι x) = z') ∧ ∀ z : C.Z, ∃ N : C.Z.Opens, z ∈ N ∧ LBIso (T.O₁.pull (C.GG.hom ⁻¹ᵁ N).ι) ((PP.L.pull (mulN C.GG T.m).left).pull (C.GG.hom ⁻¹ᵁ N).ι) := by
  intro hL C T n hT hI hC hS hF
  obtain ⟨L⟩ := Core.nonempty_law_of_hasTests_of_indep C hT hI
  refine ⟨L, ?_⟩
  letI := L.grp
  letI := L.comm
  obtain ⟨h₁, h₂⟩ := GlobalTheory.ZJ.FibreSplit.splitAll_and_isSemiAbelian C L hT hC
  obtain ⟨M, hM, hMa, hσ⟩ := GlobalTheory.T.exists_lineBundle_extension_thetaSection_semiAbelian hL.extend hL.mulN
    GlobalTheory.abelian_torsion_finite_and_mulN_surjective.2 C L T n h₂ hT hS hF
  obtain ⟨-, -, -, -, -, -, -, hcart, -, hN, -⟩ := GlobalTheory.ZJ.core_basic C
  have : Nonempty C.U.toScheme := C.ne.to_subtype
  have := h₂.smooth
  have := h₂.geomConnected
  have hgi : GeometricallyIntegral C.GG.hom := GlobalTheory.grpObj_geometricallyIntegral_of_smooth _ C.GG
  obtain ⟨PP, cub, m, hF, he, hp, hsym⟩ :=
    GlobalTheory.NormalCubeExt.exists_cubical_extension C.Z C.normal C.U.toScheme C.U.ι C.GG C.A C.a L.pull T.L T.cub M hM hMa
  have iso := GlobalTheory.T.lineBundleIso_extend_of_normal_base C.Z C.normal C.U.toScheme C.G.toScheme C.A.left C.U.ι C.GG.hom C.e C.a C.A.hom
    h₂.smooth hgi C.e_sec hcart
  have hw : LBIso T.L.L (PP.L.pull C.a) := by
    obtain ⟨w, hw, -⟩ := hp
    exact hF ▸ ⟨w, hw⟩
  refine ⟨h₁, h₂, PP, cub, m, hF, he, hp, hsym, fun z => ?_, fun z => ?_⟩
  · refine exists_sec_fibres C.GG.hom PP.isLB hM z ((iso PP.L M PP.isLB hM ?_).2 z) (hσ z)
    exact (LBIso.trans (pull_isLB hM _) T.L.isLB (pull_isLB PP.isLB _) hMa hw).symm
  · refine (iso T.O₁ (PP.L.pull (mulN C.GG T.m).left) T.isLB (pull_isLB PP.isLB _) ?_).2 z
    have i₁ : LBIso (T.L.L.pull (mulN C.A T.m).left) ((PP.L.pull (mulN C.GG T.m).left).pull C.a) :=
      hw.chartPull (h := (mulN C.A T.m).left) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ _ _ rfl)
        (chartPullLinComb PP.L _ _ _ _ _ fun _ => (mulN_comm_of_isGrpPullback L.pull T.m).symm)
    exact LBIso.trans (pull_isLB T.isLB _) (pull_isLB T.L.isLB _) (pull_isLB (pull_isLB PP.isLB _) _)
      (LBIso.symm ⟨T.w, T.w_gen⟩) i₁

end GlobalTheory.ZJ.Assembly
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSemiAbelianSplitCubicalExtensionClosureStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

theorem _root_.GlobalTheory.T.exists_semiAbelian_split_cubical_extension_closure : Out.Laws → ∀ (C : Core) (T : C.Theta) (n : ℕ), C.HasTests → C.Indep → C.HasCharts → C.TorsSec n → T.Few n → ∃ L : C.Law, letI := L.grp; letI := L.comm; SplitAll C.GG ∧ IsSemiAbelian C.GG ∧ ∃ (PP : RigLB C.GG) (cub : CubicalStr C.GG PP) (m : CubeMap C.A C.GG), m.F = C.a ∧ m.e = C.U.ι ∧ m.IsPullCubical T.cub cub ∧ (T.L.IsSymmetric → PP.IsSymmetric) ∧ (∀ z : C.Z, ∃ (N : C.Z.Opens) (σ : LB.Sec (PP.L.pull (C.GG.hom ⁻¹ᵁ N).ι)), z ∈ N ∧ ∀ z' ∈ N, ∃ x ∈ Out.nonzeroLocus σ, C.GG.hom ((C.GG.hom ⁻¹ᵁ N).ι x) = z') ∧ ∀ z : C.Z, ∃ N : C.Z.Opens, z ∈ N ∧ LBIso (T.O₁.pull (C.GG.hom ⁻¹ᵁ N).ι) ((PP.L.pull (mulN C.GG T.m).left).pull (C.GG.hom ⁻¹ᵁ N).ι) := by
  first | exact @GlobalTheory.ZJ.Assembly.exists_law_splitAll_cubical | exact GlobalTheory.ZJ.Assembly.exists_law_splitAll_cubical | (intros; apply GlobalTheory.ZJ.Assembly.exists_law_splitAll_cubical <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSemiAbelianGroupSchemeCubicalBundleClosure

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ClosureGroup

theorem exists_rescale {X' S' X S Y T : Scheme.{0}} (π : X' ⟶ S') (e' : S' ⟶ X') (he : e' ≫ π = 𝟙 S')
    (F : X' ⟶ X) (f : S' ⟶ S) (e : S ⟶ X) (hF : e' ≫ F = f ≫ e)
    (F₂ : X' ⟶ Y) (f₂ : S' ⟶ T) (e₂ : T ⟶ Y) (hF₂ : e' ≫ F₂ = f₂ ≫ e₂)
    {L : LB X} {M : LB Y} (hL : L.IsLB) (hM : M.IsLB) (a : LB.Gen (L.pull e)) (ha : a.IsGen)
    (b : LB.Gen (M.pull e₂)) (hb : b.IsGen) (H : LBIso (M.pull F₂) (L.pull F)) :
    ∃ w : LB.Iso (M.pull F₂) (L.pull F), w.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ S') (z : Z) (p : L.ι) (q : M.ι),
      F (e' (r z)) ∈ L.U p → F₂ (e' (r z)) ∈ M.U q →
      gm (r ≫ f) z ((L.pull e).U fun _ => p) (a.s fun _ => p) =
        gw w (r ≫ e') z p (fun _ => q) * gm (r ≫ f₂) z ((M.pull e₂).U fun _ => q) (b.s fun _ => q) := by
  obtain ⟨w, hw⟩ := H
  have pg := (isGen_iff w).1 hw
  have m₁ : ∀ (s : S') (p : L.ι), F (e' s) ∈ L.U p → f s ∈ (L.pull e).U fun _ => p := fun s p h =>
    mem_pull.2 ((congrArg (fun k => k s ∈ L.U p) hF).mp h)
  have m₂ : ∀ (s : S') (q : M.ι), F₂ (e' s) ∈ M.U q → f₂ s ∈ (M.pull e₂).U fun _ => q := fun s q h =>
    mem_pull.2 ((congrArg (fun k => k s ∈ M.U q) hF₂).mp h)
  let W : L.ι × M.ι → S'.Opens := fun j =>
    e' ⁻¹ᵁ ((L.pull F).U (fun _ => j.1) ⊓ (M.pull F₂).U (fun _ => j.2))
  have l₁ : ∀ j, W j ≤ f ⁻¹ᵁ (L.pull e).U fun _ => j.1 := fun j s hs => m₁ s _ (mem_pull.1 hs.1)
  have l₂ : ∀ j, W j ≤ f₂ ⁻¹ᵁ (M.pull e₂).U fun _ => j.2 := fun j s hs => m₂ s _ (mem_pull.1 hs.2)
  obtain ⟨u, hu⟩ : ∃ u : ∀ j, Γ(S', W j)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ S') (z : Z) j, r z ∈ W j →
      gm r z (W j) (u j) = gm (r ≫ f) z ((L.pull e).U fun _ => j.1) (a.s fun _ => j.1) *
        (gw w (r ≫ e') z j.1 (fun _ => j.2) * gm (r ≫ f₂) z ((M.pull e₂).U fun _ => j.2) (b.s fun _ => j.2))⁻¹ :=
    ⟨fun j => res (l₁ j) (pullU f _ (a.s fun _ => j.1)) *
      ((show Γ(S', W j)ˣ from pullU e' _ (w.s (fun _ => j.1, fun _ => j.2))) * res (l₂ j) (pullU f₂ _ (b.s fun _ => j.2)))⁻¹,
      fun Z r z j hz => (map_mul _ _ _).trans (congrArg₂ (· * ·)
        ((gm_res r z _ hz _).trans (gm_pull r f z _ (l₁ j hz) _))
        ((map_inv _ _).trans (congrArg (·⁻¹) ((map_mul _ _ _).trans (congrArg₂ (· * ·)
          (gm_pull r e' z _ hz _) ((gm_res r z _ hz _).trans (gm_pull r f₂ z _ (l₂ j hz) _)))))))⟩
  obtain ⟨c, hc⟩ := glue_unit ⊤ W (fun _ => le_top) (fun s _ => by
      obtain ⟨p, hp⟩ := exists_chart hL (F (e' s))
      obtain ⟨q, hq⟩ := exists_chart hM (F₂ (e' s))
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(p, q), mem_pull.2 hp, mem_pull.2 hq⟩) u (fun i j s hs => by
    have e₁ := gen_trans ha (𝟙 S' ≫ f) s (l₁ i hs.1) (l₁ j hs.2)
    have e₂' := gen_trans hb (𝟙 S' ≫ f₂) s (l₂ i hs.1) (l₂ j hs.2)
    have e₃ := pg _ (𝟙 S' ≫ e') s i.1 j.1 (fun _ => i.2) (fun _ => j.2) (mem_pull.1 hs.1.1) (mem_pull.1 hs.2.1)
      hs.1.2 hs.2.2
    rw [gm_pull_g M F₂ (𝟙 S' ≫ e') s _ _ hs.1.2 hs.2.2] at e₃
    simp only [trF, Fintype.prod_unique, zpow_one, Category.id_comp, ← hF, ← hF₂] at e₁ e₂' e₃
    rw [hu _ _ s i hs.1, hu _ _ s j hs.2]
    simp only [Category.id_comp]
    have alg : ∀ {V : Type} [CommGroup V] (A B x y z x' y' z' : V), x' = A * x → z' = B * z → y' = A * B⁻¹ * y →
        x' * (y' * z')⁻¹ = x * (y * z)⁻¹ := by
      rintro V _ A B x y z _ _ _ rfl rfl rfl
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    exact alg _ _ _ _ _ _ _ _ e₁ e₂' e₃)
  have hv : ∀ (Z : Scheme.{0}) (g : Z ⟶ X') (z : Z) (V : X'.Opens), g z ∈ V →
      gm g z V (res (le_top : V ≤ π ⁻¹ᵁ ⊤) (pullU π ⊤ c)) = gm (g ≫ π) z ⊤ c := fun Z g z V h =>
    (gm_res g z _ h _).trans (gm_pull g π z ⊤ trivial c)
  let w' : LB.Iso (M.pull F₂) (L.pull F) := ⟨fun j => res (le_top : _ ≤ π ⁻¹ᵁ ⊤) (pullU π ⊤ c) * w.s j⟩
  have hw' : ∀ (Z : Scheme.{0}) (g : Z ⟶ X') (z : Z) (p : L.ι) (q), F (g z) ∈ L.U p → g z ∈ (M.pull F₂).U q →
      gw w' g z p q = gm (g ≫ π) z ⊤ c * gw w g z p q := fun Z g z p q hp hq =>
    (map_mul _ _ _).trans (congrArg (· * _) (hv Z g z _ ⟨mem_pull.2 hp, hq⟩))
  refine ⟨w', (isGen_iff w').2 fun Z g z j j' k k' hj hj' hk hk' => ?_, fun Z r z p q hp hq => ?_⟩
  · rw [hw' Z g z j k hj hk, hw' Z g z j' k' hj' hk', pg Z g z j j' k k' hj hj' hk hk', mul_left_comm]
  · have hz : r z ∈ W (p, q) := ⟨mem_pull.2 hp, mem_pull.2 hq⟩
    have e₁ := (gm_res r z le_top hz c).symm.trans ((congrArg (gm r z _) (hc (p, q))).trans (hu Z r z (p, q) hz))
    rw [hw' Z (r ≫ e') z p _ hp (mem_pull.2 hq), Category.assoc, he, Category.comp_id, e₁, _root_.mul_assoc,
      inv_mul_cancel_right]

theorem isSymmetric_of_pull (hG : GlobalFnsSt) {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} [GrpObj A]
    [GrpObj A'] [IsCommMonObj A'] {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A f φ) (hA : IsAbelianScheme A)
    {L : LB A.left} (hL : L.IsLB) (hs : Sym A L) (L' : RigLB A') (H : LBIso L'.L (L.pull φ)) : L'.IsSymmetric := by
  obtain ⟨u, hu⟩ := exists_gen_neg_of_sym hG hA hL hs
  obtain ⟨w, hw⟩ := H
  obtain ⟨t, ht⟩ := gen_chartPull (chartPullSame L (K := Fin 2)
    (fun k => (![(GrpObj.inv : A' ⟶ A').left, 𝟙 A'.left] : Fin 2 → _) k ≫ φ) _ ![1, -1] φ fun k => by
      fin_cases k
      · exact PolBaseChange.inv_comm h
      · exact (Category.id_comp _).trans (Category.comp_id _).symm) u hu
  exact GlobalTheory.PrimNorm.isSymmetric_of_hasGen L' (exists_down ((isGen_iff w).1 hw) hL L'.isLB t ht)

theorem isQProjOver_ι {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R} (h : IsProjOver f) (U : X.Opens)
    [QuasiCompact U.ι] : IsQProjOver (U.ι ≫ f) := by
  obtain ⟨N, i, hi, e⟩ := h
  exact ⟨N, U.ι ≫ i, inferInstance, inferInstance, by rw [Category.assoc, e]⟩

theorem valF_eq_mul_of_gm {K : Type} [Field K] {X₁ X₂ X₃ : Scheme.{0}} {x₁ : Sp K ⟶ X₁} {x₂ : Sp K ⟶ X₂}
    {x₃ : Sp K ⟶ X₃} {U₁ : X₁.Opens} {U₂ : X₂.Opens} {U₃ : X₃.Opens} (z : Sp K) (h₁ : x₁ z ∈ U₁) (h₂ : x₂ z ∈ U₂)
    (h₃ : x₃ z ∈ U₃) {u₁ : Γ(X₁, U₁)ˣ} {u₂ : Γ(X₂, U₂)ˣ} {u₃ : Γ(X₃, U₃)ˣ}
    (e : gm x₁ z U₁ u₁ = gm x₂ z U₂ u₂ * gm x₃ z U₃ u₃) :
    valF x₁ U₁ u₁.val = valF x₂ U₂ u₂.val * valF x₃ U₃ u₃.val :=
  (toStk z).injective (by
    rw [map_mul, toStk_valF x₁ U₁ z h₁, toStk_valF x₂ U₂ z h₂, toStk_valF x₃ U₃ z h₃, e, Units.val_mul])

theorem exists_pre : Laws → Laws2 → ThmUSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Q : Clos ρ M U₀ EE) (ex : Q.Ext), S.Big → ex.core.HasTests → ex.core.Indep → ex.core.HasCharts → ex.core.TorsSec (S.r * S.N) → (∃ T : ex.core.Theta, LBIso T.L.L (ρ.P.L.pull (pullback.fst ρ.P.A.hom Q.u₀))) → ∃ Z : ZHPre ρ M U₀, (∃ e : Z.G.left ≅ Q.G.toScheme, e.hom ≫ Q.G.ι ≫ Q.P.hom = Z.G.hom ∧ Z.u₀ = Q.u₀ ∧ HEq (Z.φ ≫ e.hom) ex.a) ∧ Z.LocTheta ∧ Nonempty ex.core.Law := by
  intro hL hL2 hU o Ω _ _ _ _ S ρ M U₀ EE Q ex hbig htest hind hch htors ⟨T, hT⟩
  have hcomm : IsCommMonObj ρ.P.A := ρ.P.isAb.comm
  have gp : IsGrpPullback ex.core.A ρ.P.A Q.u₀ (pullback.fst ρ.P.A.hom Q.u₀) := isGrpPullback_pullback ρ.P.A Q.u₀
  obtain ⟨-, hamp, hK⟩ := GlobalTheory.pol_pull _ _ _ _ _ _ _ _ ρ.P.isLB T.L.isLB ρ.P.isAb gp hT
  have hsym : T.L.IsSymmetric := isSymmetric_of_pull hL.globalFns gp ρ.P.isAb ρ.P.isLB ρ.P.sym T.L hT
  have hS := GlobalTheory.SymBaseChange.hypS_baseChange _ _ _ _ _ _ _ _ ρ.P.isLB T.L.isLB gp hT ρ.hypS
  have hN : 4 ≤ S.N := by
    have h2 : 2 ≤ ρ.n ^ ρ.k := ρ.n_prime.two_le.trans (Nat.le_self_pow (by have := ρ.two_le; omega) _)
    rw [ρ.N_eq]
    nlinarith
  have hunit : IsUnit ((S.r * S.N : ℕ) : Γ(ex.core.Z, ⊤)) := by
    have h := S.unit.map (M.s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom)
    rw [map_natCast] at h
    exact h
  have hfew : T.Few (S.r * S.N) := GlobalTheory.ZJ.theta_few hU hL hL2 ex.core T (hamp ρ.P.ample) (hK ρ.P.ktriv) hsym hS S.N _
    hN hunit (hbig.2.2.trans_le (Nat.le_self_pow two_ne_zero _))
  obtain ⟨law, hmain⟩ := GlobalTheory.T.exists_semiAbelian_split_cubical_extension_closure hL ex.core T _ htest hind hch htors hfew
  let _ := law.grp
  let _ := law.comm
  obtain ⟨hsplit, hsemi, PP, cub, m, hF, he, hpull, hsym', hloc, -⟩ := hmain
  have hiso : LBIso T.L.L (PP.L.pull ex.core.a) := by
    obtain ⟨w, hw, -⟩ := hpull
    rw [← hF]
    exact ⟨w, hw⟩
  have e₁ := PolBaseChange.eSec_comm gp
  have e₂ := PolBaseChange.eSec_comm law.pull
  have hs : eSec ex.core.A ≫ ex.core.A.hom = 𝟙 _ := Over.w η[ex.core.A]
  have hsP : eSec ρ.P.A ≫ ρ.P.A.hom = 𝟙 _ := Over.w η[ρ.P.A]
  have hsG : eSec ex.core.GG ≫ ex.core.GG.hom = 𝟙 _ := Over.w η[ex.core.GG]
  obtain ⟨w, hw, hv⟩ := exists_rescale ex.core.A.hom (eSec ex.core.A) hs _ _ _ e₁ _ _ _ e₂ ρ.P.isLB PP.isLB ρ.rig
    ρ.rig_gen PP.rig PP.rigGen (LBIso.trans (pull_isLB PP.isLB _) T.L.isLB (pull_isLB ρ.P.isLB _) hiso.symm hT)
  have hqc : QuasiCompact (Q.G.ι ≫ Q.P.hom) := (GlobalTheory.ZJ.core_basic ex.core).2.2.1
  have hpr := Q.proper
  have hqc' : QuasiCompact Q.G.ι := QuasiCompact.of_comp _ Q.P.hom
  refine ⟨{ u₀ := Q.u₀
            u₀_gen := Q.u₀_pt
            G := ex.core.GG
            grp := law.grp
            comm := law.comm
            semi := hsemi
            dim := law.smooth
            qproj := by
              have h := isQProjOver_ι Q.proj Q.G
              rw [← Category.assoc] at h
              exact h
            φ := ex.a
            cart := law.pull
            L := PP
            cub := cub
            sym := hsym' hsym
            w := w
            w_gen := hw
            w_rig := ?_
            split := hsplit }, ⟨Iso.refl _, Category.id_comp _, rfl, heq_of_eq (Category.comp_id _)⟩, hloc, ⟨law⟩⟩
  intro K _ g x y jP jL hx hy hP hL'
  let r : Sp K ⟶ U₀.toScheme := g ≫ pullback.snd ρ.P.A.hom Q.u₀
  have ry : r ≫ Q.u₀ = y := by
    have h := congrArg (· ≫ ρ.P.A.hom) hy
    simp only [Category.assoc] at h
    rw [pullback.condition] at h
    exact (Category.assoc _ _ _).trans (h.trans ((congrArg (y ≫ ·) hsP).trans (Category.comp_id _)))
  have rx : r ≫ U₀.ι = x := by
    have h := congrArg (· ≫ ex.core.GG.hom) hx
    exact (Category.assoc _ _ _).trans ((congrArg (g ≫ ·) law.pull.1.w.symm).trans ((Category.assoc _ _ _).symm.trans
      (h.trans ((Category.assoc _ _ _).trans ((congrArg (x ≫ ·) hsG).trans (Category.comp_id _))))))
  have rg : r ≫ eSec ex.core.A = g := by
    apply pullback.hom_ext
    · exact (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) e₁).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ eSec ρ.P.A) ry).trans hy.symm)))
    · exact (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) hs).trans (Category.comp_id _))
  let z : Sp K := IsLocalRing.closedPoint K
  have mP : pullback.fst ρ.P.A.hom Q.u₀ (g z) ∈ ρ.P.L.U jP := hP ⟨z, rfl⟩
  have mL : ex.a (g z) ∈ PP.L.U jL := hL' ⟨z, rfl⟩
  have key := hv _ r z jP jL ((congrArg (fun k => pullback.fst ρ.P.A.hom Q.u₀ (k z) ∈ ρ.P.L.U jP) rg).mpr mP)
    ((congrArg (fun k => ex.a (k z) ∈ PP.L.U jL) rg).mpr mL)
  erw [ry, rx, rg] at key
  exact valF_eq_mul_of_gm z (mem_pull.2 ((congrArg (fun k => k z ∈ ρ.P.L.U jP) hy).mp mP))
    (show g z ∈ (ρ.P.L.pull (pullback.fst ρ.P.A.hom Q.u₀)).U (fun _ => jP) ⊓ (PP.L.pull ex.a).U (fun _ => jL) from
      ⟨mem_pull.2 mP, mem_pull.2 mL⟩) (mem_pull.2 ((congrArg (fun k => k z ∈ PP.L.U jL) hx).mp mL)) key

end GlobalTheory.ClosureGroup
end
end
end
