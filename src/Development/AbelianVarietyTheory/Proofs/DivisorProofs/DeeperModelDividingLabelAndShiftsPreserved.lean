module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCentredPureExtensionTowerMemberStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisTowerBaseChangeThetaMemberStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
public import Development.AbelianVarietyTheory.Definitions.Degenerations.NormNatCastPadicAlgClOfCoprime
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SemistableReductionPpavPadicField
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaConstantBoundedByShortestVector
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSystemHasTestsOfRealPoint
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UnitThetaConstantsGenerateIntegralTorsion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClassicalPointCentredClosedPointArithmetic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonemptyOpenThetaRingRegularStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformisationExistenceAndTorsionStatements
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
import Mathlib.Tactic.Basify
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
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupDividingLabelPersistsDeeperLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsFrameTwoLevels
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjBySmoothIsProperGeometricallyIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelPullbackIdCompCancel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfFramedPointLiesOverTorusExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueEqAdicSumAtImageOfZeroPair
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionPointLiesOverAfterFieldExtensionStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionIdentificationWithPairing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemDividingLabelsIffClassZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberExistsIntegralTermsUnitShiftStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDivTorsion

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.GSep

theorem exists_div_torsion : ∀ (X₁ : GlobalTheory.GSep.GSet) (z : X₁.M.Z) (k : ℕ), 2 ≤ k → k ∣ X₁.S.r * X₁.S.N →
    ∃ a : X₁.S.Gam, k • a = 0 ∧ X₁.M.Div X₁.S.th a z := by
  intro X z₀ k hk hd
  haveI := X.M.qc
  haveI : CompactSpace X.M.Z := QuasiCompact.compactSpace_of_compactSpace X.M.s
  obtain ⟨z, hz', hcl⟩ := (isClosed_closure (s := {z₀})).exists_closed_singleton ⟨z₀, subset_closure rfl⟩
  have hsp : z₀ ⤳ z := specializes_iff_mem_closure.2 hz'
  obtain ⟨U, hne, hU⟩ := GlobalTheory.T.exists_nonempty_open_thetaRing_regular X
  obtain ⟨p, _, y, hy, hyU⟩ := exists_cen_main _ _ X.M z hcl U hne
  obtain ⟨hL, hL2⟩ := GlobalTheory.abelianSchemeLaws_all
  obtain ⟨hTU, hUT⟩ := GlobalTheory.ZH.thmU_and_uTors
  have hle : X.S.R ≤ X.M.O ((gPt p ≫ y) (closedPoint (PadicAlgCl p))) := hU _ (hyU ⟨_, rfl⟩)
  have hsw : ∀ w, (gPt p ≫ y) w ⤳ (gPt p ≫ y) (closedPoint (PadicAlgCl p)) := fun w => by
    rw [Subsingleton.elim w (closedPoint (PadicAlgCl p))]
  let y₀ : X.S.R →+* PadicAlgCl p :=
    (RatModel.valHomOf (gPt p ≫ y) _ hsw).comp (Subalgebra.inclusion hle).toRingHom
  have hy₀ : ∀ a : X.S.R, y₀ a = X.M.val (gPt p ≫ y) a := fun _ => rfl
  have hint : ∀ a : X.o₁, ‖y₀ (algebraMap X.o₁ X.S.R a)‖ ≤ 1 := fun a => by
    rw [hy₀]
    exact RatModel.norm_val_le_one hy ((X.M.O z).algebraMap_mem a)
  obtain ⟨u, l, τ, hτ, -⟩ :=
    (hasTests_of_real GlobalTheory.SS.semistableReductionSt hTU hL hL2 hUT X.o₁ X.Ω₁ X.S X.ρ).2 p y₀ ∅ hint
  have hq : ∀ w, 0 ≤ l.q w := fun w => by
    obtain ⟨e, he, -⟩ := hτ
    have h := τ.q_nonneg (e.symm w)
    rwa [he, AddEquiv.apply_symm_apply] at h
  obtain ⟨sc, h0, h₁, -, h₃⟩ := TestVal.exists_scale hL hL2 u l hint
  have hδ := (GlobalTheory.UnitTheta.closure_unit_theta hL hL2 hUT _ _ _ X.ρ p y₀ u l hint).1
  have hle' : ∀ a, ‖y₀ ⟨X.S.th a, X.S.th_mem a⟩‖ ≤ sc := fun a => by
    obtain ⟨w, -, hw⟩ := h₁ a
    exact hw.trans (mul_le_of_le_one_right h0 (Real.exp_le_one_iff.2 (neg_nonpos.2 (div_nonneg (hq w) (by positivity)))))
  have hsc : 0 < sc := hδ.trans_le (Real.iSup_le hle' h0)
  obtain ⟨a, -, ha, hn⟩ := h₃ k hk hd 0 (zero_mem _)
  refine ⟨a, by simpa using ha, RatModel.Div.of_specializes ?_ hsp⟩
  obtain ⟨d, hdv⟩ := X.div z
  refine (hdv.div_iff_isUnit a).2 ((RatModel.norm_val_eq_one_iff hy (hdv.2 a)).1 ?_)
  have hs := RatModel.gPt_specializes hy
  have e : ‖y₀ ⟨X.S.th a, X.S.th_mem a⟩‖ =
      ‖y₀ ⟨X.S.th d, X.S.th_mem d⟩‖ * ‖X.M.val (gPt p ≫ y) (X.S.th a / X.S.th d)‖ := by
    rw [hy₀, hy₀, ← norm_mul, ← RatModel.val_mul hsw (hle (X.S.th_mem d))
      (RatModel.O_le_of_specializes (hs _) (hdv.2 a))]
    congr 2
    have := hdv.1
    field_simp
  have b₁ := RatModel.norm_val_le_one hy (hdv.2 a)
  have b₂ := hle' d
  refine le_antisymm b₁ (not_lt.1 fun hlt => ?_)
  have := mul_le_mul_of_nonneg_right b₂ (norm_nonneg (X.M.val (gPt p ≫ y) (X.S.th a / X.S.th d)))
  nlinarith

end GlobalTheory.GSep
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisTowerDividingLabelStaysDividing

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.GSep.DeepDivG

variable {I : Type} {X₁ : GSet} {z₁ : X₁.M.Z} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} {x₀ : X₁.S.Gam}
  {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
  {X : Type} [AddCommGroup X] {t : X → V} {δ : I → X → X}

end GlobalTheory.GSep.DeepDivG

namespace GlobalTheory.GSep.DeepDivG

theorem tower_same {I : Type} {X₁ : GlobalTheory.GSep.GSet} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (𝔗 : GlobalTheory.GSep.Tower X₁ act) :
    GlobalTheory.Poinc.Same X₁.ρ (fun _ => 𝟙 _) 𝔗.X₂.ρ (fun _ => 𝟙 _) 𝔗.lam (algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁) := by
  let f₂ : Sp 𝔗.X₂.Ω₁ ⟶ Sp 𝔗.X₂.S.R := spMap 𝔗.X₂.S.R.val.toRingHom
  let polPull {S S' : Scheme.{0}} (P : PolAV S) (f : S' ⟶ S) : PolAV S' := by
    exact {
      A := (Over.pullback f).obj P.A,
      isAb := TLinPf.isAb_pullback f P.A P.isAb,
      g := P.g,
      smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
        (isGrpPullback_pullback P.A f).1 P.smoothDim,
      L := P.L.pull (pullback.fst P.A.hom f),
      isLB := LB.isLB_pull P.isLB _,
      rigid := PolBaseChange.rigidified_pull (isGrpPullback_pullback P.A f) P.rigid,
      sym := PolBaseChange.sym_pull (isGrpPullback_pullback P.A f) P.sym,
      ample := by
        haveI := P.isAb.proper
        exact AmpleBaseChange.relAmple_of_isPullback P.isLB P.ample (IsPullback.of_hasPullback P.A.hom f)
      ktriv := by
        obtain ⟨w, hw⟩ := PolBaseChange.lbIso_refl (LB.isLB_pull P.isLB (pullback.fst P.A.hom f))
        exact kTriv_pull (isGrpPullback_pullback P.A f) P.isLB (LB.isLB_pull P.isLB _) ((isGen_iff w).1 hw) P.ktriv } 
  let P₀ := polPull 𝔗.X₂.ρ.P f₂
  let a' : P₀.A.left ⟶ 𝔗.X₂.ρ.P.A.left := pullback.fst 𝔗.X₂.ρ.P.A.hom f₂
  have hring : (algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁).comp X₁.S.R.val.toRingHom = 𝔗.X₂.S.R.val.toRingHom.comp 𝔗.om := by
    ext x; exact (𝔗.om_eq x).symm
  have hsp : spMap ((algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁).comp X₁.S.R.val.toRingHom) = f₂ ≫ spMap 𝔗.om := by
    rw [hring]; exact Spec.map_comp (CommRingCat.ofHom 𝔗.om) (CommRingCat.ofHom 𝔗.X₂.S.R.val.toRingHom)
  have ha' : IsGrpPullback P₀.A 𝔗.X₂.ρ.P.A f₂ a' := isGrpPullback_pullback _ _
  have hr : LBIso P₀.L (𝔗.X₂.ρ.P.L.pull a') := ⟨idIso _, idIso_isGen P₀.isLB⟩
  refine ⟨P₀, a' ≫ 𝔗.φ, a', fun _ => 𝟙 _, ?_, ha', ?_, hr, ?_, ?_⟩
  · exact (ha'.comp 𝔗.cart).congr hsp.symm rfl
  · exact LBIso.trans P₀.isLB (pull_isLB 𝔗.X₂.ρ.P.isLB _) (pull_isLB X₁.ρ.P.isLB _) hr (lbIso_pull_comp 𝔗.lb a')
  · intro E
    exact ⟨by simp, by simp⟩
  · intro x
    have hc : (f₂ ≫ (𝔗.X₂.ρ.pt (𝔗.lam x)).left) ≫ 𝔗.X₂.ρ.P.A.hom = 𝟙 _ ≫ f₂ := by
      rw [Category.assoc, Over.w (𝔗.X₂.ρ.pt (𝔗.lam x))]
      simp [baseOver]
    refine ⟨pullback.lift (f₂ ≫ (𝔗.X₂.ρ.pt (𝔗.lam x)).left) (𝟙 _) hc, ?_, ?_⟩
    · have hw : pullback.lift (f₂ ≫ (𝔗.X₂.ρ.pt (𝔗.lam x)).left) (𝟙 _) hc ≫ a' = f₂ ≫ (𝔗.X₂.ρ.pt (𝔗.lam x)).left :=
        pullback.lift_fst _ _ _
      have h3 : (f₂ ≫ (𝔗.X₂.ρ.pt (𝔗.lam x)).left) ≫ 𝔗.φ =
          spMap ((algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁).comp X₁.S.R.val.toRingHom) ≫ (X₁.ρ.pt x).left := by
        rw [Category.assoc, 𝔗.lam_pt, hsp, Category.assoc]
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ 𝔗.φ) hw).trans h3)
    · exact pullback.lift_fst _ _ _

end GlobalTheory.GSep.DeepDivG


open GlobalTheory.GSep.DeepDivG in
theorem GlobalTheory.GSep.DeepDivG.div_lam : (∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), GlobalTheory.GSep.IsAct X₁ act → (∀ m : ℕ, m ≠ 0 → IsUnit (m : X₁.M.Z.presheaf.stalk z₁)) → ∀ (𝔗 : GlobalTheory.GSep.Tower X₁ act) (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ → ∀ x₀ : X₁.S.Gam, X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ), 𝔗.X₂.M.Div 𝔗.X₂.S.th (𝔗.lam x₀) z₂) := by
  intro I X₁ z₁ act hact hunit 𝔗 z₂ hz₂ x₀ hx V _ _ _ ev X _ t δ _
  have hk : 0 < X₁.S.r * X₁.S.N := Nat.mul_pos X₁.S.r_pos (by have := X₁.S.N_ge; omega)
  have hdvd : X₁.S.r * X₁.S.N ∣ 𝔗.X₂.S.r * 𝔗.X₂.S.N := ⟨𝔗.d, 𝔗.lev⟩
  obtain ⟨a, ha, hdv⟩ := GlobalTheory.GSep.exists_div_torsion 𝔗.X₂ z₂ _ (X₁.S.N_ge.trans (Nat.le_mul_of_pos_left _ X₁.S.r_pos)) hdvd
  have hL : 0 < 𝔗.X₂.S.r * 𝔗.X₂.S.N := Nat.mul_pos 𝔗.X₂.S.r_pos (by have := 𝔗.X₂.S.N_ge; omega)
  choose x hxa using fun s => DivDeep.exists_eq_smul_of_smul_eq_zero hL hdvd (a s) (congrFun ha s)
  have hd : 𝔗.X₂.S.r * 𝔗.X₂.S.N / (X₁.S.r * X₁.S.N) = 𝔗.d := by
    rw [𝔗.lev]; exact Nat.mul_div_cancel_left _ hk
  rw [hd] at hxa
  obtain ⟨b, hb⟩ := 𝔗.lam_range x
  obtain rfl : 𝔗.lam b = a := hb.trans (funext hxa)
  obtain ⟨k, hk, e⟩ := DivDeep.same_ratio (GlobalTheory.GSep.DeepDivG.tower_same 𝔗) x₀ b
  set φ := algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁
  have h₁ : φ (X₁.S.th x₀) ≠ 0 := (map_ne_zero φ).2 hx.1
  have h₂ := hdv.1
  have h₃ : 𝔗.X₂.S.th (𝔗.lam x₀) * φ (X₁.S.th b) ≠ 0 := fun h => by
    rw [h, zero_pow hk.ne'] at e
    exact pow_ne_zero k (mul_ne_zero h₂ h₁) e.symm
  have h₄ := left_ne_zero_of_mul h₃
  have h₅ := right_ne_zero_of_mul h₃
  have hN : IsIntegrallyClosed (𝔗.X₂.M.O z₂) := RatModel.isIntegrallyClosed_O (fun z => by
    haveI := 𝔗.X₂.normal
    exact ⟨𝔗.X₂.normal.isDomain_stalk z, GlobalTheory.IsNormalScheme.isIntegrallyClosed_stalk z⟩) z₂
  have m₁ : 𝔗.X₂.S.th (𝔗.lam b) * φ (X₁.S.th x₀) / (𝔗.X₂.S.th (𝔗.lam x₀) * φ (X₁.S.th b)) ∈ 𝔗.X₂.M.O z₂ :=
    DivDeep.root_mem_O hN hk (by rw [div_pow, e, div_self (pow_ne_zero k (mul_ne_zero h₂ h₁))])
  have m₂ : φ (X₁.S.th b / X₁.S.th x₀) ∈ 𝔗.X₂.M.O z₂ := by
    obtain ⟨U, f, hU, hf⟩ := hx.2 b
    refine ⟨𝔗.p ⁻¹ᵁ U, 𝔗.p.app U f, show 𝔗.p z₂ ∈ U from hz₂ ▸ hU, ?_⟩
    refine (GlobalTheory.Points.valR_comp 𝔗.X₂.M.pt 𝔗.p U f).symm.trans ?_
    rw [𝔗.p_pt, ← hf]
    exact GlobalTheory.Points.valR_spMap_comp _ X₁.M.pt U (X₁.M.top_le_preimage_pt ⟨_, hU⟩) f
  refine ⟨h₄, fun j => ?_⟩
  have := mul_mem (hdv.2 j) (mul_mem m₁ m₂)
  convert this using 1
  rw [map_div₀]
  field_simp
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisTowerDividingLabelStaysDividingStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.galoisTower_dividing_label_stays_dividing : (∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), GlobalTheory.GSep.IsAct X₁ act → (∀ m : ℕ, m ≠ 0 → IsUnit (m : X₁.M.Z.presheaf.stalk z₁)) → ∀ (𝔗 : GlobalTheory.GSep.Tower X₁ act) (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ → ∀ x₀ : X₁.S.Gam, X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ), 𝔗.X₂.M.Div 𝔗.X₂.S.th (𝔗.lam x₀) z₂) := by
  first | exact @GlobalTheory.GSep.DeepDivG.div_lam | exact GlobalTheory.GSep.DeepDivG.div_lam | (intros; apply GlobalTheory.GSep.DeepDivG.div_lam <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeClassZeroOfMemberTerms

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.GSep.TermsLabel

theorem yy_zero_of_terms : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam) (T : X → C → V), 𝔪.Terms x₀ lab T → ∀ c, 𝔪.YY (lab c) 0 := by
  intro I X₁ z₁ act x₀ V _ _ _ ev X _ t δ 𝔪 C lab T hT c
  obtain ⟨x, fr, th, w₀, s, g', w, hx, hfr, -, hw₀, -, hg, -⟩ := hT
  haveI : CharZero V := 𝔪.cn.2.2.2
  have hL : GlobalTheory.UT.LL := GlobalTheory.firstFiveLaws
  have hA : AdmBase V (maximalIdeal V) := ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, 𝔪.cn.2.2.1⟩
  have hB := 𝔪.D.tau_bimult
  have hk : 1 ≤ X₁.S.r * X₁.S.N := by
    have := X₁.S.r_pos; have := X₁.S.N_ge
    exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  obtain ⟨⟨o, ho₁, ho₂⟩, hwc, hov⟩ := hg c
  letI := GlobalTheory.TorusExt.gtGroup 𝔪.D.toPre (FractionRing V)
  letI := GlobalTheory.TorusExt.gtGroup 𝔪.D.toPre (AlgebraicClosure (FractionRing V))
  have hkg : (X₁.S.r * X₁.S.N) • g' c = 0 :=
    ((GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).1 ho₁).symm.trans ((GlobalTheory.TorusExt.isZero_iff_eq _).1 ho₂)
  set gb := GlobalTheory.TorusExt.gtExt 𝔪.D.toPre (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)))
    (RingHom.comp_id _) (g' c) with hgb
  have hkgb : (X₁.S.r * X₁.S.N) • gb = 0 := by
    rw [hgb, ← map_nsmul, hkg, map_zero]

  have hi : GtPtF.IsIota 0 (0 : GtPtF 𝔪.D.toPre (AlgebraicClosure (FractionRing V))) := by
    have hz := (GlobalTheory.TorusExt.isZero_iff_eq (0 : GtPtF 𝔪.D.toPre (AlgebraicClosure (FractionRing V)))).2 rfl
    obtain ⟨hb, hv⟩ := (GlobalTheory.TorusExt.isZero_iff_val _).1 hz
    refine (GlobalTheory.TorusExt.isIota_iff_val 0 _).2 ⟨hb.trans (cPoint_zero _).symm, fun χ y J hJ => ?_⟩
    have C : IsCub (DVR.th 𝔪.D.toPre (T := TF (R := V) (AlgebraicClosure (FractionRing V))) y J) := isCub_cubV 𝔪.D.toPre.cub hJ
    have tt := tau_mul (𝟙 (TF (R := V) (AlgebraicClosure (FractionRing V)))) hJ hB 0 0 χ
    rw [add_zero, cPoint_zero, C.face, _root_.mul_one] at tt
    exact (hv χ y J hJ).trans (mul_eq_left.1 tt.symm).symm
  let p : QkPt 𝔪.D.toPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) :=
    ⟨0, gb, 0, (GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).2 hkgb.symm, hi⟩
  let xb : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ 𝔪.A.A :=
    GlobalTheory.TorsionExt.fieldMap (FractionRing V) (AlgebraicClosure (FractionRing V)) ≫ x (lab c)
  obtain ⟨wb, frb, hwb, hfrb, hlb⟩ := GlobalTheory.T.torusExtension_point_liesOver_after_field_extension V _ hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U (AlgebraicClosure (FractionRing V)) w₀
    hw₀ (g' c) (w c) (x (lab c)) (fr (lab c)) hwc (hfr _).1 hov xb rfl

  obtain ⟨f', f₁, -⟩ := GlobalTheory.TorsionIso.torsion_eq hL V _ hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U
    (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) hk
  have hq := (f₁ p (f' p)).2 rfl
  obtain ⟨w', fr', hw', hfr', hl'⟩ := GlobalTheory.Poinc.Tors.ValPair.liesOver_of_qkToAkU V _ hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U (AlgebraicClosure (FractionRing V))
    w₀ hw₀ _ hk p (f' p) rfl hq

  have e := GlobalTheory.Poinc.Tors.OneOver.eq_of_liesOver hL V _ hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U (AlgebraicClosure (FractionRing V)) w₀ hw₀ p.g wb w' xb
    (f' p) frb fr' hwb hw' hfrb hfr' hlb hl'
  refine ⟨p, xb, (map_zero 𝔪.e₈).symm, e ▸ hq, ?_⟩
  have e₁ : spMap (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) ≫ spMap 𝔪.yK =
      spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) :=
    (Spec.map_comp (CommRingCat.ofHom 𝔪.yK) (CommRingCat.ofHom (algebraMap _ _))).symm
  rw [← e₁, Category.assoc, ← hx (lab c)]
  rfl

end GlobalTheory.GSep.TermsLabel
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeClassZeroOfMemberTermsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.latticeClass_zero_of_member_terms : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam) (T : X → C → V), 𝔪.Terms x₀ lab T → ∀ c, 𝔪.YY (lab c) 0 := by
  first | exact @GlobalTheory.GSep.TermsLabel.yy_zero_of_terms | exact GlobalTheory.GSep.TermsLabel.yy_zero_of_terms | (intros; apply GlobalTheory.GSep.TermsLabel.yy_zero_of_terms <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeeperModelDividingLabelAndShiftsPreserved

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.GSep.div_lam_and_lam_mem_HH : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), GlobalTheory.GSep.IsAct X₁ act → (∀ m : ℕ, m ≠ 0 → IsUnit (m : X₁.M.Z.presheaf.stalk z₁)) → ∀ (𝔗 : GlobalTheory.GSep.Tower X₁ act) (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ → ∀ x₀ : X₁.S.Gam, X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ), 𝔗.X₂.M.Div 𝔗.X₂.S.th (𝔗.lam x₀) z₂ ∧ ∀ a ∈ X₁.S.HH X₁.M z₁, 𝔗.lam a ∈ 𝔗.X₂.S.HH 𝔗.X₂.M z₂ := by
  intro I X₁ z₁ act hact hunit 𝔗 z₂ hz₂ x₀ hx₀ V _ _ _ ev X _ t δ 𝔪
  refine ⟨GlobalTheory.T.galoisTower_dividing_label_stays_dividing I X₁ z₁ act hact hunit 𝔗 z₂ hz₂ x₀ hx₀ V ev X t δ 𝔪, ?_⟩
  intro a ha
  have hunitV : ∀ m : ℕ, m ≠ 0 → IsUnit (m : V) := fun m hm => by
    simpa using (hunit m hm).map ev
  obtain ⟨V', _, _, _, io, ev₂, hcn', hinj, hfin, -, -, hext⟩ := GlobalTheory.T.exists_centred_pure_extension_tower_member I X₁ z₁ act hact 𝔗 z₂ hz₂ V ev hunitV
    𝔪.cn 𝔪.loc 𝔪.reg
  obtain ⟨u, hT, -, -⟩ := GlobalTheory.T.thetaMember_exists_integral_terms_unit_shift I X₁ z₁ act x₀ hx₀ V ev X t δ 𝔪 (X₁.S.HH X₁.M z₁) Subtype.val
    Subtype.range_coe
  obtain ⟨eps, hbc⟩ := GlobalTheory.T.exists_galoisTower_baseChange_thetaMember I X₁ z₁ act hact 𝔗 z₂ hz₂ x₀ hx₀
  obtain ⟨𝔪₂, hterms, -⟩ := hbc V ev X t δ 𝔪 _ Subtype.val _ hT V' io hcn' hinj hfin
  let zt : 𝔗.X₂.M.Z.presheaf.stalk z₂ := (𝔗.X₂.M.stalkEquiv z₂).symm
    ⟨algebraMap 𝔗.X₂.o₁ 𝔗.X₂.Ω₁ 𝔗.X₂.S.ζ, (𝔗.X₂.M.O z₂).algebraMap_mem _⟩
  have hzt : 𝔗.X₂.M.stalkHom z₂ zt = algebraMap 𝔗.X₂.o₁ 𝔗.X₂.Ω₁ 𝔗.X₂.S.ζ :=
    congrArg Subtype.val ((𝔗.X₂.M.stalkEquiv z₂).apply_symm_apply _)
  have hyy := GlobalTheory.T.latticeClass_zero_of_member_terms I 𝔗.X₂ z₂ 𝔗.act₂ (𝔗.lam x₀) V' ev₂ X (fun k => io (t k)) δ (𝔪₂ ev₂ hext) _ _ _
    (hterms ev₂ hext zt hzt) ⟨a, ha⟩
  obtain ⟨x₂, hx₂⟩ := 𝔗.X₂.div z₂
  exact (GlobalTheory.T.mem_dividingLabels_iff_class_zero I 𝔗.X₂ z₂ 𝔗.act₂ x₂ hx₂ V' ev₂ X (fun k => io (t k)) δ (𝔪₂ ev₂ hext) (𝔗.lam a)).2 hyy
end
end
