module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistConeVanishing
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SumNegOnePowFinrankEqZero
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowVanishingIdealLeAnnihilator
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.HdimEqZeroOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.PreservesFiniteColimitsTwistFunctor
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteCohOfForallModification
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotMemSupportKerMulSectionOfNonvanishing
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.TopologicalKrullDimLeOfIrreducibleCloseds
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportPushforwardSubsetImageOfIsClosedImmersion
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsQuasicoherentOfLocallyIso
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedPowerVanishingInductionBySectionSqTensorStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportPushforwardSubschemeSubset

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSubsingletonCohTwistTensLbPow

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem exists_subsingleton_coh_twist_tens_lbPow : ∀ (k : Type) [Field k] {Y : Scheme.{0}} (f : Y ⟶ Sp k), IsProjOver f → ∀ (A N : LB Y), IsAmpleLB A → N.IsLB → ∀ (G : Y.Modules) [IsFiniteQC G] (B : ℕ), ∃ j₁ : ℕ, ∀ j m : ℕ, j₁ ≤ j → m < B → ∀ p, 0 < p → Subsingleton (coh (twist G (tens (lbPow A j) (lbPow N m))) p) := by
  intro k _ Y f hf A N hA hN G _ B
  letI := algebraΓOfHom f
  have := (isProper_and_exists_isAmpleLB_of_isProjOver hf).1
  have H (m : Fin B) : ∃ q : ℕ, ∀ n ≥ q, ∀ p, 0 < p →
      Subsingleton (coh (twist (twist G (lbPow N m)) (lbPow A n)) p) :=
    have := isFiniteQC_twist (F := G) (isLB_lbPow hN m)
    eventually_atTop.1 (hA.eventually_subsingleton_coh_twist (f := f) (fun _ => rfl) _)
  choose q hq using H
  obtain ⟨Q, hQ⟩ := Finite.exists_le q
  refine ⟨Q, fun j m hj hm p hp => ?_⟩
  have := hq ⟨m, hm⟩ j ((hQ _).trans hj) p hp
  obtain ⟨e⟩ := nonempty_twist_twist_iso_of_cls_eq G (isLB_lbPow hN m)
    (isLB_lbPow hA.isLB j) (isLB_tens (isLB_lbPow hA.isLB j) (isLB_lbPow hN m)) (by
      rw [cls_tens (isLB_lbPow hA.isLB j) (isLB_lbPow hN m),
        ← cls_tens (isLB_lbPow hA.isLB j) (isLB_lbPow hN m) (isLB_tens (isLB_lbPow hA.isLB j) (isLB_lbPow hN m)),
        ← cls_tens (isLB_lbPow hN m) (isLB_lbPow hA.isLB j) (isLB_tens (isLB_lbPow hN m) (isLB_lbPow hA.isLB j))]
      exact (cls_eq_iff _ _).2 (tens_comm_iso (isLB_lbPow hA.isLB j) (isLB_lbPow hN m)))
  exact (cohOn.mapIso k ⊤ p e).symm.injective.subsingleton

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSubsingletonCohTwistTensLbPowStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

theorem _root_.GlobalTheory.T.exists_subsingleton_coh_twist_tens_lbPow' : ∀ (k : Type) [Field k] {Y : Scheme.{0}} (f : Y ⟶ Sp k), IsProjOver f → ∀ (A N : LB Y), IsAmpleLB A → N.IsLB → ∀ (G : Y.Modules) [IsFiniteQC G] (B : ℕ), ∃ j₁ : ℕ, ∀ j m : ℕ, j₁ ≤ j → m < B → ∀ p, 0 < p → Subsingleton (coh (twist G (tens (lbPow A j) (lbPow N m))) p) := by
  first | exact @GlobalTheory.exists_subsingleton_coh_twist_tens_lbPow | exact GlobalTheory.exists_subsingleton_coh_twist_tens_lbPow | (intros; apply GlobalTheory.exists_subsingleton_coh_twist_tens_lbPow <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotMemSupportKerMulSectionOfNonvanishingStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

theorem _root_.GlobalTheory.T.notMem_support_ker_mulSection_of_nonvanishing : ∀ {Y : Scheme.{0}} {L : LB Y} (hL : L.IsLB) (s : L.Sec) (G : Y.Modules) [G.IsQuasicoherent], ∀ x ∈ Out.nonzeroLocus s, x ∉ support (kernel (cutHom G hL s)) := by
  first | exact @GlobalTheory.KernelCut.notMem_support_kernel_cutHom | exact GlobalTheory.KernelCut.notMem_support_kernel_cutHom | (intros; apply GlobalTheory.KernelCut.notMem_support_kernel_cutHom <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportPushforwardSubsetImageOfIsClosedImmersionStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

theorem _root_.GlobalTheory.T.support_pushforward_subset_image : ∀ {X Y : Scheme.{0}} (g : Y ⟶ X) [IsClosedImmersion g] (E : Y.Modules), support ((Scheme.Modules.pushforward g).obj E) ⊆ g '' support E := by
  first | exact @GlobalTheory.support_pushforward_subset_image_of_isClosedImmersion | exact GlobalTheory.support_pushforward_subset_image_of_isClosedImmersion | (intros; apply GlobalTheory.support_pushforward_subset_image_of_isClosedImmersion <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedPowerHigherCohomVanishingPullbackIffPushf

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

set_option autoImplicit false
noncomputable section

namespace GlobalTheory

theorem subsingleton_coh_twist_pushforward_iff {X Y : Scheme.{0}} (g : Y ⟶ X) [IsAffineHom g]
    {A N : LB X} (hA : A.IsLB) (hN : N.IsLB) (G : Y.Modules) [G.IsQuasicoherent] (j m p : ℕ) :
    Subsingleton (coh (twist G (tens (lbPow (A.pull g) j) (lbPow (N.pull g) m))) p) ↔
      Subsingleton (coh (twist ((Scheme.Modules.pushforward g).obj G)
        (tens (lbPow A j) (lbPow N m))) p) := by
  have hT : (tens (lbPow A j) (lbPow N m)).IsLB := isLB_tens (isLB_lbPow hA j) (isLB_lbPow hN m)
  have hA' := LB.isLB_pull hA g
  have hN' := LB.isLB_pull hN g
  have hT' : (tens (lbPow (A.pull g) j) (lbPow (N.pull g) m)).IsLB :=
    isLB_tens (isLB_lbPow hA' j) (isLB_lbPow hN' m)
  have hTp := LB.isLB_pull hT g
  have e : cls _ hT' = cls _ hTp := by
    apply (cls_eq_iff hT' hTp).2
    let a := chartPullPowPull A g j
    let b := chartPullPowPull N g m
    have c : ChartPull (tens (lbPow (A.pull g) j) (lbPow (N.pull g) m))
        (tens (lbPow A j) (lbPow N m)) g := by
      refine ⟨fun t => (a.idx t.1, b.idx t.2), fun t _ hz => ⟨a.le _ hz.1, b.le _ hz.2⟩, ?_⟩
      intro z i k hi hk
      exact (gm_tens _ _ (𝟙 Y) z i k hi hk).trans ((congrArg₂ (· * ·)
        (a.g z _ _ hi.1 hk.1) (b.g z _ _ hi.2 hk.2)).trans
          (gm_tens _ _ g z (a.idx i.1, b.idx i.2) (a.idx k.1, b.idx k.2)
            ⟨a.le _ hi.1, b.le _ hi.2⟩ ⟨a.le _ hk.1, b.le _ hk.2⟩).symm)
    exact LBIso.chartPull c (chartPullPull _ g) (PolBaseChange.lbIso_refl hT)
  obtain ⟨i⟩ := nonempty_twist_iso_of_cls_eq G hT' hTp e
  have := Twist.isQuasicoherent_twist (F := G) hTp
  have e₁ : coh (twist ((Scheme.Modules.pushforward g).obj G) (tens (lbPow A j) (lbPow N m))) p ≃ₗ[ℤ]
      coh (twist G (tens (lbPow (A.pull g) j) (lbPow (N.pull g) m))) p :=
    (cohOn.mapIso ℤ ⊤ p (Twist.projIso _ g G).symm).trans
      ((LinearEquiv.ofBijective (cohPushMap ℤ g (fun r => by simp) (twist G _) ⊤ p)
        (cohPushMap_bijective_of_isAffineHom ℤ g (fun r => by simp) (twist G _) ⊤ p)).trans (cohOn.mapIso ℤ ⊤ p i.symm))
  exact e₁.toEquiv.subsingleton_congr.symm

theorem twistConeVanishing_pull_iff_pushforward : ∀ {X Y : Scheme.{0}} (g : Y ⟶ X) [IsAffineHom g]
    (A N : LB X), A.IsLB → N.IsLB → ∀ (G : Y.Modules) [G.IsQuasicoherent],
    (TwistConeVanishing (A.pull g) (N.pull g) G ↔
      TwistConeVanishing A N ((Scheme.Modules.pushforward g).obj G)) := by
  intro X Y g _ A N hA hN G _
  unfold TwistConeVanishing
  simp only [subsingleton_coh_twist_pushforward_iff g hA hN G]

end GlobalTheory
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedPowerHigherCohomVanishingPullbackIffPushfStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

theorem _root_.GlobalTheory.T.twistedPowerHigherCohomVanishing_pullback_iff_pushforward : ∀ {X Y : Scheme.{0}} (g : Y ⟶ X) [IsAffineHom g] (A N : LB X), A.IsLB → N.IsLB → ∀ (G : Y.Modules) [G.IsQuasicoherent], (TwistConeVanishing (A.pull g) (N.pull g) G ↔ TwistConeVanishing A N ((Scheme.Modules.pushforward g).obj G)) := by
  first | exact @GlobalTheory.twistConeVanishing_pull_iff_pushforward | exact GlobalTheory.twistConeVanishing_pull_iff_pushforward | (intros; apply GlobalTheory.twistConeVanishing_pull_iff_pushforward <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallySubsingletonCohAmplePsEff

section

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem TwistConeVanishing.of_isZero {X : Scheme.{0}} {A N : LB X} (hA : A.IsLB) (hN : N.IsLB)
    {F : X.Modules} (hF : IsZero F) : TwistConeVanishing A N F :=
  ⟨0, fun j m _ _ p _ => cohOn.subsingleton_of_isZero
    ((isZero_twist_iff (isLB_tens (isLB_lbPow hA j) (isLB_lbPow hN m))).2 hF) ⊤ p⟩

theorem TwistConeVanishing.of_shortExact {X : Scheme.{0}} {A N : LB X} (hA : A.IsLB) (hN : N.IsLB)
    {S : ShortComplex X.Modules} (hS : S.ShortExact) (h₁ : TwistConeVanishing A N S.X₁)
    (h₃ : TwistConeVanishing A N S.X₃) : TwistConeVanishing A N S.X₂ := by
  obtain ⟨a, ha⟩ := h₁
  obtain ⟨b, hb⟩ := h₃
  refine ⟨max a b, fun j m hj hm p hp => ?_⟩
  have hT := isLB_tens (isLB_lbPow hA j) (isLB_lbPow hN m)
  exact cohOn.subsingleton₂ (Twist.shortExact_map hT hS) ⊤ p
    (ha j m (le_of_max_le_left hj) hm p hp) (hb j m (le_of_max_le_right hj) hm p hp)

theorem TwistConeVanishing.of_generic (k : Type) [Field k] {V : Scheme.{0}} [IsIntegral V]
    (f : V ⟶ Sp k) (hf : IsProjOver f) (A N : LB V) (hA : IsAmpleLB A) (hN : IsPsEff N)
    (G : V.Modules) [IsFiniteQC G]
    (h : ∀ E : V.Modules, IsFiniteQC E → genericPoint V ∉ support E → TwistConeVanishing A N E) :
    TwistConeVanishing A N G := by
  have : AlgebraicGeometry.IsNoetherian V := isNoetherian_of_isProjOver hf
  obtain ⟨r, hr, s, hs⟩ := hN.exists_hasNonzeroSec hA (m := 2) (by norm_num)
  have hM : (lbPow (tens (lbPow N 2) A) r).IsLB :=
    isLB_lbPow (isLB_tens (isLB_lbPow hN.isLB 2) hA.isLB) r
  have hgen : genericPoint V ∈ Out.nonzeroLocus s := (sec_ne_zero_iff s).1 hs
  obtain ⟨j₁, hj₁⟩ := GlobalTheory.T.exists_subsingleton_coh_twist_tens_lbPow' k f hf A N hA hN.isLB G (2 * r)
  have hCf : IsFiniteQC (cokernel (cutHom G hM s)) := ((cut_by_regular_section.{0} G hM).1 s).2.2.1
  have hCs : support (cokernel (cutHom G hM s)) = support G \ ↑(Out.nonzeroLocus s) :=
    ((cut_by_regular_section.{0} G hM).1 s).2.2.2.1
  haveI : IsFiniteQC (twistZ G (lbPow (tens (lbPow N 2) A) r) (-1)) :=
    isFiniteQC_twist (isLB_lbZPow hM (-1))
  refine GlobalTheory.T.twistedPowerVanishing_induction_by_section_sq_tensor A N hA.isLB hN.isLB r hr hM s G ⟨j₁, hj₁⟩ (h _ inferInstance ?_)
    (h _ hCf ?_)
  · exact GlobalTheory.T.notMem_support_ker_mulSection_of_nonvanishing hM s G _ hgen
  · rw [hCs]
    exact fun h' => h'.2 hgen

end GlobalTheory

namespace GlobalTheory

theorem eventually_subsingleton_coh_ample_psEff : ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Sp k), IsProjOver f → ∀ A N : LB X, IsAmpleLB A → N.IsLB → (∀ Z : Closeds X, IsIrreducible (Z : Set X) → IsPsEff (N.pull (redι Z))) → ∀ F : X.Modules, IsFiniteQC F → ∃ j₀ : ℕ, ∀ j m : ℕ, j₀ ≤ j → m ≤ j → ∀ p, 0 < p → Subsingleton (coh (twist F (tens (lbPow A j) (lbPow N m))) p) := by
  intro k _ X f hf A N hA hN hpe F hF
  have : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isProjOver hf
  refine devissage X (TwistConeVanishing A N) (fun _ h => .of_isZero hA.isLB hN h)
    (fun _ hS _ _ h₁ h₃ => .of_shortExact hA.isLB hN hS h₁ h₃) ?_ F hF
  intro Z hZ hsmall G hG
  haveI := hG
  haveI := isIntegral_red hZ
  have hAV : IsAmpleLB (A.pull (redι Z)) := hA.pull_of_isClosedImmersion _
  refine (GlobalTheory.T.twistedPowerHigherCohomVanishing_pullback_iff_pushforward (redι Z) A N hA.isLB hN G).1 ?_
  refine TwistConeVanishing.of_generic k (redι Z ≫ f)
    (ProjSpace.isProjOver_comp_of_isClosedImmersion _ hf) _ _ hAV (hpe Z hZ) G ?_
  intro E hE hη
  haveI := hE
  have hE' : IsFiniteQC ((Scheme.Modules.pushforward (redι Z)).obj E) :=
    ProperFinite.isFiniteQC_pushforward (redι Z) hAV E
  refine (GlobalTheory.T.twistedPowerHigherCohomVanishing_pullback_iff_pushforward (redι Z) A N hA.isLB hN E).2 (hsmall _ hE' ?_)
  have hsub := GlobalTheory.T.support_pushforward_subset_image (redι Z) E
  refine ⟨hsub.trans ((Set.image_subset_range _ _).trans (range_redι Z).le), fun hle => hη ?_⟩
  have hηZ : (redι Z) (genericPoint (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) ∈ (Z : Set X) :=
    (range_redι Z).le ⟨_, rfl⟩
  obtain ⟨y, hy, hyη⟩ := hsub (hle hηZ)
  rwa [(redι Z).isClosedEmbedding.injective hyη] at hy

end GlobalTheory
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensOfForallIsPsEff

section

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem IsAmpleLB.tens_of_forall_isPsEff : ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Sp k), IsProjOver f → ∀ A N : LB X, IsAmpleLB A → N.IsLB → (∀ Z : Closeds X, IsIrreducible (Z : Set X) → IsPsEff (N.pull (redι Z))) → IsAmpleLB (tens A N) := by
  intro k _ X f hf A N hA hN hpe
  haveI : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isProjOver hf
  have hT : (tens A N).IsLB := isLB_tens hA.isLB hN
  refine isAmpleLB_of_subsingleton_coh_one X (tens A N) hT fun F hF => ?_
  obtain ⟨j₀, hj⟩ := eventually_subsingleton_coh_ample_psEff k X f hf A N hA hN hpe F hF
  refine ⟨max j₀ 1, le_max_right _ _, ?_⟩
  have h1 := hj (max j₀ 1) (max j₀ 1) (le_max_left _ _) le_rfl 1 one_pos
  have hpow (L : LB X) (hL : L.IsLB) (n : ℕ) (h : (lbPow L n).IsLB) :
      cls _ h = n • cls L hL := by
    rw [cls_linComb hL, Fintype.sum_unique, pull_id, natCast_zsmul]
  obtain ⟨i⟩ := nonempty_twist_iso_of_cls_eq F
    (isLB_tens (isLB_lbPow hA.isLB (max j₀ 1)) (isLB_lbPow hN (max j₀ 1)))
    (isLB_lbPow hT (max j₀ 1)) (by
      rw [cls_tens (isLB_lbPow hA.isLB _) (isLB_lbPow hN _), hpow A hA.isLB, hpow N hN,
        hpow (tens A N) hT, cls_tens hA.isLB hN, smul_add])
  exact (cohOn.mapIso Γ(X, ⊤) ⊤ 1 i).symm.injective.subsingleton

end GlobalTheory
end
end
end
