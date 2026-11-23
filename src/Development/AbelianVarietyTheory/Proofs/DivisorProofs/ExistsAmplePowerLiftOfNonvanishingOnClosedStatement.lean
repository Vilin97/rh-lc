module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.PreservesFiniteColimitsTwistFunctor
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SumNegOnePowFinrankEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLineBundleSectionOfClosedImmersionAffineOpen
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.HdimEqZeroOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Mathlib.Algebra.Order.Star.Int

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySurjectiveToPushforwardAmpleLineBundle

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

noncomputable section
namespace GlobalTheory.SerreOnto
open CategoryTheory.Limits

variable {X T : Scheme.{0}} (i : T ⟶ X)

def unitToPush : GlobalTheory.LB.unitMod X ⟶ (Scheme.Modules.pushforward i).obj (GlobalTheory.LB.unitMod T) :=
  SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom

theorem toPushforward_comp (M : LB X) :
    GlobalTheory.LB.toPushforward M i ≫ ((Scheme.Modules.pushforward i).map (Twist.unitTwistIso (M.pull i)).inv ≫
      (Twist.projIso M i (GlobalTheory.LB.unitMod T)).hom) =
      (Twist.unitTwistIso M).inv ≫ Twist.map M (unitToPush i) := by
  apply Twist.hom_ext
  intro V s j
  change resG T (Twist.le_pull_inf i V j)
      ((i.appLE _ _ (GlobalTheory.LB.pull_inf_le i V (fun _ => j))).hom (GlobalTheory.LB.coord s j)) =
    (i.app _).hom (GlobalTheory.LB.coord s j)
  rw [GlobalTheory.LB.resG_appLE, ← Scheme.Hom.appLE_eq_app]

def kernelIso (M : LB X) (hM : M.IsLB) :
    kernel (GlobalTheory.LB.toPushforward M i) ≅ twist (kernel (unitToPush i)) M :=
  haveI := Twist.preservesFiniteLimits_twistFunctor hM
  kernel.mapIso _ _ (Twist.unitTwistIso M).symm
    ((Scheme.Modules.pushforward i).mapIso (Twist.unitTwistIso (M.pull i)).symm ≪≫
      Twist.projIso M i _) (toPushforward_comp i M) ≪≫
    (PreservesKernel.iso (twistFunctor M) (unitToPush i)).symm

end GlobalTheory.SerreOnto


open CategoryTheory.Limits in
theorem GlobalTheory.surjective_toPushforward_app_top_lbPow : ∀ (k : Type) [CommRing k] [IsNoetherianRing k]
    (X : Scheme.{0}) (p : X ⟶ Sp k), IsProjOver p → ∀ (L : LB X), IsAmpleLB L →
    ∀ (T : Scheme.{0}) (i : T ⟶ X) [IsClosedImmersion i], ∀ᶠ N in atTop,
      Function.Surjective ((GlobalTheory.LB.toPushforward (lbPow L N) i).app ⊤) := by
  intro k _ _ X p hp L hL T i _
  letI : Algebra k Γ(X, ⊤) := (p.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom).toAlgebra
  have hf : ∀ r, algebraMap k Γ(X, ⊤) r = p.appTop.hom ((Scheme.ΓSpecIso (.of k)).inv.hom r) :=
    fun _ => rfl
  haveI := (isProper_and_exists_isAmpleLB_of_isProjOver hp).1
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  haveI : QCoh.IsFiniteQC (kernel (GlobalTheory.SerreOnto.unitToPush i)) :=
    QCoh.IsFiniteQC.of_mono (kernel.ι (GlobalTheory.SerreOnto.unitToPush i))
  filter_upwards [hL.eventually_subsingleton_coh_twist hf (kernel (GlobalTheory.SerreOnto.unitToPush i))]
    with N hN
  have hM : (lbPow L N).IsLB := isLB_lbPow hL.isLB N
  haveI := GlobalTheory.PinchLift.epi_toPushforward_of_closedImm i hM
  let φ := GlobalTheory.LB.toPushforward (lbPow L N) i
  let S := ShortComplex.mk (kernel.ι φ) φ (kernel.condition φ)
  have hS : S.ShortExact := ShortComplex.ShortExact.mk'
    (S.exact_of_f_is_kernel (kernelIsKernel φ)) inferInstance inferInstance
  refine cohOn.app_surjective hS ⊤ ?_
  exact (cohOn.mapIso Γ(X, ⊤) ⊤ 1 (GlobalTheory.SerreOnto.kernelIso i _ hM)).toEquiv.subsingleton_congr.2
    (hN 1 one_pos)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySurjectiveToPushforwardAmpleLineBundleStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp


theorem _root_.GlobalTheory.T.eventually_surjective_toPushforward_ampleLineBundle_pow : ∀ (k : Type) [CommRing k] [IsNoetherianRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsProjOver p → ∀ (L : LB X), IsAmpleLB L → ∀ (T : Scheme.{0}) (i : T ⟶ X) [IsClosedImmersion i], ∀ᶠ N in atTop, Function.Surjective ((GlobalTheory.LB.toPushforward (lbPow L N) i).app ⊤) := by
  exact @GlobalTheory.surjective_toPushforward_app_top_lbPow
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionPullbackOfSurjectiveToPushforward

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

theorem GlobalTheory.LB.exists_secPull_eq_of_surjective_toPushforward : ∀ (X T : Scheme.{0}) (i : T ⟶ X) (M : LB X), M.IsLB → Function.Surjective ((GlobalTheory.LB.toPushforward M i).app ⊤) → ∀ σ : (M.pull i).Sec, ∃ u : M.Sec, GlobalTheory.secPull u i = σ := by
  intro X T i M _ hs σ
  obtain ⟨u', hu'⟩ := hs ((LB.globalEquiv (M.pull i)).symm σ)
  refine ⟨LB.globalEquiv M u', ?_⟩
  apply LB.f_injective
  funext j
  have key := LB.globalEquiv_pullSec_f i (LB.globalEquiv M u') j
  rw [← LB.globalEquiv_symm_apply, LinearEquiv.symm_apply_apply, ← LB.toPushforward_app, hu',
    LinearEquiv.apply_symm_apply] at key
  rw [key]
  exact chartSec_f _ _ _
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionPullbackOfSurjectiveToPushforwardStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp


theorem _root_.GlobalTheory.T.exists_sectionPullback_of_surjective_toPushforward : ∀ (X T : Scheme.{0}) (i : T ⟶ X) (M : LB X), M.IsLB → Function.Surjective ((GlobalTheory.LB.toPushforward M i).app ⊤) → ∀ σ : (M.pull i).Sec, ∃ u : M.Sec, GlobalTheory.secPull u i = σ := by
  first | exact @GlobalTheory.LB.exists_secPull_eq_of_surjective_toPushforward | exact GlobalTheory.LB.exists_secPull_eq_of_surjective_toPushforward | (intros; apply GlobalTheory.LB.exists_secPull_eq_of_surjective_toPushforward <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmplePowerLiftOfNonvanishingOnClosed

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

open ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory.LiftAmple

def chartPullPullPow {X T : Scheme.{0}} (L : LB X) (i : T ⟶ X) (n : ℕ) :
    ChartPull ((lbPow L n).pull i) (lbPow (L.pull i) n) (𝟙 T) where
  idx J := J
  le J y hy := mem_powChart.2 (mem_pull.2 (mem_powChart.1 (mem_pull.1 hy)))
  g y J J' hJ hJ' := by
    let K : PUnit → (L.pull i).ι := J
    let K' : PUnit → (L.pull i).ι := J'
    have h₁ : i y ∈ L.U (J PUnit.unit PUnit.unit) := mem_powChart.1 (mem_pull.1 hJ)
    have h₂ : i y ∈ L.U (J' PUnit.unit PUnit.unit) := mem_powChart.1 (mem_pull.1 hJ')
    have k₁ : (𝟙 T) y ∈ powChart (L.pull i) K := mem_powChart.2 (mem_pull.2 h₁)
    have k₂ : (𝟙 T) y ∈ powChart (L.pull i) K' := mem_powChart.2 (mem_pull.2 h₂)
    refine (gm_pull_g (lbPow L n) i (𝟙 T) y J J' hJ hJ').trans ?_
    refine (gm_lbPow_g n (𝟙 T ≫ i) y (J PUnit.unit) (J' PUnit.unit) (mem_powChart.2 h₁)
      (mem_powChart.2 h₂)).trans ?_
    refine Eq.trans ?_ (gm_lbPow_g (L := L.pull i) n (𝟙 T) y K K' k₁ k₂).symm
    rw [gm_pull_g L i (𝟙 T) y (K PUnit.unit) (K' PUnit.unit) (mem_powChart.1 k₁) (mem_powChart.1 k₂)]

theorem exists_sec_pull_pow {X T : Scheme.{0}} (L : LB X) (i : T ⟶ X) (n : ℕ) (σ : (lbPow (L.pull i) n).Sec) :
    ∃ σ' : ((lbPow L n).pull i).Sec, nonzeroLocus σ' = nonzeroLocus σ :=
  ⟨chartSec (chartPullPullPow L i n) σ, nonzeroLocus_chartSec_id _ σ fun _ J hJ =>
    ⟨J, mem_pull.2 (mem_powChart.2 (mem_pull.1 (mem_powChart.1 hJ)))⟩⟩

end GlobalTheory.LiftAmple

namespace GlobalTheory.LiftAmple

theorem exists_sec_nonzero_on_closed : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (L : LB X), IsAmpleLB L → ∀ (T : Scheme.{0}) (i : T ⟶ X) [IsClosedImmersion i] (n : ℕ)
    (s : (lbPow (L.pull i) n).Sec), 1 ≤ n → ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s = ⊤ →
    ∃ (N : ℕ) (u : (lbPow L N).Sec), 1 ≤ N ∧ Set.range i ⊆ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u := by
  intro k _ X _ p D hX L hL T i _ n s hn hs
  haveI : Module.Finite ℤ k := hX.finite
  haveI : IsNoetherian ℤ k := inferInstance
  haveI : IsNoetherianRing k := isNoetherian_of_tower ℤ this
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (GlobalTheory.T.eventually_surjective_toPushforward_ampleLineBundle_pow k X p hX.isProjOver L hL T i)
  have hN : N₀ ≤ n * (N₀ + 1) := by nlinarith
  obtain ⟨σ', hσ'⟩ := exists_sec_pull_pow L i (n * (N₀ + 1)) (secPow s (N₀ + 1))
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_sectionPullback_of_surjective_toPushforward X T i (lbPow L (n * (N₀ + 1))) (isLB_lbPow hL.isLB _) (hN₀ _ hN) σ'
  refine ⟨n * (N₀ + 1), u, by nlinarith, ?_⟩
  rintro _ ⟨z, rfl⟩
  have hz : z ∈ nonzeroLocus (GlobalTheory.secPull u i) := by
    rw [hu, hσ', nonzeroLocus_secPow s (Nat.le_add_left 1 N₀), hs]; trivial
  rw [nonzeroLocus_secPull] at hz
  exact hz

end GlobalTheory.LiftAmple
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmplePowerLiftOfNonvanishingOnClosedStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

theorem _root_.GlobalTheory.T.exists_ample_power_lift_of_nonvanishing_on_closed : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L : LB X), IsAmpleLB L → ∀ (T : Scheme.{0}) (i : T ⟶ X) [IsClosedImmersion i] (n : ℕ) (s : (lbPow (L.pull i) n).Sec), 1 ≤ n → ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s = ⊤ → ∃ (N : ℕ) (u : (lbPow L N).Sec), 1 ≤ N ∧ Set.range i ⊆ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u := by
  first | exact @GlobalTheory.LiftAmple.exists_sec_nonzero_on_closed | exact GlobalTheory.LiftAmple.exists_sec_nonzero_on_closed | (intros; apply GlobalTheory.LiftAmple.exists_sec_nonzero_on_closed <;> assumption)
end
end
