module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.GenIdeal
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChowDegreeSection
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartResidueDegreeAlgClosedClosed
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DvdOfForallEmultiplicityLe
public import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.DimClosureAddOneLe
import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.FinrankEqOfDimZero
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChowFormSectionPerfect
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ChowDegree
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PIntChowFormExists
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PChowFormHomog
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PFundCycleBaseChange
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMinimalPrimeComap
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.Tactic.Linter.HaveILetI
public import Mathlib.RingTheory.Flat.Stability
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsSectionOrderAlgClosed
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChartChoiceAlgClosed
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChartNormAlgClosed
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChartLengthAlgClosed
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsSpecFirst
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Assembly
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Assembly
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Assembly
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.Tactic.Linter.Style

-- Source module: GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChowDegreeSection

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial

theorem specFirstVar_isWeightedHomogeneous' {R : Type*} [CommSemiring R] {k n : ℕ} (u : Fin n → R)
    (ij : Fin (k + 1) × Fin n) :
    IsWeightedHomogeneous (groupWeight k n) (specFirstVar u ij)
      (fun i : Fin k => groupWeight (k + 1) n ij i.succ) := by
  obtain ⟨i, j⟩ := ij
  induction i using Fin.cases with
  | zero =>
    have h0 : (fun i : Fin k => groupWeight (k + 1) n ((0 : Fin (k + 1)), j) i.succ) = 0 := by
      funext i
      simp [groupWeight, Fin.succ_ne_zero i]
    rw [h0]
    simpa [specFirstVar] using isWeightedHomogeneous_C (groupWeight k n) (u j)
  | succ i' =>
    have h1 : (fun i : Fin k => groupWeight (k + 1) n (i'.succ, j) i.succ) = groupWeight k n (i', j) := by
      funext i
      simp [groupWeight, Pi.single_apply]
    rw [h1]
    simpa [specFirstVar] using isWeightedHomogeneous_X R (groupWeight k n) (i', j)

theorem isMultiHomog_specFirst {R : Type*} [CommSemiring R] {k n δ : ℕ}
    {f : MvPolynomial (Fin (k + 1) × Fin n) R} (u : Fin n → R) (hf : IsMultiHomog δ f) :
    IsMultiHomog δ (specFirst f u) := by
  unfold IsMultiHomog specFirst

  rw [f.as_sum, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_
  rw [bind₁_monomial]
  have hdeg : (fun _ : Fin k => δ) =
      ∑ ij ∈ d.support, d ij • (fun i : Fin k => groupWeight (k + 1) n ij i.succ) := by
    have hw := hf (mem_support_iff.mp hd)
    funext i
    have := congrFun hw i.succ
    rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply] at this
    rw [Finset.sum_apply, ← this]
    rfl
  rw [hdeg]
  refine IsWeightedHomogeneous.C_mul ?_ _
  refine IsWeightedHomogeneous.prod _ _ _ fun ij _ => ?_
  exact (specFirstVar_isWeightedHomogeneous' u ij).pow _

theorem ChowDegreeSection.proof (h : ChowFormSectionPerfect.Statement) : ChowDegreeSection.Statement := by
  intro F _ _ n e I u hI hdim hu
  obtain ⟨f, hf⟩ := chowFormExists F n (e + 2) I hI hdim
  have hfδ : IsMultiHomog (chowDegree I (e + 2)) f := Vertical.ChowFormHomog.proof F n (e + 2) I f hf
  obtain ⟨c, hc, g, hg, hfu⟩ := h F n (e + 1) I f u hI hf hu
  have hsδ : IsMultiHomog (chowDegree I (e + 2)) (specFirst f u) := isMultiHomog_specFirst u hfδ
  have hne : C c * ∏ W ∈ (divCycle I u).support, g W ^ (divCycle I u) W ≠ 0 := by
    refine mul_ne_zero (C_ne_zero.mpr hc) (Finset.prod_ne_zero_iff.mpr fun W hW => ?_)
    exact pow_ne_zero _ (hg W hW).1
  rw [hfu] at hsδ
  obtain ⟨δW, hδW, hsum⟩ :=
    exists_degrees_of_chowFormCycle (Nat.succ_pos e) (divCycle I u) c g hg hsδ hne
  rw [← hsum, Finsupp.sum]
  refine Finset.sum_congr rfl fun W hW => ?_
  congr 1
  exact Vertical.chowForm_degree_unique (Nat.succ_pos e) (hg W hW) (hg W hW) (hδW W hW)
    (Vertical.ChowFormHomog.proof F n (e + 1) W (g W) (hg W hW))

end ObjectsChow

end GroundTheory.Heights₂.Heights
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PMinimalPrimeComap

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem MinimalPrimeComap.flat (K L : Type) [Field K] [Field L] (σ : K →+* L) (ι : Type) :
    letI := σ.toAlgebra
    letI := MvPolynomial.algebraMvPolynomial (σ := ι) (R := K) (S := L)
    Module.Flat (MvPolynomial ι K) (MvPolynomial ι L) := by
  letI := σ.toAlgebra
  letI := MvPolynomial.algebraMvPolynomial (σ := ι) (R := K) (S := L)
  have h : Algebra.IsPushout K (MvPolynomial ι K) L (MvPolynomial ι L) := inferInstance
  exact Module.Flat.isBaseChange K (MvPolynomial ι K) L (MvPolynomial ι L) h.out

theorem MinimalPrimeComap.proof : MinimalPrimeComap.Statement := by
  intro K L _ _ σ ι I hI P hP
  letI := σ.toAlgebra
  letI := MvPolynomial.algebraMvPolynomial (σ := ι) (R := K) (S := L)
  have := MinimalPrimeComap.flat K L σ ι
  have halg : algebraMap (MvPolynomial ι K) (MvPolynomial ι L) = MvPolynomial.map σ := rfl
  have : P.IsPrime := hP.1.1
  have hle : I ≤ P.comap (MvPolynomial.map σ) := Ideal.map_le_iff_le_comap.mp hP.1.2
  by_contra hne
  have hlt : I < P.under (MvPolynomial ι K) := lt_of_le_of_ne hle (fun h => hne h.symm)
  have : (P.under (MvPolynomial ι K)).IsPrime := Ideal.IsPrime.under _ _
  have : P.LiesOver (P.under (MvPolynomial ι K)) := ⟨rfl⟩
  obtain ⟨Q, hQP, hQ, hQI⟩ := Ideal.exists_ideal_lt_liesOver_of_lt (p := I) P hlt
  have hIQ : I.map (MvPolynomial.map σ) ≤ Q := by
    rw [Ideal.map_le_iff_le_comap, ← halg, ← Ideal.under_def, ← hQI.over]
  exact (not_le_of_gt hQP) (hP.2 ⟨hQ, hIQ⟩ hQP.le)

end GroundTheory.Heights₂.Heights
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PSectionOrderAlgClosed

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem SectionOrderAlgClosed.proof (h₁ : IncIdealBelow.Statement) (h₂ : SpecFirstMemIncIdeal.Statement)
    (h₃ : ChartChoiceAlgClosed.Statement) (h₄ : Vertical.SpecFirstNeField.Statement)
    (h₅ : LocalizationPrimeDVR.Statement) (h₆ : EmultiplicityOrd.Statement) (h₇ : ChartFinite.Statement)
    (h₈ : ChartLocDomain.Statement) (h₉ : ChartNormAlgClosed.Statement)
    (h₁₀ : ChartLengthAlgClosed.Statement) (h₁₁ : LengthQuotientDet.Statement) :
    SectionOrderAlgClosed.Statement := by
  intro F _ _ n e I f u hI hf hu
  have hne : specFirst f u ≠ 0 := h₄ F n e I f u hI hf hu
  refine ⟨hne, fun q hq => ?_⟩
  have hqp : Prime q := hq.prime
  obtain ⟨t, ht⟩ := h₃ F n e I f q hI hf hqp

  have htI : linForm t ∉ I := by
    intro h
    have hmem := h₂ F n e I I f t hf le_rfl h
    rw [h₁ F n e I f hI hf, Ideal.mem_bot] at hmem
    exact ht (hmem ▸ dvd_zero q)
  let p : Ideal (MvPolynomial (Fin e × Fin n) F) := Ideal.span {q}
  have hpp : p.IsPrime := (Ideal.span_singleton_prime hqp.ne_zero).mpr hqp
  have htp : specFirst f t ∉ p := by
    rw [Ideal.mem_span_singleton]
    exact ht
  have : IsDiscreteValuationRing (Localization.AtPrime p) := h₅ _ q p hqp rfl
  have hem := h₆ _ q (specFirst f u) p hqp rfl hne
  have : Module.Finite (Localization.AtPrime p) (ChartLoc I t e p) := h₇ F n e I f t p hI hf htp
  obtain ⟨_, hinj, -⟩ := h₈ F n e I f t p hI hf htI
  have : Module.IsTorsionFree (Localization.AtPrime p) (ChartLoc I t e p) := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    exact hinj
  have : Module.Free (Localization.AtPrime p) (ChartLoc I t e p) :=
    Module.free_of_finite_type_torsion_free'
  have hnorm := h₉ F n e I f t p hI hf (Or.inr ⟨q, hqp, rfl⟩) htp u
  have hunit : IsUnit (algebraMap _ (Localization.AtPrime p) (specFirst f t)) :=
    IsLocalization.map_units (Localization.AtPrime p) (⟨specFirst f t, htp⟩ : p.primeCompl)
  have hinjO : Function.Injective
      (algebraMap (MvPolynomial (Fin e × Fin n) F) (Localization.AtPrime p)) :=
    IsLocalization.injective _ p.primeCompl_le_nonZeroDivisors
  have hdet : LinearMap.det (LinearMap.mulLeft (Localization.AtPrime p)
      (algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartLin I t e u))) ≠ 0 := by
    intro h0
    apply hne
    apply hinjO
    rw [hnorm, h0, mul_zero, map_zero]
  have hlen := h₁₁ (Localization.AtPrime p) (ChartLoc I t e p) _ hdet
  rw [hem, hnorm, Ring.ord_mul_of_isUnit_left hunit, ← hlen]
  exact h₁₀ F n e I f t u q p hI hf hu hqp rfl ht

end

end GroundTheory.Heights₂.Heights
end
end

-- Source module: Development.WeilBound.CoreStatements.MinimalPrimeDimensions.ChowDegreeSection

section

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier
open GroundTheory.Heights₂.Heights (IsProjPrime IsHomogIdeal IsRelevant relComps localMult chowDegree reduceMod divCycle)

namespace ChowFormHeightComparison₂.CF.V

open GroundTheory.Heights₂.Heights GlobalTheory.CompanionTheory.Ar.Short.ChowClosing in
theorem chowDegreeSection : ObjectsChow.ChowDegreeSection.Statement :=
  ObjectsChow.ChowDegreeSection.proof
    (chowFormSectionPerfect_of
      (chowFormSectionAlgClosed_of
        (SectionOrderAlgClosed.proof IncIdealBelow.full SpecFirstMemIncIdeal.full
          chartChoiceAlgClosed_closed Vertical.SpecFirstNeField.full
          LocalizationPrimeDVR.full EmultiplicityOrd.full ChartFinite.full ChartLocDomain.full
          GlobalTheory.CompanionTheory.Ar.Short.ChowClosing.Auto.ChartNormAlgClosed
          chartLengthAlgClosed_closed LengthQuotientDet.full))
      sectionCycleReduced_closed MinimalPrimeComap.proof
      (FundCycleBaseChange.proof MinimalPrimeComap.proof))

theorem algX_strHom {κ : Type} [Field κ] {Z : Scheme.{0}} [Algebra κ Γ(Z, ⊤)] :
    algX (strHom κ Z) ⊤ = algebraMap κ Γ(Z, ⊤) := by
  ext r
  rw [algebraMap_eq_strHom]
  simp only [algX, RingHom.comp_apply, CommRingCat.hom_comp]
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

section Base

variable {R S : Type} [CommRing R] [CommRing S] {Z : Scheme.{0}} {p : Z ⟶ Sp R} {q : Z ⟶ Sp S} {π : R →+* S}
  {B : LB Z} {m : ℕ} {s : Fin m → B.Sec}

theorem algX_eq_comp (h : algX p ⊤ = (algX q ⊤).comp π) (U : Z.Opens) : algX p U = (algX q U).comp π := by
  rw [← TopForm.resG_comp_algX p (le_top : U ≤ ⊤), h, ← RingHom.comp_assoc, TopForm.resG_comp_algX]

private theorem eq_of_algX_top_eq {R : Type} [CommRing R] {Z : Scheme.{0}} {f g : Z ⟶ Sp R}
    (h : algX f ⊤ = algX g ⊤) : f = g := by
  have hf : ∀ φ : Z ⟶ Sp R,
      algX φ ⊤ = ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ φ.appTop).hom := by
    intro φ
    ext r
    simp only [algX, RingHom.comp_apply, CommRingCat.hom_comp]
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  rw [hf, hf] at h
  have e : f.appTop = g.appTop := by
    simpa using CommRingCat.hom_ext h
  haveI : Mono (Sp R).toSpecΓ := by
    rw [← SpecMap_ΓSpecIso_hom]
    infer_instance
  rw [← cancel_mono (Sp R).toSpecΓ, Scheme.toSpecΓ_naturality, Scheme.toSpecΓ_naturality, e]

theorem eq_comp_spMap (h : algX p ⊤ = (algX q ⊤).comp π) : q ≫ spMap π = p := by
  apply eq_of_algX_top_eq
  rw [h]
  ext r
  have key := congrArg (fun φ => φ.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom π))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at key
  simp only [algX, Scheme.Hom.appLE, spMap, Scheme.Hom.comp_app, CommRingCat.hom_comp, RingHom.comp_apply,
    RingHom.coe_comp, Function.comp_apply]
  rw [key]
  rfl

theorem emb_base (h : algX p ⊤ = (algX q ⊤).comp π) (hE : Emb p s) : Emb q s := by
  obtain ⟨hLB, hcov, hch⟩ := hE
  refine ⟨hLB, hcov, fun k => ?_⟩
  obtain ⟨ha, t, hs, hr⟩ := hch k
  refine ⟨ha, t, fun x => ?_, hr⟩
  obtain ⟨P, rfl⟩ := hs x
  refine ⟨MvPolynomial.map π P, ?_⟩
  rw [algX_eq_comp h]
  simp [MvPolynomial.eval₂_map]

theorem ptIdeal_base (h : algX p ⊤ = (algX q ⊤).comp π) (z : Z) :
    ptIdeal p s z = (ptIdeal q s z).comap (MvPolynomial.map π) := by
  simp only [ptIdeal, Ideal.comap_iInf, RingHom.comap_ker]
  refine iInf_congr fun i => iInf_congr fun hi => congrArg _ ?_
  refine MvPolynomial.ringHom_ext (fun r => ?_) fun j => ?_
  · simp [coneHom, algX_eq_comp h]
  · simp [coneHom]

end Base

end ChowFormHeightComparison₂.CF.V

namespace ChowFormHeightComparison₂.CF

private theorem evaluation_genericPoint_eq_zero_iff {Z : Scheme.{0}} [IsIntegral Z] {U : Z.Opens}
    (hU : genericPoint Z ∈ U) (a : Γ(Z, U)) :
    Z.evaluation U (genericPoint Z) hU a = 0 ↔ a = 0 := by
  rw [Scheme.evaluation_eq_zero_iff_notMem_basicOpen]
  constructor
  · intro h
    by_contra ha
    apply h
    have hne : Z.basicOpen a ≠ ⊥ := by
      rwa [Ne, basicOpen_eq_bot_iff]
    show genericPoint Z ∈ (Z.basicOpen a : Set Z)
    rw [(genericPoint_spec Z).mem_open_set_iff (Z.basicOpen a).isOpen, Set.univ_inter]
    rwa [Ne, ← Opens.not_nonempty_iff_eq_bot, not_not] at hne
  · rintro rfl
    simp

private theorem C_mem_ptIdeal_genericPoint_iff {R : Type} [CommRing R] {Z : Scheme.{0}} [IsIntegral Z] {B : LB Z} {m : ℕ}
    (p : Z ⟶ Sp R) (s : Fin m → B.Sec) (hB : B.IsLB) (r : R) :
    MvPolynomial.C r ∈ ptIdeal p s (genericPoint Z) ↔ algX p ⊤ r = 0 := by
  have hη : genericPoint Z ∈ ⨆ i, B.U i := by
    rw [hB.cover]
    trivial
  obtain ⟨i₀, hi₀⟩ := Opens.mem_iSup.mp hη
  simp only [ptIdeal, Ideal.mem_iInf, RingHom.mem_ker, coneHom, MvPolynomial.eval₂Hom_C,
    RingHom.comp_apply, Polynomial.C_eq_zero]
  constructor
  · intro h
    have := h i₀ hi₀
    rw [V.evaluation_algX] at this
    exact (evaluation_genericPoint_eq_zero_iff _ _).mp this
  · intro h i hi
    rw [V.evaluation_algX, h]
    simp

private theorem isProjOver_of_surjective_base {R S : Type} [CommRing R] [CommRing S] {Z : Scheme.{0}}
    {p : Z ⟶ Sp R} {q : Z ⟶ Sp S} {π : R →+* S} (hπ : Function.Surjective π)
    (hq : q ≫ spMap π = p) (hP : IsProjOver p) : IsProjOver q := by
  haveI : IsClosedImmersion (spMap π) := IsClosedImmersion.spec_of_surjective _ hπ
  let ι : Z ⟶ Limits.pullback p (spMap π) := Limits.pullback.lift (𝟙 Z) q (by simp [hq])
  have h1 : ι ≫ Limits.pullback.fst p (spMap π) = 𝟙 Z := Limits.pullback.lift_fst _ _ _
  have h2 : ι ≫ Limits.pullback.snd p (spMap π) = q := Limits.pullback.lift_snd _ _ _
  haveI : IsIso ι := ⟨⟨Limits.pullback.fst p (spMap π), h1, by
    rw [← cancel_mono (Limits.pullback.fst p (spMap π)), Category.assoc, h1]
    simp⟩⟩
  rw [← h2]
  exact ProjSpace.isProjOver_comp_of_isClosedImmersion ι (ProjSpace.isProjOver_pullback_snd π hP)

open V in
attribute [local instance] MvPolynomial.gradedAlgebra in
theorem stVert (h1 : StPts) (h2 : StPull) (h3 : StDiv) : StVert := by
  intro K _ _ Z _ p B m s v d hP hE hv hd
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  set κ := v.asIdeal.ResidueField
  have hB := hE.isLB
  have hker : ∀ r, algX p ⊤ r = 0 ↔ r ∈ v.asIdeal := by
    intro r
    rw [← C_mem_ptIdeal_genericPoint_iff p s hB r, ← hv, Ideal.mem_comap]
  let e : (𝓞 K ⧸ v.asIdeal) ≃+* κ :=
    RingEquiv.ofBijective _ v.asIdeal.bijective_algebraMap_quotient_residueField
  let φ : κ →+* Γ(Z, ⊤) :=
    (Ideal.Quotient.lift v.asIdeal (algX p ⊤) fun r hr => (hker r).mpr hr).comp e.symm.toRingHom
  letI inst : Algebra κ Γ(Z, ⊤) := φ.toAlgebra
  refine ⟨inst, ?_⟩
  have hπ : algX p ⊤ = (algX (strHom κ Z) ⊤).comp (algebraMap (𝓞 K) κ) := by
    rw [V.algX_strHom]
    ext r
    show algX p ⊤ r = φ (algebraMap (𝓞 K) κ r)
    have hr : e.symm (algebraMap (𝓞 K) κ r) = Ideal.Quotient.mk v.asIdeal r := by
      rw [RingEquiv.symm_apply_eq]
      rfl
    simp only [φ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hr,
      Ideal.Quotient.lift_mk]
  have hsurj : Function.Surjective (algebraMap (𝓞 K) κ) :=
    v.asIdeal.algebraMap_residueField_surjective
  have hEκ : Emb (strHom κ Z) s := V.emb_base hπ hE
  have hPκ : IsProjOver (strHom κ (X := Z)) := isProjOver_of_surjective_base hsurj (V.eq_comp_spMap hπ) hP
  have hred : reduceMod v (ptIdeal p s (genericPoint Z)) = ptIdeal (strHom κ Z) s (genericPoint Z) := by
    rw [V.ptIdeal_base hπ]
    exact Ideal.map_comap_of_surjective _ (MvPolynomial.map_surjective _ hsurj) _
  rw [hred]
  set J := ptIdeal (strHom κ Z) s (genericPoint Z)
  have hdimle : ringKrullDim (MvPolynomial (Fin m) κ ⧸ J) ≤ m := by
    refine (ringKrullDim_quotient_le J).trans ?_
    simp [MvPolynomial.ringKrullDim_of_isNoetherianRing]
  have hdimge : ((d : WithBot ℕ∞) + 1) ≤ ringKrullDim (MvPolynomial (Fin m) κ ⧸ J) := by
    have := V.dim_add_one_le h1 hEκ
    rwa [hd] at this
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ringKrullDim (MvPolynomial (Fin m) κ ⧸ J) = n := by
    revert hdimle hdimge
    generalize ringKrullDim (MvPolynomial (Fin m) κ ⧸ J) = x
    intro hdimle hdimge
    induction x using WithBot.recBotCoe with
    | bot => simp at hdimge
    | coe y =>
      induction y using ENat.recTopCoe with
      | top =>
        exfalso
        have h' : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((m : ℕ∞) : WithBot ℕ∞) := hdimle
        rw [WithBot.coe_le_coe, top_le_iff] at h'
        exact ENat.coe_ne_top m h'
      | coe n => exact ⟨n, rfl⟩
  have hnd : d + 1 ≤ n := by
    rw [hn] at hdimge
    exact_mod_cast hdimge
  have hn' : ringKrullDim (MvPolynomial (Fin m) κ ⧸ J) = ↑(n - 1 + 1) := by
    rw [hn]
    congr 1
    omega
  obtain ⟨hZ, hdeg⟩ := V.field_case h1 h2 h3 V.chowDegreeSection
    GlobalTheory.CompanionTheory.Ar.Short.ChowClosing.Auto.ObjectsChow_ChowDegreeClosedPoint (n - 1) Z B s hPκ hEκ hn'
  have hnd' : n - 1 = d := by
    rw [hd] at hZ
    exact_mod_cast hZ.symm
  rw [← hnd']
  exact hdeg

end ChowFormHeightComparison₂.CF
end
end
end
