module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsAmpleOfGenTwist
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPerturb
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SegreJoin
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.KleimanGenericPointSectionInputStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.KleimanInputNefAmpleSectionCountStatement
import Development.WeilBound.CoreStatements.HodgeTatePoints.A12
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PVocabMultiHomog
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PVocabMultiHomogIdeal
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
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
import Mathlib.Topology.Sheaves.Init
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.DegreeOneCellEqChartUpdate
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenTwistGenerated
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CellResMemLocPart
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PCutRegular
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PAmpleOfGenTwist
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenKoszulStep
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenTwistVanish
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PKleimanNefF
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PKleimanScheme
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PKoszulCechComplex
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PKoszulCechExact
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.BlockVecSegreJoin
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsNeZeroOfWeight
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsMultiProjPrimeSegreLift
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PKHCechDDeg
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PKHCechDSq
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.RelDimMIdealOverEqTrdeg
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ZpowMemSubalgebraOfInvMem
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Tactic.Polynomial.Basic

-- Source module: GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.GeneratedCechTieSt

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver GeneratedV)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2 (IsGenerated baseDeg pnPt isModelWithBase_pnPt)

def GeneratedCechTie.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (β : K → ℤ),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → IsGenerated S y β → GeneratedV S (mIdealOver S y) β

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PGeneratedCechTieX

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (Cell cellMon CechC cechD locPart cechCc cechZc mIdealOver chartRingOver quotPart
  secOver GeneratedV)

noncomputable section

namespace GeneratedCechTie

open HZeroRowPlaceData

set_option linter.unusedSectionVars false

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, Fintype (ι k)]
  [∀ k, LinearOrder (ι k)] {Ω : Type} [Field Ω] [Algebra S Ω] {y : (Σ k, ι k) → Ω}

theorem evMap_mul {I : ∀ k, Finset (ι k)} (hI : Good y I)
    (x x' : LocalizedModule (cellMon S I) (MRingOver S ι ⧸ mIdealOver S y)) :
    evMap y I (x * x') = evMap y I x * evMap y I x' := by
  induction x using LocalizedModule.induction_on with
  | h m t =>
    induction x' using LocalizedModule.induction_on with
    | h m' t' =>
      obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective m
      obtain ⟨g', rfl⟩ := Ideal.Quotient.mk_surjective m'
      rw [LocalizedModule.mk_mul_mk, ← map_mul, evMap_mk y hI, evMap_mk y hI, evMap_mk y hI,
        Submonoid.coe_mul, map_mul, map_mul, mul_div_mul_comm]

theorem evMap_one {I : ∀ k, Finset (ι k)} (hI : Good y I) :
    evMap y I (1 : LocalizedModule (cellMon S I) (MRingOver S ι ⧸ mIdealOver S y)) = 1 := by
  have h1 : (1 : LocalizedModule (cellMon S I) (MRingOver S ι ⧸ mIdealOver S y)) =
      LocalizedModule.mk (Ideal.Quotient.mk (mIdealOver S y) 1) 1 := by
    rw [map_one, ← pow_zero (LocalizedModule.mk (1 : MRingOver S ι ⧸ mIdealOver S y) (1 : cellMon S I)),
      LocalizedModule.mk_pow, one_pow, one_pow]
  rw [h1, evMap_mk y hI]
  simp

theorem one_mem_locPart (T : Submonoid (MRingOver S ι)) :
    (1 : LocalizedModule T (MRingOver S ι ⧸ mIdealOver S y)) ∈
      locPart ι (quotPart S (mIdealOver S y)) T 0 := by
  have h1 : (1 : LocalizedModule T (MRingOver S ι ⧸ mIdealOver S y)) =
      LocalizedModule.mk (Ideal.Quotient.mk (mIdealOver S y) 1) 1 := by
    rw [map_one, ← pow_zero (LocalizedModule.mk (1 : MRingOver S ι ⧸ mIdealOver S y) (1 : T)),
      LocalizedModule.mk_pow, one_pow, one_pow]
  rw [h1]
  refine GroundTheory.Heights₂.Heights.HilbertSamuel.GenTwistGenerated.mk_mem_locPart _ 1 0
    (GroundTheory.Heights₂.Heights.HilbertSamuel.GenTwistGenerated.isMultiHomog_one _ fun _ => rfl) ?_
  refine Submodule.subset_span ⟨1, ⟨fun k => by simp, ?_⟩, rfl⟩
  exact GroundTheory.Heights₂.Heights.HilbertSamuel.GenTwistGenerated.isMultiHomog_one _ fun k => by simp

theorem exists_cocycle {n : K → ℤ} {s : Ω} (hs : s ∈ secOver S y n) :
    ∃ z ∈ cechZc ι (quotPart S (mIdealOver S y)) n 0,
      ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → evMap y (chart c) (z (cell0 c)) = s := by
  have hs' : ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
      s * ∏ k, y ⟨k, c k⟩ ^ (-n k) ∈ chartRingOver S y c := by
    intro c hc
    exact (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp hs c) hc
  have hlift : ∀ I : Cell K ι 0, Good y I.1 → ∃ w ∈ locPart ι (quotPart S (mIdealOver S y)) (cellMon S I.1) n,
      evMap y I.1 w = s := fun I hI =>
    exists_lift hI (fun k => Finset.min'_mem _ (I.2.1 k)) n
      (hs' _ fun k => hI k _ (Finset.min'_mem _ (I.2.1 k)))
  classical
  let z : CechC S ι (MRingOver S ι ⧸ mIdealOver S y) 0 := fun I =>
    if hI : Good y I.1 then (hlift I hI).choose else 0
  have hzC : ∀ I : Cell K ι 0, z I ∈ locPart ι (quotPart S (mIdealOver S y)) (cellMon S I.1) n := by
    intro I
    by_cases hI : Good y I.1
    · simp only [z, dif_pos hI]; exact (hlift I hI).choose_spec.1
    · simp only [z, dif_neg hI]; exact Submodule.zero_mem _
  have hzv : ∀ I : Cell K ι 0, Good y I.1 → evMap y I.1 (z I) = s := by
    intro I hI
    simp only [z, dif_pos hI]
    exact (hlift I hI).choose_spec.2
  have hzCc : z ∈ cechCc ι (quotPart S (mIdealOver S y)) n 0 :=
    Submodule.mem_pi.mpr fun I _ => hzC I
  have hzD : cechD S ι _ 0 z = 0 := by
    funext J
    by_cases hJ : Good y J.1
    · refine evMap_injOn y hJ n (cechD_mem_locPart n 0 hzCc J) (Submodule.zero_mem _) ?_
      have hconst : constD K ι Ω 0 (fun I => evMap y I.1 (z I)) J = constD K ι Ω 0 (fun _ => s) J :=
        CechPointVanish.constD_congr J.1 0 (fun I hIJ => hzv I fun k i hi => hJ k i (hIJ k hi)) J
          fun k => subset_refl _
      rw [evMap_cechD z J hJ, hconst, constD_const, Pi.zero_apply, map_zero]
    · unfold Good at hJ
      push Not at hJ
      obtain ⟨k, i, hi, hy0⟩ := hJ
      have := subsingleton_of_bad (S := S) hi hy0
      exact @Subsingleton.elim _ this _ _
  exact ⟨z, Submodule.mem_inf.mpr ⟨hzCc, hzD⟩, fun c hc => hzv (cell0 c) (good_chart hc)⟩

end GeneratedCechTie


open GeneratedCechTie HZeroRowPlaceData in
theorem GeneratedCechTie.proof : GeneratedCechTie.Statement := by
  intro S _ K _ _ ι _ _ Ω _ _ y β _ hgen I
  obtain ⟨n, s, hs, hgen⟩ := hgen
  obtain ⟨c, rfl⟩ := degree_zero_cell_eq_chart I
  by_cases hc : ∀ k, y ⟨k, c k⟩ ≠ 0
  · choose z hz hzv using fun j => exists_cocycle (hs j)
    obtain ⟨u, hu, hsum⟩ := hgen c hc
    have hcI : ∀ k, c k ∈ chart c k := fun k => Finset.mem_singleton_self _
    have hval : ∀ j, u j * (∏ k, y ⟨k, c k⟩ ^ (-β k)) * ∏ k, y ⟨k, c k⟩ ^ (-(-β) k) = u j := by
      intro j
      rw [mul_assoc, ← Finset.prod_mul_distrib]
      simp only [Pi.neg_apply, neg_neg]
      rw [Finset.prod_congr rfl fun k _ => zpow_neg_mul_zpow_self (β k) (hc k), Finset.prod_const_one,
        mul_one]
    choose U hU hUv using fun j => exists_lift (good_chart hc) hcI (-β)
      (s := u j * ∏ k, y ⟨k, c k⟩ ^ (-β k)) (by rw [hval j]; exact hu j)
    refine ⟨n, z, U, hz, hU, ?_⟩
    let Z : Fin n → LocalizedModule (cellMon S (chart c)) (MRingOver S ι ⧸ mIdealOver S y) := fun j => z j (cell0 c)
    show ∑ j, U j * Z j = 1
    have hmem : ∑ j, U j * Z j ∈ locPart ι (quotPart S (mIdealOver S y)) (cellMon S (chart c)) 0 := by
      refine Submodule.sum_mem _ fun j _ => ?_
      have h := GroundTheory.Heights₂.Heights.HilbertSamuel.GenTwistGenerated.locPart_mul (hU j)
        (Submodule.mem_pi.mp (Submodule.mem_inf.mp (hz j)).1 (cell0 c) (Set.mem_univ _))
      rwa [neg_add_cancel] at h
    refine evMap_injOn y (good_chart hc) 0 hmem (one_mem_locPart _) ?_

    rw [evMap_one (good_chart hc), map_sum, ← hsum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [evMap_mul (good_chart hc), hUv j, show evMap y (chart c) (Z j) = s j from hzv j c hc]
    ring
  · push Not at hc
    obtain ⟨k, hk⟩ := hc
    have := subsingleton_of_bad (S := S) (I := chart c) (Finset.mem_singleton_self (c k)) hk
    exact ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, fun j => j.elim0, @Subsingleton.elim _ this _ _⟩

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.SegreJoinGeneration.GeneratesOverSegreJoinTwist

section

@[expose] public section

namespace PositivityTheory.KAmp

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2 (IsNef IsGenerated KAt baseDeg)
open GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization (segreJoin)

theorem kAt_all (d : ℕ) : KAt d := (GlobalTheory.T.kleiman_input_nef_ample_section_count GlobalTheory.T.kleiman_genericPointSectionInput).2.1 d

theorem genTwistVanish : HilbertSamuel.GenTwistVanish.Statement :=
  HilbertSamuel.GenTwistVanish.proof PositivityTheory.HtPt.Ktw.a11 HilbertSamuel.QuotPartGraded.full
    (HilbertSamuel.GenKoszulStep.proof HilbertSamuel.KoszulCechComplex.proof HilbertSamuel.KoszulCechExact.proof
      HilbertSamuel.DoubleComplexVanish.full Kleiman.KHCechDSq.full Kleiman.KHCechDDeg.full)

theorem ampleOfGenTwist : HilbertSamuel.AmpleOfGenTwist.Statement :=
  HilbertSamuel.AmpleOfGenTwist.proof HilbertSamuel.GenTwistGenerated.full genTwistVanish

theorem generatesOver_segreJoin_twist {S : Type} [CommRing S] {K : Type} [Fintype K] [DecidableEq K]
    {ι : K → Type} {Ω : Type} [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (β : K → ℤ) (c : ℤ) {n : ℕ}
    (η : Fin n → Ω)
    (h : KH.GeneratesOver S (segreJoin y) (IndefiniteRowSideFullHecke.Kleiman2.pullDeg (K₁ := Unit) β + c • baseDeg (Sum.inl ())) η) :
    KH.GeneratesOver S y (β + fun _ => c) η := by
  intro c0 hc
  obtain ⟨u, hu, hsum⟩ := h (Kleiman.SectionsOverLocalization.segreChart c0 c0)
    (Kleiman.SectionsOverLocalization.segreChart_adm y (Kleiman.SectionsOverLocalization.segreVec_ne_zero y hc) hc)
  refine ⟨u, fun j => Kleiman.SectionsOverLocalization.segre_diag_le y c0 (hu j), ?_⟩
  have e1 : ∀ k : K, segreJoin y ⟨Sum.inr k, Kleiman.SectionsOverLocalization.segreChart c0 c0 (Sum.inr k)⟩ = y ⟨k, c0 k⟩ :=
    fun _ => rfl
  have e2 : segreJoin y ⟨Sum.inl (), Kleiman.SectionsOverLocalization.segreChart c0 c0 (Sum.inl ())⟩ = ∏ k, y ⟨k, c0 k⟩ := rfl
  set D : Unit ⊕ K → ℤ := IndefiniteRowSideFullHecke.Kleiman2.pullDeg (K₁ := Unit) β + c • baseDeg (Sum.inl ()) with hD
  have e3 : ∀ k : K, D (Sum.inr k) = β k := by
    intro k
    simp [hD, IndefiniteRowSideFullHecke.Kleiman2.pullDeg, baseDeg]
  have e4 : D (Sum.inl ()) = c := by
    simp [hD, IndefiniteRowSideFullHecke.Kleiman2.pullDeg, baseDeg]
  have hprod : (∏ k, segreJoin y ⟨k, Kleiman.SectionsOverLocalization.segreChart c0 c0 k⟩ ^ (-D k)) =
      ∏ k, y ⟨k, c0 k⟩ ^ (-(β k + c)) := by
    rw [Fintype.prod_sum_type]
    have hu1 : (∏ u : Unit, segreJoin y ⟨Sum.inl u, Kleiman.SectionsOverLocalization.segreChart c0 c0 (Sum.inl u)⟩ ^
        (-D (Sum.inl u))) = (∏ k, y ⟨k, c0 k⟩) ^ (-c) := by
      rw [Fintype.prod_unique]
      show segreJoin y ⟨Sum.inl (), Kleiman.SectionsOverLocalization.segreChart c0 c0 (Sum.inl ())⟩ ^ (-D (Sum.inl ())) = _
      rw [e2, e4]
    rw [hu1, ← Finset.prod_zpow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [e1, e3, ← zpow_add₀ (hc k)]
    congr 1
    ring
  rw [hprod] at hsum
  exact hsum

theorem generated_of_nef (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (d : ℕ) (α : K → ℤ)
    (hnz : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0)
    (hrel : FieldNumbers.relDim (KH.mIdealOver F y) = ((d : ℕ) : WithBot (WithTop ℤ)))
    (hnef : IsNef F y α) (t : ℚ) (ht : 0 < t) :
    ∃ (a' : ℕ) (m : ℤ), 1 ≤ a' ∧ (m : ℚ) = a' * t ∧ IsGenerated F y (a' • α + fun _ => m) := by
  obtain ⟨a', m, ha', hm, hva⟩ := kAt_all d F (Unit ⊕ K) _ Ω (segreJoin y) (Sum.inl ())
    (Kleiman.SectionsOverLocalization.SegreBase.proof F K ι Ω y hnz).1
    ((Kleiman.SectionsOverLocalization.SegreDim.proof F K ι Ω y hnz).trans hrel) (IndefiniteRowSideFullHecke.Kleiman2.pullDeg α)
    ((Kleiman.SectionsOverLocalization.SegreNef.proof Kleiman.SectionsOverLocalization.SegreDim.proof Kleiman.SectionsOverLocalization.SegreNum.proof
      F K ι Ω y hnz α).2 hnef) t ht
  obtain ⟨n, x', hx', hgen, -⟩ := hva
  have e : a' • IndefiniteRowSideFullHecke.Kleiman2.pullDeg (K₁ := Unit) α + m • baseDeg (Sum.inl ()) =
      IndefiniteRowSideFullHecke.Kleiman2.pullDeg (K₁ := Unit) (a' • α) + m • baseDeg (Sum.inl ()) := by
    congr 1
    funext k
    cases k <;> simp [IndefiniteRowSideFullHecke.Kleiman2.pullDeg, Pi.mul_apply, Pi.natCast_apply]
  rw [e] at hx' hgen
  refine ⟨a', m, ha', hm, n, x', fun j => ?_, generatesOver_segreJoin_twist y (a' • α) m x' hgen⟩
  have := hx' j
  rwa [Kleiman.SectionsOverLocalization.SegreTwist.proof F K ι Ω y hnz] at this

theorem kAmp : KH.KAmpStatement := by
  intro F _ K _ _ ι _ _ I V d α b a hI hV hnef hb ha
  classical
  have : V.IsPrime := hV.1.1
  have hVd := HilbertSamuel.KleimanNefF.isMultiProjPrime_dvr hV.1
  set y := Kleiman.SectionsOverLocalization.ModelGenericPoint.genPt (O := F) V
  have hy : KH.mIdealOver F y = V :=
    Kleiman.SectionsOverLocalization.ModelGenericPoint.mIdealOver_genPt V hVd.multiHomog
  have hnz : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := fun k => by
    obtain ⟨i, hi⟩ := hV.1.2.2 k
    exact ⟨i, (Kleiman.SectionsOverLocalization.ModelGenericPoint.genPt_ne_zero V _).2 hi⟩
  have hrel : FieldNumbers.relDim (KH.mIdealOver F y) = ((d : ℕ) : WithBot (WithTop ℤ)) := by
    rw [hy]
    exact (FieldNumbers.CutRegular.relDim_eq_natCast_iff V d).2 hV.2
  have hnef' : IsNef F y α := by
    intro W hW hle hW1
    rw [hy] at hle
    have hWF : IsProjVarF W 1 :=
      ⟨⟨hW.isPrime, (NumbersDVR.VocabMultiHomogIdeal.proof NumbersDVR.VocabMultiHomog.proof F K ι W).2
        hW.multiHomog, hW.relevant⟩, (FieldNumbers.CutRegular.relDim_eq_natCast_iff W 1).1 hW1⟩
    have h := hnef W hWF hle
    rwa [HilbertSamuel.KleimanNefF.eq_intNum hI 1 W _ hWF] at h
  have hb' : (0 : ℚ) < b := by exact_mod_cast hb
  have ha₀ : (0 : ℚ) < a := by exact_mod_cast ha
  obtain ⟨a', m, ha', hm, hgen⟩ :=
    generated_of_nef F K ι _ y d α hnz hrel hnef' ((a : ℚ) / (2 * b)) (by positivity)
  have hGV : KH.GeneratedV F V (a' • α + fun _ => m) := by
    have := Kleiman.SectionsOverLocalization.GeneratedCechTie.proof F K ι _ y _ hnz hgen
    rwa [hy] at this
  have hamp := ampleOfGenTwist F K ι V _ (a' * a) (2 * b) hV.1.2.1 hGV
    (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)))
  have hm' : (2 * (b : ℤ)) * m = a' * a := by
    have hq : (2 * (b : ℚ)) * m = a' * a := by
      rw [hm]
      field_simp
    exact_mod_cast hq
  have e : ((2 * b : ℕ) : ℤ) • (a' • α + fun _ => m) + (fun _ => ((a' * a : ℕ) : ℤ)) =
      (2 * a') • (b • α + fun _ => (a : ℤ)) := by
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply]
    push_cast
    linear_combination hm'
  rw [e] at hamp
  exact HilbertSamuel.ampleV_of_nsmul (by omega) hamp

end PositivityTheory.KAmp
end
end
