module

public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.SectionBaseChangeOfBasis
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsEmbExt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelFormCompatBaseEmbedding
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BoundedAtPlaceOfIntegralCoverReadingStatement
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BddGood
public import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPins
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BddGoodOfBddAll
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormIntegralLatticeUnramifiedDescent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspidalSectionBoundedNonzeroMultipleStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralFramedPointBaseChangeStable
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinitePlaceValuationCompRingEquivStatement
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCuspFormsAllEmbeddingsOfInclusionReadingStatement
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.LeCovCoeff
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.IoOverLeftUnique
public import Formalism.LocalToGlobal.ProjectiveLattices.SpMapAlgHomId
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralValuesAlgebraicPointsIffValueNonnegStatement
public import Formalism.LocalToGlobal.ProjectiveLattices.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SpanSteps

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormIntegralLatticeUnramifiedDescentStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GoodPts
open GlobalTheory.SupDescent in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 100000 in
theorem _root_.GlobalTheory.T.cuspForm_integral_lattice_unramified_descent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ), p.Prime → (p : 𝓞 c.F) ∈ la.asIdeal → l.GoodAt p → ∀ (c' : Coeff l) (hle : c.F ≤ c'.F) (la' : HeightOneSpectrum (𝓞 c'.F)), (∀ x : c.F, vLa la' (incF c c' hle x) = vLa la x) → CuspBC hle U → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → FiniteDimensional c.F (cusp Xo c U a n) → ∀ f' ∈ cusp Xo c' (unfBC hle U) a n, BddAll Xo c' la' 1 f' → ∃ (m : ℕ) (as : Fin m → c'.F) (fs : Fin m → Rul Xo c), (∀ i, la'.valuation c'.F (as i) ≤ 1) ∧ (∀ i, fs i ∈ supSet Xo c la (cusp Xo c U a n)) ∧ IsBC hle f' as fs := by
  intro E _ _ _ H Dw l Xo c r U hU la p hp hpl hgood c' hle la' hv hBC a n hD _ f' hf' hb
  obtain ⟨m, as, fs, hfs, hIs⟩ := hBC a n f' hf'
  choose κ hκ0 hκ using fun i => GlobalTheory.T.cuspidal_section_bounded_nonzero_multiple E H Dw l Xo c r U hU la p hp hpl hgood a n (fs i) hD (hfs i)
  let : Algebra c.F c'.F := (incF c c' hle).toAlgebra
  have := liesOver (K := c.F) (K' := c'.F) hv
  obtain ⟨d, b, hb1, hb2⟩ := exists_residue_basis (la := la) (la' := la')
  choose x ρ hρ hx using fun i => exists_approx (K := c.F) (K' := c'.F) hv hb2 (as i) (hκ0 i)
  let F : Fin d → Rul Xo c := fun j => ∑ i, x i j • fs i
  have hF : ∀ j, F j ∈ cusp Xo c U a n := fun j => Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hfs i)
  have hG : ∀ i, κ i • fs i ∈ supSet Xo c la (cusp Xo c U a n) := fun i =>
    ⟨Submodule.smul_mem _ _ (hfs i), (GlobalTheory.GoodPtsModel.bddAll_iff_smul _ _).1 (hκ i)⟩
  have key : ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra c'.F S] (h : AlgOver c c' hle S) (y : FrPt Xo c' S),
      evR Xo c' f' y = ∑ j, algebraMap c'.F S (b j) * evR Xo c (F j) (y.res hle h) +
        ∑ i, algebraMap c'.F S (ρ i) * evR Xo c (κ i • fs i) (y.res hle h) := by
    intro S _ _ _ h y
    have h' : ∀ t : c.F, algebraMap c'.F S (algebraMap c.F c'.F t) = algebraMap c.F S t := h
    have hs : ∀ i, evR Xo c (κ i • fs i) (y.res hle h) = algebraMap c.F S (κ i) * evR Xo c (fs i) (y.res hle h) :=
      fun i => evalAt_smul _ _ _ _ _
    rw [hIs S h y]
    simp only [F, evR_sum, hs, Finset.mul_sum]
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hx i]
    simp only [map_add (f := _), map_sum, map_mul, h', add_mul, Finset.sum_mul, mul_assoc]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  refine ⟨d + m, Fin.append (fun j => (b j : c'.F)) ρ, Fin.append F fun i => κ i • fs i, fun i => ?_, fun i => ?_, ?_⟩
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [Fin.append_left]; exact la'.valuation_le_one (b j)
    · rw [Fin.append_right]; exact hρ j
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    swap
    · rw [Fin.append_right]; exact hG j
    rw [Fin.append_left]
    refine ⟨hF j, fun T io e ho y hy => ?_⟩
    rw [map_one, one_mul]
    refine inV_of_forall_emb (K := c.F) (K' := c'.F) hb1 hy ho (fun j => evI y (F j)) ?_ j
    intro T' i e' σ e'' he' hi hT' hσ ho'
    obtain ⟨y₁, φ, hφ, hmap⟩ := GlobalTheory.IntFrBaseChange.exists_intFr_baseChange E H Dw l Xo c T T' io y i e' he' hi
    obtain ⟨y₂, hy₂⟩ := exists_intFr_ext hle (io := i.comp io) σ hσ y₁
    have hi' : ∀ t : T.Fr, vV T'.V (i t) = (e' : ℤ) * vV T.V t := fun t => by
      by_cases h : t = 0
      · subst h; simp [vV]
      · exact hi t h
    have h1 := hb T' σ e'' ho' y₂ hT'
    rw [map_one, one_mul] at h1
    have h2 : InV T' (∑ k, σ (ρ k) * evI y₁ (κ k • fs k)) := Subring.sum_mem _ fun k _ => by
      have h3 := (hG k).2 T' _ _ (ho.bc i he' hi') y₁ hT'
      rw [map_one, one_mul] at h3
      exact Subring.mul_mem _ ((GlobalTheory.GoodPtsModel.inV_iff_val T' _).2
        ((val_le_one_iff ho' _).2 (hρ k))) h3
    have h4 : ∀ j, i (evI y (F j)) = evI y₁ (F j) := fun j => by
      let := io.toAlgebra
      let := (i.comp io).toAlgebra
      exact (DFunLike.congr_fun hφ _).symm.trans
        (GlobalTheory.FlagTan.evR_frMap (cusp_le_sec Xo c U a n (hF j)).1 hmap).symm
    have h5 : evI y₂ f' = ∑ j, σ (b j) * evI y₁ (F j) + ∑ k, σ (ρ k) * evI y₁ (κ k • fs k) := by
      let := (i.comp io).toAlgebra
      let := σ.toAlgebra
      have := key T'.Fr hσ y₂.1
      rw [hy₂] at this
      exact this
    simp only [h4]
    rw [eq_sub_of_add_eq h5.symm]
    exact Subring.sub_mem _ h1 h2
  · intro S _ _ _ h y
    rw [key S h y, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniquePlaceBelowOfUnramifiedPlaceOverPrime

section

@[expose] public section

open NumberField IsDedekindDomain

namespace GlobalTheory.InertiaEigenvalues.UnramPlace

theorem exists_place_below : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] (φ : K →+* L) (l : ℕ), l.Prime → ∀ la : HeightOneSpectrum (𝓞 L), ((l : ℕ) : 𝓞 L) ∈ la.asIdeal → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.UnramAt φ {la} → ∃ p : HeightOneSpectrum (𝓞 K), GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.below φ {la} = {p} ∧ ((l : ℕ) : 𝓞 K) ∈ p.asIdeal ∧ ∀ x : K, la.valuation L (φ x) = p.valuation K x := by
  intro K L _ _ _ _ φ l _ la hl hun
  letI : Algebra K L := φ.toAlgebra
  have hmap : RingOfIntegers.mapRingHom φ = algebraMap (𝓞 K) (𝓞 L) := by
    ext x; rfl
  refine ⟨la.under (𝓞 K), ?_, ?_, ?_⟩
  · ext q
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.below, Set.mem_singleton_iff, exists_eq_left, Set.mem_setOf_eq]
    rw [hmap]
    exact ⟨fun h => HeightOneSpectrum.ext h, fun h => h ▸ rfl⟩
  · show ((l : ℕ) : 𝓞 K) ∈ la.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L))
    rw [Ideal.mem_comap, map_natCast]
    exact hl
  · intro x
    have hu := hun la rfl
    rw [hmap] at hu
    have : la.asIdeal.LiesOver (la.under (𝓞 K)).asIdeal := ⟨rfl⟩
    have he : (la.under (𝓞 K)).asIdeal.ramificationIdx' la.asIdeal = 1 := by
      refine Ideal.ramificationIdx'_spec ?_ ?_
      · rw [pow_one]; exact Ideal.map_comap_le
      · exact hu
    have h := HeightOneSpectrum.valuation_liesOver L (la.under (𝓞 K)) la x
    rw [← Ideal.ramificationIdx'_eq_ramificationIdx _ _ (la.under (𝓞 K)).ne_bot, he, pow_one] at h
    exact h.symm

end GlobalTheory.InertiaEigenvalues.UnramPlace
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniquePlaceBelowOfUnramifiedPlaceOverPrimeStatement

section

@[expose] public section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.exists_unique_place_below_of_unramified_place_over_prime : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] (φ : K →+* L) (l : ℕ), l.Prime → ∀ la : HeightOneSpectrum (𝓞 L), ((l : ℕ) : 𝓞 L) ∈ la.asIdeal → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.UnramAt φ {la} → ∃ p : HeightOneSpectrum (𝓞 K), GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.below φ {la} = {p} ∧ ((l : ℕ) : 𝓞 K) ∈ p.asIdeal ∧ ∀ x : K, la.valuation L (φ x) = p.valuation K x := by
  first | exact @GlobalTheory.InertiaEigenvalues.UnramPlace.exists_place_below | exact GlobalTheory.InertiaEigenvalues.UnramPlace.exists_place_below | (intros; apply GlobalTheory.InertiaEigenvalues.UnramPlace.exists_place_below <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumAdelicReadingEqOfTwoBaseChangeDecompsOnCover

section

@[expose] public section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverBCRead

theorem evR_sum_eq {D : D7} (T : CoreJ D) (j : ℕ) (σ : T.Q.c.F →+* ℂ) (C : Cover T j σ)
    (hσ : C.σ₂.comp C.inc = σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) {m m' : ℕ} (x : Fin m → C.c'.F)
    (f : Fin m → T.R j) (as : Fin m' → C.c'.F) (fs : Fin m' → T.R j)
    (hf : ∀ b, f b ∈ sec (T.Q.Xo j) T.Q.c a n)
    (hBC : IsBC C.hle (∑ b, x b • GlobalTheory.FieldBC.rulBC C.hle (f b)) as fs)
    (y : FrPt (T.Q.Xo j) T.Q.c (CAt σ)) :
    (∑ b, C.σ₂ (C.d.eF (x b)) * toC (evR (T.Q.Xo j) T.Q.c (f b) y)) =
      ∑ i, C.σ₂ (C.d.eF (as i)) * toC (evR (T.Q.Xo j) T.Q.c (fs i) y) := by
  letI : Algebra C.c'.F (CAt σ) := (C.σ₂.comp (C.d.eF : C.c'.F →+* C.d.c₂.F)).toAlgebra
  have hA : AlgOver T.Q.c C.c' C.hle (CAt σ) := by
    intro c0
    show C.σ₂ (C.d.eF (incF T.Q.c C.c' C.hle c0)) = σ c0
    exact RingHom.congr_fun hσ c0
  have h1 := hBC (CAt σ) hA (FrPt.ext C.hle hA y)
  rw [Formalism.L2.Pj.evR_sum_smul] at h1
  simp only [GlobalTheory.FieldBCModel.evR_rulBC C.hle (hf _).1 hA, FrPt.res_ext] at h1
  exact h1

theorem phiJ_sum_eq_of_isBC : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (σ : T.Q.c.F →+* ℂ) (C : Cover T j σ), C.σ₂.comp C.inc = σ → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (m m' : ℕ) (x : Fin m → C.c'.F) (f : Fin m → T.R j) (as : Fin m' → C.c'.F) (fs : Fin m' → T.R j), (∀ b, f b ∈ sec (T.Q.Xo j) T.Q.c a n) → IsBC C.hle (∑ b, x b • GlobalTheory.FieldBC.rulBC C.hle (f b)) as fs → ∑ b, C.σ₂ (C.d.eF (x b)) • T.phiJ j σ a (f b) = ∑ i, C.σ₂ (C.d.eF (as i)) • T.phiJ j σ a (fs i) := by
  intro D T j σ C hσ a n m m' x f as fs hf hBC
  have key : (∑ b, C.σ₂ (C.d.eF (x b)) • rdU (T.U j σ) (f b) : FDSec (T.U j σ).X) =
      ∑ i, C.σ₂ (C.d.eF (as i)) • rdU (T.U j σ) (fs i) := by
    funext k z
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    by_cases h : z ∈ ((T.U j σ).X k).dom
    · simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, dif_pos h]
      exact evR_sum_eq T j σ C hσ a n x f as fs hf hBC ((T.U j σ).un k ⟨z, h⟩)
    · simp [rdU, dif_neg h]
  let L : FDSec (T.U j σ).X →ₗ[ℂ] (GA D (T.V j σ) → ℂ) := (lieFac (T.Q.Dw j) (xiR D) a : ℂ) •
    adel (T.V j σ) (T.dict j σ) (muPin (T.V j σ) (T.dict j σ) (T.mu j σ) (T.cE j σ))
  have e : ∀ g : T.R j, T.phiJ j σ a g = L (rdU (T.U j σ) g) := fun _ => rfl
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [e, ← map_smul, ← map_sum, key]

end GlobalTheory.CoverBCRead
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumAdelicReadingEqOfTwoBaseChangeDecompsOnCoverStatement

section

@[expose] public section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.sum_adelicReading_eq_of_two_baseChange_decomps_on_cover : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (σ : T.Q.c.F →+* ℂ) (C : Cover T j σ), C.σ₂.comp C.inc = σ → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (m m' : ℕ) (x : Fin m → C.c'.F) (f : Fin m → T.R j) (as : Fin m' → C.c'.F) (fs : Fin m' → T.R j), (∀ b, f b ∈ sec (T.Q.Xo j) T.Q.c a n) → IsBC C.hle (∑ b, x b • GlobalTheory.FieldBC.rulBC C.hle (f b)) as fs → ∑ b, C.σ₂ (C.d.eF (x b)) • T.phiJ j σ a (f b) = ∑ i, C.σ₂ (C.d.eF (as i)) • T.phiJ j σ a (fs i) := by
  first | exact @GlobalTheory.CoverBCRead.phiJ_sum_eq_of_isBC | exact GlobalTheory.CoverBCRead.phiJ_sum_eq_of_isBC | (intros; apply GlobalTheory.CoverBCRead.phiJ_sum_eq_of_isBC <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedDescentIntegralFormsOnePlace

section

@[expose] public section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

namespace GlobalTheory.DescLoc

theorem holSub0_of_cusp : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ T.cuspA j a n, rdU (T.U j T.σ₀) f ∈ holSub0 (T.U j T.σ₀).X (laU (T.U j T.σ₀) a n) := by
  intro D T j a n f hf
  exact ReciprocityTheory.ChartRestriction.G.PullbackSections.rdC_mem_holSub0 T.good_σ₀ a n ⟨f, hf⟩

theorem desc_loc : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), VStd D i → ∀ hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i T.σ₀ hV → ∀ l : ℕ, l.Prime → ∀ C : Cover T ((i : ℕ) + 1) T.σ₀, GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsTowerCover T i l C → C.IsPinned (wtA (κ i)) (κ i).n → ∀ la : HeightOneSpectrum (𝓞 C.d.c₂.F), ((l : ℕ) : 𝓞 C.d.c₂.F) ∈ la.asIdeal → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.UnramAt C.inc {la} → ∀ φ ∈ C.intForms (wtA (κ i)) (κ i).n {la}, (∀ k ∈ T.Kf ((i : ℕ) + 1) T.σ₀, ∀ h, φ (h * k) = φ h) → ∀ (m : ℕ) (x : Fin m → C.d.c₂.F) (ψ : Fin m → (GA D (T.V ((i : ℕ) + 1) T.σ₀) → ℂ)), (∀ a, ψ a ∈ baseForms T ((i : ℕ) + 1) T.σ₀ (wtA (κ i)) (κ i).n) → φ = ∑ a, C.σ₂ (x a) • ψ a → ∃ (m' : ℕ) (x' : Fin m' → ℂ) (ψ' : Fin m' → (GA D (T.V ((i : ℕ) + 1) T.σ₀) → ℂ)), (∀ a, GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IntVal C.σ₂ {la} (x' a)) ∧ (∀ a, ψ' a ∈ baseInt T ((i : ℕ) + 1) T.σ₀ (wtA (κ i)) (κ i).n (GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.below C.inc {la})) ∧ φ = ∑ a, x' a • ψ' a := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hL hLev hGrp hFam hMod hThP hTie i hVstd hV hFP l hl C hC hPin la hla hUn φ hφ hKf m x ψ hψ hsum
  have hj : InR D ((i : ℕ) + 1) := inR i
  have hU := hC.1
  choose f hf hfψ using hψ
  have hfc : ∀ b, f b ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n := fun b =>
    GlobalTheory.T.mem_cuspForms_allEmbeddings_of_inclusion_reading D T hL _ hj (κ i) (GlobalTheory.AdTh.lastPos_of_kapIs hTie.kap i) (f b) (hf b).1 (hf b).2
  obtain ⟨p, hbelow, hlp, hval⟩ := GlobalTheory.T.exists_unique_place_below_of_unramified_place_over_prime _ _ C.inc l hl la hla hUn
  obtain ⟨la', hla'⟩ := GlobalTheory.T.exists_finitePlace_valuation_comp_ringEquiv _ _ C.d.eF.toRingEquiv la
  let x' : Fin m → C.c'.F := fun b => C.d.eF.symm (x b)
  have hx' : ∀ b, C.d.eF (x' b) = x b := fun b => C.d.eF.apply_symm_apply (x b)
  have hφ' : (∑ b, C.σ₂ (C.d.eF (x' b)) • T.phiJ ((i : ℕ) + 1) T.σ₀ (wtA (κ i)) (f b)) ∈
      C.intForms (wtA (κ i)) (κ i).n {la} := by
    simp only [hx', hfψ]
    rw [← hsum]
    exact hφ
  have hint := GlobalTheory.T.bounded_at_place_of_integral_cover_reading D T hL _ hj T.σ₀ T.good_σ₀ C hU (wtA (κ i)) (κ i).n (dom_wtA (κ i)) hPin la la'
    (fun y => hla' y) m x' f (fun b => (hf b).1) hφ'
  have hmem : (∑ b, x' b • GlobalTheory.FieldBC.rulBC C.hle (f b)) ∈
      cusp (T.Q.Xo ((i : ℕ) + 1)) C.c' (unfBC C.hle (T.U ((i : ℕ) + 1))) (wtA (κ i)) (κ i).n :=
    Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _
      ((GlobalTheory.FieldBC.rulBC_cusp _ _ _ _ _ _ _ C.hle _ (T.U ((i : ℕ) + 1)) _ _ (f b) (hf b).1).2.2 (hfc b))
  have hgood : T.Q.l.GoodAt l :=
    Formalism.L2.Pj.goodAt_of_two_primes hL.pins.2.1.1 (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne l hl
  have hvLa : ∀ y : T.Q.c.F, vLa la' (incF T.Q.c C.c' C.hle y) = vLa p y := fun y => by
    unfold vLa
    rw [hla', ← hval]
    rfl
  obtain ⟨m', as, fs, has, hfs, hBC⟩ := GlobalTheory.T.cuspForm_integral_lattice_unramified_descent _ _ _ _ _ _ _ (T.U ((i : ℕ) + 1)) (hL.unf _ hj) p l hl hlp hgood
    C.c' C.hle la' hvLa (GlobalTheory.SecFieldChange.cuspBC_holds C.hle _) (wtA (κ i)) (κ i).n (dom_wtA (κ i))
    (hL.cuspFD _ hj _ _ (dom_wtA (κ i))) _ hmem hint
  refine ⟨m', fun k => C.σ₂ (C.d.eF (as k)), fun k => T.phiJ ((i : ℕ) + 1) T.σ₀ (wtA (κ i)) (fs k), ?_, ?_, ?_⟩
  · intro k
    refine ⟨C.d.eF (as k), rfl, fun q hq => ?_⟩
    obtain rfl := Set.mem_singleton_iff.1 hq
    exact (hla' (as k)).symm.trans_le (has k)
  · intro k
    rw [hbelow]
    refine ⟨fs k, ⟨(cusp_le_sec _ _ _ _ _ (hfs k).1), holSub0_of_cusp D T _ _ _ (fs k) (hfs k).1, ?_⟩, rfl⟩
    intro q hq v hv
    obtain rfl := Set.mem_singleton_iff.1 hq
    exact (GlobalTheory.T.integral_values_algebraic_points_iff_value_nonneg _ _ _ _ _ _ _ (fs k)).1 (hfs k).2 v hv
  · rw [hsum]
    have e := GlobalTheory.T.sum_adelicReading_eq_of_two_baseChange_decomps_on_cover D T _ T.σ₀ C hU.2.2.1 (wtA (κ i)) (κ i).n m m' x' f as fs (fun b => (hf b).1) hBC
    simp only [hx', hfψ] at e
    exact e

end GlobalTheory.DescLoc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedDescentIntegralFormsOnePlaceStatement

section

@[expose] public section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.unramified_descent_integral_forms_one_place : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), VStd D i → ∀ hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i T.σ₀ hV → ∀ l : ℕ, l.Prime → ∀ C : Cover T ((i : ℕ) + 1) T.σ₀, GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsTowerCover T i l C → C.IsPinned (wtA (κ i)) (κ i).n → ∀ la : HeightOneSpectrum (𝓞 C.d.c₂.F), ((l : ℕ) : 𝓞 C.d.c₂.F) ∈ la.asIdeal → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.UnramAt C.inc {la} → ∀ φ ∈ C.intForms (wtA (κ i)) (κ i).n {la}, (∀ k ∈ T.Kf ((i : ℕ) + 1) T.σ₀, ∀ h, φ (h * k) = φ h) → ∀ (m : ℕ) (x : Fin m → C.d.c₂.F) (ψ : Fin m → (GA D (T.V ((i : ℕ) + 1) T.σ₀) → ℂ)), (∀ a, ψ a ∈ baseForms T ((i : ℕ) + 1) T.σ₀ (wtA (κ i)) (κ i).n) → φ = ∑ a, C.σ₂ (x a) • ψ a → ∃ (m' : ℕ) (x' : Fin m' → ℂ) (ψ' : Fin m' → (GA D (T.V ((i : ℕ) + 1) T.σ₀) → ℂ)), (∀ a, GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IntVal C.σ₂ {la} (x' a)) ∧ (∀ a, ψ' a ∈ baseInt T ((i : ℕ) + 1) T.σ₀ (wtA (κ i)) (κ i).n (GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.below C.inc {la})) ∧ φ = ∑ a, x' a • ψ' a := by
  first | exact @GlobalTheory.DescLoc.desc_loc | exact GlobalTheory.DescLoc.desc_loc | (intros; apply GlobalTheory.DescLoc.desc_loc <;> assumption)
end
end
