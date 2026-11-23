module

public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsChart
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsChartPointTrdeg
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsFibreCompDim
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsFibreCut
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsGenSecKer
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsOrd
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsSecPointSeparable
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Assembly
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.PAffineChartTrdeg
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PConeDimOfChowForm
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PIncIdealDim
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Assembly
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
public import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.ZariskisMainTheorem
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.MvPolynomial.Localization
public import Mathlib.RingTheory.QuasiFinite.Basic
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PFibreCompDim
public import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PGenSecKer
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PGenSecSeparable

-- Source module: GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PFibreClosedComponent

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial IsDedekindDomain

theorem FibreClosedComponent.proof : FibreClosedComponent.Statement := by
  intro O _ _ F _ _ _ n P W v hP hPO hW hWmax
  classical
  have := hP
  have : W.IsPrime := hW.1.1

  set mk : MvPolynomial (Fin n) O →+* MvPolynomial (Fin n) O ⧸ P := Ideal.Quotient.mk P with hmk_def
  have hmk : Function.Surjective mk := Ideal.Quotient.mk_surjective
  have hPW : P ≤ W := le_sup_left.trans hW.1.2
  have hvW : Ideal.map (C : O →+* MvPolynomial (Fin n) O) v.asIdeal ≤ W := le_sup_right.trans hW.1.2
  have hker : RingHom.ker mk = P := Ideal.mk_ker
  have hQprime : (W.map mk).IsPrime := Ideal.map_isPrime_of_surjective hmk (by rw [hker]; exact hPW)
  let Q : PrimeSpectrum (MvPolynomial (Fin n) O ⧸ P) := ⟨W.map mk, hQprime⟩
  have hcomapQ : (W.map mk).comap mk = W := by
    rw [Ideal.comap_map_of_surjective _ hmk, ← RingHom.ker_eq_comap_bot, hker, sup_eq_left.mpr hPW]
  have halg : algebraMap O (MvPolynomial (Fin n) O ⧸ P) = mk.comp C := by
    exact RingHom.ext fun _ => rfl

  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial (Fin n) O)
    (P ⊔ Ideal.map (C : O →+* MvPolynomial (Fin n) O) v.asIdeal)
  let U : Set (PrimeSpectrum (MvPolynomial (Fin n) O ⧸ P)) :=
    {q | ∀ W' ∈ (P ⊔ Ideal.map (C : O →+* MvPolynomial (Fin n) O) v.asIdeal).minimalPrimes,
      W' ≠ W → ¬ W' ≤ q.asIdeal.comap mk}
  have hU : IsOpen U := by
    have hUc : Uᶜ = ⋃ W' ∈ {W' | W' ∈ (P ⊔ Ideal.map (C : O →+* MvPolynomial (Fin n) O)
        v.asIdeal).minimalPrimes ∧ W' ≠ W},
        PrimeSpectrum.zeroLocus ((W'.map mk : Ideal (MvPolynomial (Fin n) O ⧸ P)) : Set _) := by
      ext q
      simp only [U, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_not, Set.mem_iUnion,
        PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe, Ideal.map_le_iff_le_comap, exists_prop,
        and_assoc]
    rw [← isClosed_compl_iff, hUc]
    exact Set.Finite.isClosed_biUnion (hfin.subset (by exact fun _ h => h.1))
      fun _ _ => PrimeSpectrum.isClosed_zeroLocus _
  have hiso : IsOpen (X := PrimeSpectrum.comap (algebraMap O (MvPolynomial (Fin n) O ⧸ P)) ⁻¹'
      {Q.comap (algebraMap O (MvPolynomial (Fin n) O ⧸ P))}) {⟨Q, rfl⟩} := by
    refine isOpen_induced_iff.mpr ⟨U, hU, ?_⟩
    ext ⟨q, hq⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hqU
      have hq' : q.asIdeal.comap (algebraMap O _) = Q.asIdeal.comap (algebraMap O _) :=
        congrArg PrimeSpectrum.asIdeal hq
      have hle : P ⊔ Ideal.map (C : O →+* MvPolynomial (Fin n) O) v.asIdeal ≤ q.asIdeal.comap mk := by
        refine sup_le ?_ ?_
        · intro x hx
          show mk x ∈ q.asIdeal
          rw [show mk x = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr hx]
          exact q.asIdeal.zero_mem
        · rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap, ← halg, hq', halg, ← Ideal.comap_comap]
          show v.asIdeal ≤ ((W.map mk).comap mk).comap C
          rw [hcomapQ, ← Ideal.map_le_iff_le_comap]
          exact hvW
      obtain ⟨W'', hW'', hW''le⟩ := Ideal.exists_minimalPrimes_le hle
      have hW''W : W'' = W := by
        by_contra hne
        exact hqU W'' hW'' hne hW''le
      rw [hW''W] at hW''le
      have heq : W = q.asIdeal.comap mk :=
        hWmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) hW''le
      apply Subtype.ext
      apply PrimeSpectrum.ext
      change q.asIdeal = W.map mk
      rw [heq, Ideal.map_comap_of_surjective _ hmk]
    · intro h
      obtain rfl : q = Q := congrArg Subtype.val h
      intro W' hW' hne hle
      change W' ≤ (W.map mk).comap mk at hle
      rw [hcomapQ] at hle
      exact hne (le_antisymm hle (hW.2 hW'.1 hle))
  have : Algebra.QuasiFiniteAt O Q.asIdeal :=
    (Algebra.quasiFiniteAt_iff_isOpen_singleton_fiber Q).mpr hiso

  obtain ⟨r, hrQ, hr, hm⟩ :=
    Algebra.zariskisMainProperty_iff.mp (Algebra.ZariskisMainProperty.of_finiteType (R := O) Q.asIdeal)
  have hr0 : r ≠ 0 := fun h => hrQ (h ▸ Q.asIdeal.zero_mem)
  have hDalg : ∀ d : MvPolynomial (Fin n) O ⧸ P, IsAlgebraic O d := by
    intro d
    obtain ⟨m, hm⟩ := hm d
    exact IsAlgebraic.of_mul (mem_nonZeroDivisors_of_ne_zero (pow_ne_zero m hr0))
      (hr.pow m).isAlgebraic hm.isAlgebraic

  have hIprime : (P.map (MvPolynomial.map (algebraMap O F) :
      MvPolynomial (Fin n) O →+* MvPolynomial (Fin n) F)).IsPrime := by
    let _ := MvPolynomial.algebraMvPolynomial (σ := Fin n) (R := O) (S := F)
    have hloc : IsLocalization ((nonZeroDivisors O).map (C : O →+* MvPolynomial (Fin n) O))
        (MvPolynomial (Fin n) F) := MvPolynomial.isLocalization _ _
    refine IsLocalization.isPrime_of_isPrime_disjoint
      ((nonZeroDivisors O).map (C : O →+* MvPolynomial (Fin n) O)) (MvPolynomial (Fin n) F) P hP ?_
    rw [Set.disjoint_left]
    rintro x hx hxP
    obtain ⟨c, hc, rfl⟩ := Submonoid.mem_map.mp hx
    have hcP : c ∈ P.comap (C : O →+* MvPolynomial (Fin n) O) := hxP
    rw [hPO, Ideal.mem_bot] at hcP
    exact nonZeroDivisors.ne_zero hc hcP

  let I := P.map (MvPolynomial.map (algebraMap O F) : MvPolynomial (Fin n) O →+* MvPolynomial (Fin n) F)
  let φ : (MvPolynomial (Fin n) O ⧸ P) →ₐ[O] (MvPolynomial (Fin n) F ⧸ I) :=
    Ideal.quotientMapₐ I (MvPolynomial.mapAlgHom (Algebra.ofId O F)) Ideal.le_comap_map
  have hX : ∀ i, IsIntegral F (Ideal.Quotient.mk I (X i)) := by
    intro i
    have h : Ideal.Quotient.mk I (X i) = φ (Ideal.Quotient.mk P (X i)) := by
      show _ = Ideal.Quotient.mk I (MvPolynomial.map (algebraMap O F) (X i))
      rw [MvPolynomial.map_X]
    rw [h]
    exact (((hDalg _).algHom φ).extendScalars (IsFractionRing.injective O F)).isIntegral
  have hint : ∀ x : MvPolynomial (Fin n) F ⧸ I, IsIntegral F x := by
    intro x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    induction p using MvPolynomial.induction_on with
    | C a => exact isIntegral_algebraMap
    | add p q hp hq => rw [map_add (f := _)]; exact hp.add hq
    | mul_X p i hp => rw [map_mul]; exact hp.mul (hX i)
  have : Algebra.IsIntegral F (MvPolynomial (Fin n) F ⧸ I) := ⟨hint⟩
  have hfield : IsField (MvPolynomial (Fin n) F ⧸ I) :=
    (Algebra.IsIntegral.isField_iff_isField (algebraMap F _).injective).mp (Field.toIsField F)
  exact ringKrullDim_eq_zero_of_isField hfield

end GroundTheory.Heights₂.Heights.Vertical
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PFiniteOrd

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

theorem FiniteOrd.proof : FiniteOrd.Statement := by
  intro R B _ _ _ _ _ _ b hb 𝔫
  have : IsNoetherianRing B := IsNoetherianRing.of_finite R B

  have hB : ringKrullDim B ≤ ringKrullDim R :=
    Order.krullDim_le_of_strictMono
      (fun p : PrimeSpectrum B ↦
        (⟨Ideal.comap (algebraMap R B) p.asIdeal, inferInstance⟩ : PrimeSpectrum R))
      (fun p q hpq ↦ Ideal.IsIntegral.comap_lt_comap (R := R) (A := B) hpq)
  have hS : ringKrullDim (Localization.AtPrime 𝔫.asIdeal) ≤ 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height 𝔫.asIdeal (Localization.AtPrime 𝔫.asIdeal)]
    refine Ideal.height_le_ringKrullDim_of_isPrime.trans (hB.trans ?_)
    rw [IsDiscreteValuationRing.ringKrullDim_eq_one R]
  have : Ring.KrullDimLE 1 (Localization.AtPrime 𝔫.asIdeal) :=
    Ring.krullDimLE_iff.mpr (by exact_mod_cast hS)
  have hbB : b ∈ nonZeroDivisors B := by
    refine mem_nonZeroDivisors_iff.mpr ⟨fun x hx ↦ ?_, fun x hx ↦ hb (by simpa [mul_comm, mul_zero] using hx)⟩
    exact hb (by simpa [mul_comm, mul_zero] using hx)
  have hbS : algebraMap B (Localization.AtPrime 𝔫.asIdeal) b ∈
      nonZeroDivisors (Localization.AtPrime 𝔫.asIdeal) :=
    IsLocalization.map_nonZeroDivisors_le 𝔫.asIdeal.primeCompl _ ⟨b, hbB, rfl⟩
  exact Ring.ord_ne_top hbS

end GroundTheory.Heights₂.Heights.Vertical
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.OfChartPointSecPointSpecChart

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

theorem FibreClosedComponent.full : FibreClosedComponent.Statement := FibreClosedComponent.proof
theorem FiniteOrd.full : FiniteOrd.Statement := FiniteOrd.proof
theorem FibreCompDim.full : FibreCompDim.Statement :=
  FibreCompDim.proof FibreClosedComponent.full FibreCut.full GenericFibreDrop.full

private theorem coneDim : GroundTheory.Heights₂.Heights.ConeDimOfChowForm.Statement :=
  GroundTheory.Heights₂.Heights.ConeDimOfChowForm.proof
    (GroundTheory.Heights₂.Heights.IncIdealDim.proof GroundTheory.Heights₂.Heights.IncidenceGeneric.full
      GroundTheory.Heights₂.Heights.GenericLinearTrdeg.full GroundTheory.Heights₂.Heights.AffineChartTrdeg.proof)
    GroundTheory.Heights₂.Heights.IncIdealPrime.full

theorem GenSecKer.full : GenSecKer.Statement := GenSecKer.proof SecAlgField.full coneDim

theorem ChowFormSectionVertical.of_chartPoint_secPoint_specChart
    (hTrdeg : ChartPointTrdeg.Statement) (hSep : SecPointSeparable.Statement)
    (hChart : SpecChart.Statement) : ChowFormSectionVertical.Statement :=
  ChowFormSectionVertical.of_remaining
    (GenSecSeparable.proof SecAlgFinite.full GenSecDomain.full hTrdeg hSep)
    FibreClosedComponent.full GenSecKer.full hChart FiniteOrd.full

end GroundTheory.Heights₂.Heights.Vertical
end
end
