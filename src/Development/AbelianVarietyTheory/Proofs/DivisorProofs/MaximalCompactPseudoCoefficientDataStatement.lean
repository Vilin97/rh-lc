module

public import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HarishChandraModulesIndefiniteUnitaryGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointDetOnCompactTorus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointDetTraceClassFunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasimirScalarStableSumSpace
public import Development.AbelianVarietyTheory.Definitions.Divisors.VdmSplit
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CARUnit
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CsqDdPt
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.LayerLeGeneratedTensorFock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapConditionsOfLargeGaps
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactDiscreteSeriesOwnType
public import Development.AbelianVarietyTheory.Definitions.Divisors.DatumEquiv
import Mathlib.Tactic.Linter.HaveILetI
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Arbitrary
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.BridgeExpK
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EquivSigLamOfIsDS
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.ExistsKhwGenSubOfKType
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.PropsEquiv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvConjTransposeMem
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.CoordSpan
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.Finiteness.Lattice
import Mathlib.Tactic.Linter.Style
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.ActDiagMemOfWK
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraWeightIntegralDominant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightKernelLowestType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntertwinerPreservesHighestWeight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrrepAveragesFinDimSmoothOfKTypesAndPolyAverages
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaxCompactPolynomialBlockTimesConjDetPower
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModeMatrixDetEqAdjointDet
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIrreducibleCharacterUnitaryMaxCompactEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolyCoefIrrepHasDerivedAction
import Mathlib.Analysis.InnerProductSpace.Trace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrIdxProof2
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupertraceCarriedByDiracKernel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceEqOfMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TracePairingNonzeroIntertwiner
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.KoszulLowersPower
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylFormulaCompactTorusIdentityOfIngredients
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapConditionsOfLargeGaps

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasimirValueHighestWeightCoordinates

section

@[expose] public section

noncomputable section

open Finset ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap

namespace GlobalTheory.PsCo.PcEF

open GlobalTheory.PsCo.PcEG

theorem casimirValue_highestWeightCoordinates : CasCoord := by
  intro n ε lam M _ _ E hE z hz hD s
  have hE' := eT_isGlRep (n := n) hE
  have h2 := LinearMap.congr_fun (two_D_sq hE' cpT_cmT_isCAR (eT_commutesCAR E) ε) z
  have hK := casimirK_khwVec_compact ε (diagE_compact hE' cpT_cmT_isCAR (eT_commutesCAR E) ε) hz
  have hs : ∑ a, ((rhoHol ε a : ℝ) : ℂ) • diagE ε (eT E) cpT cmT a a z =
      ((dot (rhoHol ε) (gaW ε lam) : ℝ) : ℂ) • z := by
    simp only [dot, Complex.ofReal_sum, Complex.ofReal_mul, sum_smul, hz.1, smul_smul]
  have h0 : ((2 : ℂ) • ((dOp ε (eT E) cpT + dOp' ε (eT E) cmT) * (dOp ε (eT E) cpT + dOp' ε (eT E) cmT))) z = 0 := by
    rw [LinearMap.smul_apply, mul_apply_eq_comp]
    have : (dOp ε (eT E) cpT + dOp' ε (eT E) cmT) z = 0 := hD
    rw [this, map_zero, smul_zero]
  rw [h0] at h2
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.neg_apply, LinearMap.smul_apply,
    LinearMap.sum_apply, hK, hs] at h2
  have hid := khw_real_identity ε (lam - rhoC ε)
  have hg : lam - rhoC ε + rhoHol ε = gaW ε lam := rfl
  have hl : lam - rhoC ε + rhoC ε = lam := sub_add_cancel _ _
  rw [hg, hl] at hid
  have hc : casimir (eT (n := n) E) z = ((casVal lam : ℝ) : ℂ) • z := by
    have e : casimir (eT (n := n) E) z =
        ((nsq (gaW ε lam + rhoC ε) - nsq (rhoC ε) : ℝ) : ℂ) • z -
          (2 : ℂ) • (((dot (rhoHol ε) (gaW ε lam) : ℝ) : ℂ) • z) := by
      linear_combination (norm := module) h2
    rw [e, casVal, ← hid]
    simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_ofNat, sub_smul, smul_smul]
  have hcoord := congrArg (tco s) hc
  rw [TRGap.casimir_eT, tco_map_left] at hcoord
  simpa only [tco, map_smul] using hcoord

end GlobalTheory.PsCo.PcEF
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqDiscreteSeriesOfLowestKTypeCasimir

section

@[expose] public section

noncomputable section

open ReciprocityTheory.ChartRestriction.DS

namespace GlobalTheory.PsCo.PcEF

theorem eq_discreteSeries_of_lowestKType_casimir : DatumEquiv := by
  intro n ε lam hgap H _ _ _ σ hσ hirr V hV hV0 hc X _ _ D hD
  haveI : CompleteSpace X := hD.1
  have hσD : IsURepOn (UJset ε) D := hD.2.2.1
  have hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v :=
    kStable_of_isKStableSub hσ (isDerivedOn_smE hσ) V hV.1 hV.2.1
  obtain ⟨V', hV', hV0', hVK', hc'⟩ := arb_datum hD (casOnSmooth_of_isDS hD hgap)
  have htop := data_closGen_eq_top hgap hσ (isDerivedOn_smE hσ) hV hc hVK hirr hV0
  have htop' := data_closGen_eq_top hgap hσD (isDerivedOn_smE hσD) hV' hc' hVK' hD.2.2.2.1 hV0'
  obtain ⟨U, hU⟩ := data_unitary_equiv hgap hσ (isDerivedOn_smE hσ) hV hc hVK hV0
    hσD (isDerivedOn_smE hσD) hV' hc' hVK' hV0'
  refine ⟨((LinearIsometryEquiv.ofTop _ _ htop).symm.trans U).trans (LinearIsometryEquiv.ofTop _ _ htop'),
    fun g hg x => ?_⟩
  simp only [LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.ofTop_apply]
  apply hU g hg
  simp only [LinearIsometryEquiv.ofTop_symm_apply_coe]

end GlobalTheory.PsCo.PcEF
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockCoordinatesSpanFiniteDimensional

section

@[expose] public section

noncomputable section

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap

namespace GlobalTheory.PsCo.PcEF

theorem fockCoordinates_span_finiteDimensional (n : ℕ) (ε : Fin n → Bool) (M : Type)
    [NormedAddCommGroup M] [InnerProductSpace ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    (Z : Submodule ℂ (TensorProduct ℂ M (Fock n))) (hZ : FiniteDimensional ℂ Z)
    (hK : IsKStableSub ε (diagE ε (eT E) cpT cmT) Z) :
    FiniteDimensional ℂ (coordSpan Z) ∧ IsKStableSub ε E (coordSpan Z) := by
  have hle : coordSpan Z ≤ ⨆ s : Finset (Fin (n * n)), Z.map (tcoef (M := M) ((fockBasis n).coord s)) := by
    refine Submodule.span_le.2 ?_
    rintro v ⟨s, y, hy, rfl⟩
    exact (le_iSup (fun s : Finset (Fin (n * n)) => Z.map (tcoef (M := M) ((fockBasis n).coord s))) s)
      (Submodule.mem_map_of_mem hy)
  refine ⟨Submodule.finiteDimensional_of_le hle, ?_⟩
  intro a b hab v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, y, hy, rfl⟩ := hx
    let X := Matrix.single a b (1 : ℂ)
    have e := tco_actDiag (ε := ε) E X y s
    simp only [X, TRGap.actM_single'] at e
    show E a b (tcoef ((fockBasis n).coord s) y) ∈ coordSpan Z
    rw [eq_sub_of_add_eq e.symm, tcoef_eq_sum ((fockBasis n).coord s ∘ₗ sgX ε X) y]
    refine Submodule.sub_mem _ (Submodule.subset_span ⟨s, _, hK a b hab y hy, rfl⟩) ?_
    refine Submodule.sum_mem _ fun s' _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨s', y, hy, rfl⟩)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

end GlobalTheory.PsCo.PcEF
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolyOnKConj

section

@[expose] public section

noncomputable section

open MvPolynomial
open GlobalTheory.PsCo.Pc1 (Mat Poly ev)
open scoped ComplexConjugate InnerProductSpace

namespace GlobalTheory.PsCo.PcEF

def conjPoly (n : ℕ) : Poly n →+* Poly n :=
  (rename (Sum.swap : (Fin n × Fin n) ⊕ (Fin n × Fin n) → _)).toRingHom.comp (map (starRingEnd ℂ))

theorem ev_conjPoly {n : ℕ} (g : Mat n) (P : Poly n) : ev g (conjPoly n P) = conj (ev g P) := by
  have h : (ev g).comp (conjPoly n) = (starRingEnd ℂ).comp (ev g) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [conjPoly, ev]
    · intro i
      rcases i with x | x
      · simp [conjPoly, ev]
      · simp [conjPoly, ev]
  exact congrArg (fun φ : Poly n →+* ℂ => φ P) h

theorem polyOnK_conj {n : ℕ} {ε : Fin n → Bool} {f : Mat n → ℂ} (hf : PolyOnK ε f) :
    PolyOnK ε fun k => conj (f k) := by
  obtain ⟨P, hP⟩ := hf
  exact ⟨conjPoly n P, fun k hk => by dsimp only; rw [ev_conjPoly, hP k hk]⟩

theorem polyOnK_sum {n : ℕ} {ε : Fin n → Bool} {ι : Type} (s : Finset ι) (f : ι → Mat n → ℂ)
    (hf : ∀ i ∈ s, PolyOnK ε (f i)) : PolyOnK ε fun k => ∑ i ∈ s, f i k := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun k _ => by simp⟩
  | insert a s ha ih =>
    obtain ⟨P, hP⟩ := hf a (Finset.mem_insert_self a s)
    obtain ⟨Q, hQ⟩ := ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
    exact ⟨P + Q, fun k hk => by dsimp only at hQ ⊢; rw [Finset.sum_insert ha, map_add (f := _), hP k hk, hQ k hk]⟩

theorem trPoly : TrPoly := by
  intro n ε W _ _ _ T hT
  apply polyOnK_conj
  have e : trK T = fun k => ∑ i, ⟪(stdOrthonormalBasis ℂ W) i, T k ((stdOrthonormalBasis ℂ W) i)⟫_ℂ := by
    funext k
    simp only [trK, LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℂ W)]
    rfl
  rw [e]
  exact polyOnK_sum _ _ fun i _ => hT _ _

end GlobalTheory.PsCo.PcEF
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryRepUpqMatrixFunction

section

@[expose] public section

section

noncomputable section

namespace GlobalTheory.PsCo.PcEF.MatrixRepresentation

variable {n : ℕ} (ε : Fin n → Bool) {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X]

abbrev mat (g : Formalism.REAL.UJ ε) : Matrix (Fin n) (Fin n) ℂ :=
  ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)

theorem mat_injective : Function.Injective (mat ε) := fun _ _ h => Subtype.ext (Units.ext h)

def rep (π : Formalism.REAL.UJ ε →* (X →L[ℂ] X)) (x : Matrix (Fin n) (Fin n) ℂ) : X →L[ℂ] X := by
  classical exact if h : ∃ g, mat ε g = x then π h.choose else 1

theorem rep_mat (π : Formalism.REAL.UJ ε →* (X →L[ℂ] X)) (g : Formalism.REAL.UJ ε) : rep ε π (mat ε g) = π g := by
  have h : ∃ g', mat ε g' = mat ε g := ⟨g, rfl⟩
  rw [rep, dite_eq_left h, mat_injective ε h.choose_spec]

theorem range_mat : Set.range (mat ε) = Formalism.MainNotions.S.UJset ε := (Formalism.REAL.isClosedEmbeddingMatrix n ε).2

theorem mat_mem (g : Formalism.REAL.UJ ε) : mat ε g ∈ Formalism.MainNotions.S.UJset ε := range_mat ε ▸ ⟨g, rfl⟩

theorem exists_mat {x : Matrix (Fin n) (Fin n) ℂ} (hx : x ∈ Formalism.MainNotions.S.UJset ε) : ∃ g, mat ε g = x := by
  rw [← range_mat ε] at hx; exact hx

theorem isEmbedding_mat : Topology.IsEmbedding (mat ε) := (Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isEmbedding

end GlobalTheory.PsCo.PcEF.MatrixRepresentation

namespace GlobalTheory.PsCo.PcEF

open GlobalTheory.PsCo.PcEF.MatrixRepresentation

theorem unitaryRep_upq_matrixFunction : MatRep := by
  intro n ε U _ _ π hπ hi
  refine ⟨rep ε π, ⟨⟨?_, fun a ha b hb => ?_⟩, fun a ha v => ?_, fun v => ?_⟩, fun S hS hinv => ?_, fun g => rep_mat ε π g⟩
  · have h1 : mat ε 1 = 1 := rfl
    rw [← h1, rep_mat, map_one]
  · obtain ⟨g, rfl⟩ := exists_mat ε ha
    obtain ⟨h, rfl⟩ := exists_mat ε hb
    have hm : mat ε g * mat ε h = mat ε (g * h) := rfl
    rw [hm, rep_mat, rep_mat, rep_mat, map_mul]
    rfl
  · obtain ⟨g, rfl⟩ := exists_mat ε ha
    rw [rep_mat]
    exact hπ.norm_apply g v
  · have hr : Formalism.MainNotions.S.UJset ε = Set.range (mat ε) := (range_mat ε).symm
    show ContinuousOn (fun g => rep ε π g v) (Formalism.MainNotions.S.UJset ε)
    rw [hr, continuousOn_iff_continuous_domRestrict]
    let E := (isEmbedding_mat ε).toHomeomorph
    have hE : ∀ y, (fun g => π g v) (E.symm y) = rep ε π (y : Matrix (Fin n) (Fin n) ℂ) v := by
      intro y
      obtain ⟨g, rfl⟩ := E.surjective y
      show π (E.symm (E g)) v = rep ε π (mat ε g) v
      rw [E.symm_apply_apply, rep_mat]
    exact ((hπ.continuous_apply v).comp E.symm.continuous).congr hE
  · exact hi.2 S ⟨hS, fun g v hv => by simpa [rep_mat] using hinv _ (mat_mem ε g) v hv⟩

end GlobalTheory.PsCo.PcEF

end
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactPseudoCoefficientData

section

@[expose] public section

open GlobalTheory.PsCo.Pc1

namespace GlobalTheory.PsCo.Pc1

theorem maximalCompact_pseudoCoefficientData' : StKData :=
  GlobalTheory.PsCo.PcEF.stKData_of
    GlobalTheory.PsCo.PcEF.maxCompactPolynomial_blockTimesConjDetPower GlobalTheory.PsCo.PcEF.modeMatrixDet_eq_adjointDet GlobalTheory.PsCo.PcEF.coefPoly
    GlobalTheory.PsCo.PcEF.trPoly GlobalTheory.PsCo.PcEF.adjointDetTrace_classFunction GlobalTheory.PsCo.PcEF.harishChandraWeight_integral_dominant
    GlobalTheory.PsCo.PcEF.polyCoefIrrep_hasDerivedAction GlobalTheory.PsCo.PcEF.adjointDet_onCompactTorus GlobalTheory.PsCo.PcEF.torusId_full
    GlobalTheory.PsCo.PcEF.tracePairing_nonzero_intertwiner GlobalTheory.PsCo.PcEF.norm_irreducibleCharacter_unitaryMaxCompact_eq_one GlobalTheory.PsCo.PcEF.rangeFD_closed
    GlobalTheory.PsCo.PcEF.casimirScalar_stableSumSpace GlobalTheory.PsCo.PcEF.supertrace_carriedBy_diracKernel GlobalTheory.PsCo.PcEF.StrIdx_proof2
    GlobalTheory.PsCo.PcEF.intertwiner_preserves_highestWeight GlobalTheory.PsCo.PcEF.fockCoordinates_span_finiteDimensional GlobalTheory.PsCo.PcEF.casimirValue_highestWeightCoordinates
    GlobalTheory.PsCo.PcEF.highestWeightKernel_lowestType GlobalTheory.PsCo.PcEF.eq_discreteSeries_of_lowestKType_casimir GlobalTheory.PsCo.PcEF.compactDiscreteSeries_ownType
    GlobalTheory.PsCo.PcEF.gapConditions_of_largeGaps GlobalTheory.PsCo.PcEF.unitaryRep_upq_matrixFunction GlobalTheory.HcPort.casimirActsByScalar_indefUnitary

end GlobalTheory.PsCo.Pc1
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactPseudoCoefficientDataStatement

section

@[expose] public section

open GlobalTheory.PsCo.Pc1

theorem _root_.GlobalTheory.T.maximalCompact_pseudoCoefficientData : StKData := by
  first | exact @GlobalTheory.PsCo.Pc1.maximalCompact_pseudoCoefficientData' | exact GlobalTheory.PsCo.Pc1.maximalCompact_pseudoCoefficientData' | (intros; apply GlobalTheory.PsCo.Pc1.maximalCompact_pseudoCoefficientData' <;> assumption)
end
end
