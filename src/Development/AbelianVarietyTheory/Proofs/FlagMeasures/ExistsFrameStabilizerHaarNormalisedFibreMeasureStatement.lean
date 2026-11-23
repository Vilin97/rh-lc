module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.SiegelWeilNarrowOfWide
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsHaarFrameStabiliserCompatibleFibreStatement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueSelfDualMeasuresFinitePlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarFrameStabilizerLocalFixerSectionProductStatement
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsOrthogonalBasisDotProductApplyEq
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensInfAll
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensVAll
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.ExOmTOfSteps
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.FibDis
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensAll
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiVNeOneOfTrace
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SimilitudeConjPreservesUnitaryHaarAtFinitePlaceStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StandardFrameGramDetNeZero

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSelfDualTrace

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct ENNReal

namespace GlobalTheory.TraceSelfDual

section Form

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [Field R] [Algebra F R]
  (ι : Type) [Fintype ι]

noncomputable def traceBilin : LinearMap.BilinForm R (ι → R ⊗[F] E) :=
  LinearMap.mk₂ R (fun x y => ∑ i, Algebra.trace R (R ⊗[F] E) (x i * y i))
    (fun x x' y => by simp [add_mul, Finset.sum_add_distrib])
    (fun c x y => by simp [Finset.mul_sum])
    (fun x y y' => by simp [mul_add, Finset.sum_add_distrib])
    (fun c x y => by simp [Finset.mul_sum])

theorem traceBilin_apply (x y : ι → R ⊗[F] E) :
    traceBilin R ι x y = ∑ i, Algebra.trace R (R ⊗[F] E) (x i * y i) := rfl

theorem traceBilin_symm (x y : ι → R ⊗[F] E) : traceBilin R ι x y = traceBilin R ι y x := by
  simp only [traceBilin_apply, mul_comm]

variable [NumberField F] [NumberField E]

theorem eq_zero_of_traceBilin {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : ι → R ⊗[F] E)
    (hx : ∀ y, traceBilin R ι x y = 0) : x = 0 := by
  classical
  funext j
  refine GlobalTheory.SelfDualFinite.eq_zero_of_trace R h _ fun c => ?_
  have := hx (Pi.single j c)
  rw [traceBilin_apply, Finset.sum_eq_single j] at this
  · rwa [Pi.single_eq_same, mul_comm] at this
  · intro i _ hi
    rw [Pi.single_eq_of_ne hi, mul_zero, map_zero]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

end Form

theorem exists_selfDual_trace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (v : HeightOneSpectrum (𝓞 F)), (∃ r, psiV F ψ v r ≠ 1) → ∀ (ι : Type) [Fintype ι], ∃ μ : Measure (ι → Fv F v ⊗[F] E), SelfDual μ (fun x y => psiV F ψ v (∑ i, Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (x i * y i))) := by
  intro F E _ _ _ _ _ σ h ψ hψ v hne ι _
  let χ : AddChar (Fv F v) ℂ := ψ.compAddMonoidHom
    ((AddMonoidHom.inr (Ainf F) (Af F)).comp (GlobalTheory.AdelicU.singleFin v).toAddMonoidHom)
  have hc : Continuous χ :=
    hψ.1.comp (Continuous.prodMk continuous_const (GlobalTheory.AdelicU.continuous_singleFin v))
  have hu : ∀ t, ‖χ t‖ = 1 := fun t => hψ.2.1 _
  exact (GlobalTheory.SelfDualFinite.existsUnique_of_bilin v χ hc hu hne _ (traceBilin (Fv F v) ι)
    (traceBilin_symm _ ι) (eq_zero_of_traceBilin _ ι h)).exists

end GlobalTheory.TraceSelfDual
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsTupleGramDetNeZero

section

@[expose] public section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.NondegTuple

theorem conj_conj {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2 τ, h.2.2.2 τ, star_star]

theorem exists_tuple_gram_det_ne_zero :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
      (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
      ∀ a : ℕ, a ≤ n → ∃ X0 : Fin a → Fin n → E, (gramE σ J X0).det ≠ 0 ∧
        ∀ i j, σ (gramE σ J X0 j i) = gramE σ J X0 i j := by
  intro F E _ _ _ _ _ σ hσ n J hJ a ha
  have hc : ∀ t, (σ : E →+* E) ((σ : E →+* E) t) = t := conj_conj hσ
  obtain ⟨P, d, -, hd, hfix, hne⟩ := GlobalTheory.HermDiag.exists_congr_diagonal (c := (σ : E →+* E))
    (G := J) two_ne_zero hc (fun i j => hJ.1 j i)
  have hg : gramE σ J (fun i k => σ (P k (Fin.castLE ha i))) =
      Matrix.diagonal fun i => d (Fin.castLE ha i) := by
    ext i j
    have h1 := congrFun (congrFun hd (Fin.castLE ha i)) (Fin.castLE ha j)
    rw [GlobalTheory.HermDiag.transpose_mul_mul_map_apply,
      GlobalTheory.HermDiag.dotProduct_mulVec_comp_eq_sum] at h1
    have h2 : Matrix.diagonal d (Fin.castLE ha i) (Fin.castLE ha j) =
        Matrix.diagonal (fun i => d (Fin.castLE ha i)) i j := by
      simp only [Matrix.diagonal_apply, (Fin.castLE_injective ha).eq_iff]
    rw [← h2, ← h1]
    simp only [gramE, hE, Formalism.UG.hform, RingHom.coe_coe, conj_conj hσ]
  refine ⟨fun i k => σ (P k (Fin.castLE ha i)), ?_, ?_⟩
  · rw [hg, Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun i _ => hne hJ.2 _
  · intro i j
    rw [hg]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq]
      exact hfix _
    · rw [Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ (Ne.symm hij), map_zero]

end GlobalTheory.NondegTuple
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalSelfDualMeasuresFibreFamilyExist

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.LocalFibre

theorem dX_dT_omFam :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → Formalism.MainNotions.UnusedSlot34.SWa1 F E σ n J → Formalism.L2.SG.Pf.NcWeil.StabilizerFirstChernCompatibility F E σ n J → ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ a : ℕ, 1 ≤ a → 2 * a < n → (Formalism.L2.SG.LocVol.dX σ J ψ v a).IsAddHaarMeasure ∧ (Formalism.L2.SG.LocVol.dT σ ψ v a).IsAddHaarMeasure ∧ Formalism.L2.SG.LocVol.IsOm σ J ψ v a (Formalism.L2.SG.LocVol.omFam σ J ψ v a) := by
  intro F E _ _ _ _ _ σ hE n J hJ ha hc ψ hψ v a ha1 ha2
  obtain ⟨X0, hdet, hT⟩ := GlobalTheory.NondegTuple.exists_tuple_gram_det_ne_zero F E σ hE n J hJ a (by omega)
  have hI : PI.VolStabS.FibInfEx :=
    PI.VolStabS.fibInfEx_of PI.VolStabS.DiscreteGroups.fibOfDens_holds PI.VolStabS.tensAll_holds
      PI.VolStabS.densInf_holds
  have hV : PI.VolStabS.FibVEx :=
    PI.VolStabS.fibVEx_of PI.VolStabS.DiscreteGroups.fibOfDens_holds PI.VolStabS.tensAll_holds
      PI.VolStabS.densV_holds
  obtain ⟨_, _, μv, νv, _, _, _, _, hμv, hνv, _, _⟩ :=
    PI.VolStabS.locEx_of hI hV PI.VolStabS.latSB_holds F E σ hE n J hJ ha hc a ha1 ha2 X0 hT hdet
      ψ hψ
  have hX : ∃ μ, SdW F E σ n J (Fv F v) (psiV F ψ v) a μ := ⟨_, hμv v⟩
  have hH : ∃ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν := ⟨_, hνv v⟩
  have hdX : SdW F E σ n J (Fv F v) (psiV F ψ v) a (Formalism.L2.SG.LocVol.dX σ J ψ v a) := by
    unfold Formalism.L2.SG.LocVol.dX
    rw [dite_eq_left hX]
    exact hX.choose_spec
  have hdT : SdHerm F E σ (Fv F v) (psiV F ψ v) a (Formalism.L2.SG.LocVol.dT σ ψ v a) := by
    unfold Formalism.L2.SG.LocVol.dT
    rw [dite_eq_left hH]
    exact hH.choose_spec
  have hO : ∃ fib, Formalism.L2.SG.LocVol.IsOm σ J ψ v a fib :=
    hV F E σ hE n J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ v _ hdX _ hdT
  refine ⟨hdX.1, hdT.1, ?_⟩
  unfold Formalism.L2.SG.LocVol.omFam
  rw [dite_eq_left hO]
  exact hO.choose_spec

end GlobalTheory.LocalFibre
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalSelfDualMeasuresFibreFamilyExistStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

theorem _root_.GlobalTheory.T.localSelfDualMeasures_fibreFamily_exist : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → Formalism.MainNotions.UnusedSlot34.SWa1 F E σ n J → Formalism.L2.SG.Pf.NcWeil.StabilizerFirstChernCompatibility F E σ n J → ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ a : ℕ, 1 ≤ a → 2 * a < n → (Formalism.L2.SG.LocVol.dX σ J ψ v a).IsAddHaarMeasure ∧ (Formalism.L2.SG.LocVol.dT σ ψ v a).IsAddHaarMeasure ∧ Formalism.L2.SG.LocVol.IsOm σ J ψ v a (Formalism.L2.SG.LocVol.omFam σ J ψ v a) := by
  first | exact @GlobalTheory.LocalFibre.dX_dT_omFam | exact GlobalTheory.LocalFibre.dX_dT_omFam | (intros; apply GlobalTheory.LocalFibre.dX_dT_omFam <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFrameStabilizerHaarNormalisedFibreMeasure

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.LocalStabiliserTie

theorem exists_tied_haar : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → Formalism.MainNotions.UnusedSlot34.SWa1 F E σ n J → Formalism.L2.SG.Pf.NcWeil.StabilizerFirstChernCompatibility F E σ n J → ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → Formalism.L2.SG.LocVol.IsStdChar ψ → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (r : ℕ) (P : Frame E n r) (T : F), P.IsStd σ J T → 2 * (r + 1) < n → ∀ μG : Measure (HA (Fv F v) σ J), μG.IsHaarMeasure → ∃ μS : Measure (Ssub (Fv F v) σ J P), μS.IsHaarMeasure ∧ Formalism.L2.SG.LocVol.LocTieW σ J ψ v P μG μS := by
  intro F E _ _ _ _ _ σ hcm n J hJ hW hC ψ hψ hstd v r P T hP hn μG hG
  obtain ⟨-, -, hT, -, -⟩ := GlobalTheory.FrameGram.std_frame_gram F E σ hcm n J hJ r P T hP
  obtain ⟨hdX, hdT, hOm⟩ := GlobalTheory.T.localSelfDualMeasures_fibreFamily_exist F E σ hcm n J hJ hW hC ψ hψ v (r + 1) (by omega) hn
  have hfib : IsFibreFamily (Formalism.L2.SG.LocVol.dX σ J ψ v (r + 1)) (gramR (Fv F v) σ J) Subtype.val
      {X | LinearIndependent (Fv F v ⊗[F] E) X} (Formalism.L2.SG.LocVol.dT σ ψ v (r + 1)) Set.univ
      (Formalism.L2.SG.LocVol.omFam σ J ψ v (r + 1)) := hOm
  obtain ⟨μ0, hμ0, hc1, hc2⟩ := GlobalTheory.T.exists_haar_frameStabiliser_compatible_fibre F E σ hcm n J hJ v r P T hP hT _ _ hdX hdT _ hfib μG hG
  have hconj := GlobalTheory.T.similitude_conj_preserves_unitary_haar_at_finite_place F E σ hcm n J hJ v r P T hP hT _ _ hdX hdT _ hfib μ0 hμ0
  have hne : ∃ x, psiV F ψ v x ≠ 1 := GlobalTheory.StdCharTotReal.exists_psiV_ne_one F hcm.1 ψ hψ hstd v
  have hsd := GlobalTheory.TraceSelfDual.exists_selfDual_trace F E σ hcm ψ hψ v hne (Formalism.L2.SG.LocVol.UIdx r)
  have hU : (Formalism.L2.SG.LocVol.sdE (E := E) ψ v (Formalism.L2.SG.LocVol.UIdx r)).IsAddHaarMeasure := by
    unfold Formalism.L2.SG.LocVol.sdE
    rw [dite_eq_left hsd]
    exact hsd.choose_spec.1
  obtain ⟨μS, hμS, hprod⟩ := GlobalTheory.T.haar_frameStabilizer_local_fixer_section_product F E σ hcm n J hJ v r P T hP μ0 hμ0 hconj _ hU
  refine ⟨μS, hμS, μ0, hμ0, ?_, ?_⟩
  · have hom : Formalism.L2.SG.LocVol.omAt σ J ψ v (Formalism.L2.SG.LocVol.TFl σ J v P)
        = Formalism.L2.SG.LocVol.omFam σ J ψ v (r + 1) (hermOf (Fv F v) σ (gramE σ J (F0 P)) hT) := by
      unfold Formalism.L2.SG.LocVol.omAt
      have hmem : Formalism.L2.SG.LocVol.TFl σ J v P ∈ HermR (Fv F v) σ (r + 1) :=
        map_mem_HermR (Fv F v) σ _ hT
      rw [dite_eq_left hmem]
      rfl
    unfold Formalism.L2.SG.LocVol.IsCompatLoc
    rw [hom]
    exact ⟨hc1, hc2⟩
  · intro h hh t ht
    exact hprod h hh t ht

end GlobalTheory.LocalStabiliserTie
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFrameStabilizerHaarNormalisedFibreMeasureStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

theorem _root_.GlobalTheory.T.exists_frameStabilizerHaar_normalised_fibreMeasure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → Formalism.MainNotions.UnusedSlot34.SWa1 F E σ n J → Formalism.L2.SG.Pf.NcWeil.StabilizerFirstChernCompatibility F E σ n J → ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → Formalism.L2.SG.LocVol.IsStdChar ψ → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (r : ℕ) (P : Frame E n r) (T : F), P.IsStd σ J T → 2 * (r + 1) < n → ∀ μG : Measure (HA (Fv F v) σ J), μG.IsHaarMeasure → ∃ μS : Measure (Ssub (Fv F v) σ J P), μS.IsHaarMeasure ∧ Formalism.L2.SG.LocVol.LocTieW σ J ψ v P μG μS := by
  first | exact @GlobalTheory.LocalStabiliserTie.exists_tied_haar | exact GlobalTheory.LocalStabiliserTie.exists_tied_haar | (intros; apply GlobalTheory.LocalStabiliserTie.exists_tied_haar <;> assumption)
end
end
