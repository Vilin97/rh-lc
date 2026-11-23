module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.LowRankSiegelDensities.Reduce
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.UnramifiedSchwartzDensity.SchCut
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdeleHaarMapEqScaledVolumeStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanFamilyContinuityStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanScalingStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanSectionStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DensityIntegralStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresSupportStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramRightActionIdentities
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdelesLocalRingTotallyRealStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensTop
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanCoordinates

section

@[expose] public section

noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.CoordR

theorem coordInf : PositivityTheory.PfSWUS.SchInf.CoordInf := by
  intro F E _ _ _ _ _ σ hσ n M
  obtain ⟨-, e, -, he, -⟩ := GlobalTheory.T.infinite_adele_haar_map_eq_scaled_volume F hσ.1
  let eh : Ainf F ≃ₜ (InfinitePlace F → ℝ) := he.homeomorph _
  have heh : ∀ y, eh y = e y := fun _ => rfl
  haveI : SecondCountableTopology (Ainf F) := eh.secondCountableTopology
  haveI : T2Space (Ainf F) := eh.symm.t2Space
  obtain ⟨i1, i2, i3, i4, -, -, hb, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Ainf F)
  let d := Module.finrank F E
  let b : Module.Basis (Fin d) F E := Module.finBasis F E
  let B := Algebra.TensorProduct.basis (Ainf F) b
  let Hs : (Ainf F ⊗[F] E) ≃ₜ (Fin d → Ainf F) := (hb d b).homeomorph _
  have hHs : ∀ y k, Hs y k = B.repr y k := fun _ _ => rfl
  let I := Fin n × Fin M × Fin d × InfinitePlace F
  let q : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let eH : (Fin n → Fin M → Ainf F ⊗[F] E) ≃ₜ (Fin (Fintype.card I) → ℝ) :=
    { toFun := fun X t => eh (Hs (X (q.symm t).1 (q.symm t).2.1) (q.symm t).2.2.1) (q.symm t).2.2.2
      invFun := fun y a j => Hs.symm fun k => eh.symm fun w => y (q (a, j, k, w))
      left_inv := fun X => by simp
      right_inv := fun y => by
        funext t
        simp
      continuous_toFun := continuous_pi fun t =>
        (continuous_apply _).comp (eh.continuous.comp ((continuous_apply _).comp
          (Hs.continuous.comp ((continuous_apply _).comp (continuous_apply _)))))
      continuous_invFun := continuous_pi fun a => continuous_pi fun j =>
        Hs.symm.continuous.comp (continuous_pi fun k => eh.symm.continuous.comp
          (continuous_pi fun w => continuous_apply _)) }
  have hadd : ∀ X Y, eH (X + Y) = eH X + eH Y := by
    intro X Y
    funext t
    change eh (Hs (X _ _ + Y _ _) _) _ = eh (Hs (X _ _) _) _ + eh (Hs (Y _ _) _) _
    simp only [hHs, heh, map_add (f := _), Finsupp.add_apply, Pi.add_apply]
  let eV : (Fin n → Fin M → Ainf F ⊗[F] E) ≃+ (Fin (Fintype.card I) → ℝ) :=
    { eH.toEquiv with map_add' := hadd }
  have hV : ∀ X, eV X = eH X := fun _ => rfl
  have hVs : ∀ y, eV.symm y = eH.symm y := fun _ => rfl
  have hc : Continuous fun p : (Fin n → Fin M → Ainf F ⊗[F] E) × Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E) =>
      rmul (Ainf F) p.1 p.2 := by
    refine continuous_pi fun a => continuous_pi fun i => continuous_finsetSum _ fun c _ => ?_
    have h1 : Continuous fun p : (Fin n → Fin M → Ainf F ⊗[F] E) ×
        Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E) => p.1 c i :=
      (continuous_apply i).comp ((continuous_apply c).comp continuous_fst)
    exact h1.mul (continuous_snd.matrix_elem c a)
  have hrad : ∀ (g : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) (X Y : Fin n → Fin M → Ainf F ⊗[F] E),
      rmul (Ainf F) (X + Y) g = rmul (Ainf F) X g + rmul (Ainf F) Y g := by
    intro g X Y
    funext a i
    simp [rmul, add_mul, Finset.sum_add_distrib]
  let L0 : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E) → (Fin (Fintype.card I) → ℝ) →+ (Fin (Fintype.card I) → ℝ) :=
    fun g => AddMonoidHom.mk' (fun y => eV (rmul (Ainf F) (eV.symm y) g)) fun y z => by
      rw [map_add (f := _), hrad, map_add (f := _)]
  have hL0 : ∀ g, Continuous (L0 g) := fun g =>
    eH.continuous.comp (hc.comp (eH.symm.continuous.prodMk continuous_const))
  let L : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E) → (Fin (Fintype.card I) → ℝ) →L[ℝ] (Fin (Fintype.card I) → ℝ) :=
    fun g => (L0 g).toRealLinearMap (hL0 g)
  refine ⟨Fintype.card I, eV, eH.continuous, eH.symm.continuous, L, ?_, ?_⟩
  · refine continuous_clm_apply.2 fun y => ?_
    exact eH.continuous.comp (hc.comp (continuous_const.prodMk continuous_id))
  · intro g X
    change eV _ = eV (rmul (Ainf F) (eV.symm (eV X)) g)
    rw [AddEquiv.symm_apply_apply]

end GlobalTheory.CompanionTheory.SW.CoordR

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanCoordinatesStatement

section

@[expose] public section

noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.archimedean_coordinates : PositivityTheory.PfSWUS.SchInf.CoordInf := by
  first | exact @GlobalTheory.CompanionTheory.SW.CoordR.coordInf | exact GlobalTheory.CompanionTheory.SW.CoordR.coordInf | (intros; apply GlobalTheory.CompanionTheory.SW.CoordR.coordInf <;> assumption)
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinitePartOpen

section

@[expose] public section

noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.FinOpenGram

theorem finOpen : PositivityTheory.PfSWUS.SchInf.FinOpen := by
  intro F E _ _ _ _ _ σ hCM M J hJ n μ ν m hμ hν hm f hf hfin U hU hne
  have : BorelSpace (HermR (Ainf F) σ n) := ⟨rfl⟩
  by_contra hcon
  push Not at hcon
  have hpos : ν U ≠ 0 := (hU.measure_pos ν hne).ne'
  have h2 := hm
  unfold GlobalTheory.CompanionTheory.SW.IsGramFib Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily at h2
  have hfib := h2.2.1 f hf
  have hle : (⊤ : ℝ≥0∞) * ν U ≤ ∫⁻ S, ∫⁻ X, f X ∂(m S) ∂ν := by
    rw [← lintegral_indicator_const hU.measurableSet]
    refine lintegral_mono fun S => ?_
    by_cases hS : S ∈ U
    · rw [Set.indicator_of_mem hS, hcon S hS]
    · rw [Set.indicator_of_notMem hS]
      exact bot_le
  rw [ENNReal.top_mul hpos, top_le_iff, ← hfib] at hle
  exact hfin (top_le_iff.1 (hle ▸ setLIntegral_le_lintegral _ _))

end GlobalTheory.CompanionTheory.SW.FinOpenGram
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinitePartOpenStatement

section

@[expose] public section

noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.finite_part_open : PositivityTheory.PfSWUS.SchInf.FinOpen := by
  first | exact @GlobalTheory.CompanionTheory.SW.FinOpenGram.finOpen | exact GlobalTheory.CompanionTheory.SW.FinOpenGram.finOpen | (intros; apply GlobalTheory.CompanionTheory.SW.FinOpenGram.finOpen <;> assumption)
end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.UnramifiedSchwartzDensity.Assemble

section

@[expose] public section

noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace PositivityTheory.PfSWUS.SchInf

open GlobalTheory.CompanionTheory.SW

theorem schwartz_decay {N : ℕ} (g : SchwartzMap (Fin N → ℝ) ℂ) (k : ℕ) :
    ∃ C : ℝ, ∀ y, ‖g y‖ ≤ C * (1 + ‖y‖) ^ (-(k : ℝ)) := by
  set B : ℝ := 2 ^ k * ((Finset.Iic (k, 0)).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2) g with hB
  refine ⟨B, fun y => ?_⟩
  have h1 := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 0)) (k := k) (n := 0) le_rfl le_rfl g y
  rw [norm_iteratedFDeriv_zero] at h1
  have hy : 0 < 1 + ‖y‖ := by positivity
  rw [Real.rpow_neg hy.le, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  calc ‖g y‖ * (1 + ‖y‖) ^ k = (1 + ‖y‖) ^ k * ‖g y‖ := by ring
    _ ≤ B := h1

theorem schwartzDensInf_of (hA : FamCont) (hB : SecInf) (hC : CoordInf) (hD : ScaleInf) (hE : FinOpen)
    (hF : DensInt) : PositivityTheory.PfSWUS.HMass.SchwartzDensInf := by
  intro F E _ _ _ _ _ σ hσ M J hJ n μ ν m hμ hν hm φ hφ
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  have hloc : IsLocR (Ainf F) := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hσ.1
  obtain ⟨i1, i2, i3, i4, -, -, -, hBor, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Ainf F)
  have := i1
  have := i2
  have := i3
  have := i4
  have := hBor n M
  obtain ⟨-, hcomp, hone, hmem, -⟩ := GlobalTheory.CompanionTheory.SW.GramAlg.gram_algebra F E σ hσ M J hJ (Ainf F) n
  obtain ⟨N, eV, heV, heVs, L, hL, hLe⟩ := hC F E σ hσ n M
  obtain ⟨g, hg⟩ := hφ N eV heV heVs
  have hφeq : ∀ X, φ X = g (eV X) := fun X => by rw [hg, AddEquiv.symm_apply_apply]
  let T : (Fin n → Fin M → Ainf F ⊗[F] E) ≃ₜ (Fin N → ℝ) :=
    { toEquiv := eV.toEquiv, continuous_toFun := heV, continuous_invFun := heVs }
  have hTm : MeasurableEmbedding eV := T.measurableEmbedding
  have hμ' : (μ.map eV).IsAddHaarMeasure := eV.isAddHaarMeasure_map μ heV heVs
  have key : ∀ c : HermR (Ainf F) σ n, IsUnit (c : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det →
      ∀ g' : (Fin N → ℝ) → ℂ, Continuous g' → (∀ k : ℕ, ∃ C : ℝ, ∀ y, ‖g' y‖ ≤ C * (1 + ‖y‖) ^ (-(k : ℝ))) →
      (∀ᶠ S in 𝓝 c, Integrable g' ((m S).map eV)) ∧
        ContinuousAt (fun S => ∫ y, g' y ∂((m S).map eV)) c := by
    intro c hc g' hg'c hg'd
    obtain ⟨O, hO, hcO, hsec⟩ := hB F E σ hσ n c hc
    obtain ⟨A, C, hAc, hCc, hAC⟩ := hD F E σ hσ n M μ ν hμ hν
    refine hA N (HermR (Ainf F) σ n) (μ.map eV) hμ' (fun S => (m S).map eV) c O hO hcO ?_ ?_ g' hg'c hg'd
    · intro f hf hfin U hU hne
      rw [lintegral_map hf hTm.measurable] at hfin
      obtain ⟨S, hS, hS'⟩ := hE F E σ hσ M J hJ n μ ν m hμ hν hm (fun X => f (eV X))
        (hf.comp hTm.measurable) hfin U hU hne
      exact ⟨S, hS, by rwa [lintegral_map hf hTm.measurable]⟩
    · intro s₀ hs₀
      obtain ⟨h, hinv, hhc, hhic, hhS⟩ := hsec s₀ hs₀
      have hunit : ∀ S ∈ O, IsUnit (h S).det := fun S hS =>
        Matrix.isUnit_det_of_right_inverse (hhS S hS).1
      have hcn : O ∈ 𝓝 c := hO.mem_nhds hcO
      have hh_at : ContinuousAt h c := hhc.continuousAt hcn
      have hhi_at : ContinuousAt hinv c := hhic.continuousAt hcn
      have hU_ev : ∀ᶠ S in 𝓝 c, h S ∈ {g : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E) | IsUnit g.det} :=
        Filter.mem_of_superset hcn fun S hS => hunit S hS
      have htends : Filter.Tendsto h (𝓝 c)
          (𝓝[{g : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E) | IsUnit g.det}] (h c)) :=
        tendsto_nhdsWithin_iff.2 ⟨hh_at, hU_ev⟩
      have hA_at : ContinuousAt (fun S => A (h S)) c := (hAc (h c) (hunit c hcO)).tendsto.comp htends
      have hC_at : ContinuousAt (fun S => C (h S)) c := (hCc (h c) (hunit c hcO)).tendsto.comp htends
      refine ⟨fun S => L (h S), fun S => L (hinv S), fun S => C (h S) * (A (h S))⁻¹,
        hL.continuousAt.comp hh_at, hL.continuousAt.comp hhi_at,
        hC_at.mul (hA_at.inv₀ (hAC _ (hunit c hcO)).1), ?_, ?_⟩
      · intro S hS y
        obtain ⟨X, rfl⟩ := eV.surjective y
        show L (hinv S) (L (h S) (eV X)) = eV X
        rw [← hLe, ← hLe, hcomp, (hhS S hS).1, hone]
      · intro S hS
        have hu := hunit S hS
        obtain ⟨hA0, -, hAm, hCm⟩ := hAC (h S) hu
        let τ : HermR (Ainf F) σ n → HermR (Ainf F) σ n := fun S' =>
          ⟨cT (sigR (Ainf F) σ) (h S) * (S' : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) * h S, hmem S' (h S)⟩
        have hτ : ∀ S', (τ S' : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) =
            cT (sigR (Ainf F) σ) (h S) * S' * h S := fun _ => rfl
        have hk := GlobalTheory.T.gram_fiber_measures_rmul_equivariant F E σ hσ M J hJ (Ainf F) hloc n μ ν m hμ hν hm (h S) hu τ hτ
          (A (h S)) (C (h S)) hAm (hCm τ hτ) s₀
        have hτs : τ s₀ = S := Subtype.ext (hhS S hS).2.2.symm
        rw [hτs] at hk
        have hmS : m S = (C (h S) * (A (h S))⁻¹) • (m s₀).map (fun X : Fin n → Fin M → Ainf F ⊗[F] E => rmul (Ainf F) X (h S)) := by
          rw [mul_comm, ← smul_smul, ← hk, smul_smul, inv_mul_cancel₀ hA0, one_smul]
        have hrm : Measurable (fun X : Fin n → Fin M → Ainf F ⊗[F] E => rmul (Ainf F) X (h S)) := by
          have : (fun X : Fin n → Fin M → Ainf F ⊗[F] E => rmul (Ainf F) X (h S)) = fun X => eV.symm (L (h S) (eV X)) := by
            funext X
            rw [← hLe, AddEquiv.symm_apply_apply]
          rw [this]
          exact (heVs.comp ((L (h S)).continuous.comp heV)).measurable
        show (m S).map eV = _
        rw [hmS, Measure.map_smul, Measure.map_map hTm.measurable hrm,
          Measure.map_map (L (h S)).continuous.measurable hTm.measurable]
        congr 2
        funext X
        exact hLe (h S) X
        exact hTm.measurable.aemeasurable
  have hgk : ∀ k : ℕ, ∃ C : ℝ, ∀ y, ‖g y‖ ≤ C * (1 + ‖y‖) ^ (-(k : ℝ)) := schwartz_decay g
  have hng : ∀ k : ℕ, ∃ C : ℝ, ∀ y, ‖((‖g y‖ : ℝ) : ℂ)‖ ≤ C * (1 + ‖y‖) ^ (-(k : ℝ)) := by
    intro k
    obtain ⟨C, hC⟩ := hgk k
    exact ⟨C, fun y => by simpa using hC y⟩
  have hngc : Continuous fun y => ((‖g y‖ : ℝ) : ℂ) := Complex.continuous_ofReal.comp g.continuous.norm
  have hφc : Continuous φ := by
    rw [show φ = fun X => g (eV X) from funext hφeq]
    exact g.continuous.comp heV
  have hIntS : ∀ S : HermR (Ainf F) σ n, IsUnit (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det →
      Integrable φ (m S) := by
    intro S hS
    have h1 := ((key S hS g g.continuous hgk).1).self_of_nhds
    rw [hTm.integrable_map_iff] at h1
    rwa [show φ = (⇑g ∘ ⇑eV) from funext hφeq]
  have hcont : ContinuousOn (fun S => ∫ X, φ X ∂(m S))
      {S : HermR (Ainf F) σ n | IsUnit (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det} := by
    intro S hS
    refine ((key S hS g g.continuous hgk).2.congr (Filter.Eventually.of_forall fun S' => ?_)).continuousWithinAt
    show ∫ y, g y ∂((m S').map eV) = ∫ X, φ X ∂(m S')
    rw [hTm.integral_map]
    simp only [hφeq]
  have hcontn : ContinuousOn (fun S => ∫ X, ‖φ X‖ ∂(m S))
      {S : HermR (Ainf F) σ n | IsUnit (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det} := by
    intro S hS
    have h3 : ContinuousAt (fun S' => (∫ y, ((‖g y‖ : ℝ) : ℂ) ∂((m S').map eV)).re) S :=
      Complex.continuous_re.continuousAt.comp (key S hS _ hngc hng).2
    refine (h3.congr (Filter.Eventually.of_forall fun S' => ?_)).continuousWithinAt
    show (∫ y, ((‖g y‖ : ℝ) : ℂ) ∂((m S').map eV)).re = ∫ X, ‖φ X‖ ∂(m S')
    rw [hTm.integral_map, integral_complex_ofReal, Complex.ofReal_re]
    simp only [hφeq]
  have hφμ : Integrable φ μ := by
    obtain ⟨C0, hC0⟩ := hgk (Module.finrank ℝ (Fin N → ℝ) + 1)
    have hW : Integrable (fun y : Fin N → ℝ => (1 + ‖y‖) ^ (-((Module.finrank ℝ (Fin N → ℝ) + 1 : ℕ) : ℝ)))
        (μ.map eV) := integrable_one_add_norm (by push_cast; linarith)
    have hgμ : Integrable g (μ.map eV) :=
      Integrable.mono' (hW.const_mul C0) g.continuous.aestronglyMeasurable (ae_of_all _ hC0)
    rw [hTm.integrable_map_iff] at hgμ
    rwa [show φ = (⇑g ∘ ⇑eV) from funext hφeq]
  exact ⟨hφc, ⟨hcont, fun K hK hKB => hF F E σ hσ M J hJ n μ ν m hμ hν hm φ hφc hφμ hIntS hcontn K hK hKB⟩,
    hIntS⟩

end PositivityTheory.PfSWUS.SchInf

end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.UnramifiedSchwartzDensity.SchTop

section

@[expose] public section

theorem PositivityTheory.PfSWUS.SchInf.schwartzDensInf : PositivityTheory.PfSWUS.HMass.SchwartzDensInf :=
  PositivityTheory.PfSWUS.SchInf.schwartzDensInf_of GlobalTheory.T.archimedean_family_continuity GlobalTheory.T.archimedean_section GlobalTheory.T.archimedean_coordinates GlobalTheory.T.archimedean_scaling GlobalTheory.T.finite_part_open
    GlobalTheory.T.density_integral
end
end
