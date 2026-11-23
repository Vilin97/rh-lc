module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualCinvOKSmallStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleHermitianPairStructureFactsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteNormedAlgebraEqModuleTopology
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.Normed
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyMeasAndReps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TruncatedWhittakerIntegralEqVolumeMulIntegralPerStatement
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleHermitianPairStructureFactsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualIffLatticeVolumeAndPlancherelStatement
import Mathlib.Tactic.Linter.Style
import Mathlib.Topology.Compactness.Paracompact

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EventuallyTestFunctionMulInverseUnitEq

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory

theorem eventually_isUnit_and_tendsto_inverse_normed (F : Type) [NontriviallyNormedField F]
    [CompleteSpace F] (R : Type) [NormedCommRing R] [NormedAlgebra F R] [Module.Finite F R] :
    (∀ᶠ w in 𝓝 (1 : R), IsUnit w) ∧ Tendsto Ring.inverse (𝓝 (1 : R)) (𝓝 1) := by
  have : CompleteSpace R := FiniteDimensional.complete F R
  refine ⟨Units.isOpen.mem_nhds isUnit_one, ?_⟩
  have h := (NormedRing.inverse_continuousAt (1 : Rˣ)).tendsto
  simpa using h

theorem eventually_isUnit_and_tendsto_inverse (F : Type) [NontriviallyNormedField F]
    [CompleteSpace F] (R : Type) [CommRing R] [Algebra F R] [Module.Finite F R]
    [τ : TopologicalSpace R] [IsModuleTopology F R] :
    (∀ᶠ w in 𝓝 (1 : R), IsUnit w) ∧ Tendsto Ring.inverse (𝓝 (1 : R)) (𝓝 1) := by
  classical
  have hτ : τ = moduleTopology F R := eq_moduleTopology F R
  let b := Module.finBasis F R
  let : NormedRing (Matrix (Fin (Module.finrank F R)) (Fin (Module.finrank F R)) F) :=
    Matrix.linftyOpNormedRing
  let : NormedAlgebra F (Matrix (Fin (Module.finrank F R)) (Fin (Module.finrank F R)) F) :=
    Matrix.linftyOpNormedAlgebra
  let N : NormedCommRing R := NormedCommRing.induced R _ (Algebra.leftMulMatrix b)
    (Algebra.leftMulMatrix_injective b)
  let A : @NormedAlgebra F R _ N.toNormedRing.toSeminormedRing :=
    NormedAlgebra.induced F R _ (Algebra.leftMulMatrix b)
  have key := @eventually_isUnit_and_tendsto_inverse_normed F _ _ R N A ‹_›
  have hN : N.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      = moduleTopology F R :=
    @finiteNormedAlgebra_eq_moduleTopology F _ _ R N A ‹_›
  rw [hτ, ← hN]
  exact key

theorem eventually_testFn_mul_inverse_eq : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (φ' : A.K × A.K → ℂ), IsTest φ' → ∀ a : A.K, IsUnit a → ∀ᶠ s in 𝓝 a, ∀ t : A.K, IsUnit t → φ' (s * Ring.inverse t, t) = φ' (a * Ring.inverse t, t) := by
  intro F E _ _ _ _ hU A φ' hφ a ha
  haveI : LocallyCompactSpace F := hU.lcF
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : CompleteSpace F := inferInstance
  obtain ⟨hunit, hinv⟩ := eventually_isUnit_and_tendsto_inverse F A.K
  have hC : IsCompact (tsupport φ') := hφ.2
  have H1 : ∀ᶠ w in 𝓝 (1 : A.K), ∀ q ∈ tsupport φ', φ' (q.1 * w, q.2) = φ' q := by
    refine hC.eventually_forall_of_forall_eventually fun p _ => ?_
    have hc : Tendsto (fun z : A.K × (A.K × A.K) => (z.2.1 * z.1, z.2.2)) (𝓝 (1, p)) (𝓝 p) := by
      have : Continuous (fun z : A.K × (A.K × A.K) => (z.2.1 * z.1, z.2.2)) := by fun_prop
      simpa using this.tendsto (1, p)
    have hl : ∀ᶠ q in 𝓝 p, φ' q = φ' p := hφ.1.eventually_eq p
    have h2 : Tendsto (fun z : A.K × (A.K × A.K) => z.2) (𝓝 (1, p)) (𝓝 p) := continuous_snd.tendsto _
    filter_upwards [hc.eventually hl, h2.eventually hl] with z hz1 hz2
    exact hz1.trans hz2.symm
  have H2 : ∀ᶠ w in 𝓝 (1 : A.K), ∀ q : A.K × A.K, φ' (q.1 * w, q.2) = φ' q := by
    filter_upwards [hunit, hinv.eventually H1, H1] with w hw hw' h1 q
    by_cases hq : q ∈ tsupport φ'
    · exact h1 q hq
    by_cases hq' : (q.1 * w, q.2) ∈ tsupport φ'
    · have := hw' _ hq'
      simp only [mul_assoc, Ring.mul_inverse_cancel w hw, mul_one] at this
      exact this.symm
    · rw [image_eq_zero_of_notMem_tsupport hq, image_eq_zero_of_notMem_tsupport hq']
  have hT : Tendsto (fun s : A.K => Ring.inverse a * s) (𝓝 a) (𝓝 1) := by
    have : Continuous (fun s : A.K => Ring.inverse a * s) := by fun_prop
    simpa [Ring.inverse_mul_cancel a ha] using this.tendsto a
  filter_upwards [hT.eventually H2] with s hs t _
  have := hs (a * Ring.inverse t, t)
  have e : a * Ring.inverse t * (Ring.inverse a * s) = s * Ring.inverse t := by
    calc a * Ring.inverse t * (Ring.inverse a * s) = (a * Ring.inverse a) * s * Ring.inverse t := by ring
      _ = s * Ring.inverse t := by rw [Ring.mul_inverse_cancel a ha, one_mul]
  simpa [e] using this

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EventuallyTestFunctionMulInverseUnitEqStatement

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.eventually_testFunction_mul_inverse_unit_eq : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (φ' : A.K × A.K → ℂ), IsTest φ' → ∀ a : A.K, IsUnit a → ∀ᶠ s in 𝓝 a, ∀ t : A.K, IsUnit t → φ' (s * Ring.inverse t, t) = φ' (a * Ring.inverse t, t) := by
  first | exact @GlobalTheory.eventually_testFn_mul_inverse_eq | exact GlobalTheory.eventually_testFn_mul_inverse_eq | (intros; apply GlobalTheory.eventually_testFn_mul_inverse_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VolumeScaledIntegersMulVolumeDualEqOne

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.LatVol

theorem stdChar_continuous {F : Type} [NontriviallyNormedField F] (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) :
    Continuous ψ := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  have h : ∀ᶠ y in 𝓝 x, ψ y = ψ x := by
    filter_upwards [Metric.ball_mem_nhds x one_pos] with y hy
    have h1 : ψ (y - x) = 1 := hψ.1 _ (by rw [Metric.mem_ball, dist_eq_norm] at hy; exact hy.le)
    calc ψ y = ψ (x + (y - x)) := by rw [add_sub_cancel]
      _ = ψ x * ψ (y - x) := AddChar.map_add_eq_mul ψ _ _
      _ = ψ x := by rw [h1, mul_one]
  exact (continuousAt_const).congr (h.mono fun y hy => hy.symm)

theorem main : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), SelfDual μK (A.kerK ψ) → ∀ c : F, c ≠ 0 → MeasurableSet {y : A.K | ∀ x : A.K, c • x ∈ A.OK → A.psiK ψ (x * y) = 1} ∧ (((μK {z : A.K | c • z ∈ A.OK}).toReal : ℝ) : ℂ) * (((μK {y : A.K | ∀ x : A.K, c • x ∈ A.OK → A.psiK ψ (x * y) = 1}).toReal : ℝ) : ℂ) = 1 := by
  intro F E _ _ _ _ _ A ψ hψ μK hsd c hc
  obtain ⟨-, -, hnd, -, -, -, -, -, -, hOpen, hCpt, R, hR⟩ := GlobalTheory.T.etaleHermitianPair_structure_facts F E A
  have hψc := stdChar_continuous ψ hψ

  have hcl : IsClosed {y : A.K | ∀ x : A.K, c • x ∈ A.OK → A.psiK ψ (x * y) = 1} := by
    have : {y : A.K | ∀ x : A.K, c • x ∈ A.OK → A.psiK ψ (x * y) = 1} =
        ⋂ x : A.K, ⋂ (_ : c • x ∈ A.OK), {y : A.K | ψ (Algebra.trace F A.K (x * y)) = 1} := by
      ext y; simp [Et.psiK]
    rw [this]
    refine isClosed_iInter fun x => isClosed_iInter fun _ => isClosed_eq ?_ continuous_const
    have htr : Continuous (Algebra.trace F A.K) :=
      IsModuleTopology.continuous_of_linearMap (Algebra.trace F A.K)
    exact hψc.comp (htr.comp (continuous_const.mul continuous_id))
  refine ⟨hcl.measurableSet, ?_⟩

  let M : AddSubgroup A.K := R.toAddSubgroup.comap (DistribSMul.toAddMonoidHom A.K c)
  have hM : (M : Set A.K) = {z : A.K | c • z ∈ A.OK} := by
    ext z; simp [M, ← hR]
  have hsm : Continuous fun z : A.K => c • z := continuous_const_smul c
  have hMo : IsOpen (M : Set A.K) := by rw [hM]; exact hOpen.preimage hsm
  have hMc : IsCompact (M : Set A.K) := by
    have : (M : Set A.K) = (fun w : A.K => c⁻¹ • w) '' A.OK := by
      rw [hM]; ext z; constructor
      · intro hz; exact ⟨c • z, hz, inv_smul_smul₀ hc z⟩
      · rintro ⟨w, hw, rfl⟩; simpa [smul_inv_smul₀ hc] using hw
    rw [this]; exact hCpt.image (continuous_const_smul _)
  have hk : (fun x y : A.K => ψ (Algebra.traceForm F A.K x y)) = A.kerK ψ := by
    funext x y; simp [Et.kerK, Et.psiK, Algebra.traceForm_apply]
  have hsd' : SelfDual μK (fun x y : A.K => ψ (Algebra.traceForm F A.K x y)) := by rw [hk]; exact hsd
  have key := ((GlobalTheory.T.selfDual_iff_lattice_volume_and_plancherel_alt F E ψ hψ A.K (Algebra.traceForm F A.K) (Algebra.traceForm_isSymm F) hnd μK hsd.1).1
    M hMo hMc).1.1 hsd'
  have hN : {y : A.K | ∀ x ∈ M, ψ (Algebra.traceForm F A.K x y) = 1} =
      {y : A.K | ∀ x : A.K, c • x ∈ A.OK → A.psiK ψ (x * y) = 1} := by
    ext y; simp [M, ← hR, Et.psiK, Algebra.traceForm_apply]
  rw [hN, show ((M : Set A.K)) = {z : A.K | c • z ∈ A.OK} from hM] at key
  have h1 : (μK {z : A.K | c • z ∈ A.OK}).toReal * (μK {y : A.K | ∀ x : A.K, c • x ∈ A.OK → A.psiK ψ (x * y) = 1}).toReal = 1 := by
    rw [← ENNReal.toReal_mul, key, ENNReal.toReal_one]
  rw [← Complex.ofReal_mul, h1, Complex.ofReal_one]

end GlobalTheory.LatVol
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VolumeScaledIntegersMulVolumeDualEqOneStatement

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.volume_scaledIntegers_mul_volume_dual_eq_one : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), SelfDual μK (A.kerK ψ) → ∀ c : F, c ≠ 0 → MeasurableSet {y : A.K | ∀ x : A.K, c • x ∈ A.OK → A.psiK ψ (x * y) = 1} ∧ (((μK {z : A.K | c • z ∈ A.OK}).toReal : ℝ) : ℂ) * (((μK {y : A.K | ∀ x : A.K, c • x ∈ A.OK → A.psiK ψ (x * y) = 1}).toReal : ℝ) : ℂ) = 1 := by
  first | exact @GlobalTheory.LatVol.main | exact GlobalTheory.LatVol.main | (intros; apply GlobalTheory.LatVol.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TruncatedWhittakerJHypEqOrbitalIntegral

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory

theorem scale_integral : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ (f : A.K → ℂ) (t : A.K), IsUnit t → ∫ b, f (t * b) ∂μK = ((A.absK t : ℂ))⁻¹ * ∫ s, f s ∂μK := by
  intro F E _ _ _ _ _ A μK hH f t ht
  have := Unram.lcF (F := F) (E := E); have := Unram.ultraF (F := F) (E := E)
  obtain ⟨_, _, _, _, -⟩ := GlobalTheory.JR.EtMeas.top_facts F A.K
  have hme : MeasurableEmbedding (fun b : A.K => ht.unit • b) := (Homeomorph.smul ht.unit).measurableEmbedding
  have hmap : Measure.map (fun b : A.K => ht.unit • b) μK =
      ((distribHaarChar A.K ht.unit : ENNReal))⁻¹ • μK := by
    ext S hS
    rw [hme.map_apply, Measure.smul_apply, smul_eq_mul]
    have h1 := distribHaarChar_mul μK ht.unit⁻¹ S
    rw [Set.preimage_smul, ← h1, map_inv, ENNReal.coe_inv (distribHaarChar_pos).ne']
  have hint : ∫ b, f (t * b) ∂μK = ∫ b, f b ∂(Measure.map (fun b : A.K => ht.unit • b) μK) := by
    rw [hme.integral_map]; rfl
  rw [hint, hmap, integral_smul_measure]
  simp [Et.absK, ht, Complex.real_smul]

theorem jHyp_wn : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ (φ' : A.K × A.K → ℂ) (z : A.K), A.jHyp μK ψ φ' (wS A.K * nS z) = ∫ t, (∫ b, φ' (b, t) * A.psiK ψ (t * z * b) ∂μK) * A.etaK t ∂μK := by
  intro F E _ _ _ _ _ A ψ μK hH φ' z
  have := Unram.lcF (F := F) (E := E); have := Unram.ultraF (F := F) (E := E)
  obtain ⟨_, _, _, _, -⟩ := GlobalTheory.JR.EtMeas.top_facts F A.K
  have : μK.IsNegInvariant := Measure.IsAddHaarMeasure.isNegInvariant_of_regular μK
  have h10 : ((wS A.K * nS z : SpecialLinearGroup (Fin 2) A.K) : Matrix (Fin 2) (Fin 2) A.K) 1 0 = -1 := by
    show (!![0, 1; -1, 0] * !![1, z; 0, 1] : Matrix (Fin 2) (Fin 2) A.K) 1 0 = -1
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have h11 : ((wS A.K * nS z : SpecialLinearGroup (Fin 2) A.K) : Matrix (Fin 2) (Fin 2) A.K) 1 1 = -z := by
    show (!![0, 1; -1, 0] * !![1, z; 0, 1] : Matrix (Fin 2) (Fin 2) A.K) 1 1 = -z
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have heta : ∀ t : A.K, A.etaK (-t) = A.etaK t := by
    intro t
    unfold Et.etaK
    have hg : ∀ x y : F, ‖x‖ = ‖y‖ → eta x = eta y := by
      intro x y h; unfold eta; rw [h]
    apply hg
    show ‖Algebra.norm F (-t)‖ = ‖Algebra.norm F t‖
    rw [show -t = algebraMap F A.K (-1) * t by simp, map_mul, Algebra.norm_algebraMap, norm_mul, norm_pow,
      norm_neg, norm_one, one_pow, one_mul]
  unfold Et.jHyp
  simp only [h10, h11]
  refine (integral_neg_eq_self _ μK).symm.trans ?_
  congr 1
  funext t
  simp only [neg_mul_neg, mul_one, heta, Et.tilde]

theorem whittaker_jHyp_eq_orbK : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), SelfDual μK (A.kerK ψ) → ∀ φ', IsTest φ' → ∀ a : A.K, IsUnit a → ∀ᶠ c in 𝓝[≠] (0 : F), A.abelian₂ μK ψ a (A.jHyp μK ψ φ') c = A.orbK μK φ' a := by
  intro F E _ _ _ _ _ A ψ hψ μK hμ φ' hφ a ha
  have hH : μK.IsAddHaarMeasure := hμ.1
  have hnull : μK {t : A.K | ¬ IsUnit t} = 0 := (GlobalTheory.T.etaleHermitianPair_structure_facts F E A).2.2.2.2.2.2.2.2.1 μK hH
  have hae : ∀ᵐ t ∂μK, IsUnit t := ae_iff.2 (by simpa using hnull)
  have hV : {v : A.K | ∀ t : A.K, IsUnit t → φ' ((a + v) * Ring.inverse t, t) = φ' (a * Ring.inverse t, t)}
      ∈ 𝓝 (0 : A.K) := by
    have h2 := GlobalTheory.T.eventually_testFunction_mul_inverse_unit_eq F E A φ' hφ a ha
    have hc : Tendsto (fun v : A.K => a + v) (𝓝 0) (𝓝 a) := by
      have := (continuous_const_add a).tendsto (0 : A.K)
      rwa [add_zero] at this
    exact hc h2
  filter_upwards [GlobalTheory.T.eventually_dual_scaled_OK_subset_nhds F E A ψ hψ _ hV, self_mem_nhdsWithin] with c hc hc0
  have hc0' : c ≠ 0 := hc0
  set M := {z : A.K | c • z ∈ A.OK} with hM
  set N := {y : A.K | ∀ x : A.K, c • x ∈ A.OK → A.psiK ψ (x * y) = 1} with hN
  obtain ⟨hNm, hvol⟩ := GlobalTheory.T.volume_scaledIntegers_mul_volume_dual_eq_one F E A ψ hψ μK hμ c hc0'
  have hLam : A.abelian₂ μK ψ a (A.jHyp μK ψ φ') c = (((μK M).toReal : ℝ) : ℂ) *
      ∫ t, (∫ b, φ' (b, t) * N.indicator (fun _ => (1 : ℂ)) (t * b - a) ∂μK) * A.etaK t ∂μK := by
    rw [← GlobalTheory.T.truncatedWhittakerIntegral_eq_volume_mul_integral_perp F E A ψ hψ μK hH φ' hφ a c hc0']
    unfold Et.abelian₂
    simp only [jHyp_wn F E A ψ μK hH φ']
  have hin : ∀ t : A.K, IsUnit t → (∫ b, φ' (b, t) * N.indicator (fun _ => (1 : ℂ)) (t * b - a) ∂μK) =
      ((A.absK t : ℂ))⁻¹ * (φ' (a * Ring.inverse t, t) * (((μK N).toReal : ℝ) : ℂ)) := by
    intro t ht
    have h4 := scale_integral F E A μK hH (fun s => φ' (Ring.inverse t * s, t) * N.indicator (fun _ => (1 : ℂ)) (s - a)) t ht
    simp only [Ring.inverse_mul_cancel_left t _ ht] at h4
    rw [h4]
    congr 1
    have h5 : (fun s => φ' (Ring.inverse t * s, t) * N.indicator (fun _ => (1 : ℂ)) (s - a)) =
        fun s => φ' (a * Ring.inverse t, t) * N.indicator (fun _ => (1 : ℂ)) (s - a) := by
      funext s
      by_cases hs : s - a ∈ N
      · have := hc hs t ht
        simp only [add_sub_cancel] at this
        rw [mul_comm (Ring.inverse t) s, this]
      · simp [Set.indicator_of_notMem hs]
    rw [h5, integral_const_mul]
    congr 1
    have h6 : ∫ s, N.indicator (fun _ => (1 : ℂ)) (s - a) ∂μK = ∫ s, N.indicator (fun _ => (1 : ℂ)) s ∂μK :=
      integral_sub_right_eq_self (fun s => N.indicator (fun _ => (1 : ℂ)) s) a
    rw [h6, integral_indicator_const _ hNm]
    rw [Complex.real_smul, mul_one]
    rfl
  have horb : A.orbK μK φ' a = ∫ t, φ' (a * Ring.inverse t, t) * A.etaK t * ((A.absK t : ℂ))⁻¹ ∂μK := by
    unfold Et.orbK
    rw [Measure.restrict_eq_self_of_ae_mem (s := {t : A.K | IsUnit t}) hae]
  rw [hLam, horb]
  have h7 : ∫ t, (∫ b, φ' (b, t) * N.indicator (fun _ => (1 : ℂ)) (t * b - a) ∂μK) * A.etaK t ∂μK =
      (((μK N).toReal : ℝ) : ℂ) * ∫ t, φ' (a * Ring.inverse t, t) * A.etaK t * ((A.absK t : ℂ))⁻¹ ∂μK := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hae] with t ht
    rw [hin t ht]
    ring
  rw [h7, ← mul_assoc, hvol, one_mul]

end GlobalTheory
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TruncatedWhittakerJHypEqOrbitalIntegralStatement

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.truncatedWhittaker_jHyp_eq_orbitalIntegral : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), SelfDual μK (A.kerK ψ) → ∀ φ', IsTest φ' → ∀ a : A.K, IsUnit a → ∀ᶠ c in 𝓝[≠] (0 : F), A.abelian₂ μK ψ a (A.jHyp μK ψ φ') c = A.orbK μK φ' a := by
  first | exact @GlobalTheory.whittaker_jHyp_eq_orbK | exact GlobalTheory.whittaker_jHyp_eq_orbK | (intros; apply GlobalTheory.whittaker_jHyp_eq_orbK <;> assumption)
end
end
