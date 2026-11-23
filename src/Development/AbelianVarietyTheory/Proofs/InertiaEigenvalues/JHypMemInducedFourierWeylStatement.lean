module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FourierEtaleKEqIntegralPartialFourier
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
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JHypUnipotentTorusEquivarianceStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleHermitianPairStructureFactsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualMeasureExistsUniqueFourierInversionStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnifConst
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnifConst
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FourierEtaleKEqIntegralPartialFourierStatement

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.fourierEtaleK_eq_integral_partialFourier : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ φ' : A.K × A.K → ℂ, IsTest φ' → ∀ b c : A.K, A.fourK μK ψ φ' (b, c) = fourB μK (A.kerK ψ) (fun c' => A.tilde μK ψ φ' c' c) b := by
  first | exact @GlobalTheory.FourKFub.fourK_eq_fourB_tilde | exact GlobalTheory.FourKFub.fourK_eq_fourB_tilde | (intros; apply GlobalTheory.FourKFub.fourK_eq_fourB_tilde <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PartialFourierEtaleKProdLocallyConstantCompactSu

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.TildeTest

theorem main : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ φ' : A.K × A.K → ℂ, IsTest φ' → IsTest (fun p : A.K × A.K => A.tilde μK ψ φ' p.1 p.2) := by
  intro F E _ _ _ _ _ A ψ hψ μK hμ φ' hφ
  set T : A.K → A.K → ℂ := fun c u => A.tilde μK ψ φ' c u with hTdef
  have hslice : ∀ c, IsTest (fun u => T c u) := by
    intro c
    have hnd := (GlobalTheory.T.etaleHermitianPair_structure_facts F E A).2.2.1
    have h := (GlobalTheory.T.selfDual_measure_exists_unique_fourier_inversion F E ψ hψ A.K (Algebra.traceForm F A.K) (Algebra.traceForm_isSymm F) hnd).2 μK hμ
      (fun b => φ' (b, c)) (GlobalTheory.TestFn.slice_test φ' hφ c)
    have heq : (fun u => T c u) = fourB μK (fun x y => ψ ((Algebra.traceForm F A.K) x y)) (fun b => φ' (b, c)) := by
      funext u
      simp [hTdef, Et.tilde, fourB, Et.psiK, Algebra.traceForm_apply, mul_comm]
    rw [heq]
    exact h
  obtain ⟨V, hV, hVf⟩ := GlobalTheory.TestFn.unif_const (A.K × A.K) φ' hφ
  set V₂ : Set A.K := {v | ((0 : A.K), v) ∈ V} with hV₂def
  have hV₂ : V₂ ∈ 𝓝 (0 : A.K) := by
    have hc : Continuous (fun v : A.K => ((0 : A.K), v)) := by fun_prop
    exact hc.continuousAt.preimage_mem_nhds (by rw [show ((0 : A.K), (0 : A.K)) = (0 : A.K × A.K) from rfl]; exact hV)
  have hshift : ∀ c c', c' - c ∈ V₂ → ∀ u, T c' u = T c u := by
    intro c c' hcc u
    simp only [hTdef, Et.tilde]
    congr 1; funext b
    have := hVf (b, c) (0, c' - c) hcc
    simp only [Prod.mk_add_mk, add_zero, add_sub_cancel] at this
    rw [this]
  have hnbhd : ∀ c : A.K, {c' | c' - c ∈ V₂} ∈ 𝓝 c := by
    intro c
    have hc : Continuous (fun c' : A.K => c' - c) := by fun_prop
    exact hc.continuousAt.preimage_mem_nhds (by simpa using hV₂)
  have hlc : IsLocallyConstant (fun p : A.K × A.K => T p.1 p.2) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    rintro ⟨c₀, u₀⟩
    have hu : {u | T c₀ u = T c₀ u₀} ∈ 𝓝 u₀ := ((hslice c₀).1.isOpen_fiber _).mem_nhds rfl
    rw [nhds_prod_eq]
    filter_upwards [prod_mem_prod (hnbhd c₀) hu] with p hp
    rw [hshift c₀ p.1 hp.1 p.2]; exact hp.2
  refine ⟨hlc, ?_⟩
  have hC₂ : IsCompact (Prod.snd '' tsupport φ') := hφ.2.image continuous_snd
  obtain ⟨t, -, hcover⟩ := hC₂.elim_nhds_subcover (fun c => {c' | c' - c ∈ V₂}) (fun c _ => hnbhd c)
  have hK : IsCompact ((Prod.snd '' tsupport φ') ×ˢ ⋃ c ∈ t, tsupport (fun u => T c u)) :=
    hC₂.prod (t.isCompact_biUnion fun c _ => (hslice c).2)
  have hzero : ∀ c ∉ Prod.snd '' tsupport φ', ∀ u, T c u = 0 := by
    intro c hc u
    have h0 : ∀ b, φ' (b, c) = 0 := fun b => image_eq_zero_of_notMem_tsupport (fun h => hc ⟨(b, c), h, rfl⟩)
    simp [hTdef, Et.tilde, h0]
  have hsupp : Function.support (fun p : A.K × A.K => T p.1 p.2) ⊆
      (Prod.snd '' tsupport φ') ×ˢ ⋃ c ∈ t, tsupport (fun u => T c u) := by
    rintro ⟨c, u⟩ hp
    have hc : c ∈ Prod.snd '' tsupport φ' := by
      by_contra hc; exact hp (hzero c hc u)
    refine ⟨hc, ?_⟩
    obtain ⟨c', hc't, hcc'⟩ := Set.mem_iUnion₂.mp (hcover hc)
    refine Set.mem_iUnion₂.mpr ⟨c', hc't, subset_tsupport _ ?_⟩
    show T c' u ≠ 0
    rw [← hshift c' c hcc' u]; exact hp
  have hclosed : IsClosed (Function.support (fun p : A.K × A.K => T p.1 p.2)) := by
    have := (hlc.isOpen_fiber 0).isClosed_compl
    convert this using 1
    ext p; simp [Function.mem_support]
  have hts : tsupport (fun p : A.K × A.K => T p.1 p.2) = Function.support (fun p : A.K × A.K => T p.1 p.2) :=
    hclosed.closure_eq
  unfold HasCompactSupport
  rw [hts]
  exact hK.of_isClosed_subset hclosed hsupp

end GlobalTheory.JR.TildeTest
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PartialFourierEtaleKProdLocallyConstantCompactSuStatement

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.partialFourier_etaleKProd_locallyConstantCompactSupport : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ φ' : A.K × A.K → ℂ, IsTest φ' → IsTest (fun p : A.K × A.K => A.tilde μK ψ φ' p.1 p.2) := by
  first | exact @GlobalTheory.JR.TildeTest.main | exact GlobalTheory.JR.TildeTest.main | (intros; apply GlobalTheory.JR.TildeTest.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TestFunctionLocallyInvariant

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.RowSmooth

theorem row_smooth : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (T : R × R → ℂ), IsTest T → ∃ U ∈ 𝓝 (0 : R), ∀ k : SpecialLinearGroup (Fin 2) R, (∀ i j, ((k : Matrix (Fin 2) (Fin 2) R) - 1) i j ∈ U) → ∀ c u : R, T (c * k 0 0 + u * k 1 0, c * k 0 1 + u * k 1 1) = T (c, u) := by
  intro R _ _ _ T hT
  classical
  obtain ⟨V, hV, hVT⟩ := GlobalTheory.TestFn.unif_const (R × R) T hT
  have hC : IsCompact (tsupport T) := hT.2
  let φ : (R × R × R × R) → R × R → R × R := fun e v =>
    (v.1 * e.1 + v.2 * e.2.2.1, v.1 * e.2.1 + v.2 * e.2.2.2)
  have hφ : Continuous (fun z : (R × R × R × R) × (R × R) => φ z.1 z.2) := by
    simp only [φ]; fun_prop
  have hev : ∀ᶠ e in 𝓝 (0 : R × R × R × R), ∀ v ∈ tsupport T, φ e v ∈ V := by
    refine hC.eventually_forall_of_forall_eventually (P := fun e v => φ e v ∈ V) ?_
    intro v _
    have h0 : φ 0 v = 0 := by simp [φ]
    have : V ∈ 𝓝 (φ (0 : R × R × R × R) v) := by rw [h0]; exact hV
    exact hφ.continuousAt (x := ((0 : R × R × R × R), v)) this
  obtain ⟨A₁, hA₁, S₁, hS₁, hsub₁⟩ := mem_nhds_prod_iff.mp (show _ ∈ 𝓝 ((0 : R), ((0 : R), (0 : R), (0 : R))) from hev)
  obtain ⟨A₂, hA₂, S₂, hS₂, hsub₂⟩ := mem_nhds_prod_iff.mp hS₁
  obtain ⟨A₃, hA₃, A₄, hA₄, hsub₃⟩ := mem_nhds_prod_iff.mp hS₂
  set U₀ : Set R := A₁ ∩ A₂ ∩ A₃ ∩ A₄ with hU₀def
  have hU₀ : U₀ ∈ 𝓝 (0 : R) := inter_mem (inter_mem (inter_mem hA₁ hA₂) hA₃) hA₄
  have key : ∀ a b c d : R, a ∈ U₀ → b ∈ U₀ → c ∈ U₀ → d ∈ U₀ → ∀ v ∈ tsupport T,
      T (v + φ (a, b, c, d) v) = T v := by
    intro a b c d ha hb hc hd v hv
    have hmem : ((a, b, c, d) : R × R × R × R) ∈ {e | ∀ v ∈ tsupport T, φ e v ∈ V} :=
      hsub₁ ⟨ha.1.1.1, hsub₂ ⟨hb.1.1.2, hsub₃ ⟨hc.1.2, hd.2⟩⟩⟩
    exact hVT v _ (hmem v hv)
  refine ⟨U₀ ∩ (fun x => -x) ⁻¹' U₀, inter_mem hU₀
    (continuous_neg.continuousAt.preimage_mem_nhds (by simpa using hU₀)), ?_⟩
  intro k hk c u
  have hdet : k 0 0 * k 1 1 - k 0 1 * k 1 0 = 1 := by
    have := k.2; rw [Matrix.det_fin_two] at this; exact this
  have e00 := hk 0 0
  have e01 := hk 0 1
  have e10 := hk 1 0
  have e11 := hk 1 1
  simp only [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), sub_zero] at e00 e01 e10 e11
  by_cases hv : (c, u) ∈ tsupport T
  · have := key (k 0 0 - 1) (k 0 1) (k 1 0) (k 1 1 - 1) e00.1 e01.1 e10.1 e11.1 (c, u) hv
    rw [← this]
    congr 1
    simp only [φ, Prod.mk_add_mk]
    ext <;> simp <;> ring
  by_cases hw : (c * k 0 0 + u * k 1 0, c * k 0 1 + u * k 1 1) ∈ tsupport T
  · have := key (k 1 1 - 1) (-k 0 1) (-k 1 0) (k 0 0 - 1) e11.1 e01.2 e10.2 e00.1 _ hw
    rw [← this]
    congr 1
    simp only [φ, Prod.mk_add_mk]
    ext
    · simp; linear_combination c * hdet
    · simp; linear_combination u * hdet
  · rw [image_eq_zero_of_notMem_tsupport hv, image_eq_zero_of_notMem_tsupport hw]

end GlobalTheory.RowSmooth
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TestFunctionLocallyInvariantStatement

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.test_function_locally_invariant : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (T : R × R → ℂ), IsTest T → ∃ U ∈ 𝓝 (0 : R), ∀ k : SpecialLinearGroup (Fin 2) R, (∀ i j, ((k : Matrix (Fin 2) (Fin 2) R) - 1) i j ∈ U) → ∀ c u : R, T (c * k 0 0 + u * k 1 0, c * k 0 1 + u * k 1 1) = T (c, u) := by
  first | exact @GlobalTheory.RowSmooth.row_smooth | exact GlobalTheory.RowSmooth.row_smooth | (intros; apply GlobalTheory.RowSmooth.row_smooth <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JHypMemInducedFourierWeyl

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.HypJ

theorem main : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
    [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), SelfDual μK (A.kerK ψ) →
    ∀ φ', IsTest φ' → A.InI (A.jHyp μK ψ φ') ∧
      ∀ h, A.jHyp μK ψ (A.fourK μK ψ φ') h = A.jHyp μK ψ φ' (h * wS A.K) := by
  intro F E _ _ _ _ _ A ψ hψ μK hsd φ' hφ
  have hH : μK.IsAddHaarMeasure := hsd.1
  have hT := GlobalTheory.T.partialFourier_etaleKProd_locallyConstantCompactSupport F E A ψ hψ μK hH φ' hφ
  refine ⟨⟨?_, fun z s g => GlobalTheory.T.jHyp_unipotent_torus_equivariance F E A μK hH ψ φ' z s g⟩, ?_⟩
  · obtain ⟨U, hU, hk⟩ := GlobalTheory.T.test_function_locally_invariant A.K _ hT
    refine ⟨U, hU, fun g k hkU => ?_⟩
    unfold Et.jHyp
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    have := hk k hkU (t * g 1 0) (t * g 1 1)
    simp only at this
    have e1 : ((g * k : SpecialLinearGroup (Fin 2) A.K) : Matrix (Fin 2) (Fin 2) A.K) 1 0 =
        g 1 0 * k 0 0 + g 1 1 * k 1 0 := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    have e2 : ((g * k : SpecialLinearGroup (Fin 2) A.K) : Matrix (Fin 2) (Fin 2) A.K) 1 1 =
        g 1 0 * k 0 1 + g 1 1 * k 1 1 := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    simp only [e1, e2]
    rw [← this]; congr 2 <;> ring
  · intro h
    have key : ∀ c u, A.tilde μK ψ (A.fourK μK ψ φ') c u = A.tilde μK ψ φ' (-u) c := by
      intro c u
      have hG := GlobalTheory.TestFn.slice_test _ hT c
      have := hsd.2 _ hG u
      rw [← this]
      unfold Et.tilde fourB
      refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
      simp only
      rw [GlobalTheory.T.fourierEtaleK_eq_integral_partialFourier F E A ψ hψ μK hH φ' hφ b c]
      unfold fourB Et.tilde Et.kerK
      rw [mul_comm u b]
    unfold Et.jHyp
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only
    rw [key]
    congr 2
    · rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]; simp [wS]
    · rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]; simp [wS]

end GlobalTheory.JR.HypJ
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JHypMemInducedFourierWeylStatement

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.jHyp_mem_induced_fourier_weyl : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), SelfDual μK (A.kerK ψ) → ∀ φ', IsTest φ' → A.InI (A.jHyp μK ψ φ') ∧ ∀ h, A.jHyp μK ψ (A.fourK μK ψ φ') h = A.jHyp μK ψ φ' (h * wS A.K) := by
  first | exact @GlobalTheory.JR.HypJ.main | exact GlobalTheory.JR.HypJ.main | (intros; apply GlobalTheory.JR.HypJ.main <;> assumption)
end
end
