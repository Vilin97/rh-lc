module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfTruncatedFourierTendstoZeroEtaleStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnimodularHeightSqLintegralLtTopStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleHermitianPairStructureFactsStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Normed.Field.ProperSpace
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerBoundBigCell

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.LamBound

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem norm_etaK (A : Et F E) (t : A.K) : ‖A.etaK t‖ = 1 := by
  unfold Et.etaK eta
  split_ifs <;> simp

theorem absK_nonneg (A : Et F E) (t : A.K) : 0 ≤ A.absK t := by
  unfold Et.absK
  split_ifs <;> simp

theorem bdd_of_loc_const (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
    (O : Set K) (hO : IsCompact O) (Ψ : SpecialLinearGroup (Fin 2) K → ℂ) (U : Set K) (hU : U ∈ 𝓝 (0 : K))
    (hΨ : ∀ g k : SpecialLinearGroup (Fin 2) K, (∀ i j, ((k : Matrix (Fin 2) (Fin 2) K) - 1) i j ∈ U) →
      Ψ (g * k) = Ψ g) :
    ∃ C : ℝ, ∀ k : SpecialLinearGroup (Fin 2) K, (∀ i j, (k : Matrix (Fin 2) (Fin 2) K) i j ∈ O) → ‖Ψ k‖ ≤ C := by
  classical
  let T : Set (Matrix (Fin 2) (Fin 2) K) := {M | ∀ i j, M i j ∈ O} ∩ {M | M.det = 1}
  have hT : IsCompact T := by
    have h1 : IsCompact {M : Matrix (Fin 2) (Fin 2) K | ∀ i j, M i j ∈ O} := by
      have := isCompact_univ_pi (fun _ : Fin 2 => isCompact_univ_pi (fun _ : Fin 2 => hO))
      have he : {M : Matrix (Fin 2) (Fin 2) K | ∀ i j, M i j ∈ O} =
          Set.univ.pi (fun _ : Fin 2 => Set.univ.pi fun _ : Fin 2 => O) := by
        ext M
        exact ⟨fun h => Set.mem_univ_pi.2 fun i => Set.mem_univ_pi.2 fun j => h i j,
          fun h i j => Set.mem_univ_pi.1 (Set.mem_univ_pi.1 h i) j⟩
      rw [he]; exact this
    exact h1.inter_right (isClosed_eq (continuous_id.matrix_det) continuous_const)
  let N : Matrix (Fin 2) (Fin 2) K → Set (Matrix (Fin 2) (Fin 2) K) := fun M =>
    {M' | ∀ i j, (M.adjugate * M' - 1) i j ∈ U}
  have hN : ∀ M ∈ T, N M ∈ 𝓝 M := by
    intro M hM
    have hc : Continuous (fun M' : Matrix (Fin 2) (Fin 2) K => M.adjugate * M' - 1) :=
      (continuous_const.matrix_mul continuous_id).sub continuous_const
    have h0 : M.adjugate * M - 1 = 0 := by
      rw [Matrix.adjugate_mul, hM.2]; simp
    have hij : ∀ i j, ∀ᶠ M' in 𝓝 M, (M.adjugate * M' - 1) i j ∈ U := by
      intro i j
      have hcij : Continuous (fun M' : Matrix (Fin 2) (Fin 2) K => (M.adjugate * M' - 1) i j) :=
        hc.matrix_elem i j
      have := hcij.tendsto M
      simp only [h0, Matrix.zero_apply] at this
      exact this hU
    exact Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => hij i j
  obtain ⟨t, htT, hcov⟩ := hT.elim_nhds_subcover N hN
  let g : Matrix (Fin 2) (Fin 2) K → ℝ := fun M => if h : M.det = 1 then ‖Ψ ⟨M, h⟩‖ else 0
  refine ⟨∑ M ∈ t, g M, fun k hk => ?_⟩
  have hkT : (k : Matrix (Fin 2) (Fin 2) K) ∈ T := ⟨hk, k.2⟩
  obtain ⟨M, hMt, hkM⟩ := Set.mem_iUnion₂.1 (hcov hkT)
  have hdet : M.det = 1 := (htT M hMt).2
  let k₀ : SpecialLinearGroup (Fin 2) K := ⟨M, hdet⟩
  have he : Ψ k = Ψ k₀ := by
    have := hΨ k₀ (k₀⁻¹ * k) (by
      intro i j
      have := hkM i j
      exact this)
    simpa using this
  have hg : g M = ‖Ψ k₀‖ := by simp only [g, dif_pos hdet]; rfl
  rw [he, ← hg]
  exact Finset.single_le_sum (f := g) (fun M _ => by simp only [g]; split_ifs <;> positivity) hMt

theorem main : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (Ψ : SpecialLinearGroup (Fin 2) A.K → ℂ), A.InI Ψ → ∃ C : ℝ, ∀ (z : A.K) (s : A.Kˣ) (α β : A.K), α ∈ A.OK → β ∈ A.OK → (s : A.K) ∈ A.OK → (s : A.K) * z ∈ A.OK → α * s + β * (s * z) = 1 → ‖Ψ (wS A.K * nS z)‖ ≤ C * A.absK s := by
  intro F E _ _ _ _ U A Ψ hΨ
  have := U.ultraF; have := U.lcF
  have : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  let b := Module.finBasis F A.K
  have : T2Space A.K := .of_injective_continuous b.equivFun.injective
    (IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hcpt, R, hR⟩ := GlobalTheory.T.etaleHermitianPair_structure_facts F E A
  obtain ⟨V, hV, hloc⟩ := hΨ.1
  obtain ⟨C, hC⟩ := bdd_of_loc_const A.K A.OK hcpt Ψ V hV hloc
  refine ⟨C, fun z s α β hα hβ hs hsz h => ?_⟩
  have hu : (s : A.K) * ((s⁻¹ : A.Kˣ) : A.K) = 1 := Units.mul_inv s
  let k : SpecialLinearGroup (Fin 2) A.K := ⟨!![-β, α; -(s : A.K), -((s : A.K) * z)], by
    simp [Matrix.det_fin_two]; linear_combination h⟩
  have hk : wS A.K * nS z = nS (-((s : A.K) * β)) * mS s * k := by
    apply Subtype.ext
    show !![(0 : A.K), 1; -1, 0] * !![1, z; 0, 1] =
      !![1, -((s : A.K) * β); 0, 1] * !![(s : A.K), 0; 0, ((s⁻¹ : A.Kˣ) : A.K)] * !![-β, α; -(s : A.K), -((s : A.K) * z)]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      linear_combination (-1 : A.K) * h - (β * (s : A.K) * z) * hu
  have hkO : ∀ i j, (k : Matrix (Fin 2) (Fin 2) A.K) i j ∈ A.OK := by
    rw [← hR]
    have hα' : α ∈ R := by rw [← SetLike.mem_coe, hR]; exact hα
    have hβ' : β ∈ R := by rw [← SetLike.mem_coe, hR]; exact hβ
    have hs' : (s : A.K) ∈ R := by rw [← SetLike.mem_coe, hR]; exact hs
    have hsz' : (s : A.K) * z ∈ R := by rw [← SetLike.mem_coe, hR]; exact hsz
    intro i j; fin_cases i <;> fin_cases j <;> simp [k, R.neg_mem, hα', hβ', hs', hsz']
  rw [hk, hΨ.2, norm_mul, norm_mul, norm_etaK, Complex.norm_real, Real.norm_of_nonneg (absK_nonneg A _), one_mul,
    mul_comm C]
  exact mul_le_mul_of_nonneg_left (hC k hkO) (absK_nonneg A _)

end GlobalTheory.JR.LamBound
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerBoundBigCellStatement

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.whittaker_bound_big_cell : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (Ψ : SpecialLinearGroup (Fin 2) A.K → ℂ), A.InI Ψ → ∃ C : ℝ, ∀ (z : A.K) (s : A.Kˣ) (α β : A.K), α ∈ A.OK → β ∈ A.OK → (s : A.K) ∈ A.OK → (s : A.K) * z ∈ A.OK → α * s + β * (s * z) = 1 → ‖Ψ (wS A.K * nS z)‖ ≤ C * A.absK s := by
  first | exact @GlobalTheory.JR.LamBound.main | exact GlobalTheory.JR.LamBound.main | (intros; apply GlobalTheory.JR.LamBound.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerFunctionalWeylVanishOfWeylUnipotentZero

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem wS_nS_wS_eq_unit {k : Type} [CommRing k] (z : kˣ) :
    wS k * nS (z : k) * wS k = nS ((-z⁻¹ : kˣ) : k) * mS (-z⁻¹) * (wS k * nS ((-z⁻¹ : kˣ) : k)) := by
  have h1 : (z : k) * ((z⁻¹ : kˣ) : k) = 1 := z.mul_inv
  have cw : ((wS k : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = !![0, 1; -1, 0] := rfl
  have cn : ∀ t : k, ((nS t : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = !![1, t; 0, 1] :=
    fun _ => rfl
  have cm : ∀ s : kˣ, ((mS s : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      !![(s : k), 0; 0, ((s⁻¹ : kˣ) : k)] := fun _ => rfl
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, cw, cn, cm]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_fin_two] <;> ring_nf <;> simp [h1]

theorem lam_flip_eq_zero : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ Ψ : SpecialLinearGroup (Fin 2) A.K → ℂ, A.InI Ψ → (∀ z, Ψ (wS A.K * nS z) = 0) → ∀ (a : A.K) (c : F), A.abelian₂ μK ψ a (fun h => Ψ (h * wS A.K)) c = 0 := by
  intro F E _ _ _ _ _ A ψ μK hμ Ψ hΨ h0 a c
  have hnull : μK {t | ¬ IsUnit t} = 0 := (GlobalTheory.T.etaleHermitianPair_structure_facts F E A).2.2.2.2.2.2.2.2.1 μK hμ
  have hae : ∀ᵐ z ∂μK, IsUnit z := ae_iff.2 hnull
  unfold Et.abelian₂
  apply integral_eq_zero_of_ae
  apply ae_restrict_of_ae
  filter_upwards [hae] with z hz
  obtain ⟨u, rfl⟩ := hz
  simp only [Pi.zero_apply]
  rw [wS_nS_wS_eq_unit u, hΨ.2, h0, mul_zero, zero_mul]

end GlobalTheory.JR
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerFunctionalWeylVanishOfWeylUnipotentZeroStatement

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.whittakerFunctional_weyl_vanish_of_weylUnipotent_zero : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ Ψ : SpecialLinearGroup (Fin 2) A.K → ℂ, A.InI Ψ → (∀ z, Ψ (wS A.K * nS z) = 0) → ∀ (a : A.K) (c : F), A.abelian₂ μK ψ a (fun h => Ψ (h * wS A.K)) c = 0 := by
  first | exact @GlobalTheory.JR.lam_flip_eq_zero | exact GlobalTheory.JR.lam_flip_eq_zero | (intros; apply GlobalTheory.JR.lam_flip_eq_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KirillovVanishingOfLimit

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.LTwoLemma
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem u_locallyConstant (A : Et F E) (Ψ : SpecialLinearGroup (Fin 2) A.K → ℂ) (h : A.InI Ψ) :
    IsLocallyConstant (fun z => Ψ (wS A.K * nS z)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro z
  obtain ⟨U, hU, hinv⟩ := h.1
  have h0 : (0 : A.K) ∈ U := mem_of_mem_nhds hU
  have ht : Tendsto (fun y : A.K => y - z) (𝓝 z) (𝓝 0) :=
    (continuous_sub_right z).tendsto' z 0 (sub_self z)
  filter_upwards [ht hU] with y hy
  simp only [Set.mem_preimage] at hy
  have he : wS A.K * nS y = (wS A.K * nS z) * nS (y - z) := by
    rw [mul_assoc]; congr 1; apply Subtype.ext
    show !![(1 : A.K), y; 0, 1] = !![1, z; 0, 1] * !![1, y - z; 0, 1]
    rw [Matrix.mul_fin_two]; simp
  rw [he]
  apply hinv
  intro i j
  fin_cases i <;> fin_cases j <;> simp [nS, h0, hy]

theorem absK_nonneg (A : Et F E) (t : A.K) : 0 ≤ A.absK t := by
  unfold Et.absK; split_ifs <;> simp

theorem weyl_unipotent_l2_finite [Unram F E] (hB1 : type_of% GlobalTheory.T.whittaker_bound_big_cell) (hB2 : type_of% GlobalTheory.T.unimodularHeight_sq_lintegral_lt_top) (A : Et F E) (μ : Measure A.K) (hμ : μ.IsAddHaarMeasure)
    (Ψ : SpecialLinearGroup (Fin 2) A.K → ℂ) (h : A.InI Ψ) :
    ∫⁻ z, ‖Ψ (wS A.K * nS z)‖ₑ ^ 2 ∂μ < ⊤ := by
  obtain ⟨C, hC⟩ := hB1 F E A Ψ h
  have hB := hB2 F E A μ hμ
  have h0 : ENNReal.ofReal C + 1 ≠ 0 := by simp
  have hT : ENNReal.ofReal C + 1 ≠ ⊤ := by simp
  have hle : ∀ z, ‖Ψ (wS A.K * nS z)‖ₑ ≤ (ENNReal.ofReal C + 1) *
      ⨅ (s : A.Kˣ) (_ : (s : A.K) ∈ A.OK ∧ (s : A.K) * z ∈ A.OK ∧ ∃ α ∈ A.OK, ∃ β ∈ A.OK,
        α * s + β * (s * z) = 1), ENNReal.ofReal (A.absK s) := by
    intro z
    simp only [ENNReal.mul_iInf_of_ne h0 hT]
    refine le_iInf₂ fun s hs => ?_
    obtain ⟨hs1, hs2, α, hα, β, hβ, he⟩ := hs
    have hb := hC z s α β hα hβ hs1 hs2 he
    calc ‖Ψ (wS A.K * nS z)‖ₑ = ENNReal.ofReal ‖Ψ (wS A.K * nS z)‖ := (ofReal_norm_eq_enorm _).symm
      _ ≤ ENNReal.ofReal (C * A.absK s) := ENNReal.ofReal_le_ofReal hb
      _ = ENNReal.ofReal C * ENNReal.ofReal (A.absK s) := ENNReal.ofReal_mul' (absK_nonneg A _)
      _ ≤ _ := by gcongr; exact le_self_add
  calc ∫⁻ z, ‖Ψ (wS A.K * nS z)‖ₑ ^ 2 ∂μ
      ≤ ∫⁻ z, ((ENNReal.ofReal C + 1) * ⨅ (s : A.Kˣ) (_ : (s : A.K) ∈ A.OK ∧ (s : A.K) * z ∈ A.OK ∧
          ∃ α ∈ A.OK, ∃ β ∈ A.OK, α * s + β * (s * z) = 1), ENNReal.ofReal (A.absK s)) ^ 2 ∂μ :=
        lintegral_mono fun z => pow_le_pow_left' (hle z) 2
    _ = (ENNReal.ofReal C + 1) ^ 2 * ∫⁻ z, (⨅ (s : A.Kˣ) (_ : (s : A.K) ∈ A.OK ∧ (s : A.K) * z ∈ A.OK ∧
          ∃ α ∈ A.OK, ∃ β ∈ A.OK, α * s + β * (s * z) = 1), ENNReal.ofReal (A.absK s)) ^ 2 ∂μ := by
        simp_rw [mul_pow]
        exact lintegral_const_mul' _ _ (by simp)
    _ < ⊤ := ENNReal.mul_lt_top (by simp) hB

end GlobalTheory.JR.LTwoLemma

open GlobalTheory.JR.LTwoLemma in
theorem GlobalTheory.JR.kirillov_vanishing_l2 : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), SelfDual μK (A.kerK ψ) → ∀ Ψ, A.InI Ψ → (∀ a : A.K, IsUnit a → Tendsto (A.abelian₂ μK ψ a Ψ) (𝓝[≠] 0) (𝓝 0)) → (∀ z, Ψ (wS A.K * nS z) = 0) ∧ ∀ (a : A.K) (c : F), A.abelian₂ μK ψ a (fun h => Ψ (h * wS A.K)) c = 0 := by
  intro F E _ _ _ _ _ A ψ hψ μK hsd Ψ hI hlim
  have hμ : μK.IsAddHaarMeasure := hsd.1
  have hu : (fun z => Ψ (wS A.K * nS z)) = 0 :=
    GlobalTheory.T.eq_zero_of_truncatedFourier_tendsto_zero_etale F E A ψ hψ μK hsd _ (u_locallyConstant A Ψ hI) (weyl_unipotent_l2_finite GlobalTheory.T.whittaker_bound_big_cell GlobalTheory.T.unimodularHeight_sq_lintegral_lt_top A μK hμ Ψ hI) hlim
  have h1 : ∀ z, Ψ (wS A.K * nS z) = 0 := fun z => congrFun hu z
  exact ⟨h1, GlobalTheory.T.whittakerFunctional_weyl_vanish_of_weylUnipotent_zero F E A ψ μK hμ Ψ hI h1⟩
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KirillovVanishingOfLimitStatement

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.kirillov_vanishing_of_limit : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), SelfDual μK (A.kerK ψ) → ∀ Ψ, A.InI Ψ → (∀ a : A.K, IsUnit a → Tendsto (A.abelian₂ μK ψ a Ψ) (𝓝[≠] 0) (𝓝 0)) → (∀ z, Ψ (wS A.K * nS z) = 0) ∧ ∀ (a : A.K) (c : F), A.abelian₂ μK ψ a (fun h => Ψ (h * wS A.K)) c = 0 := by
  first | exact @GlobalTheory.JR.kirillov_vanishing_l2 | exact GlobalTheory.JR.kirillov_vanishing_l2 | (intros; apply GlobalTheory.JR.kirillov_vanishing_l2 <;> assumption)
end
end
