module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SBridgeAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.IntegralMomentReduction.PrimalY
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.InstLCSL
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.IntegralMomentReduction.MtInvUpper
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.UnitaryConeEstimates.OmG
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Topology.Algebra.Group.Matrix
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.UnitaryConeEstimates.AbsLeA
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.UnitaryConeEstimates.ContVal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Presheaf
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.UnitaryConeEstimates.ContVal
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.IntegralMomentReduction.SRedOf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImportsLast
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.HaveILetI
import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.StabDirectedSystem
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.Unimodular
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.UnitaryConeEstimates.PhMemUnitary

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.IntegralMomentReduction.SetLIntegralLeOfMul

section

@[expose] public section

noncomputable section

open Matrix MeasureTheory
open scoped ENNReal

namespace PositivityTheory.KB.TwSMInt2

open PositivityTheory.KB.MomentRationality.Cz.Pk

variable {ι : Type} {N : ℕ}

theorem setLIntegral_le_of_mul {α : Type*} [MeasurableSpace α] (μ : Measure α) {X : Set α} (hX : MeasurableSet X)
    (f : α → ℝ≥0∞) (D : ℝ≥0∞) (h : ∀ x ∈ X, f x * μ X ≤ D) : ∫⁻ x in X, f x ∂μ ≤ D := by
  rcases eq_or_ne (μ X) 0 with h0 | h0
  · simp [Measure.restrict_eq_zero.mpr h0]
  rcases eq_or_ne D ⊤ with hD | hD
  · simp [hD]
  rcases eq_or_ne (μ X) ⊤ with htop | htop
  · have hz : ∀ x ∈ X, f x = 0 := by
      intro x hx
      by_contra hne
      have := h x hx
      rw [htop, ENNReal.mul_top hne] at this
      exact hD (top_le_iff.mp this)
    calc ∫⁻ x in X, f x ∂μ = ∫⁻ _ in X, 0 ∂μ := setLIntegral_congr_fun hX hz
      _ = 0 := lintegral_zero
      _ ≤ D := bot_le
  · have hle : ∀ x ∈ X, f x ≤ D / μ X := fun x hx =>
      (ENNReal.le_div_iff_mul_le (Or.inl h0) (Or.inl htop)).mpr (h x hx)
    calc ∫⁻ x in X, f x ∂μ ≤ ∫⁻ _ in X, D / μ X ∂μ := setLIntegral_mono' hX hle
      _ = D / μ X * μ X := setLIntegral_const X _
      _ = D := ENNReal.div_mul_cancel h0 htop

theorem main_of_pack (hN : 2 ≤ N) [Fintype ι] [Nonempty ι] [MeasurableSpace (G ι N)] [BorelSpace (G ι N)]
    (μ : Measure (G ι N)) [μ.IsHaarMeasure] {P : Set (G ι N)} (hPc : IsCompact P)
    (T B : ℝ) (hpk : ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ (m : Fin N → ℤ) (s0 : Fin N → ℝ), ∑ i, s0 i = 0 → Cone T s0 →
      (∀ i, (m i : ℝ) ≤ s0 i ∧ s0 i ≤ m i + 1) →
      μ (Xb P T m) ≤ K * ENNReal.ofReal (Real.exp (-2 * Phi s0))) (hB : B < 2 * ((N : ℝ) - 1)) (C : ℝ≥0∞) (hC : C ≠ ⊤) (f : G ι N → ℝ≥0∞)
    (hf : ∀ p ∈ P, ∀ (s : Fin N → ℝ) (hs : ∑ i, s i = 0), Cone T s → ∀ k ∈ KS,
      f (p * dg s hs * k) ≤ C * ENNReal.ofReal (Real.exp (B * W s))) :
    ∫⁻ x in Sg P T, f x ∂μ < ⊤ := by
  obtain ⟨K, hK, hμ⟩ := hpk
  obtain ⟨c, ε, hε, hexp⟩ := ineq hN T B hB
  set D : (Fin N → ℤ) → ℝ≥0∞ := fun m => C * K * (ENNReal.ofReal (Real.exp (c + ε * N)) *
    ENNReal.ofReal (Real.exp (-(ε * ∑ i, |((m i : ℤ) : ℝ)|)))) with hD
  have hcov : Sg P T ⊆ ⋃ m, Xb P T m := by
    rintro x ⟨p, hp, s, hs, hcone, k, hk, rfl⟩
    refine Set.mem_iUnion.mpr ⟨fun i => ⌊s i⌋, p, hp, s, hs, hcone, fun i => ⟨Int.floor_le _, (Int.lt_floor_add_one _).le⟩, k, hk, rfl⟩
  have hpiece : ∀ m, ∫⁻ x in Xb P T m, f x ∂μ ≤ D m := by
    intro m
    refine setLIntegral_le_of_mul μ (cpt_X hPc T m).measurableSet f (D m) ?_
    rintro x ⟨p, hp, s, hs, hcone, hb, k, hk, rfl⟩
    have h1 := hf p hp s hs hcone k hk
    have h2 := hμ m s hs hcone hb
    have habs : ∑ i, |((m i : ℤ) : ℝ)| ≤ ∑ i, |s i| + N := by
      have : ∀ i, |((m i : ℤ) : ℝ)| ≤ |s i| + 1 := by
        intro i
        have := (hb i).1
        have := (hb i).2
        calc |((m i : ℤ) : ℝ)| = |s i - (s i - m i)| := by ring_nf
          _ ≤ |s i| + |s i - m i| := abs_sub _ _
          _ ≤ |s i| + 1 := by
            gcongr
            rw [abs_le]
            constructor <;> linarith
      calc ∑ i, |((m i : ℤ) : ℝ)| ≤ ∑ i, (|s i| + 1) := Finset.sum_le_sum fun i _ => this i
        _ = ∑ i, |s i| + N := by simp [Finset.sum_add_distrib]
    have hreal : Real.exp (B * W s) * Real.exp (-2 * Phi s) ≤
        Real.exp (c + ε * N) * Real.exp (-(ε * ∑ i, |((m i : ℤ) : ℝ)|)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have := hexp s hs hcone
      nlinarith
    calc f (p * dg s hs * k) * μ (Xb P T m)
        ≤ (C * ENNReal.ofReal (Real.exp (B * W s))) * (K * ENNReal.ofReal (Real.exp (-2 * Phi s))) :=
          mul_le_mul' h1 h2
      _ = C * K * ENNReal.ofReal (Real.exp (B * W s) * Real.exp (-2 * Phi s)) := by
          rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
          ring
      _ ≤ C * K * ENNReal.ofReal (Real.exp (c + ε * N) * Real.exp (-(ε * ∑ i, |((m i : ℤ) : ℝ)|))) := by
          gcongr
      _ = D m := by
          rw [hD, ENNReal.ofReal_mul (Real.exp_pos _).le]
  have hsum : ∑' m, D m ≠ ⊤ := by
    simp only [hD]
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top hC hK)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (summ ε hε))
  calc ∫⁻ x in Sg P T, f x ∂μ ≤ ∫⁻ x in ⋃ m, Xb P T m, f x ∂μ := lintegral_mono_set hcov
    _ ≤ ∑' m, ∫⁻ x in Xb P T m, f x ∂μ := lintegral_iUnion_le _ _
    _ ≤ ∑' m, D m := ENNReal.tsum_le_tsum hpiece
    _ < ⊤ := lt_top_iff_ne_top.mpr hsum

end PositivityTheory.KB.TwSMInt2

end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.IntegralMomentReduction.SIntB

section

@[expose] public section

noncomputable section

open NumberField MeasureTheory

namespace PositivityTheory.KB.TwSMInt2

theorem sIntB : PositivityTheory.KB.SIntB := by
  intro L _ _ _ N hN μ _ M T B hB C hC f hf
  exact main_of_pack (ι := InfinitePlace L) hN μ (MomentRationality.Cz.Pk.cpt_Om M) T B
    (pack μ (MomentRationality.Cz.Pk.cpt_Om M) M T fun p hp w => ⟨hp.1 w, hp.2.1 w⟩) hB C hC f hf

end PositivityTheory.KB.TwSMInt2

end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.DiscreteSpecialLinearGroupRingOfIntegers

section

@[expose] public section

noncomputable section

open NumberField NumberField.InfinitePlace Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.MomentRationality.Disc

theorem eq_zero_of_lt_one {L : Type} [Field L] [NumberField L] (a : 𝓞 L)
    (h : ∀ w : InfinitePlace L, w (a : L) < 1) : a = 0 := by
  apply GlobalTheory.SmallIntegerVanishing.eq_zero_of_small <;> assumption

theorem continuous_entry {L : Type} [Field L] [NumberField L] {N : ℕ} (w : InfinitePlace L) (i j : Fin N) :
    Continuous fun x : Sp L N => mt x w i j := by
  fun_prop

theorem mt_latS {L : Type} [Field L] [NumberField L] {N : ℕ} (σ : SpecialLinearGroup (Fin N) (𝓞 L))
    (w : InfinitePlace L) (i j : Fin N) :
    mt ((MonoidHom.pi fun w : InfinitePlace L => SpecialLinearGroup.map (n := Fin N) (embO w)) σ) w i j =
      w.embedding (((σ : Matrix (Fin N) (Fin N) (𝓞 L)) i j : 𝓞 L) : L) := rfl

theorem countable_O (L : Type) [Field L] [NumberField L] : Countable (𝓞 L) :=
  (RingOfIntegers.basis L).equivFun.injective.countable

end PositivityTheory.KB.MomentRationality.Disc

namespace PositivityTheory.KB

open MomentRationality MomentRationality.Disc

theorem discrete_specialLinearGroup_ringOfIntegers : SDisc := by
  intro L _ _ N
  refine ⟨?_, ?_⟩
  · rw [discreteTopology_iff_isOpen_singleton_one]
    let U : Set (Sp L N) :=
      {x | ∀ w i j, ‖mt x w i j - (1 : Matrix (Fin N) (Fin N) ℂ) i j‖ < 1}
    have hU : IsOpen U := by
      simp only [U, Set.setOf_forall]
      exact isOpen_iInter_of_finite fun w => isOpen_iInter_of_finite fun i =>
        isOpen_iInter_of_finite fun j =>
          isOpen_lt ((continuous_entry w i j).sub continuous_const).norm continuous_const
    refine isOpen_induced_iff.2 ⟨U, hU, ?_⟩
    ext ⟨γ, hγ⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hγU
      obtain ⟨σ, rfl⟩ := hγ
      have hσ : σ = 1 := by
        refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
        have h0 := eq_zero_of_lt_one
          (((σ : Matrix (Fin N) (Fin N) (𝓞 L)) i j) - (1 : Matrix (Fin N) (Fin N) (𝓞 L)) i j) (fun w => ?_)
        · simpa using sub_eq_zero.1 h0
        · have h1 := hγU w i j
          rw [mt_latS] at h1
          rw [← norm_embedding_eq]
          convert h1 using 2
          by_cases hij : i = j
          · subst hij
            simp
          · simp [Matrix.one_apply, hij]
      subst hσ
      apply Subtype.ext
      simp
    · intro h
      have h' : γ = 1 := congrArg Subtype.val h
      subst h'
      intro w i j
      have hone : mt (1 : Sp L N) w = 1 := rfl
      rw [hone, sub_self, norm_zero]
      exact one_pos
  · haveI := countable_O L
    haveI : Countable (Matrix (Fin N) (Fin N) (𝓞 L)) :=
      inferInstanceAs (Countable (Fin N → Fin N → 𝓞 L))
    haveI : Countable (SpecialLinearGroup (Fin N) (𝓞 L)) :=
      inferInstanceAs (Countable {A : Matrix (Fin N) (Fin N) (𝓞 L) // A.det = 1})
    exact (MonoidHom.rangeRestrict_surjective
      (MonoidHom.pi fun w : InfinitePlace L => SpecialLinearGroup.map (n := Fin N) (embO w))).countable

end PositivityTheory.KB

end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.SetLIntegralPreimageMulLeft

section

@[expose] public section

noncomputable section

open NumberField NumberField.InfinitePlace Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL GroundTheory.Automorphic
open scoped ENNReal Pointwise

namespace PositivityTheory.KB.MomentRationality.Assem

section General

variable {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G]

theorem lintegral_le_of_cover (μ : Measure G) [μ.IsMulLeftInvariant] (Γ : Subgroup G) [Countable Γ]
    {F T : Set G} (hF : IsFundamentalDomain Γ F μ) (f : G → ℝ≥0∞) (hf : ∀ γ ∈ Γ, ∀ x, f (γ * x) = f x)
    (hT : ∀ x ∈ F, ∃ γ ∈ Γ, γ * x ∈ T) : ∫⁻ x in F, f x ∂μ ≤ ∫⁻ x in T, f x ∂μ := by
  have hcov : F ⊆ ⋃ g : Γ, g • T ∩ F := by
    intro x hx
    obtain ⟨γ, hγ, hxT⟩ := hT x hx
    refine Set.mem_iUnion.2 ⟨(⟨γ, hγ⟩ : Γ)⁻¹, ?_, hx⟩
    rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv]
    exact hxT
  calc ∫⁻ x in F, f x ∂μ ≤ ∫⁻ x in ⋃ g : Γ, g • T ∩ F, f x ∂μ := lintegral_mono_set hcov
    _ ≤ ∑' g : Γ, ∫⁻ x in g • T ∩ F, f x ∂μ := lintegral_iUnion_le _ _
    _ = ∫⁻ x in T, f x ∂μ := by
      rw [hF.setLIntegral_eq_tsum' f T]
      refine tsum_congr fun g => lintegral_congr fun x => ?_
      rw [Subgroup.smul_def]
      exact (hf _ (g⁻¹).2 x).symm

theorem setLIntegral_preimage_mul_left (μ : Measure G) [μ.IsMulLeftInvariant] (c : G) (S : Set G)
    (f : G → ℝ≥0∞) : ∫⁻ x in (fun x => c⁻¹ * x) ⁻¹' S, f x ∂μ = ∫⁻ y in S, f (c * y) ∂μ := by
  have key := (measurePreserving_mul_left μ c).setLIntegral_comp_preimage_emb
    (measurableEmbedding_mulLeft c) f ((fun x => c⁻¹ * x) ⁻¹' S)
  simpa [Set.preimage_preimage] using key.symm

end General

variable {L : Type} [Field L] [NumberField L] {N : ℕ}

omit [NumberField L] in
theorem continuous_ofS : Continuous (ofS L N) := by
  refine continuous_pi fun w => ?_
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · change Continuous fun x : Sp L N => ((x w : Matrix.SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)
    exact continuous_subtype_val.comp (continuous_apply w)
  · change Continuous fun x : Sp L N => (((x w)⁻¹ : Matrix.SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)
    exact continuous_subtype_val.comp ((continuous_apply w).inv)

omit [NumberField L] in
theorem ofS_latS_mul {γ : Sp L N} (hγ : γ ∈ latS L N) (x : Sp L N) :
    ∃ δ : Gm L N, ofS L N (γ * x) = emb L N δ * ofS L N x := by
  obtain ⟨g, rfl⟩ := hγ
  refine ⟨Matrix.SpecialLinearGroup.toGL g, ?_⟩
  rw [map_mul]
  congr 1
  funext w
  ext i j
  rfl

end PositivityTheory.KB.MomentRationality.Assem

namespace PositivityTheory.KB

open MomentRationality MomentRationality.Assem

theorem sMom_of_parts (hD : SDisc) (hH : SHtB) (hI : SIntB) (hR : SRed) (h : SHt) : SMom := by
  intro L _ _ hL A
  refine ⟨A + 2, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := by omega
  obtain ⟨hdisc, hcount⟩ := hD L N
  haveI := hdisc
  haveI := hcount
  obtain ⟨hcont, hinv, ⟨c0, hc0, hge⟩, -⟩ := h L hL N hN1
  obtain ⟨ι, hfin, c, M, T, hrat, hcov⟩ := hR L hL N hN1
  haveI := hfin
  let μ : Measure (Sp L N) := Measure.haar
  have hF : IsFundamentalDomain (latS L N)
      (GroundTheory.Automorphic.RightCosetSpace.fundamentalDomain (latS L N)) μ :=
    GroundTheory.Automorphic.RightCosetSpace.isFundamentalDomain_fundamentalDomain _ μ
  have hpos : ∀ x : Sp L N, 0 ≤ ht (ofS L N x) := fun x => le_trans hc0.le (hge _)
  have key : ∀ n : ℕ, n + 1 < N →
      ∫⁻ x in GroundTheory.Automorphic.RightCosetSpace.fundamentalDomain (latS L N),
        ENNReal.ofReal (ht (ofS L N x) ^ n) ∂μ < ∞ := by
    intro n hn
    let f : Sp L N → ℝ≥0∞ := fun x => ENNReal.ofReal (ht (ofS L N x) ^ n)
    have hfinv : ∀ γ ∈ latS L N, ∀ x, f (γ * x) = f x := by
      intro γ hγ x
      obtain ⟨δ, hδ⟩ := PositivityTheory.KB.MomentRationality.Assem.ofS_latS_mul hγ x
      simp only [f, hδ, hinv]
    have hcover : ∀ x ∈ GroundTheory.Automorphic.RightCosetSpace.fundamentalDomain (latS L N),
        ∃ γ ∈ latS L N, γ * x ∈ ⋃ j, (fun y => (c j)⁻¹ * y) ⁻¹' Sieg L N M T := by
      intro x _
      obtain ⟨γ, hγ, j, hj⟩ := hcov x
      exact ⟨γ, hγ, Set.mem_iUnion.2 ⟨j, hj⟩⟩
    refine lt_of_le_of_lt (PositivityTheory.KB.MomentRationality.Assem.lintegral_le_of_cover μ (latS L N) hF f hfinv hcover) ?_
    refine lt_of_le_of_lt (lintegral_iUnion_le _ _) ?_
    rw [tsum_fintype]
    refine ENNReal.sum_lt_top.2 fun j _ => ?_
    rw [PositivityTheory.KB.MomentRationality.Assem.setLIntegral_preimage_mul_left]
    obtain ⟨C, hC⟩ := hH L hL N hN1 (c j) (hrat j) M
    have hN2 : 2 ≤ N := by omega
    refine hI L hL N hN2 μ M T ((2 * n : ℕ) : ℝ) (by
        have : (n : ℝ) + 1 < N := by exact_mod_cast hn
        push_cast
        linarith) (ENNReal.ofReal (max C 0 ^ n)) ENNReal.ofReal_ne_top
      (fun y => f (c j * y)) ?_
    intro p hp s hs _ k hk
    have h1 : ht (ofS L N (c j * (p * dg L N s hs * k))) ≤ max C 0 * Real.exp (2 * W s) :=
      le_trans (hC p hp s hs k hk)
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
    have h2 : ht (ofS L N (c j * (p * dg L N s hs * k))) ^ n ≤
        max C 0 ^ n * Real.exp (((2 * n : ℕ) : ℝ) * W s) := by
      calc _ ≤ (max C 0 * Real.exp (2 * W s)) ^ n := pow_le_pow_left₀ (hpos _) h1 n
        _ = max C 0 ^ n * Real.exp (((2 * n : ℕ) : ℝ) * W s) := by
          rw [mul_pow, ← Real.exp_nat_mul]
          congr 2
          push_cast
          ring
    calc f (c j * (p * dg L N s hs * k))
        ≤ ENNReal.ofReal (max C 0 ^ n * Real.exp (((2 * n : ℕ) : ℝ) * W s)) :=
          ENNReal.ofReal_le_ofReal h2
      _ = ENNReal.ofReal (max C 0 ^ n) * ENNReal.ofReal (Real.exp (((2 * n : ℕ) : ℝ) * W s)) :=
          ENNReal.ofReal_mul (pow_nonneg (le_max_right _ _) _)
  have hvol : μ (GroundTheory.Automorphic.RightCosetSpace.fundamentalDomain (latS L N)) < ∞ := by
    have := key 0 (by omega)
    simpa using this
  haveI : IsFiniteMeasure (GroundTheory.Automorphic.RightCosetSpace.quotientMeasure (latS L N) μ) := by
    refine ⟨?_⟩
    have h0 := GroundTheory.Automorphic.RightCosetSpace.lintegral_quotientMeasure (latS L N) μ (fun _ => 1)
    rw [lintegral_one, setLIntegral_one] at h0
    rw [h0]
    exact hvol
  have hright : μ.IsMulRightInvariant :=
    GroundTheory.Automorphic.RightCosetSpace.isMulRightInvariant_of_isFiniteMeasure_quotientMeasure (latS L N) μ
  refine ⟨⟨μ, _, inferInstance, hright, hF, hvol⟩, ?_⟩
  refine ⟨((hcont.comp (PositivityTheory.KB.MomentRationality.Assem.continuous_ofS)).pow A).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => pow_nonneg (hpos x) A)]
  exact key A (by omega)

end PositivityTheory.KB

end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.IntegralMomentReduction.SMomOf

section

@[expose] public section

namespace PositivityTheory.KB.TwSMInt2

theorem sMom_of (h : SHt) : SMom :=
  sMom_of_parts discrete_specialLinearGroup_ringOfIntegers sHtB sIntB (sRed_of sRedGL2) h

end PositivityTheory.KB.TwSMInt2
end
end
