module

public import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffIter
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousFamF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfConstOfTendsto
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.RingTheory.PicardGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactPseudoUnitaryOffDiagNormSublevel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffDiagBlockNormContInv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PseudoUnitaryOffDiagNormSqZeroIffMemMaxCompact
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.Divisors.TCoefMInMMul
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactPseudoCoefficientDataStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MuPowLambdaProductCoeffMuVariablePencilEmbedding
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbIntAdSpanEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PseudoCoeffShapeSmoothCompactSupport
public import Development.AbelianVarietyTheory.Definitions.Foundations.MeasurePreservingRmulQuotMeas
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndefiniteUnitaryGroupHaarIsMulRightInvariant
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StTrAd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumInnerIntegralEq

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactCentOfMemKG

section

@[expose] public section

open MeasureTheory Matrix GlobalTheory.Orb
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)
open scoped ContDiff

namespace GlobalTheory

theorem cent_subset_KG_of_regSS {n : ℕ} {ε : Fin n → Bool} {k : UJ ε} (hk : k ∈ KG ε)
    (hr : IsRegSS (ujMat ε k)) : (cent k : Set (UJ ε)) ⊆ (KG ε : Set (UJ ε)) := by
  intro g hg
  have hg' : g * k = k * g := mem_cent.1 hg
  have h1 : ujMat ε g * ujMat ε k = ujMat ε k * ujMat ε g := by
    rw [← map_mul, ← map_mul, hg']
  have h2 : Jm ε * ujMat ε k = ujMat ε k * Jm ε := hk.2.symm
  have hJ : ujMat ε g * Jm ε = Jm ε * ujMat ε g := hr.commute h1 h2
  have hU : (ujMat ε g)ᴴ * Jm ε * ujMat ε g = Jm ε := g.2
  have hJJ := Formalism.REAL.Jm_mul_self ε
  refine ⟨?_, hJ⟩
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  change (ujMat ε g)ᴴ * ujMat ε g = 1
  calc (ujMat ε g)ᴴ * ujMat ε g = (ujMat ε g)ᴴ * (Jm ε * Jm ε) * ujMat ε g := by rw [hJJ, Matrix.mul_one]
    _ = ((ujMat ε g)ᴴ * Jm ε * ujMat ε g) * Jm ε := by
        rw [Matrix.mul_assoc (ujMat ε g)ᴴ (Jm ε * Jm ε), Matrix.mul_assoc (Jm ε), ← hJ]
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hU, hJJ]

theorem isCompact_cent_of_mem_KG : ∀ (n : ℕ) (ε : Fin n → Bool) (k : UJ ε), k ∈ KG ε → IsRegSS (ujMat ε k) →
    IsCompact (cent k : Set (UJ ε)) := by
  intro n ε k hk hr
  have hK : IsCompact (KG ε : Set (UJ ε)) := by
    simpa [Subtype.range_coe] using (isCompact_univ (X := KG ε)).image continuous_subtype_val
  exact hK.of_isClosed_subset (isClosed_cent k) (cent_subset_KG_of_regSS hk hr)

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactCentOfConj

section

@[expose] public section

open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A
open GlobalTheory.Orb
open Formalism.REAL (UJ KG toM)

namespace GlobalTheory.PsCo.NonEll

theorem isRegSS_conj {n : ℕ} {ε : Fin n → Bool} (s x : UJ ε) (hs : IsRegSS (ujMat ε s)) :
    IsRegSS (ujMat ε (x⁻¹ * s * x)) := by
  unfold IsRegSS at hs ⊢
  rw [map_mul, Matrix.charpoly_mul_comm, ← map_mul, ← mul_assoc, mul_inv_cancel,
    one_mul]
  exact hs

theorem isCompact_cent_of_conj {G : Type} [Group G] [TopologicalSpace G] [ContinuousMul G]
    (s x : G) (h : IsCompact (cent (x⁻¹ * s * x) : Set G)) : IsCompact (cent s : Set G) := by
  have hc : Continuous fun y : G => x * y * x⁻¹ := by fun_prop
  have := h.image hc
  convert this using 1
  ext y
  simp only [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff, Set.mem_image]
  constructor
  · intro hy
    refine ⟨x⁻¹ * y * x, ?_, by group⟩
    calc x⁻¹ * y * x * (x⁻¹ * s * x) = x⁻¹ * (y * s) * x := by group
      _ = x⁻¹ * (s * y) * x := by rw [hy]
      _ = x⁻¹ * s * x * (x⁻¹ * y * x) := by group
  · rintro ⟨z, hz, rfl⟩
    calc x * z * x⁻¹ * s = x * (z * (x⁻¹ * s * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * s * x) * z) * x⁻¹ := by rw [hz]
      _ = s * (x * z * x⁻¹) := by group

theorem stNonEll : GlobalTheory.PsCo.Pc1.StNonEll := by
  intro n ε s hs hnc
  set r : UJ ε → ℝ := fun g => rM ε (toM g) with hr
  have hcont : Continuous r := (GlobalTheory.offDiagBlockNorm_cont_inv n ε).1
  have hsub : IsCompact {g : UJ ε | r g ≤ r s} := GlobalTheory.isCompact_offDiag_sublevel n ε (r s)
  have hcl : IsClosed (Set.range fun x : UJ ε => x⁻¹ * s * x) := isClosed_class_realUJ hs
  have hK := hsub.inter_right hcl
  have hne : ({g : UJ ε | r g ≤ r s} ∩ Set.range fun x : UJ ε => x⁻¹ * s * x).Nonempty :=
    ⟨s, le_refl (r s), 1, by simp⟩
  obtain ⟨g, ⟨hg1, x₀, rfl⟩, hmin⟩ := hK.exists_isMinOn hne hcont.continuousOn
  refine ⟨r (x₀⁻¹ * s * x₀), ?_, fun x => ?_⟩
  · have h0 : 0 ≤ r (x₀⁻¹ * s * x₀) := Finset.sum_nonneg fun z _ => by positivity
    refine lt_of_le_of_ne h0 fun h => hnc ?_
    have hk : x₀⁻¹ * s * x₀ ∈ KG ε := (GlobalTheory.offDiag_zero_iff_mem_K n ε _).1 h.symm
    exact isCompact_cent_of_conj s x₀ (GlobalTheory.isCompact_cent_of_mem_KG n ε _ hk (isRegSS_conj s x₀ hs))
  · change r (x₀⁻¹ * s * x₀) ≤ r (x⁻¹ * s * x)
    by_cases hx : r (x⁻¹ * s * x) ≤ r s
    · exact hmin ⟨hx, x, rfl⟩
    · exact le_trans hg1 (not_le.1 hx).le

end GlobalTheory.PsCo.NonEll
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCutFnIteratedDerivScale

section

@[expose] public section

noncomputable section

open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A
open scoped ContDiff Topology

namespace GlobalTheory.PsCo.Pc1

theorem iteratedDeriv_scale_eq_zero {G : ℝ → ℝ} (hG : ∀ x, 1 ≤ x → G x = 0) {t : ℝ} (ht : 0 < t) (k : ℕ)
    {x : ℝ} (hx : 1 < t * x) : iteratedDeriv k (fun y => G (t * y)) x = 0 := by
  have hev : (fun y => G (t * y)) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    have hopen : IsOpen {y : ℝ | 1 < t * y} := isOpen_lt continuous_const (continuous_const.mul continuous_id)
    filter_upwards [hopen.mem_nhds hx] with y hy
    exact hG _ (le_of_lt hy)
  rw [hev.iteratedDeriv_eq k]
  simp [iteratedDeriv_const]

theorem isCutFn_iteratedDeriv_scale {G : ℝ → ℝ} (hGs : ContDiff ℝ ∞ G) (hG : ∀ x, 1 ≤ x → G x = 0) {t : ℝ}
    (ht : 0 < t) (k : ℕ) : IsCutFn (iteratedDeriv k (fun y => G (t * y))) := by
  refine ⟨?_, 2 / t, fun x hx => iteratedDeriv_scale_eq_zero hG ht k ?_⟩
  · rw [iteratedDeriv_eq_iterate]
    exact ContDiff.iterate_deriv k (hGs.comp (contDiff_const.mul contDiff_id))
  · have : 2 ≤ t * x := by rwa [div_le_iff₀ ht, mul_comm] at hx
    linarith

theorem stFam : StFam := by
  intro n ε G p hG
  refine ⟨(Finset.range (nMode ε + 1)).sup fun k => (p k).totalDegree, fun k hk =>
    Finset.le_sup (f := fun k => (p k).totalDegree) (Finset.mem_range.2 (Nat.lt_succ_of_le hk)), fun t ht => ⟨?_, ?_⟩⟩
  · have : famF ε G p t = ∑ k ∈ Finset.range (nMode ε + 1), bas ε (iteratedDeriv k fun x => G (t * x)) (p k) := by
      funext g; simp [famF, Finset.sum_apply]
    rw [this]
    refine Submodule.sum_mem _ fun k hk => Submodule.subset_span ⟨_, p k, isCutFn_iteratedDeriv_scale hG.1 hG.2.1 ht k,
      Finset.le_sup (f := fun k => (p k).totalDegree) hk, rfl⟩
  · intro g hg
    simp only [famF, bas]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [iteratedDeriv_scale_eq_zero hG.2.1 ht k hg]
    simp

end GlobalTheory.PsCo.Pc1
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasOrbIntOfIsCompactCentConj

section

@[expose] public section

open MeasureTheory Matrix GlobalTheory.Orb
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)
open scoped ContDiff

namespace GlobalTheory

theorem hasOrbInt_of_isCompact_cent_conj : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] [LocallyCompactSpace H] [T2Space H] (μ : Measure H) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (s : H), IsCompact (cent s : Set H) → ∀ (dt : Measure (cent s)) [dt.IsHaarMeasure] [dt.IsMulRightInvariant], IsProperOrbit (cent s) s → ∀ (y : H) (f : H → ℂ), Continuous f → HasCompactSupport f → HasOrbInt μ s dt f ((∫ x, f (x⁻¹ * (y⁻¹ * s * y) * x) ∂μ) / dt.real Set.univ) := by
  intro H _ _ _ _ _ _ _ _ μ _ _ s hT dt _ _ hP y f hf hc
  haveI : CompactSpace (cent s) := isCompact_iff_compactSpace.1 hT
  obtain ⟨C, hC, h0⟩ := hP _ hc
  have hcont : Continuous (conjFn s f) := hf.comp (by fun_prop)
  have hsupp : HasCompactSupport (conjFn s f) := by
    refine HasCompactSupport.intro' (hT.mul hC) (hT.mul hC).isClosed fun x hx => ?_
    by_contra hne
    obtain ⟨t, ht, htx⟩ := h0 x (subset_tsupport f hne)
    exact hx ⟨t⁻¹, (cent s).inv_mem ht, t * x, htx, by group⟩
  have hint : Integrable (conjFn s f) μ := hcont.integrable_of_hasCompactSupport hsupp
  have e : (∫ x, f (x⁻¹ * (y⁻¹ * s * y) * x) ∂μ) = ∫ x, f (x⁻¹ * s * x) ∂μ := by
    have := integral_mul_left_eq_self (μ := μ) (fun z => f (z⁻¹ * s * z)) y
    rw [← this]
    congr 1; ext x; congr 1; group
  rw [e]
  exact hasOrbInt_of_finite hint

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.StOrbCpt

section

@[expose] public section

open MeasureTheory GlobalTheory.Orb

namespace GlobalTheory.PsCo.Pc1

theorem stOrbCpt : GlobalTheory.PsCo.Pc1.StOrbCpt := by
  intro n ε μ _ s hs hT dt _ _ y f hf hc
  haveI : μ.IsMulRightInvariant := GlobalTheory.haar_UJ_isMulRightInvariant n ε μ
  exact GlobalTheory.hasOrbInt_of_isCompact_cent_conj _ μ s hT dt (isProperOrbit_realUJ hs) y f hf hc

end GlobalTheory.PsCo.Pc1
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.StProfileHolds

section

@[expose] public section

noncomputable section

open MvPolynomial
open scoped ContDiff

namespace GlobalTheory.PsCo.Pc1

theorem stProfile_holds : StProfile := by
  intro N
  induction N with
  | zero =>
    refine ⟨fun x => expNegInvGlue (1 - x), ?_, ?_, ?_, ?_⟩
    · exact expNegInvGlue.contDiff.comp (contDiff_const.sub contDiff_id)
    · intro x hx
      exact expNegInvGlue.zero_of_nonpos (by linarith)
    · intro x
      simpa using expNegInvGlue.nonneg _
    · simpa using expNegInvGlue.pos_of_pos (x := 1) one_pos
  | succ N ih =>
    obtain ⟨G, h1, h2, h3, h4⟩ := ih
    have hc : Continuous G := h1.continuous
    have hd : deriv (fun x => ∫ s in (1:ℝ)..x, G s) = G := by
      funext x
      exact (hc.deriv_integral G 1 x)
    refine ⟨fun x => ∫ s in (1:ℝ)..x, G s, ?_, ?_, ?_, ?_⟩
    · rw [contDiff_infty_iff_deriv, hd]
      exact ⟨fun x => (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
        (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt).differentiableAt, h1⟩
    · intro x hx
      have : ∫ s in (1:ℝ)..x, G s = ∫ s in (1:ℝ)..x, (0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [Set.uIcc_of_le hx] at hs
        exact h2 s hs.1
      simpa using this
    · intro x
      rw [iteratedDeriv_succ', hd]
      exact h3 x
    · rw [iteratedDeriv_succ', hd]
      exact h4

end GlobalTheory.PsCo.Pc1
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalPseudoCoefficientExistenceUnitaryGroup

section

@[expose] public section

open GlobalTheory.PsCo.Pc1

namespace GlobalTheory.PsCo.Pc

theorem localPC_holds : LocalPC :=
  GlobalTheory.PsCo.Pc1.localPC_of_steps GlobalTheory.PsCo.Pc1.A.stAlg GlobalTheory.PsCo.Pc1.stProfile_holds
    GlobalTheory.PsCo.Pc1.stFam GlobalTheory.PsCo.Pc1.Homot.stHomot GlobalTheory.PsCo.Pcd.stLim
    GlobalTheory.ShapeSmoothFinite.stShape GlobalTheory.PsCo.Pc1.orbInt_adSpan_eq_zero GlobalTheory.PsCo.Pc1.stOrbCpt
    GlobalTheory.PsCo.NonEll.stNonEll GlobalTheory.PsCo.Pc3.stTr GlobalTheory.PsCo.Pc3.stTrAd GlobalTheory.T.maximalCompact_pseudoCoefficientData

end GlobalTheory.PsCo.Pc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalPseudoCoefficientExistenceUnitaryGroupStatement

section

@[expose] public section

open GlobalTheory.PsCo.Pc1

theorem _root_.GlobalTheory.T.localPseudoCoefficientExistence_unitaryGroup : GlobalTheory.PsCo.Pc.LocalPC := by
  first | exact @GlobalTheory.PsCo.Pc.localPC_holds | exact GlobalTheory.PsCo.Pc.localPC_holds | (intros; apply GlobalTheory.PsCo.Pc.localPC_holds <;> assumption)
end
end
