module

public import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.AmpRootCut
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AmpOrbQuot
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AmpRelAtPt
public import Formalism.PeriodIntegrals.AmpRootH
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.ReverseCauchySchwarzHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitQuotientTopology.IsClosedRStab
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RootSubgroupBasics.FlagMatLower
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RootSubgroupJacobian.SUpPowEqZero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RootSubgroupBasics.TriShear
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RootSubgroupHaar.MatEqZeroOfSpan
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RootSubgroupJacobian.ContinuousRootCoords
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RootSubgroupHaar.MatEqZeroOfSpan
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Separation.CompletelyRegular
public import Formalism.PeriodIntegrals.AmpRoot
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RootSubgroupJacobian.ContinuousRootCoords
public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSB
public import Formalism.PeriodIntegrals.AmpOrbQ

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RootSubgroupHaar.ContinuousGS

section

@[expose] public section

open Matrix MeasureTheory

noncomputable section

namespace PI.AmpRootHaarW

open Formalism.QuantumDeterminants Formalism.MainNotions.S PI.AmpRootCommon PI.AmpRootJacW

variable {k r : ℕ}

theorem nset_mul' {a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (ha : a ∈ Nset k r)
    (hb : b ∈ Nset k r) : a * b ∈ Nset k r := by
  apply PI.AmpOrbQuot.nset_mul <;> assumption

theorem rstab_mul' {g a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r))
    (ha : a ∈ RStab k r g) (hb : b ∈ RStab k r g) : a * b ∈ RStab k r g := by
  refine ⟨nset_mul' ha.1 hb.1, ?_⟩
  have e : g⁻¹ * (a * b) * g = (g⁻¹ * a * g) * (g⁻¹ * b * g) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc g g⁻¹, uh_mul_inv hg, Matrix.one_mul]
  rw [e]; exact nset_mul' ha.2 hb.2

theorem Fm_row {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (M : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (c : Fin r) (j : Fin (r + 1)) : (Fm k r z * M) (eI k r c) j = M (Fin.castSucc c) j := by
  rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
  have hl : Fm k r z (eI k r c) (Fin.last r) = 0 := by
    show fvec k r z (Fin.last r) (eI k r c) = 0
    unfold fvec; rw [dif_neg (by simp)]; exact hz _ (Or.inl c.isLt)
  have hc : ∀ d : Fin r, Fm k r z (eI k r c) (Fin.castSucc d) = if d = c then 1 else 0 := fun d => by
    show fvec k r z (Fin.castSucc d) (eI k r c) = _
    rw [fvec_cs, bvec, Pi.single_apply]
    by_cases h : d = c
    · rw [if_pos h, if_pos (by rw [h])]
    · rw [if_neg h, if_neg]
      intro e; apply h; ext; have := congrArg Fin.val e; simp only [eI] at this; omega
  rw [hl, zero_mul, add_zero]
  simp only [hc, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem flagMat_mul {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z)
    {a x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (ha : a ∈ Nset k r) (hx : x ∈ Nset k r) :
    flagMat k r z (a * x) = flagMat k r z a * flagMat k r z x := by
  have hF : Fm k r z * flagMat k r z (a * x) = Fm k r z * (flagMat k r z a * flagMat k r z x) := by
    rw [← mul_Fm hz (nset_mul' ha hx), Matrix.mul_assoc, mul_Fm hz hx, ← Matrix.mul_assoc a, mul_Fm hz ha,
      Matrix.mul_assoc]
  ext i j
  by_cases hi : i.val < r
  · have e1 := Fm_row hz (flagMat k r z (a * x)) ⟨i.val, hi⟩ j
    have e2 := Fm_row hz (flagMat k r z a * flagMat k r z x) ⟨i.val, hi⟩ j
    have hc : Fin.castSucc (⟨i.val, hi⟩ : Fin r) = i := Fin.ext rfl
    rw [hc] at e1 e2
    rw [← e1, ← e2, hF]
  · have hrow : ∀ (b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (c : Fin (r + 1)),
        flagMat k r z b i c = if i = c then 1 else 0 := fun b c => by
      unfold flagMat; rw [dif_neg hi]
    rw [Matrix.mul_apply]
    simp only [hrow, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

def gS (p : Point ℂ (r + 1)) (s' : rootPat p → ℂ) (q : rootPat p) (v : rootPat p → ℂ) : ℂ :=
  s' q + (vM (rootPat p) s' * vM (rootPat p) v) q.1.1 q.1.2

theorem lm_eq (p : Point ℂ (r + 1)) (s' v : rootPat p → ℂ) (q : rootPat p) :
    ((1 + vM (rootPat p) s') * (1 + vM (rootPat p) v)) q.1.1 q.1.2 = v q + gS p s' q v := by
  have hne : q.1.1 ≠ q.1.2 := ne_of_lt (rootPat_lt p q.1 q.2)
  rw [add_mul, one_mul, mul_add, mul_one]
  simp only [Matrix.add_apply, Matrix.one_apply, if_neg hne, vM_at, gS]
  ring

theorem gS_dep (p : Point ℂ (r + 1)) (s' : rootPat p → ℂ) (q : rootPat p) (v w : rootPat p → ℂ)
    (h : ∀ q', rk (rootPat p) q' < rk (rootPat p) q → v q' = w q') : gS p s' q v = gS p s' q w := by
  unfold gS
  congr 1
  simp only [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  unfold vM
  by_cases h1 : (q.1.1, c) ∈ rootPat p
  · by_cases h2 : (c, q.1.2) ∈ rootPat p
    · simp only [dif_pos h1, dif_pos h2]
      rw [h ⟨(c, q.1.2), h2⟩ ?_]
      have a1 : q.1.1.val < c.val := Fin.lt_def.mp (rootPat_lt p _ h1)
      have a2 : c.val < q.1.2.val := Fin.lt_def.mp (rootPat_lt p _ h2)
      show q.1.2.val - c.val < q.1.2.val - q.1.1.val
      omega
    · simp only [dif_neg h2, mul_zero]
  · simp only [dif_neg h1, zero_mul]

theorem continuous_gS (p : Point ℂ (r + 1)) (s' : rootPat p → ℂ) (q : rootPat p) : Continuous (gS p s' q) := by
  unfold gS
  exact continuous_const.add ((continuous_const.matrix_mul (continuous_vM _)).matrix_elem _ _)

theorem lm_mp (p : Point ℂ (r + 1)) (s' : rootPat p → ℂ) :
    MeasurePreserving (fun (v : rootPat p → ℂ) q => v q + gS p s' q v) volume volume :=
  PI.AmpRootCommon.Tri.triShear (rootPat p) (rk (rootPat p)) (gS p s') (fun q => (continuous_gS p s' q).measurable)
    (fun q v w h => gS_dep p s' q v w h)

end PI.AmpRootHaarW
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RootSubgroupHaar.RootHaarMain

section

@[expose] public section

open MeasureTheory Matrix
open scoped ENNReal

noncomputable section

namespace PI.AmpRootHaarW

open Formalism.QuantumDeterminants Formalism.MainNotions.S PI.AmpRootCommon PI.AmpRootJacW

theorem ext_of_injOn {α β : Type*} [TopologicalSpace α] [PolishSpace α] [MeasurableSpace α] [BorelSpace α]
    [TopologicalSpace β] [T2Space β] [MeasurableSpace β] [BorelSpace β] {f : α → β} {S : Set α}
    (hS : MeasurableSet S) (hf : Continuous f) (hinj : Set.InjOn f S) {μ ν : Measure α}
    (hμ : μ Sᶜ = 0) (hν : ν Sᶜ = 0) (h : μ.map f = ν.map f) : μ = ν := by
  ext A hA
  have hAS : MeasurableSet (A ∩ S) := hA.inter hS
  have himg : MeasurableSet (f '' (A ∩ S)) :=
    hAS.image_of_continuousOn_injOn hf.continuousOn (hinj.mono Set.inter_subset_right)
  have hpre : f ⁻¹' (f '' (A ∩ S)) ∩ S = A ∩ S := by
    ext x
    constructor
    · rintro ⟨⟨y, hy, hxy⟩, hx⟩
      rw [← hinj hy.2 hx hxy]
      exact hy
    · intro hx
      exact ⟨⟨x, hx, rfl⟩, hx.2⟩
  have key : ∀ ρ : Measure α, ρ Sᶜ = 0 → ρ A = ρ.map f (f '' (A ∩ S)) := by
    intro ρ hρ
    rw [Measure.map_apply hf.measurable himg, ← measure_inter_conull (s := A) hρ,
      ← measure_inter_conull (s := f ⁻¹' (f '' (A ∩ S))) hρ, hpre]
  rw [key μ hμ, key ν hν, h]

theorem rootHaar_main : PI.AmpRootH.RootHaar := by
  intro k r L p g₀ μ₀ hc hrep hG hnull hmap
  obtain ⟨hg, hP⟩ := hrep
  have hz := L.hz.1
  have hz' := L.hz'.1
  set c : ℝ≥0∞ := ENNReal.ofReal ((‖L.c‖ / (2 * Real.pi)) ^ (rootPat p).card) with hc_def
  set φ : Mt k r → Mt k r := fun x => fun i j => (g₀ * Matrix.of x * g₀⁻¹) i j with hφ
  set S : Set (Mt k r) := {x | Matrix.of x ∈ RStab k r g₀} with hS_def
  set f := rootCoords k r L.z p with hf_def
  have hφm : Measurable φ := measurable_conjM g₀ g₀⁻¹
  have hSm : MeasurableSet S := measurableSet_RStab g₀
  have hfc : Continuous f := continuous_rootCoords L.z p
  have hdet : (gramM k r L.z L.z' g₀).det ≠ 0 := by
    intro h0
    have e := group_gram_holds k r L.z L.z' hz hz' g₀ hg
    rw [h0, mul_zero] at e
    have e' : Gf k r L.z L.z' g₀ = 0 := by exact_mod_cast e
    linarith
  have hinj : Set.InjOn f S := rootCoords_injOn hz hz' hg hP hdet
  have hφS : ∀ x, Matrix.of x ∈ Rset k r g₀ → φ x ∈ S := by
    intro x hx
    refine ⟨hx.2, ?_⟩
    show g₀⁻¹ * (g₀ * Matrix.of x * g₀⁻¹) * g₀ ∈ Nset k r
    rw [conj_back hg]
    exact hx.1
  have hnullS : μ₀.map φ Sᶜ = 0 := by
    rw [Measure.map_apply hφm hSm.compl]
    refine measure_mono_null ?_ hnull
    intro x hx hxR
    exact hx (hφS x hxR)
  have hνf : (μ₀.map φ).map f = c • volume := by
    rw [Measure.map_map hfc.measurable hφm]
    have hR : ∀ᵐ x ∂μ₀, Matrix.of x ∈ Rset k r g₀ := ae_iff.2 hnull
    have hae : f ∘ φ =ᵐ[μ₀] phiR p ∘ rootCoords k r L.z' p := by
      filter_upwards [hR] with x hx
      exact rootCoords_conj hz hz' hg hP hx
    rw [Measure.map_congr hae, ← Measure.map_map (phiR_mp p).measurable
      (continuous_rootCoords L.z' p).measurable, hmap, Measure.map_smul, (phiR_mp p).map_eq]
    exact (phiR_mp p).measurable.aemeasurable
  have hc0 : c ≠ 0 := by
    rw [hc_def, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact pow_pos (div_pos (norm_pos_iff.2 hc) (by positivity)) _
  have hsf : SigmaFinite (μ₀.map φ) := by
    refine SigmaFinite.of_map _ hfc.measurable.aemeasurable ?_
    rw [hνf, ← ENNReal.coe_toNNReal (show c ≠ ⊤ from by rw [hc_def]; exact ENNReal.ofReal_ne_top),
      ← ENNReal.smul_def]
    infer_instance
  have hne : μ₀.map φ ≠ 0 := by
    intro h0
    have e := hνf
    rw [h0, Measure.map_zero] at e
    have e2 := congrArg (fun m : Measure (rootPat p → ℂ) => m Set.univ) e
    simp only [Measure.coe_zero, Pi.zero_apply, Measure.smul_apply, smul_eq_mul] at e2
    rcases mul_eq_zero.1 e2.symm with h | h
    · exact hc0 h
    · exact NeZero.ne (volume : Measure (rootPat p → ℂ)) (Measure.measure_univ_eq_zero.1 h)
  refine ⟨hsf, hne, hnullS, ?_⟩
  intro s hs
  have hlm : Measurable (lmulM s : Mt k r → Mt k r) := by
    convert measurable_conjM (k := k) (r := r) s 1 using 1
    funext x i j
    simp [lmulM]
  have hνS : S ∈ ae (μ₀.map φ) := mem_ae_iff.2 hnullS
  have hone : ∀ (v : rootPat p → ℂ) (q : rootPat p), (1 + vM (rootPat p) v) q.1.1 q.1.2 = v q := by
    intro v q
    rw [Matrix.add_apply, vM_at, Matrix.one_apply_ne (ne_of_lt (rootPat_lt p q.1 q.2)), zero_add]
  set s' := f (fun i j => s i j) with hs'
  refine ext_of_injOn hSm hfc hinj ?_ hnullS ?_
  · rw [Measure.map_apply hlm hSm.compl]
    refine measure_mono_null ?_ hnullS
    intro y hy hyS
    apply hy
    show s * Matrix.of y ∈ RStab k r g₀
    exact rstab_mul' hg hs hyS
  · rw [Measure.map_map hfc.measurable hlm]
    have hae : f ∘ lmulM s =ᵐ[μ₀.map φ] (fun v q => v q + gS p s' q v) ∘ f := by
      filter_upwards [hνS] with y hy
      funext q
      have hsy : s * Matrix.of y ∈ RStab k r g₀ := rstab_mul' hg hs hy
      have e1 := flagZ_eq hz hz' hg hP hsy
      have e2 := flagMat_mul hz hs.1 hy.1
      have e3 := flagZ_eq hz hz' hg hP hs
      have e4 := flagZ_eq hz hz' hg hP (a := Matrix.of y) hy
      have e5 : 1 + vM (rootPat p) (f (fun i j => (s * Matrix.of y) i j)) =
          (1 + vM (rootPat p) s') * (1 + vM (rootPat p) (f y)) := by
        rw [← e1, e2, e3, e4]
        all_goals rfl
      have e6 := congrFun (congrFun e5 q.1.1) q.1.2
      rw [hone, lm_eq] at e6
      exact e6
    rw [Measure.map_congr hae, ← Measure.map_map (lm_mp p s').measurable hfc.measurable, hνf,
      Measure.map_smul, (lm_mp p s').map_eq]
    exact (lm_mp p s').measurable.aemeasurable

end PI.AmpRootHaarW
end
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AmpRootHaar

section

@[expose] public section

theorem amplifier_root_haar : PI.AmpRootH.RootHaar := PI.AmpRootHaarW.rootHaar_main
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AmpRootJac

section

@[expose] public section

theorem amplifier_root_jacobian : PI.AmpRoot.RootJac := PI.AmpRootJacW.rootJac
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.RowsFinalAmpRoot

section

@[expose] public section

namespace Formalism.MainNotions.S.Pv.LemmaJ

theorem relAtPt_holds : RelAtPt := (show PI.AmpRoot.RelAtPt ↔ RelAtPt from Iff.rfl).mp _root_.amplifier_relation_at_point

theorem rootJac_holds : RootJac := (show PI.AmpRoot.RootJac ↔ RootJac from Iff.rfl).mp _root_.amplifier_root_jacobian

theorem rootHaar_holds : RootHaar := (show PI.AmpRootH.RootHaar ↔ RootHaar from Iff.rfl).mp _root_.amplifier_root_haar

theorem exists_orbQuot₂ : OrbQuotEx := (show PI.AmpOrbQ.OrbQuotEx ↔ OrbQuotEx from Iff.rfl).mp (_root_.orbQuotEx_of_haarLieN (show PI.AmpOrbQ.HaarLieN from Formalism.MainNotions.BridgeCSB.haarLieN))

end Formalism.MainNotions.S.Pv.LemmaJ
end
end
