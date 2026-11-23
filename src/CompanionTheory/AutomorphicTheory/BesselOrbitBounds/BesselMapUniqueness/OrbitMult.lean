module

public import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGap
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StDefs
public import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.ContinuousOnOrbit
public import CompanionTheory.AutomorphicTheory.RankOneEstimates.DecSender
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.AdmissibleOfIwasawa
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesUnitarySmoothBasicStatement
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.MaximalCompactIsCompact
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.MeasureTheory.Function.L2Space
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
import Mathlib.Tactic.Linter.HaveILetI
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
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.FrameBlockWMem
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.InHolds
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JBeEquivA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JDiagExists
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JSchurG
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StDiagExists
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.MeasurableBetGm
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JBeConv
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JBeConvA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JBeEquivB
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JPairs
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.SigIntIntegrable
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.ThmMOfXi
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.UnitaryGroupStructuralFacts
public import Mathlib.MeasureTheory.Integral.IntegrableOn
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.CutFold

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.PhiIntegrable

section

@[expose] public section

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1.BeEquiv ReciprocityTheory.ChartRestriction.DS.Mult1.Fold

namespace MFix

variable {k r : ℕ}

theorem nR_ge (hk : 1 ≤ k) : (2 : ℝ) ≤ nR k r := by
  unfold nR
  have : (2 : ℕ) ≤ 2 * r + k + 1 := by omega
  exact_mod_cast this

theorem a_nonneg (X : SigData k r) (ha : aM k r ≤ X.a) : 0 ≤ X.a := by
  refine le_trans ?_ ha
  unfold aM nR; positivity

theorem gap (hk : 1 ≤ k) (X : SigData k r) (ha : aM k r ≤ X.a) : AS k r + 1 ≤ min X.a X.a - AG k r - 1 := by
  have hn := nR_ge (r := r) hk
  unfold aM at ha
  unfold AS AG
  rw [min_self]
  have h2 : nR k r ^ 2 * 2 ≤ nR k r ^ 3 := by nlinarith [sq_nonneg (nR k r)]
  have h3 : (4 : ℝ) ≤ nR k r ^ 2 := by nlinarith
  nlinarith

theorem orbit_mem (hGL : GNLower) (X : SigData k r) (ha : aM k r ≤ X.a) {x : Mat k r} (hx : x ∈ GV k r) :
    X.σ x X.w ∈ VflA X X.a := by
  refine ⟨|X.Cw| * gN x⁻¹ ^ X.a, fun g hg => ?_⟩
  rw [mc_sig_left X X.w X.w hg hx]
  have h1 := X.dec (g * x) (gv_mul hg hx)
  have h2 := pow_mul_le hGL hg hx (a_nonneg X ha)
  have h3 : 0 ≤ gN (g * x) ^ (-X.a) := Real.rpow_nonneg (bc_gN_nonneg _) _
  calc ‖mc X X.w X.w (g * x)‖ ≤ X.Cw * gN (g * x) ^ (-X.a) := h1
    _ ≤ |X.Cw| * gN (g * x) ^ (-X.a) := mul_le_mul_of_nonneg_right (le_abs_self _) h3
    _ ≤ |X.Cw| * (gN x⁻¹ ^ X.a * gN g ^ (-X.a)) := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    _ = |X.Cw| * gN x⁻¹ ^ X.a * gN g ^ (-X.a) := by ring

variable {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

def phi (X : SigData k r) (d : ℝ) (W' : Mat k r → Wp) (x : Mat k r) (y : Mt k r) : Wp :=
  ((d : ℂ) * star (mc X X.w X.w (x⁻¹ * Matrix.of y))) • W' (Matrix.of y)

theorem closedG_of (h : UnitaryGroupStructuralFacts) : ClosedG := by
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hCG, -⟩, -⟩ := id h
  exact hCG

theorem phi_integrable (h : UnitaryGroupStructuralFacts) (D : RealPlaceData k r Wp Wp) (X : SigData k r) (d : ℝ) (W' : Mat k r → Wp)
    (hWm : AEStronglyMeasurable (fun y : Mt k r => W' (Matrix.of y)) D.μG) {x : Mat k r} (hx : x ∈ GV k r)
    (hI : Integrable (fun y : Mt k r => gN (x⁻¹ * Matrix.of y) ^ (-X.a) * ‖W' (Matrix.of y)‖) D.μG) :
    Integrable (phi X d W' x) D.μG := by
  have cG : IsClosed {y : Mt k r | (Matrix.of y : Mat k r) ∈ GV k r} := (closedG_of h k r).closed
  have c0 : Continuous (fun y : Mt k r => (x⁻¹ * Matrix.of y : Mat k r)) :=
    Continuous.matrix_mul continuous_const continuous_id
  have c1 : ContinuousOn (fun y : Mt k r => X.σ (x⁻¹ * Matrix.of y) X.w) {y | (Matrix.of y : Mat k r) ∈ GV k r} :=
    (X.rep.2.2 X.w).comp c0.continuousOn (fun y hy => gv_mul (gv_inv hx) hy)
  have c2 : ContinuousOn (fun y : Mt k r => (d : ℂ) * star (mc X X.w X.w (x⁻¹ * Matrix.of y)))
      {y | (Matrix.of y : Mat k r) ∈ GV k r} :=
    continuousOn_const.mul (continuousOn_const.inner c1).star
  have hm := c2.aestronglyMeasurable (μ := D.μG) cG.measurableSet
  have hae : ∀ᵐ y ∂D.μG, y ∈ {y : Mt k r | (Matrix.of y : Mat k r) ∈ GV k r} := ae_mem_of_haarOn D.haarG
  rw [Measure.restrict_eq_self_of_ae_mem hae] at hm
  refine (hI.const_mul (|d| * |X.Cw|)).mono' (hm.smul hWm) ?_
  filter_upwards [ae_mem_of_haarOn D.haarG] with y hy
  have h1 := X.dec _ (gv_mul (gv_inv hx) hy)
  have h3 : 0 ≤ gN (x⁻¹ * Matrix.of y) ^ (-X.a) := Real.rpow_nonneg (bc_gN_nonneg _) _
  have h4 : ‖mc X X.w X.w (x⁻¹ * Matrix.of y)‖ ≤ |X.Cw| * gN (x⁻¹ * Matrix.of y) ^ (-X.a) :=
    h1.trans (mul_le_mul_of_nonneg_right (le_abs_self _) h3)
  unfold phi
  rw [norm_smul, norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs]
  calc |d| * ‖mc X X.w X.w (x⁻¹ * Matrix.of y)‖ * ‖W' (Matrix.of y)‖
      ≤ |d| * (|X.Cw| * gN (x⁻¹ * Matrix.of y) ^ (-X.a)) * ‖W' (Matrix.of y)‖ := by gcongr
    _ = |d| * |X.Cw| * (gN (x⁻¹ * Matrix.of y) ^ (-X.a) * ‖W' (Matrix.of y)‖) := by ring

theorem phi_Fm (D : RealPlaceData k r Wp Wp) (X : SigData k r) (d : ℝ) (W' : Mat k r → Wp)
    (hW : ∀ h ∈ UWset k r D.z, ∀ m ∈ Nset k r, ∀ x ∈ GV k r, W' (m * h * x) = psiD D m • D.π h (W' x))
    {x : Mat k r} (hx : x ∈ GV k r) {y : Mt k r} (hy : (Matrix.of y : Mat k r) ∈ GV k r) {p : Mt k r × Mt k r}
    (hp : (Matrix.of p.1 : Mat k r) ∈ UWset k r D.z ∧ (Matrix.of p.2 : Mat k r) ∈ Nset k r) :
    phi X d W' x (Fm p y) =
      (d : ℂ) • beInt D X (X.σ x X.w) (X.σ (Matrix.of y) X.w) p (W' (Matrix.of y)) := by
  have e0 : (Matrix.of (Fm p y) : Mat k r) = (Matrix.of p.2 * Matrix.of p.1 : Mat k r)⁻¹ * Matrix.of y := rfl
  unfold phi beInt
  rw [e0]
  obtain ⟨hh, hm⟩ := hp
  generalize (Matrix.of p.1 : Mat k r) = h0 at hh ⊢
  generalize (Matrix.of p.2 : Mat k r) = m at hm ⊢
  generalize (Matrix.of y : Mat k r) = t at hy ⊢
  have hs : m * h0 ∈ GV k r := gv_mul hm.1 hh.1
  have hsx : m * h0 * x ∈ GV k r := gv_mul hs hx
  have e1 : star (mc X X.w X.w (x⁻¹ * ((m * h0)⁻¹ * t))) = mc X (X.σ x X.w) (X.σ t X.w) (m * h0) := by
    rw [mc_sig_left X X.w (X.σ t X.w) hs hx]
    unfold mc
    have e2 : x⁻¹ * ((m * h0)⁻¹ * t) = (m * h0 * x)⁻¹ * t := by
      rw [Matrix.mul_inv_rev (m * h0) x, Matrix.mul_assoc]
    rw [e2, X.rep.1.2 _ (gv_inv hsx) _ hy, ContinuousLinearMap.comp_apply,
      ← inner_sig_move X _ hsx (gv_inv hsx) (gv_mul_inv hsx)]
    exact inner_conj_symm _ _
  have e3 := hW h0 hh m hm ((m * h0)⁻¹ * t) (gv_mul (gv_inv hs) hy)
  rw [← Matrix.mul_assoc, gv_mul_inv hs, Matrix.one_mul] at e3
  have e4 : D.π h0⁻¹ (D.π h0 (W' ((m * h0)⁻¹ * t))) = W' ((m * h0)⁻¹ * t) := by
    have := pi_cancel D (uw_inv hh) (W' ((m * h0)⁻¹ * t))
    rwa [gv_inv_inv hh.1] at this
  have e5 := psiD_star_mul D m
  rw [e1, _root_.smul_apply, e3, ContinuousLinearMap.map_smul, e4, smul_smul, smul_smul]
  congr 1
  linear_combination (-((d : ℂ) * mc X (X.σ x X.w) (X.σ t X.w) (m * h0))) * e5

end MFix

open MFix in
theorem stMFix (h : UnitaryGroupStructuralFacts) : StMFix := by
  intro k r Wp _ _ _ D X hD hsq ha l hl d hd W' hWm hWeq hWint
  have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  have hGL := gnLower_of h
  obtain ⟨b, -, -, hfold⟩ := foldS h D hD
  refine ⟨∫ y : Mt k r, (b y : ℂ) * ((d : ℂ) * ⟪l (X.σ (Matrix.of y) X.w), W' (Matrix.of y)⟫_ℂ) ∂D.μG, fun x hx => ?_⟩
  have hφ := phi_integrable h D X d W' hWm hx (hWint x hx)
  have e1 : ∫ y : Mt k r, ((d : ℂ) * star (mc X X.w X.w (Matrix.of y))) • W' (x * Matrix.of y) ∂D.μG =
      ∫ y, phi X d W' x y ∂D.μG := by
    have hm : AEStronglyMeasurable (phi X d W' x) (D.μG.map (lmulM x)) := by
      rw [D.haarG.left x hx]; exact hφ.aestronglyMeasurable
    have e := integral_map (μ := D.μG) (φ := lmulM x) (measurable_lmul_mt x).aemeasurable hm
    rw [D.haarG.left x hx] at e
    rw [e]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    have e0 : (Matrix.of (lmulM x y) : Mat k r) = x * Matrix.of y := rfl
    simp only [phi, e0]
    rw [← Matrix.mul_assoc, gv_inv_mul hx, Matrix.one_mul]
  rw [e1, (hfold _ hφ).2, ← integral_smul_const]
  refine integral_congr_ae ?_
  filter_upwards [ae_mem_of_haarOn D.haarG] with y hy
  have hu := orbit_mem hGL X ha hx
  have hv := orbit_mem hGL X ha hy
  have hI := stBeConv h k r Wp D X hD hsq _ (gap D.k_pos X ha) _ _
    (stPairs h k r Wp D X hD hsq d hd X.a X.a _ hu _ hv)
  have e2 : ∫ p, phi X d W' x (Fm p y) ∂(D.μW.prod D.μN) =
      (d : ℂ) • beOp D X (X.σ x X.w) (X.σ (Matrix.of y) X.w) (W' (Matrix.of y)) := by
    unfold beOp
    rw [ContinuousLinearMap.integral_apply hI, ← integral_smul]
    refine integral_congr_ae ?_
    filter_upwards [ae_mem_S D] with p hp
    exact phi_Fm D X d W' hWeq hx hy hp
  rw [e2, hl.2 _ hu _ hv]
  simp only [rk1, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_smul]
  rw [← Complex.coe_smul, smul_smul]

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.WeightedL1OfL2

section

@[expose] public section

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.SquareIntegrabilityOnOrbit

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1.BeEquiv ReciprocityTheory.ChartRestriction.DS.Mult1.Fold

variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

theorem gnInt_of (h : UnitaryGroupStructuralFacts) : GNIntSharp := by
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hGI, -⟩, -⟩ := id h
  exact hGI

theorem closed_GV (h : UnitaryGroupStructuralFacts) : IsClosed {y : Mt k r | (Matrix.of y : Mat k r) ∈ GV k r} := by
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hCG, -⟩, -⟩ := id h
  exact (hCG k r).closed

theorem aesm_of_contOn (h : UnitaryGroupStructuralFacts) (D : RealPlaceData k r Wp Wp) {F : Type} [NormedAddCommGroup F]
    [SecondCountableTopologyEither (Mt k r) F] {f : Mat k r → F} (hf : ContinuousOn f (GV k r)) :
    AEStronglyMeasurable (fun y : Mt k r => f (Matrix.of y)) D.μG := by
  have hf' : ContinuousOn (fun y : Mt k r => f (Matrix.of y)) {y : Mt k r | (Matrix.of y : Mat k r) ∈ GV k r} := hf
  have hm := hf'.aestronglyMeasurable (μ := D.μG) (closed_GV h).measurableSet
  have hae : ∀ᵐ y ∂D.μG, y ∈ {y : Mt k r | (Matrix.of y : Mat k r) ∈ GV k r} := ae_mem_of_haarOn D.haarG
  rwa [Measure.restrict_eq_self_of_ae_mem hae] at hm

end ReciprocityTheory.ChartRestriction.DS.Mult1.SquareIntegrabilityOnOrbit
end
end
end

-- Source module: CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.OrbitMult

section

@[expose] public section

open Matrix MeasureTheory Formalism.FourierDecayAlt Formalism.QuantumDeterminants ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Mult1 CompanionTheory.D.Upq.Sm
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace CompanionTheory.Bmu

theorem orbit_mult (hCL : CutLim) (hAd : DsAd) (hF : Factor) {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (D : B.RealPlaceData k r Wp Wp) (X : SigData k r) (hD : IsDiag D)
    (hS : SqIntG D X) (ha : aM k r ≤ X.a) (hU : URep (Hpk k r) X.σ) (hw : IsSm (UH (Hpk k r)) X.σ X.w)
    (hdec : ∀ v, IsSm (UH (Hpk k r)) X.σ v → ∃ C : ℝ, ∀ x ∈ B.GV k r, ‖⟪v, X.σ x X.w⟫_ℂ‖ ≤ C * B.gN x ^ (-X.a))
    {l : X.Hs → Wp} (hl : IsMultOneMap D X l) {Bm : X.Hs → Wp} (hB : CWLin (Hpk k r) X.σ Bm)
    (heq : ∀ h ∈ UWset k r D.z, ∀ m ∈ Nset k r, ∀ v, IsSm (UH (Hpk k r)) X.σ v →
      Bm (X.σ (h * m) v) = psi k r D.z cStd m • D.π h (Bm v))
    (hbd : ∃ K : ℝ, ∀ g ∈ UH (Hpk k r), ‖Bm (X.σ g X.w)‖ ≤ K) :
    ∃ c : ℂ, ∀ x ∈ UH (Hpk k r), Bm (X.σ x X.w) = c • l (X.σ x X.w) := by
  obtain ⟨d, hd⟩ := stSchurG k r Wp D X hD hS
  obtain ⟨K, hK⟩ := hbd
  have hae := BeEquiv.ae_mem_of_haarOn D.haarG
  have hAB : B.AB k r ≤ X.a := by
    refine (le_trans ?_ ha)
    have h1 : (1 : ℝ) ≤ r + 1 := by have := Nat.cast_nonneg (α := ℝ) r; linarith
    have h2 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have h3 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    have hn : (1 : ℝ) ≤ nR k r := by
      delta nR
      exact_mod_cast (by omega : 1 ≤ 2 * r + k + 1)
    have h4 : B.AB k r ≤ nR k r ^ 2 + 1 := by
      delta B.AB nR
      push_cast
      nlinarith [sq_nonneg ((k : ℝ) + r - (r + 1))]
    have h5 : nR k r ^ 2 ≤ nR k r ^ 3 := pow_le_pow_right₀ hn (by norm_num)
    have h6 := one_le_pow₀ (n := 3) hn
    delta aM
    linarith
  have hGN := TopH.gN_integrable D (SquareIntegrabilityOnOrbit.gnInt_of multiplicity_one_hypotheses_hold) hAB
  have hcont := hB.continuousOn_orbit hF hU hw
  have hWm := SquareIntegrabilityOnOrbit.aesm_of_contOn multiplicity_one_hypotheses_hold D (f := fun g => Bm (X.σ g X.w)) hcont
  obtain ⟨c, hc⟩ := stMFix multiplicity_one_hypotheses_hold k r Wp D X hD hS ha l hl d hd (fun g => Bm (X.σ g X.w)) hWm
    (fun h hh m hm x hx => by
      have hi := WeylGroupFacts.uw_inv hh
      obtain ⟨hn, he⟩ := unitary_weyl_normal_holds k r D.z D.z_mem h⁻¹ hi m hm
      have hu := WeylGroupFacts.isUnit_of_uh hh.1
      rw [Matrix.nonsing_inv_nonsing_inv _ hu] at hn he
      have e : m * h * x = h * (h⁻¹ * m * h) * x := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]
      show Bm (X.σ (m * h * x) X.w) = psi k r D.z cStd m • D.π h (Bm (X.σ x X.w))
      rw [e, hU.rep.apply_mul (hU.rep.mul_mem _ hh.1 _ hn.1) hx, heq h hh _ hn _ (hw.apply hU.rep hx)]
      delta psi
      rw [he])
    (fun x hx => by
      have hxi : x⁻¹ ∈ B.GV k r := (hU.grp.2.2.2 x hx).1
      have hmp : MeasurePreserving (lmulM x⁻¹) D.μG D.μG :=
        ⟨BeEquiv.measurable_lmul_mt x⁻¹, D.haarG.left x⁻¹ hxi⟩
      have h1 : Integrable (fun y : Mt k r => B.gN (x⁻¹ * Matrix.of y) ^ (-X.a)) D.μG :=
        hmp.integrable_comp_of_integrable hGN
      refine (h1.mul_const K).mono' (h1.aestronglyMeasurable.mul hWm.norm) ?_
      filter_upwards [hae] with y hy
      have h0 : 0 ≤ B.gN (x⁻¹ * Matrix.of y) ^ (-X.a) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
      rw [Real.norm_of_nonneg (mul_nonneg h0 (norm_nonneg _))]
      exact mul_le_mul_of_nonneg_left (hK _ hy) h0)
  have hμ : PI.IsHaarOnM (UH (Hpk k r)) D.μG :=
    ⟨BeEquiv.sigmaFinite_of_haarOn D.haarG, D.haarG.ne_zero, D.haarG.conc, D.haarG.left⟩
  have hσc : ContinuousOn (fun g => X.σ g X.w) (B.GV k r) := X.rep.2.2 X.w
  have hint : ∀ v, IsSm (UH (Hpk k r)) X.σ v →
      Integrable (fun y : Mt k r => ⟪v, X.σ (Matrix.of y) X.w⟫_ℂ) D.μG := by
    intro v hv
    obtain ⟨C, hC⟩ := hdec v hv
    refine (hGN.const_mul C).mono' (SquareIntegrabilityOnOrbit.aesm_of_contOn multiplicity_one_hypotheses_hold D (f := fun g => ⟪v, X.σ g X.w⟫_ℂ)
      ((innerSL ℂ v).continuous.comp_continuousOn hσc)) ?_
    filter_upwards [hae] with y hy
    exact hC _ hy
  have hd0 : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hd.1.ne'
  have hrep : ∀ v, IsSm (UH (Hpk k r)) X.σ v →
      ∫ y : Mt k r, conj ⟪v, X.σ (Matrix.of y) X.w⟫_ℂ • X.σ (Matrix.of y) X.w ∂D.μG = (d : ℂ)⁻¹ • v := by
    intro v hv
    have hi : Integrable (fun y : Mt k r => conj ⟪v, X.σ (Matrix.of y) X.w⟫_ℂ • X.σ (Matrix.of y) X.w) D.μG := by
      refine (hint v hv).norm.mono' (SquareIntegrabilityOnOrbit.aesm_of_contOn multiplicity_one_hypotheses_hold D
        (f := fun g => conj ⟪v, X.σ g X.w⟫_ℂ • X.σ g X.w)
        ((Complex.continuous_conj.comp_continuousOn ((innerSL ℂ v).continuous.comp_continuousOn hσc)).smul hσc)) ?_
      filter_upwards [hae] with y hy
      rw [norm_smul, hU.iso _ hy, X.w_norm, mul_one, Complex.norm_conj]
    refine ext_inner_left ℂ fun ξ => ?_
    rw [← integral_inner hi, inner_smul_right]
    have h := (hd.2 X.w ξ X.w v).2
    rw [inner_self_eq_norm_sq_to_K, X.w_norm] at h
    simp only [inner_smul_right]
    refine Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)) (h.trans ?_)
    · delta mc
      simp only [Complex.star_def]
      ring
    · simp [div_eq_inv_mul]
  refine ⟨c, fun x hx => ?_⟩
  have hBx := hB.comp_sigma hAd hU hx
  have hlim := hCL _ _ X.Hs X.σ hU Wp _ hBx D.μG hμ X.w hw hint _ hrep
    ⟨K, fun g hg => by rw [← hU.rep.apply_mul hx hg]; exact hK _ (hU.rep.mul_mem _ hx _ hg)⟩ X.w hw
  rw [← hc x hx]
  have e1 : Bm (X.σ x X.w) = (d : ℂ) • ((d : ℂ)⁻¹ • Bm (X.σ x X.w)) := by
    rw [smul_smul, mul_inv_cancel₀ hd0, one_smul]
  rw [e1, hlim, ← integral_smul]
  refine integral_congr_ae ?_
  filter_upwards [hae] with y hy
  rw [hU.rep.apply_mul hx hy, smul_smul]
  rfl

theorem cwLin_of {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Mat (2 * r + k + 1) → (H →L[ℂ] H)} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    {z : Fin (2 * r + k + 1) → ℂ} {ψ : Mat (2 * r + k + 1) → ℂ} {π : Mat (2 * r + k + 1) → (Wp →L[ℂ] Wp)}
    {Bm : H → Wp} (h : PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z ψ σ π Bm) : CWLin (Hpk k r) σ Bm := by
  obtain ⟨h1, h2, -, C, Ws, hW, hb⟩ := h
  refine ⟨fun x hx y hy => h1 x hx y hy, fun a x hx => h2 a x hx, C, Ws, hW, fun v hv => ?_⟩
  have := hb v hv
  simpa only [dsigW_eq'] using this

theorem uniq_of (hBd : Bounded) (hCL : CutLim) (hTC : TorConj) (hAd : DsAd) (hF : Factor) : BesselMapUniqGap := by
  intro k r ε lam h H _ _ σ z c u Wp _ _ π hk hg hh hl hσ hz hT hc hπ B₁ B₂ hB₁ hB₂
  haveI : CompleteSpace H := by obtain ⟨P, -, h1, -⟩ := hσ; exact h1
  haveI : FiniteDimensional ℂ Wp := by obtain ⟨g, -, -, h1, -⟩ := hπ; exact h1
  obtain ⟨hrep, hiso, hcont, hirr⟩ := TopTA.pi_facts (u := u) (π := π) hz hT hπ
  obtain ⟨D, hDz, hDπ, hD⟩ := stDiagExists multiplicity_one_hypotheses_hold k r Wp z π hk hz hT hrep hiso hcont hirr
  subst hDz hDπ
  obtain ⟨hUR, hsq⟩ := TopTA.sqInt_of_DSHpk (σ := σ) hσ D.haarG
  have hG : PI.IsMatGroup (UH (Hpk k r)) := PI.QuotSetU.UnitaryGroupMassFormula.unitary_hermitian_group k r
  have hU : URep (Hpk k r) σ :=
    ⟨(hermitian_pos_facts_hold k r).2.1, hG, ⟨hG.2.1, hG.2.2.1, hUR.1.1, hUR.1.2⟩, hUR.2.1⟩
  have hm : thrStar ε + ((4 * (2 * r + k + 1) ^ 3 : ℕ) : ℝ) < h := by
    have := CompanionTheory.FamilyDerivativeExpansion.DecS.thr_le (n := 2 * r + k + 1) (by omega) ε
    have h1 : (0 : ℝ) < ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 := by positivity
    rw [Nat.cast_mul, Nat.cast_pow]
    push_cast at *
    linarith
  have dec : ∀ w ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, ∀ v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ,
      ∃ C : ℝ, ∀ x ∈ B.GV k r, ‖⟪v, σ x w⟫_ℂ‖ ≤ C * B.gN x ^ (-aM k r) := by
    intro w hw v hv
    obtain ⟨C, Ws, -, h2⟩ := CompanionTheory.FamilyDerivativeExpansion.DecS.decayM hl hσ hg _ hm v hv
    exact ⟨_, fun x hx => h2 (aM k r) (by delta aM nR; push_cast; rfl) w hw x hx⟩
  obtain ⟨-, -, -, -, hsm, -, hKT, ⟨w0, hw0, hw0K, -⟩, -⟩ :=
    GlobalTheory.T.discreteSeries_unitary_smooth_basic CompanionTheory.D.gk.admitted.k_finite_smooth k r ε lam ⟨H, σ⟩ ⟨hl, hσ⟩
  have hw0s := hsm w0 (hKT w0 hw0K)
  obtain ⟨C0, hC0⟩ := dec w0 hw0s w0 hw0s
  let X : SigData k r := ⟨H, σ, hUR, TopTA.irr_of_DSHpk (σ := σ) hσ, w0, hw0, aM k r, C0, hC0⟩
  have hS : SqIntG D X := hsq
  obtain ⟨l, hl1⟩ := thmM k r Wp D X hD hS le_rfl
  obtain ⟨τ, hτ, hτW, hτN⟩ := hTC k r D.z c hz hc
  have hw : IsSm (UH (Hpk k r)) σ w0 := hw0s
  have hτi : τ⁻¹ * τ = 1 := mul_eq_one_comm.1 (hG.2.2.2 τ hτ).2
  have key : ∀ Bm : H → Wp,
      PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) D.z (PI.BesselMapUniq.psiGen k r D.z c) σ D.π Bm →
      ∃ c₀ : ℂ, ∀ x ∈ UH (Hpk k r), Bm (σ τ (σ x w0)) = c₀ • l (σ x w0) := by
    intro Bm hBm
    have hCW := cwLin_of hBm
    obtain ⟨K, hK⟩ := hBd k r H σ hU hk D.z c hz hT hc Wp D.π hrep.1 hiso hcont Bm hCW
      (fun h hh m hm v hv => hBm.2.2.1 h hh m hm v hv) w0 hw
    refine orbit_mult hCL hAd hF D X hD hS le_rfl hU hw (fun v hv => dec w0 hw0s v hv) hl1
      (Bm := fun v => Bm (σ τ v)) (hCW.comp_sigma hAd hU hτ) (fun h hh m hm v hv => ?_) ⟨K, fun g hg => ?_⟩
    · obtain ⟨hn, hψ⟩ := hτN m hm
      have e : τ * (h * m) = h * (τ * m * τ⁻¹) * τ := by
        rw [← Matrix.mul_assoc, hτW h hh]
        simp only [Matrix.mul_assoc, hτi, Matrix.mul_one]
      show Bm (σ τ (σ (h * m) v)) = psi k r D.z cStd m • D.π h (Bm (σ τ v))
      rw [← hU.rep.apply_mul hτ (hU.rep.mul_mem _ hh.1 _ hm.1), e,
        hU.rep.apply_mul (hU.rep.mul_mem _ hh.1 _ hn.1) hτ, hBm.2.2.1 h hh _ hn _ (hv.apply hU.rep hτ), hψ]
    · show ‖Bm (σ τ (σ g w0))‖ ≤ K
      rw [← hU.rep.apply_mul hτ hg]
      exact hK _ (hU.rep.mul_mem _ hτ _ hg)
  obtain ⟨c₁, e₁⟩ := key B₁ hB₁
  obtain ⟨c₂, e₂⟩ := key B₂ hB₂
  have fin : ∀ a b : ℂ, a * c₁ + b * c₂ = 0 →
      ∀ v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, a • B₁ v + b • B₂ v = 0 := by
    intro a b hab v hv
    have hE := (((cwLin_of hB₁).comb (cwLin_of hB₂) a b).comp_sigma hAd hU hτ)
    have hτ' := (hG.2.2.2 τ hτ).1
    have hv' : IsSm (UH (Hpk k r)) σ (σ τ⁻¹ v) := IsSm.apply hU.rep hv hτ'
    have h0 := hE.eq_zero hU hw (fun g hg => by
        show a • B₁ (σ τ (σ g w0)) + b • B₂ (σ τ (σ g w0)) = 0
        rw [e₁ g hg, e₂ g hg, smul_smul, smul_smul, ← add_smul, hab, zero_smul]) hv'
      (fun Ws hWs δ hδ => by
        have := cyc_of_smooth k r ε lam H σ w0 hσ (by intro e; rw [e, norm_zero] at hw0; exact zero_ne_one hw0)
          hw0s _ hv' Ws hWs δ hδ
        simp only [dsigW_eq'] at this
        exact this)
    have e : σ τ (σ τ⁻¹ v) = v := by
      rw [← hU.rep.apply_mul hτ hτ', (hG.2.2.2 τ hτ).2, hU.rep.map_one]; rfl
    simpa only [e] using h0
  by_cases h1 : c₁ = 0
  · exact ⟨1, 0, Or.inl one_ne_zero, fin 1 0 (by rw [h1]; simp)⟩
  · exact ⟨c₂, -c₁, Or.inr (neg_ne_zero.2 h1), fin c₂ (-c₁) (by ring)⟩

end CompanionTheory.Bmu
end
end
end
