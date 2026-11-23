module

public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DiscreteSeriesUnitarySmoothBasic
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.MatrixCoefficientDecayStatement
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DerivedActionDiscreteSeriesProperties
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselNeZeroOfCyclicOrbit
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CkOnInCCCongrOnGroup
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DilationUnipotentWeylMeasure
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne

-- Source module: CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.MatrixCoefficientSmoothDerivatives

section

@[expose] public section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CoeffDeriv

open GlobalTheory.DerivedAction

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ} {R : Rep k r}
  {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

noncomputable def coefL (R : Rep k r) (x : R.H) (X : V) : R.H →L[ℝ] V :=
  ((innerSL ℂ x).smulRight X).restrictScalars ℝ

theorem coefL_apply (x w : R.H) (X : V) : coefL R x X w = ⟪x, w⟫_ℂ • X := rfl

theorem dsigW_smooth (hR : R.IsDG ε mu) {y : R.H} (hy : y ∈ R.sm) (b : List (Mx k r))
    (hb : ∀ Y ∈ b, B.inLie k r Y) : PI.UpqRep.dsigW (k := k) (r := r) R.σ b y ∈ R.sm := by
  induction b with
  | nil => exact hy
  | cons Y b ih =>
    exact dsig_smooth hR.2 (hb Y (by simp)) (ih fun Z hZ => hb Z (by simp [hZ]))

theorem right_step (hK : PI.KFinSmooth) (hR : R.IsDG ε mu) (X : V) (F : Mx k r → V) (x : R.H) {y : R.H}
    (hy : y ∈ R.sm) (hF : ∀ g ∈ GG k r, F g = ⟪x, R.σ g y⟫_ℂ • X) {Y : Mx k r} (hY : B.inLie k r Y)
    (g : Mx k r) (hg : g ∈ GG k r) :
    deriv (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • Y))) 0 =
      ⟪x, R.σ g (PI.UpqRep.dsig (k := k) (r := r) R.σ Y y)⟫_ℂ • X := by
  obtain ⟨hmul, -⟩ := rep_basic_of_isDS hK k r ε mu R hR
  have h := (coefL R x X).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_apply (σ := R.σ) hY hy (R.σ g))
  rw [← coefL_apply, ← h.deriv]
  congr 1
  funext t
  have he : NormedSpace.exp ((t : ℂ) • Y) ∈ GG k r := exp_mem hY t
  rw [hF _ (Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul hg he), hmul g hg _ he]
  rfl

theorem left_step (hK : PI.KFinSmooth) (hR : R.IsDG ε mu) (X : V) (F : Mx k r → V) {x : R.H} (y : R.H)
    (hx : x ∈ R.sm) (hF : ∀ g ∈ GG k r, F g = ⟪x, R.σ g y⟫_ℂ • X) {Y : Mx k r} (hY : B.inLie k r Y)
    (g : Mx k r) (hg : g ∈ GG k r) :
    B.LdV Y F g = ⟪PI.UpqRep.dsig (k := k) (r := r) R.σ Y x, R.σ g y⟫_ℂ • X := by
  obtain ⟨hmul, hone, hinner, -⟩ := rep_basic_of_isDS hK k r ε mu R hR
  have h1 := (hasDerivAt_dsig (σ := R.σ) hY hx).inner ℂ (hasDerivAt_const (0 : ℝ) (R.σ g y))
  simp only [inner_zero_right, zero_add] at h1
  have h := h1.smul_const X
  unfold B.LdV
  rw [← h.deriv]
  congr 1
  funext t
  have he : NormedSpace.exp ((t : ℂ) • Y) ∈ GG k r := exp_mem hY t
  have he' : NormedSpace.exp (-((t : ℂ) • Y)) ∈ GG k r := by
    have := exp_mem hY (-t)
    rwa [Complex.ofReal_neg, neg_smul] at this
  have hee : NormedSpace.exp ((t : ℂ) • Y) * NormedSpace.exp (-((t : ℂ) • Y)) = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.refl ((t : ℂ) • Y)).neg_right, add_neg_cancel, NormedSpace.exp_zero]
  rw [hF _ (Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul he' hg), hmul _ he' g hg, ← hinner _ he, ← hmul _ he _ he', hee, hone]

theorem coeff_dLR : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (X : V) (F : Mx k r → V), R.IsDG ε mu → ∀ x ∈ R.sm, ∀ y ∈ R.sm, (∀ g ∈ GG k r, F g = ⟪x, R.σ g y⟫_ℂ • X) → B.CkOn ⊤ (B.GV k r) F ∧ ∀ a b : List (Mx k r), (∀ Y ∈ a, B.inLie k r Y) → (∀ Y ∈ b, B.inLie k r Y) → ∀ g ∈ GG k r, B.dLR a b F g = ⟪PI.UpqRep.dsigW (k := k) (r := r) R.σ a x, R.σ g (PI.UpqRep.dsigW (k := k) (r := r) R.σ b y)⟫_ℂ • X := by
  intro hK k r ε mu R V _ _ X F hR x hx y hy hF
  refine ⟨fun g₀ hg₀ => ?_, fun a b ha hb => ?_⟩
  · obtain ⟨U, G, hU, hgU, hG, hfG⟩ := hy g₀ hg₀
    refine ⟨U, fun g => coefL R x X (G g), hU, hgU, (coefL R x X).contDiff.comp_contDiffOn hG, ?_⟩
    intro g hg hgG
    have e : R.σ g y = G g := hfG g hg hgG
    rw [hF g hgG, e]
    rfl
  · have hRw : ∀ g ∈ GG k r, B.Rw b F g = ⟪x, R.σ g (PI.UpqRep.dsigW (k := k) (r := r) R.σ b y)⟫_ℂ • X := by
      induction b with
      | nil => exact hF
      | cons Y b ih =>
        have hb' : ∀ Z ∈ b, B.inLie k r Z := fun Z hZ => hb Z (by simp [hZ])
        intro g hg
        exact right_step hK hR X _ x (dsigW_smooth hR hy b hb') (ih hb') (hb Y (by simp)) g hg
    induction a with
    | nil => exact hRw
    | cons Y a ih =>
      have ha' : ∀ Z ∈ a, B.inLie k r Z := fun Z hZ => ha Z (by simp [hZ])
      intro g hg
      exact left_step hK hR X _ _ (dsigW_smooth hR hx a ha') (ih ha') (ha Y (by simp)) g hg

end GlobalTheory.CoeffDeriv
end Gp91
end
end

-- Source module: CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.MatrixCoefficientSmoothDerivativesStatement

section

@[expose] public section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.Gp91.GlobalTheory.T.matrix_coefficient_smooth_derivatives : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (X : V) (F : Mx k r → V), R.IsDG ε mu → ∀ x ∈ R.sm, ∀ y ∈ R.sm, (∀ g ∈ GG k r, F g = ⟪x, R.σ g y⟫_ℂ • X) → B.CkOn ⊤ (B.GV k r) F ∧ ∀ a b : List (Mx k r), (∀ Y ∈ a, B.inLie k r Y) → (∀ Y ∈ b, B.inLie k r Y) → ∀ g ∈ GG k r, B.dLR a b F g = ⟪PI.UpqRep.dsigW (k := k) (r := r) R.σ a x, R.σ g (PI.UpqRep.dsigW (k := k) (r := r) R.σ b y)⟫_ℂ • X := by
  first | exact @GlobalTheory.CoeffDeriv.coeff_dLR | exact GlobalTheory.CoeffDeriv.coeff_dLR | (intros; apply GlobalTheory.CoeffDeriv.coeff_dLR <;> assumption)
end Gp91
end
end

-- Source module: CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselPeriodAdjointPair

section

@[expose] public section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory
namespace CoefDecay

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem dLR_zero (u v : List (B.Mat k r)) : B.dLR u v (0 : B.Mat k r → E) = 0 := by
  have h1 : B.Rw v (0 : B.Mat k r → E) = 0 := by
    unfold B.Rw
    induction v with
    | nil => rfl
    | cons X v ih =>
      rw [List.foldr_cons, ih]
      funext g
      simp [Formalism.REAL.RdV]
  unfold B.dLR
  rw [h1]
  induction u with
  | nil => rfl
  | cons X u ih =>
    rw [List.foldr_cons, ih]
    funext g
    simp [B.LdV]

theorem sum_mem {ι : Type} (A : ℝ) (f : ι → B.Mat k r → E) (t : Finset ι)
    (hf : ∀ i ∈ t, B.CkOn ⊤ (B.GV k r) (f i) ∧ ∀ m : ℕ, B.InCC A m (f i)) :
    B.CkOn ⊤ (B.GV k r) (∑ i ∈ t, f i) ∧ ∀ m : ℕ, B.InCC A m (∑ i ∈ t, f i) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    refine ⟨fun g₀ _ => ⟨Set.univ, 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩,
      fun m => ⟨0, fun g₀ _ => ⟨Set.univ, 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩, ?_⟩⟩
    intro u v _ _ _ g _
    simp [dLR_zero]
  | insert i t hi ih =>
    rw [Finset.sum_insert hi]
    obtain ⟨h1, h2⟩ := hf i (Finset.mem_insert_self _ _)
    obtain ⟨h3, h4⟩ := ih fun j hj => hf j (Finset.mem_insert_of_mem hj)
    refine ⟨Formalism.FourierDecayAlt.P.B4.ckOn_add h1 h3, fun m => ?_⟩
    obtain ⟨c, hc⟩ := h2 m
    obtain ⟨c', hc'⟩ := h4 m
    exact ⟨_, (Formalism.FourierDecayAlt.P.matrix_coefficient_linear k r E A m _ _ c c' 1 hc hc').1⟩

end CoefDecay

theorem isCoef_ckOn_inCC : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (l : R.H → Wp) (l' : R.H → Wq) (F : Mx k r → (Wq →L[ℂ] Wp)) (s : ℂ), R.IsDG ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → IsCoef R l l' F s → B.CkOn ⊤ (B.GV k r) F ∧ ∀ m : ℕ, B.InCC (aOf r h - 1) m F := by
  intro hH k r ε mu h R Wp _ _ _ _ Wq _ _ _ _ l l' F s hR hg hok hF
  obtain ⟨n, x, y, X, hxy, hFe, -⟩ := hF
  have hK : PI.KFinSmooth := hH.1.2.2.1
  have hsm : ∀ v ∈ R.TK, v ∈ R.sm := (GlobalTheory.rep_basic_of_isDS hK k r ε mu R hR).2.2.2.2.1
  let f : Fin n → B.Mat k r → (Wq →L[ℂ] Wp) := fun i g => ⟪x i, R.σ g (y i)⟫_ℂ • X i
  have hf : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      B.CkOn ⊤ (B.GV k r) (f i) ∧ ∀ m : ℕ, B.InCC (aOf r h - 1) m (f i) := by
    intro i _
    obtain ⟨h1, h2⟩ := GlobalTheory.T.matrix_coefficient_smooth_derivatives hK k r ε mu R (Wq →L[ℂ] Wp) (X i) (f i) hR (x i) (hsm _ (hxy i).1)
      (y i) (hsm _ (hxy i).2) (fun g _ => rfl)
    refine ⟨h1, fun m => ?_⟩
    obtain ⟨c, hc⟩ := GlobalTheory.T.matrix_coefficient_decay hH k r ε mu h R hR hg hok (x i) (hxy i).1 (y i) (hxy i).2 m
    refine ⟨c * ‖X i‖, Formalism.FourierDecayAlt.P.B6.smooth_on_mono le_top h1, fun u v hu hv hlen g hgG => ?_⟩
    rw [h2 u v (fun Y hY => (hu Y hY).1) (fun Y hY => (hv Y hY).1) g hgG, norm_smul, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hc u v hu hv hlen g hgG) (norm_nonneg _)
  obtain ⟨h1, h2⟩ := CoefDecay.sum_mem (aOf r h - 1) f Finset.univ hf
  have hc := GlobalTheory.ckOn_inCC_congr_on_group k r (Wq →L[ℂ] Wp) (aOf r h - 1) (∑ i, f i) F
    (fun g hgG => by rw [hFe g hgG, Finset.sum_apply])
  exact ⟨hc.1 h1, fun m => hc.2 m (h2 m)⟩

end GlobalTheory
end Gp91
end
end

-- Source module: CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselPeriodAdjointPairStatement

section

@[expose] public section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.Gp91.GlobalTheory.T.smooth_and_inCC_of_isCoef_of_gap : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (l : R.H → Wp) (l' : R.H → Wq) (F : Mx k r → (Wq →L[ℂ] Wp)) (s : ℂ), R.IsDG ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → IsCoef R l l' F s → B.CkOn ⊤ (B.GV k r) F ∧ ∀ m : ℕ, B.InCC (aOf r h - 1) m F := by
  first | exact @GlobalTheory.isCoef_ckOn_inCC | exact GlobalTheory.isCoef_ckOn_inCC | (intros; apply GlobalTheory.isCoef_ckOn_inCC <;> assumption)
end Gp91
end
end
