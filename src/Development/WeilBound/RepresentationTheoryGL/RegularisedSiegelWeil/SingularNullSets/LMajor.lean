module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatAdelicMatrixOfMemAdelicSchwartzStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatAdelicMatrixContinuousLeMajorantStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TemperateMultiplierPreservesSchwartzStatement
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicMatrixSchwartzMajorantMeasurableRationalShStatement
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
import Mathlib.RingTheory.Radical.NatInt
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ModerateGrowthSchwartz
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SphericalEisensteinSeriesOnGroup
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBoundFiniteInfiniteStatement
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LMajorA
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LMajorD
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

-- Source module: Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.CutSupp

section

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LMajor

variable {D : D7}

theorem cutSupp (θ : InfFam D) (hθ : IsInfFam θ) {a b : ℕ} (K : Set (Mx D a b)) (hK : IsCompact K)
    (Φ : Mx D a b → ℂ) (hbox : ∀ x, Φ x ≠ 0 → GlobalTheory.Unf.InBox K x) (c : (D.what₂.Tau → Fin a → Fin b → ℂ) → ℂ)
    (hc : HasCompactSupport c) : HasCompactSupport (fun x => c (fun τ i j => compAt θ τ x i j) * Φ x) := by
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall (0 : D.what₂.Tau → Fin a → Fin b → ℂ)
  obtain ⟨hcl, hcont, -, hcpt⟩ := (GlobalTheory.T.adelicMatrixSchwartzMajorant_measurable_rationalShift D θ hθ).1 a b K hK
  set R' : ℝ := ∑ _τ : D.what₂.Tau, ∑ _i : Fin a, ∑ _j : Fin b, R with hR'
  refine HasCompactSupport.intro' (hcpt R') (hcl.inter (isClosed_le hcont continuous_const)) fun x hx => ?_
  by_contra hne
  have hc0 : c (fun τ i j => compAt θ τ x i j) ≠ 0 := left_ne_zero_of_mul hne
  have hΦ : Φ x ≠ 0 := right_ne_zero_of_mul hne
  have hmem : (fun τ i j => compAt θ τ x i j) ∈ Metric.closedBall (0 : D.what₂.Tau → Fin a → Fin b → ℂ) R :=
    hR (subset_tsupport _ hc0)
  rw [Metric.mem_closedBall, dist_zero_right] at hmem
  apply hx
  refine ⟨hbox x hΦ, ?_⟩
  show GlobalTheory.Unf.realSize θ x ≤ R'
  unfold GlobalTheory.Unf.realSize
  refine Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  have h1 := norm_le_pi_norm (fun τ i j => compAt θ τ x i j) τ
  have h2 := norm_le_pi_norm (fun i j => compAt θ τ x i j) i
  have h3 := norm_le_pi_norm (fun j => compAt θ τ x i j) j
  exact h3.trans (h2.trans (h1.trans hmem))

end PositivityTheory.Rg.Rsw.L.LMajor

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.DomBound

section

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LMajor

variable {D : D7}

theorem domBound (θ : InfFam D) (hθ : IsInfFam θ) {a b : ℕ} (Φ : Mx D a b → ℂ) (hΦ : Φ ∈ schwartzA θ a b) :
    ∃ (k : ℕ) (f : Fin k → SchwartzMap (D.what₂.Tau → Fin a → Fin b → ℂ) ℂ) (M : ℝ), 0 ≤ M ∧
      ∀ x, ‖Φ x‖ ≤ M * ∑ i, ‖f i (fun τ i j => compAt θ τ x i j)‖ := by
  obtain ⟨-, k, f, g, hg, hb⟩ := GlobalTheory.T.schwartz_bound_finite_infinite D θ hθ a b Φ hΦ
  choose C hC using fun i => ((hg i).1.continuous).bounded_above_of_compact_support (hg i).2
  refine ⟨k, f, ∑ i, max (C i) 0, Finset.sum_nonneg fun i _ => le_max_right _ _, fun x => ?_⟩
  have h1 : ‖Φ x‖ ≤ ∑ i, ‖f i (fun τ i' j => compAt θ τ x i' j) * g i (fun i' j => finPart D (x i' j))‖ := by
    have h := hb x
    simp only [enorm_eq_nnnorm, ← ENNReal.ofNNReal_finsetSum, ENNReal.coe_le_coe] at h
    have h' : ((‖Φ x‖₊ : NNReal) : ℝ) ≤ ((∑ i, ‖f i (fun τ i' j => compAt θ τ x i' j) *
        g i (fun i' j => finPart D (x i' j))‖₊ : NNReal) : ℝ) := NNReal.coe_le_coe.mpr h
    simpa only [coe_nnnorm, NNReal.coe_sum] using h'
  refine h1.trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [norm_mul, mul_comm (∑ i, max (C i) 0)]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  exact (hC i _).trans ((le_max_left _ _).trans
    (Finset.single_le_sum (f := fun i => max (C i) 0) (fun i _ => le_max_right _ _) (Finset.mem_univ i)))

end PositivityTheory.Rg.Rsw.L.LMajor

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LMajorC

section

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LMajor

variable {D : D7}

theorem prodSB {X : Type} [TopologicalSpace X] {a b : ℕ} (G : Fin a → (Fin 1 → Fin b → X) → ℂ)
    (hG : ∀ i, G i ∈ GlobalTheory.WeilM.SB (Fin 1 → Fin b → X)) :
    (fun z : Fin a → Fin b → X => ∏ i, G i (fun _ j => z i j)) ∈ GlobalTheory.WeilM.SB (Fin a → Fin b → X) := by
  have hG' : ∀ i, IsLocallyConstant (G i) ∧ HasCompactSupport (G i) := hG
  have hrow : ∀ i : Fin a, Continuous fun z : Fin a → Fin b → X => (fun (_ : Fin 1) j => z i j) :=
    fun i => continuous_pi fun _ => continuous_pi fun j => (continuous_apply j).comp (continuous_apply i)
  show IsLocallyConstant (fun z : Fin a → Fin b → X => ∏ i, G i (fun _ j => z i j)) ∧
    HasCompactSupport (fun z : Fin a → Fin b → X => ∏ i, G i (fun _ j => z i j))
  refine ⟨?_, ?_⟩
  · have hfun : (fun z : Fin a → Fin b → X => ∏ i, G i (fun _ j => z i j)) =
        ∏ i, (fun z : Fin a → Fin b → X => G i (fun _ j => z i j)) := by
      funext z
      rw [Finset.prod_apply]
    rw [hfun]
    exact Finset.prod_induction _ IsLocallyConstant (fun f g hf hg => hf.comp₂ hg (· * ·))
      (IsLocallyConstant.const 1) (fun i _ => (hG' i).1.comp_continuous (hrow i))
  · let S : Set (Fin a → Fin b → X) := ⋂ i, (fun z : Fin a → Fin b → X => (fun (_ : Fin 1) j => z i j)) ⁻¹' tsupport (G i)
    let gm : (Fin a → Fin 1 → Fin b → X) → (Fin a → Fin b → X) := fun w i j => w i 0 j
    have hgm : Continuous gm :=
      continuous_pi fun i => continuous_pi fun j =>
        (continuous_apply j).comp ((continuous_apply 0).comp (continuous_apply i))
    have hK : IsCompact (gm '' Set.univ.pi fun i => tsupport (G i)) :=
      (isCompact_univ_pi fun i => (hG' i).2).image hgm
    have hSc : IsClosed S := isClosed_iInter fun i => (isClosed_tsupport (G i)).preimage (hrow i)
    have hsub : tsupport (fun z : Fin a → Fin b → X => ∏ i, G i (fun _ j => z i j)) ⊆ S := by
      refine closure_minimal ?_ hSc
      intro z hz
      have hz' : ∏ i, G i (fun _ j => z i j) ≠ 0 := hz
      rw [Finset.prod_ne_zero_iff] at hz'
      exact Set.mem_iInter.2 fun i => subset_tsupport _ (hz' i (Finset.mem_univ i))
    have hSK : S ⊆ gm '' Set.univ.pi fun i => tsupport (G i) := by
      intro z hz
      refine ⟨fun i _ j => z i j, fun i _ => Set.mem_iInter.1 hz i, rfl⟩
    exact hK.of_isClosed_subset (isClosed_tsupport _) (hsub.trans hSK)

theorem rowSB (θ : InfFam D) {m n : ℕ} (s : AE D) (hs : infPart D s = 0) (hs' : finPart D s = 1)
    (h : Mx D m n → ℂ) (hh : h ∈ schwartzA θ m n) :
    ∃ G ∈ GlobalTheory.WeilM.SB (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E),
      ∀ y : Mx D m n, h (s • y) = G (fun i j => finPart D (y i j)) := by
  change h ∈ Submodule.span ℂ _ at hh
  induction hh using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    refine ⟨f (fun _ _ _ => 0) • g, Submodule.smul_mem _ _ hg, fun y => ?_⟩
    have h1 : (fun τ i j => Formalism.IndefR.Datum.compAt θ τ (s • y) i j) = fun _ _ _ => (0 : ℂ) := by
      funext τ i j
      have hc : Formalism.IndefR.Datum.compAt θ τ (s • y) i j = θ τ (Formalism.L2.Theta.infPart D (s * y i j)) := rfl
      rw [hc, map_mul, hs, zero_mul, map_zero]
    have h2 : (fun i j => Formalism.L2.Theta.finPart D ((s • y) i j)) = fun i j => Formalism.L2.Theta.finPart D (y i j) := by
      funext i j
      have hc : Formalism.L2.Theta.finPart D ((s • y) i j) = Formalism.L2.Theta.finPart D (s * y i j) := rfl
      rw [hc, map_mul, hs', one_mul]
    show f (fun τ i j => Formalism.IndefR.Datum.compAt θ τ (s • y) i j) *
        g (fun i j => Formalism.L2.Theta.finPart D ((s • y) i j)) = _
    rw [h1, h2, Pi.smul_apply, smul_eq_mul]
  | zero => exact ⟨0, Submodule.zero_mem _, fun y => rfl⟩
  | add x z _ _ hx hz =>
    obtain ⟨G1, hG1, e1⟩ := hx
    obtain ⟨G2, hG2, e2⟩ := hz
    exact ⟨G1 + G2, Submodule.add_mem _ hG1 hG2, fun y => by rw [Pi.add_apply, Pi.add_apply, e1, e2]⟩
  | smul c x _ hx =>
    obtain ⟨G1, hG1, e1⟩ := hx
    exact ⟨c • G1, Submodule.smul_mem _ _ hG1, fun y => by rw [Pi.smul_apply, Pi.smul_apply, e1]⟩

end PositivityTheory.Rg.Rsw.L.LMajor

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LMajorE

section

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LMajor

variable {D : D7} {a b : ℕ}

theorem row_smul (i : Fin a) (c : AE D) (x : Mx D a b) : row i (c • x) = c • row i x := by
  rfl

theorem intOff_row {S : Finset (Pl D)} {x : Mx D a b} (hx : IntOff S x) (i : Fin a) : IntOff S (row i (sF D • x)) := by
  intro v hv i' j
  show cv D v (sF D * x i j) ∈ _
  rw [cv_sF]
  exact hx v hv i j

theorem not_intOff_row {S : Finset (Pl D)} {x : Mx D a b} (hx : ¬ IntOff S x) :
    ∃ i, ¬ IntOff S (row i (sF D • x)) := by
  by_contra hcon
  push Not at hcon
  apply hx
  intro v hv i j
  have e := hcon i v hv 0 j
  have e' : cv D v (sF D * x i j) ∈ GlobalTheory.AdelicU.intLoc (↥D.host.F) D.host.E v := e
  rwa [cv_sF] at e'




theorem bumpMaj (hB : BumpEx) (θ : InfFam D) (hθ : IsInfFam θ) {S : Finset (Pl D)} {e : AE D} (he : IsIdem S e)
    (K : Set (Mx D a b)) (hK : IsCompact K) (F₀ : SchwartzMap (D.what₂.Tau → Fin a → Fin b → ℂ) ℂ)
    (hF₀ : ∀ y, 0 ≤ (F₀ y).re ∧ (F₀ y).im = 0) :
    ∃ Φ₀ ∈ schwartzA θ a b, Good S e Φ₀ ∧ (∀ x, 0 ≤ (Φ₀ x).re ∧ (Φ₀ x).im = 0) ∧
      ∀ x, IntOff S x → GlobalTheory.Unf.InBox K x → Φ₀ x = F₀ (cA θ x) := by
  have hCint : ∀ y ∈ (fun k => sF D • (e • k)) '' K, IntOff S y := by
    rintro _ ⟨k, -, rfl⟩ v hv i j
    show cv D v (sF D * (e * k i j)) ∈ _
    rw [cv_sF, map_mul, he.2 v, if_neg hv, zero_mul]
    exact (GlobalTheory.AdelicU.intLoc _ _ v).zero_mem
  obtain ⟨η, hη⟩ := hB D θ hθ a b S e he _
    (hK.image ((continuous_const_smul (sF D)).comp (continuous_const_smul e))) hCint
  have hG : ∀ i, ∃ G ∈ GlobalTheory.WeilM.SB (Fin 1 → Fin b → TensorProduct (↥D.host.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af ↥D.host.F) D.host.E),
      ∀ y : Mx D 1 b, η i (sF D • y) = G fun i' j => finPart D (y i' j) :=
    fun i => rowSB θ (sF D) infPart_sF finPart_sF (η i) (hη i).1
  choose G hGSB hGeq using hG
  set Ψ : Mx D a b → ℂ := fun x => ∏ i, η i (sF D • row i x) with hΨ
  have hΨG : ∀ x, Ψ x = (fun z => ∏ i, G i fun _ j => z i j) (fun i j => finPart D (x i j)) := by
    intro x
    exact Finset.prod_congr rfl fun i _ => hGeq i (row i x)
  have hΨgood : Good S e Ψ := by
    intro x
    by_cases hx : IntOff S x
    · rw [if_pos hx]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← row_smul, (hη i).2.2.1, if_pos (intOff_row hx i), ← row_smul, ← row_smul, smul_comm e (sF D) x]
    · rw [if_neg hx]
      obtain ⟨i, hi⟩ := not_intOff_row hx
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      rw [← row_smul, (hη i).2.2.1, if_neg hi]
  refine ⟨fun x => F₀ (cA θ x) * Ψ x, ?_, good_mul θ he hΨgood (fun z => F₀ z), ?_, ?_⟩
  · apply Submodule.subset_span
    refine ⟨F₀, fun z => ∏ i, G i fun _ j => z i j, prodSB G hGSB, ?_⟩
    funext x
    rw [hΨG x]
  · intro x
    exact re_im_mul (hF₀ _) (re_im_prod _ _ fun i => ⟨((hη i).2.2.2.1 _).1, ((hη i).2.2.2.1 _).2.2⟩)
  · rintro x hx ⟨k, hk, hxk⟩
    have hfin : ∀ i j, finPart D (x i j) = finPart D (k i j) := by
      intro i j
      have h0 := congrFun (congrFun hxk i) j
      simp only [Matrix.map_apply, Matrix.sub_apply, map_sub, Matrix.zero_apply] at h0
      exact sub_eq_zero.mp h0
    suffices h1 : Ψ x = 1 by
      show F₀ (cA θ x) * Ψ x = F₀ (cA θ x)
      rw [h1, mul_one]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [← row_smul, (hη i).2.2.1, if_pos (intOff_row hx i), ← row_smul, smul_comm e (sF D) x, row_smul, hGeq i]
    have hfun : (fun i' j => finPart D ((row i (e • x)) i' j)) = (fun i' j => finPart D ((row i (e • k)) i' j)) := by
      funext i' j
      show finPart D (e * x i j) = finPart D (e * k i j)
      rw [map_mul, map_mul, hfin]
    rw [hfun, ← hGeq i, ← row_smul]
    exact (hη i).2.2.2.2 _ ⟨k, hk, rfl⟩

end PositivityTheory.Rg.Rsw.L.LMajor

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LMajor

section

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L

open LMajor in
theorem major : IdemEx → GoodEv → BumpEx → Major := by
  intro _ _ hB D θ hθ a b S e he Φ hΦ hG
  obtain ⟨k, f, M, hM, hdom⟩ := domBound θ hθ Φ hΦ
  obtain ⟨-, K, hK, hmaj⟩ := GlobalTheory.T.schwartzBruhatAdelicMatrix_continuous_le_majorant D θ hθ a b Φ (GlobalTheory.T.isSchwartzBruhatAdelicMatrix_of_mem_adelicSchwartz D θ hθ a b Φ hΦ)
  obtain ⟨C0, hC0⟩ := hmaj 0
  have hbox : ∀ x, Φ x ≠ 0 → GlobalTheory.Unf.InBox K x := by
    intro x hx
    by_contra hb
    have h := hC0 x
    rw [GlobalTheory.Unf.maj, if_neg hb, mul_zero] at h
    exact hx (norm_le_zero_iff.mp h)
  obtain ⟨F₀, hF₀, hcut⟩ := schMajor f
  obtain ⟨Φ₀, hΦ₀, hG₀, hpos, heq⟩ := bumpMaj hB θ hθ he K hK F₀ hF₀
  refine ⟨Φ₀, hΦ₀, hG₀, hpos, fun ε hε => ?_⟩
  have hMk : 0 < M * k + 1 := by have := mul_nonneg hM (Nat.cast_nonneg (α := ℝ) k); linarith
  obtain ⟨c, hct, hcc, hcb⟩ := hcut (ε / (M * k + 1)) (div_pos hε hMk)
  refine ⟨fun x => c (cA θ x) * Φ x, GlobalTheory.T.temperate_multiplier_preserves_schwartz D θ a b c hct Φ hΦ, good_mul θ he hG c,
    cutSupp θ hθ K hK Φ hbox c hcc, fun x => ?_⟩
  show ‖Φ x - c (cA θ x) * Φ x‖ ≤ ε * (Φ₀ x).re
  rw [show Φ x - c (cA θ x) * Φ x = (1 - c (cA θ x)) * Φ x by ring, norm_mul]
  by_cases h0 : Φ x = 0
  · rw [h0, norm_zero, mul_zero]
    exact mul_nonneg hε.le (hpos x).1
  have hx : IntOff S x := by
    by_contra hx
    have h := hG x
    rw [if_neg hx] at h
    exact h0 h
  rw [heq x hx (hbox x h0)]
  have hF : 0 ≤ (F₀ (cA θ x)).re := (hF₀ _).1
  calc ‖1 - c (cA θ x)‖ * ‖Φ x‖ ≤ ‖1 - c (cA θ x)‖ * (M * ∑ i, ‖f i (cA θ x)‖) :=
        mul_le_mul_of_nonneg_left (hdom x) (norm_nonneg _)
    _ = M * ∑ i, ‖f i (cA θ x)‖ * ‖1 - c (cA θ x)‖ := by
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ M * ∑ _i : Fin k, ε / (M * k + 1) * (F₀ (cA θ x)).re := by
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hcb i _) hM
    _ = (M * k) / (M * k + 1) * (ε * (F₀ (cA θ x)).re) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
    _ ≤ 1 * (ε * (F₀ (cA θ x)).re) := by
        gcongr
        rw [div_le_one hMk]
        linarith
    _ = ε * (F₀ (cA θ x)).re := one_mul _

end PositivityTheory.Rg.Rsw.L

end
end
end
