module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerAlong
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StdCharFinitePartRationalEqExpTrace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DRhoSumAndSobOLe
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaNormSqSumHeisenbergTranslatesDistinctChars
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelHeisenbergPhaseEqCexpRealPointsStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelTermHeisenbergIsotropicCharacterStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelTermLinearThetaFunctions
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelTermLinearThetaFunctionsStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelTermDerivativeIsotropicDirection

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MixedTerm.IsoDeriv

variable {D : D7} {θ : InfFam D}

theorem isoPart_lineAt (hθ : IsInfFam θ) (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin r) ℂ) (t : ℝ) :
    isoPart V W C (lineAt θ τ z t) = lineAt θ τ (dirAt V W C τ z) t := by
  have hL := GlobalTheory.OrientedHeis.isLineAt_lineAt hθ τ z
  let L : ℝ →+ WO V W :=
    { toFun := fun t => isoPart V W C (lineAt θ τ z t)
      map_zero' := by unfold isoPart; rw [AddMonoidHom.map_zero, Matrix.zero_mul]
      map_add' := fun s t => by unfold isoPart; rw [AddMonoidHom.map_add (f := _), Matrix.add_mul] }
  have hL' : IsLineAt θ τ (dirAt V W C τ z) L := by
    refine ⟨(continuous_isoPart V W C).comp hL.1, fun t => ?_, fun t τ' => ?_⟩
    · show (isoPart V W C (lineAt θ τ z t)).map (finPart D) = 0
      unfold isoPart
      rw [Matrix.map_mul, hL.2.1, Matrix.zero_mul]
    · show compAt θ τ' (isoPart V W C (lineAt θ τ z t)) = _
      unfold isoPart
      rw [GlobalTheory.OrientedHeis.compAt_mul, hL.2.2]
      have e : compAt θ τ' ((adj D C * V.gram).map (incA D)) = (adj D C * V.gram).map (tauE D τ') := by
        unfold compAt
        rw [Matrix.map_map]
        congr 1
        funext e
        exact GlobalTheory.FockCompare.comp_incA hθ τ' e
      rw [e]
      split_ifs with h
      · subst h
        unfold dirAt
        rw [Matrix.smul_mul]
      · rw [Matrix.zero_mul]
  rw [GlobalTheory.RealLineAt.lineAt_unique D θ hθ _ _ τ _ _ _ (GlobalTheory.OrientedHeis.isLineAt_lineAt hθ τ _) hL']
  rfl

end GlobalTheory.MixedTerm.IsoDeriv

namespace GlobalTheory.MixedTerm.IsoDeriv

variable {D : D7} {θ : InfFam D}

theorem phase_lineAt (hθ : IsInfFam θ) (V W : HSp D) {r : ℕ} (C C' : Matrix (Fin V.rank) (Fin r) D.host.E)
    (hCC : adj D C * V.gram * C' = 1) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    (y : Matrix (Fin W.rank) (Fin r) D.host.E) (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin r) ℂ) (t : ℝ) :
    phase ψ V W C C' y (lineAt θ τ z t) = Complex.exp (2 * Real.pi * Complex.I *
      ((t * (2 * (Matrix.trace ((pairQ W y).map (tauE D τ) * z)).re) : ℝ) : ℂ)) := by
  have hL := GlobalTheory.OrientedHeis.isLineAt_lineAt hθ τ z
  rw [GlobalTheory.T.mixedModelHeisenbergPhase_eq_cexp_realPoints D V W r C C' hCC ψ hψ θ hθ y _ (hL.2.1 t)]
  congr 4
  simp only [hL.2.2 t]
  rw [Finset.sum_eq_single τ (fun b _ hb => by rw [if_neg hb, Matrix.mul_zero, Matrix.trace_zero, Complex.zero_re,
    mul_zero]) (by simp), if_pos rfl, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
  ring

end GlobalTheory.MixedTerm.IsoDeriv

namespace GlobalTheory.MixedTerm.IsoDeriv

theorem term_dRho_dirAt : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → adj D C * V.gram * C' = 1 → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ G : WO V W → ℂ, IsThetaFunO ψ V W G → ∀ (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin r) ℂ) (y : Matrix (Fin W.rank) (Fin r) D.host.E), term ψ V V' W C C' B μ 𝓨 (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ (dirAt V W C τ z) G) y = (2 * Real.pi * Complex.I * ((2 * (Matrix.trace ((pairQ W y).map (tauE D τ) * z)).re : ℝ) : ℂ)) * term ψ V V' W C C' B μ 𝓨 G y := by
  intro D V V' W r C C' B hs hCC ψ hψ θ hθ μ 𝓨 h G hG τ z y
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 2 * (Matrix.trace ((pairQ W y).map (tauE D τ) * z)).re := ⟨_, rfl⟩
  rw [← hc]
  have hL'r := GlobalTheory.OrientedHeis.isRealDir_lineAt (S := V) (T := W) hθ τ (dirAt V W C τ z)

  have hg : ∀ t : ℝ, term ψ V V' W C C' B μ 𝓨 (heisO ψ V W (lineAt θ τ (dirAt V W C τ z) t) G) y =
      Complex.exp (2 * Real.pi * Complex.I * ((t * c : ℝ) : ℂ)) * term ψ V V' W C C' B μ 𝓨 G y := fun t => by
    rw [← isoPart_lineAt hθ V W C τ z t, GlobalTheory.T.mixedModelTerm_heisenbergIsotropic_character D V V' W r C C' B hs ψ hψ μ 𝓨 h G hG y _,
      phase_lineAt hθ V W C C' hCC hψ y τ z t, hc]
  have hd1 : HasDerivAt (fun t : ℝ => term ψ V V' W C C' B μ 𝓨 (heisO ψ V W (lineAt θ τ (dirAt V W C τ z) t) G) y)
      (2 * Real.pi * Complex.I * (c : ℂ) * term ψ V V' W C C' B μ 𝓨 G y) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => 2 * Real.pi * Complex.I * ((t * c : ℝ) : ℂ)) (2 * Real.pi * Complex.I * (c : ℂ)) 0 := by
      have := (((hasDerivAt_id (0 : ℝ)).mul_const c).ofReal_comp).const_mul (2 * Real.pi * Complex.I)
      simpa using this
    have h2 := (h1.cexp).mul_const (term ψ V V' W C C' B μ 𝓨 G y)
    rw [zero_mul, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul] at h2
    exact h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => hg t)

  obtain ⟨K, hK⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ (GlobalTheory.OrientedHeis.theta_dLine hθ hψ hL'r hG)
  haveI : IsFiniteMeasure (μ.restrict 𝓨) :=
    ⟨by rw [Measure.restrict_apply_univ, h.2.2]; exact ENNReal.one_lt_top⟩
  have e0 : heisO ψ V W (lineAt θ τ (dirAt V W C τ z) 0) (GlobalTheory.OrientedHeis.dLine ψ V W (lineAt θ τ (dirAt V W C τ z)) G) =
      Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ (dirAt V W C τ z) G := by
    rw [AddMonoidHom.map_zero, GlobalTheory.OrientedHeis.heisO_zero]
    rfl
  have hd2 : HasDerivAt (fun t : ℝ => term ψ V V' W C C' B μ 𝓨 (heisO ψ V W (lineAt θ τ (dirAt V W C τ z) t) G) y)
      (term ψ V V' W C C' B μ 𝓨 (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ (dirAt V W C τ z) G) y) 0 := by
    rw [← e0]
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ.restrict 𝓨) (x₀ := (0 : ℝ))
      (F' := fun t x => heisO ψ V W (isoPart V W C' (Matrix.map y (incA D)))
        (heisO ψ V W (lineAt θ τ (dirAt V W C τ z) t)
          (GlobalTheory.OrientedHeis.dLine ψ V W (lineAt θ τ (dirAt V W C τ z)) G)) (isoPart V W C x + midPart V V' W B 0))
      (bound := fun _ => K) (s := Set.univ) Filter.univ_mem ?_ ?_ ?_ ?_ (integrable_const K) ?_).2
    · exact Filter.Eventually.of_forall fun t =>
        (integrableOn_heisO V W C hψ h (GlobalTheory.OrientedHeis.theta_heisO_real hθ hψ (hL'r.2 t) hG) _ _).aestronglyMeasurable
    · exact integrableOn_heisO V W C hψ h (GlobalTheory.OrientedHeis.theta_heisO_real hθ hψ (hL'r.2 0) hG) _ _
    · exact (integrableOn_heisO V W C hψ h (GlobalTheory.OrientedHeis.theta_heisO_real hθ hψ (hL'r.2 0)
        (GlobalTheory.OrientedHeis.theta_dLine hθ hψ hL'r hG)) _ _).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun x t _ => ?_
      rw [GlobalTheory.HeisOrtho.norm_heisO hψ.1, GlobalTheory.HeisOrtho.norm_heisO hψ.1]
      exact hK _
    · refine Filter.Eventually.of_forall fun x t _ => ?_
      exact (GlobalTheory.OrientedHeis.hasDerivAt_heisO hθ hψ hL'r hG _ t).const_mul _
  rw [hd2.unique hd1]

end GlobalTheory.MixedTerm.IsoDeriv
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelTermDerivativeIsotropicDirectionStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.mixedModelTerm_derivative_isotropicDirection : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → adj D C * V.gram * C' = 1 → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ G : WO V W → ℂ, IsThetaFunO ψ V W G → ∀ (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin r) ℂ) (y : Matrix (Fin W.rank) (Fin r) D.host.E), term ψ V V' W C C' B μ 𝓨 (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ (dirAt V W C τ z) G) y = (2 * Real.pi * Complex.I * ((2 * (Matrix.trace ((pairQ W y).map (tauE D τ) * z)).re : ℝ) : ℂ)) * term ψ V V' W C C' B μ 𝓨 G y := by
  first | exact @GlobalTheory.MixedTerm.IsoDeriv.term_dRho_dirAt | exact GlobalTheory.MixedTerm.IsoDeriv.term_dRho_dirAt | (intros; apply GlobalTheory.MixedTerm.IsoDeriv.term_dRho_dirAt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelTermDerivAlongRationalPairing

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm

namespace GlobalTheory.MixedTerm.DerLaw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sum_tauE_add_conj (D : D7) (e : D.host.E) :
    ∑ t, (tauE D t e + starRingEnd ℂ (tauE D t e)) = ((Algebra.trace ℚ D.host.E e : ℚ) : ℂ) := by
  classical
  have h1 : ((Algebra.trace ℚ D.host.E e : ℚ) : ℂ) = ∑ σ : D.host.E →+* ℂ, σ e := by
    have := trace_eq_sum_embeddings (K := ℚ) (L := D.host.E) ℂ (x := e)
    rw [eq_ratCast] at this
    rw [this]
    exact (Fintype.sum_equiv (RingHom.equivRatAlgHom D.host.E ℂ) _ _ fun _ => rfl).symm
  have hi := GlobalTheory.StdRat.tauE_injective D
  have hcm := GlobalTheory.StdRat.tauE_cm D
  have hb : Function.Bijective (Sum.elim (tauE D) fun t => ComplexEmbedding.conjugate (tauE D t)) := by
    have hc : ∀ σ : D.host.E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ :=
      fun σ => star_star σ
    constructor
    · rintro (a | a) (b | b) h <;> simp only [Sum.elim_inl, Sum.elim_inr] at h
      · rw [hi h]
      · exact absurd ⟨a, h⟩ ((hcm (tauE D b)).1 ⟨b, rfl⟩)
      · exact absurd ⟨b, h.symm⟩ ((hcm (tauE D a)).1 ⟨a, rfl⟩)
      · have := congrArg ComplexEmbedding.conjugate h
        rw [hc, hc] at this
        rw [hi this]
    · intro σ
      by_cases h : ∃ t, tauE D t = ComplexEmbedding.conjugate σ
      · obtain ⟨t, ht⟩ := h
        exact ⟨Sum.inr t, by simp only [Sum.elim_inr]; rw [ht, hc]⟩
      · obtain ⟨t, ht⟩ := (hcm σ).2 h
        exact ⟨Sum.inl t, ht⟩
  have h4 := hb.sum_comp fun σ : D.host.E →+* ℂ => σ e
  rw [Fintype.sum_sum_type, ← h1] at h4
  simp only [Sum.elim_inl, Sum.elim_inr, ComplexEmbedding.conjugate_coe_eq] at h4
  rw [Finset.sum_add_distrib, h4]

theorem sum_two_re_tauE (D : D7) (e : D.host.E) :
    ∑ t, (((2 * (tauE D t e).re : ℝ)) : ℂ) = ((Algebra.trace ℚ D.host.E e : ℚ) : ℂ) := by
  rw [← sum_tauE_add_conj]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Complex.add_conj]

theorem trace_map_mul (D : D7) (τ : D.what₂.Tau) {m n : ℕ} (P : Matrix (Fin m) (Fin n) D.host.E)
    (x : Matrix (Fin n) (Fin m) D.host.E) :
    Matrix.trace (P.map (tauE D τ) * x.map (tauE D τ)) = tauE D τ (Matrix.trace (P * x)) := by
  rw [← Matrix.map_mul]

  simp only [Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]

theorem term_derAlong : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → adj D C * V.gram * C' = 1 → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ G : WO V W → ℂ, IsThetaFunO ψ V W G → ∀ x y : Matrix (Fin W.rank) (Fin r) D.host.E, term ψ V V' W C C' B μ 𝓨 (derAlong ψ θ V W C x G) y = (2 * Real.pi * Complex.I * (ratPair W y x : ℂ)) * term ψ V V' W C C' B μ 𝓨 G y := by
  intro D V V' W r C C' B hiso hCC ψ hψ θ hθ μ 𝓨 hcov G hG x y
  have hlin := GlobalTheory.T.mixedModelTerm_linear_thetaFunctions D V V' W r C C' B ψ hψ μ 𝓨 hcov y
  have hder := fun τ => GlobalTheory.T.mixedModelTerm_derivative_isotropicDirection D V V' W r C C' B hiso hCC ψ hψ θ hθ μ 𝓨 hcov G hG τ (x.map (tauE D τ)) y
  set f : D.what₂.Tau → WO V W → ℂ :=
    fun τ => Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ (dirAt V W C τ (x.map (tauE D τ))) G with hf
  have hft : ∀ τ, IsThetaFunO ψ V W (f τ) := fun τ => GlobalTheory.OrientedHeis.theta_dRho hθ hψ τ _ hG
  have hsum : ∀ s : Finset D.what₂.Tau,
      term ψ V V' W C C' B μ 𝓨 (∑ τ ∈ s, f τ) y = ∑ τ ∈ s, term ψ V V' W C C' B μ 𝓨 (f τ) y := by
    intro s
    classical
    induction s using Finset.induction_on with
    | empty =>
      have h0 := hlin.2 0 G hG
      rw [zero_smul, zero_mul] at h0
      simpa using h0
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        hlin.1 _ _ (hft a) (GlobalTheory.Size.theta_finsetSum s fun i _ => hft i), ih]
  show term ψ V V' W C C' B μ 𝓨 (∑ τ, f τ) y = _
  rw [hsum, Finset.sum_congr rfl fun τ _ => hder τ, ← Finset.sum_mul, ← Finset.mul_sum]
  congr 2
  simp only [trace_map_mul, sum_two_re_tauE, ratPair, Complex.ofReal_ratCast]

end GlobalTheory.MixedTerm.DerLaw

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelTermDerivAlongRationalPairingStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.mixedModelTerm_derivAlong_rational_pairing : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → adj D C * V.gram * C' = 1 → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ G : WO V W → ℂ, IsThetaFunO ψ V W G → ∀ x y : Matrix (Fin W.rank) (Fin r) D.host.E, term ψ V V' W C C' B μ 𝓨 (derAlong ψ θ V W C x G) y = (2 * Real.pi * Complex.I * (ratPair W y x : ℂ)) * term ψ V V' W C C' B μ 𝓨 G y := by
  first | exact @GlobalTheory.MixedTerm.DerLaw.term_derAlong | exact GlobalTheory.MixedTerm.DerLaw.term_derAlong | (intros; apply GlobalTheory.MixedTerm.DerLaw.term_derAlong <;> assumption)
end
end
