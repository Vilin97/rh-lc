module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DifferenceQuotientIsometryExchangeAlt
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocalL2IsometryAlt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqEqToL2
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ContinuousBw
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DBoundB
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DCalc
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DHol
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DilDSt
import Mathlib.Algebra.Order.Archimedean.Real.Hom
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DetNeOfPosDef
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DifferenceQuotientIsometryExchange
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.EvXTemperate
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GCSch
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.IteratedDerivOfReal
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.TraceGramBReal
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.IteratedDerivOfReal
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LNe
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.SmulOneConj
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.TraceGramBReal
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DerivStep

section

@[expose] public section

noncomputable section

open Topology Metric

namespace PositivityTheory.Rg.Sw.Glob

namespace DilDH

variable {E : Type} [MetricSpace E] [ProperSpace E]

theorem deriv_step {U : Set ℂ} (hU : IsOpen U) {g : ℂ → E → ℂ}
    (hc : ContinuousOn (fun p : ℂ × E => g p.1 p.2) (U ×ˢ Set.univ))
    (hd : ∀ u, DifferentiableOn ℂ (fun z => g z u) U) :
    ContinuousOn (fun p : ℂ × E => deriv (fun z => g z p.2) p.1) (U ×ˢ Set.univ) := by
  intro p hp
  obtain ⟨z0, u0⟩ := p
  have hz0 : z0 ∈ U := hp.1
  have hopen : IsOpen (U ×ˢ (Set.univ : Set E)) := hU.prod isOpen_univ
  apply ContinuousAt.continuousWithinAt
  obtain ⟨R, hR, hRU⟩ := Metric.isOpen_iff.1 hU z0 hz0
  set r := R / 4 with hr
  have hr0 : 0 < r := by positivity
  have hK : closedBall z0 (2 * r) ⊆ U := (closedBall_subset_ball (by linarith)).trans hRU
  rw [Metric.continuousAt_iff']
  intro ε hε
  have hunif : ∀ᶠ u in 𝓝 u0, ∀ w ∈ closedBall z0 (2 * r), dist (g w u) (g w u0) < ε * r / 2 := by
    apply (isCompact_closedBall z0 (2 * r)).eventually_forall_of_forall_eventually
    intro w hw
    have hwU : w ∈ U := hK hw
    have hcont : ContinuousAt (fun p : ℂ × E => g p.1 p.2) (w, u0) :=
      hc.continuousAt (hopen.mem_nhds ⟨hwU, trivial⟩)
    have h1 : Filter.Tendsto (fun q : E × ℂ => g q.2 q.1) (𝓝 (u0, w)) (𝓝 (g w u0)) :=
      hcont.tendsto.comp (continuous_swap.tendsto (u0, w))
    have h2 : Filter.Tendsto (fun q : E × ℂ => g q.2 u0) (𝓝 (u0, w)) (𝓝 (g w u0)) :=
      hcont.tendsto.comp ((continuous_snd.prodMk continuous_const).tendsto (u0, w))
    have hε' : 0 < ε * r / 4 := by positivity
    filter_upwards [Metric.tendsto_nhds.1 h1 _ hε', Metric.tendsto_nhds.1 h2 _ hε'] with q hq1 hq2
    calc dist (g q.2 q.1) (g q.2 u0)
        ≤ dist (g q.2 q.1) (g w u0) + dist (g q.2 u0) (g w u0) := dist_triangle_right _ _ _
      _ < ε * r / 4 + ε * r / 4 := add_lt_add hq1 hq2
      _ = ε * r / 2 := by ring
  have hd0 : ContinuousAt (deriv fun z => g z u0) z0 :=
    ((hd u0).deriv hU).continuousOn.continuousAt (hU.mem_nhds hz0)
  have e1 := (continuous_fst.tendsto (z0, u0)).eventually
    (Metric.tendsto_nhds.1 hd0 (ε / 2) (by positivity))
  have e2 := (continuous_fst.tendsto (z0, u0)).eventually (Metric.ball_mem_nhds z0 hr0)
  have e3 := (continuous_snd.tendsto (z0, u0)).eventually hunif
  filter_upwards [e1, e2, e3] with q hq1 hq2 hq3
  obtain ⟨z, u⟩ := q
  simp only at hq1 hq2 hq3 ⊢
  have hzU : closedBall z r ⊆ closedBall z0 (2 * r) := by
    intro w hw
    rw [mem_closedBall] at hw ⊢
    calc dist w z0 ≤ dist w z + dist z z0 := dist_triangle _ _ _
      _ ≤ r + r := add_le_add hw hq2.le
      _ = 2 * r := by ring
  have hcu : deriv (fun z => g z u) z = Complex.cderiv r (fun z => g z u) z :=
    (Complex.cderiv_eq_deriv hU (hd u) hr0 (hzU.trans hK)).symm
  have hcu0 : deriv (fun z => g z u0) z = Complex.cderiv r (fun z => g z u0) z :=
    (Complex.cderiv_eq_deriv hU (hd u0) hr0 (hzU.trans hK)).symm
  have hsph : sphere z r ⊆ U := sphere_subset_closedBall.trans (hzU.trans hK)
  have hdiff : dist (Complex.cderiv r (fun z => g z u) z) (Complex.cderiv r (fun z => g z u0) z)
      < ε * r / 2 / r := by
    rw [dist_eq_norm]
    apply Complex.norm_cderiv_sub_lt hr0
    · intro w hw
      rw [← dist_eq_norm]
      exact hq3 w (hzU (sphere_subset_closedBall hw))
    · exact (hd u).continuousOn.mono hsph
    · exact (hd u0).continuousOn.mono hsph
  have hhalf : ε * r / 2 / r = ε / 2 := by field_simp
  rw [hhalf] at hdiff
  have hfirst : dist (deriv (fun z => g z u) z) (deriv (fun z => g z u0) z) < ε / 2 := by
    rw [hcu, hcu0]
    exact hdiff
  calc dist (deriv (fun z => g z u) z) (deriv (fun z => g z u0) z0)
      ≤ dist (deriv (fun z => g z u) z) (deriv (fun z => g z u0) z)
        + dist (deriv (fun z => g z u0) z) (deriv (fun z => g z u0) z0) := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add hfirst hq1
    _ = ε := by ring

def scaleL (m n : ℕ) (s : ℝ) (X : Fin n → ℝ) : (Fin m → Fin n → ℂ) ≃ₗ[ℝ] (Fin m → Fin n → ℂ) where
  toFun u := fun i j => u i j * (Real.exp (s * X j) : ℂ)
  invFun u := fun i j => u i j * (Real.exp (-(s * X j)) : ℂ)
  map_add' u v := by funext i j; simp [add_mul]
  map_smul' r u := by funext i j; simp [Complex.real_smul, mul_assoc]
  left_inv u := by
    funext i j
    simp only [mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, Complex.ofReal_one,
      mul_one]
  right_inv u := by
    funext i j
    simp only [mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, Complex.ofReal_one,
      mul_one]

end DilDH

theorem schScale : SchScale := by
  intro m n f s X a hf
  obtain ⟨S, hS⟩ := hf
  refine ⟨a • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (DilDH.scaleL m n s X).toContinuousLinearEquiv S, ?_⟩
  funext u
  simp only [SchwartzMap.smul_apply, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    Function.comp_apply, smul_eq_mul, ← hS]
  rfl

theorem contDeriv : ContDeriv := by
  intro m n U hU f hc hd r
  induction r generalizing f with
  | zero => simpa only [iteratedDeriv_zero] using hc
  | succ k ih =>
    have h1 := DilDH.deriv_step hU hc hd
    have h2 : ∀ u, DifferentiableOn ℂ (fun z => deriv (fun z => f z u) z) U :=
      fun u => (hd u).deriv hU
    have h3 := ih (fun z u => deriv (fun z => f z u) z) h1 h2
    simpa only [iteratedDeriv_succ'] using h3

end PositivityTheory.Rg.Sw.Glob
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.IsSiegelI

section

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.DilEH

attribute [local irreducible] famC

variable {D : D7} {n : ℕ} {θ : InfFam D} {V : HSp D} {τ : D.what₂.Tau} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ}
  {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} {ι : GR n →* G D n}
  {L : GR n → ((Fin V.rank → Fin n → ℂ) → ℂ) → ((Fin V.rank → Fin n → ℂ) → ℂ)}

theorem isSiegel_I : IsSiegel (Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
  unfold IsSiegel
  have e : (-(Complex.I / 2)) • (Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ) - (Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ) = 1 := by
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Complex.star_def, Complex.conj_I, ← sub_smul, smul_smul]
    have : -(Complex.I / 2) * (Complex.I - -Complex.I) = 1 := by ring_nf; rw [Complex.I_sq]; ring
    rw [this, one_smul]
  rw [e]; exact Matrix.PosDef.one


theorem exch (hDR : DReal) (hDB : DBound) (hDC : DCalc) (hDL : DifferenceQuotientIsometryExchange) (hCD : ContDeriv) (hSS : SchScale) (hSF : SchFP)
    (hL : IsLocFact ω τ fr ι L) (hθ : IsInfFam θ) (hfr : IsUnit fr.det) {Ψ : Mx D V.rank n → ℂ}
    (hΨ : AwayCls θ τ fr Ψ) {x₀ : Mx D V.rank n} (hx₀ : Ψ x₀ ≠ 0) {ε : Fin V.rank → Bool} {t c : ℝ} (hc : 0 < c)
    (htc : |t| = c) {e : ℤ}
    (hG : ∀ (y : GR n) (Z : Matrix (Fin n) (Fin n) ℂ), IsSiegel Z →
      L y (gZf ε t c Z) = fun u => jF e (cnt (epsT t ε) true) (cnt (epsT t ε) false) y Z * gZf ε t c (actZ y Z) u)
    {X : Fin n → ℝ} {a : ℝ → GR n} (ha : ∀ s, IsDil X s (a s)) (y'' : GR n) {κ : ℝ} (hκ : 0 < κ)
    (hL2 : ∀ f, IsSch f → ∫ u, ‖L y'' f u‖ ^ 2 = κ * ∫ u, ‖f u‖ ^ 2) (r : ℕ) :
    L y'' (fP c ((dil c X ^ r) 1)) = fun u => iteratedDeriv r (fun s : ℝ => famC ε t c e y'' X s u) 0 := by
  have hg0 : gZf ε t c (Complex.I • 1) = fP c (1 : PX V.rank n) := (DilAH.fP_one ε t c hc).symm
  have hg0s : IsSch (gZf ε t c (Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ)) : (Fin V.rank → Fin n → ℂ) → ℂ) := by
    rw [hg0]; exact hSF _ _ c hc 1
  have hbase : ∀ (y : GR n) (s : ℝ), L (y * a s) (gZf ε t c (Complex.I • 1)) = famC ε t c e y X s := by
    intro y s
    rw [hG _ _ isSiegel_I, hDR _ _ ε t c e y X a ha s]
  set Gf : ℕ → ℝ → (Fin V.rank → Fin n → ℂ) → ℂ := fun r s u => iteratedDeriv r (fun s' : ℝ => famC ε t c e 1 X s' u) s
    with hGf
  set Ef : ℕ → ℝ → (Fin V.rank → Fin n → ℂ) → ℂ :=
    fun r s u => iteratedDeriv r (fun s' : ℝ => famC ε t c e y'' X s' u) s with hEf
  obtain ⟨hC1, hC2⟩ := hDC V.rank n ε t c e X hc htc
  obtain ⟨hB1, hB2, -⟩ := hDB V.rank n ε t c e X hc htc
  have hGs : ∀ r s, IsSch (Gf r s) := by
    intro r s
    have : Gf r s = fun u => (Real.exp (s * (V.rank : ℝ) * ∑ j, X j) : ℂ) *
        fP c ((dil c X ^ r) 1) (fun a j => u a j * Real.exp (s * X j)) := by
      funext u; exact hC1 s r u
    rw [this]
    exact hSS _ _ _ s X _ (hSF _ _ c hc _)
  have hstrip : IsOpen (stripS X) := DBoundBH.isOpen_stripS X
  have hR : ∀ s : ℝ, (s : ℂ) ∈ stripS X := fun s j => by simp [div_pos Real.pi_pos]

  set F : ℂ → (Fin V.rank → Fin n → ℂ) → ℂ := fun z u => famC ε t c e y'' X z u with hF
  have hFd : ∀ u, DifferentiableOn ℂ (fun z => F z u) (stripS X) := fun u => hB1 y'' u
  have hFc : ContinuousOn (fun p : ℂ × (Fin V.rank → Fin n → ℂ) => F p.1 p.2) (stripS X ×ˢ Set.univ) := by
    have hcont : Continuous (fun p : ℂ × (Fin V.rank → Fin n → ℂ) => ((y'', p) : GR n × (ℂ × (Fin V.rank → Fin n → ℂ)))) :=
      continuous_const.prodMk continuous_id
    exact hB2.comp hcont.continuousOn fun p hp => ⟨Set.mem_univ _, hp⟩
  have hEr : ∀ r u, (fun s : ℝ => iteratedDeriv r (fun s' : ℝ => F s' u) s) = fun s : ℝ => iteratedDeriv r (fun z => F z u) s :=
    fun r u => DilCH.iteratedDeriv_ofReal hstrip (hFd u) hR r
  have key : ∀ r s, L y'' (Gf r s) = Ef r s := by
    intro r
    induction r with
    | zero =>
      intro s
      have e1 : Gf 0 s = L (a s) (gZf ε t c (Complex.I • 1)) := by
        funext u; rw [← one_mul (a s), hbase]; simp [hGf]
      have e2 : Ef 0 s = famC ε t c e y'' X s := by funext u; simp [hEf]
      rw [e1, e2, ← DilCH.L_mul hL hθ hfr hΨ hx₀ y'' (a s) hg0s, hbase]
    | succ r ih =>
      intro s
      refine hDL V.rank n (L y'') κ hκ (fun f hf => hL.1 y'' f hf)
        (fun f g hf hg => DilCH.L_sub hL hθ hfr hΨ hx₀ y'' hf hg)
        (fun a' f hf => DilCH.L_smul hL hθ hfr hΨ hx₀ y'' a' hf) hL2 (Gf r) (Gf (r + 1) s) (Ef (r + 1) s) s
        (hGs r) (hGs (r + 1) s) ?_ (hC2 r s) ?_
      ·
        have hcd := hCD V.rank n (stripS X) hstrip F hFc hFd (r + 1)
        have : Ef (r + 1) s = fun u => iteratedDeriv (r + 1) (fun z => F z u) (s : ℂ) := by
          funext u; simp only [hEf]; rw [show (fun s' : ℝ => famC ε t c e y'' X s' u) = fun s' : ℝ => F s' u from rfl,
            congrFun (hEr (r + 1) u) s]
        rw [this]
        exact hcd.comp_continuous (f := fun u : Fin V.rank → Fin n → ℂ => ((s : ℂ), u))
          (continuous_const.prodMk continuous_id) fun u => ⟨hR s, Set.mem_univ _⟩
      · intro u
        simp only [ih]
        have hd : HasDerivAt (fun s' : ℝ => Ef r s' u) (Ef (r + 1) s u) s := by
          have e3 : (fun s' : ℝ => Ef r s' u) = fun s' : ℝ => iteratedDeriv r (fun z => F z u) s' := hEr r u
          have e4 : Ef (r + 1) s u = iteratedDeriv (r + 1) (fun z => F z u) s := congrFun (hEr (r + 1) u) s
          rw [e3, e4, iteratedDeriv_succ]
          exact ((DilCH.diffOn_iteratedDeriv hstrip (hFd u) r).differentiableAt
            (hstrip.mem_nhds (hR s))).hasDerivAt.comp_ofReal
        have := hd.tendsto_slope_zero
        refine this.congr fun h => ?_
        simp only [div_eq_inv_mul, Complex.real_smul, Complex.ofReal_inv]
  have e0 : Gf r 0 = fP c ((dil c X ^ r) 1) := by
    funext u; rw [show Gf r 0 u = _ from hC1 0 r u]; simp
  rw [← e0, key r 0]

end PositivityTheory.Rg.Sw.Glob.DilEH
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.IteratedDerivMulConst

section

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.DilH

instance fcGR (n : ℕ) : FirstCountableTopology (GR n) := by
  have h1 : FirstCountableTopology (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) :=
    inferInstanceAs (FirstCountableTopology ((Fin n ⊕ Fin n) → (Fin n ⊕ Fin n) → ℂ))
  have h2 : FirstCountableTopology (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph.symm.isInducing).firstCountableTopology
  exact (Units.isInducing_embedProduct.comp Topology.IsInducing.subtypeVal).firstCountableTopology

theorem iteratedDeriv_mul_const (f : ℂ → ℂ) (k : ℂ) (r : ℕ) :
    iteratedDeriv r (fun w => f w * k) = fun w => iteratedDeriv r f w * k := by
  induction r with
  | zero => simp
  | succ r ih => rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]; exact deriv_mul_const_field' k

theorem isSiegel_Ir {n : ℕ} {r : ℝ} (hr : 0 < r) :
    IsSiegel ((Complex.I * r) • (1 : Matrix (Fin n) (Fin n) ℂ)) ∧
      IsSiegel (((-(Complex.I * r)) • (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ) := by
  have hc : ((-(Complex.I * r)) • (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ = (Complex.I * r) • 1 := by
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, star_neg, star_mul', Complex.star_def, Complex.conj_I,
      Complex.conj_ofReal]
    ring_nf
  rw [hc]
  have : IsSiegel ((Complex.I * r) • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
    unfold IsSiegel
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, ← sub_smul, smul_smul]
    have e : -(Complex.I / 2) * (Complex.I * r - star (Complex.I * r)) = (r : ℂ) := by
      rw [star_mul', Complex.star_def, Complex.conj_I, Complex.conj_ofReal]
      ring_nf; rw [Complex.I_sq]; ring
    rw [e]
    exact Matrix.PosDef.one.smul (by exact_mod_cast hr)
  exact ⟨this, this⟩

end PositivityTheory.Rg.Sw.Glob.DilH

namespace PositivityTheory.Rg.Sw.Glob

attribute [local irreducible] famC


open DilAH DilCH DilEH DilH in
theorem gIdil_of' (hWTC : GlobalTheory.Published.WeilThetaConvergence) (hDecA : DecompAway) (hAway : AwayAct) (hLF : LocFact)
    (hGL : GaussLaw) (hAI : AwayIn) (hLL2 : LocalL2Isometry) (hSF : SchFP) (hLNe : LNe) (hDC : DCalc) : GIdil := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx Ψ hΨA g X a ha
  have hl0 : ∀ τ', l τ' ≠ 0 := hLNe D ψ θ l hcx.hψ hcx.hθ hcx.hl
  have hc : 0 < cLoc l τ := cLoc_pos (hl0 τ)
  have htc : |tLoc l τ| = cLoc l τ := abs_tLoc l τ
  have hfr : IsUnit fr.det := hcx.hfr.1
  have hΨ : AwayCls θ τ fr Ψ := hAI D n V θ l s τ ε fr hcx.hθ hcx.hs hcx.hfr hl0 Ψ hΨA
  obtain ⟨L, hL⟩ := hLF D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx
  obtain ⟨e, hG⟩ := hGL D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx L hL
  obtain ⟨x, y₀, hxt, hg, -⟩ := hDecA D n θ τ ι hcx.hθ hcx.hι g
  obtain ⟨A, hA⟩ := hAway D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx x hxt
  obtain ⟨hAΨ, hAact⟩ := hA Ψ hΨ
  have hsch1 : ∀ P : PX V.rank n, IsSch (fP (cLoc l τ) P) := fun P => hSF _ _ _ hc P
  obtain ⟨hB1, hB2, hB3⟩ := dBound V.rank n ε (tLoc l τ) (cLoc l τ) e X hc htc
  have hfam : ∀ (y : GR n) (z : ℂ), z ∈ stripS X → IsSch (famC ε (tLoc l τ) (cLoc l τ) e y X z) := by
    intro y z hz
    obtain ⟨h1, h2, -, -⟩ := dSieg n y X z hz
    unfold famC
    exact SchwartzDifferenceQuotient.isSch_smul _ (gCSch V.rank n ε _ _ hc htc _ _ h1 h2)
  have hphi : ∀ P : PX V.rank n, phiS θ τ fr (cLoc l τ) Ψ P = ⟨tens θ τ fr (fP (cLoc l τ) P) Ψ, hΨ.2 _ (hsch1 P)⟩ := by
    intro P; unfold phiS; rw [dite_eq_left (hΨ.2 _ (hsch1 P))]
  have hω : ∀ (y : GR n) (P : PX V.rank n), (ω (g * ι y) (phiS θ τ fr (cLoc l τ) Ψ P)).1 =
      tens θ τ fr (L (y₀ * y) (fP (cLoc l τ) P)) (A Ψ) := by
    intro y P
    have h1 : ω (ι (y₀ * y)) ⟨tens θ τ fr (fP (cLoc l τ) P) Ψ, hΨ.2 _ (hsch1 P)⟩ =
        ⟨tens θ τ fr (L (y₀ * y) (fP (cLoc l τ) P)) Ψ, hΨ.2 _ (hL.1 _ _ (hsch1 P))⟩ :=
      Subtype.ext (hL.2 _ Ψ hΨ _ (hsch1 P))
    rw [hg, mul_assoc, ← map_mul ι, map_mul ω, Module.End.mul_apply, hphi, h1]
    exact hAact _ (hL.1 _ _ (hsch1 P))
  have hbase : ∀ (y : GR n) (s' : ℝ), L (y * a s') (fP (cLoc l τ) 1) = famC ε (tLoc l τ) (cLoc l τ) e y X s' := by
    intro y s'
    rw [fP_one ε (tLoc l τ) _ hc, hG _ _ isSiegel_I, dReal _ _ ε _ _ e y X a ha s']
  have hR : ∀ s' : ℝ, (s' : ℂ) ∈ stripS X := fun s' j => by simp [div_pos Real.pi_pos]
  have hAc : Continuous (A Ψ) := FTH.cont_of_away hcx.hθ hAΨ
  set φ : GR n → ℂ → Mx D V.rank n → ℂ := fun y z xx => tens θ τ fr (famC ε (tLoc l τ) (cLoc l τ) e (y₀ * y) X z) (A Ψ) xx
    with hφ
  have hs1 : ∀ y z, z ∈ stripS X → φ y z ∈ schwartzA θ V.rank n := fun y z hz => hAΨ.2 _ (hfam _ z hz)
  have hs2 : ∀ y xx, DifferentiableOn ℂ (fun z => φ y z xx) (stripS X) := fun y xx =>
    (hB1 (y₀ * y) _).mul_const _
  have hcu : Continuous fun xx : Mx D V.rank n => fr⁻¹ * compAt θ τ xx :=
    continuous_const.matrix_mul (GlobalTheory.RealWeil.continuous_compAt hcx.hθ τ V.rank n)
  have hs3 : ∀ xx, ContinuousOn (fun p : GR n × ℂ => φ p.1 p.2 xx) (Set.univ ×ˢ stripS X) := by
    intro xx
    have hm : Continuous fun p : GR n × ℂ => (y₀ * p.1, p.2, fr⁻¹ * compAt θ τ xx) := by fun_prop
    refine ContinuousOn.mul (hB2.comp hm.continuousOn fun p hp => ⟨Set.mem_univ _, hp.2, Set.mem_univ _⟩) continuousOn_const
  have hs4 : ∀ y, ContinuousOn (fun zx : ℂ × Mx D V.rank n => φ y zx.1 zx.2) (stripS X ×ˢ Set.univ) := by
    intro y
    have hm : Continuous fun zx : ℂ × Mx D V.rank n => (y₀ * y, zx.1, fr⁻¹ * compAt θ τ zx.2) :=
      continuous_const.prodMk (continuous_fst.prodMk (hcu.comp continuous_snd))
    refine ContinuousOn.mul (hB2.comp hm.continuousOn fun p hp => ⟨Set.mem_univ _, hp.1, Set.mem_univ _⟩)
      (hAc.comp continuous_snd).continuousOn
  have hs5 : ∀ (p₀ : GR n) (z₀ : ℂ), z₀ ∈ stripS X → ∃ (N : Set (GR n × ℂ)) (M : Mx D V.rank n → ℂ), N ∈ 𝓝 (p₀, z₀) ∧
      M ∈ schwartzA θ V.rank n ∧ ∀ pz ∈ N, pz.2 ∈ stripS X → ∀ xx, ‖φ pz.1 pz.2 xx‖ ≤ ‖M xx‖ := by
    intro p₀ z₀ hz₀
    obtain ⟨N', δ, C, hN', hδ, hbd⟩ := hB3 (y₀ * p₀) z₀ hz₀
    have hm : Continuous fun p : GR n × ℂ => (y₀ * p.1, p.2) := by fun_prop
    have hdc : 0 < δ / cLoc l τ := div_pos hδ hc
    obtain ⟨hS1, hS2⟩ := isSiegel_Ir (n := n) hdc
    have hgs := gCSch V.rank n ε _ _ hc htc _ _ hS1 hS2
    refine ⟨(fun p : GR n × ℂ => (y₀ * p.1, p.2)) ⁻¹' N', tens θ τ fr (fun u => ((max C 0 : ℝ) : ℂ) *
      gC ε (tLoc l τ) (cLoc l τ) ((Complex.I * ((δ / cLoc l τ : ℝ) : ℂ)) • 1) ((-(Complex.I * ((δ / cLoc l τ : ℝ) : ℂ))) • 1) u) (A Ψ),
      hm.continuousAt.preimage_mem_nhds hN', hAΨ.2 _ (SchwartzDifferenceQuotient.isSch_smul _ hgs), fun pz hpz hz xx => ?_⟩
    have hb := hbd _ hpz hz (fr⁻¹ * compAt θ τ xx)
    simp only [hφ, tens, norm_mul]
    have hgg := gC_gauss ε (tLoc l τ) (cLoc l τ) hc δ (fr⁻¹ * compAt θ τ xx)
    rw [hgg]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_max_right C 0)]
    have he : ∀ r : ℝ, ‖Complex.exp (-(r : ℂ))‖ = Real.exp (-r) := fun r => by
      rw [← Complex.ofReal_neg, Complex.norm_exp_ofReal]
    rw [he]
    exact mul_le_mul_of_nonneg_right (hb.trans (mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.exp_pos _).le))
      (norm_nonneg _)
  obtain ⟨hcont, hdiff, hiter⟩ := dHol hWTC D n V hcx.hn hcx.hr.2.2 θ hcx.hθ ν hcx.hν (GR n) (stripS X)
    (DBoundBH.isOpen_stripS X) φ hs1 hs2 hs3 hs4 hs5
  refine ⟨stripS X, fun y z => ⨍ q, descend (GQ V) (fun h => ∑' ξ, φ y z (GlobalTheory.SiegelFormula.invPt V h ξ)) q ∂autMeasure V ν,
    DBoundBH.isOpen_stripS X, hR, hcont, fun y => ⟨hdiff y, fun t' => ?_, fun r => ?_⟩⟩
  ·
    have hfun : (ω (g * ι (y * a t')) (phiS θ τ fr (cLoc l τ) Ψ 1)).1 = φ y t' := by
      rw [hω, ← mul_assoc, hbase]
    have key : (fun h => ∑' ξ, φ y t' (GlobalTheory.SiegelFormula.invPt V h ξ)) =
        theta ω (phiS θ τ fr (cLoc l τ) Ψ 1) (g * ι (y * a t')) := by
      funext h; unfold theta; rw [hfun]; rfl
    show (⨍ q, descend (GQ V) (fun h => ∑' ξ, φ y t' (GlobalTheory.SiegelFormula.invPt V h ξ)) q ∂autMeasure V ν) = _
    rw [key]; rfl
  ·
    rw [hiter y r 0 (hR 0)]
    have hpt : ∀ xx : Mx D V.rank n, iteratedDeriv r (fun w => φ y w xx) 0 =
        tens θ τ fr (L (y₀ * y) (fP (cLoc l τ) ((dil (cLoc l τ) X ^ r) 1))) (A Ψ) xx := by
      intro xx
      simp only [hφ, tens]
      rw [iteratedDeriv_mul_const]
      beta_reduce
      by_cases hz : ∃ x₀, Ψ x₀ ≠ 0
      · obtain ⟨x₀, hx₀⟩ := hz
        obtain ⟨κ, hκ, hκL⟩ := hLL2 D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx L hL (y₀ * y)
        have hofR := congrFun (iteratedDeriv_ofReal (DBoundBH.isOpen_stripS X)
          (hB1 (y₀ * y) (fr⁻¹ * compAt θ τ xx)) hR r) 0
        simp only [Complex.ofReal_zero] at hofR
        rw [← hofR, exch dReal dBound hDC dL2 contDeriv schScale hSF hL hcx.hθ hfr hΨ hx₀ hc htc hG ha (y₀ * y) hκ hκL r]
      · push_neg at hz
        have hΨ0 : Ψ = 0 := funext hz
        have h0 : tens θ τ fr (fP (cLoc l τ) 1) (A Ψ) = 0 := by
          rw [← hAact _ (hsch1 1)]
          have : (⟨tens θ τ fr (fP (cLoc l τ) 1) Ψ, hΨ.2 _ (hsch1 1)⟩ : schwartzA θ V.rank n) = 0 :=
            Subtype.ext (by funext x'; simp [tens, hΨ0])
          rw [this, map_zero]; rfl
        have hAx : A Ψ xx = 0 := by
          have := congrFun h0 xx
          simp only [tens, Pi.zero_apply] at this
          refine (mul_eq_zero.1 this).resolve_left ?_
          simp [fP, evX, gs, Complex.exp_ne_zero]
        rw [hAx, mul_zero, mul_zero]
    have key : (fun h => ∑' ξ, iteratedDeriv r (fun w => φ y w (GlobalTheory.SiegelFormula.invPt V h ξ)) 0) =
        theta ω (phiS θ τ fr (cLoc l τ) Ψ ((dil (cLoc l τ) X ^ r) 1)) (g * ι y) := by
      funext h; unfold theta; rw [hω]
      congr 1; funext ξ; exact hpt _
    show (⨍ q, descend (GQ V) (fun h => ∑' ξ, iteratedDeriv r (fun w => φ y w (GlobalTheory.SiegelFormula.invPt V h ξ)) 0) q
      ∂autMeasure V ν) = _
    rw [key]; rfl

theorem gIdil_of (hWTC : GlobalTheory.Published.WeilThetaConvergence) (_hGZ : GZSch) (hDecA : DecompAway) (hAway : AwayAct)
    (hLF : LocFact) (hGL : GaussLaw) (hAI : AwayIn) (hLL2 : LocalL2Isometry) : GIdil :=
  gIdil_of' hWTC hDecA hAway hLF hGL hAI hLL2 schFP lNe dCalc

end PositivityTheory.Rg.Sw.Glob
end
end
end
