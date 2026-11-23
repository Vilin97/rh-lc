module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.FourierZero
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.AvgHolPf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.COneLawPf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.CntFalse
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.DilExPf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.CompFinFinOne
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SingularHermitian.MatrixEqFrameConjugate
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.DZTranspose
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardTraceAddCharIsStandardCharOfAdmissibleCM
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.FcCont
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.WeightFactorDilation
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.ContinuousChr
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.SigmaSigmaOfGood
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SingularHermitian.AesmOfContinuous
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaSplitting.SplitW
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.SectionEqThetaZero

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.CharacterW1TraceExp

section

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.AStep

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem nbw1 (d : SD σ) (R : RD d) (w : InfinitePlace F) {nb : nA σ d.Y d.b → d.G} (hN : IsNMap d.b nb)
    (xN : GR d.n) (h : Matrix (Fin d.n) (Fin d.n) ℂ) (hxN : mR xN = nU h) :
    ∃ β₁ : nA σ d.Y d.b, R.ι w xN = nb β₁ ∧ d.cw w β₁.1 = R.ζ • h ∧ (∀ u, u ≠ w → d.cw u β₁.1 = 0) ∧
      finOne F • β₁.1 = 0 := by
  have hP : inFrame d.b (R.ι w xN) = Matrix.fromBlocks 1 (inFrame d.b (R.ι w xN)).toBlocks₁₂ 0 1 := by
    apply Place.cw_ext d
    · intro u
      rw [KSing.UnitaryGroupBasics.cw_fromBlocks, KSing.UnitaryGroupBasics.cw_toBlocks₁₂]
      by_cases hu : u = w
      · subst hu
        rw [KSing.UnitaryGroupBasics.cw_unip d R u xN _ hxN, Matrix.toBlocks_fromBlocks₁₂]
      · rw [R.off_w w u xN hu, KSing.UnitaryGroupBasics.toBlocks₁₂_one, Matrix.fromBlocks_one]
    · rw [Matrix.fromBlocks_smul, KSing.UnitaryGroupBasics.fin_toBlocks₁₂, R.off_f w xN, ← KSing.UnitaryGroupBasics.fin_toBlocks₁₂, KSing.UnitaryGroupBasics.toBlocks₁₂_one,
        smul_zero]
      rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, smul_zero]
  let β₁ : nA σ d.Y d.b := ⟨(inFrame d.b (R.ι w xN)).toBlocks₁₂, AddSubgroup.subset_closure ⟨R.ι w xN, hP⟩⟩
  have hB : inFrame d.b (R.ι w xN) = Matrix.fromBlocks 1 β₁.1 0 1 := hP
  refine ⟨β₁, KSing.UnitaryGroupBasics.inFrame_inj d (by rw [hN]; exact hB), ?_, fun u hu => ?_, ?_⟩
  · have e := KSing.UnitaryGroupBasics.cw_unip d R w xN _ hxN
    rw [hB, KSing.UnitaryGroupBasics.cw_fromBlocks] at e
    exact (Matrix.fromBlocks_inj.1 e).2.1
  · have e := R.off_w w u xN hu
    rw [hB, KSing.UnitaryGroupBasics.cw_fromBlocks, ← Matrix.fromBlocks_one] at e
    exact (Matrix.fromBlocks_inj.1 e).2.1
  · have e := R.off_f w xN
    rw [hB, Matrix.fromBlocks_smul, ← Matrix.fromBlocks_one, Matrix.fromBlocks_smul] at e
    exact (Matrix.fromBlocks_inj.1 e).2.1.trans (smul_zero _)

def betaW (d : SD σ) (R : RD d) (w : InfinitePlace F) (T : nF σ d.Y d.b) : Matrix (Fin d.n) (Fin d.n) ℂ :=
  ((2 * Real.pi : ℝ) : ℂ) • (-(2 : ℂ) • (R.ζ • d.cw w T.1.1))

theorem character_w1_trace_exp (d : SD σ) (R : RD d) (w : InfinitePlace F) (T : nF σ d.Y d.b) (β₁ : nA σ d.Y d.b)
    (h : Matrix (Fin d.n) (Fin d.n) ℂ) (hh : h.IsHermitian) (hBw : d.cw w β₁.1 = R.ζ • h)
    (hBu : ∀ u, u ≠ w → d.cw u β₁.1 = 0) (hBf : finOne F • β₁.1 = 0) :
    d.B.ψ (d.tt (T.1.1 * β₁.1)) = Complex.exp (Complex.I * (betaW d R w T * h).trace) := by
  have hT : (d.cw w T.1.1)ᵀ + ((R.ε : ℤ) : ℂ) • (d.cw w T.1.1).map star = 0 := by
    refine AddSubgroup.closure_induction
      (p := fun β _ => (d.cw w β)ᵀ + ((R.ε : ℤ) : ℂ) • (d.cw w β).map star = 0) ?_ ?_ ?_ ?_ T.1.2
    · rintro β ⟨x, hx⟩
      have e := KSing.UnitaryGroupBasics.form_w d R w x
      rw [hx, KSing.UnitaryGroupBasics.cw_fromBlocks] at e
      simp [Krd.Qc, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply] at e
      rw [add_comm]
      exact e
    · ext i j; simp [SD.cw]
    · intro a b _ _ ha hb
      ext i j
      have ea := congrFun (congrFun ha i) j
      have eb := congrFun (congrFun hb i) j
      simp [SD.cw] at ea eb ⊢
      linear_combination ea + eb
    · intro a _ ha
      ext i j
      have ea := congrFun (congrFun ha i) j
      simp [SD.cw] at ea ⊢
      linear_combination -ea
  unfold betaW
  obtain ⟨Tw, hTw⟩ : ∃ Tw, Tw = d.cw w T.1.1 := ⟨_, rfl⟩
  rw [← hTw] at hT ⊢
  have hAh : (R.ζ • Tw)ᴴ = R.ζ • Tw := by
    ext i j
    have e := congrFun (congrFun hT j) i
    simp only [Matrix.add_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.zero_apply,
      smul_eq_mul] at e
    rw [Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, star_mul']
    rcases R.hζ with ⟨hε, hζ⟩ | ⟨hε, hζ⟩
    · rw [hζ]; rw [hε] at e; simp at e ⊢; linear_combination -e
    · rw [hζ]; rw [hε] at e; simp at e ⊢; linear_combination (-Complex.I) * e
  have hf : finOne F • (T.1.1 * β₁.1).trace = 0 := by
    rw [← Matrix.trace_smul, ← Matrix.mul_smul, hBf, Matrix.mul_zero, Matrix.trace_zero]
  have hw : ∀ u, u ≠ w → piInf (d.B.emb u) (T.1.1 * β₁.1).trace = 0 := fun u hu => by
    rw [KSing.UnitaryGroupBasics.piInf_trace, KSing.UnitaryGroupBasics.cw_mul, hBu u hu, Matrix.mul_zero, Matrix.trace_zero]
  have hz := Place.psi_trace_at d.std d.cm d.B.emb w (T.1.1 * β₁.1).trace hf hw
  have hw' : piInf (d.B.emb w) (T.1.1 * β₁.1).trace = ((R.ζ • Tw) * h).trace := by
    rw [KSing.UnitaryGroupBasics.piInf_trace, KSing.UnitaryGroupBasics.cw_mul, hBw, ← hTw, Matrix.mul_smul, Matrix.smul_mul]
  have hreal : ((((R.ζ • Tw) * h).trace).re : ℂ) = ((R.ζ • Tw) * h).trace := by
    have hs : star (((R.ζ • Tw) * h).trace) = ((R.ζ • Tw) * h).trace := by
      rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hAh, hh.eq, Matrix.trace_mul_comm]
    exact Complex.conj_eq_iff_re.1 hs
  have eR : ((((2 * Real.pi : ℝ) : ℂ) • (-(2 : ℂ) • (R.ζ • Tw))) * h).trace =
      ((2 * Real.pi : ℝ) : ℂ) * (-2 * (R.ζ • Tw * h).trace) := by
    rw [Matrix.smul_mul, Matrix.trace_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul]
  unfold SD.tt
  rw [hz, hw', eR]
  generalize (R.ζ • Tw * h).trace = c at hreal ⊢
  congr 1
  push_cast
  rw [hreal]
  ring

end PositivityTheory.SiegelWeilFormula.AStep

end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.HolCoefPf

section

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.AStep

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem holPhi (H : Hyps) {d : SD σ} (R : RD d) (w : InfinitePlace F) {nb lam 𝓖}
    (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) (T : nF σ d.Y d.b) (A : d.G → ℂ) (hAc : Continuous A)
    (hAi : ∀ γ ∈ rat2 σ d.Y, ∀ g, A (γ * g) = A g) (pp qq : ℕ) (e : ℤ)
    (hA : ∀ g, IsHolW pp qq e fun y => A (g * R.ι w y)) (x' : d.G) :
    IsHolW pp qq e fun y => fc d.B.ψ d.b nb lam 𝓖 A T (x' * R.ι w y) := by
  have hc' := hc
  obtain ⟨hN, -, -, h1⟩ := hc'
  have hσ := kfour.sigma_sigma_of_good d.ok.good
  obtain ⟨iLC, iSC, iT2, iBo⟩ := kfour.nA_top hσ d.ok.frame
  obtain ⟨K, hK, hKc⟩ := kfour.nF_cocompact hσ d.ok.frame
  obtain ⟨-, -, hTG, -, -, -⟩ := H.auxEx F E σ d
  have := hTG
  have hψ := GlobalTheory.StdCharWeilDatum.isCharAF d.ok.good.std
  have hnbc := kfour.nb_continuous hσ d.ok.frame hN
  let u : nA σ d.Y d.b → ℂ := fun β => d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1))))
  have huc : Continuous u := kfour.continuous_chr hψ.1 T.1.1
  let γf : nA σ d.Y d.b → nA σ d.Y d.b := fun β => Classical.choose (hKc β)
  have hγ : ∀ β, γf β ∈ nF σ d.Y d.b ∧ γf β + β ∈ K := fun β => Classical.choose_spec (hKc β)
  let c : nA σ d.Y d.b → d.G := fun β => nb (γf β + β) * x'
  have key : ∀ β (g : d.G), A (c β * g) = A (nb β * (x' * g)) := by
    intro β g
    show A (nb (γf β + β) * x' * g) = _
    rw [KSing.nb_add d hN, mul_assoc, mul_assoc, hAi _ (KSing.nb_rat d hN (hγ β).1)]
  have : IsFiniteMeasure (lam.restrict 𝓖) := ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
  have hC : IsCompact ((fun k => nb k * x') '' K) := hK.image (hnbc.mul continuous_const)
  have hmeas : ∀ y, AEStronglyMeasurable (fun β => A (c β * R.ι w y) * u β) (lam.restrict 𝓖) := by
    intro y
    have e : (fun β => A (c β * R.ι w y) * u β) = fun β => A (nb β * (x' * R.ι w y)) * u β :=
      funext fun β => by rw [key]
    rw [e]
    exact ((hAc.comp (hnbc.mul continuous_const)).mul huc).aestronglyMeasurable
  have := H.holT.2 d.n pp qq e d.G (R.ι w) (R.cont w) A hAc hA (nA σ d.Y d.b) (lam.restrict 𝓖) c u _ hC
    (fun β => ⟨_, (hγ β).2, rfl⟩) (fun β => (hψ.2.1 _).le) hmeas
  convert this using 2 with y
  simp only [fc]
  congr 1
  funext β
  rw [key]

theorem holCoef_pf (H : Hyps) {d : SD σ} (R : RD d) (L : LD d) (w : InfinitePlace F) {nb lam 𝓖}
    (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) {T : nF σ d.Y d.b}
    {T' : nF σ L.Y L.b} (hT : L.IsSub T T') (A : d.G → ℂ) (hAc : Continuous A) (hAi : ∀ γ ∈ rat2 σ d.Y, ∀ g, A (γ * g) = A g)
    (pp qq : ℕ) (e : ℤ) (hpq : pp = d.m ∧ qq = 0 ∨ pp = 0 ∧ qq = d.m) (hA : ∀ g, IsHolW pp qq e fun y => A (g * R.ι w y)) :
    (∀ τ (y : GR d.n), IsDil (Pi.single L.i₀ 1) τ y → ∀ x,
      fc d.B.ψ d.b nb lam 𝓖 A T (R.ι w y * x) = Complex.exp (τ * d.m) * fc d.B.ψ d.b nb lam 𝓖 A T x) ∧
    ∀ uM ν 𝓤, L.UData uM ν 𝓤 → ∀ u x, fc d.B.ψ d.b nb lam 𝓖 A T (uM u * x) = fc d.B.ψ d.b nb lam 𝓖 A T x := by
  have hc' := hc
  obtain ⟨hN, -, -, -⟩ := hc'
  have hr : ∀ l, betaW d R w T L.i₀ l = 0 := fun l => by
    simp [betaW, SD.cw, Matrix.map_apply, (hT.1 l).1]
  have hcol : ∀ k, betaW d R w T k L.i₀ = 0 := fun k => by
    simp [betaW, SD.cw, Matrix.map_apply, (hT.1 k).2]
  have hchar : ∀ x' : d.G, (∀ y', x' * R.ι w y' = R.ι w y' * x') → ∀ (h : Matrix (Fin d.n) (Fin d.n) ℂ) (xN y : GR d.n),
      h.IsHermitian → mR xN = nU h → fc d.B.ψ d.b nb lam 𝓖 A T (x' * R.ι w (xN * y)) =
        Complex.exp (Complex.I * (betaW d R w T * h).trace) * fc d.B.ψ d.b nb lam 𝓖 A T (x' * R.ι w y) := by
    intro x' hx' h xN y hh hxN
    obtain ⟨β₁, hι, hBw, hBu, hBf⟩ := nbw1 d R w hN xN h hxN
    rw [map_mul, ← mul_assoc, hx' xN, hι, mul_assoc, KSing.fc_shift d hc A hAi T β₁,
      character_w1_trace_exp d R w T β₁ h hh hBw hBu hBf]
  have hright : ∀ x' : d.G, (∀ y', x' * R.ι w y' = R.ι w y' * x') → ∀ (a a' : Matrix (Fin d.n) (Fin d.n) ℂ)
      (xx y : GR d.n), mR xx = Matrix.fromBlocks a 0 0 a' → aᴴ * betaW d R w T * a = betaW d R w T →
      fc d.B.ψ d.b nb lam 𝓖 A T (x' * R.ι w (xx * y)) = F0 pp qq e xx * fc d.B.ψ d.b nb lam 𝓖 A T (x' * R.ι w y) :=
    fun x' hx' => H.holT.1 d.n pp qq e _ (holPhi H R w hc T A hAc hAi pp qq e hA x') (betaW d R w T) (hchar x' hx')
  have hleft : ∀ (a a' : Matrix (Fin d.n) (Fin d.n) ℂ) (xx : GR d.n), mR xx = Matrix.fromBlocks a 0 0 a' →
      aᴴ * betaW d R w T * a = betaW d R w T →
      ∀ x, fc d.B.ψ d.b nb lam 𝓖 A T (R.ι w xx * x) = F0 pp qq e xx * fc d.B.ψ d.b nb lam 𝓖 A T x := by
    intro a a' xx hxx hs x
    obtain ⟨x', y₀, rfl, hx'⟩ := decW_pf R w x
    rw [← mul_assoc, ← hx' xx, mul_assoc, ← map_mul, hright x' hx' a a' xx y₀ hxx hs]
  refine ⟨fun τ y hy x => ?_, fun uM ν 𝓤 hu u x => ?_⟩
  · rw [hleft _ _ y hy (stab_diag L.i₀ _ (fun k hk => by simp [Pi.single_eq_of_ne hk]) _ hr hcol) x,
      weight_factor_dilation L.i₀ τ y hy]
    congr 2
    rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  · have h0 := Krd.zeta_ne R.hζ
    refine (H.uEx F E σ d R L).2 uM ν 𝓤 hu w _ (fcCont d hc T A hAc hAi)
      (fun u hu' x => (H.fcConj F E σ d L nb lam 𝓖 hc).2 uM ν 𝓤 hu T T' hT A hAc hAi u hu' x) ?_ u x
    intro u y huy x
    rw [huy]
    obtain ⟨a', ha'⟩ := hu.1 u
    set S := ∑ j, Matrix.single L.i₀ (L.em j) (u j) with hS
    have hne : ∀ j, L.em j ≠ L.i₀ := fun j => (L.rng (L.em j)).2 ⟨j, rfl⟩
    set M := d.cw w S with hMdef
    have hM : ∀ k l, k ≠ L.i₀ → M k l = 0 := by
      intro k l hk
      simp [hMdef, hS, SD.cw, Matrix.map_apply, Matrix.sum_apply, Ne.symm hk]
    have hM0 : M L.i₀ L.i₀ = 0 := by
      simp [hMdef, hS, SD.cw, Matrix.map_apply, Matrix.sum_apply, hne]
    have hmy : mR y = dZ d.n R.ζ * d.cw w (inFrame d.b (R.ι w y)) * dZ d.n R.ζ⁻¹ := by
      rw [KSplitW.cw_iota]
      simp only [← Matrix.mul_assoc, Krd.dZ_mul_inv h0, Matrix.one_mul]
      rw [Matrix.mul_assoc, Krd.dZ_mul_inv h0, Matrix.mul_one]
    rw [← huy, ha'] at hmy
    have hy : mR y = Matrix.fromBlocks (1 + M) 0 0 ((R.ζ • (1 : Matrix (Fin d.n) (Fin d.n) ℂ)) * d.cw w a' *
        (R.ζ⁻¹ • (1 : Matrix (Fin d.n) (Fin d.n) ℂ))) := by
      rw [hmy, hMdef]
      simp [dZ, SD.cw, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.map_add (f := _)]
    rw [hleft _ _ y hy (stab_row L.i₀ M hM _ hr hcol) x, weight_factor_det_one pp qq e y _ _ hy (det_row L.i₀ M hM hM0), one_mul]

end PositivityTheory.SiegelWeilFormula.AStep

end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.DegCut

section

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.AStep

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem dilEx (n : ℕ) (X : Fin n → ℝ) (τ : ℝ) : ∃ y : GR n, IsDil X τ y := dilEx_pf n X τ

section Deg

variable (H : Hyps) {d : SD σ} (R : RD d) (L : LD d) (R' : RD L.sd) (hmn : d.m < d.n) (hIH : MainV 2 R') {Φ : d.Fn}
  (hΦ : Φ ∈ d.sch) (hv : d.T Φ ∈ R.vac) {U : Set ℂ} {p : Polynomial ℂ} {Ê : ℂ → d.G → ℂ} {t : ℝ}
  (hE : EData d (d.sec0 Φ) (s0 d.m d.n) (s0 d.m d.n) U p Ê t)


include H hmn hΦ hv hE in
theorem holA (w : InfinitePlace F) (j : ℕ) (hj : j ≤ p.rootMultiplicity (s0 d.m d.n)) (hlow : ∀ i < j, ∀ g, iteratedDeriv i (Ê · g) (s0 d.m d.n) = 0) :
    ∃ (pp qq : ℕ) (e : ℤ), (pp = d.m ∧ qq = 0 ∨ pp = 0 ∧ qq = d.m) ∧
      ∀ g, IsHolW pp qq e fun y => iteratedDeriv j (Ê · (g * R.ι w y)) (s0 d.m d.n) :=
  exists_isHolW_iteratedDeriv H R hmn hΦ hv hE w j hj hlow


include H in
theorem holCoef (w : InfinitePlace F) {nb lam 𝓖} (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) {T : nF σ d.Y d.b}
    {T' : nF σ L.Y L.b} (hT : L.IsSub T T') (A : d.G → ℂ) (hAc : Continuous A) (hAi : ∀ γ ∈ rat2 σ d.Y, ∀ g, A (γ * g) = A g)
    (pp qq : ℕ) (e : ℤ) (hpq : pp = d.m ∧ qq = 0 ∨ pp = 0 ∧ qq = d.m) (hA : ∀ g, IsHolW pp qq e fun y => A (g * R.ι w y)) :
    (∀ τ (y : GR d.n), IsDil (Pi.single L.i₀ 1) τ y → ∀ x,
      fc d.B.ψ d.b nb lam 𝓖 A T (R.ι w y * x) = Complex.exp (τ * d.m) * fc d.B.ψ d.b nb lam 𝓖 A T x) ∧
    ∀ uM ν 𝓤, L.UData uM ν 𝓤 → ∀ u x, fc d.B.ψ d.b nb lam 𝓖 A T (uM u * x) = fc d.B.ψ d.b nb lam 𝓖 A T x :=
  holCoef_pf H R L w hc hT A hAc hAi pp qq e hpq hA


include H hE in
theorem avgHol {nb lam 𝓖} (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) (T : nF σ d.Y d.b) {T' : nF σ L.Y L.b}
    (hT : L.IsSub T T') {uM ν 𝓤}
    (hu : L.UData uM ν 𝓤) (x : d.G) :
    DifferentiableOn ℂ (fun z => avg d L uM ν 𝓤 nb lam 𝓖 (Ê z) T x) U ∧ ∀ i : ℕ,
      iteratedDeriv i (fun z => avg d L uM ν 𝓤 nb lam 𝓖 (Ê z) T x) (s0 d.m d.n) =
        avg d L uM ν 𝓤 nb lam 𝓖 (fun g => iteratedDeriv i (Ê · g) (s0 d.m d.n)) T x :=
  avgHol_pf H L hE hc T hT hu x


include H hIH hΦ hv in
theorem cOneVal {nb lam 𝓖} (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) {nb' lam' 𝓖'}
    (hc' : CoefData (σ := σ) (Y := L.Y) L.b nb' lam' 𝓖') {T : nF σ d.Y d.b} {T' : nF σ L.Y L.b} (hT : L.IsSub T T') (x : d.G) :
    HolValueAt (fun z => cOne d L (d.sec0 Φ) (s0 d.m d.n) z nb' lam' 𝓖' T' x) (s0 d.m d.n)
      (2 * fc d.B.ψ d.b nb lam 𝓖 (d.I Φ) T x) :=
  cOneVal_pf H R L R' hIH hΦ hv hc hc' hT x


include H hΦ in
theorem cOneLaw (w : InfinitePlace F) {nb' lam' 𝓖'} (hc' : CoefData (σ := σ) (Y := L.Y) L.b nb' lam' 𝓖') (T' : nF σ L.Y L.b)
    (τ : ℝ) (y : GR d.n) (hy : IsDil (Pi.single L.i₀ 1) τ y) (z : ℂ) (x : d.G) :
    cOne d L (d.sec0 Φ) (s0 d.m d.n) z nb' lam' 𝓖' T' (R.ι w y * x) =
      Complex.exp (τ * (2 * z + d.n)) * cOne d L (d.sec0 Φ) (s0 d.m d.n) z nb' lam' 𝓖' T' x :=
  cOneLaw_pf H R L hΦ w hc' T' τ y hy z x

end Deg

end PositivityTheory.SiegelWeilFormula.AStep

end
end
end
