module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAstepDefs
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAstepCut
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAstepCLawD
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAvacIwaC
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
import Mathlib.Tactic.Linter.HaveILetI
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
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.COneLawPf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAstepCOne
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAstepCOneC
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.CntFalse
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.DerivInv
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.IsExtAtOfDiff
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAstepHolD
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAstepFc
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.DegCut
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.ExpNeOfLt
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAstepCLawE

section

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.AStep
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem a_dil_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (i₀ : Fin d.n) (τ : ℝ) (y : GR d.n)
    (hy : IsDil (Pi.single i₀ 1) τ y) (h : d.G) : d.a (R.ι w y * h) = Real.exp (2 * τ) * d.a h ∧ 0 ≤ d.a h := by
  haveI := d.cm.1
  have hf := _root_.PositivityTheory.SiegelWeilFormula.AStep.inFrame_dil'_k R w i₀ τ y hy
  have h21 : (inFrame d.b (R.ι w y)).toBlocks₂₁ = 0 := by rw [hf, Matrix.toBlocks_fromBlocks₂₁]
  obtain ⟨t, ht, hdet⟩ := _root_.PositivityTheory.SiegelWeilFormula.Avac.isPar_of_frame_k d (R.ι w y) h21
  have hdetU : Matrix.GeneralLinearGroup.det t = Units.map (algebraMap (AF F) (AE F E)).toMonoidHom (adrU w τ) := by
    rw [← det_dilT d.cm w i₀ τ]
    apply Units.ext
    rw [hdet, hf, Matrix.toBlocks_fromBlocks₁₁]
    rfl
  refine ⟨?_, ?_⟩
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Avac.a_mul_par_k d ht h, hdetU, absE_adrU d.cm w τ]
  · obtain ⟨p, tp, hp, k, hk, rfl⟩ := d.ok.hgt.iwa h
    rw [d.ok.hgt.val p tp hp k hk]
    exact NNReal.coe_nonneg _
end PositivityTheory.SiegelWeilFormula.AStep
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAstepCLaw

section

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.AStep
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem cOneLaw_pf_k (H : _root_.PositivityTheory.SiegelWeilFormula.AStep.Hyps_k) {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) {Φ : d.Fn} (hΦ : Φ ∈ d.sch) (w : InfinitePlace F)
    {nb' lam' 𝓖'} (hc' : CoefData (σ := σ) (Y := L.Y) L.b nb' lam' 𝓖') (T' : nF σ L.Y L.b)
    (τ : ℝ) (y : GR d.n) (hy : IsDil (Pi.single L.i₀ 1) τ y) (z : ℂ) (x : d.G) :
    _root_.PositivityTheory.SiegelWeilFormula.AStep.cOne_k d L (d.sec0 Φ) (s0 d.m d.n) z nb' lam' 𝓖' T' (R.ι w y * x) =
      Complex.exp (τ * (2 * z + d.n)) * _root_.PositivityTheory.SiegelWeilFormula.AStep.cOne_k d L (d.sec0 Φ) (s0 d.m d.n) z nb' lam' 𝓖' T' x := by
  set c := Complex.exp (τ * (2 * z + d.n)) with hc
  have hterm : ∀ g : L.sd.G, ((d.Ht (L.j g * (R.ι w y * x)) : ℝ) : ℂ) ^ (z - s0 d.m d.n) * d.sec0 Φ (L.j g * (R.ι w y * x)) =
      c * (((d.Ht (L.j g * x) : ℝ) : ℂ) ^ (z - s0 d.m d.n) * d.sec0 Φ (L.j g * x)) := by
    intro g
    rw [← mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.AStep.j_comm_dil_k R L w τ y hy g, mul_assoc]
    obtain ⟨ha, h0⟩ := _root_.PositivityTheory.SiegelWeilFormula.AStep.a_dil_k R w L.i₀ τ y hy (L.j g * x)
    rw [_root_.PositivityTheory.SiegelWeilFormula.AStep.constantTerm_dilation H R w L.i₀ τ y hy hΦ]
    have e1 : ((d.Ht (R.ι w y * (L.j g * x)) : ℝ) : ℂ) = ((Real.exp (2 * τ) : ℝ) : ℂ) * ((d.a (L.j g * x) : ℝ) : ℂ) := by
      unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.Ht
      rw [Real.coe_toNNReal _ (by rw [ha]; exact mul_nonneg (Real.exp_pos _).le h0), ha, Complex.ofReal_mul]
    have e2 : ((d.Ht (L.j g * x) : ℝ) : ℂ) = ((d.a (L.j g * x) : ℝ) : ℂ) := by
      unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.Ht
      rw [Real.coe_toNNReal _ h0]
    rw [e1, e2, Complex.mul_cpow_ofReal_nonneg (Real.exp_pos _).le h0, cpow_exp, hc]
    have e3 : Complex.exp (((2 * τ : ℝ) : ℂ) * (z - s0 d.m d.n)) * Complex.exp (τ * d.m) = Complex.exp (τ * (2 * z + d.n)) := by
      rw [← Complex.exp_add]
      congr 1
      unfold s0
      push_cast
      ring
    rw [← e3]
    ring
  unfold _root_.PositivityTheory.SiegelWeilFormula.AStep.cOne_k
  have hfun : (fun g : L.sd.G => ((d.Ht (L.j g * (R.ι w y * x)) : ℝ) : ℂ) ^ (z - s0 d.m d.n) * d.sec0 Φ (L.j g * (R.ι w y * x))) =
      fun g => c * (((d.Ht (L.j g * x) : ℝ) : ℂ) ^ (z - s0 d.m d.n) * d.sec0 Φ (L.j g * x)) := funext hterm
  rw [hfun]
  have hcs : ∀ (Ψ : L.sd.G → ℂ), GlobalTheory.Eis.cosetSum (par2 σ L.Y) (rat2 σ L.Y) (fun g => c * Ψ g) =
      fun g' => c * GlobalTheory.Eis.cosetSum (par2 σ L.Y) (rat2 σ L.Y) Ψ g' := by
    intro Ψ
    funext g'
    simp only [GlobalTheory.Eis.cosetSum, GlobalTheory.Eis.term]
    exact tsum_mul_left
  rw [hcs]
  simp only [fc, mul_assoc]
  exact integral_const_mul _ _
end PositivityTheory.SiegelWeilFormula.AStep
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAstepHolA

section

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.AStep
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem T_sub_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (Φ Φ' : d.Fn) : d.T (Φ - Φ') = d.T Φ - d.T Φ' := by
  funext X
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T, Pi.sub_apply]
  rw [← map_sub]
  congr 1
  funext y
  simp [Darboux.rho, schr, mul_sub]
theorem vac_tens_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (f : Mx F E d.m d.n → ℂ) (hf : f ∈ R.vac) :
    ∃ Ψ ∈ R.away w, f = R.tens w (fP 1) Ψ := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨g, hg, rfl⟩ := hf
    refine ⟨fun X => (∏ w' ∈ Finset.univ.erase w, fP 1 (R.loc w' X)) * g fun k => (d.crd X k).2,
      Submodule.subset_span ⟨fun _ => 1, g, hg, rfl⟩, ?_⟩
    funext X
    simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens]
    rw [← mul_assoc, Finset.mul_prod_erase _ (fun w' => fP 1 (R.loc w' X)) (Finset.mem_univ w)]
  | zero => exact ⟨0, zero_mem _, by funext X; simp [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens]⟩
  | add f f' _ _ h h' =>
    obtain ⟨Ψ, hΨ, rfl⟩ := h
    obtain ⟨Ψ', hΨ', rfl⟩ := h'
    exact ⟨Ψ + Ψ', add_mem hΨ hΨ', by funext X; simp [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, mul_add]⟩
  | smul a f _ h =>
    obtain ⟨Ψ, hΨ, rfl⟩ := h
    exact ⟨a • Ψ, Submodule.smul_mem _ a hΨ, by funext X; simp [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens]; ring⟩
theorem ndA_k (H : _root_.PositivityTheory.SiegelWeilFormula.AStep.Hyps_k) {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (hmn : d.m < d.n) {Φ : d.Fn} (hΦ : Φ ∈ d.sch) (hv : d.T Φ ∈ R.vac)
    {U p Ê t} (hE : _root_.PositivityTheory.SiegelWeilFormula.AStep.EData_k d (d.sec0 Φ) (s0 d.m d.n) (s0 d.m d.n) U p Ê t) (j : ℕ) (hj : j ≤ p.rootMultiplicity (s0 d.m d.n)) :
    ∀ L ∈ d.lamSet, L (fun g => iteratedDeriv j (Ê · g) (s0 d.m d.n)) = 0 := by
  intro L hL
  have hK := H.polyKFin F E σ d R Φ hΦ ((H.vacK F E σ d R).2.1 hv)
  have hsec := H.secK F E σ d Φ hK
  have hEis := H.eisWk F E σ d _ _ hsec
  obtain ⟨hadd, hbd⟩ := H.lamBd F E σ d L hL
  obtain ⟨nb, lam, 𝓖, T, x, hc, hT, rfl⟩ := hL
  obtain ⟨hUo, hR, hs, hp, hd, hcont, hinv, hfar⟩ := hE
  obtain ⟨hDiff, hComm⟩ := lamDeriv (rat2 σ d.Y) _ hadd hbd U Ê hUo hd hcont hinv
  show fc d.B.ψ d.b nb lam 𝓖 (fun g => iteratedDeriv j (Ê · g) (s0 d.m d.n)) T x = 0
  rw [← hComm _ hs j]
  obtain ⟨t', ht'⟩ := H.unfold F E σ d _ _ hsec hEis
  obtain ⟨ε, w, hw, -⟩ := (H.auxEx F E σ d).2.1
  have hWL := H.whitLow F E σ d R hmn Φ hΦ hv nb lam 𝓖 hc ε w hw T hT x
  rw [zero_mul] at hWL
  have := ordVal U p (fun z => fc d.B.ψ d.b nb lam 𝓖 (Ê z) T x)
    (fun z => ∫ β, flat d.a (d.sec0 Φ) (s0 d.m d.n) z (w * nb β * x) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam) (max t t')
    (s0 d.m d.n) 0 hUo hR hs hp hDiff ?_ hWL j hj
  · rw [this, mul_zero]
  · intro z hz
    have h1 := (hfar z (lt_of_le_of_lt (le_max_left _ _) hz)).2
    have h2 := (ht' z (lt_of_le_of_lt (le_max_right _ _) hz) nb lam 𝓖 hc ε w hw x).2 T hT
    rw [← h2]
    simp only [fc, h1, mul_assoc]
    exact integral_const_mul _ _
theorem holA_pf_k (H : _root_.PositivityTheory.SiegelWeilFormula.AStep.Hyps_k) {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (hmn : d.m < d.n) {Φ : d.Fn} (hΦ : Φ ∈ d.sch) (hv : d.T Φ ∈ R.vac)
    {U : Set ℂ} {p : Polynomial ℂ} {Ê : ℂ → d.G → ℂ} {t : ℝ}
    (hE : _root_.PositivityTheory.SiegelWeilFormula.AStep.EData_k d (d.sec0 Φ) (s0 d.m d.n) (s0 d.m d.n) U p Ê t) (w : InfinitePlace F) (j : ℕ)
    (hj : j ≤ p.rootMultiplicity (s0 d.m d.n)) (hlow : ∀ i < j, ∀ g, iteratedDeriv i (Ê · g) (s0 d.m d.n) = 0) :
    ∃ (pp qq : ℕ) (e : ℤ), (pp = d.m ∧ qq = 0 ∨ pp = 0 ∧ qq = d.m) ∧
      ∀ g, IsHolW pp qq e fun y => iteratedDeriv j (Ê · (g * R.ι w y)) (s0 d.m d.n) := by
  obtain ⟨-, -, hTG, hLC, hT2, hSC⟩ := H.auxEx F E σ d
  have hE' := hE
  obtain ⟨hUo, hR, hs, hp, hd, hcont, hinv, hfar⟩ := hE'
  have hAc := famCont U Ê hUo hd hcont _ hs j
  have hAi : ∀ γ ∈ rat2 σ d.Y, ∀ g, iteratedDeriv j (Ê · (γ * g)) (s0 d.m d.n) = iteratedDeriv j (Ê · g) (s0 d.m d.n) :=
    fun γ hγ g => derivInv U Ê hUo _ hs γ g (fun z hz => hinv z hz γ hγ g) j
  obtain ⟨Ψ, hΨ, hTΨ⟩ := _root_.PositivityTheory.SiegelWeilFormula.AStep.vac_tens_k R w _ hv
  obtain ⟨Lop, hLop⟩ := H.locOpEx F E σ d R w
  obtain ⟨φ, hφ⟩ := H.liftEx F E σ d R w Ψ hΨ
  obtain ⟨sL, ρ, pp, qq, e, -, hLD, hsL, -⟩ := H.locInst F E σ d R w Lop hLop
  have hΦφ : φ 1 = Φ := by
    have h0 := (H.tAll.1 F E σ d).2.2 (φ 1 - Φ) (sub_mem (hφ 1).1 hΦ) (by rw [_root_.PositivityTheory.SiegelWeilFormula.AStep.T_sub_k, (hφ 1).2, hTΨ, sub_self])
    exact sub_eq_zero.1 h0
  have hpq : pp = d.m ∧ qq = 0 ∨ pp = 0 ∧ qq = d.m := by
    rcases hLD.sign with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩
    · left; rw [h1, h2, cnt_true, cnt_false]; exact ⟨rfl, rfl⟩
    · right; rw [h1, h2, cnt_true, cnt_false]; exact ⟨rfl, rfl⟩
  refine ⟨pp, qq, e, hpq, ?_⟩
  haveI := hTG; haveI := hLC; haveI := hT2; haveI := hSC
  refine H.holLead d.m d.n pp qq e d.ok.hm hmn hpq d.G (par2 σ d.Y) (rat2 σ d.Y) (R.ι w) (s0 d.m d.n) d.Ht (d.sec0 Φ)
    (R.cont w) ?_ U p Ê t hUo hR hs hd hcont (fun z hz => ⟨(hfar z hz).1, fun g => (hfar z hz).2 g⟩) j hlow ?_
  · intro g
    obtain ⟨x, y, c, r, hr, hg, hxy⟩ := H.gSplit F E σ d R w Lop hLop Ψ hΨ φ hφ g
    refine ⟨x, y, c, r, hr, hg, fun y' => ⟨(hxy y').1, ?_⟩⟩
    rw [← hΦφ, (hxy y').2 1, ← hsL, hLD.vac]
  · intro ψ hψ nb hnb g a b
    exact H.lamSing F E σ d R w _ hAc hAi (_root_.PositivityTheory.SiegelWeilFormula.AStep.ndA_k H R hmn hΦ hv hE j hj) ψ hψ nb hnb g a b
end PositivityTheory.SiegelWeilFormula.AStep
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAstepDegCut

section

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.AStep
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
section Deg
variable (H : _root_.PositivityTheory.SiegelWeilFormula.AStep.Hyps_k) {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (R' : _root_.PositivityTheory.SiegelWeilFormula.RD_k L.sd) (hmn : d.m < d.n) (hIH : _root_.PositivityTheory.SiegelWeilFormula.MainV_k 2 R') {Φ : d.Fn}
  (hΦ : Φ ∈ d.sch) (hv : d.T Φ ∈ R.vac) {U : Set ℂ} {p : Polynomial ℂ} {Ê : ℂ → d.G → ℂ} {t : ℝ}
  (hE : _root_.PositivityTheory.SiegelWeilFormula.AStep.EData_k d (d.sec0 Φ) (s0 d.m d.n) (s0 d.m d.n) U p Ê t)
include H hmn hΦ hv hE in
theorem holA_k (w : InfinitePlace F) (j : ℕ) (hj : j ≤ p.rootMultiplicity (s0 d.m d.n)) (hlow : ∀ i < j, ∀ g, iteratedDeriv i (Ê · g) (s0 d.m d.n) = 0) :
    ∃ (pp qq : ℕ) (e : ℤ), (pp = d.m ∧ qq = 0 ∨ pp = 0 ∧ qq = d.m) ∧
      ∀ g, IsHolW pp qq e fun y => iteratedDeriv j (Ê · (g * R.ι w y)) (s0 d.m d.n) :=
  _root_.PositivityTheory.SiegelWeilFormula.AStep.holA_pf_k H R hmn hΦ hv hE w j hj hlow
include H in
theorem holCoef_k (w : InfinitePlace F) {nb lam 𝓖} (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) {T : nF σ d.Y d.b}
    {T' : nF σ L.Y L.b} (hT : L.IsSub T T') (A : d.G → ℂ) (hAc : Continuous A) (hAi : ∀ γ ∈ rat2 σ d.Y, ∀ g, A (γ * g) = A g)
    (pp qq : ℕ) (e : ℤ) (hpq : pp = d.m ∧ qq = 0 ∨ pp = 0 ∧ qq = d.m) (hA : ∀ g, IsHolW pp qq e fun y => A (g * R.ι w y)) :
    (∀ τ (y : GR d.n), IsDil (Pi.single L.i₀ 1) τ y → ∀ x,
      fc d.B.ψ d.b nb lam 𝓖 A T (R.ι w y * x) = Complex.exp (τ * d.m) * fc d.B.ψ d.b nb lam 𝓖 A T x) ∧
    ∀ uM ν 𝓤, L.UData uM ν 𝓤 → ∀ u x, fc d.B.ψ d.b nb lam 𝓖 A T (uM u * x) = fc d.B.ψ d.b nb lam 𝓖 A T x :=
  _root_.PositivityTheory.SiegelWeilFormula.AStep.holCoef_pf_k H R L w hc hT A hAc hAi pp qq e hpq hA
include H hE in
theorem avgHol_k {nb lam 𝓖} (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) (T : nF σ d.Y d.b) {T' : nF σ L.Y L.b}
    (hT : L.IsSub T T') {uM ν 𝓤}
    (hu : L.UData uM ν 𝓤) (x : d.G) :
    DifferentiableOn ℂ (fun z => _root_.PositivityTheory.SiegelWeilFormula.AStep.avg_k d L uM ν 𝓤 nb lam 𝓖 (Ê z) T x) U ∧ ∀ i : ℕ,
      iteratedDeriv i (fun z => _root_.PositivityTheory.SiegelWeilFormula.AStep.avg_k d L uM ν 𝓤 nb lam 𝓖 (Ê z) T x) (s0 d.m d.n) =
        _root_.PositivityTheory.SiegelWeilFormula.AStep.avg_k d L uM ν 𝓤 nb lam 𝓖 (fun g => iteratedDeriv i (Ê · g) (s0 d.m d.n)) T x :=
  _root_.PositivityTheory.SiegelWeilFormula.AStep.avgHol_pf_k H L hE hc T hT hu x
include H hIH hΦ hv in
theorem cOneVal_k {nb lam 𝓖} (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) {nb' lam' 𝓖'}
    (hc' : CoefData (σ := σ) (Y := L.Y) L.b nb' lam' 𝓖') {T : nF σ d.Y d.b} {T' : nF σ L.Y L.b} (hT : L.IsSub T T') (x : d.G) :
    HolValueAt (fun z => _root_.PositivityTheory.SiegelWeilFormula.AStep.cOne_k d L (d.sec0 Φ) (s0 d.m d.n) z nb' lam' 𝓖' T' x) (s0 d.m d.n)
      (2 * fc d.B.ψ d.b nb lam 𝓖 (d.I Φ) T x) :=
  _root_.PositivityTheory.SiegelWeilFormula.AStep.cOneVal_pf_k H R L R' hIH hΦ hv hc hc' hT x
include H hΦ in
theorem cOneLaw_k (w : InfinitePlace F) {nb' lam' 𝓖'} (hc' : CoefData (σ := σ) (Y := L.Y) L.b nb' lam' 𝓖') (T' : nF σ L.Y L.b)
    (τ : ℝ) (y : GR d.n) (hy : IsDil (Pi.single L.i₀ 1) τ y) (z : ℂ) (x : d.G) :
    _root_.PositivityTheory.SiegelWeilFormula.AStep.cOne_k d L (d.sec0 Φ) (s0 d.m d.n) z nb' lam' 𝓖' T' (R.ι w y * x) =
      Complex.exp (τ * (2 * z + d.n)) * _root_.PositivityTheory.SiegelWeilFormula.AStep.cOne_k d L (d.sec0 Φ) (s0 d.m d.n) z nb' lam' 𝓖' T' x :=
  _root_.PositivityTheory.SiegelWeilFormula.AStep.cOneLaw_pf_k H R L hΦ w hc' T' τ y hy z x
end Deg
end PositivityTheory.SiegelWeilFormula.AStep
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAstepDeg

section

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.AStep
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem deg_k (H : _root_.PositivityTheory.SiegelWeilFormula.AStep.Hyps_k) {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (R' : _root_.PositivityTheory.SiegelWeilFormula.RD_k L.sd) (hmn : d.m < d.n) (hIH : _root_.PositivityTheory.SiegelWeilFormula.MainV_k 2 R') {Φ : d.Fn}
    (hΦ : Φ ∈ d.sch) (hv : d.T Φ ∈ R.vac) {U p Ê t} (hE : _root_.PositivityTheory.SiegelWeilFormula.AStep.EData_k d (d.sec0 Φ) (s0 d.m d.n) (s0 d.m d.n) U p Ê t) (j : ℕ)
    (hj : j ≤ p.rootMultiplicity (s0 d.m d.n)) (hlow : ∀ i < j, ∀ g, iteratedDeriv i (Ê · g) (s0 d.m d.n) = 0)
    {nb lam 𝓖} (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) {T : nF σ d.Y d.b} {T' : nF σ L.Y L.b} (hT : L.IsSub T T')
    (x : d.G) : fc d.B.ψ d.b nb lam 𝓖 (_root_.PositivityTheory.SiegelWeilFormula.AStep.Bj_k d Φ p Ê j) T x = 0 := by
  have hK := H.polyKFin F E σ d R Φ hΦ ((H.vacK F E σ d R).2.1 hv)
  have hsec := H.secK F E σ d Φ hK
  have hEis := H.eisWk F E σ d _ _ hsec
  have hE' := hE
  obtain ⟨hUo, hR, hs, hp, hd, hcont, hinv, hfar⟩ := hE'
  obtain ⟨-, -, hI⟩ := H.tAll.2.2.2.2 F E σ d
  obtain ⟨-, hIc, hIi⟩ := hI Φ hΦ
  set s := s0 d.m d.n with hsdef
  set A : d.G → ℂ := fun g => iteratedDeriv j (Ê · g) s with hAdef
  have hAc : Continuous A := famCont U Ê hUo hd hcont _ hs j
  have hAi : ∀ γ ∈ rat2 σ d.Y, ∀ g, A (γ * g) = A g :=
    fun γ hγ g => derivInv U Ê hUo _ hs γ g (fun z hz => hinv z hz γ hγ g) j
  have hB : _root_.PositivityTheory.SiegelWeilFormula.AStep.Bj_k d Φ p Ê j = (-(iteratedDeriv j (fun z => p.eval z) s * 2)) • d.I Φ + A := by
    funext g; simp only [_root_.PositivityTheory.SiegelWeilFormula.AStep.Bj_k, hAdef, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hfcB : ∀ x', fc d.B.ψ d.b nb lam 𝓖 (_root_.PositivityTheory.SiegelWeilFormula.AStep.Bj_k d Φ p Ê j) T x' =
      fc d.B.ψ d.b nb lam 𝓖 A T x' - iteratedDeriv j (fun z => p.eval z) s * (2 * fc d.B.ψ d.b nb lam 𝓖 (d.I Φ) T x') := by
    intro x'
    rw [hB, (_root_.PositivityTheory.SiegelWeilFormula.AStep.fcAll_k d hc T x').1 _ _ _ hIc hAc hIi hAi]; ring
  let w : InfinitePlace F := Classical.arbitrary _
  obtain ⟨y, hy⟩ := dilEx d.n (Pi.single L.i₀ 1) 1
  obtain ⟨pp, qq, e, hpq, hhol⟩ := _root_.PositivityTheory.SiegelWeilFormula.AStep.holA_k H R hmn hΦ hv hE w j hj hlow
  obtain ⟨hlawA, huA⟩ := _root_.PositivityTheory.SiegelWeilFormula.AStep.holCoef_k H R L w hc hT A hAc hAi pp qq e hpq hhol
  obtain ⟨uM, ν, 𝓤, hu⟩ := (H.uEx F E σ d R L).1
  obtain ⟨nb', lam', 𝓖', hc'⟩ := H.coefEx F E σ L.sd
  obtain ⟨t', hct⟩ := H.cTSplit F E σ d R L _ _ hsec hEis
  have hspl : ∀ z : ℂ, t' < z.re → ∃ c₂ : d.G → ℂ,
      (∀ x, _root_.PositivityTheory.SiegelWeilFormula.AStep.avg_k d L uM ν 𝓤 nb lam 𝓖 (d.eis (d.sec0 Φ) s z) T x = _root_.PositivityTheory.SiegelWeilFormula.AStep.cOne_k d L (d.sec0 Φ) s z nb' lam' 𝓖' T' x + c₂ x) ∧
      ∀ x, c₂ (R.ι w y * x) = Complex.exp (((1 : ℝ) : ℂ) * (d.n - 2 * z)) * c₂ x := by
    intro z hz
    obtain ⟨c₂, h1, h2⟩ := hct z hz nb lam 𝓖 hc nb' lam' 𝓖' hc' uM ν 𝓤 hu T T' hT
    exact ⟨c₂, h1, fun x => h2 w 1 y x hy⟩
  let c2 : ℂ → d.G → ℂ := fun z => if h : t' < z.re then Classical.choose (hspl z h) else 0
  have hc2 : ∀ z : ℂ, t' < z.re → (∀ x, _root_.PositivityTheory.SiegelWeilFormula.AStep.avg_k d L uM ν 𝓤 nb lam 𝓖 (d.eis (d.sec0 Φ) s z) T x =
      _root_.PositivityTheory.SiegelWeilFormula.AStep.cOne_k d L (d.sec0 Φ) s z nb' lam' 𝓖' T' x + c2 z x) ∧
      ∀ x, c2 z (R.ι w y * x) = Complex.exp (((1 : ℝ) : ℂ) * (d.n - 2 * z)) * c2 z x := by
    intro z hz
    simp only [c2, dif_pos hz]
    exact Classical.choose_spec (hspl z hz)
  have havg_smul : ∀ (c : ℂ) (φ : d.G → ℂ) x', _root_.PositivityTheory.SiegelWeilFormula.AStep.avg_k d L uM ν 𝓤 nb lam 𝓖 (fun g => c * φ g) T x' =
      c * _root_.PositivityTheory.SiegelWeilFormula.AStep.avg_k d L uM ν 𝓤 nb lam 𝓖 φ T x' := by
    intro c φ x'
    simp only [_root_.PositivityTheory.SiegelWeilFormula.AStep.avg_k, fc, mul_assoc]
    simp only [integral_const_mul]
  have hhol1 := _root_.PositivityTheory.SiegelWeilFormula.AStep.avgHol_k H L hE hc T hT hu
  have hsep := lawSep U p (max t t') s j (fun z => _root_.PositivityTheory.SiegelWeilFormula.AStep.avg_k d L uM ν 𝓤 nb lam 𝓖 (Ê z) T x)
    (fun z => _root_.PositivityTheory.SiegelWeilFormula.AStep.avg_k d L uM ν 𝓤 nb lam 𝓖 (Ê z) T (R.ι w y * x))
    (fun z => _root_.PositivityTheory.SiegelWeilFormula.AStep.cOne_k d L (d.sec0 Φ) s z nb' lam' 𝓖' T' x) (fun z => _root_.PositivityTheory.SiegelWeilFormula.AStep.cOne_k d L (d.sec0 Φ) s z nb' lam' 𝓖' T' (R.ι w y * x))
    (fun z => c2 z x) (fun z => c2 z (R.ι w y * x)) (2 * fc d.B.ψ d.b nb lam 𝓖 (d.I Φ) T x)
    (2 * fc d.B.ψ d.b nb lam 𝓖 (d.I Φ) T (R.ι w y * x)) (d.n : ℂ) (-2) hUo hR hs hp hj (hhol1 x).1 (hhol1 _).1
    (fun i hi => by
      rw [(hhol1 x).2 i]
      have : (fun g => iteratedDeriv i (Ê · g) s) = fun _ => 0 := funext fun g => hlow i hi g
      rw [this]; simp [_root_.PositivityTheory.SiegelWeilFormula.AStep.avg_k, fc])
    (fun i hi => by
      rw [(hhol1 _).2 i]
      have : (fun g => iteratedDeriv i (Ê · g) s) = fun _ => 0 := funext fun g => hlow i hi g
      rw [this]; simp [_root_.PositivityTheory.SiegelWeilFormula.AStep.avg_k, fc])
    (fun z hz => by
      have h1 := (hfar z (lt_of_le_of_lt (le_max_left _ _) hz)).2
      have e1 : Ê z = fun g => p.eval z * d.eis (d.sec0 Φ) s z g := funext h1
      rw [e1, havg_smul, (hc2 z (lt_of_le_of_lt (le_max_right _ _) hz)).1 x])
    (fun z hz => by
      have h1 := (hfar z (lt_of_le_of_lt (le_max_left _ _) hz)).2
      have e1 : Ê z = fun g => p.eval z * d.eis (d.sec0 Φ) s z g := funext h1
      rw [e1, havg_smul, (hc2 z (lt_of_le_of_lt (le_max_right _ _) hz)).1 _])
    (_root_.PositivityTheory.SiegelWeilFormula.AStep.cOneVal_k H R L R' hIH hΦ hv hc hc' hT x) (_root_.PositivityTheory.SiegelWeilFormula.AStep.cOneVal_k H R L R' hIH hΦ hv hc hc' hT _)
    (fun z hz => by
      rw [(hc2 z (lt_of_le_of_lt (le_max_right _ _) hz)).2 x]
      congr 1; push_cast; ring_nf)
  have havgA : ∀ x', iteratedDeriv j (fun z => _root_.PositivityTheory.SiegelWeilFormula.AStep.avg_k d L uM ν 𝓤 nb lam 𝓖 (Ê z) T x') s = fc d.B.ψ d.b nb lam 𝓖 A T x' := by
    intro x'
    rw [(hhol1 x').2 j]
    show _root_.PositivityTheory.SiegelWeilFormula.AStep.avg_k d L uM ν 𝓤 nb lam 𝓖 A T x' = _
    simp only [_root_.PositivityTheory.SiegelWeilFormula.AStep.avg_k, huA uM ν 𝓤 hu, setIntegral_const]
    simp [Measure.real, hu.2.2.2]
  rw [havgA, havgA] at hsep
  have hth : fc d.B.ψ d.b nb lam 𝓖 (d.I Φ) T (R.ι w y * x) = Complex.exp (d.m : ℂ) * fc d.B.ψ d.b nb lam 𝓖 (d.I Φ) T x := by
    have := valLaw (fun z => _root_.PositivityTheory.SiegelWeilFormula.AStep.cOne_k d L (d.sec0 Φ) s z nb' lam' 𝓖' T' x)
      (fun z => _root_.PositivityTheory.SiegelWeilFormula.AStep.cOne_k d L (d.sec0 Φ) s z nb' lam' 𝓖' T' (R.ι w y * x)) 0 (d.n : ℂ) 2 s _ _
      (fun z _ => by rw [_root_.PositivityTheory.SiegelWeilFormula.AStep.cOneLaw_k H R L hΦ w hc' T' 1 y hy z x]; congr 1; push_cast; ring_nf)
      (_root_.PositivityTheory.SiegelWeilFormula.AStep.cOneVal_k H R L R' hIH hΦ hv hc hc' hT x) (_root_.PositivityTheory.SiegelWeilFormula.AStep.cOneVal_k H R L R' hIH hΦ hv hc hc' hT _)
    have e2 : (d.n : ℂ) + 2 * s = d.m := by rw [hsdef, s0]; ring
    rw [e2] at this
    linear_combination this / 2
  have hA1 := hlawA 1 y hy x
  rw [Complex.ofReal_one, one_mul] at hA1
  rw [hfcB x]
  rw [hA1, hth] at hsep
  have e3 : (d.n : ℂ) + -2 * s = ((2 * d.n - d.m : ℕ) : ℂ) := by
    have h2 : ((2 * d.n - d.m : ℕ) : ℂ) = 2 * (d.n : ℂ) - d.m := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [h2, hsdef, s0]; ring
  rw [e3] at hsep
  have hne := exp_ne_of_lt hmn
  have key : (Complex.exp ((2 * d.n - d.m : ℕ) : ℂ) - Complex.exp (d.m : ℂ)) *
      (fc d.B.ψ d.b nb lam 𝓖 A T x - iteratedDeriv j (fun z => p.eval z) s * (2 * fc d.B.ψ d.b nb lam 𝓖 (d.I Φ) T x)) = 0 := by
    linear_combination -hsep
  rcases mul_eq_zero.1 key with h | h
  · exact absurd (sub_eq_zero.1 h) hne
  · exact h
end PositivityTheory.SiegelWeilFormula.AStep
end
end
end
end
