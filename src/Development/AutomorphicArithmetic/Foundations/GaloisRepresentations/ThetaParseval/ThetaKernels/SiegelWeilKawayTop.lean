module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.AdDecompK
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopCore
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AwayActions.AwStep
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKrdPlace
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
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopPlumb
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopRel
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopStepW
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKawayDecG
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AwayActions.Imports
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AwayActions.InFrameInvOf
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AwayActions.SigmaSigma
import Mathlib.Tactic.Polynomial.Basic
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKawayFinTop
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfourW

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKawayAwStep

section

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.KAway
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
theorem cw_mul_k (w : InfinitePlace F) {p q r : Type} [Fintype q] (M : Matrix p q (AE F E)) (N : Matrix q r (AE F E)) :
    d.cw w (M * N) = d.cw w M * d.cw w N := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw]
  exact Matrix.map_mul
theorem cw_one_k (w : InfinitePlace F) {p : Type} [DecidableEq p] : d.cw w (1 : Matrix p p (AE F E)) = 1 := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw]
  exact Matrix.map_one _ (map_zero _) (map_one _)
theorem cw_transpose_k (w : InfinitePlace F) {p q : Type} (M : Matrix p q (AE F E)) : d.cw w Mᵀ = (d.cw w M)ᵀ := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, Matrix.transpose_map]
theorem cw_eW_self_k (w : InfinitePlace F) {p q : Type} (M : Matrix p q (AE F E)) : d.cw w (eW w • M) = d.cw w M := by
  ext i j
  simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, piInf_eW]
theorem cw_eW_ne_k {w w' : InfinitePlace F} (h : w' ≠ w) {p q : Type} (M : Matrix p q (AE F E)) : d.cw w' (eW w • M) = 0 := by
  ext i j
  simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, piInf_eW, h]
theorem eW_smul_eq_iff_k (w : InfinitePlace F) {p q : Type} (M M' : Matrix p q (AE F E)) :
    eW w • M = eW w • M' ↔ d.cw w M = d.cw w M' := by
  constructor
  · intro h
    rw [← _root_.PositivityTheory.SiegelWeilFormula.KAway.cw_eW_self_k d w M, h, _root_.PositivityTheory.SiegelWeilFormula.KAway.cw_eW_self_k]
  · intro h
    apply _root_.PositivityTheory.SiegelWeilFormula.Place.cw_ext_k d
    · intro w'
      by_cases hw : w' = w
      · subst hw
        rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.cw_eW_self_k, _root_.PositivityTheory.SiegelWeilFormula.KAway.cw_eW_self_k, h]
      · rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.cw_eW_ne_k d hw, _root_.PositivityTheory.SiegelWeilFormula.KAway.cw_eW_ne_k d hw]
    · rw [finOne_eW_smul, finOne_eW_smul]
theorem eW_smul_of_supp_k {w : InfinitePlace F} {p q : Type} {Z : Matrix p q (AE F E)}
    (hZ : ∀ w', w' ≠ w → d.cw w' Z = 0) (hf : finOne F • Z = 0) : eW w • Z = Z := by
  apply _root_.PositivityTheory.SiegelWeilFormula.Place.cw_ext_k d
  · intro w'
    by_cases hw : w' = w
    · subst hw
      rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.cw_eW_self_k]
    · rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.cw_eW_ne_k d hw, hZ w' hw]
  · rw [finOne_eW_smul, hf]
theorem gram_smul_right_k (a : AF F) (X Z : Mx F E d.m d.n) : d.gram X (a • Z) = a • d.gram X Z := by
  have : (a • Z).map (cA σ) = a • Z.map (cA σ) := by
    ext i j
    simp [map_smul]
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.gram, this, Matrix.mul_smul]
theorem gram_smul_left_k (a : AF F) (X Z : Mx F E d.m d.n) : d.gram (a • X) Z = a • d.gram X Z := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.gram, Matrix.transpose_smul, Matrix.smul_mul]
theorem gram_add_k (X Z : Mx F E d.m d.n) :
    d.gram (X + Z) (X + Z) = d.gram X X + (d.gram X Z + d.gram Z X + d.gram Z Z) := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.gram, Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add, Matrix.map_add _ (map_add _)]
  abel
theorem cw_eq_one_of_k (w : InfinitePlace F) {M : Mx F E d.n d.n} (h : eW w • M = eW w • (1 : Mx F E d.n d.n)) :
    d.cw w M = 1 := by
  rw [(_root_.PositivityTheory.SiegelWeilFormula.KAway.eW_smul_eq_iff_k d w M 1).1 h, _root_.PositivityTheory.SiegelWeilFormula.KAway.cw_one_k]
namespace Step
variable {d} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F)
theorem stepN_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (x : d.G) (β : Mx F E d.n d.n) (hx : inFrame d.b x = Matrix.fromBlocks 1 β 0 1)
    (hβ : eW w • β = 0) :
    R.StepOK w x id (fun Ψ X => d.B.ψ (-(⅟(2 : AF F) * d.tt (β * d.gram X X))) * Ψ X) := by
  have hP := hT.2.1 F E σ d
  refine ⟨fun f hf => hf, fun Ψ hΨ => ⟨?_, fun f hf Φ hΦ hTΦ => ?_⟩⟩
  · intro X Z hZ hf
    have hZe : eW w • Z = Z := _root_.PositivityTheory.SiegelWeilFormula.KAway.eW_smul_of_supp_k d hZ hf
    have h1 : d.gram X Z = eW w • d.gram X Z := by
      calc d.gram X Z = d.gram X (eW w • Z) := by rw [hZe]
        _ = _ := _root_.PositivityTheory.SiegelWeilFormula.KAway.gram_smul_right_k d _ X Z
    have h2 : d.gram Z X = eW w • d.gram Z X := by
      calc d.gram Z X = d.gram (eW w • Z) X := by rw [hZe]
        _ = _ := _root_.PositivityTheory.SiegelWeilFormula.KAway.gram_smul_left_k d _ Z X
    have h3 : d.gram Z Z = eW w • d.gram Z Z := by
      calc d.gram Z Z = d.gram (eW w • Z) Z := by rw [hZe]
        _ = _ := _root_.PositivityTheory.SiegelWeilFormula.KAway.gram_smul_left_k d _ Z Z
    have key : β * d.gram (X + Z) (X + Z) = β * d.gram X X := by
      rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.gram_add_k, h1, h2, h3, ← smul_add, ← smul_add, Matrix.mul_add, Matrix.mul_smul, ← Matrix.smul_mul, hβ,
        Matrix.zero_mul, add_zero]
    simp only
    rw [key, hΨ X Z hZ hf]
  · funext X
    rw [(hP Φ hΦ).1 x β hx X, hTΦ]
    simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, id]
    ring
theorem stepM_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (x : d.G) (a a' : GL (Fin d.n) (AE F E))
    (hx : inFrame d.b x = Matrix.fromBlocks a.1 0 0 a'.1) (ha : eW w • a'.1 = eW w • (1 : Mx F E d.n d.n)) :
    R.StepOK w x id (fun Ψ X => (d.χ (Matrix.GeneralLinearGroup.det a) : ℂ) *
      (((absE F E (Matrix.GeneralLinearGroup.det a) : ℝ) ^ ((d.m : ℝ) / 2) : ℝ) : ℂ) * Ψ (X * (a'⁻¹).1ᵀ)) := by
  have hP := hT.2.1 F E σ d
  have hc : d.cw w (a'⁻¹).1 = 1 := by
    have h1 : d.cw w a'.1 = 1 := _root_.PositivityTheory.SiegelWeilFormula.KAway.cw_eq_one_of_k d w ha
    have h2 : d.cw w ((a'⁻¹).1 * a'.1) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one, _root_.PositivityTheory.SiegelWeilFormula.KAway.cw_one_k]
    rwa [_root_.PositivityTheory.SiegelWeilFormula.KAway.cw_mul_k, h1, Matrix.mul_one] at h2
  refine ⟨fun f hf => hf, fun Ψ hΨ => ⟨?_, fun f hf Φ hΦ hTΦ => ?_⟩⟩
  · intro X Z hZ hf
    simp only
    rw [Matrix.add_mul, hΨ (X * (a'⁻¹).1ᵀ) (Z * (a'⁻¹).1ᵀ) (fun w' hw' => by rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.cw_mul_k, hZ w' hw', Matrix.zero_mul])
      (by rw [← Matrix.smul_mul, hf, Matrix.zero_mul])]
  · funext X
    rw [(hP Φ hΦ).2.1 x a a' hx X, hTΦ]
    have hl : R.loc w (X * (a'⁻¹).1ᵀ) = R.loc w X := by
      unfold _root_.PositivityTheory.SiegelWeilFormula.RD_k.loc
      rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.cw_mul_k, _root_.PositivityTheory.SiegelWeilFormula.KAway.cw_transpose_k, hc, Matrix.transpose_one, Matrix.mul_one]
    simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, id, hl]
    ring
end Step
end PositivityTheory.SiegelWeilFormula.KAway
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKawayAw

section

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.KAway
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace Step
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F)
theorem away_smul_k {Ψ : d.MF} (hΨ : d.IsAwayW w Ψ) (c : ℂ) : d.IsAwayW w (c • Ψ) := by
  intro X Z hZ hf
  simp only [Pi.smul_apply, hΨ X Z hZ hf]
theorem away_zero_k : d.IsAwayW w (0 : d.MF) := fun _ _ _ _ => rfl
theorem tens_key_k {f g : d.LF} {Ψ Ψ' : d.MF} (hΨ : d.IsAwayW w Ψ) (hΨ' : d.IsAwayW w Ψ')
    (h : R.tens w f Ψ = R.tens w g Ψ') : ∀ u X, f u * Ψ X = g u * Ψ' X := by
  intro u X
  obtain ⟨Z, hZ1, hZ2, hZ3⟩ := R.loc_surj w X u
  have := congrFun h (X + Z)
  simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, hZ3, hΨ X Z hZ1 hZ2, hΨ' X Z hZ1 hZ2] at this
  exact this
theorem away_conj_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) {x₁ x₂ x' : d.G} {A₁ A₂ : d.LF → d.LF} {B₁ B₂ B' : d.MF → d.MF}
    (h₁ : R.StepOK w x₁ A₁ B₁) (h₂ : R.StepOK w x₂ A₂ B₂) (h' : R.StepOK w x' id B') (h1 : x₁ * x₂ = 1) :
    ∃ B, R.StepOK w (x₁ * x' * x₂) id B := by
  have hsch := d.om_sch
  have hc := R.step_comp w hsch (R.step_comp w hsch h₁ h') h₂
  have h0 := R.step_comp w hsch h₁ h₂
  refine ⟨fun Ψ => if h : ∃ X₀, Ψ X₀ ≠ 0 ∧ B₁ (B₂ Ψ) X₀ ≠ 0 then
      (Ψ h.choose / B₁ (B₂ Ψ) h.choose) • B₁ (B' (B₂ Ψ)) else 0,
    fun f hf => hf, fun Ψ hΨ => ⟨?_, fun f hf Φ hΦ hTΦ => ?_⟩⟩
  · dsimp only
    split_ifs with h
    · exact _root_.PositivityTheory.SiegelWeilFormula.KAway.Step.away_smul_k w (hc.2 Ψ hΨ).1 _
    · exact _root_.PositivityTheory.SiegelWeilFormula.KAway.Step.away_zero_k w
  · have e := (hc.2 Ψ hΨ).2 f hf Φ hΦ hTΦ
    have e0 := (h0.2 Ψ hΨ).2 f hf Φ hΦ hTΦ
    rw [h1, map_one, Module.End.one_apply, hTΦ] at e0
    have key : ∀ u X, f u * Ψ X = A₁ (A₂ f) u * B₁ (B₂ Ψ) X := _root_.PositivityTheory.SiegelWeilFormula.KAway.Step.tens_key_k R w hΨ (h0.2 Ψ hΨ).1 e0
    by_cases hz : (∀ u, f u = 0) ∨ ∀ X, Ψ X = 0
    · have hΦ0 : Φ = 0 := d.T_inj hT Φ hΦ (by
        rw [hTΦ]
        funext X
        rcases hz with hz | hz <;> simp [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, hz])
      subst hΦ0
      rw [map_zero, d.T_zero]
      funext X
      rcases hz with hz | hz
      · simp [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, hz]
      · have hn : ¬ ∃ X₀, Ψ X₀ ≠ 0 ∧ B₁ (B₂ Ψ) X₀ ≠ 0 := fun ⟨X₀, h, _⟩ => h (hz X₀)
        simp [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, dif_neg hn]
    · push_neg at hz
      obtain ⟨⟨u₀, hu₀⟩, ⟨X₁, hX₁⟩⟩ := hz
      have hex : ∃ X₀, Ψ X₀ ≠ 0 ∧ B₁ (B₂ Ψ) X₀ ≠ 0 := by
        refine ⟨X₁, hX₁, fun h0' => ?_⟩
        have := key u₀ X₁
        rw [h0', mul_zero] at this
        exact mul_ne_zero hu₀ hX₁ this
      have hB0 := hex.choose_spec.2
      have hA : ∀ u, A₁ (A₂ f) u = f u * (Ψ hex.choose / B₁ (B₂ Ψ) hex.choose) := by
        intro u
        have := key u hex.choose
        rw [mul_div_assoc', eq_div_iff hB0]
        linear_combination -this
      rw [e]
      funext X
      simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, Function.comp_apply, id_eq, dif_pos hex, Pi.smul_apply, smul_eq_mul, hA]
      ring
end Step
theorem awayAct_of_k : _root_.PositivityTheory.SiegelWeilFormula.TAll_k → _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties → _root_.PositivityTheory.SiegelWeilFormula.AdDecomp_k → _root_.PositivityTheory.SiegelWeilFormula.AwayAct_k := by
  intro hT hA hD F E _ _ _ _ _ σ d R w x hx
  have hsch := d.om_sch
  obtain ⟨-, ⟨ε, w₀, hw₀, -⟩, -⟩ := hA F E σ d
  have he : eW w • inFrame d.b x = eW w • (1 : Matrix _ _ (AE F E)) :=
    (_root_.PositivityTheory.SiegelWeilFormula.KAway.eW_smul_eq_iff_k d w _ _).2 (by rw [hx, _root_.PositivityTheory.SiegelWeilFormula.KAway.cw_one_k])
  obtain ⟨x₁, x₂, x₃, x₄, t, c, b, a, a', hxe, h1, h2, h3, h4, ht, hc, hb, -, ha'⟩ :=
    hD F E σ d ε w₀ hw₀ (eW w) (eW_mul_self w) x he
  obtain ⟨C, s, BW, -, hW⟩ := R.stepW w hT hA ε w₀ hw₀
  have hW3 := R.step_comp w hsch (R.step_comp w hsch hW hW) hW
  have h4' : w₀ * (w₀ * w₀ * w₀) = 1 := by
    simpa only [mul_assoc] using _root_.PositivityTheory.SiegelWeilFormula.RD_k.w_four hw₀
  obtain ⟨BC, hC⟩ := _root_.PositivityTheory.SiegelWeilFormula.KAway.Step.away_conj_k R w hT hW hW3 (_root_.PositivityTheory.SiegelWeilFormula.KAway.Step.stepN_k R w hT x₂ c h2 hc) h4'
  have hinv : w₀⁻¹ = w₀ * w₀ * w₀ := (eq_inv_of_mul_eq_one_left (_root_.PositivityTheory.SiegelWeilFormula.RD_k.w_four hw₀)).symm
  have hall := R.step_comp w hsch (R.step_comp w hsch (R.step_comp w hsch (_root_.PositivityTheory.SiegelWeilFormula.KAway.Step.stepN_k R w hT x₁ t h1 ht) hC)
    (_root_.PositivityTheory.SiegelWeilFormula.KAway.Step.stepM_k R w hT x₃ a a' h3 ha')) (_root_.PositivityTheory.SiegelWeilFormula.KAway.Step.stepN_k R w hT x₄ b h4 hb)
  rw [hxe, hinv]
  exact ⟨_, fun Ψ hΨ => ⟨(hall.2 Ψ hΨ).1, fun f hf Φ hΦ hTΦ => (hall.2 Ψ hΨ).2 f hf Φ hΦ hTΦ⟩⟩
end PositivityTheory.SiegelWeilFormula.KAway
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKawayDec

section

@[expose] public section



section
noncomputable section
open scoped TensorProduct Matrix
open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
namespace PositivityTheory.SiegelWeilFormula.KAway
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem inFrame_inv_of_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (x : d.G) (N : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E))
    (h : inFrame d.b x * N = 1) : inFrame d.b x⁻¹ = N := by
  calc inFrame d.b x⁻¹ = inFrame d.b x⁻¹ * (inFrame d.b x * N) := by rw [h, Matrix.mul_one]
    _ = N := by rw [← Matrix.mul_assoc, ← _root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_mul_k, inv_mul_cancel, _root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_one_k, Matrix.one_mul]
theorem adDecomp_k : _root_.PositivityTheory.SiegelWeilFormula.AdDecomp_k := by
  intro F E _ _ _ _ _ σ d ε w hw e he x hx
  obtain ⟨ε₀, hε₀⟩ := d.ok.frame.1
  have hcm : IsCMExt F E σ := d.ok.good.cm
  set X := inFrame d.b x with hXdef
  set A := X.toBlocks₁₁ with hA
  set B := X.toBlocks₁₂ with hB
  set C := X.toBlocks₂₁ with hC
  set D := X.toBlocks₂₂ with hD
  have hXb : X = fromBlocks A B C D := (fromBlocks_toBlocks X).symm
  have heA : e • A = e • (1 : Matrix (Fin d.n) (Fin d.n) (AE F E)) := by
    rw [hA, ← smul_toBlocks₁₁, hx, smul_toBlocks₁₁, one_toBlocks₁₁]
  have heB : e • B = 0 := by
    rw [hB, ← smul_toBlocks₁₂, hx, smul_toBlocks₁₂, one_toBlocks₁₂, smul_zero]
  have heC : e • C = 0 := by
    rw [hC, ← smul_toBlocks₂₁, hx, smul_toBlocks₂₁, one_toBlocks₂₁, smul_zero]
  have heD : e • D = e • (1 : Matrix (Fin d.n) (Fin d.n) (AE F E)) := by
    rw [hD, ← smul_toBlocks₂₂, hx, smul_toBlocks₂₂, one_toBlocks₂₂]
  have hε₀2 : (ε₀ : ℤ) * (ε₀ : ℤ) = 1 := by rw [← Units.val_mul, Int.units_mul_self, Units.val_one]
  obtain ⟨t, ht, het, hunit⟩ := free_etale_sheaf_zmod_exists_hom_sending_generator hcm (ε₀ : ℤ) hε₀2 X (_root_.PositivityTheory.SiegelWeilFormula.KAway.isUnit_det_inFrame_k d x) e he heA
  obtain ⟨x₁, hx₁⟩ := _root_.PositivityTheory.SiegelWeilFormula.KAway.exists_of_inU_k hε₀ (nM t) ((nM_cond_iff (cA σ).toRingHom (ε₀ : ℤ) t).2 ht)
  have hx₁i : inFrame d.b x₁⁻¹ = nM (-t) := _root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_inv_of_k d x₁ _ (by
    rw [hx₁, nM, nM, fromBlocks_multiply]; simp [fromBlocks_one])
  set A' := A - t * C with hA'
  set B' := B - t * D with hB'
  have hY : inFrame d.b (x₁⁻¹ * x) = fromBlocks A' B' C D := by
    rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_mul_k, hx₁i, ← hXdef, hXb, nM, fromBlocks_multiply]
    simp [hA', hB', sub_eq_add_neg]
  have h11 := upper_block_rank_one_update (cA σ).toRingHom (ε₀ : ℤ) _ (_root_.PositivityTheory.SiegelWeilFormula.KAway.inU_inFrame_k hε₀ (x₁⁻¹ * x))
  rw [hY, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₂₁] at h11
  have hA'u : IsUnit A'.det := hunit
  set c₀ := C * A'⁻¹ with hc₀
  set c := ((ε : ℤ) : AE F E) • c₀ with hcdef
  have hcc := cond_c (cA σ).toRingHom (ε₀ : ℤ) A' C hA'u hε₀2 h11 (ε : ℤ)
  obtain ⟨x₂, hx₂⟩ := _root_.PositivityTheory.SiegelWeilFormula.KAway.exists_of_inU_k hε₀ (nM c) ((nM_cond_iff (cA σ).toRingHom (ε₀ : ℤ) c).2 hcc)
  have hεε : ((ε : ℤ) : AE F E) * ((ε : ℤ) : AE F E) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have hwi : inFrame d.b w⁻¹ = fromBlocks 0 (((ε : ℤ) : AE F E) • 1) 1 0 := _root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_inv_of_k d w _ (by
    rw [hw, fromBlocks_multiply]; simp [smul_smul, hεε, fromBlocks_one])
  have hL : inFrame d.b (w * x₂ * w⁻¹) = fromBlocks 1 0 c₀ 1 := by
    rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_mul_k, _root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_mul_k, hw, hx₂, hwi, nM, fromBlocks_multiply, fromBlocks_multiply]
    simp [hcdef, smul_smul, hεε]
  have hLi : inFrame d.b (w * x₂ * w⁻¹)⁻¹ = fromBlocks 1 0 (-c₀) 1 := _root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_inv_of_k d _ _ (by
    rw [hL, fromBlocks_multiply]; simp [fromBlocks_one])
  have hcA : c₀ * A' = C := by rw [hc₀, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hA'u, Matrix.mul_one]
  have hZ : inFrame d.b ((w * x₂ * w⁻¹)⁻¹ * (x₁⁻¹ * x)) = fromBlocks A' B' 0 (D - c₀ * B') := by
    rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_mul_k, hLi, hY, fromBlocks_multiply]
    simp [hcA, sub_eq_add_neg, add_comm]
  obtain ⟨hz1, hz2⟩ := blkUpper (cA σ).toRingHom (ε₀ : ℤ) A' B' (D - c₀ * B') (by rw [← hZ]; exact _root_.PositivityTheory.SiegelWeilFormula.KAway.inU_inFrame_k hε₀ _)
  have hbb := cond_b (cA σ).toRingHom (ε₀ : ℤ) (cA_cA hcm) A' B' (D - c₀ * B') hA'u hz1 hz2
  obtain ⟨x₄, hx₄⟩ := _root_.PositivityTheory.SiegelWeilFormula.KAway.exists_of_inU_k hε₀ (nM (A'⁻¹ * B')) ((nM_cond_iff (cA σ).toRingHom (ε₀ : ℤ) _).2 hbb)
  have hx₄i : inFrame d.b x₄⁻¹ = nM (-(A'⁻¹ * B')) := _root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_inv_of_k d x₄ _ (by
    rw [hx₄, nM, nM, fromBlocks_multiply]; simp [fromBlocks_one])
  have hx₃ : inFrame d.b ((w * x₂ * w⁻¹)⁻¹ * (x₁⁻¹ * x) * x₄⁻¹) = fromBlocks A' 0 0 (D - c₀ * B') := by
    rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_mul_k, hZ, hx₄i, nM, fromBlocks_multiply]
    simp [Matrix.mul_nonsing_inv_cancel_left _ _ hA'u]
  have hdet := _root_.PositivityTheory.SiegelWeilFormula.KAway.isUnit_det_inFrame_k d ((w * x₂ * w⁻¹)⁻¹ * (x₁⁻¹ * x) * x₄⁻¹)
  rw [hx₃, det_fromBlocks_zero₁₂] at hdet
  have hDu : IsUnit (D - c₀ * B').det := isUnit_of_mul_isUnit_right hdet
  have heB' : e • B' = 0 := by rw [hB', smul_sub, ← Matrix.smul_mul, het, Matrix.zero_mul, heB, sub_zero]
  refine ⟨x₁, x₂, (w * x₂ * w⁻¹)⁻¹ * (x₁⁻¹ * x) * x₄⁻¹, x₄, t, c, A'⁻¹ * B', nonsingInvUnit A' hA'u,
    nonsingInvUnit (D - c₀ * B') hDu, by group, hx₁, hx₂, hx₃, hx₄, het, ?_, ?_, ?_, ?_⟩
  · rw [hcdef, smul_comm, hc₀, ← Matrix.smul_mul, heC, Matrix.zero_mul, smul_zero]
  · rw [← Matrix.mul_smul, heB', Matrix.mul_zero]
  · change e • (A - t * C) = _
    rw [smul_sub, ← Matrix.smul_mul, het, Matrix.zero_mul, sub_zero, heA]
  · change e • (D - c₀ * B') = _
    rw [smul_sub, ← Matrix.mul_smul, heB', Matrix.mul_zero, sub_zero, heD]
end PositivityTheory.SiegelWeilFormula.KAway
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKawayTop

section

@[expose] public section



section
namespace PositivityTheory.SiegelWeilFormula.KAway
theorem awayAct_of_tAll_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) : _root_.PositivityTheory.SiegelWeilFormula.AwayAct_k :=
  _root_.PositivityTheory.SiegelWeilFormula.KAway.awayAct_of_k hT _root_.PositivityTheory.SiegelWeilFormula.kfour.auxiliaryExistence_holds _root_.PositivityTheory.SiegelWeilFormula.KAway.adDecomp_k
theorem finAct_of_tAll_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) : _root_.PositivityTheory.SiegelWeilFormula.FinAct_k :=
  _root_.PositivityTheory.SiegelWeilFormula.KAway.finAct_of_k hT _root_.PositivityTheory.SiegelWeilFormula.kfour.auxiliaryExistence_holds _root_.PositivityTheory.SiegelWeilFormula.KAway.adDecomp_k
end PositivityTheory.SiegelWeilFormula.KAway
end
end
end
