module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKawayFinBase
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.AdDecompK
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.VolumeIsAddHaar
public import Development.WeilBound.ThetaLifts.SmallCones.IdeleTop
import Mathlib.Tactic.Linter.HaveILetI
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.DoubledGroupTopologicalProperties
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfockArch
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopPlumb
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopRelPf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AwayActions.FinTop

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKawayFinSteps

section

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.KAway
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace SDf
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
theorem stepN_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (x : d.G) (β : Mx F E d.n d.n) (hx : inFrame d.b x = Matrix.fromBlocks 1 β 0 1)
    (hβ : eInf F • β = 0) :
    _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.StepF_k d x id (fun G X => d.B.ψ (-(⅟(2 : AF F) * d.tt (β * d.gram X X))) * G X) := by
  have hβ' : β = finOne F • β := by
    conv_lhs => rw [← smul_split β, hβ, zero_add]
  have hβM : ∀ M : Mx F E d.n d.n, finOne F • M = 0 → β * M = 0 := fun M hM => by
    rw [hβ', Matrix.smul_mul, ← Matrix.mul_smul, hM, Matrix.mul_zero]
  refine ⟨fun f hf => hf, fun G hG => ⟨?_, fun f hf Φ hΦ hTΦ => ?_⟩⟩
  · intro X Z hZ
    show d.B.ψ (-(⅟(2 : AF F) * d.tt (β * d.gram (X + Z) (X + Z)))) * G (X + Z) =
      d.B.ψ (-(⅟(2 : AF F) * d.tt (β * d.gram X X))) * G X
    rw [hG X Z hZ]
    have e : β * d.gram (X + Z) (X + Z) = β * d.gram X X := by
      rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.gram_add_left_k, _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.gram_add_right_k, _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.gram_add_right_k, Matrix.mul_add, Matrix.mul_add, Matrix.mul_add,
        hβM (d.gram X Z) (by rw [← _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.gram_smul_right_k, hZ]; simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.gram]),
        hβM (d.gram Z X) (by rw [← _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.gram_smul_left_k, hZ]; simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.gram]),
        hβM (d.gram Z Z) (by rw [← _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.gram_smul_left_k, hZ]; simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.gram])]
      simp
    rw [e]
  · funext X
    rw [((hT.2.1 F E σ d) Φ hΦ).1 x β hx X, hTΦ]
    simp only [id]
    ring
theorem stepM_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (x : d.G) (a a' : GL (Fin d.n) (AE F E))
    (hx : inFrame d.b x = Matrix.fromBlocks a.1 0 0 a'.1) (ha : eInf F • a'.1 = eInf F • (1 : Mx F E d.n d.n)) :
    ∃ B, _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.StepF_k d x id B := by
  set M : Mx F E d.n d.n := (a'⁻¹).1 with hM
  have hMe : eInf F • M = eInf F • (1 : Mx F E d.n d.n) := by
    have h1 : a'.1 * M = 1 := by rw [hM, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc eInf F • M = (eInf F • (1 : Mx F E d.n d.n)) * M := by rw [Matrix.smul_mul, Matrix.one_mul]
      _ = (eInf F • a'.1) * M := by rw [ha]
      _ = eInf F • (1 : Mx F E d.n d.n) := by rw [Matrix.smul_mul, h1]
  refine ⟨fun G X => (d.χ (Matrix.GeneralLinearGroup.det a) : ℂ) *
      (((absE F E (Matrix.GeneralLinearGroup.det a) : ℝ) ^ ((d.m : ℝ) / 2) : ℝ) : ℂ) * G (X * Mᵀ),
    fun f hf => hf, fun G hG => ⟨?_, fun f hf Φ hΦ hTΦ => ?_⟩⟩
  · intro X Z hZ
    show _ * G ((X + Z) * Mᵀ) = _ * G (X * Mᵀ)
    rw [Matrix.add_mul, hG _ _ (by rw [← Matrix.smul_mul, hZ, Matrix.zero_mul])]
  · funext X
    rw [((hT.2.1 F E σ d) Φ hΦ).2.1 x a a' hx X, hTΦ]
    have hf' : f (X * Mᵀ) = f X := by
      have e : X * Mᵀ = X + X * (M - 1)ᵀ := by
        rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.mul_sub, Matrix.mul_one]
        abel
      rw [e]
      refine hf X _ ((_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.cw_zero_iff_k d _).2 ?_)
      rw [← Matrix.mul_smul, Matrix.transpose_sub, smul_sub, ← Matrix.transpose_smul, ← Matrix.transpose_smul, hMe,
        sub_self, Matrix.mul_zero]
    beta_reduce
    rw [hf']
    simp only [id]
    ring
end SDf
end PositivityTheory.SiegelWeilFormula.KAway
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKawayFinW

section

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KAway
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace SDf
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
theorem stepW_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (ε : ℤˣ) (w : d.G) (hw : d.IsW ε w) : ∃ A B, _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.StepF_k d w A B := by
  obtain ⟨⟨ν, hν⟩, -, -⟩ := hA F E σ d
  have := hν.1
  obtain ⟨i1, i2, i3, i4⟩ := (PositivityTheory.ThKCT.ideleTop F E).1
  haveI : BorelSpace (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalAddGroup (Mx F E d.m d.n) := inferInstanceAs (IsTopologicalAddGroup (Fin d.m → Fin d.n → AE F E))
  haveI : LocallyCompactSpace (Mx F E d.m d.n) := inferInstanceAs (LocallyCompactSpace (Fin d.m → Fin d.n → AE F E))
  haveI : SecondCountableTopology (Mx F E d.m d.n) :=
    inferInstanceAs (SecondCountableTopology (Fin d.m → Fin d.n → AE F E))
  haveI : BorelSpace (Mx F E d.m d.n) := inferInstanceAs (BorelSpace (Fin d.m → Fin d.n → AE F E))
  have hsm : ∀ c : AF F, Continuous fun Z : Mx F E d.m d.n => c • Z := fun c =>
    continuous_pi fun i => continuous_pi fun j =>
      Continuous.fun_smul (f := fun _ : Mx F E d.m d.n => c) (g := fun Z : Mx F E d.m d.n => Z i j) continuous_const
        ((continuous_apply j).comp (continuous_apply i))
  let VI : AddSubgroup (Mx F E d.m d.n) :=
    { carrier := {Z | finOne F • Z = 0}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at *
        rw [smul_add, ha, hb, add_zero]
      zero_mem' := by simp
      neg_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at *
        rw [smul_neg, ha, neg_zero] }
  let VF : AddSubgroup (Mx F E d.m d.n) :=
    { carrier := {Z | eInf F • Z = 0}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at *
        rw [smul_add, ha, hb, add_zero]
      zero_mem' := by simp
      neg_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at *
        rw [smul_neg, ha, neg_zero] }
  have hVI : IsClosed ((VI : AddSubgroup (Mx F E d.m d.n)) : Set (Mx F E d.m d.n)) :=
    isClosed_eq (hsm (finOne F)) continuous_const
  have hVF : IsClosed ((VF : AddSubgroup (Mx F E d.m d.n)) : Set (Mx F E d.m d.n)) :=
    isClosed_eq (hsm (eInf F)) continuous_const
  haveI : LocallyCompactSpace VI := hVI.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : LocallyCompactSpace VF := hVF.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology VI :=
    TopologicalSpace.Subtype.secondCountableTopology ((VI : AddSubgroup (Mx F E d.m d.n)) : Set (Mx F E d.m d.n))
  haveI : SecondCountableTopology VF :=
    TopologicalSpace.Subtype.secondCountableTopology ((VF : AddSubgroup (Mx F E d.m d.n)) : Set (Mx F E d.m d.n))
  haveI : BorelSpace VI := Subtype.borelSpace (fun x' => x' ∈ ((VI : AddSubgroup (Mx F E d.m d.n)) : Set (Mx F E d.m d.n)))
  haveI : BorelSpace VF := Subtype.borelSpace (fun x' => x' ∈ ((VF : AddSubgroup (Mx F E d.m d.n)) : Set (Mx F E d.m d.n)))
  have h₁ : ∀ Z : Mx F E d.m d.n, eInf F • Z ∈ VI := fun Z => by
    show finOne F • eInf F • Z = 0
    rw [smul_smul, finOne_mul_eInf, zero_smul]
  have h₂ : ∀ Z : Mx F E d.m d.n, finOne F • Z ∈ VF := fun Z => by
    show eInf F • finOne F • Z = 0
    rw [smul_smul, eInf_mul_finOne, zero_smul]
  let Φs : VI × VF ≃ₜ+ Mx F E d.m d.n :=
    { toFun := fun p => p.1.1 + p.2.1
      invFun := fun Z => (⟨eInf F • Z, h₁ Z⟩, ⟨finOne F • Z, h₂ Z⟩)
      left_inv := fun p => by
        obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := p
        have ha' : finOne F • a = 0 := ha
        have hb' : eInf F • b = 0 := hb
        have ea : eInf F • a = a := by
          conv_rhs => rw [← smul_split a]
          rw [ha', add_zero]
        have eb : finOne F • b = b := by
          conv_rhs => rw [← smul_split b]
          rw [hb', zero_add]
        refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
        · show eInf F • (a + b) = a
          rw [smul_add, ea, hb', add_zero]
        · show finOne F • (a + b) = b
          rw [smul_add, eb, ha', zero_add]
      right_inv := fun Z => smul_split Z
      map_add' := fun p q => by
        show p.1.1 + q.1.1 + (p.2.1 + q.2.1) = p.1.1 + p.2.1 + (q.1.1 + q.2.1)
        abel
      continuous_toFun := (continuous_subtype_val.comp continuous_fst).add (continuous_subtype_val.comp continuous_snd)
      continuous_invFun := ((hsm (eInf F)).subtype_mk h₁).prodMk ((hsm (finOne F)).subtype_mk h₂) }
  obtain ⟨C, -, hC⟩ := KFock.integral_split ν (Measure.addHaar : Measure VI) (Measure.addHaar : Measure VF) Φs
  refine ⟨fun f X => (C : ℂ) * ∫ a : VI, d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X a.1)) * f a.1 ∂Measure.addHaar,
    fun G X => ∫ b : VF, d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X b.1)) * G b.1 ∂Measure.addHaar, fun f hf => ?_,
    fun G hG => ⟨?_, fun f hf Φ hΦ hTΦ => ?_⟩⟩
  · intro X Z hZ
    have hZ' := (_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.cw_zero_iff_k d Z).1 hZ
    dsimp only
    congr 2
    funext a
    rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.gram_add_left_k, _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.gram_fin_inf_k d hZ' a.2, add_zero]
  · intro X Z hZ
    dsimp only
    congr 1
    funext b
    rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.gram_add_left_k, _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.gram_inf_fin_k d hZ b.2, add_zero]
  · funext X
    rw [(hT.2.2.1 F E σ d) ν hν ε w hw Φ hΦ X, hTΦ, hC]
    have hpt : ∀ p : VI × VF, d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X (Φs p))) * (f (Φs p) * G (Φs p)) =
        (d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X p.1.1)) * f p.1.1) * (d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X p.2.1)) * G p.2.1) := by
      intro p
      have e1 : Φs p = p.1.1 + p.2.1 := rfl
      have hf' : f (p.1.1 + p.2.1) = f p.1.1 := hf p.1.1 p.2.1 ((_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.cw_zero_iff_k d _).2 p.2.2)
      have hG' : G (p.1.1 + p.2.1) = G p.2.1 := by rw [add_comm]; exact hG p.2.1 p.1.1 p.1.2
      rw [e1, hf', hG', _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.gram_add_right_k, _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.tt_add_k, mul_add, AddChar.map_add_eq_mul]
      ring
    simp only [hpt]
    rw [integral_prod_mul (μ := (Measure.addHaar : Measure VI)) (ν := (Measure.addHaar : Measure VF))
      (fun a : VI => d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X a.1)) * f a.1)
      (fun b : VF => d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X b.1)) * G b.1)]
    ring
end SDf
end PositivityTheory.SiegelWeilFormula.KAway
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKawayFinTop

section

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KAway
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace SDf
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
theorem step_of_triv_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (hD : _root_.PositivityTheory.SiegelWeilFormula.AdDecomp_k) (x : d.G) (hx : ∀ w, d.cw w (inFrame d.b x) = 1) :
    ∃ B, _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.StepF_k d x id B := by
  obtain ⟨-, ⟨ε, w₀, hw₀, -⟩, -⟩ := hA F E σ d
  have he : eInf F • inFrame d.b x = eInf F • (1 : Matrix _ _ (AE F E)) := (_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.cw_one_iff_k d _).1 hx
  obtain ⟨x₁, x₂, x₃, x₄, t, c, b, a, a', hxe, h1, h2, h3, h4, ht, hc, hb, -, ha'⟩ :=
    hD F E σ d ε w₀ hw₀ (eInf F) eInf_mul_self x he
  obtain ⟨AW, BW, hW⟩ := _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.stepW_k d hT hA ε w₀ hw₀
  have hW3 := _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.step_comp_k d (_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.step_comp_k d hW hW) hW
  have h4' : w₀ * (w₀ * w₀ * w₀) = 1 := by simpa only [mul_assoc] using _root_.PositivityTheory.SiegelWeilFormula.RD_k.w_four_pf hw₀
  obtain ⟨BC, hC⟩ := _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.step_conj_k d hT hW hW3 (_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.stepN_k d hT x₂ c h2 hc) h4'
  have hinv : w₀⁻¹ = w₀ * w₀ * w₀ := (eq_inv_of_mul_eq_one_left (_root_.PositivityTheory.SiegelWeilFormula.RD_k.w_four_pf hw₀)).symm
  obtain ⟨BM, hM⟩ := _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.stepM_k d hT x₃ a a' h3 ha'
  have hall := _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.step_comp_k d (_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.step_comp_k d (_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.step_comp_k d (_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.stepN_k d hT x₁ t h1 ht) hC) hM) (_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.stepN_k d hT x₄ b h4 hb)
  rw [hxe, hinv]
  exact ⟨_, hall⟩
end SDf
namespace SDf
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
theorem finAct_step_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (x : d.G) {B : (Mx F E d.m d.n → ℂ) → Mx F E d.m d.n → ℂ} (hB : _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.StepF_k d x id B) :
    ∀ g ∈ SB (Fin d.m × Fin d.n × Fin 2 → Af F), ∃ g' ∈ SB (Fin d.m × Fin d.n × Fin 2 → Af F),
      ∀ f : Mx F E d.m d.n → ℂ, (∀ X Z, (∀ w, d.cw w Z = 0) → f (X + Z) = f X) → ∀ Φ ∈ d.sch,
        d.T Φ = (fun X => f X * g fun k => (d.crd X k).2) → d.T (d.om x Φ) = fun X => f X * g' fun k => (d.crd X k).2 := by
  intro g hg
  set G : Mx F E d.m d.n → ℂ := fun X => g (_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.fcrd_k d X) with hGdef
  have hG : _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.InvInf_k d G := _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.fcrd_invInf_k d g
  have hBG := (hB.2 G hG).1
  set g₁ : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ := fun y => B G (d.cmb fun k => pairA F 0 (y k)) with hg₁
  have hfc : ∀ y, _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.fcrd_k d (d.cmb fun k => pairA F 0 (y k)) = y := fun y => by
    funext k
    simp only [_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.fcrd_k, _root_.PositivityTheory.SiegelWeilFormula.KFock.crd_cmb_k]
    rfl
  have hBg : ∀ X, B G X = g₁ (_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.fcrd_k d X) := fun X => _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.invInf_fcrd_k d hBG X
  by_cases hg0 : g = 0
  · refine ⟨0, (SB _).zero_mem, fun f hf Φ hΦ hTΦ => ?_⟩
    have hΦ0 : Φ = 0 := d.T_inj hT Φ hΦ (by rw [hTΦ, hg0]; funext X; simp)
    subst hΦ0
    rw [map_zero, d.T_zero]
    funext X
    simp
  refine ⟨g₁, ?_, fun f hf Φ hΦ hTΦ => ?_⟩
  swap
  · have e := (hB.2 G hG).2 f hf Φ hΦ hTΦ
    rw [e]
    funext X
    simp only [id]
    rw [hBg X]
    rfl
  obtain ⟨φ, v₀, hv₀⟩ := exists_schwartz_ne (κ := Fin d.m × Fin d.n × Fin 2) F
  set f₀ : Mx F E d.m d.n → ℂ := fun X => φ fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (d.crd X k).1 with hf₀d
  have hf₀ : _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.InvFin_k d f₀ := by
    intro X Z hZ
    have hZ' := (_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.cw_zero_iff_k d Z).1 hZ
    show (φ fun k => _) = φ fun k => _
    congr 1
    funext k
    have : (d.crd Z k).1 = 0 := by
      rw [← eInf_fst_mul (d.crd Z k), ← _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.crd_smul_k, hZ']
      simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.crd]
    rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.crd_add_k]
    change InfiniteAdeleRing.ringEquiv_mixedSpace F ((d.crd X k).1 + (d.crd Z k).1) = _
    rw [this, add_zero]
  have hmem : (fun X => f₀ X * G X) ∈ d.schM := by
    show (fun c => f₀ (d.cmb c) * G (d.cmb c)) ∈ schA F (Fin d.m × Fin d.n × Fin 2)
    have e : (fun c => f₀ (d.cmb c) * G (d.cmb c)) = pureA F (⇑φ) g := by
      funext c
      show (φ fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (d.crd (d.cmb c) k).1) *
        g (fun k => (d.crd (d.cmb c) k).2) = _
      rw [_root_.PositivityTheory.SiegelWeilFormula.KFock.crd_cmb_k]
      rfl
    rw [e]
    exact Submodule.subset_span ⟨φ, g, hg, rfl⟩
  obtain ⟨Φ₀, hΦ₀, hTΦ₀⟩ := (hT.1 F E σ d).2.1 _ hmem
  have e := (hB.2 G hG).2 f₀ hf₀ Φ₀ hΦ₀ hTΦ₀
  have hm := (hT.1 F E σ d).1 _ (d.om_sch x Φ₀ hΦ₀)
  rw [e] at hm
  have hs := slice_mem _ hm (fun k => (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (v₀ k))
  have e2 : (fun y : Fin d.m × Fin d.n × Fin 2 → Af F =>
      (fun X => id f₀ X * B G X) (d.cmb fun k => pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (v₀ k)) (y k))) =
      φ v₀ • g₁ := by
    funext y
    simp only [id, Pi.smul_apply, smul_eq_mul]
    rw [hBg]
    have h1 : _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.fcrd_k d (d.cmb fun k => pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (v₀ k)) (y k)) = y := by
      funext k
      simp only [_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.fcrd_k, _root_.PositivityTheory.SiegelWeilFormula.KFock.crd_cmb_k]
      rfl
    rw [h1]
    congr 1
    show (φ fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (d.crd (d.cmb _) k).1) = _
    rw [_root_.PositivityTheory.SiegelWeilFormula.KFock.crd_cmb_k]
    congr 1
    funext k
    exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply (v₀ k)
  have hs' : φ v₀ • g₁ ∈ SB (Fin d.m × Fin d.n × Fin 2 → Af F) := by
    rw [← e2]
    exact hs
  have := (SB (Fin d.m × Fin d.n × Fin 2 → Af F)).smul_mem (φ v₀)⁻¹ hs'
  rwa [smul_smul, inv_mul_cancel₀ hv₀, one_smul] at this
end SDf
theorem finAct_of_k : _root_.PositivityTheory.SiegelWeilFormula.TAll_k → _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties → _root_.PositivityTheory.SiegelWeilFormula.AdDecomp_k → _root_.PositivityTheory.SiegelWeilFormula.FinAct_k := by
  intro hT hA hD F E _ _ _ _ _ σ d x hx
  obtain ⟨B, hB⟩ := _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.step_of_triv_k d hT hA hD x hx
  exact _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.finAct_step_k d hT x hB
end PositivityTheory.SiegelWeilFormula.KAway
end
end
end
end
