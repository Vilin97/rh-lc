module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTwSt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAldTop
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilFinCore
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilFinMid
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfockFock
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfourW
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.THeisK
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
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
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfpFin
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfpLine
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.PolyGaussOfLines
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfpDefs
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopTop
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTbijMain
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTunitHeis
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTunitMain
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTwuMain
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSchwartzThetaDistributionSumNeZero
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTautoRat
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.MatrixOfUnipotentFrame
import Mathlib.Tactic.Polynomial.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTparMain
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaParabolic.InvMulSelfMatrixDoubled
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaParabolic.LRhoOm
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTwpMain

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKKfpMin

section

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFP
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
theorem exists_poly_k {Φ : d.Fn} (hΦ : d.KFin Φ) {k : d.G} (hk : k ∈ d.K) :
    ∃ q : Polynomial ℂ, q ≠ 0 ∧ ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i • d.om (k ^ i) Φ = 0 := by
  set V := Submodule.span ℂ (Set.range fun k : d.K => d.om k.1 Φ) with hV
  have : FiniteDimensional ℂ V := hΦ.2
  have hmap : ∀ v ∈ V, d.om k v ∈ V := by
    intro v hv
    refine Submodule.span_induction (p := fun v _ => d.om k v ∈ V) ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨k', rfl⟩
      refine Submodule.subset_span ⟨⟨k * k'.1, d.K.mul_mem hk k'.2⟩, ?_⟩
      simp [map_mul]
    · simp
    · intro x y _ _ hx hy; simpa using V.add_mem hx hy
    · intro a x _ hx; simpa using V.smul_mem a hx
  have hΦV : Φ ∈ V := Submodule.subset_span ⟨1, by simp⟩
  set f : V →ₗ[ℂ] V := (d.om k).restrict hmap
  have hpow : ∀ (i : ℕ) (v : V), (((f ^ i) v : V) : d.Fn) = d.om (k ^ i) v := by
    intro i
    induction i with
    | zero => intro v; simp
    | succ i ih =>
      intro v
      rw [pow_succ, Module.End.mul_apply, ih, pow_succ, map_mul, Module.End.mul_apply]
      rfl
  refine ⟨minpoly ℂ f, minpoly.ne_zero (Algebra.IsIntegral.isIntegral f), ?_⟩
  have h0 := congrArg (fun g : Module.End ℂ V => ((g ⟨Φ, hΦV⟩ : V) : d.Fn)) (minpoly.aeval ℂ f)
  rw [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply, Submodule.coe_sum] at h0
  simpa only [LinearMap.smul_apply, Submodule.coe_smul, hpow, LinearMap.zero_apply, ZeroMemClass.coe_zero] using h0
end PositivityTheory.SiegelWeilFormula.KFP
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfpMain

section

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFP
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem actB_mul_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (a b : d.G) (u : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    actB (cA σ) (a * b) u = actB (cA σ) a (actB (cA σ) b u) := by
  simp only [actB, Units.val_mul, Subgroup.coe_mul, Matrix.transpose_mul, Matrix.mul_assoc]
theorem actB_one_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (u : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    actB (cA σ) (1 : d.G) u = u := by
  simp [actB]
theorem kFinPoly_of_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hU : _root_.PositivityTheory.SiegelWeilFormula.TUnit_k) (hH : _root_.PositivityTheory.SiegelWeilFormula.THeis_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (hF : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (hLO : _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k)
    (hLI : _root_.PositivityTheory.SiegelWeilFormula.LocInst_k) : _root_.PositivityTheory.SiegelWeilFormula.KFinPoly_k := by
  intro F E _ _ _ _ _ σ d R Φ hK
  have hΦ : Φ ∈ d.sch := hK.1
  obtain ⟨k, ω, χ, C, c, ν, νf, vv, hk, hω1, hω, hχ, hC, hν, hνf, heig, hrot, hB⟩ :=
    _root_.PositivityTheory.SiegelWeilFormula.KFP.line_data_k hT hU hH hA hF hLO hLI R
  obtain ⟨q, hq0, hq⟩ := _root_.PositivityTheory.SiegelWeilFormula.KFP.exists_poly_k hK hk
  have hω0 : ω ≠ 0 := by
    intro h; rw [h, norm_zero] at hω1; exact zero_ne_one hω1
  have hωi : ∀ j : ℕ, 0 < j → ω⁻¹ ^ j ≠ 1 := fun j hj h => hω j hj (by rw [inv_pow] at h; exact inv_eq_one.1 h)
  have hμ : (star χ)⁻¹ ≠ 0 := inv_ne_zero (star_ne_zero.2 hχ)
  obtain ⟨N, hN⟩ := poly_of_rot q hq0 (star χ)⁻¹ ω⁻¹ hμ (inv_ne_zero hω0) hωi
  have hinv : ∀ ξ z, actB (cA σ) k⁻¹ (vv ξ z) = vv ξ (ω⁻¹ * z) := fun ξ z => by
    have := congrArg (actB (cA σ) k⁻¹) (hrot ξ (ω⁻¹ * z))
    rwa [← _root_.PositivityTheory.SiegelWeilFormula.KFP.actB_mul_k, inv_mul_cancel, _root_.PositivityTheory.SiegelWeilFormula.KFP.actB_one_k, ← mul_assoc, mul_inv_cancel₀ hω0, one_mul, eq_comm] at this
  have hact : ∀ (i : ℕ) ξ z, actB (cA σ) (k⁻¹ ^ i) (vv ξ z) = vv ξ (ω⁻¹ ^ i * z) := by
    intro i
    induction i with
    | zero => intro ξ z; simp [_root_.PositivityTheory.SiegelWeilFormula.KFP.actB_one_k]
    | succ i ih => intro ξ z; rw [pow_succ, _root_.PositivityTheory.SiegelWeilFormula.KFP.actB_mul_k, hinv, ih, pow_succ, mul_assoc]
  have hTΦ : d.T Φ ∈ d.schM := (hT.1 F E σ d).1 Φ hΦ
  refine _root_.PositivityTheory.SiegelWeilFormula.KFP.mem_fock_of_k R hνf hTΦ fun g hg' => ?_
  obtain ⟨Ω, hΩ, hTΩ⟩ := _root_.PositivityTheory.SiegelWeilFormula.KFP.exists_lift_k hT hF R hg'
  obtain ⟨h, hh⟩ := _root_.PositivityTheory.SiegelWeilFormula.KFP.hg_sch_k R hνf hTΦ hg'
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  obtain ⟨P, -, hP⟩ := poly_gauss_of_lines (2 * Real.pi) hpi N h fun ξ => by
    set I : ℂ → ℂ := fun z => ∫ u, h u * Real.exp (-(2 * Real.pi * ‖u‖ ^ 2)) * Complex.exp (z * ⟪ξ, u⟫_ℝ) with hI
    set Eξ : ℂ → ℂ := fun z => Complex.exp (-(z ^ 2 * ‖ξ‖ ^ 2 / (16 * Real.pi))) * I z with hE
    have hdiff : Differentiable ℂ Eξ :=
      (Differentiable.cexp (by fun_prop)).mul (entire_laplace (2 * Real.pi) hpi h ξ)
    have hrel : ∀ z, ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i * (star χ)⁻¹ ^ i * Eξ (ω⁻¹ ^ i * z) = 0 := by
      intro z
      have e0 := _root_.PositivityTheory.SiegelWeilFormula.KFP.B_rel_k hT hU hν hχ hΩ (heig g hg' Ω hΩ hTΩ) hΦ q hq (vv ξ z)
      simp only [hact, hB g hg' Ω hΩ hTΩ Φ hΦ, ← hh] at e0
      have hn : ∀ i : ℕ, ‖ω⁻¹ ^ i * z‖ = ‖z‖ := fun i => by
        rw [norm_mul, norm_pow, norm_inv, hω1, inv_one, one_pow, one_mul]
      simp only [hn] at e0
      have hc0 : (C * (Real.exp (-(c * ‖z‖ ^ 2 * ‖ξ‖ ^ 2)) : ℂ)) ≠ 0 :=
        mul_ne_zero hC (Complex.ofReal_ne_zero.2 (Real.exp_pos _).ne')
      refine (mul_eq_zero.1 (?_ : (C * (Real.exp (-(c * ‖z‖ ^ 2 * ‖ξ‖ ^ 2)) : ℂ)) *
        ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i * (star χ)⁻¹ ^ i * Eξ (ω⁻¹ ^ i * z) = 0)).resolve_left hc0
      rw [Finset.mul_sum, ← e0]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hE, hI]
      ring
    obtain ⟨p, hpN, hp⟩ := hN Eξ hdiff hrel
    refine ⟨p, hpN, fun z => ?_⟩
    have e1 := hp z
    simp only [hE] at e1
    have e2 : I z = Complex.exp (z ^ 2 * ‖ξ‖ ^ 2 / (16 * Real.pi)) * p.eval z := by
      rw [← e1, ← mul_assoc, ← Complex.exp_add]
      simp
    have e3 : ((8 : ℂ) * ((2 * Real.pi : ℝ) : ℂ)) = 16 * (Real.pi : ℂ) := by push_cast; ring
    rw [e3]
    simpa [hI] using e2
  exact ⟨P, fun u => by rw [← hh]; exact hP u⟩
end PositivityTheory.SiegelWeilFormula.KFP
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTwvThetaW

section

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.TW.ThetaWPf
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem isW_rat_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {ε : ℤˣ} {w : d.G} (hw : d.IsW ε w) : w ∈ rat2 σ d.Y := by
  refine PositivityTheory.SiegelWeilFormula.kunf.rat_of_inFrame (b := d.b) (M := Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) ?_
  rw [(hw : inFrame d.b w = _)]
  ext (i | i) (j | j) <;> simp [incM, Matrix.one_apply] <;> split_ifs <;> simp
theorem thetaW_k : _root_.PositivityTheory.SiegelWeilFormula.TW.ThetaW_k := by
  intro F E _ _ _ _ _ σ d
  refine ⟨fun ε w hw Φ hΦ => ?_, GlobalTheory.ThetaSumNe.exists_mem_schA_thetaSum_ne_zero F d.κ⟩
  exact ⟨d.ok.dbl.weil.2.1.pres w Φ hΦ, _root_.PositivityTheory.SiegelWeilFormula.Tauto.thetaSum_rational_invariant d w (_root_.PositivityTheory.SiegelWeilFormula.TW.ThetaWPf.isW_rat_k d hw) Φ hΦ⟩
end PositivityTheory.SiegelWeilFormula.TW.ThetaWPf
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTwvUpTo

section

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.TW.UpToPf
open PositivityTheory.SiegelWeilFormula.Tpar
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem w_cols_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {ε : ℤˣ} {w : d.G} (hw : d.IsW ε w) :
    mat2 w * incM F d.b.1.toCols₂ = incM F d.b.1.toCols₁ ∧
    mat2 w⁻¹ * incM F d.b.1.toCols₂ = ((ε : ℤ) : AE F E) • incM F d.b.1.toCols₁ := by
  obtain ⟨t0, hB, -, -, -⟩ := _root_.PositivityTheory.SiegelWeilFormula.Tpar.frameData_k d
  have h1 := inFrame_mul hw
  have he : ((ε : ℤ) : AE F E) * ((ε : ℤ) : AE F E) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have hN : (Matrix.fromBlocks 0 1 (((ε : ℤ) : AE F E) • 1) 0 :
        Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) *
      Matrix.fromBlocks 0 (((ε : ℤ) : AE F E) • 1) 1 0 = 1 := by
    rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
    simp [smul_smul, he]
  have h2 := inv_mul_frame h1 hN
  rw [hB, Matrix.mul_fromCols, Matrix.fromCols_mul_fromBlocks] at h1 h2
  obtain ⟨-, h1b⟩ := Matrix.fromCols_inj h1
  obtain ⟨-, h2b⟩ := Matrix.fromCols_inj h2
  refine ⟨?_, ?_⟩
  · rw [h1b]; simp
  · rw [h2b]; simp
theorem tt_smul_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (ε : ℤˣ) (X Z : Mx F E d.m d.n) :
    d.tt (d.gram (((ε : ℤ) : AE F E) • X) Z) = ((ε : ℤ) : AF F) * d.tt (d.gram X Z) := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, _root_.PositivityTheory.SiegelWeilFormula.SD_k.gram, Matrix.transpose_smul, Matrix.smul_mul, Matrix.trace_smul]
  rw [Int.cast_smul_eq_zsmul, map_zsmul, zsmul_eq_mul]
theorem upTo_of_k (hU : _root_.PositivityTheory.SiegelWeilFormula.TW.Uniq_k) : _root_.PositivityTheory.SiegelWeilFormula.TW.UpTo_k := by
  intro F E _ _ _ _ _ σ d ν hν ε w hw
  have h := d.ok.dbl
  have hψ : IsStd d.B.ψ := d.ok.good.std
  obtain ⟨t0, -, hBx, -, -⟩ := _root_.PositivityTheory.SiegelWeilFormula.Tpar.frameData_k d
  obtain ⟨hw1, hw2⟩ := _root_.PositivityTheory.SiegelWeilFormula.TW.UpToPf.w_cols_k d hw
  have hsp := h.weil.2.1.toIsSplitting
  obtain ⟨C, hC⟩ := hU F E σ d ν hν (d.l ∘ₗ d.om w) (hsp.adm w d.l h.adm) (by
    intro Z Φ hΦ
    simp only [LinearMap.comp_apply]
    rw [hsp.impl w _ Φ hΦ]
    have e : actB (cA σ) w (Z * (incM F d.b.1.toCols₂)ᵀ) =
        (Z * (incM F t0.1)ᵀ) * (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E))ᵀ := by
      change Z * (incM F d.b.1.toCols₂)ᵀ * (mat2 w)ᵀ = _
      rw [Matrix.mul_assoc, ← Matrix.transpose_mul, hw1, hBx, Matrix.transpose_mul, Matrix.mul_assoc]
    rw [e]
    convert h.kill (Z * (incM F t0.1)ᵀ) _ (hsp.pres w Φ hΦ) using 4
    all_goals rfl)
  refine ⟨C, fun Φ hΦ X => ?_⟩
  change d.l (d.dd.rho d.B.ψ (X * (incM F d.b.1.toCols₂)ᵀ) (d.om w Φ)) = _
  have key : X * (incM F d.b.1.toCols₂)ᵀ * (mat2 w⁻¹)ᵀ =
      (((ε : ℤ) : AE F E) • X) * (incM F d.b.1.toCols₁)ᵀ := by
    rw [Matrix.mul_assoc, ← Matrix.transpose_mul, hw2, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul]
  have hr := l_rho_om h w (X * (incM F d.b.1.toCols₂)ᵀ) (Φ := Φ) hΦ
  change d.l (d.dd.rho d.B.ψ (X * (incM F d.b.1.toCols₂)ᵀ) (d.om w Φ)) =
    d.l (d.om w (d.dd.rho d.B.ψ (X * (incM F d.b.1.toCols₂)ᵀ * (mat2 w⁻¹)ᵀ) Φ)) at hr
  rw [hr, key]
  have hm : d.dd.rho d.B.ψ ((((ε : ℤ) : AE F E) • X) * (incM F d.b.1.toCols₁)ᵀ) Φ ∈ d.sch :=
    GlobalTheory.HeisSchA.schr_mem_schA _ hψ _ Φ hΦ
  have e1 := hC _ hm
  simp only [LinearMap.comp_apply] at e1
  rw [e1]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun Z => ?_)
  simp only
  rw [(_root_.PositivityTheory.SiegelWeilFormula.Tunit.tHeis_k F E σ d Φ hΦ (((ε : ℤ) : AE F E) • X) Z).2, _root_.PositivityTheory.SiegelWeilFormula.TW.UpToPf.tt_smul_k]
end PositivityTheory.SiegelWeilFormula.TW.UpToPf
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilFinPre

section

@[expose] public section



section
noncomputable section
open GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Fin
theorem tWeyl_of_k (hP : _root_.PositivityTheory.SiegelWeilFormula.TW.Poisson_k) : _root_.PositivityTheory.SiegelWeilFormula.TWeyl_k :=
  _root_.PositivityTheory.SiegelWeilFormula.TW.tWeyl_of_k _root_.PositivityTheory.SiegelWeilFormula.TBij_k.tBij _root_.PositivityTheory.SiegelWeilFormula.Fin.tTheta_k (_root_.PositivityTheory.SiegelWeilFormula.TW.UpToPf.upTo_of_k _root_.PositivityTheory.SiegelWeilFormula.TW.Twu.uniq_k) hP _root_.PositivityTheory.SiegelWeilFormula.TW.ThetaWPf.thetaW_k
theorem siegelWeilStd_pre_k (hP : _root_.PositivityTheory.SiegelWeilFormula.TW.Poisson_k) (hCT : _root_.PositivityTheory.SiegelWeilFormula.CTSplit_k) : _root_.GlobalTheory.ThK.Dbl.SiegelWeilStd_k :=
  have hT := _root_.PositivityTheory.SiegelWeilFormula.Fin.tAll_of_k (_root_.PositivityTheory.SiegelWeilFormula.Fin.tWeyl_of_k hP)
  _root_.PositivityTheory.SiegelWeilFormula.Fin.siegelWeilStd_mid_k (_root_.PositivityTheory.SiegelWeilFormula.Fin.tWeyl_of_k hP)
    (_root_.PositivityTheory.SiegelWeilFormula.KFP.kFinPoly_of_k hT _root_.PositivityTheory.SiegelWeilFormula.Tunit.tUnit_k _root_.PositivityTheory.SiegelWeilFormula.Tunit.tHeis_k _root_.PositivityTheory.SiegelWeilFormula.kfour.auxiliaryExistence_holds _root_.PositivityTheory.SiegelWeilFormula.KFock.fockMem_k (_root_.PositivityTheory.SiegelWeilFormula.locOpEx_of_tAll_k hT) (_root_.PositivityTheory.SiegelWeilFormula.Fin.locInst_of_k hT))
    (_root_.PositivityTheory.SiegelWeilFormula.Ald.ldEx_of_k hT _root_.PositivityTheory.SiegelWeilFormula.kfour.auxiliaryExistence_holds) hCT
end PositivityTheory.SiegelWeilFormula.Fin
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilFinLt

section

@[expose] public section



section
open GlobalTheory.ThK.Dbl
namespace PositivityTheory.SiegelWeilFormula.Fin
theorem siegelWeilStd_of_ct_k (hCT : _root_.PositivityTheory.SiegelWeilFormula.CTSplit_k) : _root_.GlobalTheory.ThK.Dbl.SiegelWeilStd_k := _root_.PositivityTheory.SiegelWeilFormula.Fin.siegelWeilStd_pre_k _root_.PositivityTheory.SiegelWeilFormula.TW.Twp.poisson_k hCT
end PositivityTheory.SiegelWeilFormula.Fin
end
end
end
