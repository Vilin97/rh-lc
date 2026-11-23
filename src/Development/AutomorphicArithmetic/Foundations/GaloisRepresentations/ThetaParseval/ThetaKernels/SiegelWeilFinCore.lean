module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAeisWk
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAfcFcS
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicFormCongruences.GramExtendZeroEmbedded
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseUnfoldB
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.DoubledGroupTopologicalProperties
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
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAfcUExS
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAstepDefs
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAstepCut
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAstepDeg
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.DerivInv
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.IsExtAtOfDiff
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAtopField
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAvacIwaTop
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAvacVacTop
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKawayTop
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfockFock
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfourFZ
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfourLB
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfourNA
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfourW
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKheadSecK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopTop
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKrdDenseW
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKrdRD
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKsingTop
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKsplitGIinvCut
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.AdDecompK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKsplitSplitP
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKsplitSplitW
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaSplitting.SplitCut
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.SplitB
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKunfMain
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitTop
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTautoAuto
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTautoCoef
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTbijMain
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTparMain
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTweylCommB
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SiegelSetUnitaryStatement
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.HolomorphicTheta.HolomorphicAverageUniform
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilStandard.SiegelWeilStdOf
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.VacuumGeneratesPolynomials

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAfcOrbS

section

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Afc
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem gram_incM_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (X : Matrix (Fin d.m) (Fin d.n) E) :
    d.gram (incM F X) (incM F X) = incM F (gE d.A.J σ X) := by
  have h1 : (incM F X).map (cA σ) = incM F (X.map σ) := by ext i j; rfl
  show (incM F X)ᵀ * incM F d.A.J * (incM F X).map (cA σ) = _
  rw [h1]
  simp only [gE, incM, ← Matrix.transpose_map, ← Matrix.map_mul]
theorem cond_iff_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (X : Matrix (Fin d.m) (Fin d.n) E) (M : Matrix (Fin d.n) (Fin d.n) (AE F E)) :
    d.gram (incM F X) (incM F X) = (-2 : ℤ) • M ↔
      ∀ k l, inclR (F := F) (AF F) (gE d.A.J σ X k l) = (-2 : ℤ) • M k l := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.Afc.gram_incM_k, ← Matrix.ext_iff]
  rfl
theorem orb_zero_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (hmn : d.m < d.n) (T : nF σ d.Y d.b) (hT : IsND T) (Φ : d.Fn) : d.orb T Φ = 0 := by
  have hE : IsEmpty {X : Matrix (Fin d.m) (Fin d.n) E // d.gram (incM F X) (incM F X) = (-2 : ℤ) • T.1.1} := by
    refine ⟨fun ⟨X, hX⟩ => ?_⟩
    rw [_root_.PositivityTheory.SiegelWeilFormula.Afc.gram_incM_k] at hX
    have hdet := congrArg Matrix.det hX
    have h0 : (gE d.A.J σ X).det = 0 := by
      by_contra h
      have hu : IsUnit (gE d.A.J σ X) := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 h)
      have h1 := Matrix.rank_of_isUnit _ hu
      have h2 : (gE d.A.J σ X).rank ≤ d.m := by
        rw [gE, Matrix.mul_assoc]
        exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_width _)
      rw [h1, Fintype.card_fin] at h2
      omega
    have hm : ((gE d.A.J σ X).map (inclR (F := F) (AF F))).det = inclR (F := F) (AF F) (gE d.A.J σ X).det :=
      ((inclR (F := F) (AF F)).map_det _).symm
    rw [incM, hm, h0, map_zero, ← Int.cast_smul_eq_zsmul (AE F E), Matrix.det_smul, Fintype.card_fin] at hdet
    exact hT ((isUnit_neg_two_pow d.n).mul_right_eq_zero.1 hdet.symm)
  simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.orb, tsum_empty]
section Res
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
def extendByZeroColumns (X' : Matrix (Fin d.m) (Fin L.n) E) : Matrix (Fin d.m) (Fin d.n) E := fun a => Function.extend L.em (X' a) 0
theorem extendZeroColumn_apply_embed (X' : Matrix (Fin d.m) (Fin L.n) E) (a : Fin d.m) (j : Fin L.n) : _root_.PositivityTheory.SiegelWeilFormula.Afc.extendByZeroColumns L X' a (L.em j) = X' a j :=
  L.inj.extend_apply _ _ _
theorem not_mem_range_k : L.i₀ ∉ Set.range L.em := fun h => ((L.rng L.i₀).2 h) rfl
theorem extendZeroColumn_apply_missing (X' : Matrix (Fin d.m) (Fin L.n) E) (a : Fin d.m) : _root_.PositivityTheory.SiegelWeilFormula.Afc.extendByZeroColumns L X' a L.i₀ = 0 :=
  Function.extend_apply' _ _ _ fun ⟨j, hj⟩ => _root_.PositivityTheory.SiegelWeilFormula.Afc.not_mem_range_k L ⟨j, hj⟩
theorem cases_idx_k (k : Fin d.n) : k = L.i₀ ∨ ∃ j, L.em j = k := by
  by_cases h : k = L.i₀
  · exact Or.inl h
  · exact Or.inr ((L.rng k).1 h)
theorem hermForm_extendZeroColumn_embed (X' : Matrix (Fin d.m) (Fin L.n) E) (i j : Fin L.n) :
    gE d.A.J σ (_root_.PositivityTheory.SiegelWeilFormula.Afc.extendByZeroColumns L X') (L.em i) (L.em j) = gE d.A.J σ X' i j := by
  simp only [gE_apply, _root_.PositivityTheory.SiegelWeilFormula.Afc.extendZeroColumn_apply_embed]
theorem hermForm_extendZeroColumn_left (X' : Matrix (Fin d.m) (Fin L.n) E) (l : Fin d.n) : gE d.A.J σ (_root_.PositivityTheory.SiegelWeilFormula.Afc.extendByZeroColumns L X') L.i₀ l = 0 := by
  simp [gE_apply, _root_.PositivityTheory.SiegelWeilFormula.Afc.extendZeroColumn_apply_missing]
theorem hermForm_extendZeroColumn_right (X' : Matrix (Fin d.m) (Fin L.n) E) (k : Fin d.n) : gE d.A.J σ (_root_.PositivityTheory.SiegelWeilFormula.Afc.extendByZeroColumns L X') k L.i₀ = 0 := by
  simp [gE_apply, _root_.PositivityTheory.SiegelWeilFormula.Afc.extendZeroColumn_apply_missing]
theorem gE_sub_k (X : Matrix (Fin d.m) (Fin d.n) E) (i j : Fin L.n) :
    gE d.A.J σ (X.submatrix id L.em) i j = gE d.A.J σ X (L.em i) (L.em j) := by
  simp only [gE_apply, Matrix.submatrix_apply, id]
theorem col_zero_k (X : Matrix (Fin d.m) (Fin d.n) E) (h : gE d.A.J σ X L.i₀ L.i₀ = 0) (a : Fin d.m) : X a L.i₀ = 0 := by
  have hA : Aniso σ d.A.J := _root_.GlobalTheory.ThK.Dbl.aniso_of_k d.ok.good (d.ok.sign.elim (fun h => Or.inl h.1) fun h => Or.inr h.1) d.ok.aniso
  have key := hA (fun i => X i L.i₀) (by
    rw [← h, gE_apply]
    simp only [form, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
    ring)
  exact congrFun key a
theorem extension_by_zero_submatrix (X : Matrix (Fin d.m) (Fin d.n) E) (h : ∀ a, X a L.i₀ = 0) : _root_.PositivityTheory.SiegelWeilFormula.Afc.extendByZeroColumns L (X.submatrix id L.em) = X := by
  ext a k
  rcases _root_.PositivityTheory.SiegelWeilFormula.Afc.cases_idx_k L k with rfl | ⟨j, rfl⟩
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Afc.extendZeroColumn_apply_missing, h]
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Afc.extendZeroColumn_apply_embed]; rfl
theorem submatrix_extendZeroColumn (X' : Matrix (Fin d.m) (Fin L.n) E) : (_root_.PositivityTheory.SiegelWeilFormula.Afc.extendByZeroColumns L X').submatrix id L.em = X' := by
  ext a j
  exact _root_.PositivityTheory.SiegelWeilFormula.Afc.extendZeroColumn_apply_embed L X' a j
def eqv_k (T : nF σ d.Y d.b) (T' : nF σ L.Y L.b) (hs : L.IsSub T T') :
    {X : Matrix (Fin d.m) (Fin d.n) E // d.gram (incM F X) (incM F X) = (-2 : ℤ) • T.1.1} ≃
      {X : Matrix (Fin L.sd.m) (Fin L.sd.n) E // L.sd.gram (incM F X) (incM F X) = (-2 : ℤ) • T'.1.1} where
  toFun X := ⟨X.1.submatrix id L.em, by
    refine (_root_.PositivityTheory.SiegelWeilFormula.Afc.cond_iff_k L.sd _ _).2 fun i j => ?_
    have h := (_root_.PositivityTheory.SiegelWeilFormula.Afc.cond_iff_k d _ _).1 X.2 (L.em i) (L.em j)
    show inclR (F := F) (AF F) (gE d.A.J σ (X.1.submatrix id L.em) i j) = _
    rw [_root_.PositivityTheory.SiegelWeilFormula.Afc.gE_sub_k, h, hs.2]
    rfl⟩
  invFun X' := ⟨_root_.PositivityTheory.SiegelWeilFormula.Afc.extendByZeroColumns L X'.1, by
    refine (_root_.PositivityTheory.SiegelWeilFormula.Afc.cond_iff_k d _ _).2 fun k l => ?_
    rcases _root_.PositivityTheory.SiegelWeilFormula.Afc.cases_idx_k L k with rfl | ⟨i, rfl⟩
    · rw [_root_.PositivityTheory.SiegelWeilFormula.Afc.hermForm_extendZeroColumn_left, (hs.1 l).1, map_zero, smul_zero]
    rcases _root_.PositivityTheory.SiegelWeilFormula.Afc.cases_idx_k L l with rfl | ⟨j, rfl⟩
    · rw [_root_.PositivityTheory.SiegelWeilFormula.Afc.hermForm_extendZeroColumn_right, (hs.1 _).2, map_zero, smul_zero]
    rw [_root_.PositivityTheory.SiegelWeilFormula.Afc.hermForm_extendZeroColumn_embed]
    have h := (_root_.PositivityTheory.SiegelWeilFormula.Afc.cond_iff_k L.sd _ _).1 X'.2 i j
    refine h.trans ?_
    rw [hs.2]
    rfl⟩
  left_inv X := by
    refine Subtype.ext (_root_.PositivityTheory.SiegelWeilFormula.Afc.extension_by_zero_submatrix L X.1 (_root_.PositivityTheory.SiegelWeilFormula.Afc.col_zero_k L X.1 ?_))
    have h := (_root_.PositivityTheory.SiegelWeilFormula.Afc.cond_iff_k d _ _).1 X.2 L.i₀ L.i₀
    rw [(hs.1 L.i₀).1, smul_zero] at h
    exact kfour.inclR_injective (h.trans (map_zero _).symm)
  right_inv X' := Subtype.ext (_root_.PositivityTheory.SiegelWeilFormula.Afc.submatrix_extendZeroColumn L X'.1)
theorem orb_res_k (T : nF σ d.Y d.b) (T' : nF σ L.Y L.b) (hs : L.IsSub T T') (Φ : d.Fn) (Φ' : L.sd.Fn)
    (hr : L.IsRes Φ Φ') : d.orb T Φ = L.sd.orb T' Φ' := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.orb
  refine congrArg (fun f : UA σ d.A.J → ℂ => ⨍ g in d.D, f g ∂d.μ) (funext fun g => ?_)
  rw [← (_root_.PositivityTheory.SiegelWeilFormula.Afc.eqv_k L T T' hs).tsum_eq]
  refine tsum_congr fun X => ?_
  have hc : ∀ a, X.1 a L.i₀ = 0 := _root_.PositivityTheory.SiegelWeilFormula.Afc.col_zero_k L X.1 (by
    have h := (_root_.PositivityTheory.SiegelWeilFormula.Afc.cond_iff_k d _ _).1 X.2 L.i₀ L.i₀
    rw [(hs.1 L.i₀).1, smul_zero] at h
    exact kfour.inclR_injective (h.trans (map_zero _).symm))
  have hz : ∀ a, (mat g⁻¹ * incM F X.1) a L.i₀ = 0 := fun a => by
    simp [Matrix.mul_apply, incM, hc]
  rw [← hr.2 _ hz]
  congr 1
end Res
theorem orbRes_k : _root_.PositivityTheory.SiegelWeilFormula.OrbRes_k := fun _F _E _ _ _ _ _ _σ d =>
  ⟨fun hmn T hT Φ => _root_.PositivityTheory.SiegelWeilFormula.Afc.orb_zero_k d hmn T hT Φ, fun L T T' hs Φ Φ' hr => _root_.PositivityTheory.SiegelWeilFormula.Afc.orb_res_k L T T' hs Φ Φ' hr⟩
end PositivityTheory.SiegelWeilFormula.Afc
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAstepTop

section

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.AStep
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem ndZero_k (H : _root_.PositivityTheory.SiegelWeilFormula.AStep.Hyps_k) {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (hmn : d.m < d.n) {Φ : d.Fn} (hΦ : Φ ∈ d.sch) (hv : d.T Φ ∈ R.vac)
    {U p Ê t} (hE : _root_.PositivityTheory.SiegelWeilFormula.AStep.EData_k d (d.sec0 Φ) (s0 d.m d.n) (s0 d.m d.n) U p Ê t) (j : ℕ) (hj : j ≤ p.rootMultiplicity (s0 d.m d.n))
    {nb lam 𝓖} (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) {T : nF σ d.Y d.b} (hT : IsND T) (x : d.G) :
    fc d.B.ψ d.b nb lam 𝓖 (_root_.PositivityTheory.SiegelWeilFormula.AStep.Bj_k d Φ p Ê j) T x = 0 := by
  have hK := H.polyKFin F E σ d R Φ hΦ ((H.vacK F E σ d R).2.1 hv)
  have hsec := H.secK F E σ d Φ hK
  have hEis := H.eisWk F E σ d _ _ hsec
  have hL : (fun f => fc d.B.ψ d.b nb lam 𝓖 f T x) ∈ d.lamSet := ⟨nb, lam, 𝓖, T, x, hc, hT, rfl⟩
  obtain ⟨hadd, hbd⟩ := H.lamBd F E σ d _ hL
  obtain ⟨hUo, hR, hs, hp, hd, hcont, hinv, hfar⟩ := hE
  obtain ⟨hDiff, hComm⟩ := lamDeriv (rat2 σ d.Y) _ hadd hbd U Ê hUo hd hcont hinv
  obtain ⟨-, -, hI⟩ := H.tAll.2.2.2.2 F E σ d
  obtain ⟨-, hIc, hIi⟩ := hI Φ hΦ
  have hAc := famCont U Ê hUo hd hcont _ hs j
  have hAi : ∀ γ ∈ rat2 σ d.Y, ∀ g, iteratedDeriv j (Ê · (γ * g)) (s0 d.m d.n) = iteratedDeriv j (Ê · g) (s0 d.m d.n) :=
    fun γ hγ g => derivInv U Ê hUo _ hs γ g (fun z hz => hinv z hz γ hγ g) j
  have hLI : fc d.B.ψ d.b nb lam 𝓖 (d.I Φ) T x = 0 := by
    rw [H.thetaCoef F E σ d Φ hΦ nb lam 𝓖 hc T x]; exact (H.orbRes F E σ d).1 hmn T hT _
  have hB : _root_.PositivityTheory.SiegelWeilFormula.AStep.Bj_k d Φ p Ê j = (-(iteratedDeriv j (fun z => p.eval z) (s0 d.m d.n) * 2)) • d.I Φ +
      (fun g => iteratedDeriv j (Ê · g) (s0 d.m d.n)) := by
    funext g; simp only [_root_.PositivityTheory.SiegelWeilFormula.AStep.Bj_k, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have h1 := hadd (-(iteratedDeriv j (fun z => p.eval z) (s0 d.m d.n) * 2)) (d.I Φ) (fun g => iteratedDeriv j (Ê · g) (s0 d.m d.n))
    hIc hAc hIi hAi
  rw [hB, h1, hLI, mul_zero, zero_add, ← hComm _ hs j]
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
theorem stepJ_k (H : _root_.PositivityTheory.SiegelWeilFormula.AStep.Hyps_k) {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (R' : _root_.PositivityTheory.SiegelWeilFormula.RD_k L.sd) (hmn : d.m < d.n) (hIH : _root_.PositivityTheory.SiegelWeilFormula.MainV_k 2 R') {Φ : d.Fn}
    (hΦ : Φ ∈ d.sch) (hv : d.T Φ ∈ R.vac) {U p Ê t} (hE : _root_.PositivityTheory.SiegelWeilFormula.AStep.EData_k d (d.sec0 Φ) (s0 d.m d.n) (s0 d.m d.n) U p Ê t) (j : ℕ)
    (hj : j ≤ p.rootMultiplicity (s0 d.m d.n)) (hlow : ∀ i < j, ∀ g, iteratedDeriv i (Ê · g) (s0 d.m d.n) = 0) :
    ∀ g, _root_.PositivityTheory.SiegelWeilFormula.AStep.Bj_k d Φ p Ê j g = 0 := by
  obtain ⟨nb, lam, 𝓖, hc⟩ := H.coefEx F E σ d
  have hE' := hE
  obtain ⟨hUo, hR, hs, hp, hd, hcont, hinv, hfar⟩ := hE'
  obtain ⟨-, -, hI⟩ := H.tAll.2.2.2.2 F E σ d
  obtain ⟨-, hIc, hIi⟩ := hI Φ hΦ
  have hBc : Continuous (_root_.PositivityTheory.SiegelWeilFormula.AStep.Bj_k d Φ p Ê j) :=
    (famCont U Ê hUo hd hcont _ hs j).sub (continuous_const.mul (continuous_const.mul hIc))
  have hBr : ∀ γ ∈ rat2 σ d.Y, ∀ g, _root_.PositivityTheory.SiegelWeilFormula.AStep.Bj_k d Φ p Ê j (γ * g) = _root_.PositivityTheory.SiegelWeilFormula.AStep.Bj_k d Φ p Ê j g := fun γ hγ g => by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.AStep.Bj_k, derivInv U Ê hUo _ hs γ g (fun z hz => hinv z hz γ hγ g) j, hIi γ hγ g]
  have hz := H.fourierZero F E σ d nb lam 𝓖 hc (_root_.PositivityTheory.SiegelWeilFormula.AStep.Bj_k d Φ p Ê j) hBc (fun β hβ g => hBr _ (_root_.PositivityTheory.SiegelWeilFormula.AStep.nbRat_k d hc β hβ) g) ?_
  · intro g; exact congrFun hz g
  · intro T g
    by_cases hT : IsND T
    · exact _root_.PositivityTheory.SiegelWeilFormula.AStep.ndZero_k H R hmn hΦ hv hE j hj hc hT g
    · obtain ⟨γ, hγ, T₀, T', hsub, hfc⟩ := (H.fcConj F E σ d L nb lam 𝓖 hc).1 T hT
      rw [hfc _ hBc hBr g]
      exact _root_.PositivityTheory.SiegelWeilFormula.AStep.deg_k H R L R' hmn hIH hΦ hv hE j hj hlow hc hsub _
theorem step_k (H : _root_.PositivityTheory.SiegelWeilFormula.AStep.Hyps_k) : _root_.PositivityTheory.SiegelWeilFormula.Step_k := by
  intro F E _ _ _ _ _ σ d R L R' hmn hIH Φ hΦ hv x
  have hK := H.polyKFin F E σ d R Φ hΦ ((H.vacK F E σ d R).2.1 hv)
  have hsec := H.secK F E σ d Φ hK
  obtain ⟨U, p, Ê, t, hE⟩ := H.eisWk F E σ d _ _ hsec (s0 d.m d.n)
  have hall : ∀ j ≤ p.rootMultiplicity (s0 d.m d.n), ∀ g, _root_.PositivityTheory.SiegelWeilFormula.AStep.Bj_k d Φ p Ê j g = 0 := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj
      refine _root_.PositivityTheory.SiegelWeilFormula.AStep.stepJ_k H R L R' hmn hIH hΦ hv hE j hj fun i hi g => ?_
      have := ih i hi (hi.le.trans hj) g
      simpa only [_root_.PositivityTheory.SiegelWeilFormula.AStep.Bj_k, pderiv_lt p _ i (lt_of_lt_of_le hi hj), zero_mul, sub_zero] using this
  obtain ⟨hUo, hR, hs, hp, hd, hcont, hinv, hfar⟩ := hE
  refine wrap U p (Ê · x) (fun z => d.eis (d.sec0 Φ) (s0 d.m d.n) z x) t _ _ hUo hR hs hp (hd x)
    (fun z hz => (hfar z hz).2 x) (fun j hj => ?_) ?_
  · have := hall j hj.le x
    simpa only [_root_.PositivityTheory.SiegelWeilFormula.AStep.Bj_k, pderiv_lt p _ j hj, zero_mul, sub_zero] using this
  · exact sub_eq_zero.1 (hall _ le_rfl x)
theorem stepOf_k : _root_.PositivityTheory.SiegelWeilFormula.StepOf_k := fun h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 =>
  _root_.PositivityTheory.SiegelWeilFormula.AStep.step_k ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25⟩
end PositivityTheory.SiegelWeilFormula.AStep
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKsplitSplitCut

section

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.KSplit
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem commW_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (x : d.G) (hx : d.cw w (inFrame d.b x) = 1) (y : GR d.n) :
    x * R.ι w y = R.ι w y * x := by
  exact _root_.PositivityTheory.SiegelWeilFormula.KSplitW.commW_k d R w x hx y
theorem iota_mem_K_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (y : GR d.n) (hy : InK (mR y)) : R.ι w y ∈ d.K := by
  exact _root_.PositivityTheory.SiegelWeilFormula.KSplitW.iota_mem_K_k d R w y hy
theorem kSplit_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (k : d.G) (hk : k ∈ d.K) :
    ∃ y : GR d.n, (R.ι w y)⁻¹ * k ∈ d.K ∧ d.cw w (inFrame d.b ((R.ι w y)⁻¹ * k)) = 1 := by
  exact _root_.PositivityTheory.SiegelWeilFormula.KSplitW.kSplit_k d R w k hk
theorem iota_isPar_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (q : GR d.n) (hq : (mR q).toBlocks₂₁ = 0) :
    ∃ t, IsPar (R.ι w q) t ∧ (absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) = ‖(mR q).toBlocks₁₁.det‖ ^ 2 := by
  exact _root_.PositivityTheory.SiegelWeilFormula.KSplitP.iota_isPar_k d R w q hq
theorem siegel_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {p : d.G} {t : GL (Fin d.n) (AE F E)} (hp : IsPar p t) :
    ∃ C : ℂ, ∀ Φ ∈ d.sch, d.l (d.om p Φ) = C * d.l Φ := by
  exact _root_.PositivityTheory.SiegelWeilFormula.KSplitP.siegel_k d hp
theorem T_zero_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (Φ : d.Fn) : d.T Φ 0 = d.l Φ := by
  exact _root_.PositivityTheory.SiegelWeilFormula.KSplitP.T_zero_k d Φ
theorem loc_zero_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) : R.loc w 0 = 0 := by
  exact _root_.PositivityTheory.SiegelWeilFormula.KSplitP.loc_zero_k d R w
theorem gSplit_of_k (hF : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (hAw : _root_.PositivityTheory.SiegelWeilFormula.AwayAct_k) : _root_.PositivityTheory.SiegelWeilFormula.GSplit_k := by
  intro F E _ _ _ _ _ σ d R w L hL Ψ hΨ φ hφ g
  obtain ⟨p, t, hp, k, hk, rfl⟩ := d.ok.hgt.iwa g
  obtain ⟨y, hk'K, hk'w⟩ := _root_.PositivityTheory.SiegelWeilFormula.KSplit.kSplit_k d R w k hk
  set k' := (R.ι w y)⁻¹ * k with hk'
  have hcomm := _root_.PositivityTheory.SiegelWeilFormula.KSplit.commW_k d R w k' hk'w
  obtain ⟨A, hA⟩ := hAw F E σ d R w k' hk'w
  have hΨi : d.Indep w Ψ := ((hF F E σ d R).2.1 w Ψ hΨ).2
  obtain ⟨C, hC⟩ := _root_.PositivityTheory.SiegelWeilFormula.KSplit.siegel_k d hp
  refine ⟨p * k', y, C * A Ψ 0, (absE F E (Matrix.GeneralLinearGroup.det t) : ℝ), absE_pos _, ?_,
    fun y' => ⟨?_, fun P => ?_⟩⟩
  · rw [mul_assoc, hcomm y, hk', mul_inv_cancel_left]
  · obtain ⟨q, k₀, rfl, hq, hk₀, hloc⟩ := Glob.locIwasawa y'
    obtain ⟨tq, hPq, habs⟩ := _root_.PositivityTheory.SiegelWeilFormula.KSplit.iota_isPar_k d R w q hq
    have e : p * k' * R.ι w (q * k₀) = (p * R.ι w q) * (R.ι w k₀ * k') := by
      rw [map_mul, mul_assoc p, ← mul_assoc k', hcomm q, mul_assoc (R.ι w q), hcomm k₀]
      simp only [mul_assoc]
    have hval := d.ok.hgt.val _ _ (isPar_mul hp hPq) _ ((d.K).mul_mem (_root_.PositivityTheory.SiegelWeilFormula.KSplit.iota_mem_K_k d R w k₀ hk₀) hk'K)
    have h0 : 0 ≤ d.a ((p * R.ι w q) * (R.ι w k₀ * k')) := by rw [hval]; exact NNReal.coe_nonneg _
    show ((d.a (p * k' * R.ι w (q * k₀))).toNNReal : ℝ) = _
    rw [e, Real.coe_toNNReal _ h0, hval, map_mul, map_mul, NNReal.coe_mul, habs, hloc]
  · have hsw := fP_sw P
    have hΞ := (hL y' (fP P) hsw).2 Ψ hΨi (φ P) (hφ P).1 (hφ P).2
    have hΞs : d.om (R.ι w y') (φ P) ∈ d.sch := d.ok.dbl.weil.2.1.pres _ _ (hφ P).1
    have h2 := (hA Ψ hΨi).2 _ (hL y' (fP P) hsw).1 _ hΞs hΞ
    have hs2 : d.om k' (d.om (R.ι w y') (φ P)) ∈ d.sch := d.ok.dbl.weil.2.1.pres _ _ hΞs
    unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.sec0
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hC _ hs2, ← _root_.PositivityTheory.SiegelWeilFormula.KSplit.T_zero_k, h2]
    simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, _root_.PositivityTheory.SiegelWeilFormula.KSplit.loc_zero_k]
    ring
end PositivityTheory.SiegelWeilFormula.KSplit
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilFinCore

section

@[expose] public section



section
noncomputable section
open GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Fin
theorem tTheta_k : _root_.PositivityTheory.SiegelWeilFormula.TTheta_k := _root_.PositivityTheory.SiegelWeilFormula.Tpar.tTheta_of_k (_root_.PositivityTheory.SiegelWeilFormula.tweyl.tthetaComm_k _root_.PositivityTheory.SiegelWeilFormula.TBij_k.tBij)
theorem tAll_of_k (hW : _root_.PositivityTheory.SiegelWeilFormula.TWeyl_k) : _root_.PositivityTheory.SiegelWeilFormula.TAll_k := ⟨_root_.PositivityTheory.SiegelWeilFormula.TBij_k.tBij, _root_.PositivityTheory.SiegelWeilFormula.Tpar.tPar_k, hW, _root_.PositivityTheory.SiegelWeilFormula.Fin.tTheta_k, _root_.PositivityTheory.SiegelWeilFormula.Tauto.thetaAuto_k GlobalTheory.T.siegel_set_unitary _root_.PositivityTheory.SiegelWeilFormula.Tpar.tPar_k _root_.PositivityTheory.SiegelWeilFormula.Fin.tTheta_k⟩
theorem thetaCoef_k : _root_.PositivityTheory.SiegelWeilFormula.ThetaCoef_k := _root_.PositivityTheory.SiegelWeilFormula.Tauto.thetaCoef_k GlobalTheory.T.siegel_set_unitary _root_.PositivityTheory.SiegelWeilFormula.TBij_k.tBij _root_.PositivityTheory.SiegelWeilFormula.Tpar.tPar_k _root_.PositivityTheory.SiegelWeilFormula.Fin.tTheta_k
theorem siegelWeilStd_of_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hLI : _root_.PositivityTheory.SiegelWeilFormula.LocInst_k) (hGD : _root_.PositivityTheory.SiegelWeilFormula.GIdil_k) (hKP : _root_.PositivityTheory.SiegelWeilFormula.KFinPoly_k) (hPK : _root_.PositivityTheory.SiegelWeilFormula.PolyKFin_k) (hLD : _root_.PositivityTheory.SiegelWeilFormula.LDEx_k)
    (hCT : _root_.PositivityTheory.SiegelWeilFormula.CTSplit_k) (hH : HolLead) : _root_.GlobalTheory.ThK.Dbl.SiegelWeilStd_k := by
  have hA : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties := _root_.PositivityTheory.SiegelWeilFormula.kfour.auxiliaryExistence_holds
  have hF : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k := _root_.PositivityTheory.SiegelWeilFormula.KFock.fockMem_k
  have hLo : _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k := _root_.PositivityTheory.SiegelWeilFormula.locOpEx_of_tAll_k hT
  have hGS : _root_.PositivityTheory.SiegelWeilFormula.GSplit_k := _root_.PositivityTheory.SiegelWeilFormula.KSplit.gSplit_of_k hF (_root_.PositivityTheory.SiegelWeilFormula.KAway.awayAct_of_tAll_k hT)
  have hVK : _root_.PositivityTheory.SiegelWeilFormula.VacK_k := _root_.PositivityTheory.SiegelWeilFormula.Avac.vacK_of_k hT hF hLo hLI (_root_.PositivityTheory.SiegelWeilFormula.KAway.finAct_of_tAll_k hT)
  have hW : _root_.PositivityTheory.SiegelWeilFormula.WhitK_k := _root_.PositivityTheory.SiegelWeilFormula.KWhit.whitK_of_k hT hA _root_.PositivityTheory.SiegelWeilFormula.Krd.rdEx_k hF hKP _root_.PositivityTheory.SiegelWeilFormula.Khead.secK_k _root_.PositivityTheory.SiegelWeilFormula.kunf.unfold_k whitGenLt _root_.PositivityTheory.SiegelWeilFormula.Fin.thetaCoef_k _root_.PositivityTheory.SiegelWeilFormula.kfour.lamBd_k hPK
  have hWE : _root_.PositivityTheory.SiegelWeilFormula.WhitEq_k :=
    _root_.PositivityTheory.SiegelWeilFormula.KWhit.whitEq_of_k hT hA _root_.PositivityTheory.SiegelWeilFormula.Krd.rdEx_k hF hKP _root_.PositivityTheory.SiegelWeilFormula.Khead.secK_k _root_.PositivityTheory.SiegelWeilFormula.kunf.unfold_k _root_.PositivityTheory.SiegelWeilFormula.Aeis.eisWk_k whitGenEq _root_.PositivityTheory.SiegelWeilFormula.Fin.thetaCoef_k _root_.PositivityTheory.SiegelWeilFormula.kfour.lamBd_k hPK
  have hWL : _root_.PositivityTheory.SiegelWeilFormula.WhitLow_k := _root_.PositivityTheory.SiegelWeilFormula.KWhit.whitLow_of_k hVK hT hA hF _root_.PositivityTheory.SiegelWeilFormula.Khead.secK_k _root_.PositivityTheory.SiegelWeilFormula.kunf.unfold_k _root_.PositivityTheory.SiegelWeilFormula.Aeis.eisWk_k whitGenLow _root_.PositivityTheory.SiegelWeilFormula.Fin.thetaCoef_k _root_.PositivityTheory.SiegelWeilFormula.kfour.lamBd_k hPK
  have hSt : _root_.PositivityTheory.SiegelWeilFormula.Step_k := _root_.PositivityTheory.SiegelWeilFormula.AStep.stepOf_k hH Holtb.holT hT _root_.PositivityTheory.SiegelWeilFormula.Fin.thetaCoef_k hA _root_.PositivityTheory.SiegelWeilFormula.kfour.coefEx_k hF (_root_.PositivityTheory.SiegelWeilFormula.KFock.liftEx_k hT.1) hLo hLI hGS hPK _root_.PositivityTheory.SiegelWeilFormula.Khead.secK_k
    _root_.PositivityTheory.SiegelWeilFormula.Aeis.eisWk_k _root_.PositivityTheory.SiegelWeilFormula.kfour.lamBd_k (_root_.PositivityTheory.SiegelWeilFormula.KSing.lamSing_of_k _root_.PositivityTheory.SiegelWeilFormula.kfour.coefEx_k _root_.PositivityTheory.SiegelWeilFormula.kfour.fourierZero_k _root_.PositivityTheory.SiegelWeilFormula.Krd.denseW_k hA) _root_.PositivityTheory.SiegelWeilFormula.kfour.fourierZero_k _root_.PositivityTheory.SiegelWeilFormula.kunf.unfold_k hWL hVK
    (_root_.PositivityTheory.SiegelWeilFormula.Avac.iwaQ_of'_k hT) hCT _root_.PositivityTheory.SiegelWeilFormula.Afc.uEx_k (_root_.PositivityTheory.SiegelWeilFormula.Afc.fcConj_of_k hA) _root_.PositivityTheory.SiegelWeilFormula.Afc.orbRes_k
  exact _root_.PositivityTheory.SiegelWeilFormula.Atop.siegelWeilStd_of_k AbsSt.absThm hT _root_.PositivityTheory.SiegelWeilFormula.Fin.thetaCoef_k hLo hLI hGS (_root_.PositivityTheory.SiegelWeilFormula.KSplit.gIinv_of_k hT hF) hGD hKP hPK _root_.PositivityTheory.SiegelWeilFormula.kunf.unfold_k hW hWE
    AbsSt.vacuum_generates_polynomials hLD hVK hSt
end PositivityTheory.SiegelWeilFormula.Fin
end
end
end
end
