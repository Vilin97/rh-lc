module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilActCut
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.FrameDil
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopMChar
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopRelPf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopStepMA
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopStepMVal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKrdPlace
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKsplitSplitP
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.DZTranspose
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.StepMA
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.IncMTranspose
import Development.WeilBound.ThetaLifts.LatticeBasics.IsCompactOfUnits
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.IncMTranspose
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.ContinuousInFrame
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAtopMainLe
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.CountableRationalPointsDoubled
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.CBDM
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ContSingle
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ExistsSigmaNe
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.PiMapConst
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.WMUnitary
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.MatrixOfUnipotentFrame

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.FrameDilK

section

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.CL
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem rEx_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (w : InfinitePlace F) : ∃ r : ℝ → GroundTheory.Global.IdeleGroup F,
    (∀ τ τ', r (τ + τ') = r τ * r τ') ∧ r 0 = 1 ∧
    (∀ τ, (GroundTheory.Global.IdeleGroup.ideleModule F (r τ) : ℝ) = Real.exp τ) ∧
    (∀ τ, piInf (d.B.emb w) ((r τ : AF F) • (1 : AE F E)) = (Real.exp τ : ℂ)) ∧
    (∀ τ w', w' ≠ w → piInf (d.B.emb w') ((r τ : AF F) • (1 : AE F E)) = 1) ∧
    (∀ τ, finOne F * (r τ : AF F) = finOne F) := by
  have := d.cm.1
  have hw : w.IsReal := IsTotallyReal.isReal w
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  let u : ℝ → ℝˣ := fun τ => ⟨Real.exp τ, Real.exp (-τ), by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero],
    by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]⟩
  let r : ℝ → GroundTheory.Global.IdeleGroup F := fun τ => GroundTheory.Global.IdeleGroup.infiniteEmbedding w (Units.map e.symm.toMonoidHom (u τ))
  have hu : ∀ τ τ', u (τ + τ') = u τ * u τ' := fun τ τ' => Units.ext (Real.exp_add τ τ')
  have hu0 : u 0 = 1 := Units.ext Real.exp_zero
  have hr1 : ∀ τ, ((r τ : AF F)).1 = GroundTheory.Global.IdeleGroup.infiniteAdeleSingle w (e.symm (Real.exp τ)) := fun τ => rfl
  have hr2 : ∀ τ, ((r τ : AF F)).2 = 1 := fun τ => rfl
  have hee : ∀ x : ℝ, InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (e.symm x) = x := fun x => e.apply_symm_apply x
  have hext : ∀ τ, InfinitePlace.Completion.extensionEmbedding w (e.symm (Real.exp τ)) = (Real.exp τ : ℂ) := by
    intro τ
    rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw, hee]
  refine ⟨r, fun τ τ' => by simp only [r, hu, map_mul], by simp only [r, hu0, map_one], fun τ => ?_, fun τ => ?_,
    fun τ w' hw' => ?_, fun τ => ?_⟩
  · rw [GroundTheory.Global.IdeleGroup.ideleModule_infiniteEmbedding, hw.mult_eq_one, pow_one]
    show ‖e.symm (Real.exp τ)‖ = _
    rw [← (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _), hee,
      Real.norm_of_nonneg (Real.exp_pos τ).le]
  · rw [St.piInf_smul, map_one, mul_one, hr1, GroundTheory.Global.IdeleGroup.infiniteAdeleSingle_apply, Pi.mulSingle_eq_same]
    exact hext τ
  · rw [St.piInf_smul, map_one, mul_one, hr1, GroundTheory.Global.IdeleGroup.infiniteAdeleSingle_apply, Pi.mulSingle_eq_of_ne hw', map_one]
  · refine Prod.ext ?_ ?_
    · show (0 : Ainf F) * _ = 0
      rw [zero_mul]
    · show (1 : Af F) * (r τ : AF F).2 = 1
      rw [hr2, mul_one]
theorem frame_dil_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (r : ℝ → GroundTheory.Global.IdeleGroup F)
    (hw : ∀ τ, piInf (d.B.emb w) ((r τ : AF F) • (1 : AE F E)) = (Real.exp τ : ℂ))
    (ho : ∀ τ w', w' ≠ w → piInf (d.B.emb w') ((r τ : AF F) • (1 : AE F E)) = 1)
    (hf : ∀ τ, finOne F * (r τ : AF F) = finOne F) (i₀ : Fin d.n) {τ : ℝ} {y : GR d.n}
    (hy : IsDil (Pi.single i₀ 1) τ y) :
    inFrame d.b (R.ι w y) = dM i₀ ((r τ : AF F) • (1 : AE F E)) ((r (-τ) : AF F) • (1 : AE F E)) := by
  have hζ0 : R.ζ ≠ 0 := Krd.zeta_ne R.hζ
  have hC : Matrix.fromBlocks (Matrix.diagonal fun j => (Real.exp (τ * (Pi.single i₀ 1 : Fin d.n → ℝ) j) : ℂ)) 0 0
      (Matrix.diagonal fun j => (Real.exp (-(τ * (Pi.single i₀ 1 : Fin d.n → ℝ) j)) : ℂ)) = dM i₀ (Real.exp τ : ℂ) (Real.exp (-τ) : ℂ) := by
    ext u v
    rw [dM_apply]
    rcases u with u | u <;> rcases v with v | v <;>
      simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
        Matrix.diagonal_apply, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, if_false, Matrix.zero_apply] <;>
      by_cases h : u = v <;> by_cases h' : u = i₀ <;> subst_vars <;> simp_all [Pi.single_apply]
  refine _root_.PositivityTheory.SiegelWeilFormula.Place.cw_ext_k d (fun w' => ?_) ?_
  · by_cases hw' : w' = w
    · subst hw'
      rw [R.cw_iota_pf w' y, hy, dZ_conj_diag hζ0, hC, _root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, dM_map, hw, hw]
    · rw [R.off_w w w' y hw', _root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, dM_map, ho τ w' hw', ho (-τ) w' hw']
      ext u v
      rw [dM_apply, Matrix.one_apply]
      split_ifs <;> rfl
  · rw [R.off_f w y]
    ext u v
    rw [Matrix.smul_apply, Matrix.smul_apply, dM_apply, Matrix.one_apply]
    have e : ∀ t, finOne F • ((r t : AF F) • (1 : AE F E)) = finOne F • (1 : AE F E) := fun t => by
      rw [smul_smul, hf]
    split_ifs <;> simp [e]
theorem par_dil_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (i₀ : Fin d.n) {τ : ℝ} {y : GR d.n}
    (hy : IsDil (Pi.single i₀ 1) τ y) :
    ∃ t, IsPar (R.ι w y) t ∧ (absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) = Real.exp (2 * τ) ∧
      (d.χ (Matrix.GeneralLinearGroup.det t) : ℂ) = 1 := by
  obtain ⟨t0, ht0⟩ := d.ok.frame.2
  set A : Matrix (Fin d.n) (Fin d.n) ℂ := Matrix.diagonal fun j => (Real.exp (τ * (Pi.single i₀ 1 : Fin d.n → ℝ) j) : ℂ) with hAdef
  set D : Matrix (Fin d.n) (Fin d.n) ℂ := Matrix.diagonal fun j => (Real.exp (-(τ * (Pi.single i₀ 1 : Fin d.n → ℝ) j)) : ℂ)
  have hy' : mR y = Matrix.fromBlocks A 0 0 D := hy
  obtain ⟨-, hA, -, hoA, hfA, -⟩ := R.frame_diag w y A D hy'
  have h21 : (mR y).toBlocks₂₁ = 0 := by rw [hy', Matrix.toBlocks_fromBlocks₂₁]
  obtain ⟨t, ht, habs⟩ := _root_.PositivityTheory.SiegelWeilFormula.KSplitP.iota_isPar_k d R w y h21
  have hdetA : A.det = (Real.exp τ : ℂ) := by
    rw [hAdef, Matrix.det_diagonal, Finset.prod_eq_single i₀ (fun j _ hj => by simp [Pi.single_eq_of_ne hj])
      (fun h => absurd (Finset.mem_univ _) h)]
    simp
  refine ⟨t, ht, ?_, ?_⟩
  · rw [habs, hy', Matrix.toBlocks_fromBlocks₁₁, hdetA, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos τ).le,
      ← Real.exp_nat_mul]
    norm_num
  · have ht1 := ((kunf.isPar_frame ht0 (R.ι w y) t).1 ht).2
    set P := (inFrame d.b (R.ι w y)).toBlocks₁₁ with hP
    have hcw : ∀ w', d.cw w' t.1 = d.cw w' (incM F t0.1) * d.cw w' P * d.cw w' (incM F (t0⁻¹).1) := by
      intro w'; rw [ht1]; simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, Matrix.map_mul]
    have hI : incM F t0.1 * incM F (t0⁻¹).1 = 1 := by
      rw [← kunf.incM_mul', Units.mul_inv]; ext i j; simp [incM, Matrix.one_apply]
    have hT : ∀ w', d.cw w' (incM F t0.1) * d.cw w' (incM F (t0⁻¹).1) = 1 := by
      intro w'; rw [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, _root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, ← Matrix.map_mul, hI, Matrix.map_one _ (map_zero _) (map_one _)]
    have ho : ∀ w', w' ≠ w → d.cw w' t.1 = 1 := fun w' h => by rw [hcw, (hoA w' h).1, Matrix.mul_one, hT]
    have hf : finOne F • t.1 = finOne F • (1 : Matrix (Fin d.n) (Fin d.n) (AE F E)) := by
      rw [ht1, ← Matrix.smul_mul, ← Matrix.mul_smul, hfA, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hI]
    have hdet : (d.cw w t.1).det = (Real.exp τ : ℂ) := by
      have hXY := congrArg Matrix.det (hT w)
      rw [Matrix.det_mul, Matrix.det_one] at hXY
      rw [hcw, Matrix.det_mul, Matrix.det_mul, hA, hdetA]
      linear_combination ((Real.exp τ : ℝ) : ℂ) * hXY
    rw [_root_.PositivityTheory.SiegelWeilFormula.RD_k.chi_det (d := d) w t _ rfl ho hf, hdet]
    exact d.chiW_pos w _ (Real.exp_pos τ)
end PositivityTheory.SiegelWeilFormula.Act.CL
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.PtExK

section

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Act.CL
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem ptEx'_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {ε : ℤˣ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0)
    {X : Type} [TopologicalSpace X] (M M' : X → Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E))
    (hM : Continuous M) (hM' : Continuous M') (h : ∀ c, M c * M' c = 1)
    (hu : ∀ c, (M c)ᵀ * kunf.jw d.n (((ε : ℤ) : AE F E)) * (M c).map (cA σ) = kunf.jw d.n (((ε : ℤ) : AE F E))) :
    ∃ f : X → d.G, Continuous f ∧ ∀ c, inFrame d.b (f c) = M c := by
  set B0 := incM F d.b.1 with hB0
  set Bi := incM F (d.b⁻¹).1 with hBi
  have e1 : B0 * Bi = 1 := GlobalTheory.EisBL.DoubledParabolic.incM_mul_inv d.b
  have e2 : Bi * B0 = 1 := GlobalTheory.EisBL.DoubledParabolic.incM_inv_mul d.b
  have h' : ∀ c, M' c * M c = 1 := fun c => mul_eq_one_comm.1 (h c)
  let U : X → GL (Fin d.n ⊕ Fin d.n) (AE F E) := fun c => ⟨B0 * M c * Bi, B0 * M' c * Bi, by
      calc B0 * M c * Bi * (B0 * M' c * Bi) = B0 * (M c * (Bi * B0) * M' c) * Bi := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [e2, Matrix.mul_one, h, Matrix.mul_one, e1], by
      calc B0 * M' c * Bi * (B0 * M c * Bi) = B0 * (M' c * (Bi * B0) * M c) * Bi := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [e2, Matrix.mul_one, h', Matrix.mul_one, e1]⟩
  have hU : ∀ c, U c ∈ UG (cA σ) (dbl (incM F d.Y.J)) := by
    intro c
    obtain ⟨x, hx⟩ := kunf.exists_of_frame (Y := d.Y) hε (M c) (M' c) (h c) (hu c)
    have hx1 : x.1 = U c := by
      apply Units.ext
      show mat2 x = B0 * M c * Bi
      rw [← hx]
      show mat2 x = B0 * (Bi * mat2 x * B0) * Bi
      calc mat2 x = (B0 * Bi) * mat2 x * (B0 * Bi) := by rw [e1, Matrix.one_mul, Matrix.mul_one]
        _ = _ := by simp only [Matrix.mul_assoc]
    exact hx1 ▸ x.2
  refine ⟨fun c => ⟨U c, hU c⟩, ?_, fun c => ?_⟩
  · refine continuous_induced_rng.2 ?_
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · exact (continuous_const.matrix_mul hM).matrix_mul continuous_const
    · exact (continuous_const.matrix_mul hM').matrix_mul continuous_const
  · show Bi * (B0 * M c * Bi) * B0 = M c
    calc Bi * (B0 * M c * Bi) * B0 = (Bi * B0) * M c * (Bi * B0) := by simp only [Matrix.mul_assoc]
      _ = M c := by rw [e2, Matrix.one_mul, Matrix.mul_one]
end PositivityTheory.SiegelWeilFormula.Act.CL
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.CLawExK

section

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Act
def CLawEx_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d),
  ∃ (w₁ : d.G) (cM : (Fin L.n → AE F E) × AF F → d.G) (κ : Measure ((Fin L.n → AE F E) × AF F)),
    _root_.PositivityTheory.SiegelWeilFormula.Act.CLaw_k R L w₁ cM κ ∧ w₁ ∈ rat2 σ d.Y ∧
    (∃ a b : E, a ≠ 0 ∧ b ≠ 0 ∧ inFrame d.b w₁ = 1 - Matrix.single (Sum.inl L.i₀) (Sum.inl L.i₀) 1 -
      Matrix.single (Sum.inr L.i₀) (Sum.inr L.i₀) 1 + Matrix.single (Sum.inl L.i₀) (Sum.inr L.i₀) (inclR (F := F) (AF F) a) +
      Matrix.single (Sum.inr L.i₀) (Sum.inl L.i₀) (inclR (F := F) (AF F) b)) ∧
    Continuous cM ∧ κ.IsAddHaarMeasure ∧
    ∃ δ : E, δ ≠ 0 ∧ ∀ c, ∃ A', inFrame d.b (cM c) = Matrix.fromBlocks (1 + ∑ j, Matrix.single L.i₀ (L.em j) (c.1 j))
      (Matrix.single L.i₀ L.i₀ (c.2 • inclR (F := F) (AF F) δ)) 0 A'
theorem cLawEx_k : _root_.PositivityTheory.SiegelWeilFormula.Act.CLawEx_k := by
  intro F E _ _ _ _ _ σ d R L
  have hε := R.hε
  have hem : ∀ j, L.em j ≠ L.i₀ := fun j => (L.rng (L.em j)).2 ⟨j, rfl⟩
  set e : AE F E := ((R.ε : ℤ) : AE F E) with he_def
  have hee : e * e = 1 := by
    rw [he_def, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  obtain ⟨δ, hδ0, hδ⟩ := CL.deltaEx' d.cm R.ε
  obtain ⟨κ, hκ, hsc⟩ := CL.measEx' (F := F) (E := E) L.n d.bs
  let M₀ : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E := CL.wM L.i₀ (1 : E) ((R.ε : ℤ) : E)
  let M₀' : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E := CL.wM L.i₀ ((R.ε : ℤ) : E) (1 : E)
  have hW : incM F M₀ = CL.wM L.i₀ (1 : AE F E) e := by
    show M₀.map _ = _
    rw [CL.wM_map, map_one, map_intCast]
  have hW' : incM F M₀' = CL.wM L.i₀ e (1 : AE F E) := by
    show M₀'.map _ = _
    rw [CL.wM_map, map_one, map_intCast]
  have hWW : incM F M₀ * incM F M₀' = 1 := by
    rw [hW, hW']; exact CL.wM_mul L.i₀ _ _ _ _ (one_mul 1) hee
  have hWu : (incM F M₀)ᵀ * kunf.jw d.n e * (incM F M₀).map (cA σ) = kunf.jw d.n e := by
    rw [hW]
    refine CL.wM_unitary L.i₀ (cA σ).toRingHom 1 e e ?_ ?_
    · simp only [AlgHom.toRingHom_eq_coe, map_one, mul_one, hee]
    · simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, he_def, map_intCast, one_mul]
  obtain ⟨w₁, hw₁⟩ := kunf.exists_of_frame hε (incM F M₀) (incM F M₀') hWW hWu
  have hw₁' : inFrame d.b w₁ = CL.wM L.i₀ (1 : AE F E) e := hw₁.trans hW
  set δ' : AE F E := inclR (F := F) (AF F) δ with hδ'
  let Mc : (Fin L.n → AE F E) × AF F → Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) := fun c =>
    CL.cB L.i₀ L.em c.1 (fun j => cA σ (c.1 j)) (c.2 • δ')
  let Mc' : (Fin L.n → AE F E) × AF F → Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) := fun c =>
    CL.cB L.i₀ L.em (-c.1) (-fun j => cA σ (c.1 j)) (-(c.2 • δ'))
  have hcont : ∀ s : AF F → AF F, Continuous s → ∀ t : (Fin L.n → AE F E) → (Fin L.n → AE F E), Continuous t →
      Continuous fun c : (Fin L.n → AE F E) × AF F =>
        CL.cB L.i₀ L.em (t c.1) (fun j => cA σ (t c.1 j)) (s c.2 • δ') := by
    intro s hs t ht
    refine Continuous.matrix_fromBlocks ?_ ?_ continuous_const ?_
    · exact continuous_const.add (continuous_finsetSum _ fun j _ =>
        cont_single _ _ ((continuous_apply j).comp (ht.comp continuous_fst)))
    · exact cont_single _ _ (Continuous.smul (f := fun c : (Fin L.n → AE F E) × AF F => s c.2) (g := fun _ => δ')
        (hs.comp continuous_snd) continuous_const)
    · exact continuous_const.sub (continuous_finsetSum _ fun j _ => cont_single _ _
        ((GlobalTheory.EisBL.DoubledGroupTopology.continuous_cA σ).comp ((continuous_apply j).comp (ht.comp continuous_fst))))
  have hMc : Continuous Mc := hcont id continuous_id id continuous_id
  have hMc' : Continuous Mc' := by
    have := hcont (fun a => -a) continuous_neg (fun u => -u) continuous_neg
    convert this using 2 with c
    simp only [Mc', neg_smul, Pi.neg_apply, map_neg]
    rfl
  have cA_inclR (x : E) : cA σ (inclR (F := F) (AF F) x) = inclR (F := F) (AF F) (σ x) := by
    show Algebra.TensorProduct.map (AlgHom.id (AF F) (AF F)) σ ((1 : AF F) ⊗ₜ[F] x) = (1 : AF F) ⊗ₜ[F] σ x
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  have cA_invol (z : AE F E) : cA σ (cA σ z) = z := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      show Algebra.TensorProduct.map (AlgHom.id (AF F) (AF F)) σ
        (Algebra.TensorProduct.map (AlgHom.id (AF F) (AF F)) σ (a ⊗ₜ[F] x)) = a ⊗ₜ[F] x
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgHom.id_apply, CL.sigma_sigma_cm d.cm]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have hcA_z : ∀ a : AF F, cA σ (a • δ') = -(e * (a • δ')) := by
    intro a
    rw [map_smul, hδ', cA_inclR δ, hδ, map_neg, map_mul, map_intCast, smul_neg, mul_smul_comm]
  obtain ⟨cM, hcMc, hcM⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.CL.ptEx'_k d hε Mc Mc' hMc hMc'
    (fun c => CL.cB_mul hem c.1 _ _) (fun c => CL.cB_unitary hem (cA σ).toRingHom
      cA_invol e hee c.1 (c.2 • δ') (hcA_z c.2))
  have hfr := fun x y => GlobalTheory.EisBL.DoubledParabolic.inFrame_mul (σ := σ) (Y := d.Y) d.b x y
  refine ⟨w₁, cM, κ, ⟨?_, ?_, ?_⟩, kunf.rat_of_inFrame hw₁, ⟨1, (R.ε : ℤ), one_ne_zero, ?_, ?_⟩, hcMc, hκ,
    ⟨δ, hδ0, fun c => ⟨_, hcM c⟩⟩⟩
  ·
    intro w τ y g hy
    obtain ⟨r, hr0, hr1, -, hrw, hro, hrf⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.CL.rEx_k d w
    apply kunf.inFrame_injective d.b
    rw [hfr, hfr, _root_.PositivityTheory.SiegelWeilFormula.Act.CL.frame_dil_k d R w r hrw hro hrf L.i₀ hy]
    exact CL.comm_dM L.i₀ _ (L.j_out g) _ _
  ·
    intro w τ y hy
    obtain ⟨r, hr0, hr1, -, hrw, hro, hrf⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.CL.rEx_k d w
    have hy' := CL.isDil_inv hy
    obtain ⟨t, ht, ha, hχ⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.CL.par_dil_k d R w L.i₀ hy'
    refine ⟨R.ι w y⁻¹, t, ht, by rw [ha]; ring_nf, hχ, ?_⟩
    apply kunf.inFrame_injective d.b
    rw [hfr, hfr, hw₁', _root_.PositivityTheory.SiegelWeilFormula.Act.CL.frame_dil_k d R w r hrw hro hrf L.i₀ hy, _root_.PositivityTheory.SiegelWeilFormula.Act.CL.frame_dil_k d R w r hrw hro hrf L.i₀ hy', neg_neg]
    exact CL.wM_dM L.i₀ _ _ _ _
  ·
    intro w τ y hy
    obtain ⟨r, hr0, hr1, hrm, hrw, hro, hrf⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.CL.rEx_k d w
    obtain ⟨sc, hsc1, hsc2⟩ := hsc (r (-τ))
    refine ⟨sc, fun c => ?_, ?_⟩
    · apply kunf.inFrame_injective d.b
      rw [hfr, hfr, hcM, hcM, _root_.PositivityTheory.SiegelWeilFormula.Act.CL.frame_dil_k d R w r hrw hro hrf L.i₀ hy]
      have hxy : ((r τ : AF F) • (1 : AE F E)) * ((r (-τ) : AF F) • (1 : AE F E)) = 1 := by
        rw [smul_mul_smul_comm, one_mul, ← Units.val_mul, ← hr0, add_neg_cancel, hr1]; simp
      rw [CL.cB_dM hem _ _ _ _ _ hxy, hsc1]
      congr 1
      simp only [Mc]
      congr 1
      · funext j; exact smul_one_mul _ _
      · funext j; rw [map_smul, smul_one_mul]
      · rw [mul_assoc, smul_one_mul, smul_one_mul, smul_assoc, mul_smul]
    · rw [hsc2, hrm, ← Real.exp_neg, neg_neg, ← Real.exp_nat_mul, ← _root_.PositivityTheory.SiegelWeilFormula.Atop.LD.n_succ_k L]
      congr 2
      push_cast; ring
  · simp [map_intCast]
  · rw [hw₁']; simp [CL.wM, map_intCast, map_one, he_def]
end PositivityTheory.SiegelWeilFormula.Act
end
end
end
end
