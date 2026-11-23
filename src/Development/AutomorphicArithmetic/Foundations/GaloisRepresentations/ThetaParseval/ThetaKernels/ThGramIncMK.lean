module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitDict
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.ThInclRInjective
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
import Mathlib.Topology.Sheaves.Init
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.ThMSymmApply
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.ThGramIncM

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitTheta

section

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KWhit
open PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem th_JR_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (η : E) :
    HeckeCharacterZeroLocus.SiegelWeilU.JR (AF F) (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) = inclR (F := F) (E := E) (AF F) η • (incM F d.A.J)ᵀ := by
  ext i j
  simp [HeckeCharacterZeroLocus.SiegelWeilU.JR, _root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k, incM, th_inclR_eq, Matrix.transpose_apply, map_mul]
theorem th_mem_iff_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {η : E} (hη : η ≠ 0) (g : GL (Fin d.m) (AE F E)) :
    g ∈ UG (cA σ) (incM F d.A.J) ↔ g ∈ HeckeCharacterZeroLocus.SiegelWeilU.HR (AF F) σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) := by
  have hc : IsUnit (inclR (F := F) (E := E) (AF F) η) := (Ne.isUnit hη).map _
  have hm : (g : Matrix (Fin d.m) (Fin d.m) (AE F E)).map (HeckeCharacterZeroLocus.SiegelWeilU.sigR (AF F) σ) =
      (g : Matrix (Fin d.m) (Fin d.m) (AE F E)).map (cA σ) := by
    ext i j; exact th_sigR_eq _
  show (g : Matrix (Fin d.m) (Fin d.m) (AE F E))ᵀ * incM F d.A.J * (g : Matrix (Fin d.m) (Fin d.m) (AE F E)).map (cA σ) =
      incM F d.A.J ↔ HeckeCharacterZeroLocus.SiegelWeilU.cT (HeckeCharacterZeroLocus.SiegelWeilU.sigR (AF F) σ) (g : Matrix (Fin d.m) (Fin d.m) (AE F E)) *
      HeckeCharacterZeroLocus.SiegelWeilU.JR (AF F) (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) * (g : Matrix (Fin d.m) (Fin d.m) (AE F E)) = HeckeCharacterZeroLocus.SiegelWeilU.JR (AF F) (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η)
  rw [_root_.PositivityTheory.SiegelWeilFormula.KWhit.th_JR_k, HeckeCharacterZeroLocus.SiegelWeilU.cT, hm]
  set L := (g : Matrix (Fin d.m) (Fin d.m) (AE F E))ᵀ * incM F d.A.J * (g : Matrix (Fin d.m) (Fin d.m) (AE F E)).map (cA σ)
  have hL : ((g : Matrix (Fin d.m) (Fin d.m) (AE F E)).map (cA σ))ᵀ *
      (inclR (F := F) (E := E) (AF F) η • (incM F d.A.J)ᵀ) * (g : Matrix (Fin d.m) (Fin d.m) (AE F E)) =
      inclR (F := F) (E := E) (AF F) η • Lᵀ := by
    simp only [L, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  rw [hL]
  constructor
  · intro h; rw [h]
  · intro h
    have h2 := congrArg (fun M => (hc.unit⁻¹ : (AE F E)ˣ) • M) h
    simp only [Units.smul_def, smul_smul] at h2
    have h3 : ((hc.unit⁻¹ : (AE F E)ˣ) : AE F E) * inclR (F := F) (E := E) (AF F) η = 1 := by
      exact hc.val_inv_mul
    rw [h3, one_smul, one_smul] at h2
    have := congrArg Matrix.transpose h2
    simpa using this
def thE_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {η : E} (hη : η ≠ 0) : UA σ d.A.J ≃* HeckeCharacterZeroLocus.SiegelWeilU.HA (AF F) σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) :=
  MulEquiv.subgroupCongr (Subgroup.ext (_root_.PositivityTheory.SiegelWeilFormula.KWhit.th_mem_iff_k d hη))
theorem thE_cont_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {η : E} (hη : η ≠ 0) : Continuous (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thE_k d hη) :=
  continuous_subtype_val.subtype_mk _
theorem thE_symm_cont_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {η : E} (hη : η ≠ 0) : Continuous (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thE_k d hη).symm :=
  continuous_subtype_val.subtype_mk _
end PositivityTheory.SiegelWeilFormula.KWhit
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThRatIffK

section

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KWhit
open PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def thM_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {η : E} (hη : η ≠ 0) : UA σ d.A.J ≃ᵐ HeckeCharacterZeroLocus.SiegelWeilU.HA (AF F) σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) :=
  (Homeomorph.mk (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thE_k d hη).toEquiv (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thE_cont_k d hη) (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thE_symm_cont_k d hη)).toMeasurableEquiv
def thE'_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {η : E} (hη : η ≠ 0) (g : UA σ d.A.J) : HeckeCharacterZeroLocus.SiegelWeilU.HR (AF F) σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) := _root_.PositivityTheory.SiegelWeilFormula.KWhit.thE_k d hη g
theorem th_rat_iff_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {η : E} (hη : η ≠ 0) (g : UA σ d.A.J) :
    g ∈ ratU σ d.A.J ↔ _root_.PositivityTheory.SiegelWeilFormula.KWhit.thE'_k d hη g ∈ HeckeCharacterZeroLocus.SiegelWeilU.HFinIn (AF F) σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) := by
  rw [ratU, Subgroup.mem_subgroupOf, MonoidHom.mem_range, HeckeCharacterZeroLocus.SiegelWeilU.HFinIn, Subgroup.mem_subgroupOf,
    HeckeCharacterZeroLocus.SiegelWeilU.HFin, Subgroup.mem_map]
  constructor
  · rintro ⟨γ, hγ⟩
    refine ⟨γ, ?_, hγ⟩
    have hg : (g.1 : GL (Fin d.m) (AE F E)) ∈ HeckeCharacterZeroLocus.SiegelWeilU.HR (AF F) σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) := (_root_.PositivityTheory.SiegelWeilFormula.KWhit.th_mem_iff_k d hη g.1).1 g.2
    rw [← hγ] at hg
    change HeckeCharacterZeroLocus.SiegelWeilU.cT (σ : E →+* E) (γ : Matrix (Fin d.m) (Fin d.m) E) * _root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η * (γ : Matrix (Fin d.m) (Fin d.m) E) =
      _root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η
    apply Matrix.map_injective (th_inclR_injective (F := F) (E := E))
    change HeckeCharacterZeroLocus.SiegelWeilU.cT (HeckeCharacterZeroLocus.SiegelWeilU.sigR (AF F) σ) ((γ : Matrix (Fin d.m) (Fin d.m) E).map (inclR (F := F) (E := E) (AF F))) *
      HeckeCharacterZeroLocus.SiegelWeilU.JR (AF F) (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) * (γ : Matrix (Fin d.m) (Fin d.m) E).map (inclR (F := F) (E := E) (AF F)) =
      HeckeCharacterZeroLocus.SiegelWeilU.JR (AF F) (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) at hg
    dsimp only
    rw [Matrix.map_mul, Matrix.map_mul, th_cT_map]
    exact hg
  · rintro ⟨γ, -, hγ⟩
    exact ⟨γ, hγ⟩
def thR_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {η : E} (hη : η ≠ 0) : HeckeCharacterZeroLocus.SiegelWeilU.HFinIn (AF F) σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) ≃ ratU σ d.A.J where
  toFun h := ⟨(_root_.PositivityTheory.SiegelWeilFormula.KWhit.thE_k d hη).symm h.1, (_root_.PositivityTheory.SiegelWeilFormula.KWhit.th_rat_iff_k d hη _).2
    (by have e1 : _root_.PositivityTheory.SiegelWeilFormula.KWhit.thE'_k d hη ((_root_.PositivityTheory.SiegelWeilFormula.KWhit.thE_k d hη).symm h.1) = h.1 := (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thE_k d hη).apply_symm_apply h.1
        rw [e1]; exact h.2)⟩
  invFun g := ⟨_root_.PositivityTheory.SiegelWeilFormula.KWhit.thE'_k d hη g.1, (_root_.PositivityTheory.SiegelWeilFormula.KWhit.th_rat_iff_k d hη _).1 g.2⟩
  left_inv h := Subtype.ext ((_root_.PositivityTheory.SiegelWeilFormula.KWhit.thE_k d hη).apply_symm_apply h.1)
  right_inv g := Subtype.ext ((_root_.PositivityTheory.SiegelWeilFormula.KWhit.thE_k d hη).symm_apply_apply g.1)
theorem th_haar_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {η : E} (hη : η ≠ 0) :
    HeckeCharacterZeroLocus.SiegelWeilU.IsHaarH F E σ d.m (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) (d.μ.map (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thM_k d hη)) := by
  have := d.ok.haar
  exact th_haar_map d.μ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thE_k d hη) (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thE_cont_k d hη) (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thE_symm_cont_k d hη)
theorem th_fd_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {η : E} (hη : η ≠ 0) :
    HeckeCharacterZeroLocus.SiegelWeilU.IsFDH F E σ d.m (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) (d.μ.map (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thM_k d hη)) (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thM_k d hη '' d.D) := by
  refine d.ok.dom.image_of_equiv (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thM_k d hη).toEquiv ⟨(_root_.PositivityTheory.SiegelWeilFormula.KWhit.thM_k d hη).symm.measurable.aemeasurable, ?_⟩ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thR_k d hη) ?_
  · change Measure.map (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thM_k d hη).symm (Measure.map (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thM_k d hη) d.μ) ≪ d.μ
    rw [MeasurableEquiv.map_symm_map]
  · intro h x
    rfl
end PositivityTheory.SiegelWeilFormula.KWhit
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThGramIncMK

section

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KWhit
open PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem th_gram_incM_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (X : Matrix (Fin d.m) (Fin d.n) E) :
    d.gram (incM F X) (incM F X) = incM F (Xᵀ * d.A.J * X.map σ) := by
  have h1 : (incM F X).map (cA σ) = incM F (X.map σ) := by
    ext i j; simp only [incM, Matrix.map_apply]; exact th_cA_incl _
  rw [_root_.PositivityTheory.SiegelWeilFormula.SD_k.gram, h1]
  simp only [incM, Matrix.transpose_map, Matrix.map_mul]
theorem th_gramE_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (η : E) (X : Matrix (Fin d.m) (Fin d.n) E) :
    HeckeCharacterZeroLocus.SiegelWeilU.gramE σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) Xᵀ = η • (Xᵀ * d.A.J * X.map σ)ᵀ := by
  ext a b
  simp only [HeckeCharacterZeroLocus.SiegelWeilU.gramE, HeckeCharacterZeroLocus.SiegelWeilU.hE, HeckeCharacterZeroLocus.SiegelWeilU.hform, _root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k, Matrix.transpose_apply,
    Matrix.smul_apply, Matrix.mul_apply, Matrix.map_apply, smul_eq_mul, RingHom.coe_coe]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring
theorem th_gram_iff_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {η : E} (hη : η ≠ 0) (T₀ : Matrix (Fin d.n) (Fin d.n) E)
    (X : Matrix (Fin d.m) (Fin d.n) E) :
    d.gram (incM F X) (incM F X) = (-2 : ℤ) • incM F T₀ ↔ HeckeCharacterZeroLocus.SiegelWeilU.gramE σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) Xᵀ = Td η T₀ := by
  have hs : ((-2 : ℤ) • incM F T₀ : Matrix (Fin d.n) (Fin d.n) (AE F E)) = incM F ((-2 : ℤ) • T₀) := by
    ext i j; simp only [incM, Matrix.map_apply, Matrix.smul_apply, map_zsmul]
  rw [_root_.PositivityTheory.SiegelWeilFormula.KWhit.th_gram_incM_k, _root_.PositivityTheory.SiegelWeilFormula.KWhit.th_gramE_k, Td, hs]
  constructor
  · intro h
    rw [th_incM_injective h]
    ext i j
    simp only [Matrix.smul_apply, Matrix.transpose_apply]
    simp only [zsmul_eq_mul, smul_eq_mul]; push_cast; ring
  · intro h
    congr 1
    ext i j
    have := congrFun (congrFun h j) i
    simp only [Matrix.smul_apply, Matrix.transpose_apply] at this ⊢
    simp only [zsmul_eq_mul, smul_eq_mul] at this ⊢
    push_cast at this ⊢
    apply mul_left_cancel₀ hη
    rw [this]; ring
theorem th_toMx_act_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (M : GL (Fin d.m) (AE F E)) (X : Matrix (Fin d.m) (Fin d.n) E) :
    toMx (HeckeCharacterZeroLocus.SiegelWeilU.actTup (AF F) M (HeckeCharacterZeroLocus.SiegelWeilU.ratTup (AF F) Xᵀ)) =
      (M : Matrix (Fin d.m) (Fin d.m) (AE F E)) * incM F X := by
  ext a j
  simp only [toMx, HeckeCharacterZeroLocus.SiegelWeilU.actTup, HeckeCharacterZeroLocus.SiegelWeilU.ratTup, Matrix.of_apply, Matrix.mulVec, dotProduct,
    Matrix.mul_apply, incM, Matrix.map_apply, Matrix.transpose_apply, th_inclR_eq]
theorem thetaDict_k : _root_.PositivityTheory.SiegelWeilFormula.KWhit.ThetaDict_k := by
  intro F E _ _ _ _ _ σ d η hη _
  refine ⟨d.μ.map (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thM_k d hη), _root_.PositivityTheory.SiegelWeilFormula.KWhit.thM_k d hη '' d.D, _root_.PositivityTheory.SiegelWeilFormula.KWhit.th_haar_k d hη, _root_.PositivityTheory.SiegelWeilFormula.KWhit.th_fd_k d hη, ?_⟩
  intro T T₀ hT Φ _
  rw [_root_.PositivityTheory.SiegelWeilFormula.SD_k.orb, setAverage_eq, HeckeCharacterZeroLocus.SiegelWeilU.meanC, MeasurableEquiv.map_apply, (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thM_k d hη).preimage_image,
    (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thM_k d hη).restrict_map, (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thM_k d hη).preimage_image, integral_map_equiv, measureReal_def]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun g => ?_)
  simp only [HeckeCharacterZeroLocus.SiegelWeilU.thetaS]
  let e : {X : Matrix (Fin d.m) (Fin d.n) E // d.gram (incM F X) (incM F X) = (-2 : ℤ) • T.1.1} ≃
      {X : Fin d.n → Fin d.m → E | HeckeCharacterZeroLocus.SiegelWeilU.gramE σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) X = Td η T₀} :=
    { toFun := fun X => ⟨X.1ᵀ, (_root_.PositivityTheory.SiegelWeilFormula.KWhit.th_gram_iff_k d hη T₀ X.1).1 (hT ▸ X.2)⟩
      invFun := fun Y => ⟨Matrix.transpose (Y.1 : Matrix (Fin d.n) (Fin d.m) E), by
        rw [hT]; exact (_root_.PositivityTheory.SiegelWeilFormula.KWhit.th_gram_iff_k d hη T₀ _).2 Y.2⟩
      left_inv := fun X => Subtype.ext (Matrix.transpose_transpose _)
      right_inv := fun Y => Subtype.ext (Matrix.transpose_transpose (Y.1 : Matrix (Fin d.n) (Fin d.m) E)) }
  rw [← e.tsum_eq]
  refine tsum_congr fun X => ?_
  simp only [e, Equiv.coe_fn_mk]
  rw [_root_.PositivityTheory.SiegelWeilFormula.KWhit.th_toMx_act_k]
  rfl
end PositivityTheory.SiegelWeilFormula.KWhit
end
end
end
end
