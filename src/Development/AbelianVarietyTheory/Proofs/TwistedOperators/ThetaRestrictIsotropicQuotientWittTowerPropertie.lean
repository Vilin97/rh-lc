module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaFunctionIsotropicRestrictionNeZero
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
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFunctionsSquareIntegrableHeisenbergUnitary
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictionIsotropicSplitSmoothRealPointsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSquareIntegrable
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaFunctionIsotropicRestrictionNeZeroStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
open scoped ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_thetaFunction_isotropicRestriction_ne_zero : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → (∀ (y y' : Mx D W.rank r) (x x' : WO V' W), symplOH V W (isoPart V W C y + midPart V V' W B x) (isoPart V W C y' + midPart V V' W B x') = symplOH V' W x x') → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∃ f, IsThetaFunO ψ V W f ∧ res V V' W C B μ 𝓨 f ≠ 0 := by
  first | exact @GlobalTheory.TowerResNonzero.exists_res_ne_zero | exact GlobalTheory.TowerResNonzero.exists_res_ne_zero | (intros; apply GlobalTheory.TowerResNonzero.exists_res_ne_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymplecticFormIsotropicPartAddMiddlePart

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
open scoped ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TowerForm

variable {D : D7}

def ad {m n : ℕ} (A : Mx D m n) : Mx D n m := Formalism.UG.cT (cA D) A

theorem ad_mul {l m n : ℕ} (A : Mx D l m) (B : Mx D m n) :
    ad (HMul.hMul A B : Mx D l n) = HMul.hMul (ad B) (ad A) := by
  unfold ad Formalism.UG.cT
  rw [Matrix.map_mul, Matrix.transpose_mul]

theorem cA_incA_sig (e : D.host.E) : cA D (incA D e) = incA D (D.sp.cm.sig e) := by
  simp only [cA, sigR, incA, inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul, map_one]

theorem ad_map {m n : ℕ} (A : Matrix (Fin m) (Fin n) D.host.E) :
    ad (A.map (incA D) : Mx D m n) = (adj D A).map (incA D) := by
  unfold ad adj Formalism.UG.cT
  ext i j
  simp only [Matrix.transpose_apply, Matrix.map_apply, cA_incA_sig]
  rfl

theorem adj_mul {l m n : ℕ} (A : Matrix (Fin l) (Fin m) D.host.E) (B : Matrix (Fin m) (Fin n) D.host.E) :
    adj D (A * B) = adj D B * adj D A := by
  unfold adj Formalism.UG.cT
  rw [Matrix.map_mul, Matrix.transpose_mul]

theorem adj_adj {m n : ℕ} (A : Matrix (Fin m) (Fin n) D.host.E) : adj D (adj D A) = A := by
  unfold adj Formalism.UG.cT
  ext i j
  simp only [Matrix.transpose_apply, Matrix.map_apply]
  exact star_star (A i j)

theorem adj_gram (V : HSp D) : adj D V.gram = V.gram := by
  unfold adj Formalism.UG.cT
  ext i j
  simp only [Matrix.transpose_apply, Matrix.map_apply]
  exact GlobalTheory.LatVac.gram_star V j i

theorem adj_gram_inv (V : HSp D) : adj D V.gram⁻¹ = V.gram⁻¹ := by
  have hu := GlobalTheory.LatVac.gram_det_isUnit V
  symm
  apply Matrix.inv_eq_left_inv
  calc adj D V.gram⁻¹ * V.gram = adj D V.gram⁻¹ * adj D V.gram := by rw [adj_gram]
    _ = adj D (V.gram * V.gram⁻¹) := (adj_mul _ _).symm
    _ = 1 := by
      rw [Matrix.mul_nonsing_inv (h := hu)]
      unfold adj Formalism.UG.cT
      simp

theorem hO_eq_trace (S T : HSp D) (x y : WO S T) :
    hO S T x y = Matrix.trace ((S.gram⁻¹.map (incA D) * ad y) * T.gram.map (incA D) * x) := by
  unfold hO
  rw [Matrix.mul_assoc, Matrix.mul_assoc]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, ad, Formalism.UG.cT, Matrix.transpose_apply,
    Matrix.map_apply, Finset.mul_sum, mul_assoc]

theorem hO_add_left (S T : HSp D) (x x' y : WO S T) : hO S T (x + x') y = hO S T x y + hO S T x' y := by
  unfold hO
  simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem hO_add_right (S T : HSp D) (x y y' : WO S T) : hO S T x (y + y') = hO S T x y + hO S T x y' := by
  unfold hO
  simp only [Matrix.add_apply, map_add (f := _), mul_add, add_mul, Finset.sum_add_distrib]

theorem hO_mul_mul (V W : HSp D) {m n : ℕ} (y₁ : Mx D W.rank m) (y₂ : Mx D W.rank n)
    (P₁ : Matrix (Fin m) (Fin V.rank) D.host.E) (P₂ : Matrix (Fin n) (Fin V.rank) D.host.E) :
    hO V W (HMul.hMul y₁ (P₁.map (incA D))) (HMul.hMul y₂ (P₂.map (incA D))) =
      Matrix.trace (ad y₂ * W.gram.map (incA D) * y₁ * (P₁ * V.gram⁻¹ * adj D P₂).map (incA D)) := by
  rw [hO_eq_trace, ad_mul, ad_map, Matrix.map_mul, Matrix.map_mul]
  have key := Matrix.trace_mul_comm (V.gram⁻¹.map (incA D) * (adj D P₂).map (incA D))
    (ad y₂ * W.gram.map (incA D) * y₁ * P₁.map (incA D))
  simpa only [Matrix.mul_assoc] using key

theorem adj_zero {m n : ℕ} : adj D (0 : Matrix (Fin m) (Fin n) D.host.E) = 0 := by
  unfold adj Formalism.UG.cT
  simp

section Split

variable {V V' W : HSp D} {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E}
  {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E}

theorem coef_iso_iso (hs : IsIsoSplit V V' C B) :
    adj D C * V.gram * V.gram⁻¹ * adj D (adj D C * V.gram) = 0 := by
  have hC : adj D C * V.gram * C = 0 := hs.frame.2.2
  rw [adj_mul, adj_adj, adj_gram, Matrix.mul_nonsing_inv_cancel_right (h := GlobalTheory.LatVac.gram_det_isUnit V),
    ← Matrix.mul_assoc]
  exact hC

theorem coef_iso_mid (hs : IsIsoSplit V V' C B) :
    adj D C * V.gram * V.gram⁻¹ * adj D (V'.gram⁻¹ * adj D B * V.gram) = 0 := by
  rw [adj_mul, adj_mul, adj_adj, adj_gram, adj_gram_inv,
    Matrix.mul_nonsing_inv_cancel_right (h := GlobalTheory.LatVac.gram_det_isUnit V), ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    hs.orth, Matrix.zero_mul]

theorem coef_mid_iso (hs : IsIsoSplit V V' C B) :
    V'.gram⁻¹ * adj D B * V.gram * V.gram⁻¹ * adj D (adj D C * V.gram) = 0 := by
  have hBC : adj D B * (V.gram * C) = 0 := by
    have h := congrArg (adj D) hs.orth
    rwa [adj_mul, adj_mul, adj_adj, adj_gram, adj_zero] at h
  rw [adj_mul, adj_adj, adj_gram, Matrix.mul_nonsing_inv_cancel_right (h := GlobalTheory.LatVac.gram_det_isUnit V),
    Matrix.mul_assoc, hBC, Matrix.mul_zero]

theorem coef_mid_mid (hs : IsIsoSplit V V' C B) :
    V'.gram⁻¹ * adj D B * V.gram * V.gram⁻¹ * adj D (V'.gram⁻¹ * adj D B * V.gram) = V'.gram⁻¹ := by
  rw [adj_mul, adj_mul, adj_adj, adj_gram, adj_gram_inv,
    Matrix.mul_nonsing_inv_cancel_right (h := GlobalTheory.LatVac.gram_det_isUnit V)]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (adj D B), ← Matrix.mul_assoc (adj D B * V.gram), hs.isom,
    Matrix.mul_nonsing_inv (h := GlobalTheory.LatVac.gram_det_isUnit V'), Matrix.mul_one]

theorem trace_swap {m n : ℕ} (Z : Mx D m m) (A : Mx D m n) (Y : Mx D n n) (X : Mx D n m) :
    Matrix.trace (Z * A * Y * X) = Matrix.trace (A * Y * X * Z) := by
  have key := Matrix.trace_mul_comm Z (A * Y * X)
  simpa only [Matrix.mul_assoc] using key

theorem hO_isoPart_add_midPart (hs : IsIsoSplit V V' C B) (y y' : Mx D W.rank r) (x x' : WO V' W) :
    hO V W (isoPart V W C y + midPart V V' W B x) (isoPart V W C y' + midPart V V' W B x') = hO V' W x x' := by
  rw [hO_add_left, hO_add_right, hO_add_right]
  unfold isoPart midPart
  rw [hO_mul_mul, hO_mul_mul, hO_mul_mul, hO_mul_mul, coef_iso_iso hs, coef_iso_mid hs, coef_mid_iso hs,
    coef_mid_mid hs]
  simp only [Matrix.map_zero, map_zero, Matrix.mul_zero, Matrix.trace_zero, zero_add]
  rw [hO_eq_trace, trace_swap]

end Split

theorem symplOH_isoPart_add_midPart : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ (y y' : Mx D W.rank r) (x x' : WO V' W),
    symplOH V W (isoPart V W C y + midPart V V' W B x) (isoPart V W C y' + midPart V V' W B x') = symplOH V' W x x' := by
  intro D V V' W r C B hs y y' x x'
  unfold symplOH symplO
  rw [hO_isoPart_add_midPart hs]

end GlobalTheory.TowerForm

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymplecticFormIsotropicPartAddMiddlePartStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
open scoped ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.symplecticForm_isotropicPart_add_middlePart : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ (y y' : Mx D W.rank r) (x x' : WO V' W), symplOH V W (isoPart V W C y + midPart V V' W B x) (isoPart V W C y' + midPart V V' W B x') = symplOH V' W x x' := by
  first | exact @GlobalTheory.TowerForm.symplOH_isoPart_add_midPart | exact GlobalTheory.TowerForm.symplOH_isoPart_add_midPart | (intros; apply GlobalTheory.TowerForm.symplOH_isoPart_add_midPart <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictIsotropicQuotientWittTowerPropertie

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
open scoped ContDiff Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TowerRestrict

variable {D : D7}

section Maps
variable {V V' W : HSp D} {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E)

theorem isoPart_add (y y' : Mx D W.rank r) : isoPart V W C (y + y') = isoPart V W C y + isoPart V W C y' :=
  Matrix.add_mul _ _ _

theorem isoPart_zero : isoPart V W C (0 : Mx D W.rank r) = 0 := Matrix.zero_mul _

theorem midPart_add (x x' : WO V' W) : midPart V V' W B (x + x') = midPart V V' W B x + midPart V V' W B x' :=
  Matrix.add_mul _ _ _

theorem midPart_zero : midPart V V' W B (0 : WO V' W) = 0 := Matrix.zero_mul _

theorem continuous_isoPart : Continuous (isoPart V W C : Mx D W.rank r → WO V W) :=
  continuous_id.matrix_mul continuous_const

theorem continuous_midPart : Continuous (midPart V V' W B : WO V' W → WO V W) :=
  continuous_id.matrix_mul continuous_const

theorem isoPart_rat {γ : Mx D W.rank r} (h : γ ∈ ratMx D W.rank r) : isoPart V W C γ ∈ ratL W V := by
  obtain ⟨γ₀, rfl⟩ := h
  exact ⟨γ₀ * (adj D C * V.gram), by
    show (γ₀ * (adj D C * V.gram)).map (incA D) = _
    rw [Matrix.map_mul]; rfl⟩

theorem midPart_ratW (γ : Matrix (Fin W.rank) (Fin V'.rank) D.host.E) :
    midPart V V' W B (ratW W V' γ) = ratW W V (γ * (V'.gram⁻¹ * adj D B * V.gram)) := by
  unfold midPart ratW
  simp only [Matrix.map_mul]

theorem midPart_infPart {u : WO V' W} (hu : u.map (infPart D) = 0) : (midPart V V' W B u).map (infPart D) = 0 := by
  unfold midPart
  rw [Matrix.map_mul, hu, Matrix.zero_mul]

def midHom : WO V' W →+ WO V W where
  toFun := midPart V V' W B
  map_zero' := midPart_zero B
  map_add' := midPart_add B

end Maps

section Shift
variable {m n : ℕ}

theorem lattice_Mx (D : D7) (m n : ℕ) : IsTopologicalAddGroup (Mx D m n) ∧ LocallyCompactSpace (Mx D m n) ∧
    SecondCountableTopology (Mx D m n) ∧ T2Space (Mx D m n) ∧ DiscreteTopology (ratMx D m n) ∧
    ∃ K : Set (Mx D m n), IsCompact K ∧ ∀ x : Mx D m n, ∃ γ ∈ ratMx D m n, γ + x ∈ K :=
  GlobalTheory.AdelicMatrixLattice.lattice D (Examples₂.posSpace Examples₂.star_isIntegral m) (Examples₂.posSpace Examples₂.star_isIntegral n)

theorem setIntegral_add_right {μ : Measure (Mx D m n)} {𝓨 : Set (Mx D m n)} (h : IsCovolOne (ratMx D m n) μ 𝓨)
    (φ : Mx D m n → ℂ) (hφ : ∀ γ ∈ ratMx D m n, ∀ a, φ (γ + a) = φ a) (b : Mx D m n) :
    ∫ a in 𝓨, φ (a + b) ∂μ = ∫ a in 𝓨, φ a ∂μ := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := lattice_Mx D m n
  have : BorelSpace (Mx D m n) := ⟨rfl⟩
  have : Countable (ratMx D m n) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  obtain ⟨hμ, h𝓨, -⟩ := h
  have e1 : ∫ a in 𝓨, φ (a + b) ∂μ = ∫ a in b +ᵥ 𝓨, φ a ∂μ := by
    rw [← Set.image_vadd]
    simp only [vadd_eq_add]
    rw [(measurePreserving_add_left μ b).setIntegral_image_emb (MeasurableEquiv.addLeft b).measurableEmbedding]
    simp only [add_comm b]
  rw [e1]
  exact (h𝓨.vadd_of_comm b).setIntegral_eq h𝓨 fun γ a => hφ γ γ.2 a

end Shift

section Main
variable {V V' W : HSp D} {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E}
  {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E} {ψ : AddChar (AF D.host.F) ℂ}

theorem sympl_mid (hs : IsIsoSplit V V' C B) (y : Mx D W.rank r) (x x₀ : WO V' W) :
    symplOH V W (isoPart V W C y + midPart V V' W B x) (midPart V V' W B x₀) = symplOH V' W x x₀ := by
  have := GlobalTheory.T.symplecticForm_isotropicPart_add_middlePart D V V' W r C B hs y 0 x x₀
  rwa [isoPart_zero, zero_add] at this

theorem sympl_iso (hs : IsIsoSplit V V' C B) (y y₀ : Mx D W.rank r) (x : WO V' W) :
    symplOH V W (isoPart V W C y + midPart V V' W B x) (isoPart V W C y₀) = 0 := by
  have := GlobalTheory.T.symplecticForm_isotropicPart_add_middlePart D V V' W r C B hs y y₀ x 0
  rwa [midPart_zero, add_zero, GlobalTheory.ThetaSquare.symplOH_zero_right] at this

theorem sympl_mid_left (hs : IsIsoSplit V V' C B) (y : Mx D W.rank r) (x x₀ : WO V' W) :
    symplOH V W (midPart V V' W B x₀) (isoPart V W C y + midPart V V' W B x) = symplOH V' W x₀ x := by
  have := GlobalTheory.T.symplecticForm_isotropicPart_add_middlePart D V V' W r C B hs 0 y x₀ x
  rwa [isoPart_zero, zero_add] at this

theorem sympl_iso_left (hs : IsIsoSplit V V' C B) (y y₀ : Mx D W.rank r) (x : WO V' W) :
    symplOH V W (isoPart V W C y₀) (isoPart V W C y + midPart V V' W B x) = 0 := by
  have := GlobalTheory.T.symplecticForm_isotropicPart_add_middlePart D V V' W r C B hs y₀ y 0 x
  rwa [midPart_zero, add_zero, GlobalTheory.ThetaSquare.symplOH_zero_left] at this

theorem periodic_iso (hs : IsIsoSplit V V' C B) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) (x : WO V' W)
    (γ : Mx D W.rank r) (hγ : γ ∈ ratMx D W.rank r) (y : Mx D W.rank r) :
    f (isoPart V W C (γ + y) + midPart V V' W B x) = f (isoPart V W C y + midPart V V' W B x) := by
  obtain ⟨γ₀, hγ₀⟩ := isoPart_rat (V := V) C hγ
  have e := hf.quasi γ₀ (isoPart V W C y + midPart V V' W B x)
  change ratW W V γ₀ = isoPart V W C γ at hγ₀
  rw [hγ₀, sympl_iso_left hs, neg_zero, ψ.map_zero_eq_one, one_mul, ← add_assoc, ← isoPart_add] at e
  exact e

theorem res_heis_mid (hs : IsIsoSplit V V' C B) (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r))
    (f : WO V W → ℂ) (x₀ : WO V' W) :
    res V V' W C B μ 𝓨 (heisO ψ V W (midPart V V' W B x₀) f) = heisO ψ V' W x₀ (res V V' W C B μ 𝓨 f) := by
  funext x
  simp only [res, heisO]
  simp only [sympl_mid hs, add_assoc, ← midPart_add]
  exact integral_const_mul _ _

theorem res_heis_iso (hs : IsIsoSplit V V' C B) {μ : Measure (Mx D W.rank r)} {𝓨 : Set (Mx D W.rank r)}
    (h : IsCovolOne (ratMx D W.rank r) μ 𝓨) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) (y₀ : Mx D W.rank r) :
    res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C y₀) f) = res V V' W C B μ 𝓨 f := by
  funext x
  simp only [res, heisO]
  simp only [sympl_iso hs, ψ.map_zero_eq_one, one_mul]
  have e : ∀ y, isoPart V W C y + midPart V V' W B x + isoPart V W C y₀ =
      isoPart V W C (y + y₀) + midPart V V' W B x := fun y => by rw [isoPart_add]; abel
  simp only [e]
  exact setIntegral_add_right h (fun y => f (isoPart V W C y + midPart V V' W B x))
    (fun γ hγ y => periodic_iso hs hf x γ hγ y) y₀

theorem integrable_res (hψ : IsStdChar D ψ (-1)) {μ : Measure (Mx D W.rank r)} {𝓨 : Set (Mx D W.rank r)}
    (h : IsCovolOne (ratMx D W.rank r) μ 𝓨) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) (x : WO V' W) :
    IntegrableOn (fun y => f (isoPart V W C y + midPart V V' W B x)) 𝓨 μ := by
  have : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  obtain ⟨c, hc⟩ := ((GlobalTheory.ThetaSquare.thetaFunctions_squareIntegrable_heisenbergUnitary D V W).2 ψ hψ).1 f hf |>.2.1
  refine Measure.integrableOn_of_bounded (M := c) (by rw [h.2.2]; exact ENNReal.one_ne_top) ?_
    (Filter.Eventually.of_forall fun y => hc _)
  exact (hf.cont.comp ((continuous_isoPart C).add continuous_const)).aestronglyMeasurable

theorem continuous_res (hψ : IsStdChar D ψ (-1)) {μ : Measure (Mx D W.rank r)} {𝓨 : Set (Mx D W.rank r)}
    (h : IsCovolOne (ratMx D W.rank r) μ 𝓨) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) :
    Continuous (res V V' W C B μ 𝓨 f) := by
  have : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  have : IsFiniteMeasure (μ.restrict 𝓨) := isFiniteMeasure_restrict.2 (by rw [h.2.2]; exact ENNReal.one_ne_top)
  obtain ⟨c, hc⟩ := ((GlobalTheory.ThetaSquare.thetaFunctions_squareIntegrable_heisenbergUnitary D V W).2 ψ hψ).1 f hf |>.2.1
  obtain ⟨-, -, i3, -⟩ := lattice_Mx D W.rank V'.rank
  have : FirstCountableTopology (WO V' W) := @TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _ _ i3
  exact continuous_of_dominated (bound := fun _ => c)
    (fun x => (hf.cont.comp ((continuous_isoPart C).add continuous_const)).aestronglyMeasurable)
    (fun x => Filter.Eventually.of_forall fun y => hc _) (integrable_const c)
    (Filter.Eventually.of_forall fun y => hf.cont.comp (continuous_const.add (continuous_midPart B)))

theorem res_quasi (hs : IsIsoSplit V V' C B) (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r))
    {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) (γ : Matrix (Fin W.rank) (Fin V'.rank) D.host.E) (x : WO V' W) :
    res V V' W C B μ 𝓨 f (ratW W V' γ + x) = ψ (-(symplOH V' W (ratW W V' γ) x)) * res V V' W C B μ 𝓨 f x := by
  simp only [res]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  have e := hf.quasi (γ * (V'.gram⁻¹ * adj D B * V.gram)) (isoPart V W C y + midPart V V' W B x)
  rw [← midPart_ratW, sympl_mid_left hs] at e
  simp only
  rw [← e, midPart_add]
  congr 1
  abel

theorem res_level (hs : IsIsoSplit V V' C B) (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r))
    {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) : ∃ U : AddSubgroup (WO V' W), IsOpen (U : Set (WO V' W)) ∧
      ∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ V' W u (res V V' W C B μ 𝓨 f) = res V V' W C B μ 𝓨 f := by
  obtain ⟨U, hU, hfix⟩ := hf.level
  refine ⟨U.comap (midHom B), hU.preimage (continuous_midPart B), fun u hu h0 => ?_⟩
  have e := hfix (midPart V V' W B u) hu (midPart_infPart B h0)
  rw [← res_heis_mid hs, e]

end Main

theorem res_theta : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → (∀ f, IsThetaFunO ψ V W f → (∀ x, IntegrableOn (fun y => f (isoPart V W C y + midPart V V' W B x)) 𝓨 μ) ∧ IsThetaFunO ψ V' W (res V V' W C B μ 𝓨 f) ∧ (∀ x, res V V' W C B μ 𝓨 (heisO ψ V W (midPart V V' W B x) f) = heisO ψ V' W x (res V V' W C B μ 𝓨 f)) ∧ ∀ y, res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C y) f) = res V V' W C B μ 𝓨 f) ∧ ∃ f, IsThetaFunO ψ V W f ∧ res V V' W C B μ 𝓨 f ≠ 0 := by
  intro D V V' W r C B hs ψ hψ μ 𝓨 h
  have hF := GlobalTheory.T.symplecticForm_isotropicPart_add_middlePart D V V' W r C B hs
  refine ⟨fun f hf => ⟨integrable_res hψ h hf, ⟨fun γ x => res_quasi hs μ 𝓨 hf γ x, res_level hs μ 𝓨 hf,
    continuous_res hψ h hf, GlobalTheory.T.thetaRestriction_isotropicSplit_smooth_realPoints D V V' W r C B hF ψ hψ μ 𝓨 h f hf⟩,
    fun x => res_heis_mid hs μ 𝓨 f x, fun y => res_heis_iso hs h hf y⟩, GlobalTheory.T.exists_thetaFunction_isotropicRestriction_ne_zero D V V' W r C B hs hF ψ hψ μ 𝓨 h⟩

end GlobalTheory.TowerRestrict

end
end
end
