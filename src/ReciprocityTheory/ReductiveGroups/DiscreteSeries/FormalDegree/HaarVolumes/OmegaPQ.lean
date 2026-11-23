module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.DensOn
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
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
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.OmegaPQA
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.OmegaPQB

section

@[expose] public section

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.OmegaPQAux

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n P Q : ℕ}

def sg (ε : Fin n → Bool) (a : Fin n) : ℂ := if ε a then 1 else -1

theorem Jpq_eq : Formalism.UG.Jpq P Q = Matrix.diagonal (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1)) := by
  ext (i | i) (j | j)
  · by_cases h : i = j <;> simp [Formalism.UG.Jpq, Matrix.one_apply, Matrix.diagonal_apply, h]
  · simp [Formalism.UG.Jpq, Matrix.diagonal_apply]
  · simp [Formalism.UG.Jpq, Matrix.diagonal_apply]
  · by_cases h : i = j <;> simp [Formalism.UG.Jpq, Matrix.one_apply, Matrix.diagonal_apply, h]

theorem mem_lieU_iff (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :
    X ∈ Formalism.BasicNotions.lieU P Q ↔ ∀ i j, star (X j i) * Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1) j +
      Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1) i * X i j = 0 := by
  show Xᴴ * Formalism.UG.Jpq P Q + Formalism.UG.Jpq P Q * X = 0 ↔ _
  rw [Jpq_eq]
  constructor
  · intro h i j
    have hij := congrFun (congrFun h i) j
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply] using hij
  · intro h
    ext i j
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply] using h i j

theorem mem_reindex_iff (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false)
    (Y : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.reindex e.symm e.symm Y ∈ Formalism.BasicNotions.lieU P Q ↔
      ∀ a b, star (Y b a) * sg ε b + sg ε a * Y a b = 0 := by
  rw [mem_lieU_iff]
  have hs : ∀ i, Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1) i = sg ε (e i) := by
    rintro (i | i) <;> simp [sg, he1, he2]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, hs]
  constructor
  · intro h a b
    simpa using h (e.symm a) (e.symm b)
  · intro h i j
    exact h (e i) (e j)

theorem gMat_mem {ε : Fin n → Bool} (s : GCo ε) (a b : Fin n) :
    star (gMat s b a) * sg ε b + sg ε a * gMat s a b = 0 := by
  rcases lt_trichotomy a b with h | rfl | h
  · have h1 : ¬ b < a := lt_asymm h
    have h2 : a ≠ b := ne_of_lt h
    have h3 : b ≠ a := ne_of_gt h
    cases ha : ε a <;> cases hb : ε b <;> simp [gMat, kMat, pmat, sg, h, h1, h2, h3, ha, hb]
  · cases ha : ε a <;> simp [gMat, kMat, pmat, sg, ha]
  · have h1 : ¬ a < b := lt_asymm h
    have h2 : a ≠ b := ne_of_gt h
    have h3 : b ≠ a := ne_of_lt h
    cases ha : ε a <;> cases hb : ε b <;> simp [gMat, kMat, pmat, sg, h, h1, h2, h3, ha, hb]

theorem gMat_add {ε : Fin n → Bool} (s t : GCo ε) : gMat (s + t) = gMat s + gMat t := by
  ext a b
  simp only [gMat, kMat, pmat, Matrix.add_apply, Prod.fst_add, Prod.snd_add, Pi.add_apply]
  split_ifs <;> (try simp only [star_add, neg_add, Complex.ofReal_add]) <;> ring

theorem gMat_smul {ε : Fin n → Bool} (c : ℝ) (s : GCo ε) : gMat (c • s) = c • gMat s := by
  ext a b
  simp only [gMat, kMat, pmat, Matrix.add_apply, Matrix.smul_apply, Prod.smul_fst, Prod.smul_snd,
    Pi.smul_apply]
  split_ifs <;> (try simp only [smul_eq_mul, Complex.real_smul, Complex.ofReal_mul, star_mul',
    Complex.star_def, map_mul, Complex.conj_ofReal]) <;> ring

def coordOf {ε : Fin n → Bool} (Y : Matrix (Fin n) (Fin n) ℂ) : GCo ε :=
  ((fun a => (Y a a).im, fun k => Y k.1.1 k.1.2), fun p => Y p.1.1 p.1.2)

theorem coordOf_gMat {ε : Fin n → Bool} (s : GCo ε) : coordOf (gMat s) = s := by
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · funext a
    simp [coordOf, gMat, kMat, pmat]
  · funext k
    obtain ⟨⟨a, b⟩, hk⟩ := k
    have h1 : a ≠ b := ne_of_gt hk.1
    have h2 : ¬ a < b := lt_asymm hk.1
    simp [coordOf, gMat, kMat, pmat, h1, h2, hk.1, hk.2]
  · funext q
    obtain ⟨⟨a, b⟩, hq⟩ := q
    have h1 : a ≠ b := ne_of_gt hq.1
    have h2 : ¬ a < b := lt_asymm hq.1
    simp [coordOf, gMat, kMat, pmat, h1, h2, hq.1, hq.2]

theorem gMat_coordOf {ε : Fin n → Bool} (Y : Matrix (Fin n) (Fin n) ℂ)
    (hY : ∀ a b, star (Y b a) * sg ε b + sg ε a * Y a b = 0) : gMat (coordOf (ε := ε) Y) = Y := by
  ext a b
  have key := hY a b
  rcases lt_trichotomy a b with h | rfl | h
  · have h1 : ¬ b < a := lt_asymm h
    have h2 : a ≠ b := ne_of_lt h
    cases ha : ε a <;> cases hb : ε b <;>
      simp [gMat, kMat, pmat, coordOf, sg, h, h1, h2, ha, hb] at key ⊢ <;>
      first | linear_combination key | linear_combination -key
  · have hre : (Y a a).re = 0 := by
      have hk := congrArg Complex.re key
      cases ha : ε a <;> simp [sg, ha] at hk <;> linarith
    apply Complex.ext <;> simp [gMat, kMat, pmat, coordOf, hre]
  · have h1 : ¬ a < b := lt_asymm h
    have h2 : a ≠ b := ne_of_gt h
    cases ha : ε a <;> cases hb : ε b <;>
      simp [gMat, kMat, pmat, coordOf, sg, h, h1, h2, ha, hb] at key ⊢ <;>
      first | linear_combination key | linear_combination -key

end ReciprocityTheory.ChartRestriction.DS.OmegaPQAux
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.OmegaPQ

section

@[expose] public section

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

variable {P Q : ℕ}

def gToLieMat (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool} (s : GCo ε) :
    Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ :=
  Matrix.reindex e.symm e.symm (gMat s)

theorem gToLieMat_mem (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false) (s : GCo ε) :
    gToLieMat e s ∈ Formalism.BasicNotions.lieU P Q :=
  (OmegaPQAux.mem_reindex_iff e he1 he2 (gMat s)).2 (OmegaPQAux.gMat_mem s)

def gToLie (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false) (s : GCo ε) :
    Formalism.BasicNotions.lieU P Q :=
  ⟨gToLieMat e s, gToLieMat_mem e he1 he2 s⟩

namespace OmegaPQAux

def gToLieL (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false) :
    GCo ε →ₗ[ℝ] Formalism.BasicNotions.lieU P Q where
  toFun := gToLie e he1 he2
  map_add' s t := by
    apply Subtype.ext
    ext i j
    simp [gToLie, gToLieMat, gMat_add]
  map_smul' c s := by
    apply Subtype.ext
    ext i j
    simp [gToLie, gToLieMat, gMat_smul]

theorem gToLieL_bij (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false) :
    Function.Bijective (gToLieL e he1 he2) := by
  have hre : ∀ M : Matrix (Fin n) (Fin n) ℂ,
      Matrix.reindex e e (Matrix.reindex e.symm e.symm M) = M := by
    intro M; rw [← Matrix.reindex_symm, Equiv.apply_symm_apply]
  constructor
  · intro s t h
    have h2 := congrArg (fun X : Formalism.BasicNotions.lieU P Q =>
      Matrix.reindex e e (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)) h
    simp only [gToLieL, LinearMap.coe_mk, AddHom.coe_mk, gToLie, gToLieMat, hre] at h2
    rw [← coordOf_gMat s, ← coordOf_gMat t, h2]
  · intro X
    set Y := Matrix.reindex e e (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) with hYdef
    have hX : Matrix.reindex e.symm e.symm Y = X := by
      rw [hYdef, ← Matrix.reindex_symm, Equiv.symm_apply_apply]
    have hY := (mem_reindex_iff e he1 he2 Y).1 (by rw [hX]; exact X.2)
    refine ⟨coordOf Y, Subtype.ext ?_⟩
    change Matrix.reindex e.symm e.symm (gMat (coordOf (ε := ε) Y)) = X
    rw [gMat_coordOf Y hY, hX]

end OmegaPQAux

theorem isOmegaLeb_gToLie (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false) :
    Formalism.BasicNotions.IsOmegaLeb (ENNReal.ofReal (2 ^ (n * (n - 1) / 2)) • Measure.map (gToLie e he1 he2) volume) := by
  have : BorelSpace (Formalism.BasicNotions.lieU P Q) := ⟨rfl⟩
  set Lin := LinearEquiv.ofBijective _ (OmegaPQAux.gToLieL_bij e he1 he2) with hLin
  set CL := Lin.toContinuousLinearEquiv with hCL
  have hcoe : (CL : GCo ε → Formalism.BasicNotions.lieU P Q) = gToLie e he1 he2 := rfl
  have hG : Measurable (gToLie e he1 he2) := by rw [← hcoe]; exact CL.continuous.measurable
  constructor
  · have hd : (volume : Measure (Fin n → ℝ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
    have hk : (volume : Measure (KPair ε → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
    have hp : (volume : Measure (PCoord ε → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
    have hK : (volume : Measure (KCo ε)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
    have hGv : (volume : Measure (GCo ε)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
    have h1 := ContinuousLinearEquiv.isAddHaarMeasure_map CL (volume : Measure (GCo ε))
    rw [hcoe] at h1
    exact Measure.IsAddHaarMeasure.smul _ (by simp) ENNReal.ofReal_ne_top
  · have hSF : SigmaFinite (volume : Measure (GCo ε)) := Measure.prod.instSigmaFinite
    set c := ENNReal.ofReal (2 ^ (n * (n - 1) / 2)) with hc
    set E : Fin n × Fin n ≃ (Fin P ⊕ Fin Q) × (Fin P ⊕ Fin Q) := (e.prodCongr e).symm with hE
    set R := MeasurableEquiv.piCongrLeft (fun _ : (Fin P ⊕ Fin Q) × (Fin P ⊕ Fin Q) => ℂ) E
    have hGl : Measurable (OmegaPQAux.Gl ε) :=
      (LinearMap.continuous_of_finiteDimensional (OmegaPQAux.Gl ε)).measurable
    have hPm : Measurable (OmegaPQAux.pairMap ε) := by
      rw [OmegaPQAux.pairMap_eq]
      exact (OmegaPQAux.mp_Amap ε).measurable.comp (hGl.comp (OmegaPQAux.mp_Fmap ε).measurable)
    have hcomp : (fun ab : Formalism.BasicNotions.lieU P Q × Formalism.BasicNotions.lieU P Q =>
        Formalism.BasicNotions.entries ((ab.1 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) +
          Complex.I • (ab.2 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ))) ∘
          Prod.map (gToLie e he1 he2) (gToLie e he1 he2) = R ∘ OmegaPQAux.pairMap ε := by
      funext st ij
      obtain ⟨i, j⟩ := ij
      have hij : ((i, j) : (Fin P ⊕ Fin Q) × (Fin P ⊕ Fin Q)) = E (e i, e j) := by simp [hE]
      conv_rhs => rw [hij]
      simp only [Function.comp_apply, R, MeasurableEquiv.coe_piCongrLeft,
        Equiv.piCongrLeft_apply_apply]
      simp [Formalism.BasicNotions.entries, gToLie, gToLieMat, OmegaPQAux.pairMap, Matrix.reindex_apply]
    have hval : ∀ i j, Measurable (fun X : Formalism.BasicNotions.lieU P Q =>
        (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) i j) := fun i j =>
      (continuous_subtype_val.matrix_elem i j).measurable
    have hFm : Measurable (fun ab : Formalism.BasicNotions.lieU P Q × Formalism.BasicNotions.lieU P Q =>
        Formalism.BasicNotions.entries ((ab.1 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) +
          Complex.I • (ab.2 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ))) := by
      refine Measurable.of_eval fun ij => ?_
      have h1 : Measurable (fun ab : Formalism.BasicNotions.lieU P Q × Formalism.BasicNotions.lieU P Q =>
          (ab.1 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) ij.1 ij.2) :=
        (hval ij.1 ij.2).comp measurable_fst
      have h2 : Measurable (fun ab : Formalism.BasicNotions.lieU P Q × Formalism.BasicNotions.lieU P Q =>
          (ab.2 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) ij.1 ij.2) :=
        (hval ij.1 ij.2).comp measurable_snd
      exact h1.add (measurable_const.mul h2)
    rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
      Measure.map_smul _ hFm.aemeasurable,
      Measure.map_prod_map _ _ hG hG, Measure.map_map hFm (hG.prodMap hG), hcomp,
      ← Measure.map_map R.measurable hPm, ← Measure.volume_eq_prod, OmegaPQAux.map_pairMap,
      Measure.map_smul _ R.measurable.aemeasurable,
      (volume_measurePreserving_piCongrLeft (fun _ : (Fin P ⊕ Fin Q) × (Fin P ⊕ Fin Q) => ℂ) E).map_eq,
      smul_smul, hc, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← mul_pow]
    norm_num

end ReciprocityTheory.ChartRestriction.DS
end
end
end
