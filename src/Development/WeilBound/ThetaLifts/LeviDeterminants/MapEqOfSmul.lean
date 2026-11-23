module

public import Development.WeilBound.ThetaLifts.LeviDeterminants.EvStmt
public import Development.WeilBound.ThetaLifts.LeviDeterminants.DqStmt
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.WeilBound.ThetaLifts.LeviDeterminants.EvChange
public import Development.WeilBound.ThetaLifts.LeviDeterminants.LagrangianUniqueness.GeoLeaves
import Development.WeilBound.ThetaLifts.LeviDeterminants.LagrangianUniqueness.LagLine
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
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.WeilBound.ThetaLifts.LeviDeterminants.LagrangianUniqueness.GeoCore
public import Development.WeilBound.ThetaLifts.LeviDeterminants.EvFrame
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.WeilBound.ThetaLifts.LeviDeterminants.EvChange

-- Source module: Development.WeilBound.ThetaLifts.LeviDeterminants.EigenIntertwinerSkewPlaneUnique

section

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace PositivityTheory.ThKF0

theorem evaluation_at_zero_unique : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d d₁ r s r' s' i₀ i₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (M : Model σ X W)
    (M₁ : Model σ X W₁), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    M₁.IsGood B.ψ → ∀ e e' : Fn F n d →ₗ[ℂ] Fn F n d₁, IsEv B M M₁ 1 H'.ι (iso0 n H') e → IsEv B M M₁ 1 H'.ι (iso0 n H') e' →
      ∃ c : ℂ, c ≠ 0 ∧ ∀ Φ ∈ PolData B M, e' Φ = c • e Φ := by
  intro F E _ _ _ _ _ σ B n d d₁ r s r' s' i₀ i₁ X W W₁ H' M M₁ hB hX hW hM hH hM₁ e e' he he'
  have adm : ∀ e, IsEv B M M₁ 1 H'.ι (iso0 n H') e →
      (LinearMap.proj 0 : Fn F n d₁ →ₗ[ℂ] ℂ) ∘ₗ e ∈ (adeleClass F).adm (Fin n × Fin d) := fun e he =>
    evaluation_intertwining_of_models F E σ B n d n d₁ X W X W₁ M M₁ 1 H'.ι (iso0 n H') e hM hM₁ he _ (Geo.proj_adm F _ 0)
  obtain ⟨Φ₁, hΦ₁, hne'⟩ := evaluation_intertwining_support F E σ B n d n d₁ X W X W₁ M M₁ 1 H'.ι (iso0 n H') e' hM hM₁ he'
  obtain ⟨c, key⟩ := Geo.map_line lagLine hB.std (Geo.hasLagrangian_skew_adapted hB M M₁ hM hM₁ hH) e' e he'.Heisenberg₂ he.Heisenberg₂ he'.inv he.inv (adm e' he')
    (adm e he) (evaluation_intertwining_support F E σ B n d n d₁ X W X W₁ M M₁ 1 H'.ι (iso0 n H') e hM hM₁ he)
  refine ⟨c, fun h0 => hne' (by rw [key _ hΦ₁, h0, zero_smul]), fun Φ hΦ => key Φ (Submodule.span_le.2 ?_ hΦ)⟩
  rintro _ ⟨f, -, φ, h1, h2, rfl⟩
  exact Submodule.subset_span ⟨f, _, Change.finPr_mem φ h1 (by filter_upwards [h2, hM.std] with v a b using a.trans b), rfl⟩

end PositivityTheory.ThKF0
end
end
end

-- Source module: Development.WeilBound.ThetaLifts.LeviDeterminants.EigenIntertwinerTwoPlanes

section

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace PositivityTheory.ThKF0

open PositivityTheory.Mix.Adapt


theorem adapted_plane_model_evaluation_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (H : Plane E n n₁)
    (H' : Plane E d d₁) (M : Model σ X W) (M₁ : Model σ X₁ W₁), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    M.IsGood B.ψ → H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ → M₁.IsGood B.ψ →
    ∃ (Ma : Model σ X W) (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁), Ma.IsGood B.ψ ∧ IsEv B Ma M₁ H.ι H'.ι (isoB H H') e := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ X W X₁ W₁ H H' M M₁ hB hX hW hM hH hH' hM₁
  classical
  obtain ⟨Q, h⟩ := frOK_herm hB hH hX
  obtain ⟨Q', h'⟩ := frOK_skew hB hH' hW
  let w : Matrix (Fin n) (Fin d) (AE F E) →ₗ[AF F] Matrix (Fin n₁ ⊕ Fin 2) (Fin d₁ ⊕ Fin 2) (AE F E) :=
    { toFun := fun z => incM F Q * z * (incM F Q')ᵀ
      map_add' := fun z z' => by rw [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c z => by rw [Matrix.mul_smul, Matrix.smul_mul]; rfl }
  have hw : ∀ z, w z = incM F Q * z * (incM F Q')ᵀ := fun _ => rfl
  have hc := cA_cA (σ := σ) hB
  have hi : ∀ z, w (incM F H.ι * z * (incM F H'.ι)ᵀ) = Matrix.fromBlocks z 0 0 0 := fun z => by
    rw [hw, w_mul, h.qi, h'.qi]
    ext (i | i) (j | j) <;> simp [Matrix.mul_apply, Matrix.one_apply]
  have hπ : ∀ v, ∀ γ ∈ latAtV X W v, (w γ).submatrix .inl .inl ∈ latAtV X₁ W₁ v := fun v γ hγ =>
    lat_map (X₁ := X₁) (W₁ := W₁) h.low h'.low hγ
  have qv : ∀ z, incM F Q *ᵥ (incM F H.ι *ᵥ z) = Sum.elim z 0 := fun z => by
    rw [Matrix.mulVec_mulVec, h.qi]; ext (i | i) <;> simp
  have qv' : ∀ z, incM F Q' *ᵥ (incM F H'.ι *ᵥ z) = Sum.elim z 0 := fun z => by
    rw [Matrix.mulVec_mulVec, h'.qi]; ext (i | i) <;> simp
  let G : Matrix (Fin d₁ ⊕ Fin 2) (Fin d₁ ⊕ Fin 2) E := (frame H')ᵀ * W.J * (frame H').map σ
  have hG : incM F G = Matrix.fromBlocks (incM F W₁.J) 0 0 !![0, 1; -1, 0] := by
    have := h'.gram
    rw [Int.cast_neg, Int.cast_one] at this
    rw [← this, incM_mul, incM_mul]
    rfl
  have hGh : ∀ i j, cA σ (incM F G j i) = -1 * incM F G i j := fun i j => by
    have := inc_herm (F := F) (η := -1) (J := G) (gram_herm σ (conj_conj hB) (fun i j => by simp [hW.skew]) _) i j
    rwa [Int.cast_neg, Int.cast_one] at this
  obtain ⟨A0, a0, e0⟩ := h.msk 0 1 0
  obtain ⟨A1, a1, e1⟩ := h.msk 1 0 0
  obtain ⟨C0, c0, f0⟩ := h'.msk 1 1 1
  obtain ⟨C1, c1, f1⟩ := h'.msk 0 1 0
  obtain ⟨Ma, e, h1, h2⟩ := exists_model hB hX hW hM hM₁ (κ := (Fin d₁ ⊕ Fin 2) ⊕ Fin n₁) (by simp [hH.rank, hH'.rank]; ring)
    (fun z => Sum.elim (w z (.inr 1)) (fun i => ((w z).submatrix .inl id) i (.inr 1)))
    (fun z => Sum.elim (DL (cA σ) (incM F G) (w z)) (DR (cA σ) (incM F X₁.J) ((w z).submatrix .inl id)))
    (fun z => (w z).submatrix .inl .inl)
    ⟨fun z z' => by ext (k | k) <;> simp, fun c z => by ext (k | k) <;> simp⟩
    ⟨fun z z' => by ext (k | k) <;> simp only [map_add (f := _), DR, DL, Sum.elim_inl, Sum.elim_inr, Pi.add_apply, Matrix.add_apply,
        Matrix.submatrix_apply, mul_add, Finset.sum_add_distrib, neg_add],
      fun c z => by ext (k | k) <;> simp [DR, DL, Finset.smul_sum]⟩
    ⟨fun z z' => by ext; simp, fun c z => by ext; simp⟩
    (fun z z' => by
      have g := h.gram
      rw [Int.cast_one] at g
      have g' := h'.gram
      rw [Int.cast_neg, Int.cast_one, ← hG] at g'
      rw [hTens_fr _ _ h.pq h'.pq, g, g', splitL _ hc _ hGh, sumElim_dotProduct_sumElim, sumElim_dotProduct_sumElim, map_add (f := _)]
      conv_lhs => rw [hG, splitR _ hc (fun i j => by simpa using h.herm₁ i j), ← hG]
      simp only [← hw]
      rw [show ∀ z, ((w z).submatrix Sum.inl id).submatrix id Sum.inl = (w z).submatrix .inl .inl from fun _ => rfl,
        show ∀ z, ((w z).submatrix Sum.inl id).submatrix id Sum.inl = (w z).submatrix .inl .inl from fun _ => rfl]
      ring)
    (fun x => by
      simp only [hw, w_inc]
      generalize Q * x * Q'ᵀ = y
      refine ⟨⟨Sum.elim (y (.inr 1)) (fun i => (y.submatrix .inl id) i (.inr 1)), by ext (k | k) <;> rfl⟩,
        ⟨Sum.elim (DL σ G y) (DR σ X₁.J (y.submatrix .inl id)), ?_⟩, y.submatrix .inl .inl, rfl⟩
      ext (k | k)
      · exact congrFun (DL_inc G y) k
      · exact congrFun (DR_inc X₁.J (y.submatrix .inl id)) k)
    H.ι H'.ι (isoB H H') (fun z => by
      simp only [hi]
      exact ⟨by ext ((k | k) | k) <;> simp, by ext; simp⟩)
    (by
      rintro u (⟨y, rfl⟩ | ⟨y, rfl⟩)
      · simp only [hw, w_vec, h.qx]
        exact ⟨by ext (k | k) <;> simp [Matrix.vecMulVec_apply], by ext; simp [Matrix.vecMulVec_apply]⟩
      · simp only [hw, w_vec, h'.qx, qv]
        exact ⟨by ext (k | k) <;> simp [Matrix.vecMulVec_apply], by ext; simp [Matrix.vecMulVec_apply]⟩)
    (fun v γ hγ => ⟨hπ v γ hγ, _, add_mem (lat_map a0 c0 hγ) (lat_map a1 c1 hγ), by
      simp only [map_add (f := _)]
      simp only [hw, w_msk e0 f0, w_msk e1 f1]
      generalize incM F Q * γ * (incM F Q')ᵀ = y
      refine ⟨?_, ?_, ?_⟩
      · ext ((k | k) | k) <;> simp [mask]
      · ext; simp [mask]
      · ext (k | k)
        · simp only [Sum.elim_inl, DL]
          refine Finset.sum_congr rfl fun l _ => ?_
          congr 2
          rcases l with l | l
          · simp [mask]
          · fin_cases l <;> simp [mask]
        · simp [DR, mask]⟩)
  exact ⟨Ma, e, h1, h2⟩

end PositivityTheory.ThKF0
end
end
end

-- Source module: Development.WeilBound.ThetaLifts.LeviDeterminants.ExistsAdaptedModelTwoPlanes

section

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace PositivityTheory.ThKF0

open PositivityTheory.Mix.Adapt


theorem adapted_plane_model_compatibility : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (H : Plane E n n₁)
    (H' : Plane E d d₁) (M : Model σ X W) (M₁ : Model σ X₁ W₁), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    M.IsGood B.ψ → H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ → M₁.IsGood B.ψ →
    ∃ (Ma : Model σ X W) (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁), Ma.IsGood B.ψ ∧ IsEv B Ma M₁ H.ι H'.ι (isoA H H') e := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ X W X₁ W₁ H H' M M₁ hB hX hW hM hH hH' hM₁
  classical
  obtain ⟨Q, h⟩ := frOK_herm hB hH hX
  obtain ⟨Q', h'⟩ := frOK_skew hB hH' hW
  let w : Matrix (Fin n) (Fin d) (AE F E) →ₗ[AF F] Matrix (Fin n₁ ⊕ Fin 2) (Fin d₁ ⊕ Fin 2) (AE F E) :=
    { toFun := fun z => incM F Q * z * (incM F Q')ᵀ
      map_add' := fun z z' => by rw [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c z => by rw [Matrix.mul_smul, Matrix.smul_mul]; rfl }
  have hw : ∀ z, w z = incM F Q * z * (incM F Q')ᵀ := fun _ => rfl
  have hc := cA_cA (σ := σ) hB
  have hi : ∀ z, w (incM F H.ι * z * (incM F H'.ι)ᵀ) = Matrix.fromBlocks z 0 0 0 := fun z => by
    rw [hw, w_mul, h.qi, h'.qi]
    ext (i | i) (j | j) <;> simp [Matrix.mul_apply, Matrix.one_apply]
  have hπ : ∀ v, ∀ γ ∈ latAtV X W v, (w γ).submatrix .inl .inl ∈ latAtV X₁ W₁ v := fun v γ hγ =>
    lat_map (X₁ := X₁) (W₁ := W₁) h.low h'.low hγ
  have qv : ∀ z, incM F Q *ᵥ (incM F H.ι *ᵥ z) = Sum.elim z 0 := fun z => by
    rw [Matrix.mulVec_mulVec, h.qi]; ext (i | i) <;> simp
  have qv' : ∀ z, incM F Q' *ᵥ (incM F H'.ι *ᵥ z) = Sum.elim z 0 := fun z => by
    rw [Matrix.mulVec_mulVec, h'.qi]; ext (i | i) <;> simp
  let G : Matrix (Fin n₁ ⊕ Fin 2) (Fin n₁ ⊕ Fin 2) E := (frame H)ᵀ * X.J * (frame H).map σ
  have hG : incM F G = Matrix.fromBlocks (incM F X₁.J) 0 0 !![0, 1; 1, 0] := by
    have := h.gram
    rw [Int.cast_one] at this
    rw [← this, incM_mul, incM_mul]
    rfl
  have hGh : ∀ i j, cA σ (incM F G j i) = 1 * incM F G i j := fun i j => by
    have := inc_herm (F := F) (η := 1) (J := G) (gram_herm σ (conj_conj hB) (fun i j => by simp [hX.herm]) _) i j
    rwa [Int.cast_one] at this
  obtain ⟨A0, a0, e0⟩ := h.msk 1 1 1
  obtain ⟨A1, a1, e1⟩ := h.msk 0 1 0
  obtain ⟨C0, c0, f0⟩ := h'.msk 0 1 0
  obtain ⟨C1, c1, f1⟩ := h'.msk 1 0 0
  obtain ⟨Ma, e, h1, h2⟩ := exists_model hB hX hW hM hM₁ (κ := (Fin n₁ ⊕ Fin 2) ⊕ Fin d₁) (by simp [hH.rank, hH'.rank]; ring)
    (fun z => Sum.elim (fun i => w z i (.inr 1)) (((w z).submatrix id .inl) (.inr 1)))
    (fun z => Sum.elim (DR (cA σ) (incM F G) (w z)) (DL (cA σ) (incM F W₁.J) ((w z).submatrix id .inl)))
    (fun z => (w z).submatrix .inl .inl)
    ⟨fun z z' => by ext (k | k) <;> simp, fun c z => by ext (k | k) <;> simp⟩
    ⟨fun z z' => by ext (k | k) <;> simp only [map_add (f := _), DR, DL, Sum.elim_inl, Sum.elim_inr, Pi.add_apply, Matrix.add_apply,
        Matrix.submatrix_apply, mul_add, Finset.sum_add_distrib, neg_add],
      fun c z => by ext (k | k) <;> simp [DR, DL, Finset.smul_sum]⟩
    ⟨fun z z' => by ext; simp, fun c z => by ext; simp⟩
    (fun z z' => by
      have g' := h'.gram
      rw [Int.cast_neg, Int.cast_one] at g'
      have g := h.gram
      rw [Int.cast_one, ← hG] at g
      rw [hTens_fr _ _ h.pq h'.pq, g, g', splitR _ hc hGh, sumElim_dotProduct_sumElim, sumElim_dotProduct_sumElim, map_add (f := _)]
      conv_lhs => rw [hG, splitL _ hc _ (fun i j => by simpa using h'.herm₁ i j), ← hG]
      simp only [← hw]
      rw [show ∀ z, ((w z).submatrix id Sum.inl).submatrix Sum.inl id = (w z).submatrix .inl .inl from fun _ => rfl,
        show ∀ z, ((w z).submatrix id Sum.inl).submatrix Sum.inl id = (w z).submatrix .inl .inl from fun _ => rfl]
      ring)
    (fun x => by
      simp only [hw, w_inc]
      generalize Q * x * Q'ᵀ = y
      refine ⟨⟨Sum.elim (fun i => y i (.inr 1)) ((y.submatrix id .inl) (.inr 1)), by ext (k | k) <;> rfl⟩,
        ⟨Sum.elim (DR σ G y) (DL σ W₁.J (y.submatrix id .inl)), ?_⟩, y.submatrix .inl .inl, rfl⟩
      ext (k | k)
      · exact congrFun (DR_inc G y) k
      · exact congrFun (DL_inc W₁.J (y.submatrix id .inl)) k)
    H.ι H'.ι (isoA H H') (fun z => by
      simp only [hi]
      exact ⟨by ext ((k | k) | k) <;> simp, by ext; simp⟩)
    (by
      rintro u (⟨y, rfl⟩ | ⟨y, rfl⟩)
      · simp only [hw, w_vec, h'.qx]
        exact ⟨by ext (k | k) <;> simp [Matrix.vecMulVec_apply], by ext; simp [Matrix.vecMulVec_apply]⟩
      · simp only [hw, w_vec, h.qx, qv']
        exact ⟨by ext (k | k) <;> simp [Matrix.vecMulVec_apply], by ext; simp [Matrix.vecMulVec_apply]⟩)
    (fun v γ hγ => ⟨hπ v γ hγ, _, add_mem (lat_map a0 c0 hγ) (lat_map a1 c1 hγ), by
      simp only [map_add (f := _)]
      simp only [hw, w_msk e0 f0, w_msk e1 f1]
      generalize incM F Q * γ * (incM F Q')ᵀ = y
      refine ⟨?_, ?_, ?_⟩
      · ext ((k | k) | k) <;> simp [mask]
      · ext; simp [mask]
      · ext (k | k)
        · simp only [Sum.elim_inl, DR]
          congr 1
          refine Finset.sum_congr rfl fun l _ => ?_
          congr 2
          rcases l with l | l
          · simp [mask]
          · fin_cases l <;> simp [mask]
        · simp [DL, mask]⟩)
  exact ⟨Ma, e, h1, h2⟩

end PositivityTheory.ThKF0
end
end
end

-- Source module: Development.WeilBound.ThetaLifts.LeviDeterminants.MapEqOfSmul

section

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace PositivityTheory.ThKF0

namespace Top

theorem incM_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) :
    incM F (1 : Matrix (Fin n) (Fin n) E) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem vac_mem_SB {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} (hM : M.IsGood B.ψ) (v : Pl (F := F)) :
    M.vac v ∈ SB _ :=
  (hM.vac v).1

theorem isEv_comp {B : Base F E} {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}
    {M Ma : Model σ X W} {M₁ : Model σ X₁ W₁} {ι : Matrix (Fin n) (Fin n₁) E} {ι' : Matrix (Fin d) (Fin d₁) E}
    {I : Set (Matrix (Fin n) (Fin d) (AE F E))} {e₁ : Fn F n d →ₗ[ℂ] Fn F n d} {e₂ : Fn F n d →ₗ[ℂ] Fn F n₁ d₁}
    (h₁ : IsEv B M Ma 1 1 ∅ e₁) (ei₁ : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d))
    (ev₁ : ∀ v : Pl (F := F), ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d → Fv F v) → ℂ)
    (hs : Function.Surjective ei₁) (hv₁ : ∀ v, ev₁ v (M.vac v) = Ma.vac v ∧ (SB _).map (ev₁ v) = SB _)
    (hl₁ : ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) → e₁ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei₁ f) fun v => ev₁ v (φ v))
    (h₂ : IsEv B Ma M₁ ι ι' I e₂) : IsEv B M M₁ ι ι' I (e₂ ∘ₗ e₁) := by
  have heis₁ : ∀ u, ∀ Φ ∈ schA F (Fin n × Fin d), e₁ (M.co.rho B.ψ u Φ) = Ma.co.rho B.ψ u (e₁ Φ) := by
    intro u Φ hΦ
    have := h₁.Heisenberg₂ u Φ hΦ
    rwa [incM_one, incM_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one] at this
  refine ⟨fun Φ hΦ => h₂.maps _ (h₁.maps Φ hΦ), fun z Φ hΦ => ?_, fun u hu Φ hΦ => ?_, ?_⟩
  · simp only [LinearMap.comp_apply]
    rw [heis₁ _ Φ hΦ, h₂.Heisenberg₂ z _ (h₁.maps Φ hΦ)]
  · simp only [LinearMap.comp_apply]
    rw [heis₁ _ Φ hΦ, h₂.inv u hu _ (h₁.maps Φ hΦ)]
  · obtain ⟨ei₂, ev₂, hne, hv₂, hl₂⟩ := h₂.loc
    refine ⟨ei₂.comp ei₁, fun v => (ev₂ v).comp (ev₁ v), ?_, fun v => ⟨?_, ?_⟩, fun f φ hφ hc => ?_⟩
    · intro h0
      apply hne
      ext1 g
      obtain ⟨g', rfl⟩ := hs g
      exact congrArg (fun T : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁) => T g') h0
    · simp [(hv₁ v).1, (hv₂ v).1]
    · rw [Submodule.map_comp, (hv₁ v).2, (hv₂ v).2]
    · have hφ' : ∀ v, ev₁ v (φ v) ∈ SB _ := fun v => by
        rw [← (hv₁ v).2]; exact Submodule.mem_map_of_mem (hφ v)
      have hc' : ∀ᶠ v in cofinite, ev₁ v (φ v) = Ma.vac v := by
        filter_upwards [hc] with v hv; rw [hv, (hv₁ v).1]
      simp only [LinearMap.comp_apply, ContinuousLinearMap.comp_apply]
      rw [hl₁ f φ hφ hc, hl₂ _ _ hφ' hc']

theorem polData_map (B : Base F E) {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}
    (M : Model σ X W) (M₁ : Model σ X₁ W₁) (hM : ∀ v, M.vac v ∈ SB _) (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁)
    (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁))
    (ev : ∀ v : Pl (F := F), ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n₁ × Fin d₁ → Fv F v) → ℂ)
    (hP : (M.Pol B.ψ B.emb).map (ei : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n₁ × Fin d₁)) = M₁.Pol B.ψ B.emb)
    (hv : ∀ v, ev v (M.vac v) = M₁.vac v ∧ (SB _).map (ev v) = SB _)
    (hl : ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) → e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei f) fun v => ev v (φ v)) :
    (PolData B M).map e = PolData B M₁ := by
  unfold PolData
  rw [Submodule.map_span]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨Φ, ⟨f, hf, φ, hφ, hc, rfl⟩, rfl⟩
    apply Submodule.subset_span
    refine ⟨ei f, ?_, fun v => ev v (φ v), fun v => ?_, ?_, hl f φ hφ hc⟩
    · rw [← hP]; exact Submodule.mem_map_of_mem (f := (ei : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n₁ × Fin d₁))) hf
    · rw [← (hv v).2]; exact Submodule.mem_map_of_mem (hφ v)
    · filter_upwards [hc] with v hv'; rw [hv', (hv v).1]
  · rw [Submodule.span_le]
    rintro _ ⟨g, hg, φ', hφ', hc', rfl⟩
    rw [← hP] at hg
    obtain ⟨f, hf, rfl⟩ := hg
    have hpre : ∀ v, ∃ p, p ∈ SB (Fin n × Fin d → Fv F v) ∧ ev v p = φ' v := fun v => by
      have := hφ' v
      rw [← (hv v).2] at this
      exact this
    classical
    let φ : ∀ v : Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ := fun v => if φ' v = M₁.vac v then M.vac v else (hpre v).choose
    have hφ : ∀ v, φ v ∈ SB _ := fun v => by
      by_cases h : φ' v = M₁.vac v
      · simp only [φ, if_pos h]; exact hM v
      · simp only [φ, if_neg h]; exact (hpre v).choose_spec.1
    have hev : (fun v => ev v (φ v)) = φ' := funext fun v => by
      by_cases h : φ' v = M₁.vac v
      · simp only [φ, if_pos h]; rw [(hv v).1, h]
      · simp only [φ, if_neg h]; exact (hpre v).choose_spec.2
    have hc : ∀ᶠ v in cofinite, φ v = M.vac v := by
      filter_upwards [hc'] with v h; simp only [φ, if_pos h]
    apply Submodule.subset_span
    refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ, ⟨f, hf, φ, hφ, hc, rfl⟩, ?_⟩
    rw [hl f φ hφ hc, hev]
    rfl

theorem map_eq_of_smul {A C : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup C] [Module ℂ C] {N : Submodule ℂ A}
    {e e₀ : A →ₗ[ℂ] C} {c : ℂ} (hc : c ≠ 0) (h : ∀ x ∈ N, e x = c • e₀ x) : N.map e = N.map e₀ := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨c • x, N.smul_mem c hx, by rw [map_smul, h x hx]⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨c⁻¹ • x, N.smul_mem _ hx, ?_⟩
    rw [h _ (N.smul_mem _ hx), map_smul, smul_smul, mul_inv_cancel₀ hc, one_smul]

end Top

open Top Change

def EvBij : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ M' : Model σ X W, M'.IsGood B.ψ → ∃ e : Fn F n d →ₗ[ℂ] Fn F n d, IsEv B M M' 1 1 ∅ e ∧
      Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _)

theorem evCone_of_bij (hb : EvBij) : EvCone := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP n₁ d₁ X₁ W₁ H H' i₀ i₁ j₀ j₁ M₁ hH hH' hM₁
  refine ⟨?_, ?_⟩
  · obtain ⟨Ma, e₂, hMa, h₂⟩ :=
      adapted_plane_model_compatibility F E σ B n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ X W X₁ W₁ H H' M M₁ hP.base hP.herm hP.skew hP.good hH hH' hM₁
    obtain ⟨e₁, h₁, hbij⟩ := hb F E σ B n d X W M χX χW om r s r' s' hP Ma hMa
    obtain ⟨ei₁, ev₁, hs₁, -, hv₁, hl₁⟩ := change_core hP.base.std hP.good hMa h₁ hbij
    exact ⟨_, isEv_comp h₁ ei₁ ev₁ hs₁ hv₁ hl₁ h₂⟩
  · obtain ⟨Ma, e₂, hMa, h₂⟩ :=
      adapted_plane_model_evaluation_eq F E σ B n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ X W X₁ W₁ H H' M M₁ hP.base hP.herm hP.skew hP.good hH hH' hM₁
    obtain ⟨e₁, h₁, hbij⟩ := hb F E σ B n d X W M χX χW om r s r' s' hP Ma hMa
    obtain ⟨ei₁, ev₁, hs₁, -, hv₁, hl₁⟩ := change_core hP.base.std hP.good hMa h₁ hbij
    exact ⟨_, isEv_comp h₁ ei₁ ev₁ hs₁ hv₁ hl₁ h₂⟩

theorem evZero_of_bij (hb : EvBij) (hDq : SchwartzDq) (hA : AdaptedModelEvaluationAtZero) : EvZero := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ X₁ W₁ H' i₀ i₁ M₁ hX hH hM₁
  subst X₁
  obtain ⟨Ma, e₂, hMa, h₂, ei₂, ev₂, hP₂, hv₂, hl₂⟩ :=
    hA F E σ B n d d₁ r s r' s' i₀ i₁ X W W₁ H' M M₁ hP.base hP.herm hP.skew hP.good hH hM₁
  obtain ⟨e₁, h₁, hbij⟩ := hb F E σ B n d X W M χX χW om r s r' s' hP Ma hMa
  obtain ⟨ei₁, ev₁, hs₁, hP₁, hv₁, hl₁⟩ := change_core hP.base.std hP.good hMa h₁ hbij
  have hE := isEv_comp h₁ ei₁ ev₁ hs₁ hv₁ hl₁ h₂
  have hmap : (PolData B M).map (e₂ ∘ₗ e₁) = PolData B M₁ := by
    rw [Submodule.map_comp, polData_map B M Ma (vac_mem_SB hP.good) e₁ ei₁ ev₁ (hP₁ hDq) hv₁ hl₁,
      polData_map B Ma M₁ (vac_mem_SB hMa) e₂ ei₂ ev₂ hP₂ hv₂ hl₂]
  refine ⟨⟨_, hE⟩, fun e he => ?_⟩
  obtain ⟨c, hc, hce⟩ := evaluation_at_zero_unique F E σ B n d d₁ r s r' s' i₀ i₁ X W W₁ H' M M₁ hP.base hP.herm hP.skew hP.good hH hM₁ _ e hE he
  rw [← hmap]
  exact map_eq_of_smul hc hce

end PositivityTheory.ThKF0
end
end
end
