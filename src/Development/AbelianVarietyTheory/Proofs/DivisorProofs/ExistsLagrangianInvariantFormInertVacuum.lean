module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLagrAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqAdeleSupportedAtFinitePlaceOfSupportedAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunctionStatement
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetNeZeroOfSkewHermitianSelfDualLatticeSpace
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
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFieldCompletionTensorOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianDetEqUnitMulNormAtInertStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitEqNormCompletionTensorOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorSkewHermitianLatticeOpenCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceTensorLatticeSelfDualSupportedAtStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianInvariantLinearFormLocalExistenceStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLocalImageLatticeSupportedAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormEqZeroOfLagrangianAtPlaceStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetNeZeroOfSkewHermitianSelfDualLatticeSpaceStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.det_ne_zero_of_skewHermitianSelfDualLatticeSpace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n r s : ℕ) (W : Spc F E n), W.IsSkew σ B r s → W.J.det ≠ 0 := by
  first | exact @GlobalTheory.SkewDet.det_ne_zero_of_isSkew | exact GlobalTheory.SkewDet.det_ne_zero_of_isSkew | (intros; apply GlobalTheory.SkewDet.det_ne_zero_of_isSkew <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLagrangianSkewHermitianCompletionTensor

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.SkewLagr

open Matrix

theorem det_hyp {L : Type*} [CommRing L] (m : ℕ) :
    (fromBlocks (0 : Matrix (Fin m) (Fin m) L) (1 : Matrix (Fin m) (Fin m) L) 1 0).det = (-1) ^ m := by
  have h : fromBlocks (0 : Matrix (Fin m) (Fin m) L) (1 : Matrix (Fin m) (Fin m) L) 1 0 =
      (fromBlocks 1 1 0 1 * fromBlocks 1 0 (-1) 1 * fromBlocks 1 1 0 1 * fromBlocks (-1) 0 0 1 :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L) := by
    simp [fromBlocks_multiply]
  rw [h, det_mul, det_mul, det_mul, det_fromBlocks_zero₂₁, det_fromBlocks_zero₁₂, det_fromBlocks_zero₂₁]
  simp [det_neg]

theorem exists_isLagr_of_local (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    {L : Type} [Field L] [Algebra (v.adicCompletion F) L]
    [Algebra.IsQuadraticExtension (v.adicCompletion F) L]
    (c : L →ₐ[v.adicCompletion F] L) (hc : ∀ x, c (c x) = x) {δ : L} (hδ : δ ≠ 0) (hcδ : c δ = -δ)
    (m : ℕ) (J : Matrix (Fin (m + m)) (Fin (m + m)) L) (hJ : ∀ i j, c (J j i) = -J i j)
    (hd : J.det ≠ 0) (hx : ∃ x, J.det = x * c x) :
    ∃ Cy : Matrix (Fin (m + m)) (Fin m) L, GlobalTheory.WeilM.IsLagr c J Cy := by
  classical
  haveI : CharZero (v.adicCompletion F) :=
    charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective
  obtain ⟨x, hx⟩ := hx
  let σ : L ≃ₐ[v.adicCompletion F] L := AlgEquiv.ofAlgHom c c (AlgHom.ext hc) (AlgHom.ext hc)
  have hσc : ∀ y, σ y = c y := fun _ => rfl
  have h2 : (2 : L) ≠ 0 := by
    rw [← map_ofNat (algebraMap (v.adicCompletion F) L) 2]
    exact (map_ne_zero _).2 two_ne_zero
  have hσ : σ ≠ 1 := by
    intro h
    have h1 : c δ = δ := by rw [← hσc, h]; rfl
    apply hδ
    have : (2 : L) * δ = 0 := by linear_combination hcδ - h1
    exact (mul_eq_zero.1 this).resolve_left h2
  let e : Fin m ⊕ Fin m ≃ Fin (m + m) := finSumFinEquiv
  let Hyp : Matrix (Fin (m + m)) (Fin (m + m)) L :=
    (fromBlocks 0 1 1 0 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L).submatrix e.symm e.symm
  let H : Matrix (Fin (m + m)) (Fin (m + m)) L := δ • J
  have hH : ∀ a b, σ (H a b) = H b a := by
    intro a b
    simp only [H, Matrix.smul_apply, smul_eq_mul, hσc, map_mul, hcδ, hJ]
    ring
  have hHyp : ∀ a b, σ (Hyp a b) = Hyp b a := by
    intro a b
    simp only [Hyp, submatrix_apply]
    rcases e.symm a with i | i <;> rcases e.symm b with j | j <;>
      by_cases hij : i = j <;> simp [fromBlocks, one_apply, hij, eq_comm]
  have hdH : H.det = δ ^ (m + m) * J.det := by simp [H, det_smul]
  have hdHyp : Hyp.det = (-1) ^ m := by simp [Hyp, det_submatrix_equiv_self, det_hyp]
  have hs : ((-1 : L) ^ m) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  obtain ⟨P, hP, hPeq⟩ := (GlobalTheory.HermLocal.congr_iff_adicCompletion F v L σ hσ hH hHyp
    (by rw [hdH]; exact mul_ne_zero (pow_ne_zero _ hδ) hd) (by rw [hdHyp]; simp)).2 ⟨δ ^ m * x, by
      rw [hdH, hdHyp, div_eq_iff (by simp), hx, hσc, map_mul, map_pow, hcδ, neg_pow]
      linear_combination (-(δ ^ (m + m) * x * c x)) * hs⟩
  have hQ : ∀ a b, δ * (Pᵀ * J * P.map c) a b = Hyp a b := by
    intro a b
    rw [hPeq]
    simp only [H, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
    rfl
  have hiso : ∀ (f : Fin m → Fin m ⊕ Fin m), (∀ a b, Hyp (e (f a)) (e (f b)) = 0) →
      (P.submatrix id (fun j => e (f j)))ᵀ * J * (P.submatrix id (fun j => e (f j))).map c = 0 := by
    intro f hf
    ext a b
    have h1 : ((P.submatrix id (fun j => e (f j)))ᵀ * J * (P.submatrix id (fun j => e (f j))).map c) a b =
        (Pᵀ * J * P.map c) (e (f a)) (e (f b)) := rfl
    rw [h1, Matrix.zero_apply]
    have h3 := hQ (e (f a)) (e (f b))
    rw [hf] at h3
    exact (mul_eq_zero.1 h3).resolve_left hδ
  have hPu : IsUnit P.det := isUnit_iff_ne_zero.2 hP
  have hcols : fromCols (P.submatrix id (fun j => e (Sum.inl j))) (P.submatrix id (fun j => e (Sum.inr j))) =
      P.submatrix id e := by
    ext i (j | j) <;> rfl
  refine ⟨P.submatrix id (fun j => e (Sum.inl j)), hiso Sum.inl (fun a b => by simp [Hyp]),
    P.submatrix id (fun j => e (Sum.inr j)), P⁻¹.submatrix e id, hiso Sum.inr (fun a b => by simp [Hyp]), ?_, ?_⟩
  · rw [hcols, submatrix_mul_equiv, mul_nonsing_inv P hPu, submatrix_id_id]
  · rw [hcols, show (P⁻¹.submatrix e id) = P⁻¹.submatrix e (Equiv.refl _) from rfl,
      show P.submatrix id e = P.submatrix (Equiv.refl _) e from rfl, submatrix_mul_equiv,
      nonsing_inv_mul P hPu, submatrix_one_equiv]

end GlobalTheory.SkewLagr

namespace GlobalTheory.SkewLagr

open Matrix

theorem exists_isLagr_tensor : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (v : Pl (F := F)), IsField (Fv F v ⊗[F] E) →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), Even n → (∀ i j, σ (J j i) = -J i j) → J.det ≠ 0 →
    (∃ x : Fv F v ⊗[F] E, (1 : Fv F v) ⊗ₜ[F] J.det = x * Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ x) →
    ∃ Cy : Matrix (Fin n) (Fin (n / 2)) (Fv F v ⊗[F] E),
      IsLagr (Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ) (JR (Fv F v) J) Cy := by
  intro F E _ _ _ _ _ σ hcm v hF n J hn hJ hd hx
  obtain ⟨m, rfl⟩ := hn
  rw [show (m + m) / 2 = m by omega]
  letI : Field (Fv F v ⊗[F] E) := hF.toField
  haveI : Algebra.IsQuadraticExtension (Fv F v) (Fv F v ⊗[F] E) :=
    { finrank_eq_two' := by rw [Module.finrank_baseChange]; exact hcm.2.2.1 }
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hσσ : ∀ y, σ (σ y) = y := fun y => τ.injective (by rw [hcm.2.2.2, hcm.2.2.2, star_star])
  obtain ⟨t, ht⟩ : ∃ t, σ t ≠ t := by
    by_contra h
    push_neg at h
    have hw := hcm.2.1.isComplex (NumberField.InfinitePlace.mk τ)
    rw [NumberField.InfinitePlace.isComplex_mk_iff, NumberField.ComplexEmbedding.isReal_iff] at hw
    apply hw
    ext y
    have hy := hcm.2.2.2 τ y
    rw [h] at hy
    simp only [NumberField.ComplexEmbedding.conjugate_coe_eq]
    rw [starRingEnd_apply]
    exact hy.symm
  set c := Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ with hcdef
  have hct : ∀ y : E, c ((1 : Fv F v) ⊗ₜ[F] y) = (1 : Fv F v) ⊗ₜ[F] σ y := fun y => by
    simp [c, Algebra.TensorProduct.map_tmul]
  have hc : ∀ z, c (c z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [c, Algebra.TensorProduct.map_tmul, hσσ]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have hinj : Function.Injective (inclR (Fv F v) : E →+* Fv F v ⊗[F] E) := RingHom.injective _
  have hincl : ∀ y : E, inclR (Fv F v) y = (1 : Fv F v) ⊗ₜ[F] y := fun _ => rfl
  have hδ : (1 : Fv F v) ⊗ₜ[F] (t - σ t) ≠ 0 := by
    rw [← hincl]
    exact (map_ne_zero_iff _ hinj).2 (sub_ne_zero.2 (Ne.symm ht))
  have hcδ : c ((1 : Fv F v) ⊗ₜ[F] (t - σ t)) = -((1 : Fv F v) ⊗ₜ[F] (t - σ t)) := by
    rw [hct, map_sub, hσσ, ← TensorProduct.tmul_neg, neg_sub]
  have hdet : (JR (Fv F v) J).det = (1 : Fv F v) ⊗ₜ[F] J.det := by
    rw [← hincl, RingHom.map_det]
    rfl
  refine exists_isLagr_of_local F v c hc hδ hcδ m (JR (Fv F v) J) (fun i j => ?_) ?_ ?_
  · change c (inclR (Fv F v) (J j i)) = -inclR (Fv F v) (J i j)
    rw [hincl, hincl, hct, hJ, TensorProduct.tmul_neg]
  · rw [hdet, ← hincl]
    exact (map_ne_zero_iff _ hinj).2 hd
  · rw [hdet]
    exact hx

end GlobalTheory.SkewLagr
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLagrangianSkewHermitianCompletionTensorStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.exists_lagrangian_skewHermitian_completionTensor : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (v : Pl (F := F)), IsField (Fv F v ⊗[F] E) →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), Even n → (∀ i j, σ (J j i) = -J i j) → J.det ≠ 0 →
    (∃ x : Fv F v ⊗[F] E, (1 : Fv F v) ⊗ₜ[F] J.det = x * Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ x) →
    ∃ Cy : Matrix (Fin n) (Fin (n / 2)) (Fv F v ⊗[F] E),
      IsLagr (Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ) (JR (Fv F v) J) Cy := by
  first | exact @GlobalTheory.SkewLagr.exists_isLagr_tensor | exact GlobalTheory.SkewLagr.exists_isLagr_tensor | (intros; apply GlobalTheory.SkewLagr.exists_isLagr_tensor <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitEqNormCompletionTensorOfIsInertAtStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.unit_eq_norm_completionTensor_of_isInertAt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → IsField (Fv F v ⊗[F] E) →
    ∀ u : Fv F v, Valued.v u = 1 →
      ∃ z : Fv F v ⊗[F] E, algebraMap (Fv F v) (Fv F v ⊗[F] E) u = z * Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ z := by
  first | exact @GlobalTheory.InertUnitNorm.unit_eq_mul_conj | exact GlobalTheory.InertUnitNorm.unit_eq_mul_conj | (intros; apply GlobalTheory.InertUnitNorm.unit_eq_mul_conj <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLagrangianInertPlace

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.InertLagr

theorem exists_lagr : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
      ∃ Cy : Matrix (Fin (a + a')) (Fin ((a + a') / 2)) (Fv F v ⊗[F] E),
        IsLagr (Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ) (JR (Fv F v) G.W.J) Cy := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hvw
  have hF := GlobalTheory.InertTensorField.isField_tensor_of_isInertAt F E σ B hT.base v w hvw
  obtain ⟨y, u, hu, hy⟩ := GlobalTheory.T.skewHermitian_det_eq_unit_mul_norm_at_inert F E σ B hT.base _ _ _ G.W hT.geo.hW hT.geo.even v w hvw hF
  obtain ⟨z, hz⟩ := GlobalTheory.T.unit_eq_norm_completionTensor_of_isInertAt F E σ B hT.base v w hvw hF u hu
  refine GlobalTheory.T.exists_lagrangian_skewHermitian_completionTensor F E σ hT.base.cm v hF (a + a') G.W.J hT.geo.even hT.geo.hW.skew
    (GlobalTheory.T.det_ne_zero_of_skewHermitianSelfDualLatticeSpace F E σ B _ _ _ G.W hT.geo.hW) ⟨z * y, ?_⟩
  rw [hy, hz, map_mul]
  ring

end GlobalTheory.InertLagr
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLagrangianInvariantFormInertVacuum

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.InertVacLagP

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_map_compFin (v : Pl (F := F)) {d m : ℕ} (Cy : Matrix (Fin d) (Fin m) (Fv F v ⊗[F] E)) :
    ∃ C : Matrix (Fin d) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), C.map (compFin F E v) = Cy := by
  have hs : Function.Surjective (compFin F E v) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul x e =>
      refine ⟨GlobalTheory.LatVac.liftV v x ⊗ₜ e, ?_⟩
      simp [compFin, GlobalTheory.LatVac.evFin_liftV]
    | add x y hx hy =>
      obtain ⟨p, hp⟩ := hx
      obtain ⟨q, hq⟩ := hy
      exact ⟨p + q, by rw [map_add (f := _), hp, hq]⟩
  choose f hf using hs
  exact ⟨Cy.map f, by ext i j; simp [hf]⟩

def lagSub {n d m : ℕ} (v : Pl (F := F)) (C : Matrix (Fin d) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : AddSubgroup (Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) where
  carrier := GlobalTheory.InertVacLag.lagAt v C
  zero_mem' := ⟨fun u _ => smul_zero u, 0, by simp⟩
  add_mem' := by
    rintro x y ⟨hx, z, rfl⟩ ⟨hy, z', rfl⟩
    exact ⟨fun u hu => by rw [smul_add, hx u hu, hy u hu, add_zero], z + z', by rw [Matrix.add_mul]⟩
  neg_mem' := by
    rintro x ⟨hx, z, rfl⟩
    exact ⟨fun u hu => by rw [smul_neg, hx u hu, neg_zero], -z, by rw [Matrix.neg_mul]⟩

theorem acts_unique {κ : Type} [Fintype κ] (v : Pl (F := F)) (T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ)
    (φ φ₁ φ₂ : (κ → Fv F v) → ℂ) (hφ : φ ∈ SB (κ → Fv F v)) (h1 : Acts (evFin F v) T φ φ₁)
    (h2 : Acts (evFin F v) T φ φ₂) : φ₁ = φ₂ := by
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction κ v
  have e := (h1 R (hR φ hφ)).symm.trans (h2 R (hR φ hφ))
  funext y
  have hy := congrFun e (fun i => GlobalTheory.LatVac.liftV v (y i))
  simp only [tens] at hy
  have hev : (fun i => evFin F v (GlobalTheory.LatVac.liftV v (y i))) = y := funext fun i => GlobalTheory.LatVac.evFin_liftV v (y i)
  rw [hev] at hy
  have hRx : R (fun i => GlobalTheory.LatVac.liftV v (y i)) = R 0 := by
    have := (hR φ hφ).1 0 (fun i => GlobalTheory.LatVac.liftV v (y i)) (fun u hu => funext fun i => GlobalTheory.LatVac.at_liftV v (y i) u hu)
    simpa using this
  rw [hRx] at hy
  exact mul_right_cancel₀ hR0 hy

theorem eq_of_locCo {W : Type} [AddCommGroup W] [Module (AF F) W] {Bf : W → W → AF F} {κ : Type} [Fintype κ]
    (co : Darboux Bf κ) (v : Pl (F := F)) (g u : W) (hg : At (evFin F v) g) (hu : At (evFin F v) u)
    (h : GlobalTheory.LatVac.locCo co v g = GlobalTheory.LatVac.locCo co v u) : g = u := by
  have hA : ∀ z : W, At (evFin F v) z → ∀ k, At (evFin F v) ((co.e z).1 k) ∧ At (evFin F v) ((co.e z).2 k) := by
    intro z hz k
    refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · have := congrArg (fun p => p.1 k) (show co.e (t • z) = t • co.e z from co.e.map_smul t z)
      simpa [hz t ht] using this.symm
    · have := congrArg (fun p => p.2 k) (show co.e (t • z) = t • co.e z from co.e.map_smul t z)
      simpa [hz t ht] using this.symm
  apply co.e.injective
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
  · rw [GlobalTheory.VacAny.eq_atPlace_of_at v _ (hA g hg k).1, GlobalTheory.VacAny.eq_atPlace_of_at v _ (hA u hu k).1]
    exact congrArg _ (congrFun h1 k)
  · rw [GlobalTheory.VacAny.eq_atPlace_of_at v _ (hA g hg k).2, GlobalTheory.VacAny.eq_atPlace_of_at v _ (hA u hu k).2]
    exact congrArg _ (congrFun h2 k)

theorem exists_lagr_inv_vac : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∃ (C : Matrix (Fin (a + a')) (Fin ((a + a') / 2)) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (l : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] ℂ),
      GlobalTheory.InertVacLag.IsLagrAt σ G.W v C ∧ GlobalTheory.InertVacLag.HeisInv G.M' B.ψ v C l ∧ l (G.M'.vac v) ≠ 0 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hin _
  obtain ⟨Cy, hCy⟩ := GlobalTheory.InertLagr.exists_lagr F E σ B a a' G X om om' hT v w hin
  obtain ⟨C, hC⟩ := exists_map_compFin (E := E) v Cy
  have hLag : GlobalTheory.InertVacLag.IsLagrAt σ G.W v C := by
    unfold GlobalTheory.InertVacLag.IsLagrAt; rw [hC]; exact hCy
  set co := G.M'.co with hco
  set Λ := (lagSub (n := a') v C).map (GlobalTheory.LatVac.locCo co v) with hΛ
  set Γ := (latAtV G.V' G.W v).map (GlobalTheory.LatVac.locCo co v) with hΓ
  have hgood := hT.base.inert v w hin
  obtain ⟨hsb, hne, θ, hθ, hvac⟩ := hT.geo.hM'.vac v
  have hatL := (GlobalTheory.LatVac.latAtV_at_stable G.V' G.W v).1
  have hψc : Continuous (GlobalTheory.LatVac.psiAt B.ψ v) := hT.base.std.1.comp (GlobalTheory.VacAny.continuous_atPlace v)
  have hψ : ∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, GlobalTheory.LatVac.psiAt B.ψ v (x * y) = 1) →
      x ∈ v.adicCompletionIntegers F := fun x hx => (hgood.2.2 x).1 hx
  have hiso : ∀ x ∈ Λ, ∀ x' ∈ Λ, x.1 ⬝ᵥ x'.2 - x'.1 ⬝ᵥ x.2 = 0 := by
    rintro _ ⟨u, hu, rfl⟩ _ ⟨u', hu', rfl⟩
    have h0 := GlobalTheory.T.symplecticForm_eq_zero_of_lagrangianAtPlace σ G.V'.J G.W v C hLag (-1) u u' hu hu'
    change symp (cA σ) (-1) (incM F G.V'.J) (incM F G.W.J) u u' = 0 at h0
    rw [co.form] at h0
    have h1 := congrArg (evFin F v) h0

    simpa [GlobalTheory.LatVac.locCo, dotProduct, map_sum, map_mul, map_sub] using h1
  have hOC := GlobalTheory.LatOpenCpt.main σ B G.V' G.W _ _ _ _ hT.geo.hV' hT.geo.hW G.M' hT.geo.hM'.rat v
  have hdual := GlobalTheory.LatVac.DualLoc.map_selfDual v co B.ψ (latAtV G.V' G.W v) hatL
    (GlobalTheory.T.inertPlace_tensorLattice_selfDual_supportedAt F E σ B a a' G X om om' hT v w hin)
  have heig0 : ∀ g ∈ latAtV G.V' G.W v, schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo co v g) (G.M'.vac v) =
      B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) g g) • G.M'.vac v :=
    fun g hg => acts_unique v _ _ _ _ hsb (GlobalTheory.VacBridge.rho_acts_locCo co B.ψ v g (hatL g hg) _) (hvac g hg)
  have heig : ∀ γ ∈ Γ, ∃ c : ℂ, schr (GlobalTheory.LatVac.psiAt B.ψ v) γ (G.M'.vac v) = c • G.M'.vac v := by
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨_, heig0 g hg⟩
  have hfix : ∀ γ ∈ Γ ⊓ Λ, schr (GlobalTheory.LatVac.psiAt B.ψ v) γ (G.M'.vac v) = G.M'.vac v := by
    rintro γ ⟨⟨g, hg, rfl⟩, ⟨u, hu, hgu⟩⟩
    have e : g = u := eq_of_locCo co v g u (hatL g hg) hu.1 hgu.symm
    subst e
    rw [heig0 g hg, GlobalTheory.T.symplecticForm_eq_zero_of_lagrangianAtPlace σ G.V'.J G.W v C hLag _ g g hu hu, mul_zero, AddChar.map_zero_eq_one, one_smul]
  obtain ⟨l, hl, hl0⟩ := GlobalTheory.T.lagrangian_invariant_linearForm_local_uniqueness v (GlobalTheory.LatVac.psiAt B.ψ v) (Fin a' × Fin (a + a')) Λ Γ (G.M'.vac v) hψc hψ hiso
    hOC.1 hOC.2 hdual hsb hne heig hfix
  refine ⟨C, l, hLag, ?_, hl0⟩
  intro u hu φ hφ φ₁ _ hA
  have e := acts_unique v _ φ φ₁ _ hφ hA (GlobalTheory.VacBridge.rho_acts_locCo co B.ψ v u hu.1 φ)
  rw [e]
  exact hl _ ⟨u, hu, rfl⟩ φ hφ

end GlobalTheory.InertVacLagP

end
end
end
