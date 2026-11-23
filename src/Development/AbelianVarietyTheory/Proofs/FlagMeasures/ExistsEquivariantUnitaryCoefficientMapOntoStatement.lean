module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnWittFrameBasisBlockGramStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameComplementChangeOfBasis
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.HermitianForms.TiedStep
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MapFnOfEqValC
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TensorTypesRealPlacesEquivSpanWeylModules

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalFrameComplementRealPlaces

section

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.St.CFrame

theorem hJ_rv_gen (I : AutInst) (v : InfinitePlace I.F) (x y : Fin I.n → I.E) :
    hJ (I.ε v) (rv I v x) (rv I v y) = I.φ v (Formalism.UG.hform (starRingEnd I.E) I.J x y) := by
  have hPi : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
  have hJv : I.J.map (I.φ v) = ((I.P v)⁻¹)ᴴ * Formalism.REAL.Jm (I.ε v) * (I.P v)⁻¹ := by
    rw [← I.P_spec v]
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv _ hPi, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul,
      Matrix.mul_nonsing_inv _ hPi, Matrix.conjTranspose_one, Matrix.one_mul]
  unfold hJ rv
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hJv]

  simp only [dotProduct, mulVec, Pi.star_apply, Matrix.map_apply, Formalism.UG.hform, map_sum, map_mul,
  starRingEnd_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [I.cm.cmUnram.2.1]
  simp only [RCLike.star_def]
  ring

theorem hform_cols {A : Type} [CommRing A] {n ι : Type} [Fintype n] [Fintype ι] (σ : A →+* A)
    (J : Matrix n n A) (Q : Matrix n ι A) (α β : ι) :
    Formalism.UG.hform σ J (fun i => Q i α) (fun i => Q i β) = ((Q.map σ)ᵀ * J * Q) α β := by
  simp only [Formalism.UG.hform, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  exact Finset.sum_comm

variable {D : D7} (X : HidaSetting D)

theorem hJ_crd' (v : InfinitePlace X.B.I.F) (a b : (VS D).V) :
    hJ (X.B.I.ε v) (rv X.B.I v (X.crd a)) (rv X.B.I v (X.crd b)) = X.B.I.φ v (X.ιE.symm ((VS D).hT a b)) := by
  rw [hJ_rv_gen, ← Formalism.L2.SG.PoincareInHH.Cut.hform_crd X a b, RingEquiv.symm_apply_apply]

theorem card_eq : X.B.I.n = 2 * D.R.rS + D.R.k + 1 := by
  obtain ⟨t, ht⟩ := D.R.m_even
  have h2 := D.R.two_le_m
  rw [X.n_eq]
  simp only [Formalism.BasicNotions.Ranks.r, Formalism.BasicNotions.Ranks.rS]
  omega

end GlobalTheory.St.CFrame

namespace GlobalTheory.St.CFrame

variable {D : D7} (X : HidaSetting D)

theorem gram_blocks (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hw : WittX X u wt) :
    (∀ v a b, hJ (X.B.I.ε v) (rvV X v (qFr wt a)) (rvV X v (qFr wt b)) =
        X.B.I.φ v (X.ιE.symm (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _) a b))) ∧
    (∀ v c a, hJ (X.B.I.ε v) (rv X.B.I v (X.eR c)) (rvV X v (qFr wt a)) = 0 ∧
        hJ (X.B.I.ε v) (rv X.B.I v (X.fR c)) (rvV X v (qFr wt a)) = 0) ∧
    (∀ v a, hJ (X.B.I.ε v) (rv X.B.I v (X.zR u)) (rvV X v (qFr wt a)) = 0) ∧
    (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).det ≠ 0 := by
  obtain ⟨Q, Qi, G', hQQi, hQiQ, hq, he, hf, hz, _, hblk⟩ := GlobalTheory.T.columnWittFrame_basis_blockGram D X u wt hw
  have hent : ∀ α β, Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (fun i => Q i α) (fun i => Q i β) =
      Matrix.fromBlocks ((Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm) 0 0 G' α β := by
    intro α β
    rw [hform_cols, hblk]
  have colq : ∀ j, (fun i => Q i (Sum.inl j)) = X.crd (qFr wt j) := fun j => funext fun i => hq j i
  have cole : ∀ a, (fun i => Q i (Sum.inr (Sum.inl a))) = X.eR a := fun a => funext fun i => he a i
  have colf : ∀ a, (fun i => Q i (Sum.inr (Sum.inr (Sum.inl a)))) = X.fR a := fun a => funext fun i => hf a i
  have colz : (fun i => Q i (Sum.inr (Sum.inr (Sum.inr ())))) = X.zR u := funext fun i => hz i
  refine ⟨fun v a b => ?_, fun v c a => ⟨?_, ?_⟩, fun v a => ?_, ?_⟩
  · have h := hent (Sum.inl a) (Sum.inl b)
    rw [colq, colq] at h
    rw [rvV, rvV, hJ_rv_gen, h]
    rfl
  · have h := hent (Sum.inr (Sum.inl c)) (Sum.inl a)
    rw [cole, colq] at h
    rw [rvV, hJ_rv_gen, h]
    simp
  · have h := hent (Sum.inr (Sum.inr (Sum.inl c))) (Sum.inl a)
    rw [colf, colq] at h
    rw [rvV, hJ_rv_gen, h]
    simp
  · have h := hent (Sum.inr (Sum.inr (Sum.inr ()))) (Sum.inl a)
    rw [colz, colq] at h
    rw [rvV, hJ_rv_gen, h]
    simp
  · intro h0
    have hJu : IsUnit X.B.I.J.det := isUnit_iff_ne_zero.2 X.B.I.J_det
    have e1 : (Q.map (starRingEnd X.B.I.E))ᵀ * (Qi.map (starRingEnd X.B.I.E))ᵀ = 1 := by
      rw [← Matrix.transpose_mul, ← Matrix.map_mul, hQiQ, Matrix.map_one _ (map_zero _) (map_one _),
        Matrix.transpose_one]
    have hinv : ((Q.map (starRingEnd X.B.I.E))ᵀ * X.B.I.J * Q) *
        (Qi * X.B.I.J⁻¹ * (Qi.map (starRingEnd X.B.I.E))ᵀ) = 1 := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Q Qi, hQQi, Matrix.one_mul, ← Matrix.mul_assoc X.B.I.J X.B.I.J⁻¹,
        Matrix.mul_nonsing_inv _ hJu, Matrix.one_mul, e1]
    rw [hblk] at hinv
    have hd := congrArg Matrix.det hinv
    rw [Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one] at hd
    have hA : ((Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm).det = 0 := by
      rw [show ((Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm).det =
          X.ιE.symm.toRingHom (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).det from
          (RingHom.map_det X.ιE.symm.toRingHom _).symm, h0, map_zero]
    rw [hA, zero_mul, zero_mul] at hd
    exact zero_ne_one hd

end GlobalTheory.St.CFrame

namespace GlobalTheory.St.CFrame

theorem frame_of_type : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V), WittX X u wt → ∃ o : Formalism.L2.Forms.Fr D 0 (Nat.zero_le _), (∀ τ, (o.1 τ)ᴴ * Formalism.L2.Forms.gramC (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Formalism.L2.Forms.embT D) τ * o.1 τ = 1) ∧ ∀ s ∈ Hinf X u, ∃ m : D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ, ∀ τ, m τ ∈ Matrix.unitaryGroup (Fin (D.R.N 0)) ℂ ∧ (m τ).submatrix (Fin.cast D.R.N_zero.symm) (Fin.cast D.R.N_zero.symm) = matW X.B.I (X.wfr u (X.pl.symm τ)) (X.pl.symm τ) s ∧ sTil X wt s τ = o.1 τ * m τ * (o.1 τ)⁻¹ := by
  intro D X u wt hw
  obtain ⟨hqq, hqef, hqz, hdet⟩ := gram_blocks X u wt hw
  have hgQ : ∀ v, gramQ X wt v = (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map (Formalism.L2.Forms.embT D (X.pl v)) := by
    intro v
    ext a b
    simp only [gramQ, Matrix.of_apply, Matrix.map_apply]
    rw [hqq, X.φ_eq, RingEquiv.apply_symm_apply]
    rfl
  have hGu : ∀ v, IsUnit (gramQ X wt v).det := by
    intro v
    rw [hgQ, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact isUnit_iff_ne_zero.2 ((map_ne_zero _).2 hdet)
  have hJm : ∀ v, IsUnit (Formalism.REAL.Jm (X.B.I.ε v)).det :=
    fun v => Matrix.isUnit_det_of_left_inverse (Formalism.REAL.Jm_mul_self _)
  have key := fun v => GlobalTheory.frame_complement_change_of_basis X.B.I.n D.R.rS D.R.k (D.R.N 0) D.R.N_zero.symm (Formalism.REAL.Jm (X.B.I.ε v))
    (fun a => rv X.B.I v (X.eR a)) (fun a => rv X.B.I v (X.fR a)) (rv X.B.I v (X.zR u)) (X.wfr u v)
    (fun a => rvV X v (qFr wt a)) (card_eq X) (Formalism.REAL.Jm_conjTranspose _) (hJm v)
    (fun a b => by
      show hJ (X.B.I.ε v) _ _ = 0
      refine (hJ_crd' X v (X.eX a) (X.eX b)).trans ?_
      rw [X.ee]; simp)
    (fun a b => by
      show hJ (X.B.I.ε v) _ _ = 0
      refine (hJ_crd' X v (X.fY a) (X.fY b)).trans ?_
      rw [X.ff]; simp)
    (fun a b => by
      show hJ (X.B.I.ε v) _ _ = _
      refine (hJ_crd' X v (X.eX a) (X.fY b)).trans ?_
      rw [X.ef]; split_ifs <;> simp)
    (fun a => ⟨by
      show hJ (X.B.I.ε v) _ _ = 0
      refine (hJ_crd' X v (X.eX a) (X.zu u)).trans ?_
      rw [(X.zu_orth u a).1]; simp, by
      show hJ (X.B.I.ε v) _ _ = 0
      refine (hJ_crd' X v (X.fY a) (X.zu u)).trans ?_
      rw [(X.zu_orth u a).2]; simp⟩)
    (by
      show hJ (X.B.I.ε v) _ _ ≠ 0
      refine (hJ_crd' X v (X.zu u) (X.zu u)).trans_ne ?_
      rw [X.zu_norm]
      have hT : (((D.mem u).A.T : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (D.mem u).A.T_prime.ne_zero
      simpa using hT)
    (X.wfr_on u v) (X.wfr_perp u v)
    (fun a => ⟨fun c => ⟨(hqef v c a).1, (hqef v c a).2⟩, hqz v a⟩)
    (gramQ X wt v) (fun a b => rfl) (hGu v)
  choose oo hoo using key
  refine ⟨⟨fun τ => oo (X.pl.symm τ), fun τ => (hoo _).1⟩, fun τ => ?_, fun s hs => ?_⟩
  · have h := (hoo (X.pl.symm τ)).2.1
    rw [hgQ, Equiv.apply_symm_apply] at h
    exact h
  · have hfix : ∀ v, ∀ x ∈ fixSet X u, uMat (s v) *ᵥ rv X.B.I v x = rv X.B.I v x := hs
    have hm := fun τ => (hoo (X.pl.symm τ)).2.2 (uMat (s (X.pl.symm τ))) (s (X.pl.symm τ)).2
      (fun a => ⟨hfix _ _ (Or.inl (Or.inl ⟨a, rfl⟩)), hfix _ _ (Or.inl (Or.inr ⟨a, rfl⟩))⟩)
      (hfix _ _ (Or.inr rfl))
    choose m hmU hmW hmT using hm
    exact ⟨m, fun τ => ⟨hmU τ, hmW τ, hmT τ⟩⟩

end GlobalTheory.St.CFrame
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalFrameComplementRealPlacesStatement

section

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_orthonormalFrame_complement_realPlaces : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V), WittX X u wt → ∃ o : Formalism.L2.Forms.Fr D 0 (Nat.zero_le _), (∀ τ, (o.1 τ)ᴴ * Formalism.L2.Forms.gramC (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Formalism.L2.Forms.embT D) τ * o.1 τ = 1) ∧ ∀ s ∈ Hinf X u, ∃ m : D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ, ∀ τ, m τ ∈ Matrix.unitaryGroup (Fin (D.R.N 0)) ℂ ∧ (m τ).submatrix (Fin.cast D.R.N_zero.symm) (Fin.cast D.R.N_zero.symm) = matW X.B.I (X.wfr u (X.pl.symm τ)) (X.pl.symm τ) s ∧ sTil X wt s τ = o.1 τ * m τ * (o.1 τ)⁻¹ := by
  first | exact @GlobalTheory.St.CFrame.frame_of_type | exact GlobalTheory.St.CFrame.frame_of_type | (intros; apply GlobalTheory.St.CFrame.frame_of_type <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.HcParamEqWeightStepZeroAddRho

section

@[expose] public section

open Formalism.BasicNotions

namespace GlobalTheory

theorem hcParam_eq_weight_step_zero_add_rho : ∀ (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) (i : Fin D.R.k), (((D.hcW u τ).u i : ℚ) : ℝ) = ((Formalism.L2.Forms.lamT u 0 τ).w (Fin.cast D.R.N_zero.symm i) : ℝ) + ((rhoVec D.R.k i : ℚ) : ℝ) := by
  intro D u τ i
  rw [Formalism.L2.Forms.lamT_zero]
  have h0 := (D.fm u).lam_eq 0 (Nat.zero_le _) τ (Fin.cast D.R.N_zero.symm i)
  rw [dite_eq_left (show (Fin.cast D.R.N_zero.symm i : ℕ) < D.R.k from i.2)] at h0
  have hq : ((D.hcW u τ).u i : ℚ) =
      (((D.fm u).lam 0 τ).w (Fin.cast D.R.N_zero.symm i) : ℚ) + rhoVec D.R.k i := by
    rw [h0, hcToWeightQ]
    simp
  rw [hq]
  push_cast
  ring

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.TensorTypesRealPlacesEquivSpanWeylModulesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

theorem _root_.GlobalTheory.T.tensor_types_realPlaces_equiv_span_weylModules : ∀ (ι : Type) [Fintype ι] (k n : ℕ) (h : k = n) (lam : ι → DomWeight n) (u : ι → Fin k → ℝ), (∀ τ (i : Fin k), u τ i = ((lam τ).w (Fin.cast h i) : ℝ) + ((rhoVec k i : ℚ) : ℝ)) → ∀ (Vl : ι → Type) [∀ τ, NormedAddCommGroup (Vl τ)] [∀ τ, InnerProductSpace ℂ (Vl τ)] (πl : ∀ τ, Matrix (Fin k) (Fin k) ℂ → (Vl τ →L[ℂ] Vl τ)), (∀ τ, IsHCTypeU k (u τ) (πl τ)) → ∀ (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (tens : (∀ τ, Vl τ) → W), (∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ τ, ⟪x τ, y τ⟫_ℂ) → Submodule.span ℂ (Set.range tens) = ⊤ → ∃ Jp : W →ₗ⋆[ℂ] MvPolynomial (ι × Fin n × Fin n) ℂ, (∀ ξ, Jp ξ ∈ CSpan lam) ∧ (∀ p ∈ CSpan lam, ∃ ξ, Jp ξ = p) ∧ (∀ ξ η, nfAll lam (Jp η) (Jp ξ) = ⟪η, ξ⟫_ℂ) ∧ ∀ (m : ι → Matrix (Fin n) (Fin n) ℂ), (∀ τ, m τ ∈ Matrix.unitaryGroup (Fin n) ℂ) → ∀ A : W →L[ℂ] W, (∀ x, A (tens x) = tens (fun τ => πl τ ((m τ).submatrix (Fin.cast h) (Fin.cast h)) (x τ))) → ∀ (G o : ι → Matrix (Fin n) (Fin n) ℂ), (∀ τ, IsUnit (o τ).det) → ∀ (ξ : W) (y y' : Frames G), IsTr (fun τ => o τ * m τ * (o τ)⁻¹) y' y → fnOf G (shiftOf lam) (fun τ => (o τ)⁻¹) (Jp (A ξ)) y = fnOf G (shiftOf lam) (fun τ => (o τ)⁻¹) (Jp ξ) y' := by
  first | exact @GlobalTheory.TenTypes.tensor_dict | exact GlobalTheory.TenTypes.tensor_dict | (intros; apply GlobalTheory.TenTypes.tensor_dict <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEquivariantUnitaryCoefficientMapOnto

section

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St

theorem coefficient_map_exists_onto : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V), WittX X u wt → ∃ J : X.Vpi u →ₗ⋆[ℂ] (Formalism.L2.Forms.Fr D 0 (Nat.zero_le _) → ℂ), JOK X u F wt J ∧ ∀ p ∈ Formalism.L2.Forms.ValC (Formalism.L2.Forms.gramC (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Formalism.L2.Forms.embT D)) (Formalism.L2.Forms.lamT u 0), ∃ ξ, J ξ = p := by
  intro D X u F wt hw
  obtain ⟨o, ho, hfr⟩ := GlobalTheory.T.exists_orthonormalFrame_complement_realPlaces D X u wt hw
  let e := Equiv.piCongrLeft (X.Vloc u) X.pl.symm
  have he : ∀ (x : ∀ τ, X.Vloc u (X.pl.symm τ)) τ, e x (X.pl.symm τ) = x τ := fun x τ =>
    Equiv.piCongrLeft_apply_apply (X.Vloc u) X.pl.symm x τ
  let tens : (∀ τ, X.Vloc u (X.pl.symm τ)) → X.Vpi u := fun x => X.tensU u (e x)
  have hin : ∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ τ, ⟪x τ, y τ⟫_ℂ := by
    intro x y
    show ⟪X.tensU u (e x), X.tensU u (e y)⟫_ℂ = _
    rw [X.tensU_inner, ← Equiv.prod_comp X.pl.symm]
    exact Finset.prod_congr rfl fun τ _ => by rw [he, he]
  have hsp : Submodule.span ℂ (Set.range tens) = ⊤ := by
    have : Set.range tens = Set.range (X.tensU u) := e.surjective.range_comp _
    rw [this]; exact X.tensU_span u
  have hty : ∀ τ, IsHCTypeU D.R.k (fun i => (((D.hcW u τ).u i : ℚ) : ℝ)) (X.piLoc u (X.pl.symm τ)) := by
    intro τ
    have h := X.piLoc_type u (X.pl.symm τ)
    rwa [X.pl.apply_symm_apply] at h
  obtain ⟨Jp, hJv, hJs, hJi, hJe⟩ := GlobalTheory.T.tensor_types_realPlaces_equiv_span_weylModules D.what₂.Tau D.R.k (D.R.N 0) D.R.N_zero.symm
    (Formalism.L2.Forms.lamT u 0) (fun τ i => (((D.hcW u τ).u i : ℚ) : ℝ))
    (fun τ i => GlobalTheory.hcParam_eq_weight_step_zero_add_rho D u τ i)
    (fun τ => X.Vloc u (X.pl.symm τ)) (fun τ => X.piLoc u (X.pl.symm τ)) hty (X.Vpi u) tens hin hsp
  have hoinv : ∀ τ, IsUnit ((o.1 τ)⁻¹).det := fun τ => by
    have h := o.2 τ
    rw [Matrix.det_nonsing_inv]
    exact (Ring.inverse_unit h.unit ▸ (h.unit⁻¹).isUnit)
  have hmap := GlobalTheory.ValueSpaceCoordinates.map_fnOf_eq_ValC D.what₂.Tau (D.R.N 0) (Formalism.L2.Forms.lamT u 0)
    (Formalism.L2.Forms.gramC (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Formalism.L2.Forms.embT D))
    (fun τ => (o.1 τ)⁻¹) hoinv
  let fo := Formalism.L2.Forms.fnOf (Formalism.L2.Forms.gramC (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Formalism.L2.Forms.embT D))
    (Formalism.L2.Forms.shiftOf (Formalism.L2.Forms.lamT u 0)) (fun τ => (o.1 τ)⁻¹)
  refine ⟨fo.comp Jp, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro s hs ξ y y' hyy
    obtain ⟨m, hm⟩ := hfr s hs
    have hA : ∀ x, X.piU u s (tens x) = tens (fun τ =>
        X.piLoc u (X.pl.symm τ) ((m τ).submatrix (Fin.cast D.R.N_zero.symm) (Fin.cast D.R.N_zero.symm)) (x τ)) := by
      intro x
      show X.piU u s (X.tensU u (e x)) = X.tensU u (e _)
      rw [X.tensU_equiv u s hs (e x)]
      congr 1
      funext v
      obtain ⟨τ, rfl⟩ := X.pl.symm.surjective v
      rw [he, he, (hm τ).2.1]
    have hy : Formalism.L2.Forms.IsTr (fun τ => o.1 τ * m τ * (o.1 τ)⁻¹) y' y := fun τ => by
      rw [hyy τ, (hm τ).2.2]
    exact hJe m (fun τ => (hm τ).1) (X.piU u s) hA _ o.1 (fun τ => o.2 τ) ξ y y' hy
  · intro ξ
    rw [← hmap]
    exact ⟨Jp ξ, hJv ξ, rfl⟩
  · intro c ξ η
    have hon : o.IsON := fun τ => Or.inl (ho τ)
    have hP : ∀ ζ, Jp ζ ∈ Formalism.L2.Forms.CSpan ((D.fm u).lam 0) := fun ζ => by
      rw [← Formalism.L2.Forms.lamT_zero]; exact hJv ζ
    have h := F.val0.ipV c o hon (Jp ξ) (hP ξ) (Jp η) (hP η)
    rw [← Formalism.L2.Forms.lamT_zero] at h
    exact h.trans (hJi ξ η)
  · intro p hp
    rw [← hmap] at hp
    obtain ⟨P, hP, rfl⟩ := hp
    obtain ⟨ξ, rfl⟩ := hJs P hP
    exact ⟨ξ, rfl⟩

end GlobalTheory.St
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEquivariantUnitaryCoefficientMapOntoStatement

section

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_equivariant_unitary_coefficientMap_onto : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V), WittX X u wt → ∃ J : X.Vpi u →ₗ⋆[ℂ] (Formalism.L2.Forms.Fr D 0 (Nat.zero_le _) → ℂ), JOK X u F wt J ∧ ∀ p ∈ Formalism.L2.Forms.ValC (Formalism.L2.Forms.gramC (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Formalism.L2.Forms.embT D)) (Formalism.L2.Forms.lamT u 0), ∃ ξ, J ξ = p := by
  first | exact @GlobalTheory.St.coefficient_map_exists_onto | exact GlobalTheory.St.coefficient_map_exists_onto | (intros; apply GlobalTheory.St.coefficient_map_exists_onto <;> assumption)
end
end
