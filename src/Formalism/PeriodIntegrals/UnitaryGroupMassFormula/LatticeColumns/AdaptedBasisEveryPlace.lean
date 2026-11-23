module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.HAdaptRed
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SecondCoordsCongruentMod
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.SecondProjWeightVectorZero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ExistsGlOfLeftInv
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.FrAIntReindex
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.MatRMulMatC
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.InGMulInt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.AdqHRRatV
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.PsiVIteOne
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.HacFrame
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SplitLatticeBasisExists

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.AdaptInDet

section

@[expose] public section

noncomputable section

namespace PIW.MassDataColumns

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxRed MassDataIdxSpl
  MassDataIdxFrA MassDataIdxAdA MassDataIdxSteps Formalism.FourierDecayAlt.S3
open scoped Matrix TensorProduct

variable {D : D7}

section B

variable (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (p : TypX X)
  (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p) (P : GL (IdxD D) (FpX X p))

def vT : IdxD D → Fin X.B.I.n → TpX X p
  | Sum.inr (Sum.inl (Sum.inl i)) => adqM X hb u p *ᵥ PI.FinKW.vecV X.B.I p.1 (X.bw i)
  | Sum.inl a => ratV (F := X.B.I.F) (FpX X p) (vecAt (k := D.R.k) (frameOf X u) (Sum.inl a))
  | Sum.inr (Sum.inl (Sum.inr v)) => ratV (F := X.B.I.F) (FpX X p) (vecAt (k := D.R.k) (frameOf X u) (Sum.inr (Sum.inl (Sum.inr v))))
  | Sum.inr (Sum.inr c) => ratV (F := X.B.I.F) (FpX X p) (vecAt (k := D.R.k) (frameOf X u) (Sum.inr (Sum.inr c)))

def mT : Matrix (IdxD D) (IdxD D) (FpX X p) := fun j t => crd1 X p θ P (vT X hb u p t) j

theorem mC_eq :
    ((P⁻¹ : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p)) *
      ofCols (colv (cV X u p θ) (yV X hb u p θ)) = mT X hb u p θ P := by
  ext j t
  have e : (((P⁻¹ : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p)) *
      ofCols (colv (cV X u p θ) (yV X hb u p θ))) j t =
      (((P⁻¹ : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p)) *ᵥ
        colv (cV X u p θ) (yV X hb u p θ) t) j := by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, ofCols]
  rw [e]
  rcases t with a | ((i | v) | c) <;> rfl

theorem vT_cong (t : IdxD D) : vT X hb u p t - adqRef X hb u p t ∈ gLam X p := by
  rcases t with a | ((i | v) | c)
  · exact adq_e_cong X hb u p a
  · show adqM X hb u p *ᵥ PI.FinKW.vecV X.B.I p.1 (X.bw i) -
      adqM X hb u p *ᵥ PI.FinKW.vecV X.B.I p.1 (X.bw i) ∈ gLam X p
    rw [sub_self]
    exact zero_mem _
  · exact adq_z_cong X hb u p
  · exact adq_f_cong X hb u p (Fin.rev c)

theorem vT_cong1 (hL : LatBasis X p θ (reindex₂ X p P)) (t j : IdxD D) :
    InG X p (crd1 X p θ P (vT X hb u p t) j - crd1 X p θ P (adqRef X hb u p t) j) :=
  firstCoords_congruent_mod X p θ P hL _ _ (vT_cong X hb u p t) j

theorem vT_int (hL : LatBasis X p θ (reindex₂ X p P)) (t j : IdxD D) :
    crd1 X p θ P (vT X hb u p t) j ∈ OvA X p := by
  have h := (OvA X p).add_mem _ _ (adq_inG_int X p (vT_cong1 X hb u p θ P hL t j))
    (((latCrd_of X p θ P hL _).1 (adq_ref_lat X hb u p t)).1 j)
  rwa [sub_add_cancel] at h

theorem vT_RC (hθ : IsSplitEquiv X p θ) (hε : θ (epsP X p) = (1, 0)) (hL : LatBasis X p θ (reindex₂ X p P))
    (s t : IdxD D) : ∃ z : OvA X p, (adqR X hb u p θ P * mT X hb u p θ P) s t =
      (1 : Matrix (IdxD D) (IdxD D) (FpX X p)) s t + ((gOf p : ℕ) : FpX X p) * (z : FpX X p) := by
  have e1 : (adqR X hb u p θ P * mT X hb u p θ P) s t =
      sgnV X p s * (crd2 X p θ P (adqRefR X hb u p s) ⬝ᵥ crd1 X p θ P (vT X hb u p t)) := by
    simp only [Matrix.mul_apply, adqR, mT, dotProduct, Finset.mul_sum, mul_assoc]
  have hD := adq_dotG X p (a := crd2 X p θ P (adqRefR X hb u p s)) (a' := crd2 X p θ P (adqRefR X hb u p s))
    (b := crd1 X p θ P (vT X hb u p t)) (b' := crd1 X p θ P (adqRef X hb u p t))
    (fun j => ((latCrd_of X p θ P hL _).1 (adq_refR_lat X hb u p s)).2 j)
    (fun j => vT_int X hb u p θ P hL t j) (fun j => by rw [sub_self]; exact inG_zero)
    (fun j => vT_cong1 X hb u p θ P hL t j)
  rw [adq_pairM X hb u p θ P hθ] at hD
  obtain ⟨y, hy⟩ := inG_mul_int _ (sgnV_int X p s) hD
  obtain ⟨z, hz⟩ := rc_cong X p θ P hθ hε hL s t
  refine ⟨y + z, ?_⟩
  rw [e1]
  push_cast
  linear_combination hy + hz

theorem adaptIn_det (hθ : IsSplitEquiv X p θ) (hε : θ (epsP X p) = (1, 0)) (hL : LatBasis X p θ (reindex₂ X p P)) :
    IntO (p.1.adicCompletionIntegers X.B.I.F).toSubring
        (((P⁻¹ : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p)) *
          ofCols (colv (cV X u p θ) (yV X hb u p θ))) ∧
      ∃ uu : FpX X p, uu ∈ p.1.adicCompletionIntegers X.B.I.F ∧
        (((P⁻¹ : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p)) *
          ofCols (colv (cV X u p θ) (yV X hb u p θ))).det * uu = 1 := by
  rw [mC_eq X hb u p θ P]
  choose N hN using fun s t => vT_RC X hb u p θ P hθ hε hL s t
  have hgc : ((gA X p : OvA X p) : FpX X p) = ((gOf p : ℕ) : FpX X p) := by simp [gA]
  have hRC : adqR X hb u p θ P * mT X hb u p θ P =
      1 + ((gA X p : OvA X p) : FpX X p) • Matrix.of (fun s t => ((N s t : OvA X p) : FpX X p)) := by
    ext s t
    rw [hN s t, hgc]
    simp
  obtain ⟨c, hc⟩ := exists_gl_of_left_inv (OvA X p) (gA X p) (PIW.MassDataColumns.gOf_nonunit X p)
    (mT X hb u p θ P) (adqR X hb u p θ P) _
    (fun i t => vT_int X hb u p θ P hL t i)
    (fun s i => (OvA X p).mul_mem _ _ (sgnV_int X p s)
      (((latCrd_of X p θ P hL _).1 (adq_refR_lat X hb u p s)).2 i))
    (fun s t => (N s t).2) hRC
  refine ⟨fun i t => vT_int X hb u p θ P hL t i,
    ((((c⁻¹ : GL (IdxD D) (OvA X p)) : Matrix (IdxD D) (IdxD D) (OvA X p)).det : OvA X p) : FpX X p),
    (((c⁻¹ : GL (IdxD D) (OvA X p)) : Matrix (IdxD D) (IdxD D) (OvA X p)).det : OvA X p).2, ?_⟩
  have hdet : (mT X hb u p θ P).det = (((c : Matrix (IdxD D) (IdxD D) (OvA X p)).det : OvA X p) : FpX X p) := by
    rw [← hc]
    exact (RingHom.map_det (OvA X p).subtype (c : Matrix (IdxD D) (IdxD D) (OvA X p))).symm
  have hu : (c : Matrix (IdxD D) (IdxD D) (OvA X p)).det *
      ((c⁻¹ : GL (IdxD D) (OvA X p)) : Matrix (IdxD D) (IdxD D) (OvA X p)).det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  rw [hdet]
  have := congrArg (fun x : OvA X p => (x : FpX X p)) hu
  simpa using this

end B

end PIW.MassDataColumns
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.DotPTPinv

section

@[expose] public section

noncomputable section

namespace PIW.MassDataColumns

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxRed MassDataIdxSpl
  MassDataIdxFrA MassDataIdxAdA MassDataIdxSteps Formalism.FourierDecayAlt.S3
open scoped Matrix TensorProduct

variable {D : D7}

section B

variable (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (p : TypX X)
  (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p) (P : GL (IdxD D) (FpX X p))

theorem yV_crd (i : Fin D.R.k) :
    ((P⁻¹ : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p)) *ᵥ yV X hb u p θ i =
      crd1 X p θ P (adqM X hb u p *ᵥ PI.FinKW.vecV X.B.I p.1 (X.bw i)) := rfl

theorem dot_PT_Pinv (a w : IdxD D → FpX X p) :
    ((P : Matrix (IdxD D) (IdxD D) (FpX X p))ᵀ *ᵥ a) ⬝ᵥ
      (((P⁻¹ : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p)) *ᵥ w) = a ⬝ᵥ w := by
  rw [Matrix.mulVec_transpose, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel,
    Units.val_one, Matrix.vecMul_one]

theorem aV_dot (s : IdxD D) (w : IdxD D → FpX X p) :
    aV X u p θ s ⬝ᵥ w = crd2 X p θ P (ratV (F := X.B.I.F) (FpX X p) (vecAt (frameOf X u) s)) ⬝ᵥ
      (((P⁻¹ : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p)) *ᵥ w) := by
  unfold crd2 aV
  exact (dot_PT_Pinv X p P _ _).symm

theorem ay_gen (hθ : IsSplitEquiv X p θ) (hL : LatBasis X p θ (reindex₂ X p P)) (i : Fin D.R.k)
    (V : Fin X.B.I.n → TpX X p) (v0 : Formalism.L2.SG.HidaSetting.VA X.B.I)
    (hw : adqM X hb u p *ᵥ PI.FinKW.vecV X.B.I p.1 v0 ∈
      latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)))
    (hd : V - adqM X hb u p *ᵥ PI.FinKW.vecV X.B.I p.1 v0 ∈ gLam X p)
    (h0 : ∃ z : OvA X p, crd2 X p θ P (PI.FinKW.vecV X.B.I p.1 v0) ⬝ᵥ
      crd1 X p θ P (PI.FinKW.vecV X.B.I p.1 (X.bw i)) = ((gOf p : ℕ) : FpX X p) * (z : FpX X p)) :
    InG X p (crd2 X p θ P V ⬝ᵥ crd1 X p θ P (adqM X hb u p *ᵥ PI.FinKW.vecV X.B.I p.1 (X.bw i))) := by
  have hyi : ∀ j, crd1 X p θ P (adqM X hb u p *ᵥ PI.FinKW.vecV X.B.I p.1 (X.bw i)) j ∈ OvA X p :=
    fun j => ((latCrd_of X p θ P hL _).1 (adq_ref_lat X hb u p (wI i))).1 j
  have h1 := adq_dotG X p (a := crd2 X p θ P V)
    (a' := crd2 X p θ P (adqM X hb u p *ᵥ PI.FinKW.vecV X.B.I p.1 v0))
    (b := crd1 X p θ P (adqM X hb u p *ᵥ PI.FinKW.vecV X.B.I p.1 (X.bw i)))
    (b' := crd1 X p θ P (adqM X hb u p *ᵥ PI.FinKW.vecV X.B.I p.1 (X.bw i)))
    (fun j => ((latCrd_of X p θ P hL _).1 hw).2 j) hyi
    (secondCoords_congruent_mod X p θ P hL _ _ hd) (fun j => by rw [sub_self]; exact inG_zero)
  rw [adq_pairM X hb u p θ P hθ] at h1
  obtain ⟨z, hz⟩ := h0
  rw [hz] at h1
  have h3 := inG_add h1 (inG_g_mul (X := X) (p := p) z)
  rwa [sub_add_cancel] at h3

theorem ay_inG (hθ : IsSplitEquiv X p θ) (hL : LatBasis X p θ (reindex₂ X p P)) (s : IdxD D) (hs : ¬ IsW s)
    (i : Fin D.R.k) : InG X p (aV X u p θ s ⬝ᵥ yV X hb u p θ i) := by
  rw [aV_dot X u p θ P, yV_crd X hb u p θ P]
  rcases s with a | ((j | v) | c)
  · exact ay_gen X hb u p θ P hθ hL i _ (X.e0 a) (adq_ref_lat X hb u p (Sum.inl a)) (adq_e_cong X hb u p a)
      (fin_dir X p θ P hθ hL _ _ ((X.weightVectorsIntegral i).2.2 a).1)
  · exact absurd ⟨j, rfl⟩ hs
  · exact ay_gen X hb u p θ P hθ hL i _ X.z0 (adq_ref_lat X hb u p zI) (adq_z_cong X hb u p)
      (fin_dir X p θ P hθ hL _ _ (X.weightVectorsIntegral i).1)
  · exact ay_gen X hb u p θ P hθ hL i _ (X.f0 (Fin.rev c)) (adq_refR_lat X hb u p (Sum.inl (Fin.rev c)))
      (adq_f_cong X hb u p (Fin.rev c)) (fin_dir X p θ P hθ hL _ _ ((X.weightVectorsIntegral i).2.2 (Fin.rev c)).2.1)

theorem adaptIn_ay (hθ : IsSplitEquiv X p θ) (hL : LatBasis X p θ (reindex₂ X p P)) :
    ∃ o : IdxD D → Fin D.R.k → FpX X p,
      (∀ s i, ¬ IsW s → aV X u p θ s ⬝ᵥ yV X hb u p θ i = ((gOf p : ℕ) : FpX X p) * o s i) ∧
      (∀ s i, o s i ∈ p.1.adicCompletionIntegers X.B.I.F) := by
  have h : ∀ (s : IdxD D) (i : Fin D.R.k), ∃ y : OvA X p,
      ¬ IsW s → aV X u p θ s ⬝ᵥ yV X hb u p θ i = ((gOf p : ℕ) : FpX X p) * (y : FpX X p) := by
    intro s i
    by_cases hs : IsW s
    · exact ⟨0, fun h => absurd hs h⟩
    · obtain ⟨y, hy⟩ := ay_inG X hb u p θ P hθ hL s hs i
      exact ⟨y, fun _ => hy⟩
  choose o ho using h
  exact ⟨fun s i => (o s i : FpX X p), ho, fun s i => (o s i).2⟩

end B

end PIW.MassDataColumns
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.AdaptedBasisEveryPlace

section

@[expose] public section

noncomputable section

namespace PIW.MassDataColumns

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets Formalism.L2.SG.Measures Formalism.L2.SG.Sub
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain Formalism.FourierDecayAlt.S3 MassDataIdxSteps MassDataIdxStIm MassDataIdxSpl
open scoped Matrix TensorProduct

variable {D : D7}

theorem adaptIn_holds (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (p : TypX X) :
    AdaptIn X hb u p := by
  obtain ⟨θ, hθ, hε⟩ := exists_split_eps X p
  obtain ⟨P, hL⟩ := exists_GL_latBasis_of_isSplitEquiv X p θ hθ
  obtain ⟨o, hay, ho⟩ := adaptIn_ay X hb u p θ P hθ hL
  obtain ⟨hC, uu, huu, hdet⟩ := adaptIn_det X hb u p θ P hθ hε hL
  exact ⟨θ, hθ, P, hL, lF X u p θ, o, uu, fun s t hs ht => hac_frame X u p θ hθ s t hs ht, hay,
    fun s hs => (lF_unit X u p θ hb hθ s hs).1, fun s hs => (lF_unit X u p θ hb hθ s hs).2, ho, hC, huu, hdet⟩

theorem adapted_basis_every_place : AdaptInAll :=
  fun X hb _ u _ _ p => adaptIn_holds X hb u p

end PIW.MassDataColumns
end
end
end
