module

public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.InvarianceIffAdditiveMapsExist
public import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.NumericalIdentityScalar
public import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.BranchingSourceIdentity
public import Formalism.LocalToGlobal.GroupLattices.FockModels.TestSideEdge
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
import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.ProdItePow
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FinalC
public import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.HighestVectorFullHolds
import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.InterpolationHolds
public import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.TransposedFrameImageBlockwiseHolds
import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.YVMapRowAct
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.SumIccEqRange
import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.TransposedFrameImageBlockwiseHolds
public import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.XShape
public import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.AdmissibleGeneralLatticeTuple
import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSp

-- Source module: Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.FrameEdgeIdentityHolds

section

@[expose] public section

open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] (X : Sys p)

def dgQ (K : Type) [Field K] (p k r : ℕ) : Matrix (Fin k) (Fin k) K := Matrix.diagonal fun c => if c.val < r then (p : K)⁻¹ else 1

theorem dgQ_det_ne (K : Type) [Field K] (p k r : ℕ) (hp : (p : K) ≠ 0) : (dgQ K p k r).det ≠ 0 := by
  unfold dgQ
  rw [Matrix.det_diagonal]
  refine Finset.prod_ne_zero_iff.2 fun c _ => ?_
  split_ifs
  · exact inv_ne_zero hp
  · exact one_ne_zero

theorem mF_dgQ (j : ℕ) (b : BX X) (i0 : X.Pl → ℕ) :
    mF X (j + 1) b (dgQ (X.G.P.Qq b.1) p _ (i0 b.1)) = DgX X X.G.Kf j i0 b.1 := by
  unfold mF dgQ DgX
  ext a c
  simp only [Matrix.submatrix_apply, Matrix.map_apply, Matrix.diagonal_apply]
  by_cases hac : a = c
  · subst hac
    rw [if_pos rfl, if_pos rfl]
    have : ((finCongr (rank_eq X (j + 1)).symm) a).val = a.val := rfl
    rw [this]
    split_ifs
    · rw [map_inv₀, map_inv₀, map_natCast, map_natCast]
    · rw [map_one, map_one]
  · rw [if_neg hac, if_neg (fun h => hac ((finCongr (rank_eq X (j + 1)).symm).injective h)), map_zero, map_zero]

theorem frame_edge_identity_holds : XEdge := by
  intro p _ X j L' L'' i0 h2 h4
  have key : ∀ v : X.Pl, ∃ g' h' : GL (Fin ((X.Pj (j + 1)).m + 1)) (X.G.P.Qq v),
      X.latAt v (j + 1) L'' = colSpan (X.G.P.W v) (g' : Matrix _ _ (X.G.P.Qq v)) ∧
      X.latAt v (j + 1) L' = colSpan (X.G.P.W v) (h' : Matrix _ _ (X.G.P.Qq v)) ∧
      (h' : Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj (j + 1)).m + 1)) (X.G.P.Qq v)) =
        (g' : Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj (j + 1)).m + 1)) (X.G.P.Qq v)) *
          dgQ (X.G.P.Qq v) p ((X.Pj (j + 1)).m + 1) (i0 v) := by
    intro v
    have hS := X.G.P.setting v
    have := hS.frac_alt
    have hp0 : (p : X.G.P.Qq v) ≠ 0 := pQ_ne hS.p_unif
    rcases h4 v with ⟨h0, hL⟩ | ⟨_, he⟩
    · obtain ⟨g, hg, hgL⟩ := h2 v
      have h0' : i0 v = 0 := h0
      refine ⟨Matrix.nonsingInvUnit g hg, Matrix.nonsingInvUnit g hg, ?_, hgL, ?_⟩
      · show L'' v = _
        rw [hL]; exact hgL
      · have : dgQ (X.G.P.Qq v) p ((X.Pj (j + 1)).m + 1) (i0 v) = 1 := by
          unfold dgQ
          rw [h0']
          simp
        rw [this, mul_one]
    · obtain ⟨g, hg, hsrc, htgt⟩ := Formalism.L2.G.Model.edgeBasis hS _ _ _ he
      have hd : IsUnit (g * dgQ (X.G.P.Qq v) p ((X.Pj (j + 1)).m + 1) (i0 v)).det := by
        rw [Matrix.det_mul]
        exact hg.mul (isUnit_iff_ne_zero.2 (dgQ_det_ne _ _ _ _ hp0))
      exact ⟨Matrix.nonsingInvUnit g hg, Matrix.nonsingInvUnit _ hd, hsrc, htgt, rfl⟩
  choose g' h' h1 h2' h3 using key
  refine ⟨g', h', h1, h2', fun b => ?_⟩
  rw [h3 b.1, ← mF_dgQ X j b i0]
  unfold mF
  rw [Matrix.submatrix_mul_equiv]
  congr 1
  exact Matrix.map_mul (f := (X.G.P.ι b.1).comp (X.G.P.σ b.1 ^ b.2.val : X.G.P.Qq b.1 ≃+* X.G.P.Qq b.1).toRingHom)

end Formalism.L2.PairingIndexBounds.Ent
end
end
end

-- Source module: Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.SubDRenameHvE

section

@[expose] public section

open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.G.Model.TS

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

namespace XAAux

section Rule

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (j : ℕ)

theorem NJ_pos : 0 < NJ X j := by
  unfold NJ NN
  omega

theorem hvE_congr {A : Type*} [CommRing A] {n : ℕ} (x : Fin n → ℕ → A) (y : Matrix (Fin n) (Fin n) A) (c : ℕ) (h h' : Fin c → ℕ)
    (hh : ∀ k, h k ≤ n) (hh' : ∀ k, h' k ≤ n) (e : h = h') : hvE x y c h hh = hvE x y c h' hh' := by
  subst e
  rfl

theorem rename_yV (b : BX X) :
    (yV X.G.Kf (NJ X j)).map ((rename (emX X j b) :
      MvPolynomial (Fin (NJ X j) × Fin (NJ X j)) X.G.Kf →ₐ[X.G.Kf] (X.Pj j).Xsp) :
      MvPolynomial (Fin (NJ X j) × Fin (NJ X j)) X.G.Kf →+* (X.Pj j).Xsp) = yL X j b.1 b.2 := by
  refine Matrix.ext fun a t => ?_
  simp only [Matrix.map_apply, yV, RingHom.coe_coe, rename_X]
  rfl

theorem rename_hvO (b : BX X) (x : Fin (NJ X j) → ℕ → X.G.Kf) (c : ℕ) (h : Fin c → ℕ) :
    rename (emX X j b) (hvO (fun a i => C (x a i)) (yV X.G.Kf (NJ X j)) c h) = hvOdd X j b.1 b.2 x c h := by
  rw [← RingHom.coe_coe (rename (emX X j b)), map_hvO, rename_yV]
  unfold hvO hvOdd
  refine Finset.prod_congr rfl fun k _ => ?_
  congr 2
  funext a i
  rw [RingHom.coe_coe, rename_C]

theorem subD_rename_hvE (b : BX X) (ho : ¬ IsOddPos b.2) (x : Fin (NJ X j) → ℕ → X.G.Kf) (c : ℕ) (h : Fin c → ℕ)
    (hh : ∀ k, h k ≤ NJ X j) :
    subD X Kc j (rename (emX X j b) (hvE (fun a i => C (x a i)) (yV X.G.Kf (NJ X j)) c h hh)) =
      hvE (fun a i => algebraMap X.G.Kf (DA X Kc j) (x a i)) (dyMat X Kc j b.1 b.2) c h hh := by
  rw [← RingHom.coe_coe (rename (emX X j b)), map_hvE, rename_yV, ← RingHom.coe_coe (subD X Kc j), map_hvE]
  congr 1
  · funext a i
    rw [RingHom.coe_coe, RingHom.coe_coe, rename_C]
    exact (subD X Kc j).commutes (x a i)
  · have := subD_yL X Kc j b.1 b.2
    unfold ySub at this
    rw [if_neg ho] at this
    exact this

theorem hvE_dy (b : BX X) (x : Fin (NJ X j) → ℕ → X.G.Kf) (c : ℕ) (h : Fin c → ℕ) (hh : ∀ k, h k ≤ NJ X j)
    (hh' : ∀ k, h k ≤ NJ X (j + 1)) :
    hvE (fun a i => algebraMap X.G.Kf (DA X Kc j) (x a i)) (dyMat X Kc j b.1 b.2) c h hh =
      hvE (xd X Kc j b.1 b.2 x) (yMat X Kc j b.1 b.2) c h hh' := by
  unfold hvE
  refine Finset.prod_congr rfl fun k _ => ?_
  congr 1
  refine Matrix.ext fun i t => ?_
  rw [Matrix.of_apply, Matrix.of_apply]
  exact pair_dy X Kc j b.1 b.2 x i.val (Fin.castLE (hh k) t)

end Rule

end XAAux

theorem xA_of (hS : XShape) : XA := by
  intro p _ X Kc _ _ j x
  have key := polDel_hv X Kc j (fun v s => x ⟨v, s⟩) (fun v s => cX X j ⟨v, s⟩)
    (fun v s k => colH (muX X j (NJ X j) ⟨v, s⟩) k.val)
    (fun v s => rename (emX X j ⟨v, s⟩) (srcN X j ⟨v, s⟩ (x ⟨v, s⟩)))
    (fun v s _ k => colH_le _ _) (fun v s _ => cMu_toNat X v j s)
    (fun v s _ => by
      rw [← sum_colHt X v j s]
      congr 1
      exact Finset.sum_congr rfl fun k _ => (hS p X j ⟨v, s⟩).2.2.2.2.1 k.val)
  rw [Fintype.prod_sigma, Fintype.prod_sigma]
  have h1 : (∏ v, ∏ s, rename (emX X j ⟨v, s⟩) (srcN X j ⟨v, s⟩ (x ⟨v, s⟩))) =
      ∏ v, ∏ s, if IsOddPos s then hvOdd X j v s (x ⟨v, s⟩) (cX X j ⟨v, s⟩) (fun k => colH (muX X j (NJ X j) ⟨v, s⟩) k.val)
        else rename (emX X j ⟨v, s⟩) (srcN X j ⟨v, s⟩ (x ⟨v, s⟩)) := by
    refine Finset.prod_congr rfl fun v _ => Finset.prod_congr rfl fun s _ => ?_
    split_ifs with ho
    · unfold srcN
      rw [if_pos ho]
      exact XAAux.rename_hvO X j ⟨v, s⟩ _ _ _
    · rfl
  rw [h1, key]
  refine Finset.prod_congr rfl fun v _ => Finset.prod_congr rfl fun s _ => ?_
  obtain ⟨-, -, hanti, hle, hc1, hc2, he1, he2, -, -⟩ := hS p X j ⟨v, s⟩
  unfold tgtD
  split_ifs with ho
  · unfold hvOdd' hvO
    refine Finset.prod_congr rfl fun k _ => ?_
    beta_reduce
    rw [hc1, hc2]
  · have hf := highest_vector_full_holds (DA X Kc j) (NJ X j) (muX X j (NJ X j) ⟨v, s⟩) (hanti _) (cX X j ⟨v, s⟩) (eX X j ⟨v, s⟩)
      (hle _) he1 he2 (XAAux.NJ_pos X j) (fun a i => algebraMap X.G.Kf (DA X Kc j) (x ⟨v, s⟩ a i)) (dyMat X Kc j v s)
    have hnu : nuS X j ⟨v, s⟩ = fun t => muX X j (NJ X j) ⟨v, s⟩ t - eX X j ⟨v, s⟩ := if_neg ho
    have hdet : (Matrix.of fun a i : Fin (NJ X j) => algebraMap X.G.Kf (DA X Kc j) (x ⟨v, s⟩ a i.val)).det =
        algebraMap X.G.Kf (DA X Kc j) (Matrix.of fun a i : Fin (NJ X j) => x ⟨v, s⟩ a i.val).det := by
      rw [RingHom.map_det]
      rfl
    have h2 : hvE (xd X Kc j v s (x ⟨v, s⟩)) (yMat X Kc j v s) (cX X j ⟨v, s⟩)
        (fun k => colH (muX X j (NJ X (j + 1)) ⟨v, s⟩) k.val) (fun k => colH_le _ k.val) =
        hvE (fun a i => algebraMap X.G.Kf (DA X Kc j) (x ⟨v, s⟩ a i)) (dyMat X Kc j v s) (cX X j ⟨v, s⟩)
          (fun k => colH (muX X j (NJ X j) ⟨v, s⟩) k.val) (fun k => colH_le _ k.val) := by
      rw [XAAux.hvE_dy X Kc j ⟨v, s⟩ _ _ _ _ (fun k => (colH_le _ k.val).trans (NN_le X j))]
      exact XAAux.hvE_congr _ _ _ _ _ _ _ (funext fun k => by rw [hc1, hc2])
    show _ = hvE (xd X Kc j v s (x ⟨v, s⟩)) (yMat X Kc j v s) (cX X j ⟨v, s⟩)
        (fun k => colH (muX X j (NJ X (j + 1)) ⟨v, s⟩) k.val) (fun k => colH_le _ k.val)
    rw [h2, hf, hdet]
    unfold srcN
    rw [if_neg ho, map_mul, map_mul, rename_C, XAAux.subD_rename_hvE X Kc j ⟨v, s⟩ ho,
      show subD X Kc j (C ((Matrix.of fun a i : Fin (NJ X j) => x ⟨v, s⟩ a i.val).det ^ eX X j ⟨v, s⟩)) =
        algebraMap X.G.Kf (DA X Kc j) ((Matrix.of fun a i : Fin (NJ X j) => x ⟨v, s⟩ a i.val).det ^ eX X j ⟨v, s⟩) from
        (subD X Kc j).commutes _, map_pow, mul_pow,
      XAAux.hvE_congr _ _ _ (fun k => colH (nuS X j ⟨v, s⟩) k.val)
        (fun k => colH (fun t => muX X j (NJ X j) ⟨v, s⟩ t - eX X j ⟨v, s⟩) k.val) _ (fun k => colH_le _ k.val) (by rw [hnu])]
    show _ * _ * (dyMat X Kc j v s).det ^ eX X j ⟨v, s⟩ = _
    ring

namespace XAAux

section Span

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (j : ℕ)

theorem pairD_mem [Infinite Kc] (W : Submodule Kc (XspC (X.Pj (j + 1)) Kc)) (P : DA X Kc j)
    (h : ∀ d0 : X.ZA j → Kc, evD X Kc j d0 P ∈ W) (f : MvPowerSeries (X.ZA j) Kc) : pairD X Kc j P f ∈ W := by
  by_contra hn
  obtain ⟨l, hl, hW⟩ := Submodule.exists_le_ker_of_notMem hn
  refine hl ?_
  rw [pairing_series_linear_form_holds p X Kc j P f l 0 fun d0 => by rw [map_zero, LinearMap.mem_ker.1 (hW (h d0))]]
  simp

theorem map_bidet {K K' : Type} [CommRing K] [CommRing K'] (φ : K →+* K') {r n c : ℕ} (sz : Fin c → ℕ) (hsz : ∀ k, sz k ≤ n)
    (I : ∀ k, Fin (sz k) → Fin r) : map φ (bideterminant K sz hsz I) = bideterminant K' sz hsz I := by
  unfold bideterminant initMinor
  rw [map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [RingHom.map_det]
  congr 1
  ext a b
  simp

theorem tgtN_mem [CharZero Kc] (hS : XShape) (b : BX X) (z : Fin (NJ X (j + 1)) → ℕ → Kc) :
    tgtN X Kc j b z ∈ dualWeyl Kc (NJ X (j + 1)) (NJ X (j + 1)) (nuT X j b) := by
  obtain ⟨-, -, hanti, hle, -⟩ := hS p X j b
  unfold tgtN nuT
  split_ifs with ho
  · exact highest_vector_mem_odd Kc _ _ (hanti _) _ (hle _) z
  · exact highest_vector_mem_even Kc _ _ (hanti _) _ (hle _) z

end Span

end XAAux

theorem xSpanN_of (hS : XShape) : XSpanN := by
  intro p _ X Kc _ _ _ j x f
  classical
  rw [delF_apply, xA_of hS p X Kc j x]
  refine XAAux.pairD_mem X Kc j _ _ (fun d0 => ?_) f
  rw [map_prod]
  simp only [frame_change_compatibility_holds p X Kc j]
  refine prod_span (R := Kc) (fun b : BX X => {y : XspC (X.Pj (j + 1)) Kc |
      ∃ (K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ NJ X (j + 1)) (I : ∀ k, Fin (sz k) → Fin (NJ X (j + 1))),
        shapeDeg sz = nuT X j b ∧ y = rename (emX X (j + 1) b) (bideterminant Kc sz hsz I)}) _ (fun g hg => ?_) _ (fun b => ?_)
  · choose K sz hsz I hsh hgb using hg
    refine Submodule.subset_span ⟨fun b => bideterminant X.G.Kf (sz b) (hsz b) (I b), fun b => ?_, ?_⟩
    · rw [← hsh b]
      exact bidetMem X.G.Kf _ _ _ _ _ _
    · rw [map_prod]
      refine Finset.prod_congr rfl fun b _ => ?_
      rw [hgb b, map_rename, XAAux.map_bidet]
  · have h1 := XAAux.tgtN_mem X Kc j hS b
      (mulC (dM X Kc j b d0).transpose fun a i => algebraMap X.G.Kf Kc (x b a i))
    rw [standardMonomialSpanDomain Kc] at h1
    have h2 := Submodule.mem_map_of_mem (f := (rename (emX X (j + 1) b) :
      MvPolynomial (Fin (NJ X (j + 1)) × Fin (NJ X (j + 1))) Kc →ₐ[Kc] XspC (X.Pj (j + 1)) Kc).toLinearMap) h1
    rw [Submodule.map_span] at h2
    refine Submodule.span_mono ?_ h2
    rintro _ ⟨q, ⟨K, sz, hsz, I, hsh, rfl⟩, rfl⟩
    exact ⟨K, sz, hsz, I, hsh, rfl⟩

end Formalism.L2.PairingIndexBounds.Ent
end
end
end

-- Source module: Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.FinalOf

section

@[expose] public section

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G)
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (hst : FinStab X.Lv)
    {g : Formalism.MainNotions.GL3Theta.G1 p} (hLT : LTIso g) {T : Type} (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T)
    (F : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p])

theorem pending_tuple_admissible_of_shape (hS : XShape) (hBrS : XBrS) (hBrT : XBrT) (hInj : XInj) (hSp : XSpanN) (hMid : XMid) (hU : XUnit)
    (hE : XEdge) (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.FormalGroupSystem.adm7 D X (pendT X E hfin hst hLT pos F) := by
  letI := wittFractionAlgebraCp p
  letI := algKfC E.toCEmb
  intro j _ La c' L' L'' i0 h1 h2 h3 h4
  exact admissible_general_lattice_tuple X ℂ_[p] hS hBrS hBrT hInj hSp hMid hU hE (OcC p) OcC_val
    (fun o => ((pendT X E hfin hst hLT pos F).Oc_K _).2 ⟨o, rfl⟩) j La c' L' L'' i0 h1 h2 h3 h4

end Formalism.L2.PairingIndexBounds.Ent
end
end
end

-- Source module: Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.LatticeShapeMiddleHolds

section

@[expose] public section

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend

theorem lattice_shape_a_holds : XA := xA_of frame_shape_identity_holds
theorem lattice_span_normal_holds : XSpanN := xSpanN_of frame_shape_identity_holds
theorem lattice_shape_middle_holds : XMid := xMid_of frame_shape_identity_holds lattice_shape_a_holds frame_change_pairing_holds transposed_frame_image_blockwise_holds frame_change_compatibility_holds frame_change_group_action_holds
theorem lattice_shape_unit_holds : XUnit := xUnit_of frame_shape_identity_holds

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G)
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (hst : FinStab X.Lv)
    {g : Formalism.MainNotions.GL3Theta.G1 p} (hLT : LTIso g) {T : Type} (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T)
    (F : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p])

theorem pending_tuple_admissible (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.FormalGroupSystem.adm7 D X (pendT X E hfin hst hLT pos F) :=
  pending_tuple_admissible_of_shape X E hfin hst hLT pos F frame_shape_identity_holds branching_source_identity branching_target_identity frame_change_injective_holds lattice_span_normal_holds lattice_shape_middle_holds lattice_shape_unit_holds
    frame_edge_identity_holds D

end Formalism.L2.PairingIndexBounds.Ent
end
end
end
