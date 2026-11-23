module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.RowParseval
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.RealCovolume
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.CovolBR
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ProductExactness
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FrameZZEqNegT
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXPS
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.PjFrameRow
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SCompact
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
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ReImESymmAdd
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.BaseLatticeLe
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FinrankSpanLb
public import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeGluingRadicals
import Mathlib.Tactic.Linter.HaveILetI
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.RowVZero
public import Formalism.SharpRestriction.CuspSpanNormBounds.BlockEstimateWords
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.RingTheory.PicardGroup
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.EmbVHomInjective

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.PjRowPars

section

@[expose] public section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX.CovB

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.WFL Formalism.L2.SG.Pf Formalism.L2.SG.Pf.NcReal.JX
  Formalism.L2.SG.RealObj.InfCut Formalism.L2.SG.Pf.NcReal.JX.FR

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem rowParseval_holds : RowParseval := by
  intro D X u x y hx hy v
  set a := rv X.B.I v (X.crd x) with ha
  set b := rv X.B.I v (X.crd y) with hb
  have hbe : ∀ c, hJ (X.B.I.ε v) (eV X v c) b = 0 := by
    intro c
    show hJ (X.B.I.ε v) (rv X.B.I v (X.crd (X.eX c))) (rv X.B.I v (X.crd y)) = 0
    rw [Formalism.L2.SG.Pf.hJ_crd, (hy c).1]; simp
  have hbf : ∀ c, hJ (X.B.I.ε v) (rv X.B.I v (X.crd (X.fY c))) b = 0 := by
    intro c
    show hJ (X.B.I.ε v) (rv X.B.I v (X.crd (X.fY c))) (rv X.B.I v (X.crd y)) = 0
    rw [Formalism.L2.SG.Pf.hJ_crd, (hy c).2]; simp
  have hdec := decomp (nX X) (ProductExactness.Tw_pos u) (fX_ee X v) (LsNc5.fr_ff X v) (LsNc5.fr_ef X v) (fX_ww X u v) (fX_ew X u v)
    (LsNc5.fr_fw X u v) (LsNc5.fr_ez X u v) (LsNc5.fr_fz X u v) (LsNc5.frame_z_z_eq_neg_t X u v) (LsNc5.fr_zw X u v) b hbe hbf
  have hab : hJ (X.B.I.ε v) a b = ∑ c, hJ (X.B.I.ε v) a (X.wfr u v c) * star (hJ (X.B.I.ε v) b (X.wfr u v c)) +
      hJ (X.B.I.ε v) a (LsNc5.zV X u v) * star (hJ (X.B.I.ε v) b (LsNc5.zV X u v)) * (-(1 / ((Tw u : ℝ) : ℂ))) := by
    conv_lhs => rw [hdec]
    rw [fr_add_r, fr_sum_r, fr_smul_r]
    congr 1
    · refine Finset.sum_congr rfl fun c _ => ?_
      rw [fr_smul_r, hJ_swap (X.B.I.ε v) (X.wfr u v c) b, star_star]
      ring
    · rw [hJ_swap (X.B.I.ε v) (LsNc5.zV X u v) b, star_star]
      ring
  rw [← Formalism.L2.SG.Pf.hJ_crd, ← ha, ← hb, hab, Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    have hj : (Fin.castSucc j).val < D.R.k := j.isLt
    simp only [rowV, gC, dif_pos hj, if_pos hj, mul_one]
    rfl
  · have hl : ¬ (Fin.last D.R.k).val < D.R.k := by simp
    simp only [rowV, gC, dif_neg hl, if_neg hl]
    rfl

end Formalism.L2.SG.Pf.NcReal.JX.CovB
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.RowRankHolds

section

@[expose] public section

noncomputable section

open NumberField Formalism.BasicNotions Module
open scoped BigOperators

namespace Formalism.L2.SG.Pf.NcReal.JX.CovB.CovolumeSpans

open Formalism.L2.SG.HidaSetting Formalism.MainNotions.S

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D)

theorem rowRank_holds : RowRank := by
  intro D X b
  set S := Submodule.span D.host.E (aaLbS X b : Set (VS D).V) with hSdef
  have hSfin : finrank D.host.E S = D.R.k + 1 := by
    rw [hSdef, span_aaLbS, finrank_span_Lb]
  have hSle : ∀ x ∈ aaLbS X b, x ∈ S := fun x hx => Submodule.subset_span hx
  let B : Basis (Fin (D.R.k + 1)) D.host.E S := Module.finBasisOfFinrankEq D.host.E S hSfin
  let eS : S ≃ₗ[D.host.E] (Fin (D.R.k + 1) → D.host.E) := B.equivFun
  let Φ : (Fin (D.R.k + 1) → D.host.E) →ₗ[𝓞 D.host.E] (VS D).V :=
    (S.subtype.comp eS.symm.toLinearMap).restrictScalars (𝓞 D.host.E)
  have hΦ : ∀ y, Φ y = ((eS.symm y : S) : (VS D).V) := fun y => rfl
  have hΦinj : Function.Injective Φ := by
    intro y y' h
    rw [hΦ, hΦ] at h
    exact eS.symm.injective (Subtype.ext h)
  let A : Submodule (𝓞 D.host.E) (Fin (D.R.k + 1) → D.host.E) := (aaLbS X b).comap Φ
  have hmemA : ∀ y, y ∈ A ↔ Φ y ∈ aaLbS X b := fun y => Iff.rfl

  have hmap : A.map Φ = aaLbS X b := by
    refine le_antisymm (Submodule.map_comap_le _ _) fun x hx => ?_
    refine ⟨eS ⟨x, hSle x hx⟩, ?_, ?_⟩
    · show Φ (eS ⟨x, hSle x hx⟩) ∈ aaLbS X b
      rw [hΦ, LinearEquiv.symm_apply_apply]
      exact hx
    · show Φ (eS ⟨x, hSle x hx⟩) = x
      rw [hΦ, LinearEquiv.symm_apply_apply]
  have hAfg : A.FG := Submodule.fg_of_fg_map_injective Φ hΦinj (by rw [hmap]; exact fg_aaLbS X b)

  have hAspan : Submodule.span D.host.E (A : Set (Fin (D.R.k + 1) → D.host.E)) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have key : ∀ (v : (VS D).V) (hv : v ∈ S), eS ⟨v, hv⟩ ∈ Submodule.span D.host.E (A : Set _) := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem x hx =>
        refine Submodule.subset_span ?_
        show Φ (eS ⟨x, _⟩) ∈ aaLbS X b
        rw [hΦ, LinearEquiv.symm_apply_apply]
        exact hx
      | zero =>
        have : eS ⟨0, S.zero_mem⟩ = 0 := by
          rw [show (⟨0, S.zero_mem⟩ : S) = 0 from rfl, map_zero]
        rw [this]
        exact Submodule.zero_mem _
      | add x y hx hy ihx ihy =>
        have : eS ⟨x + y, S.add_mem hx hy⟩ = eS ⟨x, hx⟩ + eS ⟨y, hy⟩ := by
          rw [← map_add (f := _)]; rfl
        rw [this]
        exact Submodule.add_mem _ ihx ihy
      | smul c x hx ihx =>
        have : eS ⟨c • x, S.smul_mem c hx⟩ = c • eS ⟨x, hx⟩ := by
          rw [← map_smul]; rfl
        rw [this]
        exact Submodule.smul_mem _ c ihx
    have := key _ (eS.symm y).2
    rwa [Subtype.coe_eta, LinearEquiv.apply_symm_apply] at this

  let Az : Submodule ℤ (Fin (D.R.k + 1) → D.host.E) := A.restrictScalars ℤ
  have h1 : Module.Finite (𝓞 D.host.E) A := Module.Finite.iff_fg.2 hAfg
  have h2 : Module.Finite ℤ A := Module.Finite.trans (𝓞 D.host.E) _
  have h3 : Module.Finite ℤ Az :=
    Module.Finite.equiv ((Submodule.restrictScalarsEquiv ℤ (𝓞 D.host.E) _ A).restrictScalars ℤ).symm
  have hlat : Submodule.IsFullLattice ℚ Az := by
    letI : Submodule.IsLattice ℚ Az := Submodule.IsLattice.of_fg ℚ (Module.Finite.iff_fg.1 h3)
    refine ⟨?_⟩
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ Submodule.span D.host.E (A : Set (Fin (D.R.k + 1) → D.host.E)) := by rw [hAspan]; trivial
    obtain ⟨n, hn, hnx⟩ := Formalism.MainNotions.LatticeGluingRadicals.j_exists_nat_smul_mem A hx
    have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
    have : x = (n : ℚ)⁻¹ • (n • x) := by
      rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ hn', one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hnx)
  have hr : finrank ℤ Az = finrank ℚ (Fin (D.R.k + 1) → D.host.E) :=
    Module.finrank_eq_of_rank_eq
      ((Submodule.IsFullLattice.rank_eq ℚ Az).trans (Module.finrank_eq_rank ℚ (Fin (D.R.k + 1) → D.host.E)).symm)
  let bZ : Basis (Fin (finrank ℚ (Fin (D.R.k + 1) → D.host.E))) ℤ Az := Module.finBasisOfFinrankEq ℤ Az hr
  have hdim : finrank ℚ (Fin (D.R.k + 1) → D.host.E) = finrank ℚ D.host.E * (D.R.k + 1) := by
    rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_comm]

  let eqv : Az ≃ₗ[ℤ] ((aaLbS X b).restrictScalars ℤ) :=
    { toFun := fun y => ⟨Φ (y : Fin (D.R.k + 1) → D.host.E), (hmemA _).1 y.2⟩
      invFun := fun x => ⟨eS ⟨x, hSle x x.2⟩, by
        show Φ (eS ⟨x, hSle x x.2⟩) ∈ aaLbS X b
        rw [hΦ, LinearEquiv.symm_apply_apply]
        exact x.2⟩
      map_add' := fun y y' => Subtype.ext (map_add Φ (y : Fin (D.R.k + 1) → D.host.E) y')
      map_smul' := fun c y => Subtype.ext (by
        show Φ (c • (y : Fin (D.R.k + 1) → D.host.E)) = c • Φ (y : Fin (D.R.k + 1) → D.host.E)
        exact map_zsmul Φ c _)
      left_inv := fun y => Subtype.ext (by
        show eS ⟨Φ (y : Fin (D.R.k + 1) → D.host.E), _⟩ = (y : Fin (D.R.k + 1) → D.host.E)
        have : (⟨Φ (y : Fin (D.R.k + 1) → D.host.E), hSle _ ((hmemA _).1 y.2)⟩ : S) = eS.symm y := Subtype.ext (hΦ _)
        rw [this, LinearEquiv.apply_symm_apply])
      right_inv := fun x => Subtype.ext (by
        show Φ (eS ⟨x, _⟩) = (x : (VS D).V)
        rw [hΦ, LinearEquiv.symm_apply_apply]) }
  exact ⟨(bZ.map eqv).reindex (finCongr hdim)⟩

end Formalism.L2.SG.Pf.NcReal.JX.CovB.CovolumeSpans
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.TraceReHolds

section

@[expose] public section

noncomputable section

open NumberField Formalism.BasicNotions

namespace Formalism.L2.SG.Pf.NcReal.JX.CovB

open Formalism.L2.SG.HidaSetting Formalism.MainNotions.S

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem traceRe_holds : TraceRe := by
  intro D X t
  have h1 : ∀ v, X.B.I.φ v (X.ιE.symm t) = embS D (X.pl v) t := fun v => by
    rw [X.φ_eq, RingEquiv.apply_symm_apply]
  simp only [h1]
  rw [Formalism.MainNotions.BlockEstimateWords.trace_tau D t, Finset.sum_div,
    Equiv.sum_comp X.pl (fun τ => ((embS D τ) t).re)]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [mul_div_cancel_left₀ _ two_ne_zero]
  rfl

end Formalism.L2.SG.Pf.NcReal.JX.CovB
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.RowBlockCovolOf

section

@[expose] public section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX.CovB

open Formalism.L2.SG.HidaSetting Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX Formalism.L2.SG.Pf.RealCovolume

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def gR {D : D7} (u : D.what₂.Word) (c : Fin (D.R.k + 1)) : ℝ :=
  if c.val < D.R.k then 1 else -(1 / Formalism.L2.SG.RealObj.Tw u)

theorem gC_eq {D : D7} (u : D.what₂.Word) (c : Fin (D.R.k + 1)) : gC u c = ((gR u c : ℝ) : ℂ) := by
  unfold gC gR; split_ifs <;> push_cast <;> rfl

theorem perp_aaLbS {D : D7} (X : HidaSetting D) (b : Fin D.R.rS) {x : (VS D).V} (hx : x ∈ aaLbS X b) (a : Fin D.R.rS) :
    (VS D).hT (X.eX a) x = 0 ∧ (VS D).hT (X.fY a) x = 0 := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨c, -, l, hl, rfl⟩ := hy
    obtain ⟨h1, h2⟩ := X.Lb_perp l hl a
    exact ⟨by rw [map_smul, h1, smul_zero], by rw [map_smul, h2, smul_zero]⟩
  | zero => exact ⟨map_zero _, map_zero _⟩
  | add y z _ _ hy hz => exact ⟨by rw [map_add (f := _), hy.1, hz.1, add_zero], by rw [map_add (f := _), hy.2, hz.2, add_zero]⟩
  | smul c y _ hy =>
    refine ⟨?_, ?_⟩
    · rw [← algebraMap_smul D.host.E c y, map_smul, hy.1, smul_zero]
    · rw [← algebraMap_smul D.host.E c y, map_smul, hy.2, smul_zero]

theorem gR_ne {D : D7} (u : D.what₂.Word) (c : Fin (D.R.k + 1)) : gR u c ≠ 0 := by
  have hT := Formalism.L2.SG.RealObj.InfCut.ProductExactness.Tw_pos (D := D) u
  unfold gR; split_ifs
  · exact one_ne_zero
  · simp only [ne_eq, neg_eq_zero, one_div, inv_eq_zero]; exact hT.ne'

theorem prod_gR {D : D7} (u : D.what₂.Word) : ∏ c : Fin (D.R.k + 1), |gR u c| = 1 / Formalism.L2.SG.RealObj.Tw u := by
  have hT := Formalism.L2.SG.RealObj.InfCut.ProductExactness.Tw_pos (D := D) u
  rw [Fin.prod_univ_castSucc]
  have h1 : ∀ i : Fin D.R.k, |gR u (Fin.castSucc i)| = 1 := fun i => by
    unfold gR; rw [if_pos (by simp)]; simp
  have h2 : |gR u (Fin.last D.R.k)| = 1 / Formalism.L2.SG.RealObj.Tw u := by
    unfold gR; rw [if_neg (by simp)]; rw [abs_neg, abs_of_pos (by positivity)]
  rw [Finset.prod_congr rfl fun i _ => h1 i, Finset.prod_const_one, one_mul, h2]

theorem Qf_rowV {D : D7} (X : HidaSetting D) (u : D.what₂.Word) {x y : (VS D).V}
    (hx : ∀ a, (VS D).hT (X.eX a) x = 0 ∧ (VS D).hT (X.fY a) x = 0)
    (hy : ∀ a, (VS D).hT (X.eX a) y = 0 ∧ (VS D).hT (X.fY a) y = 0) :
    Qf (gR u) (rowV X u x) (rowV X u y) = ((Algebra.trace ℚ D.host.E ((VS D).hT x y) : ℚ) : ℝ) / 2 := by
  rw [← traceRe_holds X]
  unfold Qf
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [← rowParseval_holds X u x y hx hy v, Complex.re_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [gC_eq, Complex.re_mul_ofReal]

theorem rowBlockCovol_of (hT : TrDetUnimod) : RowBlockCovol := by
  intro D X u b
  classical
  obtain ⟨m⟩ := CovolumeSpans.rowRank_holds X b
  set N := Module.finrank ℚ D.host.E * (D.R.k + 1) with hNdef
  set w : Fin N → (InfinitePlace X.B.I.F → Fin (D.R.k + 1) → ℂ) := fun i => rowV X u (m i : (VS D).V) with hw
  have hmem : ∀ i, ((m i : (VS D).V)) ∈ aaLbS X b := fun i => (m i).2

  have hcl : cLat X u (Sum.inl (Sum.inr b)) = AddSubgroup.closure (Set.range w) := by
    show AddSubgroup.closure (rowV X u '' aaLb X b) = _
    apply le_antisymm
    · rw [AddSubgroup.closure_le]
      rintro _ ⟨x, hx, rfl⟩
      have hx' : x ∈ (aaLbS X b).restrictScalars ℤ := hx
      have hsum := m.sum_repr ⟨x, hx'⟩
      have e : x = ∑ i, (m.repr ⟨x, hx'⟩ i) • (m i : (VS D).V) := by
        have := congrArg Subtype.val hsum
        simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower] at this
        exact this.symm
      rw [e]
      have : rowV X u (∑ i, (m.repr ⟨x, hx'⟩ i) • (m i : (VS D).V)) =
          ∑ i, (m.repr ⟨x, hx'⟩ i) • w i := by
        have h := map_sum (Formalism.L2.SG.Pf.NcReal.JX.NOf.rowHom X u)
          (fun i => (m.repr ⟨x, hx'⟩ i) • (m i : (VS D).V)) Finset.univ
        simp only [map_zsmul] at h
        exact h
      rw [SetLike.mem_coe, this]
      exact AddSubgroup.sum_mem _ fun i _ =>
        AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self i)) _
    · rw [AddSubgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact AddSubgroup.subset_closure ⟨(m i : (VS D).V), hmem i, rfl⟩

  have hQ : (Matrix.of fun i j => Qf (gR u) (w i) (w j)) =
      (1 / 2 : ℝ) • (Matrix.of fun i j =>
        (Algebra.trace ℚ D.host.E ((VS D).hT (m i : (VS D).V) (m j : (VS D).V)))).map (Rat.castHom ℝ) := by
    ext i j
    simp only [Matrix.of_apply, Matrix.smul_apply, Matrix.map_apply, hw, smul_eq_mul]
    change _ = 1 / 2 * (((Algebra.trace ℚ D.host.E ((VS D).hT (m i : (VS D).V) (m j : (VS D).V))) : ℚ) : ℝ)
    rw [Qf_rowV X u (perp_aaLbS X b (hmem i)) (perp_aaLbS X b (hmem j))]
    ring
  have hTr := hT X b m rfl
  have hdE : (discr D.host.E : ℚ) ≠ 0 := by exact_mod_cast discr_ne_zero D.host.E
  have hNa : (FractionalIdeal.absNorm (aaD D b) : ℚ) ≠ 0 := by
    rw [Ne, FractionalIdeal.absNorm_eq_zero_iff]; exact aaD_ne_zero X b
  have hdetQ : (Matrix.of fun i j =>
      (Algebra.trace ℚ D.host.E ((VS D).hT (m i : (VS D).V) (m j : (VS D).V)))).det ≠ 0 := by
    intro h0; rw [h0, abs_zero] at hTr
    exact (mul_ne_zero (pow_ne_zero _ (abs_ne_zero.2 hdE)) (pow_ne_zero _ hNa)) hTr.symm
  have hdetG : (Matrix.of fun i j => Qf (gR u) (w i) (w j)).det =
      (1 / 2 : ℝ) ^ N * (((Matrix.of fun i j =>
        (Algebra.trace ℚ D.host.E ((VS D).hT (m i : (VS D).V) (m j : (VS D).V)))).det : ℚ) : ℝ) := by
    rw [hQ, Matrix.det_smul, Fintype.card_fin]
    congr 1
    exact (RingHom.map_det (Rat.castHom ℝ) _).symm
  have hdet : (Matrix.of fun i j => Qf (gR u) (w i) (w j)).det ≠ 0 := by
    rw [hdetG]; exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast hdetQ)
  have hcard : Fintype.card (InfinitePlace X.B.I.F × Fin (D.R.k + 1) × Fin 2) = N := by
    rw [Fintype.card_prod, Fintype.card_prod, card_ι X, Fintype.card_fin, Fintype.card_fin, hNdef,
      ← Module.finrank_mul_finrank ℚ D.host.F D.host.E, D.sp.cm.deg2]
    ring
  obtain ⟨h1, h2, h3⟩ := covol_of_gram w (gR u) (gR_ne u) hcard hdet
  rw [hcl]
  refine ⟨h1, h2, fun F hF hFd => ?_⟩
  change (volume : Measure (InfinitePlace X.B.I.F → Fin (D.R.k + 1) → ℂ)) F = _
  rw [h3 F hF hFd]
  congr 1

  set dF : ℝ := |(discr X.B.I.F : ℝ)| with hdF
  have hdF0 : 0 < dF := dF_pos X
  set fC : ℕ := Fintype.card (InfinitePlace X.B.I.F) with hfC
  set T : ℝ := Formalism.L2.SG.RealObj.Tw u with hTdef
  have hT0 : 0 < T := Formalism.L2.SG.RealObj.InfCut.ProductExactness.Tw_pos (D := D) u
  have hNf : N = 2 * (fC * (D.R.k + 1)) := by
    rw [← hcard, Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]; ring
  set x : ℝ := -(2 * ((D.R.rS : ℝ) - (b : ℕ))) with hx
  have hTrR : |(((Matrix.of fun i j =>
      (Algebra.trace ℚ D.host.E ((VS D).hT (m i : (VS D).V) (m j : (VS D).V)))).det : ℚ) : ℝ)| =
      (dF ^ 2) ^ (D.R.k + 1) * (dF ^ x) ^ (2 * (D.R.k + 1)) := by
    have h := congrArg (fun q : ℚ => (q : ℝ)) hTr
    simp only [Rat.cast_abs, Rat.cast_mul, Rat.cast_pow] at h
    rw [h, ← absDiscrE X, absNorm_aaD X b]
    push_cast; rfl
  have hsq : |(Matrix.of fun i j => Qf (gR u) (w i) (w j)).det| =
      ((1 / 2 : ℝ) ^ (fC * (D.R.k + 1)) * dF ^ (D.R.k + 1) * (dF ^ x) ^ (D.R.k + 1)) ^ 2 := by
    rw [hdetG, abs_mul, hTrR, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), hNf]
    ring
  have hnn : 0 ≤ (1 / 2 : ℝ) ^ (fC * (D.R.k + 1)) * dF ^ (D.R.k + 1) * (dF ^ x) ^ (D.R.k + 1) := by positivity
  rw [hsq, Real.sqrt_sq hnn]
  have hprod : ∏ v : InfinitePlace X.B.I.F, ∏ c : Fin (D.R.k + 1), |gR u c| = (1 / T) ^ fC := by
    simp only [prod_gR, Finset.prod_const, Finset.card_univ]; rfl
  rw [hprod]
  show _ = T ^ fC * (2 : ℝ)⁻¹ ^ (fC * (D.R.k + 1)) *
    dF ^ (((D.R.k : ℝ) + 1) * (1 - 2 * ((D.R.rS : ℝ) - (b : ℕ))))
  have hexp : dF ^ (D.R.k + 1) * (dF ^ x) ^ (D.R.k + 1) =
      dF ^ (((D.R.k : ℝ) + 1) * (1 - 2 * ((D.R.rS : ℝ) - (b : ℕ)))) := by
    rw [← Real.rpow_natCast dF, ← Real.rpow_natCast (dF ^ x), ← Real.rpow_mul hdF0.le, ← Real.rpow_add hdF0]
    congr 1; rw [hx]; push_cast; ring
  have hTinv : ((1 / T) ^ fC)⁻¹ = T ^ fC := by rw [one_div, inv_pow, inv_inv]
  rw [mul_assoc, hexp, div_eq_mul_inv, hTinv]
  ring

end Formalism.L2.SG.Pf.NcReal.JX.CovB
end
end
end
