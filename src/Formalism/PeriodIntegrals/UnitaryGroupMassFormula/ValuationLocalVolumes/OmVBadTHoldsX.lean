module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DiffProd
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcXOmVSt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.LocalGramMatrixFrame
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
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
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.OmegaUnramifiedHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.LocalOmegaVolumeUnique
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.FFInertBHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVBadTOfFfX
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.BaseLatticeLeSecondIsotropic
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.IotaAlgInj
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVPrimOfDdX
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.DVIsDiffVal
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OneMemOev
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVPrimOfDdX
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVScaleHoldsX
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.HostStarConj
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.InclRMemOEv

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcXOmVTop

section

@[expose] public section

noncomputable section

namespace Formalism.L2.SG.Pf.NcX.OmVSt

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  MeasureTheory NumberField IsDedekindDomain

variable {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem n_sub_a : X.B.I.n - (D.R.rS + 1 + D.R.rS) = D.R.k := by
  have h1 := X.n_eq
  have h2 := D.R.rS_two
  unfold Ranks.r at h1
  omega

theorem a_le_n : D.R.rS + 1 + D.R.rS ≤ X.B.I.n := by
  have h1 := X.n_eq
  have h2 := D.R.rS_two
  unfold Ranks.r at h1
  omega

theorem fac_nonneg (v : PlX X) (j : ℕ) :
    0 ≤ 1 - (etaV (E := X.B.I.E) v : ℝ) ^ j * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(j : ℤ)) := by
  have hq : (1 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
    have : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  have h1 : ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(j : ℤ)) ≤ 1 := zpow_le_one_of_nonpos₀ hq (by omega)
  have h0 : 0 ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(j : ℤ)) := by positivity
  have he : (etaV (E := X.B.I.E) v : ℝ) ^ j = 1 ∨ (etaV (E := X.B.I.E) v : ℝ) ^ j = -1 := by
    unfold etaV
    split_ifs
    · left; simp
    · push_cast; exact neg_one_pow_eq_or ℝ j
  rcases he with h | h <;> rw [h] <;> linarith

theorem val_nonneg (v : PlX X) (x : ℝ) (s : Finset ℕ) :
    0 ≤ absV v (dV v) ^ x * ∏ j ∈ s,
      (1 - (etaV (E := X.B.I.E) v : ℝ) ^ j * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(j : ℤ))) := by
  refine mul_nonneg (Real.rpow_nonneg ?_ _) (Finset.prod_nonneg fun j _ => fac_nonneg X v j)
  unfold absV
  split_ifs <;> positivity

theorem prod_eq (v : PlX X) (s : Finset ℕ) :
    ∏ j ∈ s, (1 - (etaV (E := X.B.I.E) v : ℝ) ^ j * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(j : ℤ))) =
      ∏ i ∈ s, (1 - ((etaV (E := X.B.I.E) v : ℤ) : ℝ) ^ i / ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ i) := by
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [zpow_neg, zpow_natCast, div_eq_mul_inv]

theorem exp_eq :
    (X.B.I.n : ℝ) * ((D.R.rS + 1 + D.R.rS : ℕ) : ℝ) - ((D.R.rS + 1 + D.R.rS : ℕ) : ℝ) ^ 2 / 2 =
      (X.B.I.n : ℝ) * (2 * D.R.rS + 1) - ((2 * (D.R.rS : ℝ) + 1) ^ 2) / 2 := by
  push_cast; ring

theorem omV_of (hStd : OmVStd X ψ) (hLat : OmVLat X) (hSD : OmVSD X) (hUn : OmVUnram X) (hPrim : OmVPrim X u')
    (hGram : OmVGram X u') (hDet : OmVDet X u') (hScale : OmVScale X u' ψ) (hBad : OmVBadT X u' ψ)
    (hLocU : OmVLocU X ψ) : Formalism.L2.SG.Pf.NcVal.OmV X u' ψ := by
  intro hψ hψ' v
  show (omAt X.B.I.cm.sig X.B.I.J ψ v (localGramMatrixFrame X u' v)
      {Y | ∃ k ∈ Kv X.B.I.cm.sig X.B.I.J (abelian₂ X) v, Y = k • ratTup (Fv X.B.I.F v) (tupH (frameOf X u'))}).toReal = _
  rw [hScale hψ hψ' v]
  by_cases hT : ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal
  · rw [hBad hψ hψ' v hT (hSD v) (hUn v) (hPrim v), ENNReal.toReal_ofReal (val_nonneg X v _ _), exp_eq X, prod_eq X v]
    unfold aP
    rw [if_pos hT, n_sub_a X]
  · have h := hLocU v _ (yTup X u' v) (hStd hψ hψ') hLat (hSD v) (hUn v) (a_le_n X) (hPrim v)
      (by rw [hGram v]; exact hDet v hT)
    rw [hGram v] at h
    rw [h, ENNReal.toReal_ofReal (val_nonneg X v _ _), exp_eq X, prod_eq X v]
    unfold aP
    rw [if_neg hT, n_sub_a X]

end Formalism.L2.SG.Pf.NcX.OmVSt
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVPrimOfTrX

section

@[expose] public section

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmX

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  NumberField IsDedekindDomain Formalism.L2.SG.Pf.NcVal.OmVSt.OmW
open scoped TensorProduct

variable {D : D7} (X : HidaSetting D)

theorem host_el (x0 : 𝓞 X.B.I.F) : ∃ d0 : 𝓞 D.host.F, ((d0 : D.host.F) : D.host.E) = X.ιE (algebraMap X.B.I.F X.B.I.E (x0 : X.B.I.F)) := by
  have hmem : X.ιE (algebraMap X.B.I.F X.B.I.E (x0 : X.B.I.F)) ∈ D.host.F := (X.ιE_F _).2 ⟨x0, rfl⟩
  set y : D.host.F := ⟨_, hmem⟩
  have hi : IsIntegral ℤ (X.ιE (algebraMap X.B.I.F X.B.I.E (x0 : X.B.I.F))) :=
    ((RingOfIntegers.isIntegral_coe x0).map (algebraMap X.B.I.F X.B.I.E).toIntAlgHom).map (X.ιE : X.B.I.E →+* D.host.E).toIntAlgHom
  have hy : IsIntegral ℤ y :=
    (isIntegral_algHom_iff ((D.host.F).subtype : D.host.F →+* D.host.E).toIntAlgHom Subtype.val_injective).1 hi
  exact ⟨⟨y, (mem_integralClosure_iff ℤ _).2 hy⟩, rfl⟩

theorem dd2 (hT : OmVDdTr X) (v : PlX X) (k : ℕ) (x : D.host.E) (hx : x ∈ (ddS D ^ k)⁻¹) :
    sc (E := X.B.I.E) v ((dV v) ^ k) * inclR (F := X.B.I.F) (Fv X.B.I.F v) (X.ιE.symm x) ∈ OEv (E := X.B.I.E) v := by
  obtain ⟨x0, hx0, hv0⟩ := (dV_isDiffVal v).2.2
  obtain ⟨d0, hd0e⟩ := host_el X x0
  have hd0 : d0 ∈ differentIdeal ℤ (𝓞 D.host.F) := (hT d0).2 ⟨x0, hx0, hd0e.symm⟩
  set g : 𝓞 D.host.E := algebraMap (𝓞 D.host.F) (𝓞 D.host.E) d0 with hg_def
  have hgE : (g : D.host.E) = X.ιE (algebraMap X.B.I.F X.B.I.E (x0 : X.B.I.F)) := hd0e
  set c : Fv X.B.I.F v := algebraMap X.B.I.F (Fv X.B.I.F v) (x0 : X.B.I.F) with hc_def
  have hvd0 : Valued.v (dV v) ≠ 0 := (Valuation.ne_zero_iff _).2 (dV_ne_zero v)
  have hc0 : c ≠ 0 := by
    intro h; rw [h, map_zero] at hv0; exact hvd0 hv0.symm
  have hg0 : (g : D.host.E) ≠ 0 := by
    rw [hgE]; intro h
    apply hc0
    have : algebraMap X.B.I.F X.B.I.E (x0 : X.B.I.F) = 0 := by
      rw [← map_zero X.ιE] at h; exact X.ιE.injective h
    rw [hc_def, (algebraMap X.B.I.F X.B.I.E).injective (this.trans (map_zero _).symm), map_zero]
  have hgk : (g : D.host.E) ^ k ∈ ddS D ^ k := by
    rw [ddS_pow, FractionalIdeal.mem_coeIdeal]
    exact ⟨algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (d0 ^ k),
      Ideal.mem_map_of_mem _ (Ideal.pow_mem_pow hd0 k), by rw [map_pow, map_pow]⟩
  have hne : ddS D ^ k ≠ 0 := by
    intro h
    rw [h, FractionalIdeal.mem_zero_iff] at hgk
    exact hg0 (by by_contra hne0; exact (pow_ne_zero k hne0) hgk)
  have hprod : x * (g : D.host.E) ^ k ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
    have := FractionalIdeal.mul_mem_mul hx hgk
    rwa [inv_mul_cancel₀ hne] at this
  obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 hprod
  have key : X.ιE.symm x * (algebraMap X.B.I.F X.B.I.E (x0 : X.B.I.F)) ^ k = X.ιE.symm (o : D.host.E) := by
    have h1 : ((o : D.host.E)) = x * (g : D.host.E) ^ k := ho
    rw [h1, map_mul, map_pow, hgE, RingEquiv.symm_apply_apply]
  have key2 : inclR (F := X.B.I.F) (Fv X.B.I.F v) (X.ιE.symm x) *
      algebraMap (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) (c ^ k) =
      inclR (F := X.B.I.F) (Fv X.B.I.F v) (X.ιE.symm (o : D.host.E)) := by
    rw [← key, map_mul, map_pow, map_pow, hc_def, alg_alg]
  have hu : Valued.v (dV v * c⁻¹) = 1 := by rw [map_mul, map_inv₀, ← hv0, mul_inv_cancel₀ (hv0 ▸ hvd0)]
  have hid : (dV v * c⁻¹) ^ k * c ^ k = dV v ^ k := by
    rw [mul_pow, inv_pow, mul_assoc, inv_mul_cancel₀ (pow_ne_zero k hc0), mul_one]
  have e : sc (E := X.B.I.E) v (dV v ^ k) * inclR (F := X.B.I.F) (Fv X.B.I.F v) (X.ιE.symm x) =
      algebraMap (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) ((dV v * c⁻¹) ^ k) *
        inclR (F := X.B.I.F) (Fv X.B.I.F v) (X.ιE.symm (o : D.host.E)) := by
    rw [← key2]
    change algebraMap (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) (dV v ^ k) * _ = _
    rw [← hid, map_mul]; ring
  rw [e]
  refine oev_mul v (alg_int_mem X v _ ?_) (incl_mem v (⟨X.ιE.symm (o : D.host.E),
    (RingOfIntegers.isIntegral_coe o).map (X.ιE.symm : D.host.E →+* X.B.I.E).toIntAlgHom⟩ : 𝓞 X.B.I.E))
  rw [map_pow, hu, one_pow]

theorem omVDdLoc_of (hT : OmVDdTr X) : OmVDdLoc X := by
  intro v a
  have hlt : ((a.castSucc : Fin (D.R.rS + 1)) : ℕ) < D.R.rS := by simp
  have halp : alp v D.R.rS a.castSucc = (dV v)⁻¹ ^ (D.R.rS - (a : ℕ)) := by
    unfold alp; rw [if_pos hlt]; simp
  have hk : ((D.R.rS : ℤ) - ((a : ℕ) : ℤ)) = ((D.R.rS - (a : ℕ) : ℕ) : ℤ) := by
    rw [Nat.cast_sub a.isLt.le]
  have haa : aaD D a = (ddS D ^ (D.R.rS - (a : ℕ)))⁻¹ := by
    unfold aaD; rw [hk, zpow_neg, zpow_natCast]
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · rw [haa, inv_inv] at hx; rw [halp]; exact dd1 X hT v _ x hx
  · rw [haa] at hx; rw [halp, inv_pow, inv_inv]; exact dd2 X hT v _ x hx

variable (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmX
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVMemEFHolds

section

@[expose] public section

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmX

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  NumberField IsDedekindDomain Formalism.L2.SG.Pf.NcVal.OmVSt.OmW

theorem mem_diff_iff {K : Type} [Field K] [NumberField K] (x : 𝓞 K) :
    x ∈ differentIdeal ℤ (𝓞 K) ↔ ∀ y : K, (∀ a : 𝓞 K, Algebra.trace ℚ K (y * a) ∈ (algebraMap ℤ ℚ).range) →
      IsIntegral ℤ ((x : K) * y) := by
  have h1 : x ∈ differentIdeal ℤ (𝓞 K) ↔ (x : K) ∈ IsLocalization.coeSubmodule K (differentIdeal ℤ (𝓞 K)) := by
    rw [IsLocalization.mem_coeSubmodule]
    constructor
    · intro h; exact ⟨x, h, rfl⟩
    · rintro ⟨x', hx', he⟩
      have : x' = x := Subtype.ext he
      rwa [← this]
  rw [h1, coeSubmodule_differentIdeal ℤ ℚ, Submodule.mem_div_iff_forall_mul_mem]
  constructor
  · intro h y hy
    have h2 := h y (by
      rw [Submodule.mem_traceDual]
      intro a ha
      obtain ⟨a', rfl⟩ := Submodule.mem_one.1 ha
      simpa [Algebra.traceForm_apply] using hy a')
    obtain ⟨b, hb⟩ := Submodule.mem_one.1 h2
    rw [← hb]
    exact RingOfIntegers.isIntegral_coe b
  · intro h y hy
    rw [Submodule.mem_traceDual] at hy
    have hint := h y (fun a => by simpa [Algebra.traceForm_apply] using hy _ (Submodule.mem_one.2 ⟨a, rfl⟩))
    exact Submodule.mem_one.2 ⟨⟨_, (mem_integralClosure_iff ℤ K).2 hint⟩, rfl⟩

theorem diff_map {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] (e : K ≃+* K')
    (x : 𝓞 K) (x' : 𝓞 K') (hxx : e (x : K) = (x' : K')) (hx : x ∈ differentIdeal ℤ (𝓞 K)) :
    x' ∈ differentIdeal ℤ (𝓞 K') := by
  rw [mem_diff_iff] at hx ⊢
  intro y' hy'
  have htr : ∀ z : K, Algebra.trace ℚ K' (e z) = Algebra.trace ℚ K z := fun z =>
    Algebra.trace_eq_of_algEquiv e.toRatAlgEquiv z
  have hy : ∀ a : 𝓞 K, Algebra.trace ℚ K (e.symm y' * a) ∈ (algebraMap ℤ ℚ).range := by
    intro a
    have hi : IsIntegral ℤ (e (a : K)) := (RingOfIntegers.isIntegral_coe a).map (e : K →+* K').toIntAlgHom
    have h3 := hy' ⟨e a, (mem_integralClosure_iff ℤ K').2 hi⟩
    rw [← htr, map_mul, RingEquiv.apply_symm_apply]
    exact h3
  have h4 := (hx _ hy).map (e : K →+* K').toIntAlgHom
  change IsIntegral ℤ (e ((x : K) * e.symm y')) at h4
  rwa [map_mul, RingEquiv.apply_symm_apply, hxx] at h4

variable {D : D7} (X : HidaSetting D)

def eF : X.B.I.F ≃+* D.host.F :=
  RingEquiv.ofBijective
    (((X.ιE : X.B.I.E →+* D.host.E).comp (algebraMap X.B.I.F X.B.I.E)).codRestrict D.host.F
      (fun a => (X.ιE_F _).2 ⟨a, rfl⟩))
    ⟨fun a b h => iota_alg_inj X (congrArg Subtype.val h), fun y => by
      obtain ⟨a, ha⟩ := (X.ιE_F (y : D.host.E)).1 y.2
      exact ⟨a, Subtype.ext ha⟩⟩

theorem eF_val (a : X.B.I.F) : ((eF X a : D.host.F) : D.host.E) = X.ιE (algebraMap X.B.I.F X.B.I.E a) := rfl

theorem omVDdTr_holds : OmVDdTr X := by
  intro d
  constructor
  · intro hd
    obtain ⟨x, hx⟩ := pre_int X d
    refine ⟨x, diff_map (eF X).symm d x ?_ hd, hx⟩
    rw [RingEquiv.symm_apply_eq]
    exact Subtype.ext (by rw [eF_val]; exact hx.symm)
  · rintro ⟨x, hx, hxd⟩
    exact diff_map (eF X) x d (Subtype.ext (by rw [eF_val]; exact hxd)) hx

theorem omVDdLoc_holds : OmVDdLoc X := omVDdLoc_of X (omVDdTr_holds X)

variable (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem omVPrim_holds : OmVPrim X u' := omVPrim_of_dd X u' (omVDdLoc_holds X)

theorem omVPrim_holdsX : Formalism.L2.SG.Pf.NcX.OmVSt.OmVPrim X u' := omVPrim_holds X u'

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmX
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVBadTHoldsX

section

@[expose] public section

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmVZ

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem omVLocU_holds : OmVLocU X ψ := fun v a Y =>
  PI.OmLocU.Done.omLocU_closed X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) a Y

theorem omVBadT_holdsX : Formalism.L2.SG.Pf.NcX.OmVSt.OmVBadT X u' ψ :=
  PI.OmVg.omVBadT_of_ffX X u' ψ (Formalism.L2.SG.Pf.NcX.OmVSt.omega_standard_holds X ψ) (Formalism.L2.SG.Pf.NcX.OmVSt.omega_lattice_holds X)
    (OmW.omVGram_holds X u') PI.OmVe.Top.fFInertB_holds PI.OmVe.Top.fFSplitB_holds

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmVZ

namespace Formalism.L2.SG.Pf.NcX.OmVSt

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem omVZGram : OmVGram X u' := Formalism.L2.SG.Pf.NcVal.OmVSt.OmW.omVGram_holds X u'

theorem omVZDet : OmVDet X u' := Formalism.L2.SG.Pf.NcVal.OmVSt.OmW.omVDet_holds X u'

theorem omVZLocU : OmVLocU X ψ := Formalism.L2.SG.Pf.NcVal.OmVSt.OmVZ.omVLocU_holds X ψ

theorem omVZ_holdsX : Formalism.L2.SG.Pf.NcVal.OmV X u' ψ :=
  omV_of X u' ψ (omega_standard_holds X ψ) (omega_lattice_holds X) (Formalism.L2.SG.Pf.NcVal.OmVSt.OmX.omVSD_holdsX X)
    (omega_unramified_holds X) (Formalism.L2.SG.Pf.NcVal.OmVSt.OmX.omVPrim_holdsX X u') (omVZGram X u') (omVZDet X u')
    (Formalism.L2.SG.Pf.NcVal.OmVSt.OmVc.omVScale_holdsX X u' ψ) (Formalism.L2.SG.Pf.NcVal.OmVSt.OmVZ.omVBadT_holdsX X u' ψ)
    (omVZLocU X ψ)

end Formalism.L2.SG.Pf.NcX.OmVSt

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmVZ

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem omV_holdsX {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) : Formalism.L2.SG.Pf.NcVal.OmV X u' ψ :=
  Formalism.L2.SG.Pf.NcX.OmVSt.omVZ_holdsX X u' ψ

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmVZ
end
end
end
