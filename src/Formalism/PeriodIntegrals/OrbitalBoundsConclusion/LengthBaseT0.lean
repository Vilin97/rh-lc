module

public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.FirstLengthLePrimeBound
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.TaylorSpanGeneratorsAlt
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FiltLenF
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SumAntidiagonalTuple
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.Column
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.EqZeroOfOrdTop
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.FkFilt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.HasseMemHK
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.FinitePtsOfCurve
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
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.HassePresH
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.HasseVan
import Mathlib.Tactic.Linter.Style
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.HasseVan
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.MonoCount
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.TaylorRep
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.FinitePtsOfCurve
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.TaylorHasse

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.HasseOpSmul

section

@[expose] public section

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PoleLengthBounds

theorem sum_snd_le {D : D7} {j N : ℕ} {β : Idx D j N →₀ ℕ} {q : (Idx D j N →₀ ℕ) × (Idx D j N →₀ ℕ)}
    (hq : q ∈ Finset.HasAntidiagonal.antidiagonal β) :
    (q.2.sum fun _ n => n) ≤ (β.sum fun _ n => n) := by
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq
  rw [← hq, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
  exact Nat.le_add_left _ _

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {wL wF : WeightFamilies.Wt D j}
  {la : HeightOneSpectrum (𝓞 B.KO)} {N : ℕ} {w : Fin N → B.Cusp j wL}

theorem hasse_Op_smul (o : Op X la N) (x : ↥(HK X la w wF)) (β : Idx D j N →₀ ℕ) :
    hasse X la w β (((@algebraMap (Op X la N) (Kp X la N) _ _ _ o • x : ↥(HK X la w wF))) : Lw X la w) =
      ∑ q ∈ Finset.HasAntidiagonal.antidiagonal β,
        @algebraMap (Op X la N) (Kp X la N) _ _ _ (hasseOp X la N q.1 o) • hasse X la w q.2 (x : Lw X la w) := by
  have e1 : ((@algebraMap (Op X la N) (Kp X la N) _ _ _ o • x : ↥(HK X la w wF)) : Lw X la w) =
      algebraMap (Rp X la N) (Lw X la w) (algebraMap (Op X la N) (Rp X la N) o) * (x : Lw X la w) := by
    rw [Submodule.coe_smul_of_tower, Algebra.smul_def,
      IsScalarTower.algebraMap_apply (Kp X la N) (Rp X la N) (Lw X la w),
      ← IsScalarTower.algebraMap_apply (Op X la N) (Kp X la N) (Rp X la N)]
  rw [e1]
  refine (hasse_mul X la w β _ _).trans (Finset.sum_congr rfl fun q _ => ?_)
  rw [Algebra.smul_def]
  congr 1
  rw [IsScalarTower.algebraMap_apply (Kp X la N) (Rp X la N) (Lc X la w),
    ← IsScalarTower.algebraMap_apply (Op X la N) (Kp X la N) (Rp X la N)]
  exact hasse_algebraMap_Op X la w q.1 o

theorem aaRep_holds : AARep := by
  unfold AARep
  intro D B P j X ka wL wF G la Q S CRm T c hOk hw x hx
  have hC : Q.InCurve := hOk.2.1
  have hU := isUnif_of_curve Q hC
  have : ∀ ζ : PtsG G la, IsDVRAt ζ := fun ζ => isDVRAt_of_curve Q hC ζ
  suffices key : ∃ x' : ↥(HK X la G.w wF),
      (∃ hx' : ∀ β : Idx D j G.N →₀ ℕ, (β.sum fun _ n => n) ≤ a0 D j T - 1 →
          hasse X la G.w β (x' : Lw X la G.w) ∈ HK X la G.w wF,
        ∀ β hβ, toA0K X la G.w wF ⟨_, hx' β hβ⟩ ∈ Q.A0) ∧
      toWK X la G.w wF (a0 D j T) x' = x by
    obtain ⟨x', ⟨_, h2⟩, h3⟩ := key
    exact ⟨x', h3, fun β hβ _ => h2 β hβ⟩
  unfold LocalPointData.AA LocalPointData.AAp at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x0, ⟨hx0, hb0⟩, rfl⟩ := hy
    refine ⟨x0, ⟨hx0, fun β hβ => ?_⟩, rfl⟩
    unfold LocalPointData.A0
    rw [mem_ballO_iff Q.c hU hC.2.2]
    intro ζ
    have h := hb0 β hβ ζ
    simpa [LocalPointData.ordA] using h
  | zero =>
    have hz : ∀ β : Idx D j G.N →₀ ℕ,
        hasse X la G.w β ((0 : ↥(HK X la G.w wF)) : Lw X la G.w) = 0 := fun β => by
      exact map_zero (hasse X la G.w β)
    refine ⟨0, ⟨fun β _ => by rw [hz]; exact (HK X la G.w wF).zero_mem, fun β hβ => ?_⟩, map_zero _⟩
    convert Q.A0.zero_mem using 1
    rw [← map_zero (toA0K X la G.w wF)]
    exact congrArg _ (Subtype.ext (hz β))
  | add a b _ _ ha hb =>
    obtain ⟨xa, ⟨ha1, ha2⟩, rfl⟩ := ha
    obtain ⟨xb, ⟨hb1, hb2⟩, rfl⟩ := hb
    have hs : ∀ β : Idx D j G.N →₀ ℕ, hasse X la G.w β ((xa + xb : ↥(HK X la G.w wF)) : Lw X la G.w) =
        hasse X la G.w β (xa : Lw X la G.w) + hasse X la G.w β (xb : Lw X la G.w) := fun β => by
      exact map_add (hasse X la G.w β) _ _
    refine ⟨xa + xb, ⟨fun β hβ => by rw [hs]; exact add_mem (ha1 β hβ) (hb1 β hβ), fun β hβ => ?_⟩, map_add _ _ _⟩
    convert Q.A0.add_mem (ha2 β hβ) (hb2 β hβ) using 1
    rw [← map_add (f := _)]
    exact congrArg _ (Subtype.ext (hs β))
  | smul o y _ ih =>
    classical
    obtain ⟨x0, ⟨h1, h2⟩, rfl⟩ := ih
    let g : (Idx D j G.N →₀ ℕ) × (Idx D j G.N →₀ ℕ) → ↥(HK X la G.w wF) := fun q =>
      if h : hasse X la G.w q.2 (x0 : Lw X la G.w) ∈ HK X la G.w wF then ⟨_, h⟩ else 0
    have hg' : ∀ q : (Idx D j G.N →₀ ℕ) × (Idx D j G.N →₀ ℕ), ∀ hq : (q.2.sum fun _ n => n) ≤ a0 D j T - 1,
        g q = ⟨_, h1 q.2 hq⟩ := fun q hq => dif_pos (h1 q.2 hq)
    let F : (Idx D j G.N →₀ ℕ) → ↥(HK X la G.w wF) := fun β =>
      ∑ q ∈ Finset.HasAntidiagonal.antidiagonal β, @algebraMap (Op X la G.N) (Kp X la G.N) _ _ _ (hasseOp X la G.N q.1 o) • g q
    have he : ∀ β : Idx D j G.N →₀ ℕ, (β.sum fun _ n => n) ≤ a0 D j T - 1 →
        hasse X la G.w β ((@algebraMap (Op X la G.N) (Kp X la G.N) _ _ _ o • x0 : ↥(HK X la G.w wF)) : Lw X la G.w) =
          ((F β : ↥(HK X la G.w wF)) : Lw X la G.w) := by
      intro β hβ
      rw [hasse_Op_smul, Submodule.coe_sum]
      refine Finset.sum_congr rfl fun q hq => ?_
      rw [Submodule.coe_smul_of_tower, hg' q ((sum_snd_le hq).trans hβ)]
      rfl
    refine ⟨@algebraMap (Op X la G.N) (Kp X la G.N) _ _ _ o • x0, ⟨fun β hβ => ?_, fun β hβ => ?_⟩, ?_⟩
    · rw [he β hβ]
      exact Submodule.coe_mem _
    · have hm : toA0K X la G.w wF (F β) ∈ Q.A0 := by

        rw [map_sum]
        refine Q.A0.sum_mem fun q hq => ?_
        rw [LinearMap.map_smul_of_tower, algebraMap_smul, hg' q ((sum_snd_le hq).trans hβ)]
        exact Q.A0.smul_mem _ (h2 q.2 ((sum_snd_le hq).trans hβ))
      convert hm using 1
      exact congrArg _ (Subtype.ext (he β hβ))
    · rw [LinearMap.map_smul_of_tower]
      rfl

end PoleLengthBounds
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.HasseSmul

section

@[expose] public section

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PoleLengthBounds

theorem hasseSmul_holds : HasseSmul := by
  intro D B P j X ka wL wF G la k o x hx β hβ h h'
  classical
  have hmem : ∀ q : Idx D j G.N →₀ ℕ, hasse X la G.w q (x : Lw X la G.w) ∈ HK X la G.w wF := fun q =>
    (mem_HK X la G.w).2 (hasse_presentation X la G.w wF q _ ((mem_HK X la G.w).1 x.2))
  have key : (⟨_, h⟩ : ↥(HK X la G.w wF)) = ∑ q ∈ Finset.HasAntidiagonal.antidiagonal β,
      (@algebraMap (Op X la G.N) (Kp X la G.N) _ _ _ (hasseOp X la G.N q.1 o)) •
        (⟨_, hmem q.2⟩ : ↥(HK X la G.w wF)) := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    show hasse X la G.w β ((o • x : ↥(HK X la G.w wF)) : Lw X la G.w) = _
    rw [Submodule.coe_smul_of_tower, Algebra.smul_def,
      IsScalarTower.algebraMap_apply (Op X la G.N) (Rp X la G.N) (Lw X la G.w)]
    erw [hasse_mul]
    refine Finset.sum_congr rfl fun q _ => ?_
    erw [hasse_algebraMap_Op]
    rw [Submodule.coe_smul_of_tower, Algebra.smul_def]
    congr 1

  rw [key, map_sum, Finset.sum_eq_single (0, β)]
  · rw [LinearMap.map_smul_of_tower, hasseOp_zero, algebraMap_smul]
  · intro q hq hne
    rw [LinearMap.map_smul_of_tower]
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq
    have h1 : q.1 ≠ 0 := fun h0 => hne (Prod.ext h0 (by rw [← hq, h0, zero_add]))
    have h2 : (q.2.sum fun _ n => n) < k := by
      rw [sumN_eq] at hβ ⊢
      rw [← hq, map_add (f := _)] at hβ
      have : Finsupp.degree q.1 ≠ 0 := fun h0 => h1 ((Finsupp.degree_eq_zero_iff _).1 h0)
      omega
    rw [hasseVan_holds G la k x hx q.2 h2 (hmem q.2), smul_zero]
  · intro h0
    exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.2 (zero_add β)) h0

end PoleLengthBounds
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.LenBaseOf

section

@[expose] public section

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PoleLengthBounds

theorem sum_mon_le (hM : MonoCount) (D : D7) (j T n : ℕ) :
    ∑ k ∈ Finset.range (a0 D j T), (mon D j k).card * n ≤ Nat.choose (T - 1) (WeightFamilies.dimY D j) * n := by
  rw [← Finset.sum_mul]
  by_cases h : WeightFamilies.dimY D j < T
  · rw [show a0 D j T = T - WeightFamilies.dimY D j from rfl, hM _ _ h]
  · have h0 : a0 D j T = 0 := by
      show T - WeightFamilies.dimY D j = 0
      omega
    simp [h0]

theorem lenBase_of (hF : FiltLenGr) (hM : MonoCount) (hK : FkFilt) (hG : GrBound) :
    ∀ {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j},
      LenBase (X := X) (ka := ka) (wL := wL) (wF := wF) := by
  intro D B P j X ka wL wF G la Q S CRm T c hOk hth hw hI
  obtain ⟨hA, h0, hT⟩ := hK G la T
  obtain ⟨φ, Pk, Qk, hker, hP, hQ, hL⟩ := hG G la Q S CRm T c hOk hth hw hI
  have key := hF (Op X la G.N) (WK X la G.w wF (a0 D j T)) (Fk G la T) (a0 D j T) hA h0 hT
    (fun _ => Vg G la) φ hker (Q.AA T) (firstLength_le_prime_bound G la T ⊓ Q.AA T) Pk Qk inf_le_right hP hQ
  have e : (firstLength_le_prime_bound G la T ⊓ Q.AA T).comap (Q.AA T).subtype = (firstLength_le_prime_bound G la T).comap (Q.AA T).subtype := by
    ext x
    simp [x.2]
  rw [e] at key
  refine key.trans ?_
  calc ∑ k ∈ Finset.range (a0 D j T), Module.length (Op X la G.N) (↥(Pk k) ⧸ (Qk k).comap (Pk k).subtype)
      ≤ ∑ k ∈ Finset.range (a0 D j T), ((((mon D j k).card * Q.Ila.toNat : ℕ)) : ℕ∞) :=
        Finset.sum_le_sum fun k hk => hL k (Finset.mem_range.1 hk)
    _ = ((∑ k ∈ Finset.range (a0 D j T), (mon D j k).card * Q.Ila.toNat : ℕ) : ℕ∞) := by
        push_cast; rfl
    _ ≤ _ := by exact_mod_cast sum_mon_le hM D j T Q.Ila.toNat

end PoleLengthBounds
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.UInjOfColumn

section

@[expose] public section

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PoleLengthBounds

theorem uInj_of_column (hCol : Column) : UInj := by
  unfold UInj
  intro D B P j X ka wL wF G la Q S CRm T c hOk hw α b hb
  have hC : Q.InCurve := hOk.2.1
  have hU := isUnif_of_curve Q hC
  have : ∀ ζ : PtsG G la, IsDVRAt ζ := fun ζ => isDVRAt_of_curve Q hC ζ
  have hco : (coord Q.e b : OsK X la G.w) = 0 := by
    refine eq_zero_of_ord_top hU fun ζ => ?_
    obtain ⟨jj, hjj⟩ := (hCol G la Q S CRm T c hOk hw ζ).2
    have h1 := congrArg (ordV (unifO X la G.N) ζ Q.e Q.c) (hb jj)
    rw [ordV_smul Q.c ζ hU hC.2.2, ord_uC_eq_zero Q hC ζ jj α hjj, zero_add,
      ordV_zero Q.c ζ hU hC.2.2, ordV, WithTop.add_eq_top] at h1
    rcases h1 with h1 | h1
    · exact h1
    · exact absurd h1 WithTop.coe_ne_top
  rw [← coord_smul_self hC.2.2 b, hco, zero_smul]

end PoleLengthBounds
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.Assembly

section

@[expose] public section

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PoleLengthBounds

theorem filtLenGr_holds : FiltLenGr := by
  intro R W _ _ _ F a hF h0 ha V _ _ φ hker M N P Q hNM hP hQ
  refine filtration_length_bound R W F a hF h0 ha V φ hker M N P Q hNM
    (fun k hk => Submodule.map_le_iff_le_comap.2 fun x hx => hP k hk x hx) (fun k hk v hv => ?_)
  obtain ⟨x, hx, rfl⟩ := hQ k hk v hv
  exact Submodule.mem_map_of_mem hx

theorem monoCount_holds : MonoCount := sum_antidiagonalTuple

theorem lenBase_of_steps (hTR : TaylorRep) (hTH : TaylorHasse) (hHS : HasseSmul) (hHV : HasseVan) (hUI : UInj)
    (hUB : UBall) (hAR : AARep) :
    ∀ {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j},
      LenBase (X := X) (ka := ka) (wL := wL) (wF := wF) :=
  lenBase_of filtLenGr_holds monoCount_holds fkFilt_holds (grBound_of hTR hTH hHS hHV hUI hUB hAR)

theorem lenBase_of_taylorHasse (hTH : TaylorHasse) :
    ∀ {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j},
      LenBase (X := X) (ka := ka) (wL := wL) (wF := wF) :=
  lenBase_of_steps taylorRep_holds hTH hasseSmul_holds hasseVan_holds (uInj_of_column column_holds)
    (uBall_of_column column_holds) aaRep_holds

end PoleLengthBounds
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.LenBaseHolds

section

@[expose] public section

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PoleLengthBounds

theorem lenBase_holds :
    ∀ {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j},
      LenBase (X := X) (ka := ka) (wL := wL) (wF := wF) :=
  lenBase_of_taylorHasse taylorHasse_holds

end PoleLengthBounds
end
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LengthBaseT0

section

@[expose] public section

theorem length_base_t0 : ∀ {D : Formalism.BasicNotions.D7} {B : Formalism.MainNotions.WeightFamilies.Prov D} {P : Formalism.MainNotions.ModuliIntegralCharts.Prov D} {j : ℕ}
    {X : Formalism.MainNotions.WeightAlgebra.PJ D B P j} {ka wL wF : Formalism.MainNotions.WeightFamilies.Wt D j},
    Formalism.MainNotions.Gaps.EtaleWeightGaps.LenBase (X := X) (ka := ka) (wL := wL) (wF := wF) :=
  PoleLengthBounds.lenBase_holds
end
end
