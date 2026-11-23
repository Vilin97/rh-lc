module

public import Formalism.LocalToGlobal.GlobalTheory.UnramifiedTrace.DUAllOfParts
import Formalism.LocalToGlobal.GlobalTheory.GL6.BwAValIntegralNonneg
public import Formalism.LocalToGlobal.GlobalTheory.GL6.PDnDil
import Formalism.LocalToGlobal.GlobalTheory.GL6.PRLocV
public import Formalism.LocalToGlobal.GlobalTheory.UnramifiedDiagonal.DiaFun
public import Formalism.LocalToGlobal.GlobalTheory.UnramifiedTrace.DUPt0FOfVals
public import Formalism.LocalToGlobal.GlobalTheory.UnramifiedTrace.NatSmulInv
import Formalism.LocalToGlobal.GlobalTheory.UnramifiedTrace.TripMem
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CrossDiagonalMatching.Common
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CrossDiagonalMatching.DnkLkLocP
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CrossDiagonalMatching.DualSigmaApply
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
public import Formalism.LocalToGlobal.GlobalTheory.UnramifiedTrace.MulLatSupSpan
public import Formalism.LocalToGlobal.GlobalTheory.UnramifiedDiagonal.HeckeRamifiedZeroOfMatchingsAndDu
import Formalism.LocalToGlobal.GlobalTheory.GL6.PDnDil
import Formalism.LocalToGlobal.GlobalTheory.UnramifiedTrace.DUPt0FOfVals
public import Formalism.LocalToGlobal.GroupLattices.DownNaturalLevelZero
public import Formalism.LocalToGlobal.GlobalTheory.GL6.BwAValIntegralNonneg
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CrossDiagonalMatching.DnkLkLocP
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Formalism.LocalToGlobal.GlobalTheory.UnramifiedTrace.ProjectionKernelEqFunctional

section

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0 NumberField IsDedekindDomain Matrix
  Formalism.UG
open scoped TensorProduct Classical

variable {D : D7} {u : D.what₂.Word}

theorem projection_kernel_eq_functional (T : Forms0 D u) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0)
    (y : ↥(Ld D u 0 (Nat.zero_le _) c))
    (hy : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • y.1 ∈ Lk T.atT 0 (Nat.zero_le _) v c) :
    T.lv0.prk v c ⟨_, hy⟩ = (D.fm u).fv 0 v c (T.lv0.pr v c y) • (D.fm u).te 0 v c := by
  obtain ⟨z0, hz0⟩ := CrossDiaZero.dni_exists_one T v c
  obtain ⟨e, he⟩ := T.atT.res_surj v ((D.fm u).fv 0 v c (T.lv0.pr v c y))
  have hT0 : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • z0.1 ∈ Lk T.atT 0 (Nat.zero_le _) v c :=
    Submodule.mem_sup_left (CrossDiaZero.dnk_tld T c z0.1 z0.2)
  have hte := T.lv0.te v c z0 hz0 hT0
  have hk : (y - e • z0).1 ∈ Lk T.atT 0 (Nat.zero_le _) v c := by
    refine (T.lv0.fv_ker v c (y - e • z0)).1 ?_
    rw [map_sub, map_sub, T.lv0.pr_smul, map_smul, hz0, he, smul_eq_mul, mul_one, sub_self]
  have hTk : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (y - e • z0).1 ∈
      T.atT.Pv v • Lk T.atT 0 (Nat.zero_le _) v c :=
    Submodule.smul_mem_smul (bwA_T_mem_Pv (D := D) (u := u) (A := T.atT) (v := v)) hk
  have h0 : T.lv0.prk v c ((⟨_, hy⟩ : ↥(Lk T.atT 0 (Nat.zero_le _) v c)) - e • ⟨_, hT0⟩) = 0 := by
    refine (T.lv0.prk_ker v c _).2 ?_
    show (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • y.1 - e • ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • z0.1) ∈ _
    rw [smul_comm e, ← smul_sub]
    exact hTk
  rw [map_sub, T.lv0.prk_smul, hte, he, sub_eq_zero] at h0
  exact h0

theorem ld_locP (T : Forms0 D u) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0)
    (z3 : ↥(Ld D u 0 (Nat.zero_le _) c)) (hz3 : (D.fm u).fv 0 v c (T.lv0.pr v c z3) ≠ 0) :
    Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) c) =
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c ⊔ Submodule.span (𝓞 D.host.E) {z3.1}) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨t, ht, htx⟩ := (rlv_mem_locP _ _ _).1 hx
    obtain ⟨e, he⟩ := T.atT.res_surj v ((D.fm u).fv 0 v c (T.lv0.pr v c ⟨_, htx⟩) *
      ((D.fm u).fv 0 v c (T.lv0.pr v c z3))⁻¹)
    have hk : ((⟨_, htx⟩ : ↥(Ld D u 0 (Nat.zero_le _) c)) - e • z3).1 ∈ Lk T.atT 0 (Nat.zero_le _) v c := by
      refine (T.lv0.fv_ker v c _).1 ?_
      rw [map_sub, map_sub, T.lv0.pr_smul, map_smul, he, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hz3, mul_one,
        sub_self]
    have hl := CrossDiaZero.dnk_lk_locP T v c (mem_localization_of_mem₂ _ hk)
    obtain ⟨r, hr, hrl⟩ := (rlv_mem_locP _ _ _).1 hl
    refine (rlv_mem_locP _ _ _).2 ⟨r * t, fun h => (Ideal.IsPrime.mem_or_mem inferInstance h).elim hr ht, ?_⟩
    have e1 : (r * t) • x = r • (t • x - e • z3.1) + (r * e) • z3.1 := by
      rw [smul_sub, mul_smul, mul_smul, sub_add_cancel]
    rw [e1]
    exact Submodule.add_mem _ (Submodule.mem_sup_left hrl)
      (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)))
  · exact localization_mono₂ _ (sup_le (CrossDiaZero.cls_le_ld T c)
      ((Submodule.span_singleton_le_iff_mem _ _).2 z3.2))



theorem ptz_val (T : Forms0 D u) {v : (D.mem u).A.vT} {c : (D.mem u).C.cls 0}
    {g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c)}
    {γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))}
    {η : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)} {κ : T.cls0.lev.U}
    (hD : DnMvL T v c g γ η κ) (z : ↥(Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g))) (y : (D.fm u).lk 0 v c)
    (hy : IsPtZ T v c g γ z y) : g y = (D.fm u).fv 0 v _ (T.lv0.pr v _ z) := by
  obtain ⟨s, hs, hz, hy⟩ := hy
  have hz' : γ.1.1 *ᵥ (s • z).1 ∈ Lk T.atT 0 (Nat.zero_le _) v c := by
    rw [Submodule.coe_smul, Matrix.mulVec_smul]; exact hz
  have h4 := hD.2.2.2.1 (s • z) hz'
  have e1 : T.lv0.prk v c ⟨_, hz'⟩ = T.lv0.prk v c ⟨_, hz⟩ := by
    congr 1
    apply Subtype.ext
    show γ.1.1 *ᵥ (s • z).1 = s • (γ.1.1 *ᵥ z.1)
    rw [Submodule.coe_smul, Matrix.mulVec_smul]
  rw [e1, hy, T.lv0.pr_smul, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h4
  exact (mul_left_cancel₀ (res_ne T hs) h4).symm

def PtLatF (T : Forms0 D u) : Prop :=
  ∀ (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0) (w1 w3 : Fin (D.R.N 0) → D.host.E) (s1 s3 : 𝓞 D.host.E)
    (hz1 : s1 • w1 ∈ Lk T.atT 0 (Nat.zero_le _) v c) (hz3 : s3 • w3 ∈ Lk T.atT 0 (Nat.zero_le _) v c),
    s1 ∉ T.atT.Pv v → s3 ∉ T.atT.Pv v → ∀ y : (D.fm u).lk 0 v c,
    T.lv0.prk v c ⟨_, hz1⟩ = T.atT.res v s1 • y → T.lv0.prk v c ⟨_, hz3⟩ = T.atT.res v s3 • y →
    Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c ⊔
              Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • w1}) ≤
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c ⊔
        Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • w3})



theorem valDia_of_lat (T : Forms0 D u) (hL : PtLatF T) : ValDia T := by
  intro v c
  refine ⟨Equiv.inv _, ?_⟩
  intro G hG a g η κ μ hP k hk δ hδ
  obtain ⟨_, γ, hD, z, γ', κ', hz1, hU, hpt⟩ := hP
  obtain ⟨u1, u2, u3, u4, u5, -⟩ := hU
  have H1 := comp_of_moves T v c g γ η κ hD.1 hD.2.1 hD.2.2.1 hD.2.2.2.1 z γ' μ κ' u1 u2 u3 u4 u5
  have hga := (ptz_val T hD z _ hpt).trans hz1
  have hkb : ((k : ℤ) : (D.mem u).A.Fv v) = ((a⁻¹ : ((D.mem u).A.Fv v)ˣ) : (D.mem u).A.Fv v) := hk
  have hgte : g ((D.fm u).te 0 v c) = ((k : ℤ) : (D.mem u).A.Fv v) := by
    rw [hkb, Units.val_inv_eq_inv_val]
    rw [map_smul, smul_eq_mul] at hga
    exact eq_inv_of_mul_eq_one_right hga

  have hcl := T.val0.dil v a⁻¹ k hkb c δ hδ
  obtain ⟨hh, hhH, κ0, hκK, e⟩ := (@DoubleCoset.eq _ _ _ _ _ _).1 hcl
  have hκ : κ0.1 ∈ T.cls0.lev.U := hκK
  obtain ⟨γd, hγd, hge⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hhH)
  have hrel : (T.cls0.y c * δ).1 =
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γd *
        (T.cls0.y ((D.fm u).dil 0 v a⁻¹ c)).1 * κ0.1 := by
    rw [e]
    simp only [Subgroup.coe_mul]
    rw [← hge]
  obtain ⟨hLc, hLd⟩ := diamond_lattice_transport T v k δ hδ c ((D.fm u).dil 0 v a⁻¹ c) γd hγd ⟨κ0.1, hκ⟩ hrel
  obtain ⟨z0, hz0⟩ := CrossDiaZero.dni_exists_one T v c
  obtain ⟨ea, hea⟩ := T.atT.res_surj v (a : (D.mem u).A.Fv v)
  have hfz3 : (D.fm u).fv 0 v c (T.lv0.pr v c (ea • z0)) = (a : (D.mem u).A.Fv v) := by
    rw [T.lv0.pr_smul, map_smul, hz0, hea, smul_eq_mul, mul_one]
  have hTne : (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0 := by exact_mod_cast (D.mem u).A.T_prime.ne_zero
  have hw3v : ((((D.mem u).A.T : ℕ) : D.host.E))⁻¹ • ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (ea • z0).1) =
      (ea • z0).1 := by
    rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul D.host.E, inv_smul_smul₀ hTne]
  have H3 : IsCompMv T v c ((D.fm u).dil 0 v a⁻¹ c) ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (ea • z0).1) g
      ⟨γd, hγd⟩ δ (⟨κ0.1, hκ⟩⁻¹) := by
    refine ⟨hδ.1, ?_, congrArg _ hLc, ?_, ?_⟩
    · show bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γd *
          (T.cls0.y ((D.fm u).dil 0 v a⁻¹ c)).1 = (T.cls0.y c).1 * δ.1 * κ0.1⁻¹
      simp only [Subgroup.coe_mul] at hrel
      rw [hrel, mul_inv_cancel_right]
    · show Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)
          (Ld D u 0 (Nat.zero_le _) ((D.fm u).dil 0 v a⁻¹ c))) = _
      rw [hLd, hw3v]
      exact ld_locP T v c (ea • z0) (by rw [hfz3]; exact Units.ne_zero a)
    · intro x hx
      have hw : (γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ x.1 ∈ Ld D u 0 (Nat.zero_le _) c :=
        CrossDiaZero.dni_mem_of _ hLd x.2
      have hz2 : ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ
          ((γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ x.1) ∈
          Ld D u 0 (Nat.zero_le _) ((D.fm u).dil 0 v a⁻¹ c) := by
        rw [inv_mv]; exact x.2
      have hdf := UnramifiedDiagonal.diaFun_same T v k δ hδ c _ γd ⟨κ0.1, hκ⟩ hrel _ hw hz2
      rw [CrossDiaZero.pr_congr T v _ ⟨_, hz2⟩ x (inv_mv γd x.1)] at hdf
      rw [hdf]
      have hp := projection_kernel_eq_functional T v c ⟨_, hw⟩ hx
      show _ = g (T.lv0.prk v c ⟨_, hx⟩)
      rw [hp, map_smul, hgte, smul_eq_mul, zsmul_eq_mul, mul_comm]

  have hw3 : (1 : 𝓞 D.host.E) • ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (ea • z0).1) ∈
      Lk T.atT 0 (Nat.zero_le _) v c := by
    rw [one_smul]; exact Submodule.mem_sup_left (CrossDiaZero.dnk_tld T c _ (ea • z0).2)
  have hy3 : T.lv0.prk v c ⟨_, hw3⟩ = T.atT.res v 1 • ((a : (D.mem u).A.Fv v) • (D.fm u).te 0 v c) := by
    have hT3 : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (ea • z0).1 ∈ Lk T.atT 0 (Nat.zero_le _) v c := by
      rw [← one_smul (𝓞 D.host.E) ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (ea • z0).1)]; exact hw3
    have e3 : (⟨_, hw3⟩ : ↥(Lk T.atT 0 (Nat.zero_le _) v c)) = ⟨_, hT3⟩ := Subtype.ext (one_smul _ _)
    rw [e3, projection_kernel_eq_functional T v c (ea • z0) hT3, hfz3, map_one, one_smul]
  obtain ⟨s1, hs1, hw1, hy1⟩ := hpt
  have hlat := le_antisymm
    (hL v c _ _ s1 1 hw1 hw3 hs1 (one_nmem T) _ hy1 hy3)
    (hL v c _ _ 1 s1 hw3 hw1 (one_nmem T) hs1 _ hy3 hy1)
  have hm := comp_cmp T v c _ _ (γ.1.1 *ᵥ z.1) _ g g (γ * γ') ⟨γd, hγd⟩ (hcomp T η κ μ) δ (κ * κ')
    (⟨κ0.1, hκ⟩⁻¹) H1 H3 hlat (dn_fwd T hD z.1 z.2) (fun _ _ _ _ => rfl)
  exact val_of_mem T v (T.cls0.y c) δ (hcomp T η κ μ) hδ.1 H1.1 hm G hG

end Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

end
end
end

-- Source module: Formalism.LocalToGlobal.GlobalTheory.UnramifiedTrace.TNotinSq

section

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0 NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct Classical

variable {D : D7} {u : D.what₂.Word}




theorem t_notin_sq (T : Forms0 D u) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0) :
    (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∉ T.atT.Pv v ^ 2 := by
  intro hT
  obtain ⟨x0, hx0⟩ : ∃ x0, (D.fm u).fv 0 v c x0 ≠ 0 := by
    by_contra h
    apply (D.fm u).fv_ne 0 v c
    ext x0
    by_contra hx
    exact h ⟨x0, by rwa [LinearMap.zero_apply] at hx⟩
  obtain ⟨z, hz⟩ := T.lv0.pr_surj v c (((D.fm u).fv 0 v c x0)⁻¹ • x0)
  have hx : (D.fm u).fv 0 v c (T.lv0.pr v c z) = 1 := by
    rw [hz, map_smul, smul_eq_mul, inv_mul_cancel₀ hx0]
  have hTz : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • z.1 ∈ Lk T.atT 0 (Nat.zero_le _) v c :=
    Submodule.mem_sup_left (CrossDiaZero.dnk_tld T c z.1 z.2)
  have hte := T.lv0.te v c z hx hTz
  have hsq : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • z.1 ∈ T.atT.Pv v • Lk T.atT 0 (Nat.zero_le _) v c := by
    have h1 : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • z.1 ∈ (T.atT.Pv v ^ 2) • Ld D u 0 (Nat.zero_le _) c :=
      Submodule.smul_mem_smul hT z.2
    rw [pow_two, Submodule.mul_smul] at h1
    exact Submodule.smul_mono le_rfl le_sup_right h1
  have h0 := (T.lv0.prk_ker v c ⟨_, hTz⟩).2 hsq
  rw [hte] at h0
  exact (D.fm u).te_ne 0 v c h0




theorem exists_not_mem_Pv_mul_mem_span_T (T : Forms0 D u) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0) :
    ∃ s : 𝓞 D.host.E, s ∉ T.atT.Pv v ∧ ∀ p ∈ T.atT.Pv v, ∃ e : 𝓞 D.host.E,
      s * p = e * (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) := by
  have hle : Ideal.span {(((D.mem u).A.T : ℕ) : 𝓞 D.host.E)} ≤ T.atT.Pv v :=
    (Ideal.span_singleton_le_iff_mem _).2 (bwA_T_mem_Pv (D := D) (u := u) (A := T.atT) (v := v))
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.2 hle
  have hJP : ¬ J ≤ T.atT.Pv v := by
    intro h
    apply t_notin_sq T v c
    have h2 : Ideal.span {(((D.mem u).A.T : ℕ) : 𝓞 D.host.E)} ≤ T.atT.Pv v ^ 2 := by
      rw [hJ, pow_two]; exact Ideal.mul_mono_right h
    exact h2 (Ideal.subset_span rfl)
  obtain ⟨s, hsJ, hsP⟩ := Set.not_subset.1 hJP
  refine ⟨s, hsP, fun p hp => ?_⟩
  have hm : s * p ∈ Ideal.span {(((D.mem u).A.T : ℕ) : 𝓞 D.host.E)} := by
    rw [hJ, mul_comm s p]; exact Ideal.mul_mem_mul hp hsJ
  obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 hm
  exact ⟨e, he.symm⟩

end Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

end
end
end

-- Source module: Formalism.LocalToGlobal.GlobalTheory.UnramifiedTrace.DUAllOfSameTe

section

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0 NumberField IsDedekindDomain Matrix
  Formalism.UG
open scoped TensorProduct Classical

section Gen

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem natS_cancel (N : ℕ) (hN : (N : E) ≠ 0) (a b : Fin n → E)
    (h : ((N : ℕ) : 𝓞 E) • a = ((N : ℕ) : 𝓞 E) • b) : a = b := by
  funext i
  have hi := congrFun h i
  simp only [Pi.smul_apply, Algebra.smul_def, map_natCast] at hi
  exact mul_left_cancel₀ hN hi

theorem natS_inv (N : ℕ) (hN : (N : E) ≠ 0) (w : Fin n → E) : ((N : ℕ) : 𝓞 E) • ((N : E)⁻¹ • w) = w := by
  funext i
  simp [Algebra.smul_def, hN]

theorem smul_T_of (P : Ideal (𝓞 E)) (N : Submodule (𝓞 E) (Fin n → E)) (σ τ : 𝓞 E)
    (hσT : ∀ p ∈ P, ∃ e : 𝓞 E, σ * p = e * τ) (q : Fin n → E) (hq : q ∈ P • N) :
    ∃ d' ∈ N, σ • q = τ • d' := by
  refine Submodule.smul_induction_on (p := fun q => ∃ d' ∈ N, σ • q = τ • d') hq
    (fun p hp n hn => ?_) (fun x y hx hy => ?_)
  · obtain ⟨e, he⟩ := hσT p hp
    exact ⟨e • n, N.smul_mem e hn, by rw [smul_smul, he, mul_comm e τ, mul_smul]⟩
  · obtain ⟨d1, h1, e1⟩ := hx
    obtain ⟨d2, h2, e2⟩ := hy
    exact ⟨d1 + d2, N.add_mem h1 h2, by rw [smul_add, e1, e2, smul_add]⟩

end Gen

variable {D : D7} {u : D.what₂.Word}



theorem ptLat_holds (T : Forms0 D u) : PtLatF T := by
  intro v c w1 w3 s1 s3 hz1 hz3 hs1 hs3 y hy1 hy3
  have hTne : (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0 := by exact_mod_cast (D.mem u).A.T_prime.ne_zero
  have hdm : s3 • (s1 • w1) - s1 • (s3 • w3) ∈ Lk T.atT 0 (Nat.zero_le _) v c :=
    sub_mem (Submodule.smul_mem _ _ hz1) (Submodule.smul_mem _ _ hz3)
  have hd0 : T.lv0.prk v c ⟨_, hdm⟩ = 0 := by
    have e0 : (⟨_, hdm⟩ : ↥(Lk T.atT 0 (Nat.zero_le _) v c)) =
        s3 • (⟨_, hz1⟩ : ↥(Lk T.atT 0 (Nat.zero_le _) v c)) - s1 • (⟨_, hz3⟩ : ↥(Lk T.atT 0 (Nat.zero_le _) v c)) :=
      Subtype.ext rfl
    rw [e0, map_sub, T.lv0.prk_smul, T.lv0.prk_smul, hy1, hy3, smul_smul, smul_smul, mul_comm, sub_self]
  have hdP : s3 • (s1 • w1) - s1 • (s3 • w3) ∈ T.atT.Pv v • Lk T.atT 0 (Nat.zero_le _) v c :=
    (T.lv0.prk_ker v c _).1 hd0
  obtain ⟨σ, hσ, hσT⟩ := exists_not_mem_Pv_mul_mem_span_T T v c
  obtain ⟨d', hd'L, hd'⟩ := smul_T_of _ _ σ _ hσT _ hdP
  have hW : (σ * s1 * s3) • ((((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • w1) =
      d' + (σ * s1 * s3) • ((((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • w3) := by
    rw [← sub_eq_iff_eq_add]
    apply natS_cancel _ hTne
    rw [← hd', smul_sub, smul_comm (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) (σ * s1 * s3),
      smul_comm (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) (σ * s1 * s3), natS_inv _ hTne, natS_inv _ hTne, smul_sub,
      smul_smul, smul_smul, smul_smul, smul_smul, mul_right_comm σ s3 s1]
  have hd'loc := CrossDiaZero.dnk_lk_locP T v c (mem_localization_of_mem₂ _ hd'L)
  obtain ⟨t', ht', ht'd⟩ := (rlv_mem_locP _ _ _).1 hd'loc
  intro x hx
  obtain ⟨t, ht, htx⟩ := (rlv_mem_locP _ _ _).1 hx
  obtain ⟨l, hl, m, hm, em⟩ := Submodule.mem_sup.1 htx
  obtain ⟨e, rfl⟩ := Submodule.mem_span_singleton.1 hm
  have hP : (T.atT.Pv v).IsPrime := inferInstance
  refine (rlv_mem_locP _ _ _).2 ⟨t' * (σ * s1 * s3) * t, ?_, ?_⟩
  · intro h
    rcases hP.mem_or_mem h with h | h
    · rcases hP.mem_or_mem h with h | h
      · exact ht' h
      · rcases hP.mem_or_mem h with h | h
        · rcases hP.mem_or_mem h with h | h
          · exact hσ h
          · exact hs1 h
        · exact hs3 h
    · exact ht h
  · rw [mul_smul, ← em, smul_add]
    refine add_mem (Submodule.mem_sup_left (Submodule.smul_mem _ _ hl)) ?_
    rw [smul_comm (t' * (σ * s1 * s3)) e, mul_smul t' (σ * s1 * s3), hW, smul_add, smul_add]
    exact add_mem (Submodule.mem_sup_left (Submodule.smul_mem _ _ ht'd))
      (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.smul_mem _ _
        (Submodule.mem_span_singleton_self _)))))

theorem valDia_holds (T : Forms0 D u) : ValDia T :=
  valDia_of_lat T (ptLat_holds T)

theorem dUAll_of_same_te (h : ∀ (D : D7) (u : D.what₂.Word) (T : Forms0 D u), ValSame T ∧ ValTe T) :
    Formalism.L2.GlobalTheoryTheory.UnramifiedDiagonal.DUAll :=
  dUAll_of_vals fun D u T => ⟨(h D u T).1, (h D u T).2, valDia_holds T⟩

end Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

end
end
end
