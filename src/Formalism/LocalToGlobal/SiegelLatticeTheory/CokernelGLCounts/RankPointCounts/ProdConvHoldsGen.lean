module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CanonicalAnalyticData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TheoremSRecursion
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdConvNewTies
public import Formalism.LocalRingCardinality.IntCastDvdOfDvdIntegers
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcValVolOrd
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcValVolOrdFull
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcValVolOrdSd
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.CondAllPf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.VolVFinal
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
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataTies
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcValVolOrdSd
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcValVolOrdTr
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataTies
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.CondAllPf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.InertPow
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.KitAbs
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.Development
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.BoxMul
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.KitShear
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensFibV
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DetAdmA
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TensTop
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.ContinuousTrESymm
import Mathlib.Tactic.Linter.HaveILetI
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcValVolOrdA

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocalPositivity

section

@[expose] public section

noncomputable section

open scoped Classical TensorProduct

namespace Formalism.L2.SG.Pf.LocalPositivity

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.Pf.NcVal
  Formalism.L2.SG.Pf.NcVal.VolOrdW Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Formalism.L2.SG.TypedSets

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem pos_of_div {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : 0 < a / b) : 0 < a ∧ 0 < b := by
  rcases div_pos_iff.1 h with h' | h'
  · exact h'
  · exact absurd ha (not_le.2 h'.1)

theorem localVolumeUnit_pos_and_ZZX_pos (hψ : IsCharAF X.B.I.F ψ) (hs : IsStdChar ψ)
    (hTT : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2]) (hg : ∀ v, TypAt X v → 0 < gAt X v) (v : PlX X) :
    0 < localVolumeUnit X ψ v ∧ 0 < ZZX X u u' ψ v := by
  have hU : 0 ≤ localVolumeUnit X ψ v := ENNReal.toReal_nonneg
  have hZ : 0 ≤ ZZX X u u' ψ v := ENNReal.toReal_nonneg
  by_cases hv : TypAt X v
  · have e := volTypV_holds X u u' ψ hψ hs hTT v hv
    exact pos_of_div hU hZ (by rw [e]; exact pow_pos (by exact_mod_cast hg v hv) _)
  · have e := volOrdV_holds X u u' ψ hψ hs v hv
    exact pos_of_div hU hZ (by rw [e]; exact Real.rpow_pos_of_pos (absV_pos v (dV_ne_zero v)) _)

theorem pp_pos_ord (hψ : IsCharAF X.B.I.F ψ) (hs : IsStdChar ψ) {v : PlX X} (hv : ¬ TypAt X v)
    (l : Fin (D.R.rS + 1)) : 0 < PPX X u u' ψ l v := by
  have hN : SdNormDV X ψ := sdNormDV_of X ψ (annX_of X ψ Formalism.L2.SG.Pf.conductor_inverse_different) hψ hs
  have hfin : Module.finrank X.B.I.F X.B.I.E = 2 := X.B.I.cm.deg2
  obtain ⟨hH, -, hO⟩ := hN v hv Unit
  have := hH
  have hset : (fun c : Unit → Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E => c ()) ⁻¹' PPOrd (E := X.B.I.E) v D.R.rS l =
      Set.univ.pi fun _ : Unit => {c | sc (E := X.B.I.E) v (alp v D.R.rS l ^ 2) * c ∈ OEv (E := X.B.I.E) v} := by
    ext z
    simp [PPOrd, Set.mem_pi]
    exact ⟨fun h i => h, fun h => h ()⟩
  unfold PPX volC
  rw [if_neg hv, hset, SdW.boxScaleL_holds v Unit hfin (sdE (E := X.B.I.E) ψ v Unit)
    (fun _ : Unit => alp v D.R.rS l ^ 2) (fun _ => pow_ne_zero _ (alp_ne_zero v D.R.rS l)), hO]
  refine mul_pos (pow_pos (absV_pos v (dV_ne_zero v)) _) (Finset.prod_pos fun q _ => ?_)
  exact inv_pos.2 (pow_pos (absV_pos v (pow_ne_zero _ (alp_ne_zero v D.R.rS l))) 2)

theorem jac_pos (hg : ∀ v, TypAt X v → 0 < gAt X v) (v : PlX X) : 0 < jacX X v := by
  unfold jacX jacS
  refine Finset.prod_pos fun l _ => ?_
  have hx : (∏ i ∈ Finset.univ.filter (fun i : Fin (D.R.rS + 1) => (i : ℕ) ≤ (l : ℕ)), alp v D.R.rS i ^ 2) *
      (if TypAt X v then ((gAt X v : Fv X.B.I.F v)⁻¹) ^ ((l : ℕ) + 1) else 1) ≠ 0 := by
    refine mul_ne_zero (Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (alp_ne_zero v D.R.rS i)) ?_
    split_ifs with ht
    · refine pow_ne_zero _ (inv_ne_zero ?_)
      exact_mod_cast (hg v ht).ne'
    · exact one_ne_zero
  exact pow_pos (pow_pos (absV_pos v hx) 2) 2

end Formalism.L2.SG.Pf.LocalPositivity
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.ParabolicVolume

section

@[expose] public section

noncomputable section

namespace PI.UnitaryGroupMassFormula.LocJacTyp

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain PI.LocJacTyp
open scoped TensorProduct

attribute [local instance] PI.VolStabSW.secondCountable_Fv PI.VolStabSW.locallyCompact_Fv
attribute [local instance] Sd.finDim

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F))

theorem unit_forall {P : Unit → Prop} : (∀ i, P i) ↔ P () := ⟨fun h => h (), fun h _ => h⟩

theorem parabolic_volume : VolPP σ v := by
  intro g r T T' m hS hg hT μ hμ hm l
  obtain ⟨D⟩ := exists_SD hS
  have hp0 : ∀ s t, D.p 0 (D.pt s t) = s := fun s t => (D.p_pt s t).1
  have hp1 : ∀ s t, D.p 1 (D.pt s t) = t := fun s t => (D.p_pt s t).2
  have hg0 : (g : Fv F v) ≠ 0 := natCast_ne_zero v hg
  have hgO : (g : Fv F v) ∈ v.adicCompletionIntegers F := natCast_mem _ g
  have hsh : ∀ X : Set (Unit → Fv F v ⊗[F] E), μ ((D.shear id) ⁻¹' X) = μ X :=
    haar_shear μ (D.shear id) (Obox (E := E) v Unit) (obox_compact Unit) (obox_open Unit)
      (obox_nonempty Unit) (D.shear_box id)
  by_cases hl : (l : ℕ) < r
  · have ha : alp v r l ^ 2 ≠ 0 := pow_ne_zero _ (alp_ne_zero v r l)
    have hset : (fun c : Unit → Fv F v ⊗[F] E => c ()) ⁻¹' PPTyp σ v g r T T' l =
        (D.shear id) ⁻¹' (Set.univ.pi fun _ : Unit =>
          {c | D.pt (alp v r l ^ 2 * ((g : Fv F v)⁻¹) ^ 2) (alp v r l ^ 2 * (g : Fv F v)⁻¹) * c ∈
            OEv (E := E) v}) := by
      ext c
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_ofPred_eq, PPTyp,
        if_pos hl, unit_forall]
      rw [D.mem_sc_mul, D.mem_sc_mul, D.mem_pt_mul, D.shear_first_coordinate, D.shear_second_coordinate]
      simp only [map_add (f := _), (D.p_sig _).1, (D.p_sig _).2, id]
      constructor
      · rintro ⟨⟨_, h2⟩, h3, _⟩
        exact ⟨h3, h2⟩
      · rintro ⟨h3, h2⟩
        refine ⟨⟨?_, h2⟩, h3, ?_⟩
        · have e1 : alp v r l ^ 2 * (g : Fv F v)⁻¹ * D.p 0 (c ()) =
              (g : Fv F v) * (alp v r l ^ 2 * ((g : Fv F v)⁻¹) ^ 2 * (D.p 0 (c ()) + D.p 1 (c ()))) -
                alp v r l ^ 2 * (g : Fv F v)⁻¹ * D.p 1 (c ()) := by
            field_simp <;> ring
          rw [e1]
          exact sub_mem (mul_mem hgO h3) h2
        · rwa [add_comm (D.p 1 (c ()))]
    have hu : ∀ _ : Unit, IsUnit (D.pt (alp v r l ^ 2 * ((g : Fv F v)⁻¹) ^ 2) (alp v r l ^ 2 * (g : Fv F v)⁻¹)) :=
      fun _ => D.isUnit_pt (mul_ne_zero ha (pow_ne_zero _ (inv_ne_zero hg0))) (mul_ne_zero ha (inv_ne_zero hg0))
    rw [hset, hsh, BM.box_measure_mul (E := E) v Unit μ _ hu, hm]
    simp only [Finset.univ_unique, Finset.prod_singleton, D.norm_pt]
    rw [absV_mul, absV_mul, absV_mul, absV_pow, absV_pow, absV_inv]
    have hA := absV_pos v (alp_ne_zero v r l)
    have hG := absV_pos v hg0
    field_simp
  · have hlr : alp v r l = 1 := by unfold alp; rw [if_neg hl]
    obtain ⟨k, hk⟩ := hT
    have hk' : ((T : Fv F v) - (T' : Fv F v)) = (g : Fv F v) * (k : Fv F v) := by
      have := congrArg (Int.cast : ℤ → Fv F v) hk
      push_cast at this
      exact this
    have hset : (fun c : Unit → Fv F v ⊗[F] E => c ()) ⁻¹' PPTyp σ v g r T T' l =
        (D.shear id) ⁻¹' ((fun w => w + fun _ : Unit => D.pt ((T : Fv F v) + T') (T : Fv F v)) ⁻¹'
          (Set.univ.pi fun _ : Unit =>
            {c | D.pt (((g : Fv F v)⁻¹) ^ 2) (g : Fv F v)⁻¹ * c ∈ OEv (E := E) v})) := by
      ext c
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_ofPred_eq, PPTyp,
        if_neg hl, unit_forall, Pi.add_apply]
      rw [D.mem_sc_mul, D.mem_sc_mul, D.mem_pt_mul]
      simp only [map_add (f := _), D.shear_first_coordinate, D.shear_second_coordinate, hp0, hp1, map_natCast, (D.p_sig _).1, (D.p_sig _).2, id]
      constructor
      · rintro ⟨⟨_, h2⟩, h3, _⟩
        refine ⟨?_, h2⟩
        have e1 : ((g : Fv F v)⁻¹) ^ 2 * (D.p 0 (c ()) + D.p 1 (c ()) + ((T : Fv F v) + T')) =
            ((g : Fv F v)⁻¹) ^ 2 * (D.p 0 (c ()) + D.p 1 (c ()) + T + T') := by ring
        rw [e1]; exact h3
      · rintro ⟨h3, h2⟩
        have e0 : ((g : Fv F v)⁻¹) ^ 2 * (D.p 0 (c ()) + D.p 1 (c ()) + T + T') =
            ((g : Fv F v)⁻¹) ^ 2 * (D.p 0 (c ()) + D.p 1 (c ()) + ((T : Fv F v) + T')) := by ring
        refine ⟨⟨?_, h2⟩, by rw [e0]; exact h3, ?_⟩
        · have e1 : (g : Fv F v)⁻¹ * (D.p 0 (c ()) + T) =
              (g : Fv F v) * (((g : Fv F v)⁻¹) ^ 2 * (D.p 0 (c ()) + D.p 1 (c ()) + ((T : Fv F v) + T'))) -
                (g : Fv F v)⁻¹ * (D.p 1 (c ()) + T) + (g : Fv F v)⁻¹ * ((T : Fv F v) - T') := by
            field_simp <;> ring
          have e2 : (g : Fv F v)⁻¹ * ((T : Fv F v) - T') = (k : Fv F v) := by
            rw [hk']; field_simp
          rw [e1, e2]
          exact add_mem (sub_mem (mul_mem hgO h3) h2) (intCast_mem _ k)
        · have e2 : ((g : Fv F v)⁻¹) ^ 2 * (D.p 1 (c ()) + D.p 0 (c ()) + T + T') =
              ((g : Fv F v)⁻¹) ^ 2 * (D.p 0 (c ()) + D.p 1 (c ()) + ((T : Fv F v) + T')) := by ring
          rw [e2]; exact h3
    have hu : ∀ _ : Unit, IsUnit (D.pt (((g : Fv F v)⁻¹) ^ 2) (g : Fv F v)⁻¹) :=
      fun _ => D.isUnit_pt (pow_ne_zero _ (inv_ne_zero hg0)) (inv_ne_zero hg0)
    rw [hset, hsh, measure_preimage_add_right, BM.box_measure_mul (E := E) v Unit μ _ hu, hm]
    simp only [Finset.univ_unique, Finset.prod_singleton, D.norm_pt, hlr, absV_one]
    rw [absV_mul, absV_pow, absV_inv]
    have hG := absV_pos v hg0
    field_simp

end PI.UnitaryGroupMassFormula.LocJacTyp
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PpPosTypGen

section

@[expose] public section

noncomputable section

open scoped Classical TensorProduct

namespace Formalism.L2.SG.Pf.ProdConvCut2

open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcVal
  Formalism.L2.SG.Pf.NcVal.VolOrdW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem pp_pos_typ_gen {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (ψ : AddChar (AF X.B.I.F) ℂ)
    (hψ : IsCharAF X.B.I.F ψ) (hs : IsStdChar ψ) (u u' : D.what₂.Word) (v : PlX X) (hv : TypAt X v)
    (l : Fin (D.R.rS + 1)) : 0 < PPX X u u' ψ l v := by
  have hTF := Formalism.L2.SG.Pf.typFacts_holds X hb u u' ⟨v, hv⟩

  have hnt : X.B.I.cm.sig ≠ AlgHom.id X.B.I.F X.B.I.E := by
    have hmax : v.asIdeal.IsMaximal := v.isMaximal
    obtain ⟨P, hPmax, -⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 X.B.I.E) v.asIdeal
      (by
        rw [(RingHom.injective_iff_ker_eq_bot _).mp
          (FaithfulSMul.algebraMap_injective (𝓞 X.B.I.F) (𝓞 X.B.I.E))]
        exact bot_le)
    obtain ⟨θ, t, htθ, hnot⟩ := X.B.I.cm.cmUnram.2.2 P hPmax
    intro h
    apply hnot
    have hθ : (t : X.B.I.E) = θ := by
      have h1 : X.B.I.cm.sig (θ : X.B.I.E) = star (θ : X.B.I.E) := rfl
      rw [h, AlgHom.id_apply] at h1
      have htθ' : (t : X.B.I.E) = star (θ : X.B.I.E) := htθ
      rw [htθ', ← h1]
    have : θ - t = 0 := by ext; simp [hθ]
    rw [this]
    exact P.zero_mem

  have hid : ∃ x : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E, x * x = x ∧ x ≠ 0 ∧ x ≠ 1 := by
    by_contra h
    have he := hTF.2.2.1
    unfold etaV at he
    rw [if_neg h] at he
    exact absurd he (by decide)
  have hS : PI.UnitaryGroupMassFormula.LocJacTyp.SplitHyp X.B.I.cm.sig v := ⟨X.B.I.cm.deg2, hnt, hid⟩
  have hg : 0 < gAt X v := hTF.1.pos
  have hA := SdW.sdFromAnn_holds ψ v (dV v) hψ X.B.I.cm.deg2 (dV_ne_zero v)
    (annX_of X ψ Formalism.L2.SG.Pf.conductor_inverse_different hψ hs v) Unit
  haveI := hA.1
  have hP := PI.UnitaryGroupMassFormula.LocJacTyp.parabolic_volume X.B.I.cm.sig v (gAt X v) D.R.rS (Tw u) (Tw u')
    (absV v (dV v) ^ Fintype.card Unit) hS hg hTF.2.2.2.1 (sdE (E := X.B.I.E) ψ v Unit) hA.1 hA.2.2 l
  have hP' : ((sdE (E := X.B.I.E) ψ v Unit) ((fun c : Unit → Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E => c ()) ⁻¹'
      PPTyp X.B.I.cm.sig v (gAt X v) D.R.rS (Tw u) (Tw u') l)).toReal =
      absV v (dV v) ^ Fintype.card Unit * PI.LocJacTyp.absV v (gAt X v : Fv X.B.I.F v) ^ 3 *
        (PI.LocJacTyp.absV v (PI.LocJacTyp.alp v D.R.rS l) ^ 4)⁻¹ := hP
  unfold PPX volC
  rw [if_pos hv, hP']
  have hd : 0 < absV v (dV v) := absV_pos v (dV_ne_zero v)
  have hgv : (gAt X v : Fv X.B.I.F v) ≠ 0 := by exact_mod_cast hg.ne'
  have h1 : 0 < PI.LocJacTyp.absV v (gAt X v : Fv X.B.I.F v) := PI.UnitaryGroupMassFormula.LocJacTyp.absV_pos v hgv
  have ha : PI.LocJacTyp.alp v D.R.rS l ≠ 0 := alp_ne_zero v D.R.rS l
  have h2 : 0 < PI.LocJacTyp.absV v (PI.LocJacTyp.alp v D.R.rS l) := PI.UnitaryGroupMassFormula.LocJacTyp.absV_pos v ha
  positivity

end Formalism.L2.SG.Pf.ProdConvCut2
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdConvNewHoldsGen

section

@[expose] public section

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ProdConvCut2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol

theorem level_congr_mod_sq (D : D7) (u u' : D.what₂.Word) :
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD Formalism.MainNotions.S.Lat.gS D ^ 2] := by
  have h : Formalism.MainNotions.S.Lat.gS D ^ 2 ∣ D.modT := by unfold Formalism.MainNotions.S.Lat.gS; exact D.gg_dvd_modT
  exact (D.T_modEq_of_dvd u h).trans (D.T_modEq_of_dvd u' h).symm

theorem prodConvNew_holds_gen {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (hψ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF X.B.I.F ψ) (hs : IsStdChar ψ)
    (hloc : ∀ w : D.what₂.Word, LocCompatX X ψ w) (u u' : D.what₂.Word) : ProdConvNew X u u' ψ := by
  have hg : ∀ v, TypAt X v → 0 < gAt X v := fun v hv =>
    (Formalism.L2.SG.Pf.typFacts_holds X hb u u' ⟨v, hv⟩).1.pos
  have hUZ := Formalism.L2.SG.Pf.LocalPositivity.localVolumeUnit_pos_and_ZZX_pos X u u' ψ hψ hs (level_congr_mod_sq D u u') hg
  refine prodConvNew_gen X u u' ψ hb hψ hs hloc fun v => ⟨fun _ => (hUZ v).1, (hUZ v).2, fun l => ?_,
    Formalism.L2.SG.Pf.LocalPositivity.jac_pos X hg v⟩
  by_cases hv : TypAt X v
  · exact pp_pos_typ_gen X hb ψ hψ hs u u' v hv l
  · exact Formalism.L2.SG.Pf.LocalPositivity.pp_pos_ord X u u' ψ hψ hs hv l

end Formalism.L2.SG.Pf.ProdConvCut2
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdConvHoldsGen

section

@[expose] public section

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ProdConvCut2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol

theorem prodConv_holds_gen {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (hψ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF X.B.I.F ψ) (hs : IsStdChar ψ)
    (hloc : ∀ w : D.what₂.Word, LocCompatX X ψ w) (u u' : D.what₂.Word) : ProdConv X u u' ψ :=
  prodConvNew_holds_gen X hb ψ hψ hs hloc u u'

theorem prodConv_holds {D : D7} (T : Formalism.L2.SG.SpectralTiesReal.STies D) (u u' : D.what₂.Word) : ProdConv T.X u u' T.ψ :=
  prodConv_holds_gen T.X T.hb T.ψ T.ψ_char T.ψ_std T.locCompat u u'

theorem prodConvAll_holds : Formalism.L2.SG.PoincareAmplitudeLowerBounds.ProdConvAll :=
  fun _ T u u' _ _ => prodConv_holds T u u'

theorem prodConv_onTied :
    Formalism.L2.SG.NGAnalytic.MassDataLemmas.OnTied fun _ X _ _ u u' _ ψ => ProdConv X u u' ψ := by
  intro Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' _ hb X0 ψ hT
  exact prodConv_holds_gen X hb ψ hT.2.1 hT.2.2.1 hT.2.2.2.2.1 u u'

end Formalism.L2.SG.Pf.ProdConvCut2
end
end
end
