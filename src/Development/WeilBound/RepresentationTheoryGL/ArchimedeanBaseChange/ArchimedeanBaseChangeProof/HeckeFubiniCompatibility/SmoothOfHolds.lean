module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PackOf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.InfinitesimalCharacterGL.BridgeSt
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.ActHcsSlice
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.HasCompactSupportOfSection
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.IntegrableTens
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PCompat
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PFinInvMulInfGL
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PGrowth
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PInfConv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CapelliOfGelfand
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QdetPolyMapMonicStatement
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.InfinitesimalCharacterGL.NatDegreeDefectGelf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.InfinitesimalCharacterGL.PChart
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.CompatFub
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PSmoothB
import GroundTheory.GlobalFields.Adele.Approximation
import Mathlib.Tactic.Linter.Style

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PInfEx

section

@[expose] public section

noncomputable section

open Polynomial Finset NumberField GlobalTheory.CuspRep
open PositivityTheory.RgBcC.Bridge PositivityTheory.Rg.BcB.CG.InfiniteConvergence

namespace PositivityTheory.Rg.BcB.CG

namespace HeckeFubiniEvaluationDefect

theorem eval_sS (t : ℕ → ℂ) (m N : ℕ) : (sS t m N).eval (m : ℂ) = (-1) ^ N * t N := by
  rw [sS, sum_range_succ, eval_add, eval_finsetSum, sum_eq_zero]
  · simp
  · intro k hk
    have := mem_range.mp hk
    simp only [eval_mul, eval_C, eval_pow, eval_sub, eval_X, sub_self]
    rw [zero_pow (by omega), mul_zero]

theorem eq_of_defect (m : ℕ) (t t' : ℕ → ℂ) (Q : ℂ[X]) (hQ : Q.natDegree = m + 1)
    (h : ∀ N, (defect t m N Q).natDegree ≤ m) (h' : ∀ N, (defect t' m N Q).natDegree ≤ m) (k : ℕ) : t k = t' k := by
  have hQ0 : Q ≠ 0 := by intro e; rw [e, natDegree_zero] at hQ; omega
  have hS : sS t m k = sS t' m k := by
    have e : defect t m k Q - defect t' m k Q = Q * (sS t' m k - sS t m k) := by
      simp only [defect_eq]; ring
    by_contra hne
    have hD : sS t' m k - sS t m k ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    have h1 : (Q * (sS t' m k - sS t m k)).natDegree ≤ m := by
      rw [← e]; exact (natDegree_sub_le _ _).trans (max_le (h k) (h' k))
    rw [natDegree_mul hQ0 hD, hQ] at h1
    omega
  have e := congrArg (fun p => p.eval (m : ℂ)) hS
  simp only [eval_sS] at e
  have hu : ((-1 : ℂ) ^ k) ≠ 0 := pow_ne_zero _ (by norm_num)
  exact mul_left_cancel₀ hu e

theorem exists_enum (s : Multiset ℂ) : ∀ n, Multiset.card s = n → ∃ r : Fin n → ℂ, Multiset.map r univ.val = s := by
  induction s using Multiset.induction_on with
  | empty =>
    intro n hn
    simp only [Multiset.card_zero] at hn
    subst hn
    exact ⟨Fin.elim0, by simp⟩
  | cons a s ih =>
    intro n hn
    rw [Multiset.card_cons] at hn
    subst hn
    obtain ⟨r, hr⟩ := ih _ rfl
    refine ⟨Fin.cons a r, ?_⟩
    conv_rhs => rw [← hr]
    simp [Fin.univ_succ, Multiset.map_map, Function.comp_def]

theorem exists_gelf (V : Type) [AddCommGroup V] [Module ℂ V] (m : ℕ) (M : Fin (m + 1) → Fin (m + 1) → Module.End ℂ V)
    (hM : Formalism.REAL.GlRel M) (v : V) (hv : v ≠ 0) (t : ℕ → ℂ) (ht : ∀ k, Formalism.REAL.etr M k v = t k • v) :
    ∃ χ : Fin (m + 1) → ℂ, ∀ k, GlobalTheory.Dec.gelfVal χ k = t k := by
  obtain ⟨f₀, hf₀⟩ : ∃ f : Module.Dual ℂ V, f v ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hv ((Module.forall_dual_apply_eq_zero_iff ℂ v).mp hc)
  set f : Module.Dual ℂ V := (f₀ v)⁻¹ • f₀ with hfd
  have hf : f v = 1 := by
    rw [hfd, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hf₀]
  obtain ⟨c, hc1, hc⟩ := GlobalTheory.T.exists_monic_poly_eq_qdet (Module.End ℂ V) (m + 1) M
  set Q := GlobalTheory.CapelliNewton.polyOf (m + 1) c f v with hQd
  have hQ : ∀ u : ℂ, Q.eval u = f (Formalism.REAL.qdet M u v) := fun u => by
    rw [hQd, GlobalTheory.CapelliNewton.polyOf_eval, hc]
  have hQc : Q.coeff (m + 1) = 1 := by
    rw [hQd, GlobalTheory.CapelliNewton.polyOf_coeff, hc1]
    exact hf
  have hQn : Q.natDegree = m + 1 :=
    le_antisymm (GlobalTheory.CapelliNewton.polyOf_natDegree _ _ _ _)
      (le_natDegree_of_ne_zero (by rw [hQc]; exact one_ne_zero))
  have hQm : Q.Monic := by
    rw [Monic, leadingCoeff, hQn, hQc]
  have hcard : Multiset.card Q.roots = m + 1 := by
    rw [IsAlgClosed.card_roots_eq_natDegree, hQn]
  have hprod : (Q.roots.map fun a => X - Polynomial.C a).prod = Q :=
    prod_multiset_X_sub_C_of_monic_of_roots_card_eq hQm (by rw [hcard, hQn])
  obtain ⟨r, hr⟩ := exists_enum Q.roots (m + 1) hcard
  refine ⟨fun s => (m : ℂ) / 2 - r s, fun k => ?_⟩
  have hcq : (∏ s, (X + Polynomial.C ((m : ℂ) / 2 - r s - (m : ℂ) / 2))) = Q := by
    conv_rhs => rw [← hprod, ← hr]
    rw [Multiset.map_map, Finset.prod_eq_multiset_prod]
    congr 1
    refine Multiset.map_congr rfl fun s _ => ?_
    simp only [Function.comp_apply, map_sub]
    ring
  have h1 : ∀ N, (defect (GlobalTheory.Dec.gelfVal fun s => (m : ℂ) / 2 - r s) m N Q).natDegree ≤ m := by
    intro N
    have := natDegree_defect_gelf m (fun s => (m : ℂ) / 2 - r s) N
    rwa [hcq] at this
  have h2 : ∀ N, (defect t m N Q).natDegree ≤ m := fun N =>
    natDegree_defect_op V m M hM v t ht f Q hQ N
  exact eq_of_defect m _ t Q hQn h1 h2 k

theorem one_mem_GLs' {a : ℕ} : (1 : Matrix (Fin a) (Fin a) ℂ) ∈ PositivityTheory.RgBcC.GLs a := by
  simp [PositivityTheory.RgBcC.GLs]

end HeckeFubiniEvaluationDefect

open HeckeFubiniEvaluationDefect in
theorem infEx : InfEx := by
  intro E _ _ _ n S v t ⟨φ, hφS, hφ0⟩ h
  have hs : ∀ s k, Formalism.REAL.etr (eopW v s) k φ = t s k • φ := by
    intro s k
    apply Subtype.ext
    funext g
    have h1 := h φ hφS g s k 1 one_mem_GLs'
    rw [gel_along v g s k φ one_mem_GLs', along_one, along_one] at h1
    rw [Submodule.coe_smul, Pi.smul_apply]
    exact h1
  rcases n with _ | m
  · refine ⟨fun _ => Fin.elim0, fun s k => ?_⟩
    have ht0 : t s k = 0 := by
      have e : t s k • φ = 0 := by rw [← hs s k]; simp [Formalism.REAL.etr]
      exact (smul_eq_zero.mp e).resolve_right hφ0
    rw [ht0]
    simp [GlobalTheory.Dec.gelfVal]
  · have hgl : ∀ s, Formalism.REAL.GlRel (eopW (E := E) (a := m + 1) v s) := by
      intro s
      unfold eopW
      split <;> exact glRel_Eop _
    choose χ hχ using fun s => exists_gelf (Sm E (m + 1)) m (eopW v s) (hgl s) φ hφ0 (t s) (hs s)
    exact ⟨χ, fun s k => hχ s k⟩

end PositivityTheory.Rg.BcB.CG

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PSmooth

section

@[expose] public section

noncomputable section

open NumberField MeasureTheory Matrix
open GlobalTheory.CuspRep PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf finH)
open scoped ContDiff Classical

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

namespace PositivityTheory.Rg.BcB.CG

namespace SmoothIntegrals

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def entL (M : KMod n) (i j : Ix M) : (M.V →L[ℂ] M.V) →L[ℝ] ℂ :=
  ((innerSL ℂ (stdOrthonormalBasis ℂ M.V i)).comp
    (ContinuousLinearMap.apply ℂ M.V (stdOrthonormalBasis ℂ M.V j))).restrictScalars ℝ

theorem mult_contDiffOn [MeasurableSpace (G n)] {μ : Measure (G n)} {M : KMod n} {k : Mat n → (M.V →L[ℂ] M.V)}
    {val : Inf n → ℂ} {T : ℝ} (h : IsMult μ M k val T) : ContDiffOn ℝ ∞ k (GLs n) := by
  obtain ⟨m, c, w, g, ks, hks, hk, -⟩ := h
  exact (ContDiffOn.sum fun i _ => ((hks i).2.1).const_smul (c i)).congr fun y hy => hk y hy

theorem ent_contDiffOn [MeasurableSpace (G n)] {μ : Measure (G n)} {M : KMod n} {k : Mat n → (M.V →L[ℂ] M.V)}
    {val : Inf n → ℂ} {T : ℝ} (h : IsMult μ M k val T) (i j : Ix M) :
    ContDiffOn ℝ ∞ (fun A => ent M (k A) i j) (GLs n) :=
  (entL M i j).contDiff.comp_contDiffOn (mult_contDiffOn h)

theorem continuous_entA [MeasurableSpace (G n)] {μ : Measure (G n)} {M : Mods E n} {k : Kers M}
    {val : InfinitePlace E → Inf n → ℂ} {T : ℝ} (h : IsMults μ k val T) (I J : IxA M) :
    Continuous fun g : GA E n => entA k I J g :=
  continuous_finsetProd _ fun v _ => (entL (M v) (I v) (J v)).continuous.comp
    ((mult_contDiffOn (h v)).continuousOn.comp_continuous (Units.continuous_val.comp (continuous_gI v))
      fun _ => val_mem_GLs₀ _)

omit [IsCMField E] in
theorem continuous_gFin₀ : Continuous (gFin : GA E n → GL (Fin n) (Af E)) :=
  Continuous.units_map _ (continuous_id.matrix_map continuous_snd)

theorem continuous_hFin₀ {a b : ℕ} : Continuous (hFin : H E a b → Hf E a b) :=
  (continuous_gFin₀.comp continuous_fst).prodMk (continuous_gFin₀.comp continuous_snd)

theorem gFin_infGL₀ (u : GL (Fin n) (Cinf E)) : gFin (infGL E n u) = 1 := pFin_infGL u

end SmoothIntegrals


open SmoothIntegrals in
theorem smoothOf (hTT : TensTest) : SmoothOf := by
  set_option synthInstance.maxHeartbeats 200000 in
    intro E _ _ _ a b _ _ _ _ μa _ μb _ Ma Mb ι _ D ka kb va vb T ψ U f hka hkb hψ _ _ hR
    have : BorelSpace (H E a b) := ⟨rfl⟩
    have : D.μ.IsMulLeftInvariant := D.haar.1
    have : IsLocallyFiniteMeasure D.μ := D.haar.2.2.2
    have : IsFiniteMeasureOnCompacts D.μ := isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure
    obtain ⟨hfc, c, hc, hconv⟩ := hR
    have hTest := (hTT E a b μa μb Ma Mb ι ka kb va vb T ψ hka hkb hψ).1
    have hψc : ∀ x y, Continuous fun w : H E a b => ψ x y (hFin w) := fun x y => (hψ x y).1.comp continuous_hFin₀

    have hrep : ∀ i z, f i z = c⁻¹ * ∑ j, ∫ y, tens ka kb ψ i j y * f j (z * y) ∂D.μ := by
      intro i z
      have h1 := congrFun (congrFun hconv i) z
      have h2 : c * f i z = ∑ j, ∫ y, tens ka kb ψ i j y * f j (z * y) ∂D.μ := h1.symm
      rw [← h2, inv_mul_cancel_left₀ hc]
    refine ⟨fun i m₂ => ?_, fun i m₁ => ?_⟩
    · have hj : ∀ j, (fun x => ∫ y, tens ka kb ψ i j y * f j ((x, m₂) * y) ∂D.μ) ∈ Sm E a := by
        intro j
        have h := mem_Sm_conv D.μ (MonoidHom.inl (GA E a) (GA E b)) (continuous_id.prodMk continuous_const) Prod.fst
          continuous_fst (fun h w => by simp) (fun v A => ent (Ma v) (ka v A) (i.1.1 v) (j.1.1 v))
          (fun v => ent_contDiffOn (hka v) _ _) (fun w => entA kb i.1.2 j.1.2 w.2 * ψ i.2 j.2 (hFin w))
          (((continuous_entA hkb _ _).comp continuous_snd).mul (hψc _ _))
          (fun _ w => by simp [hFin, gFin_infGL₀]) (f j) (hfc j) (tens ka kb ψ i j) (fun w => mul_assoc _ _ _)
          (hTest i j).2 ((1 : GA E a), m₂)
        have e : ∀ x : GA E a, ((1 : GA E a), m₂) * MonoidHom.inl (GA E a) (GA E b) x = (x, m₂) := fun x =>
          Prod.ext (one_mul x) (mul_one m₂)
        simpa only [e] using h
      refine ⟨⟨c⁻¹ • ∑ j, fun x => ∫ y, tens ka kb ψ i j y * f j ((x, m₂) * y) ∂D.μ,
        (Sm E a).smul_mem c⁻¹ ((Sm E a).sum_mem fun j _ => hj j)⟩, ?_⟩
      funext x
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact (hrep i (x, m₂)).symm
    · have hj : ∀ j, (fun x => ∫ y, tens ka kb ψ i j y * f j ((m₁, x) * y) ∂D.μ) ∈ Sm E b := by
        intro j
        have h := mem_Sm_conv D.μ (MonoidHom.inr (GA E a) (GA E b)) (continuous_const.prodMk continuous_id) Prod.snd
          continuous_snd (fun h w => by simp) (fun v A => ent (Mb v) (kb v A) (i.1.2 v) (j.1.2 v))
          (fun v => ent_contDiffOn (hkb v) _ _) (fun w => entA ka i.1.1 j.1.1 w.1 * ψ i.2 j.2 (hFin w))
          (((continuous_entA hka _ _).comp continuous_fst).mul (hψc _ _))
          (fun _ w => by simp [hFin, gFin_infGL₀]) (f j) (hfc j) (tens ka kb ψ i j)
          (fun w => by
            show entA ka _ _ w.1 * entA kb _ _ w.2 * ψ _ _ (hFin w) = entA kb _ _ w.2 * (entA ka _ _ w.1 * ψ _ _ (hFin w))
            ring)
          (hTest i j).2 (m₁, (1 : GA E b))
        have e : ∀ x : GA E b, (m₁, (1 : GA E b)) * MonoidHom.inr (GA E a) (GA E b) x = (m₁, x) := fun x =>
          Prod.ext (mul_one m₁) (one_mul x)
        simpa only [e] using h
      refine ⟨⟨c⁻¹ • ∑ j, fun x => ∫ y, tens ka kb ψ i j y * f j ((m₁, x) * y) ∂D.μ,
        (Sm E b).smul_mem c⁻¹ ((Sm E b).sum_mem fun j _ => hj j)⟩, ?_⟩
      funext x
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact (hrep i (m₁, x)).symm

end PositivityTheory.Rg.BcB.CG

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.SmoothOfHolds

section

@[expose] public section

open PositivityTheory.RgBcC

namespace PositivityTheory.Rg.BcB.CG

theorem smoothOf_holds : SmoothOf := smoothOf tensTest

theorem actVal_of (h : MultAlg) : ActVal := actVal h compatFub tensTest

theorem pack_of_gel (hS : SizeBasic) (hB : Bridge.BridgeSt) (hG : GelOf) : Pack :=
  pack_of tensTest typeOf smoothOf_holds (growthOf hS) hG infEx (PAut.autOf hB)

end PositivityTheory.Rg.BcB.CG
end
end
