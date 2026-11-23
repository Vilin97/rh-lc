module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyInst
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BesselFrame
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.HaarSubS
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ProductExactness
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.FolnerS2
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BesselLevi
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyAbs
import Mathlib.Tactic.Linter.HaveILetI
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BesselLevi
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.KoszulLowersPower
import Mathlib.Topology.Algebra.Group.Units
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.HaarSubSAsm
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.HaarSubSD
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.HaarSubSH

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.FolnerG2

section

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal Pointwise

namespace Formalism.L2.S.Pv.FolnerG

open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.SW PI.QuotSetU.UnitaryGroupMassFormula.ModW PI.QuotSetU.UnitaryGroupMassFormula.ModW.MG
  Formalism.L2.S.Pv.FolnerAbs Formalism.L2.SG.Pf.EnergyAbs Formalism.L2.S.Pv.FolnerS

variable {k r : ℕ} {ι : Type} [Fintype ι] (z : ι → Fin (2 * r + k + 1) → ℂ)

def SP : Set (ι → GH k r) := {s | ∀ v, s v ∈ Sg k r (z v)}

def CP : Set (ι → GH k r) := {s | ∀ v, s v ∈ Cg k r (z v)}

def fP (s : ι → GH k r) : ℝ := ∑ v, fG k r (z v) (s v)

variable {z}

theorem fG_nonneg (z0 : Fin (2 * r + k + 1) → ℂ) (g : GH k r) : 0 ≤ fG k r z0 g := by
  unfold fG
  refine Real.sInf_nonneg ?_
  rintro _ ⟨c, -, rfl⟩
  unfold nrm; positivity

theorem cjB_pi (b s : ι → GH k r) (v : ι) : cjB b s v = cjB (b v) (s v) := rfl

theorem isFolner_pi (hz : ∀ v, inWb k r (z v)) (hT : ∀ v, 0 < Tz k r (z v)) (μS : Measure (ι → GH k r))
    (hμ : IsHaarSub (SP z) μS) : IsFolner (SP z) μS := by
  have hCc : IsCompact (CP z) := by
    have : CP z = Set.pi Set.univ (fun v => Cg k r (z v)) := by ext s; simp [CP, Set.mem_pi]
    rw [this]; exact isCompact_univ_pi fun v => isCompact_Cg (hz v) (hT v)
  refine isFolner_of_contract hμ (CP z) (fP z) ?_ ?_ ?_ (fun _ => aT k r) ?_ ?_
  · exact continuous_finsetSum _ fun v _ => (continuous_fG (hz v) (hT v)).comp (continuous_apply v)
  · intro c hc x
    unfold fP
    exact Finset.sum_congr rfl fun v _ => fG_mul_left (hc v) (x v)
  · intro ρ
    have hsub : {x | fP z x ≤ ρ} ∩ SP z ⊆ Set.pi Set.univ (fun v => {y | fG k r (z v) y ≤ ρ} ∩ Sg k r (z v)) := by
      rintro s ⟨hs, hsS⟩ v -
      refine ⟨?_, hsS v⟩
      show fG k r (z v) (s v) ≤ ρ
      refine le_trans ?_ hs
      exact Finset.single_le_sum (f := fun w => fG k r (z w) (s w)) (fun w _ => fG_nonneg _ _) (Finset.mem_univ v)
    refine (isCompact_univ_pi fun v => isCompact_sublevel (hz v) (hT v) ρ).of_isClosed_subset ?_ hsub
    refine (isClosed_le (continuous_finsetSum _ fun v _ => (continuous_fG (hz v) (hT v)).comp (continuous_apply v))
      continuous_const).inter ?_
    have : SP z = ⋂ v, (fun s : ι → GH k r => s v) ⁻¹' Sg k r (z v) := by ext s; simp [SP]
    rw [this]
    exact isClosed_iInter fun v => (isClosed_Sg (hz v) (hT v)).preimage (continuous_apply v)
  · intro s
    show (∀ v, s v ∈ Sg k r (z v)) ↔ ∀ v, cjB (fun _ => aT k r) s v ∈ Sg k r (z v)
    exact forall_congr' fun v => by rw [cjB_pi]; exact aT_iff (z v) (s v)
  · intro K hK hKS U hU hCU
    obtain ⟨V, hV, hCV⟩ := compact_open_separated_mul_right hCc hU hCU
    rw [nhds_pi, Filter.mem_pi'] at hV
    obtain ⟨I, t, ht, hIt⟩ := hV
    have hev : ∀ v, ∀ᶠ m : ℕ in atTop, ∀ x ∈ (fun s : ι → GH k r => s v) '' K,
        cjB (aT k r ^ m) x ∈ Cg k r (z v) * t v := fun v =>
      contractV (hz v) (hT v) _ (hK.image (continuous_apply v)) (by rintro _ ⟨s, hs, rfl⟩; exact hKS hs v) (t v) (ht v)
    filter_upwards [Filter.eventually_all.2 hev] with m hm x hx
    have hx' : ∀ v, cjB (aT k r ^ m) (x v) ∈ Cg k r (z v) * t v := fun v => hm v (x v) ⟨x, hx, rfl⟩
    choose c hc w hw hcw using hx'
    refine hCV ⟨c, hc, w, hIt (fun v _ => hw v), ?_⟩
    funext v
    show c v * w v = cjB ((fun _ => aT k r) ^ m) x v
    rw [cjB_pi, Pi.pow_apply]
    exact hcw v

end Formalism.L2.S.Pv.FolnerG
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.IsFolnerOfEquiv

section

@[expose] public section

set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Measure Filter Topology
open scoped ENNReal

namespace Formalism.L2.S.Pv.FolnerT

open Formalism.L2.SG.Pf.EnergyAbs

variable {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] [SecondCountableTopology H]
  [MeasurableSpace H] [BorelSpace H]

theorem isHaarSub_comap (Φ : G ≃* H) (hΦ : Continuous Φ) (hΦ' : Continuous Φ.symm) {S : Set H} {μ : Measure H}
    (hμ : IsHaarSub S μ) : IsHaarSub (Φ ⁻¹' S) (μ.map Φ.symm) := by
  obtain ⟨hC, h1, hm, hi, hσ, h0, hc, hl, hK, hr, hinv⟩ := hμ
  have hs : Measurable Φ.symm := hΦ'.measurable
  let E : G ≃ₜ H := { Φ.toEquiv with continuous_toFun := hΦ, continuous_invFun := hΦ' }
  let M : G ≃ᵐ H := E.toMeasurableEquiv
  have hmap : ∀ A : Set G, (μ.map Φ.symm) A = μ (Φ.symm ⁻¹' A) := fun A => by
    exact MeasurableEquiv.map_apply M.symm A
  refine ⟨hC.preimage hΦ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show Φ 1 ∈ S
    rw [map_one]
    exact h1
  · intro a ha b hb
    show Φ (a * b) ∈ S
    rw [map_mul]
    exact hm _ ha _ hb
  · intro a ha
    show Φ a⁻¹ ∈ S
    rw [map_inv]
    exact hi _ ha
  · haveI := hσ
    show SigmaFinite (μ.map M.symm)
    first
      | exact M.symm.sigmaFinite_map
      | exact MeasurableEquiv.sigmaFinite_map M.symm
      | (refine SigmaFinite.of_map _ M.measurable.aemeasurable ?_
         rw [Measure.map_map M.measurable M.symm.measurable, M.self_comp_symm, Measure.map_id]
         exact hσ)
  · intro h
    exact h0 ((Measure.map_eq_zero_iff hs.aemeasurable).1 h)
  · rw [hmap]
    convert hc using 2
    ext x
    simp
  · intro s hsS
    rw [Measure.map_map (continuous_const_mul s).measurable hs]
    have e1 : (fun x => s * x) ∘ ⇑Φ.symm = ⇑Φ.symm ∘ (fun y => Φ s * y) := by
      funext y
      simp
    rw [e1, ← Measure.map_map hs (continuous_const_mul (Φ s)).measurable, hl _ hsS]
  · intro K hKc
    rw [hmap]
    exact hK _ ((E.symm.isCompact_preimage).2 hKc)
  · intro s hsS
    rw [Measure.map_map (continuous_mul_const s).measurable hs]
    have e1 : (fun x => x * s) ∘ ⇑Φ.symm = ⇑Φ.symm ∘ (fun y => y * Φ s) := by
      funext y
      simp
    rw [e1, ← Measure.map_map hs (continuous_mul_const (Φ s)).measurable, hr _ hsS]
  · rw [Measure.map_map continuous_inv.measurable hs]
    have e1 : (fun x : G => x⁻¹) ∘ ⇑Φ.symm = ⇑Φ.symm ∘ (fun y => y⁻¹) := by
      funext y
      simp
    rw [e1, ← Measure.map_map hs continuous_inv.measurable, hinv]

theorem isFolner_of_equiv (Φ : G ≃* H) (hΦ : Continuous Φ) (hΦ' : Continuous Φ.symm) {S : Set H} {μ : Measure H}
    (hμ : IsHaarSub S μ) (hF : IsFolner (Φ ⁻¹' S) (μ.map Φ.symm)) : IsFolner S μ := by
  have hs : Measurable Φ.symm := hΦ'.measurable
  let E : G ≃ₜ H := { Φ.toEquiv with continuous_toFun := hΦ, continuous_invFun := hΦ' }
  let M : G ≃ᵐ H := E.toMeasurableEquiv
  have hmap : ∀ A : Set G, (μ.map Φ.symm) A = μ (Φ.symm ⁻¹' A) := fun A => by
    exact MeasurableEquiv.map_apply M.symm A
  intro K hK hKS ε hε
  obtain ⟨Ω, hΩm, hΩS, hpos, hfin, hle⟩ :=
    hF (Φ ⁻¹' K) ((E.isCompact_preimage).2 hK) (Set.preimage_mono hKS) ε hε
  refine ⟨Φ.symm ⁻¹' Ω, hs hΩm, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have := hΩS hx
    simpa using this
  · rw [← hmap]
    exact hpos
  · rw [← hmap]
    exact hfin
  · have hset : {t | t ∈ ⇑Φ.symm ⁻¹' Ω ∧ ∀ k ∈ K, k * t ∈ ⇑Φ.symm ⁻¹' Ω} =
        ⇑Φ.symm ⁻¹' {t | t ∈ Ω ∧ ∀ k ∈ ⇑Φ ⁻¹' K, k * t ∈ Ω} := by
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_preimage, map_mul]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h1, fun k hk => ?_⟩
        have := h2 (Φ k) hk
        rwa [MulEquiv.symm_apply_apply] at this
      · rintro ⟨h1, h2⟩
        refine ⟨h1, fun k hk => ?_⟩
        exact h2 (Φ.symm k) (by simpa using hk)
    rw [hset, ← hmap, ← hmap]
    exact hle

end Formalism.L2.S.Pv.FolnerT
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.FolnerJ2

section

@[expose] public section

noncomputable section

open MeasureTheory Topology Matrix
open scoped ENNReal

namespace Formalism.L2.S.Pv.FolnerJ

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.WFL Formalism.L2.SG.Pf.EnergyAbs Formalism.L2.S.Pv.FolnerS Formalism.L2.S.Pv.FolnerG
  Formalism.L2.S.Pv.FolnerT PI.QuotSetU.UnitaryGroupMassFormula.ModW PI.QuotSetU.UnitaryGroupMassFormula.ModW.MG

open Formalism.MainNotions.S (uMat)

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {e f : Fin r → Fin (2 * r + k + 1) → ℂ}
  {wf : Fin k → Fin (2 * r + k + 1) → ℂ} {z0 : Fin (2 * r + k + 1) → ℂ}

theorem uMat_ext {a b : Formalism.REAL.UJ ε} (h : uMat a = uMat b) : a = b :=
  Subtype.ext (Units.ext h)

theorem continuous_uMat : Continuous (uMat : Formalism.REAL.UJ ε → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :=
  Units.continuous_val.comp continuous_subtype_val

def ofM (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    GH k r :=
  mk (PI.QuotSetU.UnitaryGroupMassFormula.unitary_hermitian_group k r) g hg

theorem toM_ofM (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    (ofM g hg).toM = g := toM_mk g hg

def psiF (hF : IsFrameJ ε e f wf z0) : GH k r ≃* Formalism.REAL.UJ ε where
  toFun g := toUJ (Qm e f wf z0 * g.toM * Qi ε e f wf z0) (conjQ_UJ hF g.toM_mem)
  invFun s := ofM (Qi ε e f wf z0 * uMat s * Qm e f wf z0) (conj_mem_UH hF (uMat_mem s))
  left_inv g := by
    apply toM_injective
    rw [toM_ofM, uMat_toUJ]
    exact Qi_Qm_conj hF _
  right_inv s := by
    apply uMat_ext
    rw [uMat_toUJ, toM_ofM]
    simp only [← Matrix.mul_assoc, Qm_mul_Qi hF, Matrix.one_mul]
    rw [Matrix.mul_assoc, Qm_mul_Qi hF, Matrix.mul_one]
  map_mul' g h := by
    apply uMat_ext
    rw [uMat_mul, uMat_toUJ, uMat_toUJ, uMat_toUJ, toM_mul]
    calc Qm e f wf z0 * (g.toM * h.toM) * Qi ε e f wf z0
        = Qm e f wf z0 * g.toM * (Qi ε e f wf z0 * Qm e f wf z0) * h.toM * Qi ε e f wf z0 := by
          rw [Qi_mul_Qm hF, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]

theorem continuous_psiF (hF : IsFrameJ ε e f wf z0) : Continuous (psiF hF) := by
  rw [(Formalism.REAL.isClosedEmbeddingMatrix _ ε).1.isEmbedding.continuous_iff]
  show Continuous (fun g : GH k r => Qm e f wf z0 * g.toM * Qi ε e f wf z0)
  exact (continuous_const.matrix_mul continuous_toM).matrix_mul continuous_const

theorem continuous_psiF_symm (hF : IsFrameJ ε e f wf z0) : Continuous (psiF hF).symm := by
  rw [continuous_iff_toM]
  have e1 : (fun s : Formalism.REAL.UJ ε => ((psiF hF).symm s).toM) = fun s => Qi ε e f wf z0 * uMat s * Qm e f wf z0 := by
    funext s; exact toM_ofM _ (conj_mem_UH hF (uMat_mem s))
  rw [e1]
  exact (continuous_const.matrix_mul continuous_uMat).matrix_mul continuous_const

theorem inS_psiF_iff {T : ℝ} {z : Fin (2 * r + k + 1) → ℂ} (hF : IsFrameJ ε e f wf (z0v T z)) (hT : 0 < T) (g : GH k r) :
    InS e z (uMat (psiF hF g)) ↔ g.toM ∈ Formalism.QuantumDeterminants.Sset k r (zBv k r T) := by
  have hz := Qm_zB (e := e) (f := f) (wf := wf) hT z
  have key : psiF hF g ∈ HNset ε e f wf (z0v T z) (zBv k r T) ↔ g.toM ∈ Formalism.QuantumDeterminants.Sset k r (zBv k r T) := by
    show Qi ε e f wf (z0v T z) * uMat (psiF hF g) * Qm e f wf (z0v T z) ∈ Formalism.QuantumDeterminants.Sset k r (zBv k r T) ↔ _
    show Qi ε e f wf (z0v T z) * (Qm e f wf (z0v T z) * g.toM * Qi ε e f wf (z0v T z)) * Qm e f wf (z0v T z) ∈ _ ↔ _
    rw [Qi_Qm_conj hF]
  rw [← key]
  constructor
  · intro hs
    exact HNset_of_inS (fun k r T hT s hs h1 h2 => bessel_levi_formula k r T hT s hs h1 h2) hF hT hz hs
  · intro hs
    exact inS_of_HNset hF hz (inWb_zB T) ⟨_, rfl⟩ hs

theorem isFolner_Sinf {ι : Type} [Fintype ι] {εv : ι → Fin (2 * r + k + 1) → Bool}
    (ev fv : ι → Fin r → Fin (2 * r + k + 1) → ℂ) (wv : ι → Fin k → Fin (2 * r + k + 1) → ℂ)
    (zv : ι → Fin (2 * r + k + 1) → ℂ) (T : ι → ℝ) (hT : ∀ v, 0 < T v)
    (hF : ∀ v, IsFrameJ (εv v) (ev v) (fv v) (wv v) (z0v (T v) (zv v)))
    (μS : Measure (∀ v, Formalism.REAL.UJ (εv v)))
    (hμ : IsHaarSub {s : ∀ v, Formalism.REAL.UJ (εv v) | ∀ v, InS (ev v) (zv v) (uMat (s v))} μS) :
    IsFolner {s : ∀ v, Formalism.REAL.UJ (εv v) | ∀ v, InS (ev v) (zv v) (uMat (s v))} μS := by
  let Φ : (ι → GH k r) ≃* (∀ v, Formalism.REAL.UJ (εv v)) := MulEquiv.piCongrRight fun v => psiF (hF v)
  have hΦ : Continuous Φ := continuous_pi fun v => (continuous_psiF (hF v)).comp (continuous_apply v)
  have hΦ' : Continuous Φ.symm := continuous_pi fun v => (continuous_psiF_symm (hF v)).comp (continuous_apply v)
  have hset : Φ ⁻¹' {s : ∀ v, Formalism.REAL.UJ (εv v) | ∀ v, InS (ev v) (zv v) (uMat (s v))} =
      SP (fun v => zBv k r (T v)) := by
    ext x
    show (∀ v, InS (ev v) (zv v) (uMat (psiF (hF v) (x v)))) ↔ ∀ v, (x v).toM ∈ PI.QuotSetU.Sset k r (zBv k r (T v))
    exact forall_congr' fun v => inS_psiF_iff (hF v) (hT v) (x v)
  refine isFolner_of_equiv Φ hΦ hΦ' hμ ?_
  have hμ' := isHaarSub_comap Φ hΦ hΦ' hμ
  rw [hset] at hμ' ⊢
  exact isFolner_pi (z := fun v => zBv k r (T v)) (fun v => inWb_zB (T v))
    (fun v => by show 0 < Formalism.QuantumDeterminants.Tz k r (zBv k r (T v)); rw [Tz_zB (hT v).le]; exact hT v) _ hμ'

end Formalism.L2.S.Pv.FolnerJ
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.HaarSubSF

section

@[expose] public section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Matrix

namespace Formalism.L2.S.Pv.HaarSubS

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.EnergyAbs Formalism.L2.SG.RealObj.InfCut Formalism.L2.SG.Pf.WFL

theorem isFolner_Sinf_gen {n r k : ℕ} (hn : n = 2 * r + k + 1) {ι : Type} [Fintype ι] {εv : ι → Fin n → Bool}
    (ev fv : ι → Fin r → Fin n → ℂ) (wv : ι → Fin k → Fin n → ℂ) (zv : ι → Fin n → ℂ) (T : ι → ℝ)
    (hT : ∀ v, 0 < T v)
    (hee : ∀ v a b, hJ (εv v) (ev v a) (ev v b) = 0) (hff : ∀ v a b, hJ (εv v) (fv v a) (fv v b) = 0)
    (hef : ∀ v a b, hJ (εv v) (ev v a) (fv v b) = if a = b then 1 else 0)
    (hez : ∀ v a, hJ (εv v) (ev v a) (z0v (T v) (zv v)) = 0)
    (hfz : ∀ v a, hJ (εv v) (fv v a) (z0v (T v) (zv v)) = 0)
    (hzz : ∀ v, hJ (εv v) (z0v (T v) (zv v)) (z0v (T v) (zv v)) = -1)
    (hww : ∀ v a b, hJ (εv v) (wv v a) (wv v b) = if a = b then 1 else 0)
    (hew : ∀ v c a, hJ (εv v) (ev v c) (wv v a) = 0) (hfw : ∀ v c a, hJ (εv v) (fv v c) (wv v a) = 0)
    (hzw : ∀ v a, hJ (εv v) (z0v (T v) (zv v)) (wv v a) = 0)
    (μS : Measure (∀ v, Formalism.REAL.UJ (εv v)))
    (hμ : IsHaarSub {s : ∀ v, Formalism.REAL.UJ (εv v) | ∀ v, InS (ev v) (zv v) (uMat (s v))} μS) :
    IsFolner {s : ∀ v, Formalism.REAL.UJ (εv v) | ∀ v, InS (ev v) (zv v) (uMat (s v))} μS := by
  subst hn
  exact Formalism.L2.S.Pv.FolnerJ.isFolner_Sinf ev fv wv zv T hT
    (fun v => ⟨hee v, hff v, hef v, hez v, hfz v, hzz v, hww v, hew v, hfw v, hzw v⟩) μS hμ

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hermitian_scaled_right {n : ℕ} (ε : Fin n → Bool) (T : ℝ) (x z : Fin n → ℂ) :
    hJ ε x (z0v T z) = (((Real.sqrt T)⁻¹ : ℝ) : ℂ) * hJ ε x z := by
  unfold z0v hJ
  simp [Matrix.mulVec_smul, dotProduct_smul]

theorem hermitian_scaled_left {n : ℕ} (ε : Fin n → Bool) (T : ℝ) (x z : Fin n → ℂ) :
    hJ ε (z0v T z) x = (((Real.sqrt T)⁻¹ : ℝ) : ℂ) * hJ ε z x := by
  unfold z0v hJ
  simp [Matrix.mulVec_smul, smul_dotProduct, star_smul]

theorem folner_of_haar {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word)
    (hμ : IsHaarSub (X.SinfU u) (Formalism.L2.SG.RealObj.muS X u)) :
    IsFolner (X.SinfU u) (Formalism.L2.SG.RealObj.muS X u) := by
  have hn : X.B.I.n = 2 * D.R.rS + D.R.k + 1 := X.n_eq.trans (dimS_eq D.R).symm
  have hT : 0 < Tw (D := D) u := ProductExactness.Tw_pos u
  have hk : 0 < D.R.k := by have := D.R.m_add_three_le_k; omega
  refine isFolner_Sinf_gen hn (fun v a => rv X.B.I v (X.eR a)) (fun v a => rv X.B.I v (X.fR a))
    (fun v => X.wfr u v) (fun v => rv X.B.I v (X.zR u)) (fun _ => Tw u) (fun _ => hT) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (Formalism.L2.SG.RealObj.muS X u) hμ
  · intro v a b
    exact (ProductExactness.hJ_X X v _ _).trans (by rw [X.ee]; simp)
  · intro v a b
    exact (ProductExactness.hJ_X X v _ _).trans (by rw [X.ff]; simp)
  · intro v a b
    exact (ProductExactness.hJ_X X v _ _).trans (by rw [X.ef]; split_ifs <;> simp)
  · intro v a
    rw [hermitian_scaled_right]
    have : hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) = 0 :=
      (ProductExactness.hJ_X X v _ _).trans (by rw [(X.zu_orth u a).1]; simp)
    rw [this, mul_zero]
  · intro v a
    rw [hermitian_scaled_right]
    have : hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) (rv X.B.I v (X.zR u)) = 0 :=
      (ProductExactness.hJ_X X v _ _).trans (by rw [(X.zu_orth u a).2]; simp)
    rw [this, mul_zero]
  · intro v
    rw [hermitian_scaled_right, hermitian_scaled_left]
    have h5 : hJ (X.B.I.ε v) (rv X.B.I v (X.zR u)) (rv X.B.I v (X.zR u)) = -(Tw (D := D) u : ℂ) :=
      (ProductExactness.hJ_X X v _ _).trans (by rw [X.zu_norm u]; simp [Tw])
    rw [h5]
    have hs : ((Real.sqrt (Tw (D := D) u))⁻¹ : ℝ) * (Real.sqrt (Tw (D := D) u))⁻¹ * Tw (D := D) u = 1 := by
      rw [← mul_inv, Real.mul_self_sqrt hT.le, inv_mul_cancel₀ hT.ne']
    have : (((Real.sqrt (Tw (D := D) u))⁻¹ : ℝ) : ℂ) * ((((Real.sqrt (Tw (D := D) u))⁻¹ : ℝ) : ℂ) *
        -((Tw (D := D) u : ℝ) : ℂ)) = -(((Real.sqrt (Tw (D := D) u))⁻¹ * (Real.sqrt (Tw (D := D) u))⁻¹ *
          Tw (D := D) u : ℝ) : ℂ) := by push_cast; ring
    rw [this, hs]
    simp
  · intro v a b
    exact X.wfr_on u v a b
  · intro v c a
    exact ((X.wfr_perp u v a).1 c).1
  · intro v c a
    exact ((X.wfr_perp u v a).1 c).2
  · intro v a
    rw [hermitian_scaled_left]
    have h0 : hJ (X.B.I.ε v) (rv X.B.I v (X.zR u)) (X.wfr u v a) = 0 := (X.wfr_perp u v a).2
    rw [h0, mul_zero]

theorem stepSubG_of_MN (hN : MeasN) (hQ : NuQSFinite) : Formalism.L2.SG.RealObj.EnergyInst.StepSubG := by
  exact stepSubG_of sDecomp_holds hN (measH_of sDecomp_holds)
    (fun D X u => folner_of_haar X u (isHaarSub_SinfU sDecomp_holds hN (measH_of sDecomp_holds) X u)) hQ

end Formalism.L2.S.Pv.HaarSubS
end
end
end
