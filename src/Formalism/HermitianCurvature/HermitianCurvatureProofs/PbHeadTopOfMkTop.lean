module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEX2
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXAsm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXHeadFam
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXMkCpt
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXPbEquiv2
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXPbRight2
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsCompactCutoffCoefficient
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LeftFubiniNormalizedTower
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelsOfBuiltSetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyZeroNear
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PartialBesselSmoothCompactSupport
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ProperDomP
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXPbSupp2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.JfBetaAdjCOfLemmaBNorm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadJFExists
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceCompactSupportCoefficient
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXSliceTop
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FnValLift
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OperatorPreservesFusionForms
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEX_UwTop
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
import Formalism.HermitianCurvature.HermitianCurvatureProofs.EmbeddedGroupMeasurePreserving
import Formalism.HermitianCurvature.HermitianCurvatureProofs.KloostermanDensityOfParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceContOn
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WCellMemOmPlus
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.BitVec
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FirstBasisVectorIsRadialSlice
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameParameterRegularity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadGermSmoothExtension
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PbHeadTopOf
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopUnipotentIntegralPositive

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXPbSmooth

section

@[expose] public section

noncomputable section

open Matrix MeasureTheory Filter Topology Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutEX

open Formalism.FourierDecayAlt.P.PBI.Sm

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section lemmas

variable {k : ℕ}

theorem contDiff_castM {a b : ℕ} (e : a = b) : ContDiff ℝ ∞ (fun g : B.Mat k a => D.castM e g) := by
  subst e
  simp only [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]
  exact contDiff_id

theorem ms_mMap {r : ℕ} (q₀ : (Fin r → Fin r → ℂ) × Mt k (r - r)) (h₀ : (Matrix.of q₀.1).det ≠ 0) :
    MS (fun q : (Fin r → Fin r → ℂ) × Mt k (r - r) => U.mMap k r (r - r) (Matrix.of q.1) (Matrix.of q.2)) q₀ := by
  have hZ : MS (fun q : (Fin r → Fin r → ℂ) × Mt k (r - r) => Matrix.of q.1) q₀ :=
    Formalism.FourierDecayAlt.P.PBI.ms_ofC contDiffAt_fst
  have hμ : MS (fun q : (Fin r → Fin r → ℂ) × Mt k (r - r) => Matrix.of q.2) q₀ :=
    Formalism.FourierDecayAlt.P.PBI.ms_ofC contDiffAt_snd
  have hZi : MS (fun q : (Fin r → Fin r → ℂ) × Mt k (r - r) => (Matrix.of q.1)ᴴ⁻¹) q₀ :=
    ms_inv (ms_conjT hZ) (by rw [Matrix.det_conjTranspose]; exact star_ne_zero.mpr h₀)
  unfold U.mMap
  exact Formalism.FourierDecayAlt.P.PBI.measurable_block_three (ms_const _) (ms_const _) (ms_mul hZi (ms_const _)) (ms_const _) hμ (ms_const _)
    (ms_mul (ms_const _) hZ) (ms_const _) (ms_const _)

theorem contDiffOn_xT (r : ℕ) :
    ContDiffOn ℝ ∞ (fun q : (Fin r → Fin r → ℂ) × Mt k (r - r) => xT k r (Matrix.of q.1) (Matrix.of q.2))
      {q | (Matrix.of q.1).det ≠ 0} := by
  intro q₀ h₀
  have hm := ms_mMap q₀ h₀
  have hc : ContDiffAt ℝ ∞ (fun q : (Fin r → Fin r → ℂ) × Mt k (r - r) =>
      U.mMap k r (r - r) (Matrix.of q.1) (Matrix.of q.2)) q₀ :=
    contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun l => hm i l
  exact ((contDiff_castM (k := k) (by omega : r + (r - r) = r)).contDiffAt.comp q₀ hc).contDiffWithinAt

theorem dmin_xT (r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (Z : Matrix (Fin r) (Fin r) ℂ) (μ : B.Mat k (r - r)) :
    Dmin k r z z' (xT k r Z μ) ⟨r, by omega⟩ = Z.det := by
  unfold xT
  rw [Formalism.FourierDecayAlt.P.PBI.dmin_castM (by omega) z z' _ r (by omega) (by omega),
    Formalism.FourierDecayAlt.P.hat_z_minimum_degree k r (r - r)]
  have e := Formalism.FourierDecayAlt.P.hat_z_on_slice k r (r - r) 0 0 Z μ
  rw [Formalism.FourierDecayAlt.P.LeftFubiniLemmas.rn_zero, inv_one, Matrix.one_mul, Matrix.mul_one] at e
  unfold U.DjU
  rw [e]

theorem xT_GV (r : ℕ) {Z : Matrix (Fin r) (Fin r) ℂ} {μ : B.Mat k (r - r)} (hZ : Z.det ≠ 0) (hμ : μ ∈ B.GV k (r - r)) :
    xT k r Z μ ∈ B.GV k r :=
  Formalism.FourierDecayAlt.P.PBE.castM_GV _ ((Formalism.FourierDecayAlt.P.slice_membership k r (r - r)).1 Z μ hZ hμ)

theorem gf_castM {a b : ℕ} (e : a = b) (z z' : Fin (2 * b + k + 1) → ℂ) (g : B.Mat k a) :
    Gf k b z z' (D.castM e g) = Gf k a (D.castV e.symm z) (D.castV e.symm z') g := by
  subst e
  rw [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl, Formalism.FourierDecayAlt.P.JCTx5.castV_rfl, Formalism.FourierDecayAlt.P.JCTx5.castV_rfl]

theorem inWb_castV {a b : ℕ} (e : a = b) {z : Fin (2 * a + k + 1) → ℂ} (h : inWb k a z) : inWb k b (D.castV e z) := by
  subst e
  rwa [Formalism.FourierDecayAlt.P.JCTx5.castV_rfl]

end lemmas

theorem pullback_smooth_formula : PbSmooth := by
  intro Wp Wq _ _ _ _ _ _ P p G hG q₀ hq₀ hG₀
  obtain ⟨⟨hsm, ⟨R, hR⟩, -⟩, -⟩ := hG
  have hCs : IsCompact {g : B.Mat P.k P.r | B.gN g ≤ R} := Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le P.k P.r R
  have hHC : ∀ g ∈ B.GV P.k P.r, g ∉ {g : B.Mat P.k P.r | B.gN g ≤ R} → G g = 0 := by
    intro g hg hn
    by_contra hne
    exact hn (hR g hg hne)
  have hΩ := PBQ.isOpen_domP P.k P.r P.r p.T.base.z p.T.base.z'
  have hP := proper_left_variables_domain Wp Wq P p P.r le_rfl _ hCs
  have hG₀' : Matrix.of q₀.2 ∈ B.GV P.k (P.r - P.r) := hG₀.1
  have hgf : 0 < Gf P.k P.r p.T.base.z p.T.base.z' (xT P.k P.r (Matrix.of q₀.1) (Matrix.of q₀.2)) := by
    unfold xT
    rw [gf_castM]
    have e := Formalism.FourierDecayAlt.P.level_function_slice P.k P.r (P.r - P.r)
      (D.castV (by omega : P.r = P.r + (P.r - P.r)) p.T.base.z) (D.castV (by omega : P.r = P.r + (P.r - P.r)) p.T.base.z')
      (inWb_castV _ p.T.base.z_mem) (inWb_castV _ p.T.base.z'_mem) 0 0 (Matrix.of q₀.1) (Matrix.of q₀.2)
    rw [Formalism.FourierDecayAlt.P.LeftFubiniLemmas.rn_zero, inv_one, Matrix.one_mul, Matrix.mul_one] at e
    rw [e, MkCptPf.lowV_top p.T _, MkCptPf.lowV_top' p.T _, MkCptPf.gf_eq_ggl (by omega)]
    exact mul_pos (Complex.normSq_pos.2 hq₀.1) hq₀.2
  have hyΩ : xT P.k P.r (Matrix.of q₀.1) (Matrix.of q₀.2) ∈ PBQ.domP P.k P.r P.r p.T.base.z p.T.base.z' := by
    refine ⟨fun l hl1 hl2 => ?_, hgf⟩
    have hl : l = ⟨P.r, by omega⟩ := Fin.ext (by show (l : ℕ) = P.r; omega)
    rw [hl, dmin_xT]; exact hq₀.1
  have hyG := xT_GV P.r hq₀.1 hG₀'
  have hz : p.T.base.z = D.castV (by omega : P.r + (P.r - P.r) = P.r) (liftVec P.k P.r (P.r - P.r) (p.T.bs P.r).z) :=
    (p.T.z_lev P.r le_rfl).symm
  obtain ⟨V, f', hV, hyV, hf', hag⟩ := partial_bessel_smooth_compact_support P.k P.r (P.r - P.r) P.r Wp Wq (p.T.bs P.r) p.T.base
    (by omega) hz G _ hsm hCs hHC _ hΩ hP _ hyΩ hyG
  have hxc := contDiffOn_xT (k := P.k) P.r
  have hOD : IsOpen {q : (Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r) | (Matrix.of q.1).det ≠ 0} :=
    isOpen_ne_fun (Continuous.matrix_det (continuous_fst)) continuous_const
  refine ⟨{q | (Matrix.of q.1).det ≠ 0} ∩
      (fun q : (Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r) => xT P.k P.r (Matrix.of q.1) (Matrix.of q.2)) ⁻¹' V,
    fun q => f' (xT P.k P.r (Matrix.of q.1) (Matrix.of q.2)), hxc.continuousOn.isOpen_inter_preimage hOD hV,
    ⟨hq₀.1, hyV⟩, hf'.comp (hxc.mono Set.inter_subset_left) (fun q hq => hq.2), fun q hq hqG => ?_⟩
  exact hag _ hq.2 (xT_GV P.r hq.1 hqG.1)

end Formalism.FourierDecayAlt.P.CutEX

namespace Formalism.FourierDecayAlt.P

theorem pullback_smooth : CutEX.PbSmooth := CutEX.pullback_smooth_formula

end Formalism.FourierDecayAlt.P
end
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXRadSliceTop

section

@[expose] public section

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt

theorem radial_slice_top : CutEX.RadSliceTop := by
  intro Wp Wq _ _ _ _ _ _ P p G hG h hh
  have hc : P.r - P.r = P.r - D.ptSize h := by rw [hh.2]
  have hcpt : KB.CptCoef (p.T.bs P.r) (D.castF hc (D.sliceAt P.k P.r p.T.base.z p.T.base.z' G h)) := by
    cases P with
    | mk k r T T' u u' =>
      rcases Nat.eq_zero_or_pos r with h0 | h0
      · subst h0
        exact PBE.slice_level_zero_compact_support k 0 Wp Wq p.T G hG.1 (Nat.zero_le _) [] h hc hh (fun x => x.elim0)
      · exact PBE.slice_pos_cpt k r Wp Wq p.T G hG.1 r le_rfl h0 [] h hc hh (fun x => x.elim0)
  obtain ⟨R, hR⟩ := hcpt.2.1
  have hJ : P5.JFOK (JC.parLev P P.r) (p.T.bs P.r).z (p.T.bs P.r).z'
      (D.castF hc (D.sliceAt P.k P.r p.T.base.z p.T.base.z' G h)) := by
    refine ⟨fun A m => JFxG.cptInCC_G hcpt.1 (PBE.isCompact_gN_le _ _ R) (fun g hg hgC => ?_) A m, hcpt.2.2⟩
    by_contra hne
    exact hgC (hR g hg hne)
  obtain ⟨Φ, hΦ⟩ := P5.radJFExists Wp Wq (JC.parLev P P.r) _ _ _ _ (p.T.bs P.r) _
    (JCTx5.isPlace_lev P p.T ⟨P.r, Nat.lt_succ_self _⟩ p.hP) rfl rfl rfl rfl hJ
  exact ⟨Φ, hΦ⟩

end Formalism.FourierDecayAlt.P
end
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXTopPt

section

@[expose] public section

noncomputable section

open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutEXTop

theorem domR_pt (k i r' : ℕ) (hr' : r' = 0) (zs zs' : Fin (2 * r' + k + 1) → ℂ) (x : (Fin (i + r') → ℂ) × Q.Mx k (i + r'))
    (hx : x ∈ Q.DomR k (i + r') (liftVec k i r' zs) (liftVec k i r' zs')) :
    ∃ g : Q.Mx k r', g ∈ Q.Glev k r' (Fin.last r') ∧ 0 < Q.GGl k r' zs zs' g ∧ x.2 = ιLev k i r' g := by
  subst hr'
  obtain ⟨-, hxG, hxP⟩ := hx
  have himg := Formalism.FourierDecayAlt.P.level_group_image k i 0
  have hxG' : x.2 ∈ Q.Glev k (i + 0) ⟨i, by omega⟩ := hxG
  rw [himg] at hxG'
  obtain ⟨g, hgU, hgx⟩ := hxG'
  refine ⟨g, ⟨hgU, fun a => a.elim0⟩, ?_, hgx.symm⟩
  rw [← Formalism.FourierDecayAlt.P.WordCorrespondence.ggl_lift zs zs' g, hgx]
  exact hxP

theorem domR_pt_cast (k n i r' : ℕ) (hn : i + r' = n) (hr' : r' = 0) {z z' : Fin (2 * n + k + 1) → ℂ}
    {zs zs' : Fin (2 * r' + k + 1) → ℂ} (hz : D.castV hn (liftVec k i r' zs) = z)
    (hz' : D.castV hn (liftVec k i r' zs') = z') (x : (Fin n → ℂ) × Q.Mx k n) (hx : x ∈ Q.DomR k n z z') :
    ∃ g : Q.Mx k r', g ∈ Q.Glev k r' (Fin.last r') ∧ 0 < Q.GGl k r' zs zs' g ∧ x.2 = D.castM hn (ιLev k i r' g) := by
  subst hn
  subst hz
  subst hz'
  obtain ⟨g, h1, h2, h3⟩ := domR_pt k i r' hr' zs zs' x hx
  exact ⟨g, h1, h2, h3⟩

theorem gv_iff_glev (k ρ : ℕ) (hρ : ρ = 0) (γ : B.Mat k ρ) : γ ∈ B.GV k ρ ↔ γ ∈ Q.Glev k ρ (Fin.last ρ) := by
  subst hρ
  constructor
  · intro h
    exact ⟨h, fun a => a.elim0⟩
  · intro h
    exact h.1

end Formalism.FourierDecayAlt.P.CutEXTop

open Formalism.FourierDecayAlt.P.CutEXTop in
theorem Formalism.FourierDecayAlt.P.top_point_existence : Formalism.FourierDecayAlt.P.CutEX.TopPt := by
  intro Wp Wq _ _ _ _ _ _ P p
  refine ⟨fun x hx => ?_, fun γ => gv_iff_glev P.k (P.r - P.r) (by omega) γ⟩
  exact domR_pt_cast P.k P.r P.r (P.r - P.r) (by omega) (by omega) (p.T.z_lev P.r le_rfl) (p.T.z'_lev P.r le_rfl) x hx
end
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXp

section

@[expose] public section

noncomputable section

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutEX

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem residue_top_exceptional : ResTop := by
  intro E _ _ k ρ hρ J c g
  subst hρ
  simp [Q.resG, Q.wCell]

theorem radial_extension_holds : RadExt := by
  intro Wp Wq _ _ _ _ k ρ z z' π π' Ψ Ψ' h
  apply Subtype.ext
  funext c g
  by_cases hx : ((c, g) : (Fin ρ → ℂ) × Q.Mx k ρ) ∈ Q.DomR k ρ z z'
  · exact h _ hx
  · rw [Ψ.2.1 (c, g) hx, Ψ'.2.1 (c, g) hx]

theorem radial_of_function_holds : RadOfFun := by
  classical
  intro Wp Wq _ _ _ _ k ρ z z' π π' f hloc hequiv
  have hUW : ∀ {w : Fin (2 * ρ + k + 1) → ℂ} {h : Mx k ρ}, h ∈ UWset k ρ w → h ∈ Glev k ρ (Fin.last ρ) :=
    fun hh => ⟨hh.1, fun a _ => hh.2.1 a⟩
  refine ⟨⟨fun c g => if (c, g) ∈ DomR k ρ z z' then f g else 0, ?_, ?_, ?_⟩, ?_⟩
  · intro x hx
    show (if (x.1, x.2) ∈ DomR k ρ z z' then f x.2 else 0) = 0
    exact if_neg hx
  · intro x₀ hx₀
    obtain ⟨hΩ, hG, hpos⟩ := hx₀
    obtain ⟨U, F, hU, hgU, hF, hFe⟩ := hloc x₀.2 hG hpos
    refine ⟨OmX ρ ×ˢ (U ∩ {g | 0 < GGl k ρ z z' g}), fun x => F x.2, ?_, ?_, ?_, ?_⟩
    · exact (Formalism.FourierDecayAlt.P.Qx5.isOpen_OmX ρ).prod
        (hU.inter (isOpen_lt continuous_const (Formalism.FourierDecayAlt.P.Qx5.GGl_continuous k ρ z z')))
    · exact ⟨hΩ, hgU, hpos⟩
    · exact hF.comp contDiff_snd.contDiffOn (fun x hx => hx.2.1)
    · intro x hx hxG
      have hxD : (x.1, x.2) ∈ DomR k ρ z z' := ⟨hx.1, hxG, hx.2.2⟩
      show (if (x.1, x.2) ∈ DomR k ρ z z' then f x.2 else 0) = F x.2
      rw [if_pos hxD]
      exact hFe x.2 hx.2.1 hxG
  · intro x hx h hh h' hh'
    obtain ⟨hΩ, hG, hpos⟩ := hx
    have hD : (x.1, h * x.2 * h') ∈ DomR k ρ z z' :=
      ⟨hΩ, Formalism.FourierDecayAlt.P.Qx5.Glev_mul (Formalism.FourierDecayAlt.P.Qx5.Glev_mul (hUW hh) hG) (hUW hh'),
        by rw [Formalism.FourierDecayAlt.P5.Rad.GGl_uw hh hh']; exact hpos⟩
    have hD0 : (x.1, x.2) ∈ DomR k ρ z z' := ⟨hΩ, hG, hpos⟩
    show (if (x.1, h * x.2 * h') ∈ DomR k ρ z z' then f (h * x.2 * h') else 0) =
      π h ∘SL (if (x.1, x.2) ∈ DomR k ρ z z' then f x.2 else 0) ∘SL π' h'
    rw [if_pos hD, if_pos hD0]
    exact hequiv x.2 hG hpos h hh h' hh'
  · intro x hx
    show (if (x.1, x.2) ∈ DomR k ρ z z' then f x.2 else 0) = f x.2
    exact if_pos hx

theorem determinant_vanishing_holds : ZxDet := by
  intro r h hh v
  unfold PBQ.zxH
  rw [Matrix.det_reindex_self, Matrix.det_mul]
  exact mul_ne_zero (LeftFubiniLemmas.lh_unit _ v).ne_zero
    (Formalism.FourierDecayAlt.P.PBM.hMat_det_ne _ _ (fun a => Formalism.FourierDecayAlt.P.PBJ.Asm.ptScal_ne h hh.1 a a.isLt))

end Formalism.FourierDecayAlt.P.CutEX

namespace Formalism.FourierDecayAlt.P

theorem residue_top_exceptional_level : CutEX.ResTop := CutEX.residue_top_exceptional
theorem radial_extension_exceptional : CutEX.RadExt := CutEX.radial_extension_holds
theorem radial_of_function_exceptional : CutEX.RadOfFun := CutEX.radial_of_function_holds
theorem determinant_exceptional_holds : CutEX.ZxDet := CutEX.determinant_vanishing_holds

end Formalism.FourierDecayAlt.P
end
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.PbHeadTopOfMkTop

section

@[expose] public section

namespace Formalism.FourierDecayAlt.P

theorem pb_exhPic_of_mkTop (hMk : CutEX.MkTop) : PBI.ExhPic :=
  CutEX.exhPic_of_leaves CutEX.exceptional_assumption_holds unipotent_weight_top slice_top_exhaustion pullback_smooth
    pullback_right_action pullback_support pullback_equivalence hMk compact_truncation_construction top_point_existence
    determinant_exceptional_holds head_family_exhaustion radial_slice_top radial_of_function_exceptional radial_extension_exceptional
    residue_top_exceptional_level frame_parameter_regularity (pb_radWordSliceOfHeadPic head_picture) level_zero_picture_of_slice

theorem pb_headTop_of_mkTop (hMk : CutEX.MkTop) : KB.HeadTop :=
  pb_headTop_of top_unipotent_integral (pb_exhPic_of_mkTop hMk)

end Formalism.FourierDecayAlt.P
end
end
