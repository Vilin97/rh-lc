module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddSSn
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnGeomCut
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnGeomAtGq
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnGeomUBL
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.EmbeddingMulVecFactorization
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GeometryEquivarianceEmbedding
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GeometryEquivarianceFirstVector
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSchmidtFrames.GsFramesOfIso
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSchmidtFrames.HmSelfRe
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSchmidtFrames.LocBCore
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSchmidtFrames.XiHermitianCofactorDet
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Lemma

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnGeomAssemble

section

@[expose] public section

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Geom

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH Formalism.FourierDecayAlt.P.AdmissibleLieWords
open scoped ComplexConjugate Matrix

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem bd_of_ubl {k r : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (z z' : Fin (2 * r + k + 1) → ℂ) (φ : B.Mat k r → F) (e γ : ℕ) (Bg : ℝ)
    (hBg : (e : ℝ) + γ ≤ Bg) (ε : ℝ)
    (h0 : ∃ C0 : ℝ, ∀ g ∈ geG k r z z' ε, ‖φ g‖ ≤ C0) (hU : ∀ n : ℕ, UBL φ (geG k r z z' ε) n e γ) (m : ℕ) :
    ∃ C : ℝ, ∀ u w : List (B.Mat k r),
      (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ w, B.unitLie k r X) → u.length + w.length ≤ m →
      ∀ g ∈ B.GV k r, ε ≤ Gf k r z z' g → ‖B.dLR u w φ g‖ ≤ C * B.gN g ^ (Bg * m) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    obtain ⟨C0, hC0⟩ := h0
    refine ⟨C0, fun u w _ _ hl g hg hgε => ?_⟩
    have hu : u = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hw : w = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hu hw
    simp only [Nat.cast_zero, mul_zero, Real.rpow_zero, mul_one]
    exact hC0 g ⟨hg, hgε⟩
  · obtain ⟨⟨C, hC0, hUB⟩, -⟩ := hU m
    refine ⟨C, fun u w hu hw hl g hg hgε => ?_⟩
    have hA : admitted m (wL u ++ wR w) := ⟨u, w, hu, hw, hl, rfl⟩
    have hb := hUB _ hA g ⟨hg, hgε⟩
    rw [dLR_eq]
    refine hb.trans (mul_le_mul_of_nonneg_left ?_ hC0)
    have h1 : 1 ≤ B.gN g := gN_ge_one hg
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le h1
    rw [len_LR]
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hl' : ((u.length + w.length : ℕ) : ℝ) ≤ m := by exact_mod_cast hl
    have he : (0 : ℝ) ≤ e := Nat.cast_nonneg _
    have hγ : (0 : ℝ) ≤ γ := Nat.cast_nonneg _
    push_cast at hl' ⊢
    nlinarith [mul_le_mul_of_nonneg_left hl' hγ, mul_le_mul_of_nonneg_left hm1 he,
      mul_le_mul_of_nonneg_right hBg (by linarith : (0 : ℝ) ≤ m)]

theorem geometry_assembly_holds : GeomAssemble := by
  intro hS hEn hEi hAt hB0 hU
  refine ⟨6, by norm_num, ?_⟩
  intro Cc Cb hCc hCb E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  set Bs := (T v).base with hBs
  have hk : 1 ≤ S.G.k := Bs.k_pos
  have hz : C2.StdZ S.G.k S.G.r Bs.z := ⟨Bs.z_mem, Bs.T_pos⟩
  have hz' : C2.StdZ S.G.k S.G.r Bs.z' := ⟨Bs.z'_mem, Bs.T'_pos⟩
  refine ⟨nuG Bs.z Bs.z', nuG' Bs.z Bs.z', ioG Bs.z Bs.z', ?_⟩
  obtain ⟨s1, s2, s3⟩ := hS _ _ _ _ hk hz hz'
  obtain ⟨C0, hC0⟩ := hB0 _ _ _ _ hk hz hz'
  have hr0 : (0 : ℝ) ≤ S.G.r := Nat.cast_nonneg _
  have hBg : ∀ e γ : ℕ, e ≤ 4 * (S.G.r + 1) → γ ≤ 2 * (S.G.r + 1) → (e : ℝ) + γ ≤ Cb * ((S.G.r : ℝ) + 1) := by
    intro e γ he hγ
    have he' : (e : ℝ) ≤ 4 * ((S.G.r : ℝ) + 1) := by exact_mod_cast he
    have hγ' : (γ : ℝ) ≤ 2 * ((S.G.r : ℝ) + 1) := by exact_mod_cast hγ
    nlinarith
  have hpos : ∀ ε : ℝ, 0 < ε → ∀ g ∈ geG S.G.k S.G.r Bs.z Bs.z' ε, g ∈ posG S.G.k S.G.r Bs.z Bs.z' :=
    fun ε hε g hg => ⟨hg.1, lt_of_lt_of_le hε hg.2⟩
  refine ⟨s1, s2, s3, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp g hg
    obtain ⟨h1, h2⟩ := hEn _ _ _ _ hk hz hz' _ hp.1 _ hp.2.1 _ hp.2.2.1 _ hp.2.2.2 g hg
    exact ⟨h1, h2, hEi _ _ _ _ hk hz hz' _ hp.1 _ hp.2.1 _ hp.2.2.1 _ hp.2.2.2 g hg⟩
  · intro ε hε m
    obtain ⟨⟨e, γ, he, hγ, hu⟩, -, -⟩ := hU _ _ _ _ hk hz hz' ε hε
    exact bd_of_ubl Bs.z Bs.z' _ e γ _ (hBg e γ he hγ) ε ⟨C0, fun g hg => (hC0 g (hpos ε hε g hg)).1⟩ hu m
  · intro ε hε m
    obtain ⟨-, ⟨e, γ, he, hγ, hu⟩, -⟩ := hU _ _ _ _ hk hz hz' ε hε
    exact bd_of_ubl Bs.z Bs.z' _ e γ _ (hBg e γ he hγ) ε ⟨C0, fun g hg => (hC0 g (hpos ε hε g hg)).2.1⟩ hu m
  · intro ε hε m
    obtain ⟨-, -, ⟨e, γ, he, hγ, hu⟩⟩ := hU _ _ _ _ hk hz hz' ε hε
    exact bd_of_ubl Bs.z Bs.z' _ e γ _ (hBg e γ he hγ) ε ⟨C0, fun g hg => (hC0 g (hpos ε hε g hg)).2.2⟩ hu m
  · intro q hq
    have hTT : (D.parOf S v).TT = Tz S.G.k S.G.r Bs.z * Tz S.G.k S.G.r Bs.z' := by
      show (D.parOf S v).T * (D.parOf S v).T' = _
      rw [hPl.2.2.2.1, hPl.2.2.2.2.1]
    have hq2 : Tz S.G.k S.G.r Bs.z * Tz S.G.k S.G.r Bs.z' < Complex.normSq q.2 := hTT ▸ hq.2
    exact hAt _ _ _ _ Bs.μsec hk hz hz' Bs.sec q.1 q.2 hq.1 hq2

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Geom
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothHermitianRankTwo

section

@[expose] public section

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Geom

open Formalism.QuantumDeterminants PI.UnitaryGroupMassFormula.GsFr
open scoped Matrix

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace S1

variable {k r : ℕ}

lemma smooth_hermitian_rank_two {s : Set (B.Mat k r)} {p q : B.Mat k r → Fin (2 * r + k + 1) → ℂ}
    (hp : Sm p s) (hq : Sm q s) : Sm (fun x => Rk k r (p x) (q x)) s := by
  unfold Sm Rk at *
  refine contDiffOn_pi.mpr fun i => contDiffOn_pi.mpr fun j => ?_
  simp only [Matrix.vecMulVec_apply, Matrix.vecMul, dotProduct, Pi.star_apply]
  have hs : ∀ l, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => star (q x l)) s := fun l => by
    have h := Complex.conjCLE.contDiff.comp_contDiffOn (contDiffOn_pi.mp hq l)
    simpa [Function.comp_def] using h
  exact (contDiffOn_pi.mp hp i).mul (ContDiffOn.sum fun l _ => (hs l).mul contDiffOn_const)

lemma s_unitH {s : Set (B.Mat k r)} {v : B.Mat k r → Fin (2 * r + k + 1) → ℂ} (hv : Sm v s)
    (hp : ∀ x ∈ s, 0 < (Formalism.QuantumDeterminants.herm (Hpk k r) (v x) (v x)).re) : Sm (fun x => unitH k r (v x)) s := by
  unfold Sm unitH Formalism.QuantumDeterminants.herm at *
  have hvi : ∀ i, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => v x i) s := fun i => contDiffOn_pi.mp hv i
  have hsi : ∀ i, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => star (v x i)) s := fun i => by
    have h := Complex.conjCLE.contDiff.comp_contDiffOn (hvi i)
    simpa [Function.comp_def] using h
  have hh : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => star (v x) ⬝ᵥ Hpk k r *ᵥ v x) s := by
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply]
    exact ContDiffOn.sum fun i _ => (hsi i).mul (ContDiffOn.sum fun j _ => contDiffOn_const.mul (hvi j))
  have hre : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => (star (v x) ⬝ᵥ Hpk k r *ᵥ v x).re) s := by
    have h := Complex.reCLM.contDiff.comp_contDiffOn hh
    simpa [Function.comp_def] using h
  have hsq := hre.sqrt fun x hx => (hp x hx).ne'
  have hinv := hsq.inv fun x hx => (Real.sqrt_pos.mpr (hp x hx)).ne'
  have hc : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x => (((Real.sqrt (star (v x) ⬝ᵥ Hpk k r *ᵥ v x).re)⁻¹ : ℝ) : ℂ)) s := by
    have h := Complex.ofRealCLM.contDiff.comp_contDiffOn hinv
    simpa [Function.comp_def] using h
  exact hc.smul hv

end S1

open S1 in
theorem geometry_smoothness_holds : GeomSmooth := by
  intro k r z z' _hk hz hz'
  let fd : B.Mat k r → ℂ := fun g => (Zhat k r z z' g).det
  let f1 : B.Mat k r → ℝ := fun g =>
    (Formalism.QuantumDeterminants.herm (Hpk k r) (omW k r z z' g) (omW k r z z' g)).re
  let f2 : B.Mat k r → ℝ := fun g =>
    (Formalism.QuantumDeterminants.herm (Hpk k r) (omS k r z z' g) (omS k r z z' g)).re
  have hid : Sm (fun g : B.Mat k r => g) Set.univ := contDiffOn_id
  have cd : Continuous fd := (contDiffOn_univ.1 (s_det (s_Zhat z z' hid))).continuous
  have c1 : Continuous f1 :=
    (contDiffOn_univ.1 (s_re (s_herm _ (s_omW z z' hid) (s_omW z z' hid)))).continuous
  have c2 : Continuous f2 :=
    (contDiffOn_univ.1 (s_re (s_herm _ (s_omS (s := Set.univ) z z') (s_omS z z')))).continuous
  let U : Set (B.Mat k r) := (fd ⁻¹' {0}ᶜ ∩ {g | 0 < f1 g}) ∩ {g | 0 < f2 g}
  have hU : IsOpen U :=
    ((isOpen_compl_singleton.preimage cd).inter (isOpen_lt continuous_const c1)).inter
      (isOpen_lt continuous_const c2)
  have hmem : ∀ g ∈ posG k r z z', g ∈ U := by
    intro g hg
    obtain ⟨hgV, hG⟩ := hg
    refine ⟨⟨det_ne_of_G hz hz' hG, ?_⟩, ?_⟩
    · have hm : omW k r z z' g ∈ Wsp k r z := prW_mem hz _
      exact posV hz hm.1 hm.2 (omW_ne hz hz' hgV hG)
    · have hm : omS k r z z' g ∈ Wsp k r z' := prW_mem hz' _
      have hω : omS k r z z' g ≠ 0 := by rw [← omS_eq z z' hgV]; exact omW'_ne hz hz' hgV hG
      exact posV hz' hm.1 hm.2 hω
  have sU : Sm (fun g : B.Mat k r => g) U := contDiffOn_id
  have hd0 : ∀ g ∈ U, (Zhat k r z z' g).det ≠ 0 := fun g hg => hg.1.1
  have hnu : Sm (fun g => nuG z z' g) U := s_unitH (s_omW z z' sU) fun g hg => hg.1.2
  have hnuS : Sm (fun g => unitH k r (omS k r z z' g)) U := s_unitH (s_omS z z') fun g hg => hg.2
  have hdi : Sm (fun g => -((Zhat k r z z' g).det)⁻¹) U := ((s_det (s_Zhat z z' sU)).inv hd0).neg
  have hL : Sm (fun g => Lm k r z z' g) U := by
    unfold Lm
    exact contDiffOn_const.add (ContDiffOn.sum fun c _ => ContDiffOn.sum fun a _ =>
      s_msmul (hdi.mul (s_adj (s_Zhat z z' sU) c a)) (s_mmul contDiffOn_const sU))
  have hP : Sm (fun g => Phi k r z z' g) U := by
    unfold Phi
    exact s_mmul (s_mmul contDiffOn_const sU) hL
  have hio : Sm (fun g => Phi k r z z' g *
      (Pm k r z' - Rk k r (unitH k r (omS k r z z' g)) (unitH k r (omS k r z z' g)) * Pm k r z')) U :=
    s_mmul hP (contDiffOn_const.sub (s_mmul (smooth_hermitian_rank_two hnuS hnuS) contDiffOn_const))
  refine ⟨fun g₀ hg₀ => ⟨U, fun g => nuG z z' g, hU, hmem g₀ hg₀, hnu, fun g _ _ => rfl⟩,
    fun g₀ hg₀ => ⟨U, fun g => unitH k r (omS k r z z' g), hU, hmem g₀ hg₀, hnuS, fun g _ hgV => ?_⟩,
    fun g₀ hg₀ => ⟨U, _, hU, hmem g₀ hg₀, hio, fun g _ hgV => ?_⟩⟩
  · show unitH k r (omW' k r z z' g) = _
    rw [omS_eq z z' hgV]
  · show Phi k r z z' g * (Pm k r z' - Rk k r (unitH k r (omW' k r z z' g)) (unitH k r (omW' k r z z' g)) *
      Pm k r z') = _
    rw [omS_eq z z' hgV]

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Geom
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnGeom

section

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

theorem second_shift_geometry_holds : SSn.SSnGeom :=
  SSn.Geom.geometry_assembly_holds SSn.Geom.geometry_smoothness_holds SSn.Geom.geometry_equivariance_first_vector SSn.Geom.geometry_equivariance_embedding
    SSn.Geom.geometry_at_level_function SSn.Geom.geometry_boundedness_at_zero SSn.Geom.geometry_unipotent_bound_holds

end Formalism.FourierDecayAlt.P.CutMP.JA
end
end
