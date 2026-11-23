module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCLocalCut
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CoordinateCommuteRaisingConstant
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnTrSmooth
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedA
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.cut_GCore_GTConnCut
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCRadSpSmooth
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTConnGaugeA
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTConnGaugeB
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedA
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedF
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NfRadOrder0OfRadRed
import Mathlib.Analysis.InnerProductSpace.Calculus

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCLocalFrameA

section

@[expose] public section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

theorem gcl_slice_iter {r : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : (Fin r → ℂ) × ℂ → V) (s : Set ((Fin r → ℂ) × ℂ)) (hs : IsOpen s)
    (hF : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F s) (q : (Fin r → ℂ) × ℂ) (hq : q ∈ s) (j : ℕ) :
    iteratedFDeriv ℝ j (fun ζ => F (q.1, ζ)) q.2 =
      (iteratedFDeriv ℝ j F q).compContinuousLinearMap (fun _ => ContinuousLinearMap.inr ℝ (Fin r → ℂ) ℂ) := by
  let a : (Fin r → ℂ) × ℂ := (q.1, 0)
  let L : ℂ →L[ℝ] (Fin r → ℂ) × ℂ := ContinuousLinearMap.inr ℝ (Fin r → ℂ) ℂ
  let G : (Fin r → ℂ) × ℂ → V := fun p => F (a + p)
  let s' : Set ((Fin r → ℂ) × ℂ) := (fun p => a + p) ⁻¹' s
  have hs' : IsOpen s' := hs.preimage (continuous_const.add continuous_id)
  have hG : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G s' :=
    hF.comp ((contDiff_const.add contDiff_id).contDiffOn) (fun p hp => hp)
  have hslice : (fun ζ : ℂ => F (q.1, ζ)) = G ∘ L := by
    funext ζ
    simp [G, a, L]
  have hq' : L q.2 ∈ s' := by
    show a + L q.2 ∈ s
    simpa [a, L] using hq
  have hpre : IsOpen (L ⁻¹' s') := hs'.preimage L.continuous
  have hmem : q.2 ∈ L ⁻¹' s' := hq'
  rw [hslice, ← iteratedFDerivWithin_of_isOpen j hpre hmem,
    L.iteratedFDerivWithin_comp_right hG hs'.uniqueDiffOn hpre.uniqueDiffOn hq'
      (by exact_mod_cast (le_top : ((j : ℕ∞)) ≤ ⊤)),
    iteratedFDerivWithin_of_isOpen j hs' hq']
  have hGq : iteratedFDeriv ℝ j G (L q.2) = iteratedFDeriv ℝ j F q := by
    show iteratedFDeriv ℝ j (fun p => F (a + p)) (L q.2) = _
    rw [iteratedFDeriv_comp_add_left']
    show iteratedFDeriv ℝ j F (a + L q.2) = _
    congr 1
    ext <;> simp [a, L]
  rw [hGq]

theorem gcl_isRadDiff {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (hRB : NF.RadBase P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π')
    (T : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) (hT : RadDZ P Bs T) :
    NF.IsRadDiff P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' T := by
  obtain ⟨n, A, hA, hT'⟩ := hT
  have hmem : ∀ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π',
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp))) (NF.QR P.k P.r Bs.z Bs.z') :=
    fun Φ => (Formalism.FourierDecayAlt.P.radical_reduction_mem Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hRB Φ Φ.2).1
  have hopen : IsOpen (NF.QR P.k P.r Bs.z Bs.z') := by
    have h1 : IsOpen (Formalism.QuantumDeterminants.OmX P.r) := by
      have h2 : Formalism.QuantumDeterminants.OmX P.r = ⋂ l, {x : Fin P.r → ℂ | x l ≠ 0} := by
        ext x
        simp [Formalism.QuantumDeterminants.OmX]
      rw [h2]
      exact isOpen_iInter_of_finite (fun l => isOpen_ne_fun (continuous_apply l) continuous_const)
    exact (h1.preimage continuous_fst).inter
      (isOpen_lt continuous_const (Complex.continuous_normSq.comp continuous_snd))
  refine ⟨n, fun j q => (A j q.2).comp (ContinuousMultilinearMap.compContinuousLinearMapL
    (fun _ : Fin j => ContinuousLinearMap.inr ℝ (Fin P.r → ℂ) ℂ)), ?_, ?_⟩
  · intro j
    have hA' : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : (Fin P.r → ℂ) × ℂ => A j q.2)
        (NF.QR P.k P.r Bs.z Bs.z') :=
      (hA j).comp contDiff_snd.contDiffOn (fun q hq => hq.2)
    exact hA'.clm_comp contDiffOn_const
  · intro Φ q hq
    rw [hT' Φ q hq]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [gcl_slice_iter _ _ hopen (hmem Φ) q hq j]
    simp only [ContinuousLinearMap.comp_apply, ContinuousMultilinearMap.compContinuousLinearMapL_apply]

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCLocalFrameB

section

@[expose] public section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

section frame

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem gcl_hsVec_add (A A' : Wq →L[ℂ] Wp) : B.hsVec (A + A') = B.hsVec A + B.hsVec A' := by
  ext i
  simp [B.hsVec]

theorem gcl_hsVec_sum {ι : Type} (s : Finset ι) (A : ι → (Wq →L[ℂ] Wp)) :
    B.hsVec (∑ i ∈ s, A i) = ∑ i ∈ s, B.hsVec (A i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · ext i
    simp [B.hsVec]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, gcl_hsVec_add, ih]

theorem gcl_hsVec_smul (c : ℂ) (A : Wq →L[ℂ] Wp) : B.hsVec (c • A) = c • B.hsVec A := by
  ext i
  simp [B.hsVec]

theorem gcl_wRc_smooth (P : M.Par) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ζ : ℂ => ((wR P.k P.TT ζ : ℝ) : ℂ)) (Ann P) := by
  have hre : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ζ : ℂ => ζ.re) := Complex.reCLM.contDiff
  have him : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ζ : ℂ => ζ.im) := Complex.imCLM.contDiff
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ζ : ℂ => Complex.normSq ζ - P.TT) := by
    simp_rw [Complex.normSq_apply]
    exact ((hre.mul hre).add (him.mul him)).sub contDiff_const
  have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ζ : ℂ => wR P.k P.TT ζ) (Ann P) := by
    simp only [wR]
    exact ((h1.pow _).contDiffOn).sqrt (fun ζ hζ => (pow_pos (sub_pos.2 hζ) _).ne')
  exact Complex.ofRealCLM.contDiff.comp_contDiffOn h2

theorem gcl_wR_ne (P : M.Par) {ζ : ℂ} (hζ : ζ ∈ Ann P) : ((wR P.k P.TT ζ : ℝ) : ℂ) ≠ 0 := by
  have h : 0 < Complex.normSq ζ - P.TT := sub_pos.2 hζ
  have hw : 0 < wR P.k P.TT ζ := by
    unfold wR
    exact Real.sqrt_pos.2 (pow_pos h _)
  exact Complex.ofReal_ne_zero.2 hw.ne'

theorem gcl_dZ_smooth {g : ℂ → ℂ} {s : Set ℂ} (hs : IsOpen s) (hg : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g s) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (NF.dZ g) s ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (NF.dZb g) s := by
  have hd : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => fderiv ℝ g y) s :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen hs).1 hg).2
  have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => fderiv ℝ g y 1) s :=
    hd.clm_apply contDiffOn_const
  have hI : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => fderiv ℝ g y Complex.I) s :=
    hd.clm_apply contDiffOn_const
  refine ⟨?_, ?_⟩
  · exact contDiffOn_const.mul (h1.sub (contDiffOn_const.mul hI))
  · exact contDiffOn_const.mul (h1.add (contDiffOn_const.mul hI))

theorem gcl_wirt_slice {r : ℕ} (F : MA.E r → ℂ) (x : MA.E r) (hF : DifferentiableAt ℝ F x) :
    MA.wirt M.vz F x = NF.dZ (fun ζ => F (x.1, ζ)) x.2 ∧
      MA.wirt M.vzb F x = NF.dZb (fun ζ => F (x.1, ζ)) x.2 := by
  have hmap : HasFDerivAt (fun ζ : ℂ => (x.1, ζ))
      ((0 : ℂ →L[ℝ] (Fin r → ℂ)).prod (ContinuousLinearMap.id ℝ ℂ)) x.2 :=
    (hasFDerivAt_const x.1 x.2).prodMk (hasFDerivAt_id x.2)
  have hF' : HasFDerivAt F (fderiv ℝ F x) (x.1, x.2) := by
    simpa using hF.hasFDerivAt
  have hcomp : HasFDerivAt (fun ζ => F (x.1, ζ))
      ((fderiv ℝ F x).comp ((0 : ℂ →L[ℝ] (Fin r → ℂ)).prod (ContinuousLinearMap.id ℝ ℂ))) x.2 :=
    hF'.comp x.2 hmap
  have hd : ∀ v : ℂ, fderiv ℝ (fun ζ => F (x.1, ζ)) x.2 v = fderiv ℝ F x (0, v) := by
    intro v
    rw [hcomp.fderiv]
    simp
  have e1 : MA.dirE (r := r) M.vz = ((0 : Fin r → ℂ), (1 : ℂ)) := by
    simp [MA.dirE, M.vz]
  have e2 : MA.dirE (r := r) M.vzb = ((0 : Fin r → ℂ), (1 : ℂ)) := by
    simp [MA.dirE, M.vzb]
  refine ⟨?_, ?_⟩
  · simp only [MA.wirt, NF.dZ, e1, hd]
    simp [M.vz] <;> ring
  · simp only [MA.wirt, NF.dZb, e2, hd]
    simp [M.vzb] <;> ring

theorem gcl_radR_sum {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {ι : Type} (s : Finset ι) (F : ι → Q.Fn k r E)
    (x : (Fin r → ℂ) × ℂ) :
    NF.radR k r z z' μsec (∑ i ∈ s, F i) x = ∑ i ∈ s, NF.radR k r z z' μsec (F i) x := by
  by_cases hx : x ∈ NF.QR k r z z'
  · simp [NF.radR, Set.indicator, hx, Finset.sum_apply]
  · simp [NF.radR, Set.indicator, hx]

theorem gcl_trR_val (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π')
    (hk : 2 ≤ P.k) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (he : IsFrameB P Bs e)
    (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (ρ : M.Ty P) (q : MA.Qp P.r P.TT) :
    ((trR P Bs e Φ ρ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q =
      ((wR P.k P.TT q.1.2 : ℝ) : ℂ) *
        inner ℂ (B.hsVec (e ρ q.1.2)) (B.hsVec (NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1)) := by
  have hmem := radial_space_smoothness Wp Wq P Bs hpl hk e he Φ ρ
  have hq : q.1 ∈ NF.QR P.k P.r Bs.z Bs.z' := by
    obtain ⟨h1, h2⟩ := q.2
    refine ⟨h1, ?_⟩
    rw [hpl.2.2.2.1, hpl.2.2.2.2.1]
    exact h2
  have h1 : ((trR P Bs e Φ ρ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) =
      rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ := by
    simp only [trR, MA.toSm, dif_pos hmem]
  rw [h1]
  simp [rawR, NF.radR, Set.indicator_of_mem hq]

end frame

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.cut_GCore_GTCLocalFrameC

section

@[expose] public section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

section core

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem gcl_core (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')))
    (hH : GTHyp P Bs X d) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (he : IsFrameB P Bs e) (hk : KapF P Bs d e)
    (T : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) (hT : RadDZ P Bs T) (a b : ℂ)
    (ha : ∀ Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π',
      (Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) = NF.mulZ P.k P.r Bs.z Bs.z' id (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) →
        (T Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) =
          NF.mulZ P.k P.r Bs.z Bs.z' id (T Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) + a • (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)))
    (hb : ∀ Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π',
      (Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) = NF.mulZ P.k P.r Bs.z Bs.z' (starRingEnd ℂ) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) →
        (T Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) =
          NF.mulZ P.k P.r Bs.z Bs.z' (starRingEnd ℂ) (T Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) + b • (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)))
    (hκ : ∀ (f : M.Ty P → ℂ) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), T ((d.κ f).1 Φ) = (d.κ f).1 (T Φ)) :
    ∃ A : M.Ty P → ℂ → ℂ, (∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (A ρ) (Ann P)) ∧
      ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (ρ : M.Ty P) (q : MA.Qp P.r P.TT),
        ((trR P Bs e (T Φ) ρ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q =
          a * MA.wirt M.vz (MA.ext ((trR P Bs e Φ ρ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ)) q.1 +
          b * MA.wirt M.vzb (MA.ext ((trR P Bs e Φ ρ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ)) q.1 +
          A ρ q.1.2 * ((trR P Bs e Φ ρ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q := by
  obtain ⟨hpl, hk2, hcs, hL, hS, hR, hQ⟩ := hH
  have hTz : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' = P.TT := by rw [hpl.2.2.2.1, hpl.2.2.2.2.1]; rfl
  have hRB : NF.RadBase P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' :=
    ⟨hpl.1.k_pos, hpl.2.1, hpl.2.2.1, by rw [hpl.2.2.2.1]; exact hpl.1.T_pos,
      by rw [hpl.2.2.2.2.1]; exact hpl.1.T'_pos, Bs.sec, hpl.2.2.2.2.2.1.2.1, hpl.2.2.2.2.2.2.2.1,
      hpl.2.2.2.2.2.1.2.2.1, hpl.2.2.2.2.2.2.2.2.1⟩
  have hIR := gcl_isRadDiff P Bs hRB T hT
  have hUo : IsOpen (Ann P) := ann_open P
  have hUeq : {ζ : ℂ | Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ} = Ann P := by
    rw [hTz]; rfl
  have hQR : ∀ x : (Fin P.r → ℂ) × ℂ, x ∈ NF.QR P.k P.r Bs.z Bs.z' ↔ (x.1 ∈ OmX P.r ∧ x.2 ∈ Ann P) := by
    intro x
    show (x.1 ∈ OmX P.r ∧ Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq x.2) ↔ _
    rw [hTz]; rfl
  have hQRo : IsOpen (NF.QR P.k P.r Bs.z Bs.z') := Formalism.FourierDecayAlt.P.NFRO.isOpen_QR
  have hMem := Formalism.FourierDecayAlt.P.radical_reduction_mem Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hRB

  have hφ : ∀ σ, ((NF.QR P.k P.r Bs.z Bs.z').indicator fun x => e σ x.2) ∈
      NF.RadSec P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' := by
    intro σ
    refine ⟨?_, fun x hx => ?_, fun x hx => ?_⟩
    · have h1 : ContDiffOn ℝ ∞ (fun x : (Fin P.r → ℂ) × ℂ => e σ x.2) (NF.QR P.k P.r Bs.z Bs.z') :=
        (he.1 σ).comp contDiff_snd.contDiffOn fun x hx => ((hQR x).1 hx).2
      exact h1.congr fun x hx => by simp [Set.indicator_of_mem hx]
    · simp only [Set.indicator_of_mem hx]
      exact (he.2 x.2 ((hQR x).1 hx).2).1 σ
    · simp [Set.indicator_of_notMem hx]
  choose Ψ0 hΨ0 hradΨ using fun σ =>
    Formalism.FourierDecayAlt.P.radical_reduction_surjective Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hRB _ (hφ σ)
  let Ψ : M.Ty P → Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' := fun σ => ⟨Ψ0 σ, hΨ0 σ⟩
  have hΨv : ∀ σ x, x ∈ NF.QR P.k P.r Bs.z Bs.z' →
      NF.radR P.k P.r Bs.z Bs.z' Bs.μsec ((Ψ σ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x = e σ x.2 := by
    intro σ x hx
    show NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (Ψ0 σ) x = e σ x.2
    rw [hradΨ σ]; simp [Set.indicator_of_mem hx]

  have hKv : ∀ (f : M.Ty P → ℂ) (Θ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (ρ : M.Ty P) (x : (Fin P.r → ℂ) × ℂ),
      x ∈ NF.QR P.k P.r Bs.z Bs.z' →
      inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (NF.radR P.k P.r Bs.z Bs.z' Bs.μsec
          (((d.κ f).1 Θ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x)) =
        f ρ * inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (NF.radR P.k P.r Bs.z Bs.z' Bs.μsec
          (Θ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x)) := by
    intro f Θ ρ x hx
    have hx' := (hQR x).1 hx
    let q : MA.Qp P.r P.TT := ⟨x, ⟨hx'.1, hx'.2⟩⟩
    have h1 := congrArg (fun F : MA.SmQ P.r P.TT => (F : MA.Qp P.r P.TT → ℂ) q) (congrFun (hk f Θ) ρ)
    simp only [actA_kap] at h1
    rw [gcl_trR_val P Bs hpl hk2 e he] at h1
    have h1' : ((f ρ • trR P Bs e Θ ρ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q =
        f ρ * ((trR P Bs e Θ ρ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q := rfl
    rw [h1', gcl_trR_val P Bs hpl hk2 e he] at h1
    have hw := gcl_wR_ne P hx'.2
    have h2 : ((wR P.k P.TT x.2 : ℝ) : ℂ) * inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (NF.radR P.k P.r Bs.z Bs.z' Bs.μsec
          (((d.κ f).1 Θ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x)) =
        ((wR P.k P.TT x.2 : ℝ) : ℂ) * (f ρ * inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (NF.radR P.k P.r Bs.z Bs.z' Bs.μsec
          (Θ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x))) := by
      have h3 : f ρ * (((wR P.k P.TT x.2 : ℝ) : ℂ) * inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (NF.radR P.k P.r Bs.z Bs.z' Bs.μsec
          (Θ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x))) = ((wR P.k P.TT x.2 : ℝ) : ℂ) * (f ρ * inner ℂ (B.hsVec (e ρ x.2))
          (B.hsVec (NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (Θ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x))) := by ring
      exact h1.trans h3
    exact mul_left_cancel₀ hw h2

  have hexp : ∀ (Θ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (x : (Fin P.r → ℂ) × ℂ), x ∈ NF.QR P.k P.r Bs.z Bs.z' →
      NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (Θ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x =
        ∑ σ, inner ℂ (B.hsVec (e σ x.2)) (B.hsVec (NF.radR P.k P.r Bs.z Bs.z' Bs.μsec
          (Θ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x)) • e σ x.2 := by
    intro Θ x hx
    exact (he.2 x.2 ((hQR x).1 hx).2).2.2 _ ((hMem _ Θ.2).2.1 x hx)
  have hON : ∀ ζ ∈ Ann P, ∀ ρ σ, inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec (e σ ζ)) = if ρ = σ then (1 : ℂ) else 0 :=
    fun ζ hζ => (he.2 ζ hζ).2.1

  have hΨfix : ∀ σ, (d.κ (fun ρ => if ρ = σ then (1 : ℂ) else 0)).1 (Ψ σ) = Ψ σ := by
    intro σ
    apply Subtype.ext
    apply Formalism.FourierDecayAlt.P.radical_reduction_injective Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hRB _ (Subtype.property _) _
      (Ψ σ).2
    funext x
    by_cases hx : x ∈ NF.QR P.k P.r Bs.z Bs.z'
    · rw [hexp _ x hx, hexp (Ψ σ) x hx]
      refine Finset.sum_congr rfl fun ρ _ => ?_
      rw [hKv _ _ ρ x hx, hΨv σ x hx, hON x.2 ((hQR x).1 hx).2 ρ σ]
      split_ifs <;> simp
    · simp only [NF.radR, Set.indicator_of_notMem hx]

  obtain ⟨n, Aj, hAs, hAeq⟩ := hT
  have hloc : ∀ (Φ₁ Φ₂ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (x₁ x₂ : (Fin P.r → ℂ) × ℂ),
      x₁ ∈ NF.QR P.k P.r Bs.z Bs.z' → x₂ ∈ NF.QR P.k P.r Bs.z Bs.z' → x₁.2 = x₂.2 →
      (fun ζ => NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (Φ₁ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (x₁.1, ζ)) =ᶠ[nhds x₁.2]
        (fun ζ => NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (Φ₂ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (x₂.1, ζ)) →
      NF.radR P.k P.r Bs.z Bs.z' Bs.μsec ((T Φ₁ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x₁ =
        NF.radR P.k P.r Bs.z Bs.z' Bs.μsec ((T Φ₂ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x₂ := by
    intro Φ₁ Φ₂ x₁ x₂ h₁ h₂ h12 hev
    rw [hAeq Φ₁ x₁ h₁, hAeq Φ₂ x₂ h₂, ← h12]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [(hev.iteratedFDeriv ℝ j).eq_of_nhds]

  let c1 : Fin P.r → ℂ := fun _ => 1
  have hc1 : c1 ∈ OmX P.r := fun _ => one_ne_zero
  let α : M.Ty P → ℂ → ℂ := fun ρ ζ => inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec (NF.radR P.k P.r Bs.z Bs.z' Bs.μsec
    ((T (Ψ ρ) : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c1, ζ)))
  have hsliceΘ : ∀ (Θ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (c : Fin P.r → ℂ), c ∈ OmX P.r →
      ContDiffOn ℝ ∞ (fun ζ => NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (Θ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c, ζ)) (Ann P) := by
    intro Θ c hc
    exact (hMem _ Θ.2).1.comp (contDiffOn_const.prodMk contDiffOn_id) fun ζ hζ => (hQR (c, ζ)).2 ⟨hc, hζ⟩
  have hαs : ∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (α ρ) (Ann P) := by
    intro ρ
    exact (Formalism.FourierDecayAlt.P.CutMP.En.hsVec_contDiff.comp_contDiffOn (he.1 ρ)).inner ℂ
      (Formalism.FourierDecayAlt.P.CutMP.En.hsVec_contDiff.comp_contDiffOn (hsliceΘ _ c1 hc1))
  have hTΨ : ∀ ρ σ (x : (Fin P.r → ℂ) × ℂ), x ∈ NF.QR P.k P.r Bs.z Bs.z' →
      inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (NF.radR P.k P.r Bs.z Bs.z' Bs.μsec
        ((T (Ψ σ) : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x)) =
        if σ = ρ then α ρ x.2 else 0 := by
    intro ρ σ x hx
    have h1 := hKv (fun ρ' => if ρ' = σ then (1 : ℂ) else 0) (T (Ψ σ)) ρ x hx
    rw [← hκ, hΨfix] at h1
    by_cases hσ : σ = ρ
    · subst hσ
      rw [if_pos rfl]
      have hx1 : ((c1, x.2) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := (hQR _).2 ⟨hc1, ((hQR x).1 hx).2⟩
      have heq := hloc (Ψ σ) (Ψ σ) x (c1, x.2) hx hx1 rfl (by
        filter_upwards [hUo.mem_nhds ((hQR x).1 hx).2] with ζ hζ
        rw [hΨv σ (x.1, ζ) ((hQR (x.1, ζ)).2 ⟨((hQR x).1 hx).1, hζ⟩), hΨv σ (c1, ζ) ((hQR (c1, ζ)).2 ⟨hc1, hζ⟩)])
      show _ = inner ℂ (B.hsVec (e σ x.2)) (B.hsVec (NF.radR P.k P.r Bs.z Bs.z' Bs.μsec
        ((T (Ψ σ) : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c1, x.2)))
      rw [heq]
    · rw [if_neg hσ]
      rw [if_neg (Ne.symm hσ), zero_mul] at h1
      exact h1

  let wc : ℂ → ℂ := fun ζ => ((wR P.k P.TT ζ : ℝ) : ℂ)
  have hwc : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) wc (Ann P) := gcl_wRc_smooth P
  obtain ⟨hdw, hdbw⟩ := gcl_dZ_smooth hUo hwc
  refine ⟨fun ρ ζ => α ρ ζ - (a * NF.dZ wc ζ + b * NF.dZb wc ζ) * (wc ζ)⁻¹, fun ρ => ?_, ?_⟩
  · exact (hαs ρ).sub (((contDiffOn_const.mul hdw).add (contDiffOn_const.mul hdbw)).mul
      (hwc.inv fun ζ hζ => gcl_wR_ne P hζ))
  intro Φ ρ q
  have hx0 : q.1 ∈ NF.QR P.k P.r Bs.z Bs.z' := (hQR _).2 ⟨q.2.1, q.2.2⟩
  let f : M.Ty P → ℂ → ℂ := fun σ ζ => inner ℂ (B.hsVec (e σ ζ))
    (B.hsVec (NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (q.1.1, ζ)))
  have hfs : ∀ σ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f σ) (Ann P) := fun σ =>
    (Formalism.FourierDecayAlt.P.CutMP.En.hsVec_contDiff.comp_contDiffOn (he.1 σ)).inner ℂ
      (Formalism.FourierDecayAlt.P.CutMP.En.hsVec_contDiff.comp_contDiffOn (hsliceΘ Φ q.1.1 q.2.1))
  have hfs' : ∀ σ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f σ)
      {ζ : ℂ | Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ} := fun σ => by rw [hUeq]; exact hfs σ
  let Θ : M.Ty P → Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' := fun σ =>
    ⟨NF.mulZ P.k P.r Bs.z Bs.z' (f σ) (Ψ σ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)), Formalism.FourierDecayAlt.P.NFx4.mulZ_mem (hfs' σ) (Ψ σ).2⟩
  have hB : NF.radR P.k P.r Bs.z Bs.z' Bs.μsec ((T Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1 =
      NF.radR P.k P.r Bs.z Bs.z' Bs.μsec ((T (∑ σ, Θ σ) : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1 := by
    refine hloc Φ (∑ σ, Θ σ) q.1 q.1 hx0 hx0 rfl ?_
    filter_upwards [hUo.mem_nhds q.2.2] with ζ hζ
    have hxζ : ((q.1.1, ζ) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := (hQR _).2 ⟨q.2.1, hζ⟩
    rw [Submodule.coe_sum, gcl_radR_sum, hexp Φ _ hxζ]
    refine Finset.sum_congr rfl fun σ _ => ?_
    show _ = NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (NF.mulZ P.k P.r Bs.z Bs.z' (f σ) (Ψ σ : Q.Fn P.k P.r (Wq →L[ℂ] Wp))) (q.1.1, ζ)
    rw [Formalism.FourierDecayAlt.P.NFRO.radR_mulZ hRB (f σ) (Ψ σ).2 hxζ, hΨv σ _ hxζ]
  have hC : ∀ σ, ((T (Θ σ) : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) =
      NF.mulZ P.k P.r Bs.z Bs.z' (f σ) ((T (Ψ σ) : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) +
        NF.mulZ P.k P.r Bs.z Bs.z' (fun ζ => a * NF.dZ (f σ) ζ + b * NF.dZb (f σ) ζ) (Ψ σ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) :=
    fun σ => Formalism.FourierDecayAlt.P.radical_order_zero Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hRB T a b hIR ha hb (f σ)
      (hfs' σ) (Ψ σ) (Θ σ) rfl
  have hterm : ∀ σ, inner ℂ (B.hsVec (e ρ q.1.2)) (B.hsVec (NF.radR P.k P.r Bs.z Bs.z' Bs.μsec
      ((T (Θ σ) : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1)) =
        f σ q.1.2 * (if σ = ρ then α ρ q.1.2 else 0) +
          (a * NF.dZ (f σ) q.1.2 + b * NF.dZb (f σ) q.1.2) * (if ρ = σ then (1 : ℂ) else 0) := by
    intro σ
    rw [hC σ, Formalism.FourierDecayAlt.P.NFRO.radR_add, Formalism.FourierDecayAlt.P.NFRO.radR_mulZ hRB _ (T (Ψ σ)).2 hx0,
      Formalism.FourierDecayAlt.P.NFRO.radR_mulZ hRB _ (Ψ σ).2 hx0, hΨv σ _ hx0, gcl_hsVec_add, gcl_hsVec_smul, gcl_hsVec_smul,
      inner_add_right, inner_smul_right, inner_smul_right, hTΨ ρ σ q.1 hx0, hON q.1.2 q.2.2 ρ σ]
  have hval : inner ℂ (B.hsVec (e ρ q.1.2)) (B.hsVec (NF.radR P.k P.r Bs.z Bs.z' Bs.μsec
      ((T Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1)) =
        f ρ q.1.2 * α ρ q.1.2 + (a * NF.dZ (f ρ) q.1.2 + b * NF.dZb (f ρ) q.1.2) := by

    rw [hB, map_sum, Submodule.coe_sum, gcl_radR_sum, gcl_hsVec_sum, inner_sum]
    rw [Finset.sum_congr rfl fun σ _ => hterm σ]
    simp [Finset.sum_add_distrib, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']

  let G : MA.E P.r → ℂ := fun x => wc x.2 * inner ℂ (B.hsVec (e ρ x.2))
    (B.hsVec (NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x))
  have hGev : MA.ext ((trR P Bs e Φ ρ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) =ᶠ[nhds q.1] G := by
    filter_upwards [(MA.Qset_open P.r P.TT).mem_nhds q.2] with x hx
    simp only [MA.ext, dif_pos hx]
    exact gcl_trR_val P Bs hpl hk2 e he Φ ρ ⟨x, hx⟩
  have hGs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G (NF.QR P.k P.r Bs.z Bs.z') :=
    (hwc.comp contDiff_snd.contDiffOn fun x hx => ((hQR x).1 hx).2).mul
      ((Formalism.FourierDecayAlt.P.CutMP.En.hsVec_contDiff.comp_contDiffOn
        ((he.1 ρ).comp contDiff_snd.contDiffOn fun x hx => ((hQR x).1 hx).2)).inner ℂ
        (Formalism.FourierDecayAlt.P.CutMP.En.hsVec_contDiff.comp_contDiffOn (hMem _ Φ.2).1))
  have hGd : DifferentiableAt ℝ G q.1 :=
    (hGs.differentiableOn (by simp)).differentiableAt (hQRo.mem_nhds hx0)
  obtain ⟨hw1, hw2⟩ := gcl_wirt_slice G q.1 hGd
  have hsl : (fun ζ => G (q.1.1, ζ)) = fun ζ => wc ζ * f ρ ζ := rfl
  rw [hsl] at hw1 hw2
  have hwd : DifferentiableAt ℝ wc q.1.2 :=
    (hwc.differentiableOn (by simp)).differentiableAt (hUo.mem_nhds q.2.2)
  have hfd : DifferentiableAt ℝ (f ρ) q.1.2 :=
    ((hfs ρ).differentiableOn (by simp)).differentiableAt (hUo.mem_nhds q.2.2)
  obtain ⟨hm1, hm2⟩ := Formalism.FourierDecayAlt.P.NFRO.wirt_mul hwd hfd
  rw [gcl_trR_val P Bs hpl hk2 e he (T Φ) ρ q, gcl_trR_val P Bs hpl hk2 e he Φ ρ q, hval,
    Formalism.FourierDecayAlt.P.MAx1.An.wirt_congr _ hGev, Formalism.FourierDecayAlt.P.MAx1.An.wirt_congr _ hGev, hw1, hw2, hm1, hm2]
  have hne : wc q.1.2 ≠ 0 := gcl_wR_ne P q.2.2
  show wc q.1.2 * _ = _
  field_simp
  ring

end core

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end
end
