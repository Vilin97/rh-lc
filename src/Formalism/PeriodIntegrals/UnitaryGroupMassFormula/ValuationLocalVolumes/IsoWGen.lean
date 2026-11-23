module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.FibPOfDual
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.GramAugT
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.IsoExtOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.GramInvOHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.NormOneUnitFixedPoints
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.TrOntoHolds
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Formalism.LocalRingCardinality.SpanPowerMembership.Adelic
public import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Linter.HaveILetI
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol
import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.LevelIntersectParabolic
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.MeasureImageCosets
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVBadTOf

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.QuadRoot

section

@[expose] public section

noncomputable section

open Polynomial IsLocalRing

namespace PI.OmVf

theorem quad_root {R : Type*} [CommRing R] [HenselianLocalRing R] (A B K : R) (hA : A ∈ maximalIdeal R)
    (hB : IsUnit B) : ∃ s : R, A * s ^ 2 + B * s + K = 0 := by
  obtain ⟨u, hu⟩ := hB.exists_right_inv
  have haK : A * u * u * K ∈ maximalIdeal R := by
    have h1 : A * u * u * K = A * (u * u * K) := by ring
    rw [h1]; exact Ideal.mul_mem_right _ _ hA
  obtain ⟨w, hwr, hwm⟩ := HenselianLocalRing.is_henselian
    (X ^ 2 + X + Polynomial.C (A * u * u * K)) (by monicity!) 0
    (by simpa using haK) (by simp)
  have hw : w ^ 2 + w + A * u * u * K = 0 := by simpa using hwr
  have hwm' : w ∈ maximalIdeal R := by simpa using hwm
  have hunit : IsUnit (1 + w) := by
    by_contra hn
    have h1 : 1 + w ∈ maximalIdeal R := (mem_maximalIdeal _).mpr hn
    have h2 : (1 : R) ∈ maximalIdeal R := by
      have e : (1 : R) = (1 + w) - w := by ring
      rw [e]; exact Ideal.sub_mem _ h1 hwm'
    exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr h2)
  obtain ⟨v, hv⟩ := hunit.exists_right_inv
  refine ⟨-(u * K * v), ?_⟩
  linear_combination K * v ^ 2 * hw - K * (2 - v + ((1 + w) * v - 1)) * hv - K * v * hu

end PI.OmVf
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.Root

section

@[expose] public section

noncomputable section

namespace PI.OmVf

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU PI.OmVd IsLocalRing
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem exists_integral_root_of_quadratic (β γ ν : Fv F v) (hβ : β ∈ v.adicCompletionIntegers F) (hγ : γ ∈ v.adicCompletionIntegers F)
    (hγm : Valued.v γ < 1) (hν : ν ∈ v.adicCompletionIntegers F) :
    ∃ s ∈ v.adicCompletionIntegers F, β + (1 - γ * β) * s - γ * (1 - γ * β) * ν * s ^ 2 = 0 := by
  set b : v.adicCompletionIntegers F := ⟨β, hβ⟩
  set g : v.adicCompletionIntegers F := ⟨γ, hγ⟩
  set m : v.adicCompletionIntegers F := ⟨ν, hν⟩
  have hg : g ∈ maximalIdeal (v.adicCompletionIntegers F) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨w, hw⟩
    have h1 : ((w⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) * g = 1 := by
      rw [← hw]; simp
    have h2 : ((((w⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) : Fv F v)) * γ = 1 := by
      have := congrArg (fun x : v.adicCompletionIntegers F => (x : Fv F v)) h1
      simpa using this
    have h3 : Valued.v ((((w⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) : Fv F v)) ≤ 1 :=
      (HeightOneSpectrum.mem_adicCompletionIntegers (K := F) (v := v)).1 (Subtype.property _)
    have h4 := congrArg Valued.v h2
    rw [map_mul, map_one] at h4
    have : Valued.v ((((w⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) : Fv F v)) * Valued.v γ < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_left' h3) hγm
    rw [h4] at this
    exact lt_irrefl _ this
  have hu : IsUnit (1 - g * b) :=
    IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ ((maximalIdeal _).mul_mem_right b hg)
  open scoped WithZero Topology in
  open HeightOneSpectrum Filter in
  have hcomplete : IsAdicComplete (maximalIdeal (v.adicCompletionIntegers F)) (v.adicCompletionIntegers F) := by
    let R := 𝓞 F
    let L := F
    let w := v
    let Ow := v.adicCompletionIntegers F
    let Lw := v.adicCompletion F
    have lt_one_iff_le (g : ℤᵐ⁰) : g < 1 ↔ g ≤ WithZero.exp (-1 : ℤ) := by
      induction g using WithZero.expRecOn with
      | zero => simp
      | exp a => rw [← WithZero.exp_zero, WithZero.exp_lt_exp, WithZero.exp_le_exp]; omega

    have v_algebraMap (l : L) : Valued.v (algebraMap L Lw l) = w.valuation L l :=
      valuedAdicCompletion_eq_valuation' w l

    have exists_unif : ∃ π : Ow, Valued.v (π : Lw) = WithZero.exp (-1 : ℤ) := by
      obtain ⟨π, hπ⟩ := w.valuation_exists_uniformizer L
      have h : Valued.v (algebraMap L Lw π) = WithZero.exp (-1 : ℤ) := by
        rw [v_algebraMap, hπ]
      refine ⟨⟨algebraMap L Lw π, ?_⟩, h⟩
      rw [mem_adicCompletionIntegers, h]
      exact ((lt_one_iff_le _).2 le_rfl).le

    have mem_max_iff (x : Ow) :
        x ∈ IsLocalRing.maximalIdeal Ow ↔ Valued.v (x : Lw) < 1 := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        adicCompletionIntegers.isUnit_iff_valued_eq_one]
      have : Valued.v (x : Lw) ≤ 1 := (mem_adicCompletionIntegers R L w).1 x.2
      exact ⟨fun h => lt_of_le_of_ne this h, fun h => h.ne⟩

    have max_eq_span {π : Ow} (hπ : Valued.v (π : Lw) = WithZero.exp (-1 : ℤ)) :
        IsLocalRing.maximalIdeal Ow = Ideal.span {π} := by
      ext x
      rw [mem_max_iff, Ideal.mem_span_singleton, lt_one_iff_le, ← hπ]
      exact (adicCompletionIntegers.integers L w).le_iff_dvd

    have mem_max_pow_iff {π : Ow} (hπ : Valued.v (π : Lw) = WithZero.exp (-1 : ℤ)) (x : Ow) (n : ℕ) :
        x ∈ IsLocalRing.maximalIdeal Ow ^ n ↔ Valued.v (x : Lw) ≤ Valued.v (π : Lw) ^ n := by
      rw [max_eq_span hπ, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      have := (adicCompletionIntegers.integers L w).le_iff_dvd (x := x) (y := π ^ n)
      rw [map_pow, map_pow] at this
      exact this.symm

    obtain ⟨π, hπ⟩ := exists_unif
    have hπ1 : ‖(π : Lw)‖ < 1 := by
      rw [Valued.toNormedField.norm_lt_one_iff]
      exact (lt_one_iff_le _).2 hπ.le
    have hπ0 : (π : Lw) ≠ 0 := by
      intro h
      rw [h, map_zero] at hπ
      exact WithZero.exp_ne_zero hπ.symm
    have hr0 : 0 < ‖(π : Lw)‖ := norm_pos_iff.mpr hπ0
    have key : ∀ (n : ℕ) (x y : Ow),
        x ≡ y [SMOD ((IsLocalRing.maximalIdeal Ow) ^ n • ⊤ : Submodule Ow Ow)] ↔
          ‖(x : Lw) - y‖ ≤ ‖(π : Lw)‖ ^ n := by
      intro n x y
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, mem_max_pow_iff hπ,
        ← map_pow, ← Valued.toNormedField.norm_le_iff]
      simp only [norm_pow]
      rfl
    refine { haus' := ?_, prec' := ?_ }
    · intro x hx
      have h : ∀ n : ℕ, ‖(x : Lw)‖ ≤ ‖(π : Lw)‖ ^ n := fun n => by
        simpa using (key n x 0).mp (hx n)
      have hx0 : ‖(x : Lw)‖ ≤ 0 :=
        ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hπ1) h
      exact Subtype.ext (norm_le_zero_iff.mp hx0)
    · intro f hf
      have hc : ∀ n : ℕ, dist (f n : Lw) (f (n + 1)) ≤ 1 * ‖(π : Lw)‖ ^ n := fun n => by
        rw [dist_eq_norm, one_mul]
        exact (key n _ _).mp (hf n.le_succ)
      obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric _ 1 hπ1 hc)
      have hl1 : ‖l‖ ≤ 1 := le_of_tendsto' hl.norm (fun n =>
        Valued.toNormedField.norm_le_one_iff.mpr (f n).2)
      refine ⟨⟨l, Valued.toNormedField.norm_le_one_iff.mp hl1⟩, fun n => ?_⟩
      rw [key]
      have ht : Tendsto (fun m => ‖(f n : Lw) - f m‖) atTop (𝓝 ‖(f n : Lw) - l‖) :=
        (tendsto_const_nhds.sub hl).norm
      exact le_of_tendsto ht (eventually_atTop.mpr ⟨n, fun m hm => (key n _ _).mp (hf hm)⟩)

  letI := hcomplete
  haveI : HenselianLocalRing (v.adicCompletionIntegers F) := ⟨fun f hf a h₁ h₂ => HenselianRing.is_henselian f hf a h₁ (h₂.map _)⟩
  obtain ⟨s, hs⟩ := PI.OmVf.quad_root (-(g * (1 - g * b) * m)) (1 - g * b) b
    (neg_mem ((maximalIdeal _).mul_mem_right m ((maximalIdeal _).mul_mem_right _ hg))) hu
  refine ⟨s, s.property, ?_⟩
  have := congrArg (fun x : v.adicCompletionIntegers F => (x : Fv F v)) hs
  simp only [b, g, m] at this
  push_cast at this
  linear_combination this
end PI.OmVf
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.IsoWGen

section

@[expose] public section

noncomputable section

namespace PI.OmVf

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU PI.OmVd IsLocalRing
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem isoW_gen {a : ℕ} (Y : TupV (E := E) v n a) (z : Fin a) (γ : Fv F v)
    (hγ : γ ∈ v.adicCompletionIntegers F) (hγm : Valued.v γ < 1)
    (hz : ∀ i, gramR (Fv F v) σ J Y i z = if i = z then sc (E := E) v γ else 0)
    (hPD : PrimDual σ J ψ v Λ a)
    (hTS : ∃ S : Matrix (Fin (a + 1)) (Fin (a + 1)) (Fv F v ⊗[F] E), (∀ i j, S i j ∈ OEv (E := E) v) ∧
      bordM v (gramR (Fv F v) σ J Y) z * S = 1) :
    IsoW σ J ψ v Λ a Y := by
  classical
  intro hG
  obtain ⟨hS, hL, hSD, hUn, -, hYp⟩ := hG
  have hcm := hS.1
  have hJ : ∀ i j, σ (J j i) = J i j := hS.2.1.1
  have hconj : ∀ x y, sigR (Fv F v) σ (hR (Fv F v) σ J x y) = hR (Fv F v) σ J y x :=
    fun x y => PI.OmLocU.Orb.hR_conj σ J v hcm hJ x y
  have hsc : ∀ r : Fv F v, sigR (Fv F v) σ (sc (E := E) v r) = sc (E := E) v r :=
    fun r => PI.OmLocU.NormOneUnitFixedPoints.sigR_sc' σ v r
  set G := gramR (Fv F v) σ J Y with hGdef

  obtain ⟨S, hSi, hTS1⟩ := hTS
  have hGi : ∀ i j, G i j ∈ OEv (E := E) v := fun i j =>
    PI.OmLocU.hR_mem_oEv σ J v Λ hSD (hYp.1 i) (hYp.1 j)
  have hBi : ∀ i j, bordM v G z i j ∈ OEv (E := E) v := by
    intro i j
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => simp only [bordM, Fin.snoc_last]; exact oEv_zero v
      | cast j =>
        simp only [bordM, Fin.snoc_last, Fin.snoc_castSucc]
        split_ifs
        · exact oEv_one v
        · exact oEv_zero v
    | cast i =>
      induction j using Fin.lastCases with
      | last =>
        simp only [bordM, Fin.snoc_last, Fin.snoc_castSucc]
        split_ifs
        · exact oEv_one v
        · exact oEv_zero v
      | cast j => simp only [bordM, Fin.snoc_castSucc]; exact hGi i j
  refine ⟨bordM v G z, ⟨S.det, det_int v _ hSi, det_int v _ hBi, ?_⟩, ?_⟩
  · rw [← Matrix.det_mul, hTS1, Matrix.det_one]
  intro X hX hXY
  obtain ⟨W, hW, hWd⟩ := hPD hS hSD hUn hL X hX
  set g := sc (E := E) v γ with hg
  have hgO : g ∈ OEv (E := E) v := PI.OmLocU.NormOneUnitFixedPoints.sc_mem v hγ
  have hXz : ∀ i, hR (Fv F v) σ J (X i) (X z) = if i = z then g else 0 := by
    intro i
    have := congrFun (congrFun hXY i) z
    simp only [gramR] at this
    rw [this]; exact hz i
  set w0 := W z with hw0
  have hw0L : w0 ∈ latLoc (E := E) v Λ := hW z
  have hXw0 : ∀ i, hR (Fv F v) σ J (X i) w0 = if i = z then 1 else 0 := fun i => (hWd i z).1
  have hw0X : ∀ i, hR (Fv F v) σ J w0 (X i) = if i = z then 1 else 0 := fun i => (hWd i z).2
  set y := X z + (-g) • w0 with hy
  have hyL : y ∈ latLoc (E := E) v Λ :=
    Submodule.add_mem _ (hX.1 z) (PI.OmLocU.Orb.oSmul v Λ hL _ (oEv_neg v hgO) _ hw0L)
  have hXy : ∀ i, hR (Fv F v) σ J (X i) y = 0 := by
    intro i
    rw [hy, hAddR, hSmulR, hXz, hXw0]
    split_ifs <;> ring
  have hyX : ∀ i, hR (Fv F v) σ J y (X i) = 0 := by
    intro i; rw [← hconj, hXy, map_zero]
  set b := hR (Fv F v) σ J w0 w0 with hb
  have hbO : b ∈ OEv (E := E) v := PI.OmLocU.hR_mem_oEv σ J v Λ hSD hw0L hw0L
  obtain ⟨β, hβ, hbβ⟩ := PI.OmLocU.NormOneUnitFixedPoints.fix_int_sc σ v hcm hbO (hconj w0 w0)
  have h1 : hR (Fv F v) σ J w0 y = 1 + (-g) * b := by
    rw [hy, hAddR, hSmulR, hw0X, if_pos rfl]
  have h2 : hR (Fv F v) σ J y w0 = 1 + (-g) * b := by
    rw [← hconj, h1, map_add (f := _), map_one, map_mul, map_neg, hg, hsc, hconj]
  have h3 : hR (Fv F v) σ J y y = (-g) * (1 + (-g) * b) := by
    rw [hy, hAddR, hSmulR, ← hy, hyX, h2, zero_add]

  obtain ⟨θ, hθO, hθ⟩ := PI.OmLocU.Red.trOnto_holds σ J ψ v hS hUn 1 (oEv_one v) (map_one _)
  have hinv : ∀ x, sigR (Fv F v) σ (sigR (Fv F v) σ x) = x := PI.OmLocU.Orb.sigR_invol σ v hcm
  have hNO : sigR (Fv F v) σ θ * θ ∈ OEv (E := E) v := by
    refine oEv_mul v ?_ hθO
    have := hθ ▸ (oEv_one (E := E) v)
    have e : sigR (Fv F v) σ θ = (θ + sigR (Fv F v) σ θ) - θ := by ring
    rw [e]
    exact oEv_add v this (oEv_neg v hθO)
  have hNf : sigR (Fv F v) σ (sigR (Fv F v) σ θ * θ) = sigR (Fv F v) σ θ * θ := by
    rw [map_mul, hinv, mul_comm]
  obtain ⟨ν, hν, hNν⟩ := PI.OmLocU.NormOneUnitFixedPoints.fix_int_sc σ v hcm hNO hNf
  obtain ⟨s, hsO, hs⟩ := exists_integral_root_of_quadratic v β γ ν hβ hγ hγm hν
  set t := sc (E := E) v s * θ with ht
  have htO : t ∈ OEv (E := E) v := oEv_mul v (PI.OmLocU.NormOneUnitFixedPoints.sc_mem v hsO) hθO
  have hσt : sigR (Fv F v) σ t = sc (E := E) v s * sigR (Fv F v) σ θ := by
    rw [ht, map_mul, hsc]
  set w := w0 + t • y with hw
  have hwL : w ∈ latLoc (E := E) v Λ :=
    Submodule.add_mem _ hw0L (PI.OmLocU.Orb.oSmul v Λ hL _ htO _ hyL)
  have hXw : ∀ i, hR (Fv F v) σ J (X i) w = if i = z then 1 else 0 := by
    intro i; rw [hw, hAddR, hSmulR, hXy, hXw0, mul_zero, add_zero]
  have hwX : ∀ i, hR (Fv F v) σ J w (X i) = if i = z then 1 else 0 := by
    intro i; rw [hw, hAddL, hSmulL, hyX, hw0X, mul_zero, add_zero]
  have E0 : hR (Fv F v) σ J w w = b + t * hR (Fv F v) σ J w0 y +
      (sigR (Fv F v) σ t * hR (Fv F v) σ J y w0 + sigR (Fv F v) σ t * (t * hR (Fv F v) σ J y y)) := by
    rw [hw, hAddL, hAddR, hAddR, hSmulR, hSmulL, hSmulL, hSmulR]
  have key : sc (E := E) v (β + (1 - γ * β) * s - γ * (1 - γ * β) * ν * s ^ 2) = 0 := by
    rw [hs]; simp [sc]
  have keyE : sc (E := E) v β + (1 - g * sc (E := E) v β) * sc (E := E) v s -
      g * (1 - g * sc (E := E) v β) * sc (E := E) v ν * sc (E := E) v s ^ 2 = 0 := by
    rw [← key, hg]
    simp only [PI.OmLocU.NormOneUnitFixedPoints.sc_eq, map_add (f := _), map_sub, map_mul, map_one, map_pow]
  have hww : hR (Fv F v) σ J w w = 0 := by
    rw [E0, h1, h2, h3, hσt, hbβ, ht]
    linear_combination keyE + ((1 - g * sc (E := E) v β) * sc (E := E) v s) * hθ -
      (g * (1 - g * sc (E := E) v β) * sc (E := E) v s ^ 2) * hNν
  refine ⟨w, hwL, ?_⟩
  rw [gram_augT σ J v X w z hXw hwX hww, hXY]

end PI.OmVf
end
end
end
