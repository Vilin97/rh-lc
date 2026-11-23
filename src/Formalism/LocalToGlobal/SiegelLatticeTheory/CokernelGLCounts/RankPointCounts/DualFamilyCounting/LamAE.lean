module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSIntWittSt
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.RingTheory.LocalRing.Defs
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol
import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.LevelIntersectParabolic
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Lattice
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSIntWittOEv
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSKfOrb
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensTop
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSIntWittLam

section

@[expose] public section

noncomputable section

namespace Formalism.L2.SG.Pf.NcS.IntWittPf

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Filter
open scoped TensorProduct

theorem norm_id {S : Type} [CommRing S] (B p q a b D Θ : S) (h : Θ ^ 2 = D) :
    (B - (p - q * Θ) * (a + b * Θ)) * (B - (p + q * Θ) * (a - b * Θ)) =
      (B - p * a + q * b * D) ^ 2 - D * (q * a - p * b) ^ 2 := by
  linear_combination (q * b * (2 * (B - p * a) + q * b * (Θ ^ 2 + D)) - (p * b - q * a) ^ 2) * h

theorem norm_one {S : Type} [CommRing S] (p q D Θ : S) (h : Θ ^ 2 = D) :
    (p + q * Θ) * (p - q * Θ) = p ^ 2 - D * q ^ 2 := by
  linear_combination (-q ^ 2) * h

theorem core_loc {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S] (ι : R →+* S) (s : S →+* S)
    (O : Subring S) (hιO : ∀ r, ι r ∈ O) (Θ : S) (hΘO : Θ ∈ O) (D Bt P Q a b : R)
    (hΘ : Θ ^ 2 = ι D) (hsΘ : s Θ = -Θ) (hsι : ∀ r, s (ι r) = ι r) (hPQ : P ^ 2 - D * Q ^ 2 = 1)
    (Bi K i4 : R) (hB : Bt * Bi = 1) (hK : Q * D * K = 1) (h4 : (4 : R) * i4 = 1) :
    ∃ lam ∈ O, lam * s lam = 1 ∧ ∃ c' ∈ O, (ι Bt - s lam * (ι a + ι b * Θ)) * c' = 1 := by
  let pp : Fin 4 → R := ![1, -1, P, -P]
  let qq : Fin 4 → R := ![0, 0, Q, -Q]
  let f : Fin 4 → R := fun i => (Bt - pp i * a + qq i * b * D) ^ 2 - D * (qq i * a - pp i * b) ^ 2
  have ef0 : f 0 = (Bt - a) ^ 2 - D * b ^ 2 := by simp [f, pp, qq] <;> ring
  have ef1 : f 1 = (Bt + a) ^ 2 - D * b ^ 2 := by simp [f, pp, qq] <;> ring
  have ef2 : f 2 = (Bt - P * a + Q * b * D) ^ 2 - D * (Q * a - P * b) ^ 2 := by simp [f, pp, qq] <;> ring
  have ef3 : f 3 = (Bt + P * a - Q * b * D) ^ 2 - D * (Q * a - P * b) ^ 2 := by simp [f, pp, qq] <;> ring
  have hspanTop : Ideal.span (Set.range f) = ⊤ := by
    have mem : ∀ i, f i ∈ Ideal.span (Set.range f) := fun i => Ideal.subset_span ⟨i, rfl⟩
    have ha : a ∈ Ideal.span (Set.range f) := by
      have : a = i4 * Bi * (f 1 - f 0) := by
        rw [ef1, ef0]; linear_combination (-a) * h4 + (-4 * i4 * a) * hB
      rw [this]; exact Ideal.mul_mem_left _ _ (sub_mem (mem 1) (mem 0))
    have hm : P * a - Q * D * b ∈ Ideal.span (Set.range f) := by
      have : P * a - Q * D * b = i4 * Bi * (f 3 - f 2) := by
        rw [ef3, ef2]
        linear_combination (-(P * a - Q * D * b)) * h4 + (-4 * i4 * (P * a - Q * D * b)) * hB
      rw [this]; exact Ideal.mul_mem_left _ _ (sub_mem (mem 3) (mem 2))
    have hb : b ∈ Ideal.span (Set.range f) := by
      have : b = K * (P * a - (P * a - Q * D * b)) := by linear_combination (-b) * hK
      rw [this]; exact Ideal.mul_mem_left _ _ (sub_mem (Ideal.mul_mem_left _ _ ha) hm)
    have hN : a ^ 2 - D * b ^ 2 ∈ Ideal.span (Set.range f) := by
      have : a ^ 2 - D * b ^ 2 = a * a - (D * b) * b := by ring
      rw [this]; exact sub_mem (Ideal.mul_mem_left _ _ ha) (Ideal.mul_mem_left _ _ hb)
    have hB2 : Bt ^ 2 ∈ Ideal.span (Set.range f) := by
      have : Bt ^ 2 = f 0 + (2 * Bt) * a - (a ^ 2 - D * b ^ 2) := by rw [ef0]; ring
      rw [this]; exact sub_mem (add_mem (mem 0) (Ideal.mul_mem_left _ _ ha)) hN
    rw [Ideal.eq_top_iff_one]
    have : (1 : R) = Bi ^ 2 * Bt ^ 2 := by linear_combination (-(Bt * Bi + 1)) * hB
    rw [this]; exact Ideal.mul_mem_left _ _ hB2
  have hnorm : ∀ i, pp i ^ 2 - D * qq i ^ 2 = 1 := by
    intro i; fin_cases i <;> simp [pp, qq] <;> linear_combination hPQ
  obtain ⟨i, hi⟩ : ∃ i, IsUnit (f i) := by
    by_contra H
    push Not at H
    have hle : Ideal.span (Set.range f) ≤ IsLocalRing.maximalIdeal R := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact (IsLocalRing.mem_maximalIdeal _).2 (H i)
    rw [hspanTop] at hle
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top (top_le_iff.1 hle)
  set L : S := ι (pp i) + ι (qq i) * Θ with hL
  set M : S := ι (pp i) - ι (qq i) * Θ with hM
  have hsL : s L = M := by rw [hL, hM, map_add (f := _), map_mul, hsι, hsι, hsΘ]; ring
  have hsM : s M = L := by rw [hL, hM, map_sub, map_mul, hsι, hsι, hsΘ]; ring
  have hLM : L * M = 1 := by
    rw [hL, hM, norm_one _ _ _ _ hΘ, ← map_pow, ← map_pow, ← map_mul, ← map_sub, hnorm i, map_one]
  set c : S := ι Bt - M * (ι a + ι b * Θ) with hc
  set sc : S := ι Bt - L * (ι a - ι b * Θ) with hsc
  have hcc : c * sc = ι (f i) := by
    rw [hc, hsc, hL, hM]
    simp only [f, map_sub, map_add (f := _), map_mul, map_pow]
    exact norm_id _ _ _ _ _ _ _ hΘ
  obtain ⟨u, hu⟩ := hi
  have hLO : L ∈ O := O.add_mem (hιO _) (O.mul_mem (hιO _) hΘO)
  have hMO : M ∈ O := O.sub_mem (hιO _) (O.mul_mem (hιO _) hΘO)
  refine ⟨L, hLO, by rw [hsL]; exact hLM, sc * ι ((u⁻¹ : Rˣ) : R), ?_, ?_⟩
  · exact O.mul_mem (O.sub_mem (hιO _) (O.mul_mem hLO (O.sub_mem (hιO _) (O.mul_mem (hιO _) hΘO)))) (hιO _)
  · rw [hsL, ← hc, ← mul_assoc, hcc, ← hu, ← map_mul, Units.mul_inv, map_one]

end Formalism.L2.SG.Pf.NcS.IntWittPf
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LamAE

section

@[expose] public section

noncomputable section

namespace Formalism.L2.SG.Pf.NcS.IntWittPf

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Filter
  Formalism.L2.SG.Pf.NcS.KfOrbPf
open scoped TensorProduct

theorem lamAE : LamAE := by
  intro F E _ _ _ _ _ σ hCM δ hδ hδ0
  classical
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have hσ : ∀ z, σ (σ z) = z := PI.VolStabS.sigma_invol σ hCM.2.2.2
  obtain ⟨x, hx⟩ : ∃ x : E, σ x ≠ x := by
    by_contra H
    push Not at H
    let w : InfinitePlace E := Classical.arbitrary _
    have hreal : ComplexEmbedding.IsReal w.embedding := by
      rw [ComplexEmbedding.isReal_iff]
      ext z
      rw [ComplexEmbedding.conjugate_coe_eq, ← Complex.star_def, ← hCM.2.2.2, H z]
    exact (InfinitePlace.not_isReal_iff_isComplex.2 (hCM.2.1.isComplex w)) (InfinitePlace.isReal_iff.2 hreal)
  set θ : E := x - σ x with hθdef
  have hσθ : σ θ = -θ := by rw [hθdef, map_sub, hσ]; ring
  have hθ0 : θ ≠ 0 := sub_ne_zero.2 (Ne.symm hx)
  have hind : ∀ p q : F, algebraMap F E p + algebraMap F E q * θ = 0 → p = 0 ∧ q = 0 := by
    intro p q h
    have h' := congrArg σ h
    rw [map_add (f := _), map_mul, AlgHom.commutes, AlgHom.commutes, hσθ, map_zero] at h'
    have hq : (2 : E) * (algebraMap F E q * θ) = 0 := by linear_combination h - h'
    have hq0 : q = 0 := by
      rcases mul_eq_zero.1 ((mul_eq_zero.1 hq).resolve_left two_ne_zero) with h1 | h1
      · exact (algebraMap F E).injective (by rw [h1, map_zero])
      · exact absurd h1 hθ0
    subst hq0
    rw [map_zero, zero_mul, add_zero] at h
    exact ⟨(algebraMap F E).injective (by rw [h, map_zero]), rfl⟩
  let v2 : Fin 2 → E := ![1, θ]
  have hli : LinearIndependent F v2 := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_two] at hg
    have e : algebraMap F E (g 0) + algebraMap F E (g 1) * θ = 0 := by
      rw [← hg]; simp [v2, Algebra.smul_def]
    obtain ⟨h0, h1⟩ := hind _ _ e
    intro i
    fin_cases i
    · exact h0
    · exact h1
  let b2 : Module.Basis (Fin 2) F E :=
    basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin, hCM.2.2.1])
  have hb2 : ∀ i, b2 i = v2 i := fun i => by
    simp only [b2, coe_basisOfLinearIndependentOfCardEqFinrank]
  have hdec : ∀ e : E, e = algebraMap F E (b2.repr e 0) + algebraMap F E (b2.repr e 1) * θ := by
    intro e
    conv_lhs => rw [← b2.sum_repr e]
    rw [Fin.sum_univ_two, hb2, hb2]
    simp [v2, Algebra.smul_def]

  have hfixF : ∀ e : E, σ e = e → e = algebraMap F E (b2.repr e 0) := by
    intro e he
    have h1 := hdec e
    have h2 := congrArg σ h1
    rw [he, map_add (f := _), map_mul, AlgHom.commutes, AlgHom.commutes, hσθ] at h2
    have h3 : algebraMap F E 0 + algebraMap F E (2 * b2.repr e 1) * θ = 0 := by
      rw [map_zero, map_mul, map_ofNat]; linear_combination h2 - h1
    have hq := (hind _ _ h3).2
    have hq' : b2.repr e 1 = 0 := (mul_eq_zero.1 hq).resolve_left two_ne_zero
    rw [hq', map_zero (algebraMap F E), zero_mul, add_zero] at h1
    exact h1
  have hθ2σ : σ (θ ^ 2) = θ ^ 2 := by rw [map_pow, hσθ, neg_sq]
  set d := b2.repr (θ ^ 2) 0 with hd_def
  have hd : θ ^ 2 = algebraMap F E d := hfixF _ hθ2σ
  have hd0 : d ≠ 0 := by
    intro h
    rw [h, map_zero] at hd
    exact hθ0 ((pow_eq_zero_iff two_ne_zero).1 hd)
  have hd1 : d ≠ 1 := by
    intro h
    rw [h, map_one] at hd
    have h1 : (θ - 1) * (θ + 1) = 0 := by linear_combination hd
    rcases mul_eq_zero.1 h1 with h | h
    · have e : θ = 1 := sub_eq_zero.1 h
      rw [e, map_one] at hσθ
      exact two_ne_zero (by linear_combination hσθ : (2 : E) = 0)
    · have e : θ = -1 := eq_neg_of_add_eq_zero_left h
      rw [e, map_neg, map_one] at hσθ
      exact two_ne_zero (by linear_combination -hσθ : (2 : E) = 0)
  set β0 := b2.repr δ 0 with hβ0_def
  have hδF : δ = algebraMap F E β0 := hfixF δ hδ
  have hβ0 : β0 ≠ 0 := by
    intro h
    rw [h, map_zero] at hδF
    exact hδ0 hδF
  have h1d : (1 - d) ≠ 0 := sub_ne_zero.2 (Ne.symm hd1)
  set Pc : F := (1 + d) / (1 - d) with hPc
  set Qc : F := 2 / (1 - d) with hQc_def
  have hQc : Qc ≠ 0 := div_ne_zero two_ne_zero h1d
  have hpq : Pc ^ 2 - d * Qc ^ 2 = 1 := by
    rw [hPc, hQc_def]
    field_simp
    ring
  filter_upwards [ev_int (F := F) d, ev_int (F := F) β0, ev_int (F := F) β0⁻¹, ev_int (F := F) Pc,
    ev_int (F := F) Qc, ev_int (F := F) (Qc * d)⁻¹, ev_int (F := F) (4 : F)⁻¹, ev_oev (F := F) θ, ev_crd_oev b2]
    with v hdv hβv hβiv hPv hQv hKv h4v hθv hcrd
  intro t ht
  let ι : v.adicCompletionIntegers F →+* Fv F v ⊗[F] E :=
    (algebraMap (Fv F v) (Fv F v ⊗[F] E)).comp (v.adicCompletionIntegers F).subtype
  have hιF : ∀ (y : F) (hy : algebraMap F (Fv F v) y ∈ v.adicCompletionIntegers F),
      ι ⟨_, hy⟩ = algebraMap F (Fv F v ⊗[F] E) y := by
    intro y hy
    show algebraMap (Fv F v) (Fv F v ⊗[F] E) (algebraMap F (Fv F v) y) = _
    rw [← IsScalarTower.algebraMap_apply]
  have hιO : ∀ r, ι r ∈ oevRing (E := E) v := by
    intro r
    show algebraMap (Fv F v) (Fv F v ⊗[F] E) (r : Fv F v) ∈ OEv (E := E) v
    rw [Algebra.algebraMap_eq_smul_one]
    exact oev_smul' v r.2 (oev_one v)
  have hsι : ∀ r, sigR (Fv F v) σ (ι r) = ι r := by
    intro r
    show sigR (Fv F v) σ (algebraMap (Fv F v) (Fv F v ⊗[F] E) (r : Fv F v)) = _
    simp [sigR, Algebra.TensorProduct.algebraMap_apply]
    rfl
  have hincl : ∀ y : F, inclR (F := F) (Fv F v) (algebraMap F E y) = algebraMap F (Fv F v ⊗[F] E) y :=
    fun y => (Algebra.TensorProduct.includeRight : E →ₐ[F] Fv F v ⊗[F] E).commutes y
  have hΘ : (inclR (F := F) (Fv F v) θ) ^ 2 = ι ⟨_, hdv⟩ := by
    rw [hιF, ← map_pow, hd, hincl]
  have hsΘ : sigR (Fv F v) σ (inclR (F := F) (Fv F v) θ) = -inclR (F := F) (Fv F v) θ := by
    simp [sigR, inclR, hσθ, TensorProduct.tmul_neg]
  have hcrd' := hcrd t ht
  have htd : t = ι ⟨_, hcrd' 0⟩ + ι ⟨_, hcrd' 1⟩ * inclR (F := F) (Fv F v) θ := by
    conv_lhs => rw [← (Algebra.TensorProduct.basis (Fv F v) b2).sum_repr t]
    rw [Fin.sum_univ_two, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.basis_apply, hb2, hb2]
    show _ = algebraMap (Fv F v) (Fv F v ⊗[F] E) (PI.VolStabS.PositiveNearLattice.crd b2 (Fv F v) t 0) +
      algebraMap (Fv F v) (Fv F v ⊗[F] E) (PI.VolStabS.PositiveNearLattice.crd b2 (Fv F v) t 1) * inclR (F := F) (Fv F v) θ
    simp only [PI.VolStabS.PositiveNearLattice.crd, Algebra.smul_def, v2, Matrix.cons_val_zero, Matrix.cons_val_one]
    simp [inclR]
  have hPQ : (⟨_, hPv⟩ : v.adicCompletionIntegers F) ^ 2 - ⟨_, hdv⟩ * ⟨_, hQv⟩ ^ 2 = 1 := by
    apply Subtype.ext
    show (algebraMap F (Fv F v) Pc) ^ 2 - algebraMap F (Fv F v) d * (algebraMap F (Fv F v) Qc) ^ 2 = 1
    rw [← map_pow, ← map_pow, ← map_mul, ← map_sub, hpq, map_one]
  have hB : (⟨_, hβv⟩ : v.adicCompletionIntegers F) * ⟨_, hβiv⟩ = 1 := by
    apply Subtype.ext
    show algebraMap F (Fv F v) β0 * algebraMap F (Fv F v) β0⁻¹ = 1
    rw [← map_mul, mul_inv_cancel₀ hβ0, map_one]
  have hK : (⟨_, hQv⟩ : v.adicCompletionIntegers F) * ⟨_, hdv⟩ * ⟨_, hKv⟩ = 1 := by
    apply Subtype.ext
    show algebraMap F (Fv F v) Qc * algebraMap F (Fv F v) d * algebraMap F (Fv F v) (Qc * d)⁻¹ = 1
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ (mul_ne_zero hQc hd0), map_one]
  have h4 : (4 : v.adicCompletionIntegers F) * ⟨_, h4v⟩ = 1 := by
    apply Subtype.ext
    show ((4 : v.adicCompletionIntegers F) : Fv F v) * algebraMap F (Fv F v) (4 : F)⁻¹ = 1
    have e4 : ((4 : v.adicCompletionIntegers F) : Fv F v) = algebraMap F (Fv F v) 4 := by
      rw [map_ofNat]; rfl
    rw [e4, ← map_mul, mul_inv_cancel₀ (by norm_num), map_one]
  obtain ⟨lam, hlamO, hlam, c', hc'O, hc'⟩ := core_loc ι (sigR (Fv F v) σ) (oevRing (E := E) v) hιO
    (inclR (F := F) (Fv F v) θ) hθv ⟨_, hdv⟩ ⟨_, hβv⟩ ⟨_, hPv⟩ ⟨_, hQv⟩ ⟨_, hcrd' 0⟩ ⟨_, hcrd' 1⟩
    hΘ hsΘ hsι hPQ ⟨_, hβiv⟩ ⟨_, hKv⟩ ⟨_, h4v⟩ hB hK h4
  refine ⟨lam, hlamO, hlam, c', hc'O, ?_⟩
  have hδι : inclR (F := F) (Fv F v) δ = ι ⟨_, hβv⟩ := by rw [hιF, hδF, hincl]
  rw [hδι]
  conv_lhs => rw [htd]
  exact hc'

end Formalism.L2.SG.Pf.NcS.IntWittPf
end
end
end
