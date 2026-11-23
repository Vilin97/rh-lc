module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationLift.IntLatOfUnimod
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationLift.DiffIdealNeBot
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationLift.ActsByFrameAct
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationLift.HTOsmulRight
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationLift.CoeCj
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationLift.ResidueOnto

section

@[expose] public section

noncomputable section

open scoped Classical

namespace PI.NRL

open NumberField IsDedekindDomain Formalism.BasicNotions

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

section Prime

variable (Λ : Submodule (𝓞 E) S.V) (hU : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) (hint : IntLat Λ)
  (e : Fin r → S.V) (hind : LinearIndependent E e) (he : ∀ i, e i ∈ Λ) (P : HeightOneSpectrum (𝓞 E))
  (hloc : ∀ x ∈ Λ, x ∈ Submodule.span E (Set.range e) →
    ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • x ∈ Submodule.span (𝓞 E) (Set.range e))

include hU hint hind he hloc in
theorem residue_onto (c : Fin r) :
    ∃ y ∈ Λ, ∃ o : Fin r → 𝓞 E, (∀ i, S.hT y (e i) = (o i : E)) ∧
      ∀ i, (o i - if i = c then 1 else 0) ∈ P.asIdeal := by
  haveI := P.isMaximal
  letI : Field (𝓞 E ⧸ P.asIdeal) := Ideal.Quotient.field P.asIdeal
  let mk := Ideal.Quotient.mk P.asIdeal
  let U : Submodule (𝓞 E ⧸ P.asIdeal) (Fin r → 𝓞 E ⧸ P.asIdeal) :=
    { carrier := {φ | ∃ y ∈ Λ, ∃ o : Fin r → 𝓞 E, (∀ i, S.hT y (e i) = (o i : E)) ∧ ∀ i, φ i = mk (o i)}
      zero_mem' := ⟨0, Λ.zero_mem, 0, fun i => by simp, fun i => by simp⟩
      add_mem' := by
        rintro φ ψ ⟨y, hy, o, ho, hφ⟩ ⟨y', hy', o', ho', hψ⟩
        refine ⟨y + y', Λ.add_mem hy hy', o + o', fun i => ?_, fun i => ?_⟩
        · simp [map_add (f := _), ho, ho']
        · simp [hφ, hψ]
      smul_mem' := by
        rintro κ φ ⟨y, hy, o, ho, hφ⟩
        obtain ⟨κ', rfl⟩ := Ideal.Quotient.mk_surjective κ
        refine ⟨cj κ' • y, Λ.smul_mem _ hy, fun i => κ' * o i, fun i => ?_, fun i => ?_⟩
        · rw [hT_cj_left, ho]; push_cast; ring
        · simp [hφ, mk] }
  have hUtop : U = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hfU⟩ := Submodule.exists_le_ker_of_lt_top U (lt_top_iff_ne_top.mpr hne)
    let α : Fin r → 𝓞 E ⧸ P.asIdeal := fun i => f (fun j => if i = j then 1 else 0)
    have hfα : ∀ φ, f φ = ∑ i, φ i * α i := by
      intro φ
      rw [LinearMap.pi_apply_eq_sum_univ f φ]
      simp [α, smul_eq_mul]
    have hα0 : ∃ i, α i ≠ 0 := by
      by_contra h
      push Not at h
      apply hf0
      refine LinearMap.ext fun φ => ?_
      rw [hfα, LinearMap.zero_apply]
      exact Finset.sum_eq_zero fun i _ => by rw [h i, mul_zero]
    choose α' hα' using fun i => Ideal.Quotient.mk_surjective (α i)
    have hmem := coeff_mem_P Λ hU e hind P hloc α' (by
      intro y hy
      choose o ho using fun i => hint y hy (e i) (he i)
      have hφ : (fun i => mk (o i)) ∈ U := ⟨y, hy, o, ho, fun i => rfl⟩
      have hz : f (fun i => mk (o i)) = 0 := hfU hφ
      rw [hfα] at hz
      refine ⟨∑ i, o i * α' i, ?_, ?_⟩
      · rw [← Ideal.Quotient.eq_zero_iff_mem]

        simpa [map_sum, map_mul, hα', mk] using hz
      · set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        push_cast
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hT_osmul_right, ho]; ring)
    obtain ⟨i, hi⟩ := hα0
    apply hi
    rw [← hα' i]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hmem i)
  have hc : (fun i => if i = c then (1 : 𝓞 E ⧸ P.asIdeal) else 0) ∈ U := by rw [hUtop]; trivial
  obtain ⟨y, hy, o, ho, hφ⟩ := hc
  refine ⟨y, hy, o, ho, fun i => ?_⟩
  rw [← Ideal.Quotient.eq]
  have := hφ i
  simp only at this
  by_cases hic : i = c
  · simp only [hic, if_true] at this ⊢; rw [map_one]; exact this.symm
  · simp only [hic, if_false] at this ⊢; rw [map_zero]; exact this.symm

include hU hint hind he hloc in
theorem exact_dual (c : Fin r) :
    ∃ y ∈ Λ, (∀ i, i ≠ c → S.hT y (e i) = 0) ∧ ∃ o : 𝓞 E, S.hT y (e c) = (o : E) ∧ o ∉ P.asIdeal := by
  choose y hy o ho hP using fun j => residue_onto Λ hU hint e hind he P hloc j
  let G : Matrix (Fin r) (Fin r) (𝓞 E) := fun j i => o j i
  have hdet : G.det ∉ P.asIdeal := by
    intro hmem
    have h1 : (Ideal.Quotient.mk P.asIdeal).mapMatrix G = 1 := by
      ext j i
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.one_apply]
      have := Ideal.Quotient.eq.mpr (hP j i)
      rw [this]
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij, Ne.symm hij]
    have := RingHom.map_det (Ideal.Quotient.mk P.asIdeal) G
    rw [h1, Matrix.det_one, Ideal.Quotient.eq_zero_iff_mem.mpr hmem] at this
    exact zero_ne_one this
  have key : ∀ i, S.hT (∑ j, cj (G.adjugate c j) • y j) (e i) = ((G.adjugate * G) c i : E) := by
    intro i

    rw [map_sum, LinearMap.sum_apply, Matrix.mul_apply]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hT_cj_left, ho]
  rw [Matrix.adjugate_mul] at key
  refine ⟨∑ j, cj (G.adjugate c j) • y j, Λ.sum_mem fun j _ => Λ.smul_mem _ (hy j), fun i hi => ?_,
    G.det, ?_, hdet⟩
  · rw [key, Matrix.smul_apply, Matrix.one_apply_ne (Ne.symm hi)]; simp
  · rw [key, Matrix.smul_apply, Matrix.one_apply_eq]; simp

end Prime

end PI.NRL
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationLift.GlobalDual

section

@[expose] public section

noncomputable section

open scoped Classical

namespace PI.NRL

open NumberField IsDedekindDomain Formalism.BasicNotions

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem global_dual (Λ : Submodule (𝓞 E) S.V) (hU : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) (hint : IntLat Λ)
    (e : Fin r → S.V) (hind : LinearIndependent E e) (he : ∀ i, e i ∈ Λ) (g : 𝓞 E)
    (hlocg : ∀ P : HeightOneSpectrum (𝓞 E), g ∈ P.asIdeal → ∀ x ∈ Λ, x ∈ Submodule.span E (Set.range e) →
      ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • x ∈ Submodule.span (𝓞 E) (Set.range e))
    (c : Fin r) :
    ∃ y ∈ Λ, (∀ i, i ≠ c → S.hT y (e i) = 0) ∧ ∃ q : 𝓞 E, S.hT y (e c) = ((1 + g * q : 𝓞 E) : E) := by
  let J : Ideal (𝓞 E) :=
    { carrier := {o | ∃ y ∈ Λ, (∀ i, i ≠ c → S.hT y (e i) = 0) ∧ S.hT y (e c) = (o : E)}
      zero_mem' := ⟨0, Λ.zero_mem, fun i _ => by simp, by simp⟩
      add_mem' := by
        rintro o o' ⟨y, hy, h0, ho⟩ ⟨y', hy', h0', ho'⟩
        refine ⟨y + y', Λ.add_mem hy hy', fun i hi => ?_, ?_⟩
        · simp [h0 i hi, h0' i hi]
        · simp [ho, ho']
      smul_mem' := by
        rintro κ o ⟨y, hy, h0, ho⟩
        refine ⟨cj κ • y, Λ.smul_mem _ hy, fun i hi => ?_, ?_⟩
        · rw [hT_cj_left, h0 i hi, mul_zero]
        · rw [hT_cj_left, ho, smul_eq_mul]; push_cast; rfl }
  have htop : J ⊔ Ideal.span {g} = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    have hMbot : M ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField E)
    let P : HeightOneSpectrum (𝓞 E) := ⟨M, hM.isPrime, hMbot⟩
    have hg : g ∈ M := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self g))
    obtain ⟨y, hy, h0, o, ho, hoP⟩ := exact_dual Λ hU hint e hind he P (hlocg P hg) c
    exact hoP (hle (Ideal.mem_sup_left ⟨y, hy, h0, ho⟩))
  have h1 : (1 : 𝓞 E) ∈ J ⊔ Ideal.span {g} := by rw [htop]; trivial
  obtain ⟨j, hj, x, hx, hjx⟩ := Submodule.mem_sup.mp h1
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hx
  obtain ⟨y, hy, h0, ho⟩ := hj
  refine ⟨y, hy, h0, -a, ?_⟩
  rw [ho]
  have : j = 1 + g * -a := by rw [← hjx]; ring
  rw [this]

end PI.NRL
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationLift.PreRowvec

section

@[expose] public section

noncomputable section

open scoped Classical

namespace PI.NRL

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem pre_rowvec (Λ : Submodule (𝓞 E) S.V) (hint : IntLat Λ) (Tn : ℕ) (F : LFlag S r ((Tn : ℕ) : E))
    (hz : F.fl.z ∈ Λ) (g : 𝓞 E)
    (hdual : ∀ c : Fin r, ∃ y ∈ Λ, (∀ i, i ≠ c → S.hT y (F.fl.e i) = 0) ∧
      ∃ q : 𝓞 E, S.hT y (F.fl.e c) = ((1 + g * q : 𝓞 E) : E))
    (hTg : ∃ x y : 𝓞 E, x * (Tn : 𝓞 E) + y * g = 1) (a : Fin r) (t : Fin (r + 1) → 𝓞 E) :
    ∃ v ∈ Λ, (∀ i, i ≤ a → S.hT v (F.fl.e i) = 0) ∧
      ∀ c, Fin.castSucc a < c → ∃ q : 𝓞 E, S.hT v (frame F c) = ((t c + g * q : 𝓞 E) : E) := by
  choose y hy h0 q hq using hdual
  let v₀ : S.V := ∑ c : Fin r, (if a < c then cj (t c.castSucc) else 0) • y c
  have hv₀ : v₀ ∈ Λ := Λ.sum_mem fun c _ => Λ.smul_mem _ (hy c)
  have hv0e : ∀ i, S.hT v₀ (F.fl.e i) =
      if a < i then (t i.castSucc : E) * ((1 + g * q i : 𝓞 E) : E) else 0 := by
    intro i

    rw [map_sum, LinearMap.sum_apply, Finset.sum_eq_single i]
    · by_cases hai : a < i
      · rw [if_pos hai, if_pos hai, hT_cj_left, hq]
      · rw [if_neg hai, if_neg hai, zero_smul, map_zero, LinearMap.zero_apply]
    · intro c _ hci
      by_cases hac : a < c
      · rw [if_pos hac, hT_cj_left, h0 c i (Ne.symm hci), mul_zero]
      · rw [if_neg hac, zero_smul, map_zero, LinearMap.zero_apply]
    · intro h; exact absurd (Finset.mem_univ i) h
  obtain ⟨ζ, hζ⟩ := hint v₀ hv₀ F.fl.z hz
  obtain ⟨x, y', hxy⟩ := hTg
  have hxyE : (x : E) * (Tn : E) + (y' : E) * (g : E) = 1 := by
    have := congrArg (fun o : 𝓞 E => (o : E)) hxy
    simpa using this
  let m : 𝓞 E := x * (ζ - t (Fin.last r))
  let v : S.V := v₀ + cj m • F.fl.z
  have hze : ∀ i, S.hT F.fl.z (F.fl.e i) = 0 := by
    intro i; rw [herm_eq, F.fl.z_orth i, star_zero]
  have hve : ∀ i, S.hT v (F.fl.e i) = S.hT v₀ (F.fl.e i) := by
    intro i; simp only [v, map_add (f := _), LinearMap.add_apply, hT_cj_left, hze, mul_zero, add_zero]
  refine ⟨v, Λ.add_mem hv₀ (Λ.smul_mem _ hz), fun i hi => ?_, fun c hc => ?_⟩
  · rw [hve, hv0e, if_neg (not_lt.mpr hi)]
  · induction c using Fin.lastCases with
    | last =>
      refine ⟨y' * (ζ - t (Fin.last r)), ?_⟩
      have hfz : frame F (Fin.last r) = F.fl.z := by simp [frame, FlagG.fvec]
      rw [hfz]
      simp only [v, map_add (f := _), LinearMap.add_apply, hT_cj_left, F.fl.z_norm, hζ, m]
      push_cast
      linear_combination (-((ζ : E) - (t (Fin.last r) : E))) * hxyE
    | cast i =>
      have hai : a < i := Fin.castSucc_lt_castSucc_iff.mp hc
      refine ⟨t i.castSucc * q i, ?_⟩
      have hfi : frame F (Fin.castSucc i) = F.fl.e i := by simp [frame, FlagG.fvec]
      rw [hfi, hve, hv0e, if_pos hai]
      push_cast; ring

theorem coe_nat (N : ℕ) : ((N : 𝓞 E) : E) = (N : E) := map_natCast (algebraMap (𝓞 E) E) N

theorem trace_fix (Λ : Submodule (𝓞 E) S.V) (hint : IntLat Λ) {n : ℕ} (f : Fin n → S.V) (g : 𝓞 E)
    (htr : (∃ k : ℕ, (g : E) = 2 * (k : E) + 1) ∨ ∃ ω : 𝓞 E, (ω : E) + star (ω : E) = 1)
    (Z : Set (Fin n)) (t : Fin n → 𝓞 E) (v : S.V) (hv : v ∈ Λ)
    (hZ : ∀ c ∈ Z, S.hT v (f c) = 0) (hc : ∀ c ∉ Z, ∃ q : 𝓞 E, S.hT v (f c) = ((t c + g * q : 𝓞 E) : E)) :
    ∃ v' ∈ Λ, ∃ l : 𝓞 E, (l : E) + star (l : E) = -S.hT v' v' ∧ (∀ c ∈ Z, S.hT v' (f c) = 0) ∧
      ∀ c ∉ Z, ∃ q : 𝓞 E, S.hT v' (f c) = ((t c + g * q : 𝓞 E) : E) := by
  obtain ⟨o, ho⟩ := hint v hv v hv
  have hself : star (o : E) = (o : E) := by rw [← ho, ← herm_eq]
  rcases htr with ⟨k, hk⟩ | ⟨ω, hω⟩
  · obtain ⟨M, hM⟩ : ∃ M : ℕ, M = 2 * (k + 1) := ⟨_, rfl⟩
    obtain ⟨N, hN⟩ : ∃ N : ℕ, N = 2 * (k + 1) * (k + 1) := ⟨_, rfl⟩
    have hmE : (M : E) = 2 * ((k : E) + 1) := by rw [hM]; push_cast; ring
    have hNE : (N : E) = 2 * ((k : E) + 1) * ((k : E) + 1) := by rw [hN]; push_cast; ring
    have hmg : (M : E) = (g : E) + 1 := by rw [hmE, hk]; ring
    refine ⟨cj (M : 𝓞 E) • v, Λ.smul_mem _ hv, -((N : 𝓞 E) * o), ?_, fun c hcZ => ?_, fun c hcZ => ?_⟩
    · rw [hT_cj_left, hT_osmul_right, coe_cj, ho]
      simp only [coe_nat, map_neg, map_mul, map_natCast, star_neg, star_mul', hself, star_natCast]
      rw [hNE, hmE]; ring
    · rw [hT_cj_left, hZ c hcZ, mul_zero]
    · obtain ⟨q, hq⟩ := hc c hcZ
      refine ⟨t c + (M : 𝓞 E) * q, ?_⟩
      rw [hT_cj_left, hq]
      simp only [coe_nat, map_add (f := _), map_mul, map_natCast]
      linear_combination ((t c : E) + (g : E) * (q : E) - (g : E) * (q : E)) * hmg
  · refine ⟨v, hv, -(ω * o), ?_, hZ, hc⟩
    rw [ho]
    simp only [map_neg, map_mul, star_neg, star_mul', hself]
    linear_combination (-(o : E)) * hω

end PI.NRL
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationLift.NormRepStepOfTrace

section

@[expose] public section

noncomputable section

open scoped Classical

namespace PI.NRL

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def TraceOne (D : D7) : Prop := ∃ ω : 𝓞 D.host.E, (ω : D.host.E) + star (ω : D.host.E) = 1

theorem rowVec_of (D : D7) (u : D.what₂.Word) (T' : ℕ) (htr : Odd (gS D) ∨ TraceOne D) :
    RowVec D u T' := by
  intro hP F0 Λ hΛ a t
  have hU : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ := hΛ.2.1.2.1
  have hint : IntLat Λ := intLat_of_unimod Λ hU
  have hz : F0.z ∈ Λ := hΛ.2.1.2.2.1.1
  have he : ∀ i, F0.e i ∈ Λ := fun i => e_mem_lam D F0 Λ hΛ i
  have hlocg : ∀ P : HeightOneSpectrum (𝓞 D.host.E), ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal →
      ∀ x ∈ Λ, x ∈ Submodule.span D.host.E (Set.range F0.e) →
        ∃ s : 𝓞 D.host.E, s ∉ P.asIdeal ∧ s • x ∈ Submodule.span (𝓞 D.host.E) (Set.range F0.e) := by
    intro P hg x hx hxE
    haveI := P.isPrime
    obtain ⟨c, _, hc1, hceq⟩ := hΛ.2.1.2.2.2.1 P
    have hxX : x ∈ XLam Λ (lf D F0) := Submodule.mem_inf.mpr ⟨hx, hxE⟩
    have hxl : x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ (lf D F0)) :=
      ⟨1, (Ideal.primeCompl P.asIdeal).one_mem, by simpa using hxX⟩
    rw [hceq] at hxl
    obtain ⟨s, hs, hsx⟩ := hxl
    have hfun : (fun a => c a • (lf D F0).fl.e a) = F0.e := by
      funext a; rw [hc1 hg a, one_smul]
    rw [hfun] at hsx
    exact ⟨s, hs, hsx⟩
  have hdual := fun c => global_dual Λ hU hint F0.e F0.e_indep he ((gS D : ℕ) : 𝓞 D.host.E) hlocg c
  have hcop : Nat.Coprime (Tu D u) (gS D) :=
    (Nat.Coprime.coprime_mul_right_right hP.2.2.2.2.2.2.2.1).symm
  have hTg : ∃ x y : 𝓞 D.host.E, x * ((Tu D u : ℕ) : 𝓞 D.host.E) + y * ((gS D : ℕ) : 𝓞 D.host.E) = 1 := by
    refine ⟨((Nat.gcdA (Tu D u) (gS D) : ℤ) : 𝓞 D.host.E), ((Nat.gcdB (Tu D u) (gS D) : ℤ) : 𝓞 D.host.E), ?_⟩
    have h := Nat.gcd_eq_gcd_ab (Tu D u) (gS D)
    rw [hcop.gcd_eq_one] at h
    have := congrArg (Int.cast : ℤ → 𝓞 D.host.E) h
    push_cast at this
    rw [this]; ring
  obtain ⟨v, hv, hv0, hvc⟩ := pre_rowvec Λ hint (Tu D u) (lf D F0) hz ((gS D : ℕ) : 𝓞 D.host.E)
    hdual hTg a t
  have htr' : (∃ k : ℕ, (((gS D : ℕ) : 𝓞 D.host.E) : D.host.E) = 2 * (k : D.host.E) + 1) ∨
      ∃ ω : 𝓞 D.host.E, (ω : D.host.E) + star (ω : D.host.E) = 1 := by
    rcases htr with ⟨k, hk⟩ | h
    · exact Or.inl ⟨k, by rw [coe_nat, hk]; push_cast; ring⟩
    · exact Or.inr h
  have hframe_e : ∀ i : Fin D.R.rS, frame (lf D F0) (Fin.castSucc i) = F0.e i := by
    intro i; simp [frame, FlagG.fvec]
  obtain ⟨v', hv', l, hl, hZ, hc⟩ := trace_fix Λ hint (frame (lf D F0)) ((gS D : ℕ) : 𝓞 D.host.E) htr'
    {c | c ≤ Fin.castSucc a} t v hv
    (by
      intro c hc
      have hcl : c ≠ Fin.last _ := fun h => by
        rw [h] at hc; exact absurd hc (not_le.mpr (Fin.castSucc_lt_last a))
      obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.mpr hcl
      rw [hframe_e]
      exact hv0 i (Fin.castSucc_le_castSucc_iff.mp hc))
    (fun c hc => hvc c (not_le.mp hc))
  refine ⟨v', hv', l, hl, fun i hi => ?_, fun c hc' => hc c (not_le.mpr hc')⟩
  rw [← hframe_e]
  exact hZ _ (Fin.castSucc_le_castSucc_iff.mpr hi)

theorem normRepStep_of_trace (D : D7) (u u' : D.what₂.Word) (hS : TermStable D u u')
    (hP : PrimeHyp D u (Tu D u')) (htr : Odd (gS D) ∨ TraceOne D) : PI.NormRepLift.NormRepStep D u u' :=
  normRepStep_of D u u' hS hP (rowVec_of D u (Tu D u') htr)

end PI.NRL
end
end
end
