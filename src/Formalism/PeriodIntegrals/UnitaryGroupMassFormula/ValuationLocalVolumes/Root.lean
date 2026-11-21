module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.GramAugT
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVBadTOfThreeX

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
  set_option maxHeartbeats 0 in
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
    
      have isPrecomplete : IsPrecomplete (IsLocalRing.maximalIdeal Ow) Ow := by
        obtain ⟨π, hπ⟩ := exists_unif 
        have hπ1 : Valued.v (π : Lw) < 1 := (lt_one_iff_le _).2 hπ.le
        have hπ0 : (π : Lw) ≠ 0 := by
          intro h
          rw [h, map_zero] at hπ
          exact WithZero.exp_ne_zero hπ.symm
        refine ⟨fun f hf => ?_⟩
        simp only [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem, mem_max_pow_iff hπ] at hf ⊢
        let g : ℕ → Lw := fun n => (f n : Lw)
        have hc : Cauchy (map g atTop) := by
          rw [Valued.cauchy_iff]
          refine ⟨map_neBot, fun γ => ?_⟩
          obtain ⟨n, hn⟩ := exists_pow_lt₀ hπ1 (Units.map (MonoidWithZeroHom.ValueGroup₀.embedding
            (f := ↑(Valued.v : Valuation Lw ℤᵐ⁰))).toMonoidHom γ)
          refine ⟨g '' Set.Ici n, image_mem_map (Ici_mem_atTop n), ?_⟩
          rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
          rw [Valuation.restrict_lt_iff_lt_embedding]
          refine lt_of_le_of_lt ?_ hn
          have h1 := hf (m := n) (n := a) ha
          have h2 := hf (m := n) (n := b) hb
          have e : g b - g a = ((f n - f a : Ow) : Lw) - ((f n - f b : Ow) : Lw) := by
            simp only [g]; push_cast; ring
          rw [e]
          exact Valuation.map_sub_le _ h1 h2
        obtain ⟨l, hl⟩ := CompleteSpace.complete hc
        have key : ∀ n, Valued.v (g n - l) ≤ Valued.v (π : Lw) ^ n := by
          intro n
          have hU : {y : Lw | (Valued.v : Valuation Lw ℤᵐ⁰).restrict (y - l) <
              (Valued.v : Valuation Lw ℤᵐ⁰).restrict ((π : Lw) ^ n)} ∈ 𝓝 l := by
            rw [Valued.mem_nhds]
            exact ⟨Units.mk0 ((Valued.v : Valuation Lw ℤᵐ⁰).restrict ((π : Lw) ^ n)) (by simp [hπ0]),
              subset_rfl⟩
          have hm := hl hU
          rw [mem_map, mem_atTop_sets] at hm
          obtain ⟨N, hN⟩ := hm
          have h1 : (Valued.v : Valuation Lw ℤᵐ⁰).restrict (g (max N n) - l) <
              (Valued.v : Valuation Lw ℤᵐ⁰).restrict ((π : Lw) ^ n) := hN (max N n) (le_max_left _ _)
          rw [Valuation.restrict_lt_iff, map_pow] at h1
          have h2 := hf (m := n) (n := max N n) (le_max_right N n)
          have e : g n - l = ((f n - f (max N n) : Ow) : Lw) + (g (max N n) - l) := by
            simp only [g]; push_cast; ring
          rw [e]
          exact Valuation.map_add_le _ h2 h1.le
        have hl1 : l ∈ Ow := by
          have e : l = g 0 - (g 0 - l) := by ring
          rw [e]
          exact sub_mem (f 0).2 ((mem_adicCompletionIntegers R L w).2 (by simpa using key 0))
        exact ⟨⟨l, hl1⟩, fun n => key n⟩
    
      have isAdicComplete : IsAdicComplete (IsLocalRing.maximalIdeal Ow) Ow :=
        { toIsHausdorff := inferInstance, toIsPrecomplete := isPrecomplete }
      exact isAdicComplete
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
