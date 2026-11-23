module

public import Formalism.PeriodIntegrals.LocHaarRR
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalHaarSubgroup.ExistsHaarOfSubgroup
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Topology.Algebra.Module.ModuleTopology
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalHaarSubgroup.IntegralMemNhdsAndSubsetCompactOfFinrankTwo

section

@[expose] public section

noncomputable section

open ValuativeRel Topology Polynomial

namespace PI.LocHaarRRW

section None

variable {K V : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [CharZero K] [CommRing V] [Algebra K V]

theorem key_bound [Nontrivial V] [Module.Finite K V] {θ : V} {d : K}
    (hθr : θ ∉ (algebraMap K V).range) (hθ : θ * θ = algebraMap K V d) (hdO : d ∈ 𝒪[K])
    {a b : K} (hx : IsIntegral 𝒪[K] (algebraMap K V a + algebraMap K V b * θ)) :
    2 * a ∈ 𝒪[K] ∧ 2 * b * d ∈ 𝒪[K] := by
  obtain ⟨hxi, hx'⟩ : IsIntegral 𝒪[K] (algebraMap K V a + algebraMap K V b * θ) ∧
      IsIntegral 𝒪[K] (algebraMap K V a - algebraMap K V b * θ) := by
    refine ⟨hx, ?_⟩
    by_cases hb : b = 0
    · subst hb
      simpa using hx
    · obtain ⟨p, hpm, hp⟩ := hx
      have hqm : ((X - C a) ^ 2 - C (b ^ 2 * d) : K[X]).Monic := by monicity!
      have hqd : ((X - C a) ^ 2 - C (b ^ 2 * d) : K[X]).natDegree = 2 := by compute_degree!
      have hQx : ∀ y : V, (y - algebraMap K V a) ^ 2 = algebraMap K V (b ^ 2 * d) →
          aeval y ((X - C a) ^ 2 - C (b ^ 2 * d) : K[X]) = 0 := by
        intro y hy
        simp only [map_sub, map_pow, aeval_X, aeval_C, hy, sub_self]
      generalize ((X - C a) ^ 2 - C (b ^ 2 * d) : K[X]) = Q at hqm hqd hQx
      have e : ∀ y : V, aeval y (p.map (algebraMap 𝒪[K] K)) = eval₂ (algebraMap 𝒪[K] V) y p :=
        fun y => by rw [aeval_map_algebraMap, aeval_def]
      generalize p.map (algebraMap 𝒪[K] K) = P at e
      have key : ∀ y : V, aeval y Q = 0 → aeval y P = aeval y (P %ₘ Q) := by
        intro y hy
        conv_lhs => rw [← modByMonic_add_div P Q]
        simp [hy]
      have hQ1 : Q ≠ 1 := by
        rintro rfl
        simp at hqd
      have hrd : (P %ₘ Q).natDegree ≤ 1 := by
        have := natDegree_modByMonic_lt P hqm hQ1
        omega
      generalize P %ₘ Q = r at key hrd
      have hr := eq_X_add_C_of_natDegree_le_one hrd
      have hx1 : (algebraMap K V a + algebraMap K V b * θ - algebraMap K V a) ^ 2 =
          algebraMap K V (b ^ 2 * d) := by
        rw [map_mul, map_pow, ← hθ]; ring
      have hx2 : (algebraMap K V a - algebraMap K V b * θ - algebraMap K V a) ^ 2 =
          algebraMap K V (b ^ 2 * d) := by
        rw [map_mul, map_pow, ← hθ]; ring
      have hrx : aeval (algebraMap K V a + algebraMap K V b * θ) r = 0 := by
        rw [← key _ (hQx _ hx1), e]
        exact hp
      rw [hr] at hrx
      simp only [map_add (f := _), map_mul, aeval_X, aeval_C] at hrx
      have hw : r.coeff 1 = 0 := by
        by_contra hw
        apply hθr
        have hwb : r.coeff 1 * b ≠ 0 := mul_ne_zero hw hb
        have hinv : algebraMap K V (r.coeff 1 * b)⁻¹ *
            (algebraMap K V (r.coeff 1) * algebraMap K V b) = 1 := by
          rw [← map_mul, ← map_mul, inv_mul_cancel₀ hwb, map_one]
        refine ⟨-(r.coeff 1 * a + r.coeff 0) * (r.coeff 1 * b)⁻¹, ?_⟩
        rw [map_mul, map_neg, map_add (f := _), map_mul]
        linear_combination (-(algebraMap K V (r.coeff 1 * b)⁻¹)) * hrx + θ * hinv
      have hu : r.coeff 0 = 0 := by
        rw [hw] at hrx
        apply (algebraMap K V).injective
        simpa using hrx
      refine ⟨p, hpm, ?_⟩
      rw [← e, key _ (hQx _ hx2), hr, hw, hu]
      simp
  have hθi : IsIntegral 𝒪[K] θ := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    rw [pow_two, hθ]
    exact integral_V_of_memO hdO
  have hA : algebraMap K V (2 * a) = (algebraMap K V a + algebraMap K V b * θ) +
      (algebraMap K V a - algebraMap K V b * θ) := by
    rw [map_mul, map_ofNat]; ring
  have hB : algebraMap K V (2 * b * d) = (algebraMap K V a + algebraMap K V b * θ) * θ +
      (algebraMap K V a - algebraMap K V b * θ) * (-θ) := by
    rw [map_mul, map_mul, map_ofNat]
    linear_combination (-2 * algebraMap K V b) * hθ
  refine ⟨memO_of_integral_V (V := V) ?_, memO_of_integral_V (V := V) ?_⟩
  · rw [hA]; exact hxi.add hx'
  · rw [hB]; exact (hxi.mul hθi).add (hx'.mul hθi.neg)

theorem integral_mem_nhds_and_subset_compact_of_finrank_two [Module.Free K V] (hr : Module.finrank K V = 2) [IsReduced V]
    [TopologicalSpace V] [IsModuleTopology K V]
    (O : Subring V) (hO : ∀ x, x ∈ O ↔ IsIntegral 𝒪[K] x) :
    ∃ _ : K × K ≃ₜ V, (O : Set V) ∈ 𝓝 (0 : V) ∧ ∃ C : Set V, IsCompact C ∧ (O : Set V) ⊆ C := by
  classical
  obtain ⟨θ, d, hθr, hθ, hd0, hdO⟩ := exists_sq (K := K) (V := V) hr
  haveI : Module.Finite K V := Module.finite_of_finrank_pos (by rw [hr]; norm_num)
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by rw [hr]; norm_num)
  have hθi : IsIntegral 𝒪[K] θ := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    rw [pow_two, hθ]
    exact integral_V_of_memO hdO
  let L : K × K →ₗ[K] V :=
    (LinearMap.fst K K K).smulRight (1 : V) + (LinearMap.snd K K K).smulRight θ
  have hL : ∀ p : K × K, L p = algebraMap K V p.1 + algebraMap K V p.2 * θ := by
    intro p
    simp [L, Algebra.smul_def]
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro p hp
    rw [hL] at hp
    have hb : p.2 = 0 := by
      by_contra hb
      apply hθr
      refine ⟨-p.1 * p.2⁻¹, ?_⟩
      have hinv : algebraMap K V p.2⁻¹ * algebraMap K V p.2 = 1 := by
        rw [← map_mul, inv_mul_cancel₀ hb, map_one]
      rw [map_mul, map_neg]
      linear_combination (-(algebraMap K V p.2⁻¹)) * hp + θ * hinv
    have ha : p.1 = 0 := by
      rw [hb] at hp
      apply (algebraMap K V).injective
      simpa using hp
    exact Prod.ext ha hb
  have hsurj : Function.Surjective L := by
    have : Module.finrank K (K × K) = Module.finrank K V := by
      rw [Module.finrank_prod, Module.finrank_self, hr]
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank this).mp hinj
  obtain ⟨e, he⟩ : ∃ e : (K × K) ≃ₗ[K] V,
      ∀ p, e p = algebraMap K V p.1 + algebraMap K V p.2 * θ :=
    ⟨LinearEquiv.ofBijective L (show Function.Bijective L from ⟨hinj, hsurj⟩), fun p => hL p⟩
  haveI : ContinuousAdd V := IsModuleTopology.toContinuousAdd (R := K) (A := V)
  haveI : ContinuousSMul K V := IsModuleTopology.toContinuousSMul (R := K) (A := V)
  obtain ⟨h, hh⟩ : ∃ h : K × K ≃ₜ V, ∀ p, h p = e p :=
    ⟨{ toEquiv := e.toEquiv
       continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
       continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap },
     fun _ => rfl⟩
  refine ⟨h, ?_, ?_⟩
  · have hsub : h '' ((𝒪[K] : Set K) ×ˢ (𝒪[K] : Set K)) ⊆ (O : Set V) := by
      rintro _ ⟨p, ⟨hp1, hp2⟩, rfl⟩
      show h p ∈ O
      rw [hO, hh, he]
      exact (integral_V_of_memO hp1).add ((integral_V_of_memO hp2).mul hθi)
    have hopen : IsOpen (h '' ((𝒪[K] : Set K) ×ˢ (𝒪[K] : Set K))) :=
      h.isOpenMap _ ((isOpen_integer' (K := K)).prod (isOpen_integer' (K := K)))
    have h0 : (0 : V) ∈ h '' ((𝒪[K] : Set K) ×ˢ (𝒪[K] : Set K)) :=
      ⟨(0, 0), ⟨Subring.zero_mem _, Subring.zero_mem _⟩, by rw [hh]; exact map_zero e⟩
    exact Filter.mem_of_superset (hopen.mem_nhds h0) hsub
  · refine ⟨h '' ((fun q : K × K => (q.1 * 2⁻¹, q.2 * (2 * d)⁻¹)) ''
      ((𝒪[K] : Set K) ×ˢ (𝒪[K] : Set K))), ?_, ?_⟩
    · exact (((isCompact_integer (K := K)).prod (isCompact_integer (K := K))).image
        (by fun_prop)).image h.continuous
    · intro x hx
      have hpx : h (h.symm x) = x := h.apply_symm_apply x
      have hint : IsIntegral 𝒪[K]
          (algebraMap K V (h.symm x).1 + algebraMap K V (h.symm x).2 * θ) := by
        rw [← he, ← hh, hpx]
        exact (hO x).mp hx
      obtain ⟨h1, h2⟩ := key_bound hθr hθ hdO hint
      refine ⟨h.symm x, ⟨(2 * (h.symm x).1, 2 * (h.symm x).2 * d), ⟨h1, h2⟩, ?_⟩, hpx⟩
      refine Prod.ext ?_ ?_ <;> dsimp only <;> first | (field_simp; done) | (field_simp; ring)

end None

end PI.LocHaarRRW
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalHaarSubgroup.MemOrdR

section

@[expose] public section

noncomputable section

open ValuativeRel MeasureTheory Topology IsDedekindDomain NumberField

namespace PI.LocHaarRRW

section Some

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} {A : Formalism.MainNotions.S.Loc.LocAt F E sig p}

theorem mem_ordR (sg : Formalism.MainNotions.S.Loc.SplitAt A.Fp A.Ep A.cj (Formalism.MainNotions.S.Loc.resChar p)) {x : A.Ep}
    (h1 : (sg.e x).1 ∈ 𝒪[A.Fp]) (h2 : (sg.e x).2 ∈ 𝒪[A.Fp])
    (h12 : Ideal.Quotient.mk (Ideal.span {sg.q}) ⟨(sg.e x).1, h1⟩ =
      Ideal.Quotient.mk (Ideal.span {sg.q}) ⟨(sg.e x).2, h2⟩) :
    x ∈ PI.LocHaarRR.ordR sg := by
  simp only [PI.LocHaarRR.ordR]
  rw [Subring.mem_comap, Subring.mem_map]
  exact ⟨(⟨_, h1⟩, ⟨_, h2⟩), h12, rfl⟩

theorem ordR_sub (sg : Formalism.MainNotions.S.Loc.SplitAt A.Fp A.Ep A.cj (Formalism.MainNotions.S.Loc.resChar p)) {x : A.Ep}
    (hx : x ∈ PI.LocHaarRR.ordR sg) : (sg.e x).1 ∈ 𝒪[A.Fp] ∧ (sg.e x).2 ∈ 𝒪[A.Fp] := by
  simp only [PI.LocHaarRR.ordR] at hx
  rw [Subring.mem_comap, Subring.mem_map] at hx
  obtain ⟨y, -, hy⟩ := hx
  have hy' : sg.e x = ((y.1 : A.Fp), (y.2 : A.Fp)) := hy.symm
  rw [hy']
  exact ⟨y.1.2, y.2.2⟩

end Some

theorem target : PI.LocHaarRR.Target := by
  intro F E _ _ _ _ _ sig p A hred
  haveI := A.lf
  haveI := A.top
  haveI := A.borel
  haveI := A.char0
  haveI := A.free
  haveI : IsTopologicalAddGroup A.Ep := IsModuleTopology.topologicalAddGroup A.Fp A.Ep
  haveI := sigmaCompactSpace_lf A.Fp
  rcases hs : A.split with _ | sg
  · obtain ⟨H, h0, C, hC, hOC⟩ := integral_mem_nhds_and_subset_compact_of_finrank_two A.rank A.O A.O_def
    haveI : SigmaCompactSpace A.Ep := H.symm.isClosedEmbedding.sigmaCompactSpace
    have hR : PI.LocHaarRR.RR A = (A.O : Set A.Ep) := by simp [PI.LocHaarRR.RR, hs]
    rw [hR]
    exact exists_haar_of_subgroup A.O.toAddSubgroup h0 hC hOC
  · have hR : PI.LocHaarRR.RR A = (PI.LocHaarRR.ordR sg : Set A.Ep) := by
      simp [PI.LocHaarRR.RR, hs]
    rw [hR]
    let H : A.Fp × A.Fp ≃ₜ A.Ep := homeoOfLin sg.e.symm.toLinearEquiv
    have hH : ∀ y, sg.e (H y) = y := fun y => sg.e.apply_symm_apply y
    have hH' : ∀ x, H (sg.e x) = x := fun x => sg.e.symm_apply_apply x
    haveI : SigmaCompactSpace A.Ep := H.symm.isClosedEmbedding.sigmaCompactSpace
    have hq0 : (sg.q : A.Fp) ≠ 0 := fun h => sg.q_irr.ne_zero (Subtype.ext h)
    let Q : Set A.Fp := (fun y : A.Fp => (sg.q : A.Fp) * y) '' (𝒪[A.Fp] : Set A.Fp)
    have hQ : IsOpen Q := (Homeomorph.mulLeft₀ (sg.q : A.Fp) hq0).isOpenMap _ (isOpen_integer' _)
    refine exists_haar_of_subgroup (PI.LocHaarRR.ordR sg).toAddSubgroup ?_
      (((isCompact_integer _).prod (isCompact_integer _)).image H.continuous) ?_
    · rw [mem_nhds_iff]
      refine ⟨H '' (Q ×ˢ Q), ?_, H.isOpenMap _ (hQ.prod hQ), ⟨(0, 0), ⟨⟨0, zero_mem _, by simp⟩,
        ⟨0, zero_mem _, by simp⟩⟩, by have h00 := hH' 0; rw [map_zero] at h00; exact h00⟩⟩
      rintro _ ⟨⟨_, _⟩, ⟨⟨u, hu, rfl⟩, ⟨v, hv, rfl⟩⟩, rfl⟩
      have h1 : (sg.e (H ((sg.q : A.Fp) * u, (sg.q : A.Fp) * v))).1 ∈ 𝒪[A.Fp] := by
        rw [hH]; exact mul_mem sg.q.2 hu
      have h2 : (sg.e (H ((sg.q : A.Fp) * u, (sg.q : A.Fp) * v))).2 ∈ 𝒪[A.Fp] := by
        rw [hH]; exact mul_mem sg.q.2 hv
      refine mem_ordR sg h1 h2 ?_
      rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
      refine ⟨⟨u, hu⟩ - ⟨v, hv⟩, Subtype.ext ?_⟩
      simp only [hH, AddSubgroupClass.coe_sub, MulMemClass.coe_mul]
      ring
    · intro x hx
      obtain ⟨h1, h2⟩ := ordR_sub sg hx
      exact ⟨sg.e x, ⟨h1, h2⟩, hH' x⟩

end PI.LocHaarRRW
end
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocHaarRR

section

@[expose] public section

theorem local_haar_real_real : PI.LocHaarRR.Target := PI.LocHaarRRW.target
end
end
