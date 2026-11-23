module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicOutsideLine
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientLattice
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Lemma
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.EmbeddingHermitianPairs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.RealEmbeddingCharacters
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCubeIntegral
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.UnipotentVectorGroup
public import Mathlib.Analysis.Fourier.AddCircleMulti

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FixedPointImaginarySpan

section

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.FD.FixedPointImaginarySpan

open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientMatrices
  ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientLattice ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (g : ℕ)

lemma cc_mul'' (x y : E) : cc (x * y) = cc x * cc y := map_mul (IsCMField.complexConj E) x y

lemma im_of_fixed {a : E} (ha : cc a = a) (τ : E →+* ℂ) : (τ a).im = 0 := by
  have h : conj (τ a) = τ a := by
    rw [← NumberField.IsCMField.complexEmbedding_complexConj E τ a]
    exact congrArg τ ha
  exact Complex.conj_eq_iff_im.mp h

lemma span_Lc (hg : 0 < g) :
    Submodule.span ℝ (Lc X g : Set (X.Ψ → Fin 2 → Fin 2 → ℝ)) = ⊤ := by
  set Sp := Submodule.span ℝ (Lc X g : Set (X.Ψ → Fin 2 → Fin 2 → ℝ)) with hSp
  have hsub : ∀ b ∈ X.LZ g, kap b ∈ Sp := fun b hb =>
    Submodule.subset_span ((mem_Lc X g).2 ⟨b, hb, rfl⟩)
  have hcr := cr_pos (E := E) g hg
  have hposition : ∀ (i0 k0 : Fin 2), (∀ a : E, cc a = a → IsIntegral ℤ a →
      intersection_update_fsHerm_neg_one i0 k0 (cr (E := E) g • fun τ : X.Ψ => (τ.1 a).re) ∈ Sp) → ∀ p, intersection_update_fsHerm_neg_one i0 k0 p ∈ Sp := by
    intro i0 k0 h p
    have := span_gen X g ((intersection_update_fsHerm_neg_one i0 k0).comp (cr (E := E) g • LinearMap.id)) (fun a ha hai => by
      simpa using h a ha hai) ((cr (E := E) g)⁻¹ • p)
    simpa [smul_smul, inv_mul_cancel₀ hcr.ne'] using this
  have h00 : ∀ p, intersection_update_fsHerm_neg_one 0 0 p ∈ Sp := hposition 0 0 fun a ha hai => by
    have hm := mem_LZ_of X g !![a, 0; 0, 0]
      (fun i k => by fin_cases i <;> fin_cases k <;> simp [ha, RealEmbeddingCharacters.cc_zero'])
      (fun i k => by fin_cases i <;> fin_cases k <;> simp [hai, isIntegral_zero])
    convert hsub _ hm using 1
    funext τ i k
    fin_cases i <;> fin_cases k <;> simp [kap, position_apply, Data.embH, emb_cE]
  have h11 : ∀ p, intersection_update_fsHerm_neg_one 1 1 p ∈ Sp := hposition 1 1 fun a ha hai => by
    have hm := mem_LZ_of X g !![0, 0; 0, a]
      (fun i k => by fin_cases i <;> fin_cases k <;> simp [ha, RealEmbeddingCharacters.cc_zero'])
      (fun i k => by fin_cases i <;> fin_cases k <;> simp [hai, isIntegral_zero])
    convert hsub _ hm using 1
    funext τ i k
    fin_cases i <;> fin_cases k <;> simp [kap, position_apply, Data.embH, emb_cE]
  have h01 : ∀ p, intersection_update_fsHerm_neg_one 0 1 p ∈ Sp := hposition 0 1 fun a ha hai => by
    have hm := mem_LZ_of X g !![0, a; a, 0]
      (fun i k => by fin_cases i <;> fin_cases k <;> simp [ha, RealEmbeddingCharacters.cc_zero'])
      (fun i k => by fin_cases i <;> fin_cases k <;> simp [hai, isIntegral_zero])
    convert hsub _ hm using 1
    funext τ i k
    fin_cases i <;> fin_cases k <;> simp [kap, position_apply, Data.embH, emb_cE, im_of_fixed ha]
  obtain ⟨η, hηcc, hηi, hηne⟩ : ∃ η : E, cc η = -η ∧ IsIntegral ℤ η ∧ η ≠ 0 := by
    have halg : IsAlgebraic ℤ X.ξ0 :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic X.ξ0)
    obtain ⟨k, hk, hki⟩ := halg.exists_integral_multiple
    refine ⟨k • X.ξ0, ?_, hki, smul_ne_zero hk X.ξ0_ne⟩
    rw [show cc (k • X.ξ0) = k • cc X.ξ0 from map_zsmul _ k _, X.ξ0_im, smul_neg]
  have hre : ∀ τ : E →+* ℂ, (τ η).re = 0 := fun τ => by
    have h := emb_cc' τ η
    rw [hηcc, map_neg] at h
    have := congrArg Complex.re h
    simp at this
    linarith
  have him : ∀ τ : E →+* ℂ, (τ η).im ≠ 0 := fun τ h => by
    have : τ η = 0 := Complex.ext (hre τ) h
    exact hηne ((map_eq_zero τ).1 this)
  have h10 : ∀ p, intersection_update_fsHerm_neg_one 1 0 p ∈ Sp := by
    set D : (X.Ψ → ℝ) →ₗ[ℝ] (X.Ψ → ℝ) :=
      LinearMap.pi fun τ : X.Ψ => (cr (E := E) g * (τ.1 η).im) • LinearMap.proj τ with hD
    have hDapp : ∀ q τ, D q τ = cr (E := E) g * (τ.1 η).im * q τ := fun q τ => by simp [hD]
    have key : ∀ q, (intersection_update_fsHerm_neg_one 1 0).comp D q ∈ Sp := span_gen X g _ fun a ha hai => by
      have hm := mem_LZ_of X g !![0, η * a; -(η * a), 0]
        (fun i k => by
          fin_cases i <;> fin_cases k <;>
            simp [ha, RealEmbeddingCharacters.cc_zero', cc_mul'', hηcc, RealEmbeddingCharacters.cc_neg'])
        (fun i k => by fin_cases i <;> fin_cases k <;> simp [(hηi.mul hai), (hηi.mul hai).neg, isIntegral_zero])
      convert hsub _ hm using 1
      funext τ i k
      rw [LinearMap.comp_apply]
      fin_cases i <;> fin_cases k <;>
        simp [kap, position_apply, Data.embH, emb_cE, hDapp, Complex.mul_re, Complex.mul_im, hre,
          im_of_fixed ha]
      ring
    intro p
    have e : D (fun τ => p τ / (cr (E := E) g * (τ.1 η).im)) = p := by
      funext τ
      rw [hDapp]
      have : cr (E := E) g * (τ.1 η).im ≠ 0 := mul_ne_zero hcr.ne' (him τ.1)
      field_simp [him τ.1]
    have := key (fun τ => p τ / (cr (E := E) g * (τ.1 η).im))
    rwa [LinearMap.comp_apply, e] at this
  refine eq_top_iff.2 fun y _ => ?_
  rw [sum_position y]
  refine Submodule.sum_mem _ fun i0 _ => Submodule.sum_mem _ fun k0 _ => ?_
  fin_cases i0 <;> fin_cases k0
  exacts [h00 _, h01 _, h10 _, h11 _]

theorem exists_basis (hg : 0 < g) : ∃ ω, X.IsLZBasis g ω := by
  have : Fact (0 < g) := ⟨hg⟩
  have : IsZLattice ℝ (Lc X g) := ⟨span_Lc X g hg⟩
  have := ZLattice.module_free ℝ (Lc X g)
  have := ZLattice.module_finite ℝ (Lc X g)
  have hrank : Module.finrank ℤ (Lc X g) = 4 * Fintype.card X.Ψ := by
    rw [ZLattice.rank ℝ (Lc X g), finrank_rfam]
  set bZ := Module.finBasisOfFinrankEq ℤ (Lc X g) hrank
  set eR := bZ.ofZLatticeBasis ℝ (Lc X g)
  have heR : ∀ j, eR j = (bZ j : X.Ψ → Fin 2 → Fin 2 → ℝ) := fun j =>
    bZ.ofZLatticeBasis_apply ℝ (Lc X g) j
  have hthinj : LinearMap.ker (thL : (X.Ψ → Fin 2 → Fin 2 → ℝ) →ₗ[ℝ] _) = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro z z' h
    rw [← kap_th z, ← kap_th z']
    exact congrArg kap h
  have hli : LinearIndependent ℝ (fun j => th (eR j)) := eR.linearIndependent.map' thL hthinj
  have hc : ∀ (m : ℤ) (v : X.Ψ → Fin 2 → Fin 2 → ℂ), (m : ℂ) • v = (m : ℝ) • v := fun m v => by
    rw [← Complex.ofReal_intCast, Complex.coe_smul]
  refine ⟨fun j => th (eR j), fun j => ?_, fun b hb => ?_, hli⟩
  · obtain ⟨b, hb, hkb⟩ := (mem_Lc X g).1 (show eR j ∈ Lc X g by rw [heR]; exact (bZ j).2)
    show th (eR j) ∈ X.LZ g
    rw [← hkb, th_kap (herm_of_LZ X g hb)]
    exact hb
  · have hmem : kap b ∈ Lc X g := (mem_Lc X g).2 ⟨b, hb, rfl⟩
    set n := bZ.repr ⟨kap b, hmem⟩
    have h1 := congrArg Subtype.val (bZ.sum_repr ⟨kap b, hmem⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower] at h1
    have hb' : b = ∑ j, (n j : ℂ) • th (eR j) := by
      calc b = thL (kap b) := (th_kap (herm_of_LZ X g hb)).symm
        _ = thL (∑ j, ((n j : ℝ)) • eR j) := by
            congr 1
            rw [← h1]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [heR, Int.cast_smul_eq_zsmul]
        _ = ∑ j, (n j : ℂ) • th (eR j) := by

            rw [map_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [map_smul, hc]
            rfl
    refine ⟨n, hb', fun n' hn' => ?_⟩
    have e : ∑ j, (n' j : ℝ) • th (eR j) = ∑ j, (n j : ℝ) • th (eR j) := by
      have := hn'.symm.trans hb'
      simpa only [hc] using this
    have hz := Fintype.linearIndependent_iff.1 hli (fun j => (n' j : ℝ) - n j) (by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [e, sub_self])
    funext j
    have := sub_eq_zero.1 (hz j)
    exact_mod_cast this

end

end ReciprocityTheory.ChartRestriction.G.FD.FixedPointImaginarySpan
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientsOfVectorGroup

section

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex MeasureTheory FourierCoefficientMatrices FourierCubeVolume FourierCubeIntegral

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem fourier_coefficients_of_vector_group (hL1 : UnipotentVectorGroup (E := E)) : FourierCoefficientProperties (E := E) := by
  intro r X u g hiso hg la G hGd hB hper χ
  classical
  obtain ⟨hadd, hH⟩ := hL1 r X u hiso
  have hunit : ∀ b, IsHermFam b → X.IsUnitaryC (X.zmat u b) := fun b hb => (hH b hb).1
  have hdomH : ∀ b, IsHermFam b → ∀ x ∈ X.dom, X.Zb u b x ∈ X.dom := fun b hb => (hH b hb).2.2.2.1
  have hex : ∃ ω, X.IsLZBasis g ω := FixedPointImaginarySpan.exists_basis X g hg
  obtain ⟨ω, hωdef⟩ : ∃ ω, ω = hex.choose := ⟨_, rfl⟩
  have hω : X.IsLZBasis g ω := hωdef ▸ hex.choose_spec
  have hfz : ∀ ψ x, X.fz u g ψ G x =
      if IsHermFam ψ ∧ X.IsFreqZ g ψ then Ich X u ω G ψ x else 0 := by
    intro ψ x
    unfold Data.fz
    rw [dite_eq_left hex, ← hωdef]
    rfl
  have hsum : ∀ x ∈ X.dom, Summable (fun ψ : X.Ψ → Fin 2 → Fin 2 → ℂ => ‖X.fz u g ψ G x‖) →
      HasSum (fun ψ : X.Ψ → Fin 2 → Fin 2 → ℂ => X.fz u g ψ G x) (G x) := by
    intro x hx hs
    have hωh := herm_ω hω
    have hli := hω.2.2
    obtain ⟨c, hc⟩ : ∃ c : (Fin (4 * Fintype.card X.Ψ) → ℤ) → X.Ψ → Fin 2 → Fin 2 → ℂ,
        c = fun m => chiOf ω hωh hli rfl fun j => (m j : ℝ) := ⟨_, rfl⟩
    have hcm : ∀ m, c m = chiOf ω hωh hli rfl fun j => (m j : ℝ) := fun m => by rw [hc]
    have hc_inj : Function.Injective c := by
      intro m m' h
      rw [hcm, hcm] at h
      have h' := chiOf_inj ω hωh hli rfl h
      funext j
      exact_mod_cast congrFun h' j
    have hcfreq : ∀ m, IsHermFam (c m) ∧ X.IsFreqZ g (c m) := by
      intro m
      refine ⟨by rw [hcm]; exact chiOf_herm ω hωh hli rfl _, ?_⟩
      intro b hb
      obtain ⟨n, hn, -⟩ := hω.2.1 b hb
      refine ⟨∑ j, n j * m j, ?_⟩
      have hb' : b = ∑ j, ((n j : ℝ) : ℂ) • ω j := by
        rw [hn]
        simp only [Complex.ofReal_intCast]
      show 2 * pr (c m) b = _
      rw [hb', pr_sum, Finset.mul_sum]
      push_cast
      refine Finset.sum_congr rfl fun j _ => ?_
      have hp : 2 * pr (c m) (ω j) = (m j : ℝ) := by
        rw [hcm]
        exact chiOf_pair ω hωh hli rfl _ j
      calc 2 * ((n j : ℝ) * pr (c m) (ω j)) = (n j : ℝ) * (2 * pr (c m) (ω j)) := by ring
        _ = (n j : ℝ) * (m j : ℝ) := by rw [hp]
    obtain ⟨D, hD⟩ := I2.DimB.descend (fun t => G (X.Zb u (Bv ω t) x))
      (psi_cont hω hdomH hGd hx) (fun n t => psi_per hω hadd hdomH hper hx n t)
    have hcoef : ∀ m, X.fz u g (c m) G x = UnitAddTorus.mFourierCoeff D m := by
      intro m
      rw [hfz, if_pos (hcfreq m)]
      refine Ich_coeff (fun j => ?_) D hD
      show 2 * pr (c m) (ω j) = (m j : ℝ)
      rw [hcm]
      exact chiOf_pair ω hωh hli rfl _ j
    have hsupp : ∀ ψ ∉ Set.range c, X.fz u g ψ G x = 0 := by
      intro ψ hψ
      rw [hfz]
      split_ifs with h
      · exfalso
        apply hψ
        choose k hk using fun j => h.2 (ω j) (hω.1 j)
        refine ⟨k, ?_⟩
        rw [hcm]
        exact (chiOf_eq ω hωh hli rfl h.1 (m := fun j => (k j : ℝ)) hk).symm
      · rfl
    have hsm : Summable (UnitAddTorus.mFourierCoeff D) := by
      refine Summable.of_norm ((hs.comp_injective hc_inj).congr fun m => ?_)
      simp only [Function.comp, hcoef]
    have hG0 : D (I2.DimB.tproj 0) = G x := by
      rw [hD, Bv_zero, Zb_zero]
    have hF := UnitAddTorus.hasSum_mFourier_series_apply_of_summable hsm (I2.DimB.tproj 0)
    rw [hG0] at hF
    have hF' : HasSum (UnitAddTorus.mFourierCoeff D) (G x) := by
      simpa [I2.DimB.mF_tproj] using hF
    rw [← hc_inj.hasSum_iff hsupp]
    have hcomp : (fun ψ : X.Ψ → Fin 2 → Fin 2 → ℂ => X.fz u g ψ G x) ∘ c =
        UnitAddTorus.mFourierCoeff D := funext fun m => hcoef m
    rw [hcomp]
    exact hF'
  by_cases hχ : IsHermFam χ ∧ X.IsFreqZ g χ
  · have hfe : X.fz u g χ G = Ich X u ω G χ := funext fun x => by rw [hfz, if_pos hχ]
    have hfreq : ∀ j, ∃ k : ℤ, 2 * X.pairR χ (ω j) = k := fun j => hχ.2 (ω j) (hω.1 j)
    refine ⟨⟨?_, ?_, ?_⟩, ?_, hsum⟩
    · rw [hfe]
      exact Ich_diff hω hdomH hGd χ
    · intro x hx b hb
      rw [hfe]
      exact Ich_rmul la hB hω hdomH χ hx hb
    · intro b hb x hx
      rw [hfe]
      exact Ich_Zb hω hadd hdomH hGd hper hfreq hb hx
    · intro x hx M hM
      rw [pnorm_eq, hfe]
      exact Ich_bound hω hunit la χ x hM
  · have hfe : X.fz u g χ G = fun _ => 0 := funext fun x => by rw [hfz, if_neg hχ]
    have hh0 : IsHermFam (0 : X.Ψ → Fin 2 → Fin 2 → ℂ) := by
      have h := th_herm (0 : X.Ψ → Fin 2 → Fin 2 → ℝ)
      rwa [th_zero] at h
    refine ⟨⟨?_, ?_, ?_⟩, ?_, hsum⟩
    · rw [hfe]
      exact differentiableOn_const 0
    · intro x hx b hb
      rw [hfe]
      simp
    · intro b hb x hx
      rw [hfe]
      simp
    · intro x hx M hM
      have h0 := hM 0 hh0
      rw [Zb_zero, pnorm_eq] at h0
      rw [pnorm_eq, hfe]
      simp only [norm_zero, zero_mul]
      exact (mul_nonneg (norm_nonneg _) (fac_nonneg X la x)).trans h0

theorem fourier_coefficients_holds : FourierCoefficientProperties (E := E) :=
  fourier_coefficients_of_vector_group unipotent_vector_group

end ReciprocityTheory.ChartRestriction.G.FD
end
end
