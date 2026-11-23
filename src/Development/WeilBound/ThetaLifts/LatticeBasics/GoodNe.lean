module

public import Development.WeilBound.ThetaLifts.LatticeBasics.PairsStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterOfIdeleClass
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPowHeckeCharUnramifiedEverywhere
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NotIsOfFinOrderHeckeCharacterValueCompletelySpli
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CharacterValueAtT
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsPowLocKMulInf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalIdeleSndSelf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharacterInfiniteOrderAtSplit
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceSplitOrInert
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedCharacterAtUniformizer
import Mathlib.RingTheory.Ideal.Norm.RelNorm

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeValueNotFiniteOrder

section

@[expose] public section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

namespace GlobalTheory.CMSplitValue

open WithZero GlobalTheory.CharVal GlobalTheory.Formalism.L2.Col.HostOk

theorem exists_aut_comp {E : Type} [Field E] [NumberField E] [IsGalois ℚ E] (τ₀ τ₁ : E →+* ℂ) :
    ∃ g : E ≃ₐ[ℚ] E, ∀ x, τ₀ (g x) = τ₁ x := by
  letI : Algebra E ℂ := τ₀.toAlgebra
  haveI : IsScalarTower ℚ E ℂ := IsScalarTower.of_algebraMap_eq fun q => by
    show algebraMap ℚ ℂ q = τ₀ (algebraMap ℚ E q)
    rw [eq_ratCast (algebraMap ℚ ℂ), eq_ratCast (algebraMap ℚ E), map_ratCast]
  exact ⟨(τ₁.toRatAlgHom).restrictNormal' E, fun x => (τ₁.toRatAlgHom).restrictNormal_commutes E x⟩

theorem not_isOfFinOrder_val_of_tame (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) (hgal : IsGalois ℚ E) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (χ : Formalism.L2.Host.HChar E) (n : InfinitePlace F → ℤ) (ht : ∀ v, χ.TameAt v) (hinf : χ.HasInf (fun w => (τ w).1) n)
    (hn : ∀ w, n w ≠ 0) (p : ℕ) (hp : p.Prime) (W : HeightOneSpectrum (𝓞 E)) (hN : Ideal.absNorm W.asIdeal = p)
    (hsq : (p : 𝓞 E) ∉ W.asIdeal ^ 2) : ¬ IsOfFinOrder (χ.val W) := by
  intro hfin
  classical
  obtain ⟨M, z, hM, h1, h2, h3⟩ := GlobalTheory.TamePow.exists_pow_locK_mul_inf E χ
    (GlobalTheory.Mem.UnrAe.unr_ae_and_level _ χ).1.toFinset (GlobalTheory.HeckeProduct.hchar_productRule _ χ)
    (fun v hv => by simpa using hv) ht W (Formalism.L2.Host.unif W)
  obtain ⟨a, ha, hpow⟩ := isOfFinOrder_iff_pow_eq_one.1 hfin
  have h4 : χ.inf z ^ a = 1 := by
    have := congrArg (· ^ a) h3
    simp only [mul_pow, one_pow] at this
    rw [← pow_mul, mul_comm M a, pow_mul] at this
    change χ.val W ^ a = 1 at hpow
    unfold Formalism.L2.Host.HChar.val at hpow
    rwa [hpow, one_pow, one_mul] at this
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace F) := inferInstance
  set τ₀ : E →+* ℂ := (τ w₀).1 with hτ₀
  choose g hg using fun w => exists_aut_comp τ₀ (τ w).1
  have h5 : ((χ.inf z : ℂˣ) : ℂ) ^ 2 = τ₀ (∏ w, (g w z / g w (σ z)) ^ n w) := by
    rw [hinf z, map_prod, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [map_zpow₀, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
    congr 1
    have e : τ₀ (g w (σ z)) = starRingEnd ℂ (τ₀ (g w z)) := by
      rw [hg, hg]
      exact hcm.2.2.2 _ _
    have e' : (τ w).1 z = τ₀ (g w z) := (hg w z).symm
    have h0 : τ₀ (g w z) ≠ 0 := by simp
    rw [map_div₀, e, e', div_pow, div_eq_div_iff (pow_ne_zero _ (by simpa using h0)) (by simpa using h0), sq, mul_assoc,
      Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  have h6 : (∏ w, (g w z / g w (σ z)) ^ n w) ^ a = 1 := by
    apply τ₀.injective
    rw [map_pow, ← h5, ← pow_mul, mul_comm, pow_mul, ← Units.val_pow_eq_pow_val, h4, map_one]
    simp
  have h7 := unit_of_pow (w := W) ha (by rw [h6, map_one])
  have hg0 : ∀ x, g w₀ x = x := fun x => τ₀.injective (hg w₀ x)
  have hres : ∀ w, (∀ f : F, τ₀ (algebraMap F E f) = w.embedding f) → w = w₀ := by
    intro w hw
    have e : w.embedding = w₀.embedding := by
      ext f
      rw [← hw f]
      exact (RingHom.congr_fun (τ w₀).2 f)
    rw [← InfinitePlace.mk_embedding w, e, InfinitePlace.mk_embedding]
  have hc : ∀ w, W.valuation E (g w (σ z)) = 1 := by
    intro w
    refine GlobalTheory.SplitValue.val_map_eq_one hp hN hsq h2 ((g w : E →+* E).comp (σ : E →+* E)) fun e => ?_
    have hw : w = w₀ := hres w fun f => by
      have := RingHom.congr_fun e (algebraMap F E f)
      change g w (σ (algebraMap F E f)) = algebraMap F E f at this
      rw [← this, hg, AlgHom.commutes]
      exact RingHom.congr_fun (τ w).2 f
    subst hw
    obtain ⟨x, hx⟩ := GlobalTheory.AdelicU.exists_cm_conj_ne hcm
    have := RingHom.congr_fun e x
    change g w (σ x) = x at this
    rw [hg0] at this
    exact hx this
  have hgw : ∀ w, w ≠ w₀ → W.valuation E (g w z) = 1 := by
    intro w hw
    refine GlobalTheory.SplitValue.val_map_eq_one hp hN hsq h2 (g w : E →+* E) fun e => hw (hres w fun f => ?_)
    have := RingHom.congr_fun e (algebraMap F E f)
    change g w (algebraMap F E f) = algebraMap F E f at this
    rw [← this, hg]
    exact RingHom.congr_fun (τ w).2 f
  rw [map_prod, Finset.prod_eq_single w₀ (fun w _ h => by rw [map_zpow₀, map_div₀, hgw w h, hc w, div_one, one_zpow])
    (by simp), map_zpow₀, map_div₀, hc, div_one, hg0, h1, val_unif, ← exp_nsmul, ← exp_zsmul,
    ← exp_zero, exp_inj] at h7
  simp only [nsmul_eq_mul, smul_eq_mul, mul_eq_zero] at h7
  rcases h7 with h | h | h
  · exact hn w₀ h
  · omega
  · omega

end GlobalTheory.CMSplitValue

namespace GlobalTheory.CMSplitValue

theorem not_isOfFinOrder_val : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → IsGalois ℚ E → ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (H : Formalism.L2.Host.HChar E) (n : InfinitePlace F → ℤ), H.HasInf (fun w => (τ w).1) n → (∀ w, n w ≠ 0) → ∀ (p : ℕ), p.Prime → ∀ W : HeightOneSpectrum (𝓞 E), Ideal.absNorm W.asIdeal = p → (p : 𝓞 E) ∉ W.asIdeal ^ 2 → ¬ IsOfFinOrder (H.val W) := by
  intro F E _ _ _ _ _ σ hcm hgal τ H n hinf hn p hp W hN hsq hfin
  obtain ⟨N, hN0, hunr⟩ := GlobalTheory.Corev.UnrPow.exists_pow_unrAt E H
  have ht : ∀ v, (H ^ N).TameAt v := fun v x hx _ => hunr v x hx
  have hinf' : (H ^ N).HasInf (fun w => (τ w).1) (fun w => (N : ℤ) * n w) := by
    intro k
    rw [GlobalTheory.SplitValuePow.inf_pow, Units.val_pow_eq_pow_val, hinf k, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [← zpow_natCast, ← zpow_mul, mul_comm]
  refine not_isOfFinOrder_val_of_tame F E σ hcm hgal τ (H ^ N) _ ht hinf'
    (fun w => mul_ne_zero (by exact_mod_cast hN0.ne') (hn w)) p hp W hN hsq ?_
  rw [GlobalTheory.SplitValuePow.val_pow]
  exact hfin.pow

end GlobalTheory.CMSplitValue
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPrimeDegreeOne

section

@[expose] public section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

namespace GlobalTheory.SplitFullyNorm

theorem exists_prime_absNorm_eq_of_splitsFully (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (W : HeightOneSpectrum (𝓞 E)) (h : SplitsFully E (W.under (𝓞 F))) :
    ∃ p : ℕ, p.Prime ∧ Ideal.absNorm W.asIdeal = p ∧ (p : 𝓞 E) ∉ W.asIdeal ^ 2 := by
  classical

  set P : Ideal ℤ := W.asIdeal.under ℤ with hPdef
  have hP0 : P ≠ ⊥ := mt Ideal.eq_bot_of_comap_eq_bot W.ne_bot
  haveI hPprime : P.IsPrime := Ideal.IsPrime.under ℤ W.asIdeal
  haveI hPmax : P.IsMaximal := hPprime.isMaximal hP0

  have hunder : (W.under (𝓞 F)).asIdeal.under ℤ = P := by
    change (W.asIdeal.under (𝓞 F)).under ℤ = W.asIdeal.under ℤ
    exact Ideal.under_under _
  have hcard : (P.primesOver (𝓞 E)).ncard = Module.finrank ℚ E := by
    have h' := h
    unfold SplitsFully at h'
    rwa [hunder] at h'

  have hsum := Ideal.sum_ramification_inertia_eq_finrank P (𝓞 E)
  rw [NumberField.RingOfIntegers.rank] at hsum

  have hone : ∀ q : P.primesOver (𝓞 E), q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ = 1 := by
    intro q
    haveI : q.1.IsPrime := q.2.1
    have hpos := Nat.mul_pos (Ideal.ramificationIdx_pos (R := ℤ) q.1) (Ideal.inertiaDeg_pos q.1 ℤ)
    by_contra hne
    have hlt : ∑ _r : P.primesOver (𝓞 E), (1 : ℕ) <
        ∑ r : P.primesOver (𝓞 E), r.1.ramificationIdx ℤ * r.1.inertiaDeg ℤ := by
      apply Finset.sum_lt_sum
      · intro r _
        haveI : r.1.IsPrime := r.2.1
        exact Nat.mul_pos (Ideal.ramificationIdx_pos (R := ℤ) r.1) (Ideal.inertiaDeg_pos r.1 ℤ)
      · exact ⟨q, Finset.mem_univ _, by omega⟩
    rw [hsum, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, Fintype.card_eq_nat_card,
      Nat.card_coe_set_eq, hcard] at hlt
    exact lt_irrefl _ hlt
  have hWmem : W.asIdeal ∈ P.primesOver (𝓞 E) := ⟨W.isPrime, ⟨rfl⟩⟩
  have hw := hone ⟨W.asIdeal, hWmem⟩
  have he : W.asIdeal.ramificationIdx ℤ = 1 := Nat.eq_one_of_mul_eq_one_right hw
  have hf : W.asIdeal.inertiaDeg ℤ = 1 := Nat.eq_one_of_mul_eq_one_left hw

  set n : ℕ := (Submodule.IsPrincipal.generator P).natAbs with hn
  have hspan : Ideal.span {((n : ℕ) : ℤ)} = P := by
    rw [hn, Int.span_natAbs, Ideal.span_singleton_generator]
  have hn0 : ((n : ℕ) : ℤ) ≠ 0 := by
    intro h0
    apply hP0
    rw [← hspan, h0, Ideal.span_singleton_eq_bot]
  have hnprime : n.Prime := by
    rw [Nat.prime_iff_prime_int, ← Ideal.span_singleton_prime hn0, hspan]
    exact hPprime
  haveI : W.asIdeal.LiesOver (Ideal.span {((n : ℕ) : ℤ)}) := ⟨by rw [hspan]⟩
  refine ⟨n, hnprime, ?_, ?_⟩
  ·
    rw [← Ideal.pow_inertiaDeg n W.asIdeal, hf, pow_one]
  ·
    intro hmem
    have hmap0 : P.map (algebraMap ℤ (𝓞 E)) ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot hP0
    have hle : P.map (algebraMap ℤ (𝓞 E)) ≤ W.asIdeal ^ 2 := by
      rw [← hspan, Ideal.map_span, Set.image_singleton, Ideal.span_le, Set.singleton_subset_iff]
      simpa using hmem
    have hdvd : W.asIdeal ^ 2 ∣ P.map (algebraMap ℤ (𝓞 E)) := Ideal.dvd_iff_le.mpr hle
    have hfin : FiniteMultiplicity W.asIdeal (P.map (algebraMap ℤ (𝓞 E))) :=
      FiniteMultiplicity.of_not_isUnit (by rw [Ideal.isUnit_iff]; exact W.isPrime.ne_top) hmap0
    have h2 := hfin.le_multiplicity_of_pow_dvd hdvd
    rw [← Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity P W.asIdeal hmap0, he] at h2
    omega

end GlobalTheory.SplitFullyNorm
end
end

-- Source module: Development.WeilBound.ThetaLifts.LatticeBasics.GoodNe

section

@[expose] public section

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {B : Base F E}
  {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

theorem isHecke_nu (h : IsTriple B G X om om') : IsHecke F E X.ν :=
  ⟨(h.chars.heckeα.1.div' h.chars.heckeβ.1 :), fun x => by
    rw [Chars.ν, MonoidHom.div_apply, h.chars.heckeα.2 x, h.chars.heckeβ.2 x, div_one]⟩

theorem hasExp_nu (h : IsTriple B G X om om') : HasExp B.emb X.ν (fun w => B.mα w - B.mβ w) := by
  intro z hz
  show (((X.α z / X.β z : Circle)) : ℂ) = _
  rw [Circle.coe_div, h.chars.expα z hz, h.chars.expβ z hz, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hne : piInf (B.emb w) z ≠ 0 := (z.isUnit.map (piInf (B.emb w))).ne_zero
  rw [zpow_sub₀ (div_ne_zero hne (by exact_mod_cast (norm_ne_zero_iff.2 hne)))]

theorem nonempty_emb_of_splitsFully (hB : B.IsGood σ) {v : Pl F} (hv : SplitsFully E v) : Nonempty (E →ₐ[F] Fv F v) := by
  refine (GlobalTheory.KFinLoc.split_or_inert F E σ B hB v).resolve_right ?_
  rintro ⟨w, hw⟩
  have hw' : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = w.asIdeal := hw
  have hu : w.under (𝓞 F) = v := (HeightOneSpectrum.ext (v.isMaximal.eq_of_le (w.under (𝓞 F)).isPrime.ne_top
    (Ideal.map_le_iff_le_comap.1 hw'.le))).symm
  obtain ⟨p, hp, hN, -⟩ := GlobalTheory.SplitFullyNorm.exists_prime_absNorm_eq_of_splitsFully F E w (hu ▸ hv)
  rw [← hw', Ideal.absNorm_algebraMap, ← Algebra.IsAlgebraic.finrank_of_isFractionRing (𝓞 F) F (𝓞 E) E, hB.cm.2.2.1] at hN
  exact Nat.Prime.not_prime_pow le_rfl (hN ▸ hp)

theorem nu_pow_ne_one (h : IsTriple B G X om om') {v : Pl F} (hv : X.Good v) (t : E →ₐ[F] Fv F v) {k : ℤ} (hk : k ≠ 0) :
    chrW X.ν t (unifAt v) ^ k ≠ 1 := by
  intro hpow
  have hW : splitPrime t ∉ above E (X.T : Set (Pl F)) := fun hmem => hv.1 (by simpa [above, splitPrime_under] using hmem)
  have hunr : UnrAt X.ν (splitPrime t) := by
    rw [Chars.ν, div_eq_mul_inv]
    exact (h.chars.unrα _ hW).mul (h.chars.unrβ _ hW).inv
  rw [GlobalTheory.ChrWUnif.chrW_unifAt F E X.ν v t hunr] at hpow
  obtain ⟨H, hloc, hinf⟩ := GlobalTheory.HeckeBridge.exists_hchar F E σ h.base.cm X.ν (isHecke_nu h)
  have hval : val X.ν (splitPrime t) = H.val (splitPrime t) := (hloc _ _).symm
  obtain ⟨p, hp, hN, hsq⟩ := GlobalTheory.SplitFullyNorm.exists_prime_absNorm_eq_of_splitsFully F E (splitPrime t)
    (by rw [splitPrime_under]; exact hv.2)
  refine GlobalTheory.CMSplitValue.not_isOfFinOrder_val F E σ h.base.cm h.base.galois B.emb H _ (hinf _ _ (hasExp_nu h))
    (fun w => ?_) p hp _ hN hsq ?_
  · have := h.geo.kappa w
    omega
  · rw [← hval]
    exact isOfFinOrder_iff_zpow_eq_one.2 ⟨k, hk, hpow⟩

theorem goodNe : GoodNe := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h _ hv =>
  ⟨nonempty_emb_of_splitsFully h.base hv.2, fun t e => nu_pow_ne_one h hv t one_ne_zero (by rw [e, zpow_one])⟩

end GlobalTheory.ThK.Dbl

end
end
end
