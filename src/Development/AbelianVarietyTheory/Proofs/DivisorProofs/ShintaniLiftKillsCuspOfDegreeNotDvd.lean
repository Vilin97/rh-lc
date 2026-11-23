module

public import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardExponentTuplesModEqOneOfPrimeNotDvdStatement
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.EndomorphismMassMobiusInverseMonicEqStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvariantSubspaceMobiusInverseCharpolyLinearEquiStatement
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsPrimitiveEndClassFunctionInvariantSubspaceMobiStatement
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.PrimitiveEndClassFunctionZeroOfCharpolyMassZero
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.PrimitiveEndClassFunctionZeroOfCharpolyMassZeroStatement
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.RootPowerSumCharacterAdditiveAndXSubOnePowStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootSumMapFrobeniusPowStatement
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
public import Mathlib.FieldTheory.Finite.Extension
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Charpoly.BaseChange
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
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Mathlib.FieldTheory.Finite.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCharacterGLFiniteFieldFrobeniusPowStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCharacterGLIsCharacterNormOneOfRegularStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVirtualCharacterShintaniPsiLiftStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveFunctionCharpolyPairProdRootSumStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdRootPowerSumMapGaloisEqStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiSumEqCharSumAgainstCuspForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularPairLiftToPrimePowerField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShintaniLiftClassFunctionIsometryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedHarishChandraInductionGLIsTwistedClassFunStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedVirtualCharacterNormOneSupportStatement
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCharacterGLFiniteFieldEqOfModEq

section

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem pow_card_pow_sub_one_of_root (F : Type) [Field F] [Finite F] (f : F[X]) (hf : f.Monic)
    (hi : Irreducible f) (m : ℕ) (hd : f.natDegree ∣ m) (α : AlgebraicClosure F)
    (hα : α ∈ (f.map (algebraMap F (AlgebraicClosure F))).roots) (h0 : α ≠ 0) :
    α ^ (Nat.card F ^ m - 1) = 1 := by
  have hf0 : f.map (algebraMap F (AlgebraicClosure F)) ≠ 0 := Polynomial.map_ne_zero hi.ne_zero
  have hr : aeval α f = 0 := by
    have := (mem_roots hf0).1 hα
    rwa [IsRoot, eval_map_algebraMap] at this
  have hmin : f = minpoly F α := minpoly.eq_of_irreducible_of_monic hi hr hf
  have hx : IsIntegral F α := Algebra.IsIntegral.isIntegral α
  have hfix : α ^ Nat.card F ^ m = α := by
    have h1 := ((minpoly.irreducible hx).natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X (n := m)).1
      (by rw [← hmin]; exact hd)
    rw [minpoly.dvd_iff] at h1
    simpa [sub_eq_zero] using h1
  have hpos : 1 ≤ Nat.card F ^ m := Nat.one_le_pow _ _ Nat.card_pos
  have : α ^ (Nat.card F ^ m - 1) * α = 1 * α := by
    rw [← pow_succ, Nat.sub_add_cancel hpos, hfix, one_mul]
  exact mul_right_cancel₀ h0 this

theorem pow_eq_pow_of_modEq' {M : Type} [Monoid M] (α : M) (N a b : ℕ) (h : α ^ N = 1)
    (hab : a ≡ b [MOD N]) : α ^ a = α ^ b := by
  rw [← Nat.div_add_mod a N, ← Nat.div_add_mod b N, pow_add, pow_add, pow_mul, pow_mul, h, one_pow,
    one_pow, hab]

end GlobalTheory.Shin

namespace GlobalTheory.Shin

theorem rootSum_eq_of_modEq (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (f : F[X])
    (hf : f.Monic) (hi : Irreducible f) (hc : f.coeff 0 ≠ 0) (m k k' a : ℕ) (hd : f.natDegree ∣ m)
    (hk : k' ≡ k * Nat.card F ^ a [MOD Nat.card F ^ m - 1]) :
    rootSum θ k' f = rootSum θ k f := by
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨n, -, hn⟩ := FiniteField.card F (ringChar F)
  have hq : ringChar F ^ ((n : ℕ) * a) = Nat.card F ^ a := by
    rw [Nat.card_eq_fintype_card, hn, pow_mul]
  have hgal := GlobalTheory.T.rootSum_map_frobenius_pow_eq_rootSum_mul F θ (RingHom.id F) ((n : ℕ) * a) (fun x => by
    rw [hq, Nat.card_eq_fintype_card, FiniteField.pow_card_pow]; rfl) k f
  rw [Polynomial.map_id, hq] at hgal
  rw [hgal]
  unfold rootSum
  congr 1
  refine Multiset.map_congr rfl fun α hα => ?_
  have hf0 : f.map (algebraMap F (AlgebraicClosure F)) ≠ 0 := Polynomial.map_ne_zero hi.ne_zero
  have h0 : α ≠ 0 := by
    rintro rfl
    have h := (mem_roots hf0).1 hα
    rw [IsRoot, ← coeff_zero_eq_eval_zero, coeff_map] at h
    exact hc ((algebraMap F (AlgebraicClosure F)).injective (by rw [h, map_zero]))
  rw [← map_pow, ← map_pow,
    pow_eq_pow_of_modEq' α _ _ _ (pow_card_pow_sub_one_of_root F f hf hi m hd α hα h0) hk]

end GlobalTheory.Shin

namespace GlobalTheory.Shin

theorem cusp_eq_of_modEq : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ),
    (∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) →
    ∀ m k k' a : ℕ, 0 < m → k' ≡ k * Nat.card F ^ a [MOD Nat.card F ^ m - 1] →
      cusp θ m k' = cusp θ m k := by
  intro F _ _ θ _ m k k' a _ hk
  funext x
  unfold cusp psiG
  congr 1
  set V := Fin m → F
  set g : Module.End F V := Matrix.toLin' (x : Matrix (Fin m) (Fin m) F)
  have hV : Finite V := Module.finite_of_finite F
  have hE : Finite (Module.End F V) := Finite.of_injective _ DFunLike.coe_injective
  have hs := (GlobalTheory.T.rootPowerSumCharacter_additive_and_X_sub_one_pow F θ k).1
  have hs' := (GlobalTheory.T.rootPowerSumCharacter_additive_and_X_sub_one_pow F θ k').1
  let φ : Module.End F V → ℂ := fun h => psi (rootSum θ k') V h - psi (rootSum θ k) V h
  have hc : IsClassFn φ := by
    intro e h
    simp only [φ, GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_linearEquiv_conj]
  have hp : GlobalTheory.CuspGL.IsPrimitive φ := by
    intro A hA hA' g' hg'
    have e1 := GlobalTheory.T.isPrimitiveEndClassFunction_invariantSubspaceMobiusInverse F V _ hs' A hA hA' g' hg'
    have e2 := GlobalTheory.T.isPrimitiveEndClassFunction_invariantSubspaceMobiusInverse F V _ hs A hA hA' g' hg'
    have := finsum_mem_lin_comb_of_finite (nilRad A) 1 1 (fun h => psi (rootSum θ k') V (g' + h))
      (fun h => psi (rootSum θ k) V (g' + h))
    simp only [one_mul] at this
    simp only [φ]
    rw [this, e1, e2, sub_zero]
  have hP : (LinearMap.charpoly g).Monic := LinearMap.charpoly_monic g
  have hdeg : (LinearMap.charpoly g).natDegree = Module.finrank F V := LinearMap.charpoly_natDegree g
  have hdegm : (LinearMap.charpoly g).natDegree = m := by rw [hdeg, Module.finrank_fin_fun]
  have hc0 : (LinearMap.charpoly g).coeff 0 ≠ 0 := by
    intro h0
    have hdet := LinearMap.det_eq_sign_charpoly_coeff g
    rw [h0, mul_zero, LinearMap.det_toLin'] at hdet
    exact ((Matrix.isUnit_iff_isUnit_det _).1 x.isUnit).ne_zero hdet
  have hmang : mangoldt (rootSum θ k') (LinearMap.charpoly g) =
      mangoldt (rootSum θ k) (LinearMap.charpoly g) := by
    unfold mangoldt
    refine finsum_mem_congr rfl fun f hf => ?_
    obtain ⟨hfm, hfi, r, hr, hfr⟩ := hf
    refine rootSum_eq_of_modEq F θ f hfm hfi ?_ m k k' a ?_ hk
    · intro h
      apply hc0
      rw [hfr, coeff_zero_eq_eval_zero, eval_pow, ← coeff_zero_eq_eval_zero, h, zero_pow hr.ne']
    · refine ⟨r, ?_⟩
      rw [← hdegm, hfr, natDegree_pow, mul_comm]
  have hmass : mass φ (LinearMap.charpoly g) = 0 := by
    have := finsum_mem_lin_comb_of_finite {h : Module.End F V | LinearMap.charpoly h = LinearMap.charpoly g}
      1 1 (psi (rootSum θ k') V) (psi (rootSum θ k) V)
    simp only [one_mul] at this
    unfold mass
    simp only [φ]
    rw [this]
    have m1 := GlobalTheory.T.endomorphismMass_mobiusInverse_monic_eq F V _ hs' _ hP hdeg
    have m2 := GlobalTheory.T.endomorphismMass_mobiusInverse_monic_eq F V _ hs _ hP hdeg
    unfold mass at m1 m2
    rw [m1, m2, hmang, sub_self]
  exact sub_eq_zero.1 (GlobalTheory.T.primitiveEndClassFunction_zero_of_charpoly_mass_zero F V φ hc hp g hmass)

end GlobalTheory.Shin
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCharacterGLFiniteFieldEqOfModEqStatement

section

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.cuspidalCharacterGLFiniteField_eq_of_modEq : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ), (∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ m k k' a : ℕ, 0 < m → k' ≡ k * Nat.card F ^ a [MOD Nat.card F ^ m - 1] → cusp θ m k' = cusp θ m k := by
  first | (exact @GlobalTheory.Shin.cusp_eq_of_modEq) | (exact GlobalTheory.Shin.cusp_eq_of_modEq) | (intros; apply GlobalTheory.Shin.cusp_eq_of_modEq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShintaniLiftCuspidalVanishing

section

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem shLift_cusp_kills_of_not_dvd : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (Module.finrank F F').Prime → s ≠ 1 → ∀ (ι : AlgebraicClosure F →ₐ[F] AlgebraicClosure F') (θ : AlgebraicClosure F' →* ℂ), (∀ x y : AlgebraicClosure F', x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ n k : ℕ, 0 < n → ¬ Module.finrank F F' ∣ n → Reg (Nat.card F) n k → Kills (shLift s (cusp (pullθ ι θ) n k)) (cusp θ n (k * ∑ i ∈ Finset.range (Module.finrank F F'), Nat.card F ^ (n * i))) := by
  intro F F' _ _ _ _ s hl hs ι θ hθ n k hn hnd hreg
  haveI : Finite F := Finite.of_injective _ (algebraMap F F').injective
  haveI := Fintype.ofFinite F
  haveI := Fintype.ofFinite F'
  haveI : Fact (Module.finrank F F').Prime := ⟨hl⟩
  set l := Module.finrank F F' with hl_def
  set q := Nat.card F with hq_def
  have hq2 : 2 ≤ q := Finite.one_lt_card
  have hcard' : Nat.card F' = q ^ l := by
    rw [hq_def, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := F)]
  set K := k * ∑ i ∈ Finset.range l, q ^ (n * i) with hK_def
  obtain ⟨hregK, a, ha⟩ := GlobalTheory.T.regular_pair_lift_to_prime_power_field q l n k hq2 hl hn hnd hreg
  have hregK' : Reg (Nat.card F') n K := by rw [hcard']; exact hregK
  obtain ⟨hYchar, -⟩ := GlobalTheory.T.cuspidalCharacterGL_isCharacter_norm_one_of_regular F' θ hθ n K hn hregK'
  have hYs : ∀ g, cusp θ n K (galAct F F' n s g) = cusp θ n K g := by
    intro g
    obtain ⟨⟨i, hi⟩, hi'⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow F F').2 s
    simp only at hi'
    obtain ⟨r, hp, hr⟩ := FiniteField.card F (ringChar F)
    have hchar : ringChar F' = ringChar F := (Algebra.ringChar_eq F F').symm
    have hsx : ∀ x, s.toRingEquiv x = x ^ (ringChar F' ^ ((r : ℕ) * i)) := by
      intro x
      change s x = _
      rw [← hi', AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate, hr, hchar, pow_mul]
    have h1 := GlobalTheory.T.cuspidalCharacterGLFiniteField_frobenius_pow F' θ s.toRingEquiv ((r : ℕ) * i) hsx n K g
    have hpq : ringChar F' ^ ((r : ℕ) * i) = q ^ i := by
      rw [hchar, pow_mul, ← hr, hq_def, Nat.card_eq_fintype_card]
    rw [hpq] at h1
    have hpow : ∀ j, K * q ^ j ≡ K * Nat.card F' ^ (a * j) [MOD Nat.card F' ^ n - 1] := by
      intro j
      induction j with
      | zero => simp only [pow_zero, mul_zero, mul_one]; exact Nat.ModEq.refl _
      | succ j ih =>
        have e1 : K * q ^ (j + 1) = (K * q ^ j) * q := by ring
        have e2 : K * Nat.card F' ^ (a * (j + 1)) = (K * (q ^ l) ^ a) * Nat.card F' ^ (a * j) := by
          rw [hcard']; ring
        rw [e1, e2]
        calc K * q ^ j * q ≡ K * Nat.card F' ^ (a * j) * q [MOD Nat.card F' ^ n - 1] := ih.mul_right _
          _ = (K * q) * Nat.card F' ^ (a * j) := by ring
          _ ≡ (K * (q ^ l) ^ a) * Nat.card F' ^ (a * j) [MOD Nat.card F' ^ n - 1] := by
            apply Nat.ModEq.mul_right
            rw [hcard']; exact ha
    have h2 := GlobalTheory.T.cuspidalCharacterGLFiniteField_eq_of_modEq F' θ hθ n K (K * q ^ i) (a * i) hn (hpow i)
    rw [galAct_apply]
    exact h1.trans (congrFun h2 g)
  obtain ⟨X0, hX0, hX0a, hX0b⟩ := GlobalTheory.T.exists_virtualCharacter_shintani_psi_lift F F' s hl hs ι θ hθ k n
  set c : ℂ := (-1) ^ (n - 1) with hc_def
  have hc2 : c * c = 1 := by rw [hc_def, ← mul_pow]; simp
  have hcstar : star c = c := by rw [hc_def]; simp
  set X : GHat F F' n → ℂ := fun x => c * X0 x with hX_def
  have hX : X ∈ Virt ℂ ℂ (GHat F F' n) := by
    have e : X = ((-1 : ℤ) ^ (n - 1)) • X0 := by
      funext x
      simp only [hX_def, Pi.smul_apply, zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, hc_def]
    rw [e]
    exact AddSubgroup.zsmul_mem _ hX0 _
  have hfun : (fun δ => X (inl δ * inr s)) = shLift s (cusp (pullθ ι θ) n k) := by
    funext δ
    simp only [hX_def, hX0b]
    by_cases h : ∃ γ, IsNorm s δ γ <;> simp [shLift, cusp, h, hc_def]
  have hcl : IsCl (cusp (pullθ ι θ) n k) := by
    intro x y
    have := ((GlobalTheory.T.twistedHarishChandraInductionGL_isTwistedClassFunction F (RingHom.id F) 0 0 n (fun _ => 0) (fun _ => 0)).2.2 (rootSum (pullθ ι θ) k)).1 x y
    simp only [cusp]
    rw [this]
  have hinj : Function.Injective ι := ι.toRingHom.injective
  have hθ' : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → pullθ ι θ x = pullθ ι θ y → x = y := by
    intro x y hx hy h
    apply hinj
    refine hθ _ _ ?_ ?_ h
    · exact fun h0 => hx (hinj (h0.trans (map_zero ι).symm))
    · exact fun h0 => hy (hinj (h0.trans (map_zero ι).symm))
  obtain ⟨-, hnormF⟩ := GlobalTheory.T.cuspidalCharacterGL_isCharacter_norm_one_of_regular F (pullθ ι θ) hθ' n k hn hreg
  have hΓ : Nat.card (F' ≃ₐ[F] F') = l := IsGalois.card_aut_eq_finrank F F'
  have htop : ∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s := fun t => by
    rw [zpowers_eq_top_of_prime_card hΓ hs]; trivial
  have hiso := GlobalTheory.T.shintaniLiftClassFunction_isometry F F' s htop n _ _ hcl hcl
  rw [hnormF] at hiso
  have hnorm : ∑ᶠ g, X (inl g * inr s) * star (X (inl g * inr s)) = (Nat.card (GL (Fin n) F') : ℂ) := by
    have e : ∀ g, X (inl g * inr s) * star (X (inl g * inr s)) =
        shLift s (cusp (pullθ ι θ) n k) g * star (shLift s (cusp (pullθ ι θ) n k) g) := fun g => by
      rw [← congrFun hfun g]
    rw [finsum_congr e]
    have hpos : (Nat.card (GL (Fin n) F) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
    apply mul_left_cancel₀ hpos
    rw [hiso, mul_comm]
  set S : F'[X] → ℂ := fun P => ∏ t : F' ≃ₐ[F] F', rootSum θ k (P.map (t : F' →+* F')) with hS_def
  have hS1 : S 1 = 0 := by
    simp only [hS_def, Polynomial.map_one]
    apply Finset.prod_eq_zero (Finset.mem_univ 1)
    simp [rootSum]
  have hSprod : S = fun P => ∏ j : Fin l, rootSum θ (k * q ^ (j : ℕ)) P := by
    funext P
    simp only [hS_def]
    rw [GlobalTheory.T.prod_rootPowerSum_map_galois_eq F F' θ k P, Fin.prod_univ_eq_prod_range (fun j => rootSum θ (k * q ^ j) P) l]
  have hprim := GlobalTheory.T.psi_sum_eq_char_sum_against_cusp_form F' θ S n K hS1
  have hprod := GlobalTheory.T.primitiveFunctionCharpoly_pair_prod_rootSum F' θ hθ n K l (fun j => k * q ^ (j : ℕ)) hn
  rw [hcard'] at hprod
  set cnt := (Finset.univ.filter fun a : Fin l → Fin n =>
    K ≡ ∑ j : Fin l, k * q ^ (j : ℕ) * (q ^ l) ^ (a j : ℕ) [MOD (q ^ l) ^ n - 1]).card with hcnt_def
  have hcnt : cnt ≡ 1 [MOD l] := GlobalTheory.T.card_exponent_tuples_modEq_one_of_prime_not_dvd q l n k hq2 hl hn hnd hreg
  have hz : ∑ᶠ g, X (inl g) * star (cusp θ n K g) = ((cnt : ℤ) : ℂ) * (Nat.card (GL (Fin n) F') : ℂ) := by
    simp only [finsum_eq_sum_of_fintype] at hprim hprod ⊢
    have e1 : ∀ g, X (inl g) * star (cusp θ n K g) = c * (psiG S n g * star (cusp θ n K g)) := fun g => by
      simp only [hX_def, hX0a]; ring
    rw [Finset.sum_congr rfl (fun g _ => e1 g), ← Finset.mul_sum, hprim]
    have e2 : ∀ g, chG S n g * star (cusp θ n K g) = star (cusp θ n K g * star (chG S n g)) := fun g => by
      rw [star_mul, star_star, mul_comm]
    rw [Finset.sum_congr rfl (fun g _ => e2 g), ← star_sum]
    have e3 : ∀ g, cusp θ n K g * star (chG S n g) = c * (psiG (rootSum θ K) n g * star (chG S n g)) :=
      fun g => by simp only [cusp, hc_def]; ring
    rw [Finset.sum_congr rfl (fun g _ => e3 g), ← Finset.mul_sum, hSprod, hprod, star_mul', hcstar, ← mul_assoc, hc2,
      one_mul, star_mul', star_natCast, star_natCast]
    push_cast
    ring
  have hndvd : ¬ ((Nat.card (F' ≃ₐ[F] F') : ℤ) ∣ (cnt : ℤ)) := by
    rw [hΓ, Int.natCast_dvd_natCast]
    intro h
    have h1 : cnt % l = 1 % l := hcnt
    rw [(Nat.dvd_iff_mod_eq_zero).1 h, Nat.mod_eq_of_lt hl.one_lt] at h1
    exact zero_ne_one h1
  have key := GlobalTheory.T.twisted_virtualCharacter_norm_one_support (GL (Fin n) F') (F' ≃ₐ[F] F') (galAct F F' n) s (hΓ ▸ hl) hs X hX hnorm (cusp θ n K)
    hYchar hYs (cnt : ℤ) hz hndvd
  rw [hfun] at key
  exact key

end GlobalTheory.Shin
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShintaniLiftKillsCuspOfDegreeNotDvd

section

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.shintani_lift_kills_cusp_of_degree_not_dvd : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (Module.finrank F F').Prime → s ≠ 1 → ∀ (ι : AlgebraicClosure F →ₐ[F] AlgebraicClosure F') (θ : AlgebraicClosure F' →* ℂ), (∀ x y : AlgebraicClosure F', x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ n k : ℕ, 0 < n → ¬ Module.finrank F F' ∣ n → Reg (Nat.card F) n k → Kills (shLift s (cusp (pullθ ι θ) n k)) (cusp θ n (k * ∑ i ∈ Finset.range (Module.finrank F F'), Nat.card F ^ (n * i))) := by
  first | (exact @GlobalTheory.Shin.shLift_cusp_kills_of_not_dvd) | (exact GlobalTheory.Shin.shLift_cusp_kills_of_not_dvd) | (intros; apply GlobalTheory.Shin.shLift_cusp_kills_of_not_dvd  <;> assumption)
end
end
