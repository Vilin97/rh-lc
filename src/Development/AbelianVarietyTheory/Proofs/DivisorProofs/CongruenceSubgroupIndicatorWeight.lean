module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnramifiedQuadraticDatumAtInertPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdentityOfPrincipalCongruenceStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaOrbitalIntegralCongruenceInertLatticeCountStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableTwistedOrbitalIntegralIntegralNormCongruen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralLevelFunctionInertEqLatticStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValResultantCharpolyShiftedUnitAdjoinRootStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisUnitMatchAllRanksStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitLemmaLieAlgebraUnitaryGroupOfJacquetRallisStatement
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Lemma

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvolutiveAlgebraAdjoinRootSelfReciprocal

section

@[expose] public section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.InvAlgConstr

theorem exists_invAlg_adjoinRoot : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → ∀ (t : K.O), t ≠ 0 → ∀ Q : (w.adicCompletion E)[X], Q.Monic → IsCsr w Q → ∃ B : GlobalTheory.UnitLemma.InvAlg K, Algebra.adjoin K.E {(1 + algebraMap K.O B.A t * B.g)} = ⊤ ∧ aeval (1 + algebraMap K.O B.A t * B.g) (Q.map e.symm.toRingHom) = 0 ∧ Module.finrank K.E B.A = Q.natDegree ∧ (1 + algebraMap K.O B.A t * B.g) * B.σ (1 + algebraMap K.O B.A t * B.g) = 1 := by
  intro E _ _ _ w hw K e he t ht Q hQ hcsr
  set Q' : K.E[X] := Q.map e.symm.toRingHom with hQ'
  have hinj : Function.Injective (e.symm.toRingHom) := e.symm.injective
  have hQ'm : Q'.Monic := hQ.map _
  have hdeg : Q'.natDegree = Q.natDegree := natDegree_map_eq_of_injective hinj _
  have hc := hcsr.resolve_left hw
  have hQ0 : Q.coeff 0 ≠ 0 := by
    intro h0
    rw [h0, map_zero, C_0, zero_mul] at hc
    exact (hQ.map (cj w)).ne_zero (reverse_eq_zero.mp hc.symm)
  have hQ'0 : Q'.coeff 0 ≠ 0 := by
    rw [hQ', coeff_map]
    exact fun h => hQ0 (hinj (by rw [h, map_zero]))
  let A := AdjoinRoot Q'
  let r : A := AdjoinRoot.root Q'
  let pb := AdjoinRoot.powerBasis' hQ'm
  haveI : Module.Finite K.E A := pb.finite
  have hr0 : aeval r Q' = 0 := by
    rw [aeval_def, AdjoinRoot.algebraMap_eq]; exact AdjoinRoot.eval₂_root Q'
  set v : A := -(aeval r (divX Q')) * algebraMap K.E A (Q'.coeff 0)⁻¹ with hv
  have hrv : r * v = 1 := by
    have h1 := congrArg (aeval r) (X_mul_divX_add Q')
    rw [map_add (f := _), map_mul, aeval_X, aeval_C, hr0] at h1
    have h2 : algebraMap K.E A (Q'.coeff 0) * algebraMap K.E A (Q'.coeff 0)⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hQ'0, map_one]
    linear_combination (-(algebraMap K.E A (Q'.coeff 0)⁻¹)) * h1 + h2
  letI : Invertible v := ⟨r, hrv, by rw [mul_comm]; exact hrv⟩
  have hce : ∀ y, K.c (e.symm y) = e.symm (cj w y) := by
    intro y; apply e.injective; rw [he, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  have hmapc : Q'.map K.c.toRingHom = (Q.map (cj w)).map e.symm.toRingHom := by
    rw [hQ', Polynomial.map_map, Polynomial.map_map]; congr 1; ext y; exact hce y
  have hrev : (Q'.map K.c.toRingHom).reverse = C (e.symm (cj w (Q.coeff 0))) * Q' := by
    rw [hmapc]
    unfold reverse
    rw [natDegree_map_eq_of_injective hinj, reflect_map, ← reverse, ← hc, Polynomial.map_mul, map_C]
    rfl
  have hev : eval₂ ((algebraMap K.E A).comp K.c.toRingHom) v Q' = 0 := by
    rw [← eval₂_map, ← eval₂_reverse_mul_pow (algebraMap K.E A) v, hrev]
    show eval₂ (algebraMap K.E A) r (C (e.symm (cj w (Q.coeff 0))) * Q') * _ = 0
    have hev0 : eval₂ (algebraMap K.E A) r Q' = 0 := by rw [← aeval_def]; exact hr0
    rw [eval₂_mul, hev0, mul_zero, zero_mul]
  let σ0 : A →+* A := AdjoinRoot.lift ((algebraMap K.E A).comp K.c.toRingHom) v hev
  have hσr : σ0 r = v := AdjoinRoot.lift_root hev
  have hσof : ∀ a, σ0 (algebraMap K.E A a) = algebraMap K.E A (K.c a) := fun a => AdjoinRoot.lift_of hev
  have hσv : σ0 v = r := by
    calc σ0 v = σ0 v * (r * v) := by rw [hrv, mul_one]
      _ = σ0 (r * v) * r := by rw [map_mul σ0 r v, hσr]; ring
      _ = r := by rw [hrv, map_one, one_mul]
  have hcomp : σ0.comp σ0 = RingHom.id A := by
    apply Ideal.Quotient.ringHom_ext
    apply Polynomial.ringHom_ext
    · intro a
      show σ0 (σ0 (algebraMap K.E A a)) = algebraMap K.E A a
      rw [hσof, hσof]; simp [K.c_c]
    · show σ0 (σ0 r) = r
      rw [hσr, hσv]
  have hσσ : ∀ y, σ0 (σ0 y) = y := fun y => RingHom.congr_fun hcomp y
  let σ : A ≃+* A :=
    { toFun := σ0, invFun := σ0, left_inv := hσσ, right_inv := hσσ, map_mul' := map_mul σ0, map_add' := map_add σ0 }
  set tE : K.E := algebraMap K.O K.E t
  have htE : tE ≠ 0 := fun h => ht ((IsFractionRing.injective K.O K.E) (by rw [map_zero]; exact h))
  let B : GlobalTheory.UnitLemma.InvAlg K :=
    { A := A, σ := σ, σ_σ := hσσ, σ_alg := hσof, g := (r - 1) * algebraMap K.E A tE⁻¹ }
  have hu : (1 + algebraMap K.O B.A t * B.g) = r := by
    show (1 + algebraMap K.O A t * ((r - 1) * algebraMap K.E A tE⁻¹)) = r
    rw [IsScalarTower.algebraMap_apply K.O K.E A t]
    have h3 : algebraMap K.E A tE * algebraMap K.E A tE⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ htE, map_one]
    linear_combination (r - 1) * h3
  refine ⟨B, ?_, ?_, ?_, ?_⟩
  · rw [hu]; exact AdjoinRoot.adjoinRoot_eq_top
  · rw [hu]; exact hr0
  · show Module.finrank K.E A = Q.natDegree
    rw [pb.finrank, AdjoinRoot.powerBasis'_dim, hdeg]
  · rw [hu]
    show r * σ0 r = 1
    rw [hσr, hrv]

end GlobalTheory.InvAlgConstr
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvolutiveAlgebraAdjoinRootSelfReciprocalStatement

section

@[expose] public section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

theorem _root_.GlobalTheory.T.exists_involutiveAlgebra_adjoinRoot_selfReciprocal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → ∀ (t : K.O), t ≠ 0 → ∀ Q : (w.adicCompletion E)[X], Q.Monic → IsCsr w Q → ∃ B : GlobalTheory.UnitLemma.InvAlg K, Algebra.adjoin K.E {(1 + algebraMap K.O B.A t * B.g)} = ⊤ ∧ aeval (1 + algebraMap K.O B.A t * B.g) (Q.map e.symm.toRingHom) = 0 ∧ Module.finrank K.E B.A = Q.natDegree ∧ (1 + algebraMap K.O B.A t * B.g) * B.σ (1 + algebraMap K.O B.A t * B.g) = 1 := by
  first | exact @GlobalTheory.InvAlgConstr.exists_invAlg_adjoinRoot | exact GlobalTheory.InvAlgConstr.exists_invAlg_adjoinRoot | (intros; apply GlobalTheory.InvAlgConstr.exists_invAlg_adjoinRoot <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmallConjFixedOfValuation

section

@[expose] public section

open Polynomial

namespace GlobalTheory.UnitLemma

noncomputable def UQ.cInt (K : UQ) : K.O ≃+* K.O :=
  let f := algebraMap K.O K.E
  have hf : Function.Injective f := IsFractionRing.injective K.O K.E
  let d : K.O → K.O := fun x => Classical.choose (K.c_int x)
  have hd : ∀ x, f (d x) = K.c (f x) := fun x => (Classical.choose_spec (K.c_int x)).symm
  have hdd : ∀ x, d (d x) = x := fun x => hf (by rw [hd, hd, K.c_c])
  { toFun := d
    invFun := d
    left_inv := hdd
    right_inv := hdd
    map_mul' := fun a b => hf (by rw [hd, map_mul, map_mul, map_mul, hd, hd])
    map_add' := fun a b => hf (by rw [hd, map_add (f := _), map_add (f := _), map_add (f := _), hd, hd]) }

theorem UQ.cInt_spec (K : UQ) (x : K.O) :
    algebraMap K.O K.E (K.cInt x) = K.c (algebraMap K.O K.E x) :=
  (Classical.choose_spec (K.c_int x)).symm

theorem val_algebraMap_irreducible_pow (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {E : Type} [Field E]
    [Algebra O E] [IsFractionRing O E] {s : O} (hs : Irreducible s) (n : ℕ) :
    val O (algebraMap O E (s ^ n)) = n := by
  have h1 : (IsDiscreteValuationRing.maximalIdeal O).intValuation s = WithZero.exp (-1 : ℤ) :=
    IsDedekindDomain.HeightOneSpectrum.intValuation_singleton _ hs.ne_zero
      ((IsDiscreteValuationRing.irreducible_iff_uniformizer s).mp hs)
  unfold val
  rw [map_pow, map_pow, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, h1]
  simp

theorem exists_small_val (K : UQ) (k : ℕ) (hk : 1 ≤ k) :
    ∃ t : K.O, K.Small t ∧ val K.O (algebraMap K.O K.E t) = k := by
  have hm : ∀ a : K.O, a ∈ IsLocalRing.maximalIdeal K.O ↔ ¬ IsUnit a := fun a =>
    IsLocalRing.mem_maximalIdeal a
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible K.O
  have hcϖ : Irreducible (K.cInt ϖ) := (MulEquiv.irreducible_iff (K.cInt : K.O ≃* K.O)).mpr hϖ
  obtain ⟨ε, hε⟩ := IsDiscreteValuationRing.associated_of_irreducible K.O hϖ hcϖ
  obtain ⟨x, y, hxy, hunit⟩ := K.c_res
  have hcx : K.cInt x = y :=
    IsFractionRing.injective K.O K.E (by rw [K.cInt_spec, hxy])
  have hcc : ∀ a, K.cInt (K.cInt a) = a := fun a => K.cInt.symm_apply_apply a

  obtain ⟨s, hs, hsc⟩ : ∃ s : K.O, Irreducible s ∧ K.cInt s = s := by
    by_cases h1 : IsUnit (1 + (ε : K.O))
    · refine ⟨ϖ + K.cInt ϖ, ?_, ?_⟩
      · have : ϖ + K.cInt ϖ = ϖ * h1.unit := by rw [← hε]; simp [mul_add]
        rw [this]
        exact (associated_mul_unit_right ϖ _ h1.unit.isUnit).irreducible hϖ
      · rw [map_add (f := _), hcc, add_comm]
    · by_cases h2 : IsUnit (x + y * (ε : K.O))
      · refine ⟨x * ϖ + K.cInt (x * ϖ), ?_, ?_⟩
        · have : x * ϖ + K.cInt (x * ϖ) = ϖ * h2.unit := by
            rw [map_mul, hcx, ← hε]; simp; ring
          rw [this]
          exact (associated_mul_unit_right ϖ _ h2.unit.isUnit).irreducible hϖ
        · rw [map_add (f := _), hcc, add_comm]
      · apply absurd _ hunit
        have e : x - y = (x + y * (ε : K.O)) - y * (1 + (ε : K.O)) := by ring
        rw [e]
        exact Ideal.sub_mem _ ((hm _).mpr h2) (Ideal.mul_mem_left _ _ ((hm _).mpr h1))
  refine ⟨s ^ k, ⟨pow_ne_zero _ hs.ne_zero, ?_, ?_⟩, val_algebraMap_irreducible_pow K.O hs k⟩
  · exact Ideal.pow_mem_of_mem _ ((hm s).mpr hs.not_isUnit) k hk
  · rw [← K.cInt_spec, map_pow, hsc]

end GlobalTheory.UnitLemma
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmallConjFixedOfValuationStatement

section

@[expose] public section

open Polynomial

theorem _root_.GlobalTheory.T.exists_small_conjFixed_of_valuation : ∀ (K : GlobalTheory.UnitLemma.UQ) (k : ℕ), 1 ≤ k → ∃ t : K.O, K.Small t ∧ GlobalTheory.UnitLemma.val K.O (algebraMap K.O K.E t) = k := by
  first | exact @GlobalTheory.UnitLemma.exists_small_val | exact GlobalTheory.UnitLemma.exists_small_val | (intros; apply GlobalTheory.UnitLemma.exists_small_val <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableTwistedOrbitalIntegralIntegralNormCongruenStatement

section

@[expose] public section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

theorem _root_.GlobalTheory.T.stableTwistedOrbitalIntegral_integralNormCongruence_product : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (a b k : ℕ) (Q₁ Q₂ : (w.adicCompletion E)[X]) (c : ℂ), Q₁.Monic → Q₂.Monic → Q₁.natDegree = a → Q₂.natDegree = b → (Q₁ * Q₂).Separable → stTw2 a b w Q₁ Q₂ (fun y : GLw a w × GLw b w => c * (if y.1 ∈ GlobalTheory.LFun.KGL w (n := a) ∧ nrmL a w y.1 ∈ {g : GLw a w | g ∈ GlobalTheory.LFun.KGL w (n := a) ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} ∧ y.2 ∈ GlobalTheory.LFun.KGL w (n := b) ∧ nrmL b w y.2 ∈ {g : GLw b w | g ∈ GlobalTheory.LFun.KGL w (n := b) ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin b) (Fin b) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} then 1 else 0)) = c * (stTw a w Q₁ (fun y : GLw a w => if y ∈ GlobalTheory.LFun.KGL w (n := a) ∧ nrmL a w y ∈ {g : GLw a w | g ∈ GlobalTheory.LFun.KGL w (n := a) ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} then 1 else 0) * stTw b w Q₂ (fun y : GLw b w => if y ∈ GlobalTheory.LFun.KGL w (n := b) ∧ nrmL b w y ∈ {g : GLw b w | g ∈ GlobalTheory.LFun.KGL w (n := b) ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin b) (Fin b) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} then 1 else 0)) := by
  first | exact @GlobalTheory.BCT.StTwLevel.stTw2_lev | exact GlobalTheory.BCT.StTwLevel.stTw2_lev | (intros; apply GlobalTheory.BCT.StTwLevel.stTw2_lev <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CongruenceSubgroupIndicatorWeight

section

@[expose] public section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.CongMatch

lemma unit_product_rescale_disjoint_finsets (q : ℕ) (hq : q ≠ 0) (v : ℤ) (N : ℕ) (X : ℚ) :
    ((-((Real.sqrt (((q ^ 2 : ℕ)) : ℝ) : ℝ) : ℂ)) ^ N)⁻¹ * ((((-(q : ℚ)) ^ (-(v - ((N : ℕ) : ℤ))) * X : ℚ)) : ℂ) =
      ((-1 : ℂ) ^ v * ((Real.sqrt ((((q ^ 2 : ℕ)) : ℝ) ^ (-v)) : ℝ) : ℂ)) * (X : ℂ) := by
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have h1 : Real.sqrt (((q ^ 2 : ℕ)) : ℝ) = q := by push_cast; exact Real.sqrt_sq hq0
  have h2 : Real.sqrt ((((q ^ 2 : ℕ)) : ℝ) ^ (-v)) = (q : ℝ) ^ (-v) := by
    push_cast
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul]
    exact Real.sqrt_sq (by positivity)
  rw [h1, h2]
  have hqc : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  have hm : (-(q : ℂ)) ≠ 0 := neg_ne_zero.2 hqc
  push_cast
  have e1 : (-(q : ℂ)) ^ (-(v - (N : ℤ))) = (-(q : ℂ)) ^ (N : ℤ) * (-(q : ℂ)) ^ (-v) := by
    rw [← zpow_add₀ hm]; congr 1; ring
  have e2 : (-(q : ℂ)) ^ (-v) = (-1 : ℂ) ^ v * (q : ℂ) ^ (-v) := by
    rw [neg_eq_neg_one_mul, mul_zpow]
    congr 1
    rw [_root_.zpow_neg, ← _root_.inv_zpow, inv_neg, inv_one]
  rw [e1, e2, zpow_natCast]
  field_simp

theorem match_principal_congruence_inert : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (n a b k : ℕ), a + b = n → 1 ≤ k → Match n a b w 1 ((({γ : UL n w | γ.1 ∈ {g : GLw n w | g ∈ GlobalTheory.LFun.KGL w (n := n) ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))}} : Set (UL n w))).indicator 1) (fun y : GLw a w × GLw b w => ((-((Real.sqrt (qV E w : ℝ) : ℝ) : ℂ)) ^ (k * a * b))⁻¹ * (if y.1 ∈ GlobalTheory.LFun.KGL w (n := a) ∧ nrmL a w y.1 ∈ {g : GLw a w | g ∈ GlobalTheory.LFun.KGL w (n := a) ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} ∧ y.2 ∈ GlobalTheory.LFun.KGL w (n := b) ∧ nrmL b w y.2 ∈ {g : GLw b w | g ∈ GlobalTheory.LFun.KGL w (n := b) ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin b) (Fin b) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} then 1 else 0)) := by
  intro E _ _ _ hU w hw n a b k hab hk
  obtain ⟨K, e, he1, he2, he3, hq⟩ := GlobalTheory.InertUQ.exists_uq E hU w hw
  obtain ⟨t, ht, htv⟩ := GlobalTheory.T.exists_small_conjFixed_of_valuation K k hk
  intro Q₁ Q₂ hm₁ hm₂ hd₁ hd₂ hsep hc₁ hc₂
  obtain ⟨B₁, h11, h12, h13, h14⟩ := GlobalTheory.T.exists_involutiveAlgebra_adjoinRoot_selfReciprocal E w hw K e he1 t ht.1 Q₁ hm₁ hc₁
  obtain ⟨B₂, h21, h22, h23, h24⟩ := GlobalTheory.T.exists_involutiveAlgebra_adjoinRoot_selfReciprocal E w hw K e he1 t ht.1 Q₂ hm₂ hc₂
  obtain ⟨hsB, hres⟩ := GlobalTheory.T.val_resultant_charpoly_shifted_unit_adjoinRoot E w K e he3 k t ht.1 htv a b Q₁ Q₂ B₁ B₂ hm₁ hm₂ hd₁ hd₂ hsep h11 h12 h13 h21 h22 h23
  have hid := GlobalTheory.T.invAlg_identity_of_principal_congruence (GlobalTheory.T.unitLemma_lieAlgebra_unitaryGroup_of_jacquetRallis GlobalTheory.T.jacquetRallisUnitMatch_all_ranks).1 K t ht B₁ B₂ h14 h24 hsB
  rw [GlobalTheory.T.stableTwistedOrbitalIntegral_integralNormCongruence_product E w hw a b k Q₁ Q₂ _ hm₁ hm₂ hd₁ hd₂ hsep,
    GlobalTheory.T.twistedOrbitalIntegral_levelFunction_inert_eq_latticeCount E hU w hw K e he1 he2 he3 hq k t ht htv a Q₁ B₁ hm₁ hd₁ hsep.of_mul_left hc₁ h11 h12 h13 h14,
    GlobalTheory.T.twistedOrbitalIntegral_levelFunction_inert_eq_latticeCount E hU w hw K e he1 he2 he3 hq k t ht htv b Q₂ B₂ hm₂ hd₂ hsep.of_mul_right hc₂ h21 h22 h23 h24,
    GlobalTheory.T.kappaOrbitalIntegral_congruence_inert_latticeCount E hU w hw K e he1 he2 he3 hq k t ht htv n a b Q₁ Q₂ B₁ B₂ hab hm₁ hm₂ hd₁ hd₂ hsep hc₁ hc₂
      h11 h12 h13 h14 h21 h22 h23 h24]
  unfold GlobalTheory.UnitLemma.InvAlg.Identity at hid
  rw [← Rat.cast_mul, ← hid, hres]
  have hq0 : K.q ≠ 0 := by
    intro h0
    have hc := K.card_res
    rw [h0] at hc
    haveI : Nonempty (IsLocalRing.ResidueField K.O) := ⟨0⟩
    have := Nat.card_pos (α := IsLocalRing.ResidueField K.O)
    simp at hc; omega
  unfold delta absHalf
  rw [if_neg hw, hq]
  exact unit_product_rescale_disjoint_finsets K.q hq0 _ (k * a * b) _

end GlobalTheory.CongMatch
end
end
