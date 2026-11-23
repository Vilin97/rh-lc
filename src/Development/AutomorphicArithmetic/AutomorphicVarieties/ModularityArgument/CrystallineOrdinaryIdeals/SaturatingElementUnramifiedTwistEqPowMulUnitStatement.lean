module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsInertiaInfiniteCyclotomic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.ChosenFrobeniusIsFrobeniusStatement
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
public import Mathlib.RingTheory.Nilpotent.Exp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsUniqueUnramifiedCocycleFrobeniusValue
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Padics.LocalField
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.UnitaryThreeReflectionRight
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.GaloisSubgroupLBasicPropertiesStatement
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.IsUnitCharacterDiffAtChosenInertiaStatement
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.NilpotentTwistStatement
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.ExpEqOneAddAddSq

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.UnrUnipChar

theorem exp_eq_one_add_add_sq {A : Type} [CommRing A] [Algebra ℚ A] {a : A} (ha : IsNilpotent a) :
    ∃ s, IsNilpotent.exp a = 1 + a + a ^ 2 * s := by
  obtain ⟨k, hk⟩ := ha
  have h2 : a ^ (k + 1 + 1) = 0 := pow_eq_zero_of_le (by omega) hk
  refine ⟨∑ i ∈ Finset.range k, (((i + 1 + 1).factorial : ℚ))⁻¹ • a ^ i, ?_⟩
  rw [IsNilpotent.exp_eq_sum h2, Finset.sum_range_succ', Finset.sum_range_succ', Finset.mul_sum]
  have : ∀ i ∈ Finset.range k, (((i + 1 + 1).factorial : ℚ))⁻¹ • a ^ (i + 1 + 1)
      = a ^ 2 * ((((i + 1 + 1).factorial : ℚ))⁻¹ • a ^ i) := fun i _ => by
    rw [mul_smul_comm]; congr 1; ring
  rw [Finset.sum_congr rfl this]
  simp only [zero_add, Nat.factorial_one, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, pow_one,
    pow_zero]
  ring

end GlobalTheory.UnrUnipChar


open GlobalTheory.UnrUnipChar in
theorem GlobalTheory.unr_unip_char_frob :
    ∀ {l : ℕ} [Fact l.Prime] {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] (t : B),
      IsNilpotent t → ∀ σ : GQ l, UpperTheory.V.Loc.IsFrob σ → ∃ u : GQ l →* Bˣ, QCont l (fun g => (u g : B)) ∧
        (∀ g ∈ Iq l, u g = 1) ∧ (∀ g, IsNilpotent ((u g : B) - 1)) ∧
        ∃ v : Bˣ, ∀ m : ℕ, ∃ b : B, (u (σ ^ m) : B) - 1 = t * ((m : B) * v + t * b) := by
  intro l _ B _ _ _ x hx σ hσ
  letI : Algebra ℚ B := ((algebraMap ℚ_[l] B).comp (algebraMap ℚ ℚ_[l])).toAlgebra
  letI : TopologicalSpace B := moduleTopology ℚ_[l] B
  haveI : IsModuleTopology ℚ_[l] B := ⟨rfl⟩
  haveI : IsTopologicalAddGroup B := IsModuleTopology.topologicalAddGroup ℚ_[l] B
  haveI : ContinuousSMul ℚ_[l] B := IsModuleTopology.toContinuousSMul ℚ_[l] B
  obtain ⟨c, ⟨hc, hcI, hcσ⟩, -⟩ := existsUnique_unramified_cocycle_frobenius_value (v := l) (l := l) (A := ℚ_[l]) (V := ℚ_[l])
    (1 : Representation ℚ_[l] (GQ l) ℚ_[l]) continuous_snd (fun _ _ => rfl) σ hσ 1
  have hadd : ∀ g h, c (g * h) = c g + c h := fun g h => hc.2 g h
  have hcc : Continuous c := hc.1
  have hc1 : c 1 = 0 := hcI 1 (one_mem _)
  have hcpow : ∀ m : ℕ, c (σ ^ m) = m := by
    intro m
    induction m with
    | zero => simp [hc1]
    | succ m ih => rw [pow_succ, hadd, ih, hcσ]; push_cast; ring
  let f : GQ l →* B :=
    { toFun := fun g => IsNilpotent.exp (c g • x)
      map_one' := by rw [hc1, zero_smul, IsNilpotent.exp_zero]
      map_mul' := fun g h => by
        rw [hadd, add_smul, IsNilpotent.exp_add_of_commute (Commute.all _ _) (hx.smul _) (hx.smul _)] }
  have hf : Continuous f := by
    obtain ⟨k, hk⟩ := hx
    have : (f : GQ l → B) = fun g => ∑ i ∈ Finset.range k,
        ((((i.factorial : ℚ)⁻¹ : ℚ) : ℚ_[l]) * c g ^ i) • x ^ i := by
      funext g
      change IsNilpotent.exp (c g • x) = _
      rw [IsNilpotent.exp_eq_sum (k := k) (by rw [_root_.smul_pow, hk, smul_zero])]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_smul, Rat.cast_smul_eq_qsmul, _root_.smul_pow]
    rw [this]
    fun_prop
  have hfI : ∀ g ∈ Iq l, f g = 1 := fun g hg => by
    change IsNilpotent.exp (c g • x) = 1
    rw [hcI g hg, zero_smul, IsNilpotent.exp_zero]
  refine ⟨f.toHomUnits, hf, fun g hg => Units.ext (hfI g hg), fun g => ?_, 1, fun m => ?_⟩
  · change IsNilpotent (IsNilpotent.exp (c g • x) - 1)
    obtain ⟨s, hs⟩ := exp_eq_one_add_add_sq (hx.smul (c g))
    rw [hs, show 1 + c g • x + (c g • x) ^ 2 * s - 1 = (c g • x) * (1 + (c g • x) * s) by ring]
    first
      | exact (Commute.all _ _).isNilpotent_mul_right (hx.smul (c g))
      | exact (Commute.all _ _).isNilpotent_mul_left (hx.smul (c g))
  · change ∃ b, IsNilpotent.exp (c (σ ^ m) • x) - 1 = x * ((m : B) * ((1 : Bˣ) : B) + x * b)
    rw [hcpow m]
    obtain ⟨s, hs⟩ := exp_eq_one_add_add_sq (hx.smul ((m : ℚ_[l])))
    refine ⟨(m : B) ^ 2 * s, ?_⟩
    have e : ((m : ℚ_[l]) • x) = (m : B) * x := by rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
    rw [hs, e, Units.val_one]
    ring
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.SaturatingElementUnramifiedTwistEqPowMulUnit

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.OrdLoc.NilpotentTwist

theorem isUnit_algebraMap_of_ne_zero {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (C : Type) [CommRing C] [Algebra ℚ_[l] C] [Algebra O C]
    [Algebra ℤ_[l] C] [IsScalarTower ℤ_[l] O C] [IsScalarTower ℤ_[l] ℚ_[l] C] {c : O} (hc : c ≠ 0) :
    IsUnit (algebraMap O C c) := by
  have hI : (Ideal.span {c}).comap (algebraMap ℤ_[l] O) ≠ ⊥ :=
    Ideal.comap_ne_bot_of_integral_mem hc (Ideal.mem_span_singleton_self c) (Algebra.IsIntegral.isIntegral c)
  obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  rw [Ideal.mem_comap, Ideal.mem_span_singleton] at hn
  obtain ⟨d, hd⟩ := hn
  have hq : algebraMap ℤ_[l] ℚ_[l] n ≠ 0 := by
    first
      | exact (map_ne_zero_iff _ (IsFractionRing.injective ℤ_[l] ℚ_[l])).mpr hn0
      | exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective ℤ_[l] ℚ_[l])).mpr hn0
  have hu : IsUnit (algebraMap ℤ_[l] C n) := by
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] C]
    exact (isUnit_iff_ne_zero.mpr hq).map (algebraMap ℚ_[l] C)
  rw [IsScalarTower.algebraMap_apply ℤ_[l] O C, hd, map_mul] at hu
  exact isUnit_of_mul_isUnit_left hu

theorem isUnit_add_nil {C : Type} [CommRing C] {a n : C} (ha : IsUnit a) (hn : IsNilpotent n) : IsUnit (a + n) := by
  first
    | exact hn.isUnit_add_left_of_commute ha (Commute.all _ _)
    | exact IsNilpotent.isUnit_add_left_of_commute hn ha (Commute.all _ _)

theorem nil_mul {C : Type} [CommRing C] {t : C} (ht : IsNilpotent t) (z : C) : IsNilpotent (t * z) := by
  first
    | exact (Commute.all _ _).isNilpotent_mul_left ht
    | exact (Commute.all _ _).isNilpotent_mul_right ht
    | exact ht.mul_right (Commute.all _ _)

theorem prod_eq {C : Type} [CommRing C] (L K0 K1 ε t w a : C) (y : Cˣ) (hy : (y : C) = a * (1 + t * w)) :
    L * (K0 * ((y : C) - ε)) * (K1 * (1 - ε * ((y⁻¹ : Cˣ) : C))) =
      (L * K0 * K1 * ((y⁻¹ : Cˣ) : C)) * ((a - ε) + t * (a * w)) ^ 2 := by
  have h := y.mul_inv
  rw [hy] at h ⊢
  linear_combination (-(L * K0 * K1 * (a * (1 + t * w) - ε))) * h

end GlobalTheory.OrdLoc.NilpotentTwist


open GlobalTheory.OrdLoc.NilpotentTwist in
theorem GlobalTheory.OrdLoc.del_unr_twist {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O]
    [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (E : Type) [Field E] [Algebra ℚ_[l] E]
    [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E]
    (C : Type) [CommRing C] [Algebra ℚ_[l] C] [Module.Finite ℚ_[l] C] [Algebra O C] [Algebra ℤ_[l] C]
    [IsScalarTower ℤ_[l] O C] [IsScalarTower ℤ_[l] ℚ_[l] C] [Algebra E C] [IsScalarTower O E C]
    [IsScalarTower ℚ_[l] E C] (t : C) (ht : IsNilpotent t) :
    ∃ u : GQ l →* Cˣ, QCont l (fun g => (u g : C)) ∧ (∀ g ∈ Iq l, u g = 1) ∧ (∀ g, IsNilpotent ((u g : C) - 1)) ∧
      ∃ (j : ℕ) (v : Cˣ), j ≤ 2 ∧
        GlobalTheory.OrdLoc.del D (r0 D.η ((Units.map (algebraMap O C : O →* C)).comp D.Ψ * u)) = t ^ j * v := by
  obtain ⟨-, σ₀, m, hF, hm, hI⟩ := GlobalTheory.T.chosenFrobenius_isFrobenius D
  obtain ⟨-, -, -, -, hs0⟩ := GlobalTheory.T.galoisSubgroupL_basic_properties D
  obtain ⟨u, hcont, huI, hunil, v, hv⟩ := GlobalTheory.unr_unip_char_frob t ht σ₀ hF
  refine ⟨u, hcont, huI, hunil, ?_⟩
  obtain ⟨b, hb⟩ := hv m
  obtain ⟨-, hcc⟩ := GlobalTheory.T.isUnit_characterDiff_at_chosenInertia D C
  have huσ : u (fr D) = u (σ₀ ^ m) := by
    calc u (fr D) = u (σ₀ ^ m * ((σ₀ ^ m)⁻¹ * fr D)) := by rw [mul_inv_cancel_left]
      _ = u (σ₀ ^ m) := by rw [map_mul, huI _ hI, mul_one]
  have hmat : ∀ g, (r0 D.η ((Units.map (algebraMap O C : O →* C)).comp D.Ψ * u) g).mat =
      Matrix.diagonal (fun i => ((((Units.map (algebraMap O C : O →* C)).comp D.Ψ g * u g) ^ wt1 i : Cˣ) : C)) :=
    fun g => rfl
  have hdiag : (r0 D.η ((Units.map (algebraMap O C : O →* C)).comp D.Ψ * u) (s0 D)).mat =
      Matrix.diagonal (fun a => algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a (s0 D))) := by
    rw [hmat, huI _ hs0.2.1, mul_one]
    congr 1
    funext a
    rw [MonoidHom.comp_apply, ← map_zpow, Units.coe_map]
    rfl
  have h0 := GlobalTheory.T.ordinary_derivative_entry_formula D _ hdiag 0
  have h1 := GlobalTheory.T.ordinary_derivative_entry_formula D _ hdiag 1
  rw [hmat, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq] at h0 h1
  have e01 : (0 : Fin 3) + 1 = 1 := rfl
  have e12 : (1 : Fin 3) + 1 = 2 := rfl
  have w0 : wt1 (0 : Fin 3) = 1 := rfl
  have w1 : wt1 (1 : Fin 3) = 0 := rfl
  have w2 : wt1 (2 : Fin 3) = -1 := rfl
  rw [e01, w0, w1, zpow_one, zpow_zero, Units.val_one, mul_one] at h0
  rw [e12, w1, w2, zpow_zero, zpow_neg_one, Units.val_one] at h1
  have hyv : (((Units.map (algebraMap O C : O →* C)).comp D.Ψ (fr D) * u (fr D) : Cˣ) : C) =
      algebraMap O C (D.Ψ (fr D) : O) * (1 + t * ((m : C) * v + t * b)) := by
    rw [Units.val_mul, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, huσ, ← hb]
    ring
  have hl : IsUnit (l : C) := by
    have : IsUnit ((l : ℚ_[l])) := isUnit_iff_ne_zero.mpr (by exact_mod_cast (Fact.out : l.Prime).ne_zero)
    simpa using this.map (algebraMap ℚ_[l] C)
  have hmu : IsUnit (m : C) := by
    have : IsUnit ((m : ℚ_[l])) := isUnit_iff_ne_zero.mpr (by exact_mod_cast (show m ≠ 0 by omega))
    simpa using this.map (algebraMap ℚ_[l] C)
  have hk0 : IsUnit (algebraMap O C (cc D 0 * cc D 1)) := by rw [map_mul]; exact (hcc 0).mul (hcc 1)
  have hk1 : IsUnit (algebraMap O C (cc D 1 * cc D 2)) := by rw [map_mul]; exact (hcc 1).mul (hcc 2)
  have hw : IsUnit ((m : C) * v + t * b) := isUnit_add_nil (hmu.mul (Units.isUnit v)) (nil_mul ht b)
  have ha : IsUnit (algebraMap O C (D.Ψ (fr D) : O)) := (Units.isUnit (D.Ψ (fr D))).map (algebraMap O C)
  unfold GlobalTheory.OrdLoc.del
  rw [h0, h1, prod_eq _ _ _ _ _ _ _ _ hyv, ← map_sub]
  have hQ : IsUnit ((l : C) * algebraMap O C (cc D 0 * cc D 1) * algebraMap O C (cc D 1 * cc D 2) *
      ((((Units.map (algebraMap O C : O →* C)).comp D.Ψ (fr D) * u (fr D))⁻¹ : Cˣ) : C)) :=
    ((hl.mul hk0).mul hk1).mul (Units.isUnit _)
  by_cases hc : (D.Ψ (fr D) : O) - ((cycA l l O (fr D) : Oˣ) : O) = 0
  · rw [hc, map_zero, zero_add]
    refine ⟨2, (hQ.mul ((ha.mul hw).pow 2)).unit, le_rfl, ?_⟩
    rw [IsUnit.unit_spec]
    ring
  · have hn : IsUnit (algebraMap O C ((D.Ψ (fr D) : O) - ((cycA l l O (fr D) : Oˣ) : O)) +
        t * (algebraMap O C (D.Ψ (fr D) : O) * ((m : C) * v + t * b))) :=
      isUnit_add_nil (isUnit_algebraMap_of_ne_zero (l := l) C hc) (nil_mul ht _)
    refine ⟨0, (hQ.mul (hn.pow 2)).unit, by norm_num, ?_⟩
    rw [IsUnit.unit_spec, pow_zero, one_mul]
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.SaturatingElementUnramifiedTwistEqPowMulUnitStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

theorem _root_.GlobalTheory.T.saturatingElement_unramified_twist_eq_pow_mul_unit : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] (C : Type) [CommRing C] [Algebra ℚ_[l] C] [Module.Finite ℚ_[l] C] [Algebra O C] [Algebra ℤ_[l] C] [IsScalarTower ℤ_[l] O C] [IsScalarTower ℤ_[l] ℚ_[l] C] [Algebra E C] [IsScalarTower O E C] [IsScalarTower ℚ_[l] E C] (t : C), IsNilpotent t → ∃ u : GQ l →* Cˣ, QCont l (fun g => (u g : C)) ∧ (∀ g ∈ Iq l, u g = 1) ∧ (∀ g, IsNilpotent ((u g : C) - 1)) ∧ ∃ (j : ℕ) (v : Cˣ), j ≤ 2 ∧ GlobalTheory.OrdLoc.del D (r0 D.η ((Units.map (algebraMap O C : O →* C)).comp D.Ψ * u)) = t ^ j * v := by
  first | exact @GlobalTheory.OrdLoc.del_unr_twist | exact GlobalTheory.OrdLoc.del_unr_twist | (intros; apply GlobalTheory.OrdLoc.del_unr_twist <;> assumption)
end
end
