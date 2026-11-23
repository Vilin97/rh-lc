module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.CycRepApply
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.TwSingle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.AmbHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.CardTors
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.IneCyc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PullEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PullMem
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.GamGen
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.RelCyc
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.AmbIndex

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

theorem UpperTheory.V.FW.amb :
    ∀ (F : Type) [Field F] [NumberField F] (l : ℕ) [Fact l.Prime] (ζ : F), IsPrimitiveRoot ζ l → ∃ B : ℕ, ∀ (n : ℕ) (K : Type) [Field K] [NumberField K] [Algebra F K] [IsCyclotomicExtension {l ^ n} F K] (τ : Gal(K/F)), IsTotallyComplex K → (∀ σ : Gal(K/F), σ ∈ Subgroup.zpowers τ) → (powR (Cl K) l ⊔ difR (clMap τ.toRingEquiv)).index ≤ B := by
  intro F _ _ l _ ζ hζ
  obtain ⟨Ω, _, _, hΩ⟩ : ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra F Ω), IsAlgClosure F Ω :=
    ⟨AlgebraicClosure F, inferInstance, inferInstance, inferInstance⟩
  haveI : IsAlgClosed Ω := hΩ.isAlgClosed
  haveI : Algebra.IsAlgebraic F Ω := hΩ.isAlgebraic
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  refine ⟨{φ : G F Ω → ZMod l | IsLocallyConstant φ ∧ (∀ a b : G F Ω, φ (a * b) = φ a + φ b) ∧
      ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ g ∈ Ine A, φ g = 0}.ncard,
    fun n K _ _ _ _ τ hK hτ => ?_⟩
  haveI hgal : IsGalois F K := IsCyclotomicExtension.isGalois (S := {l ^ n}) (K := F) (L := K)
  let e : K →ₐ[F] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  letI : Algebra K Ω := e.toRingHom.toAlgebra
  haveI : IsScalarTower F K Ω := IsScalarTower.of_algebraMap_eq (fun x => (e.commutes x).symm)
  haveI : Algebra.IsAlgebraic K Ω := Algebra.IsAlgebraic.tower_top (K := F) K
  haveI : IsAlgClosure K Ω := ⟨inferInstance, inferInstance⟩
  let ρ : Representation (ZMod l) (G F Ω) (ZMod l) := scalRep (ZMod l) 1
  have hcyc : IsCyclic Gal(K/F) := ⟨⟨τ, hτ⟩⟩
  have hpe := (pullEq F Ω K (galOf F K Ω) le_rfl 1 (ZMod l) (ZMod l) ρ one_ne_zero le_rfl (Or.inl hK)).1
  have hinj := (pullMem F Ω K (galOf F K Ω) le_rfl 1 (ZMod l) (ZMod l) one_ne_zero).2 le_rfl
  haveI hCfin : Finite (ClEq K 1 ρ) := Subtype.finite
  have hcardEq : Nat.card (EqHom 1 (galOf F K Ω) ρ) = Nat.card (ClEq K 1 ρ) := by
    rw [← hpe]
    exact Nat.card_congr (Submodule.equivMapOfInjective _ hinj _).toEquiv.symm
  have hEfin : Finite (EqHom 1 (galOf F K Ω) ρ) := by
    rw [← hpe]
    exact Finite.of_equiv _ (Submodule.equivMapOfInjective _ hinj _).toEquiv
  have hamb := ambHom F Ω K l ζ hζ hcyc (ineCyc F Ω K l n) hEfin
  set H := powR (Cl K) l ⊔ difR (clMap τ.toRingEquiv) with hH
  have hfix : ∀ c : Cl K, (QuotientGroup.mk (clMap τ.toRingEquiv c) : Cl K ⧸ H) = QuotientGroup.mk c := by
    intro c
    rw [QuotientGroup.eq]
    have h1 : c / clMap τ.toRingEquiv c ∈ H := le_sup_right (a := powR (Cl K) l) ⟨c, rfl⟩
    have h2 : (clMap τ.toRingEquiv c)⁻¹ * c = c / clMap τ.toRingEquiv c := by
      rw [div_eq_mul_inv, mul_comm]
    rw [h2]
    exact h1
  have hmulc : ∀ (a b : Gal(K/F)) (c : Cl K),
      clMap (a * b).toRingEquiv c = clMap a.toRingEquiv (clMap b.toRingEquiv c) :=
    fun a b c => clMap_trans b.toRingEquiv a.toRingEquiv c
  have hone1 : ∀ c : Cl K, clMap (1 : Gal(K/F)).toRingEquiv c = c := fun c => clMap_refl K c
  have hinv : ∀ d : Cl K, (QuotientGroup.mk (clMap τ⁻¹.toRingEquiv d) : Cl K ⧸ H) = QuotientGroup.mk d := by
    intro d
    have h3 : clMap τ.toRingEquiv (clMap τ⁻¹.toRingEquiv d) = d := by
      rw [← hmulc, mul_inv_cancel, hone1]
    conv_rhs => rw [← h3]
    rw [hfix]
  have hall : ∀ α : Gal(K/F), ∀ c : Cl K,
      (QuotientGroup.mk (clMap α.toRingEquiv c) : Cl K ⧸ H) = QuotientGroup.mk c := by
    intro α
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hτ α)
    induction k using Int.induction_on with
    | zero =>
      intro c
      rw [zpow_zero, hone1]
    | succ k ih =>
      intro c
      rw [zpow_add_one, hmulc, ih, hfix]
    | pred k ih =>
      intro c
      rw [zpow_sub_one, hmulc, ih, hinv]
  have hlift : ∀ (g : G F Ω) (τ' : K ≃+* K), IsLift τ' g.toRingEquiv → ∀ c : Cl K,
      (QuotientGroup.mk (clMap τ' c) : Cl K ⧸ H) = QuotientGroup.mk c := by
    intro g τ' hl c
    unfold IsLift at hl
    have hF : ∀ x : F, τ' (algebraMap F K x) = algebraMap F K x := by
      intro x
      apply (algebraMap K Ω).injective
      rw [← hl]
      show g (algebraMap K Ω (algebraMap F K x)) = algebraMap K Ω (algebraMap F K x)
      rw [← IsScalarTower.algebraMap_apply, AlgEquiv.commutes]
    let α : Gal(K/F) := AlgEquiv.ofRingEquiv (f := τ') hF
    have hα : α.toRingEquiv = τ' := RingEquiv.ext fun x => rfl
    rw [← hα]
    exact hall α c
  have hpowQ : powR (Cl K ⧸ H) l = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    unfold powR at hy
    obtain ⟨x, rfl⟩ := hy
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective x
    rw [Subgroup.mem_bot]
    show (QuotientGroup.mk c : Cl K ⧸ H) ^ l = 1
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact le_sup_left (b := difR (clMap τ.toRingEquiv)) ⟨c, rfl⟩
  have hcardQ : H.index = Nat.card (Cl K ⧸ H →* Multiplicative (ZMod l)) := by
    rw [(cardTors (Cl K ⧸ H)).2 l, hpowQ, Subgroup.index_bot]
    rfl
  let Φ : (Cl K ⧸ H →* Multiplicative (ZMod l)) → ClEq K 1 ρ := fun ψ =>
    ⟨fun c => Multiplicative.toAdd (ψ (QuotientGroup.mk c)), by
      unfold ClEq
      rw [Submodule.mem_inf, Submodule.mem_iInf]
      refine ⟨?_, fun g => ?_⟩
      · unfold ClDual
        refine ⟨fun a b => ?_, fun v hv => ?_⟩
        · beta_reduce
          rw [QuotientGroup.mk_mul, map_mul, toAdd_mul]
        · exfalso
          unfold Above at hv
          exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr (by simpa using hv))
      · unfold clCond
        intro τ' hl c
        beta_reduce
        rw [hlift g τ' hl c]
        simp [ρ, scalRep]⟩
  have hΦ : Function.Injective Φ := by
    intro ψ1 ψ2 h
    apply MonoidHom.ext
    intro x
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective x
    have h4 := congrFun (congrArg Subtype.val h) c
    exact Multiplicative.toAdd.injective h4
  calc H.index = Nat.card (Cl K ⧸ H →* Multiplicative (ZMod l)) := hcardQ
    _ ≤ Nat.card (ClEq K 1 ρ) := Nat.card_le_card_of_injective Φ hΦ
    _ = Nat.card (EqHom 1 (galOf F K Ω) ρ) := hcardEq.symm
    _ ≤ _ := hamb
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.AmbCyc

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

theorem UpperTheory.V.FW.ambCyc :
    ∀ (l : ℕ) [Fact l.Prime] (f : ℕ), f.Coprime l → ∃ B : ℕ, ∀ (n : ℕ) [NeZero (f * l ^ n)] (L : Type) [Field L] [NumberField L] [IsCyclotomicExtension {f * l ^ n} ℚ L] (γ : (ZMod (f * l ^ n))ˣ), 2 ≤ n → (γ : ZMod (f * l ^ n)) = 1 + f * l ^ ee l → (powR (Cl L) l ⊔ difR (clA (f * l ^ n) L γ)).index ≤ B := by
  intro l hl f hf
  have hl1 : 1 < l := hl.out.one_lt
  have hlpos : 0 < l := hl.out.pos
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [Nat.coprime_zero_left] at hf
    omega
  have hfpos : 0 < f := Nat.pos_of_ne_zero hf0
  have he1 : 1 ≤ ee l := by unfold ee; split_ifs <;> omega
  have he2 : ee l ≤ 2 := by unfold ee; split_ifs <;> omega
  haveI : NeZero (f * l ^ ee l) := ⟨by positivity⟩
  haveI : NeZero ((f * l ^ ee l : ℕ) : ℚ) := ⟨by exact_mod_cast (show f * l ^ ee l ≠ 0 by positivity)⟩
  haveI : IsCyclotomicExtension {f * l ^ ee l} ℚ (CyclotomicField (f * l ^ ee l) ℚ) := by
    convert CyclotomicField.isCyclotomicExtension (f * l ^ ee l) ℚ
    · rfl
  haveI : NumberField (CyclotomicField (f * l ^ ee l) ℚ) :=
    IsCyclotomicExtension.numberField {f * l ^ ee l} ℚ _
  obtain ⟨z, hz⟩ : ∃ z : CyclotomicField (f * l ^ ee l) ℚ, IsPrimitiveRoot z (f * l ^ ee l) :=
    ⟨_, IsCyclotomicExtension.zeta_spec _ ℚ _⟩
  have hsplit : f * l ^ ee l = l * (f * l ^ (ee l - 1)) := by
    rw [mul_comm l, mul_assoc, ← pow_succ, Nat.sub_add_cancel he1]
  have hzl : IsPrimitiveRoot (z ^ (f * l ^ (ee l - 1))) l := by
    have h := hz.pow_of_dvd (by positivity) (Dvd.intro_left l hsplit.symm)
    rwa [Nat.div_eq_of_eq_mul_left (by positivity) hsplit] at h
  obtain ⟨B, hB⟩ := amb (CyclotomicField (f * l ^ ee l) ℚ) l _ hzl
  refine ⟨B, ?_⟩
  intro n _ L _ _ _ γ hn hγ
  have hen : ee l ≤ n := le_trans he2 hn
  have h : f * l ^ ee l ∣ f * l ^ n := mul_dvd_mul_left f (pow_dvd_pow l hen)
  obtain ⟨alg, hcycL, hall, hex⟩ := relCyc l f (ee l) n h (CyclotomicField (f * l ^ ee l) ℚ) L hf
  obtain ⟨hker, -⟩ := gamGen l f n h γ hf hen hγ
  letI := alg
  haveI := hcycL
  have hγinv : γ⁻¹ ∈ (ZMod.unitsMap h).ker := by
    rw [hker]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers γ)
  obtain ⟨τ, hτ⟩ := hex γ⁻¹ hγinv
  have hbig : 2 < f * l ^ n := by
    have h4 : 4 ≤ l ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ l ^ 2 := Nat.pow_le_pow_left hl.out.two_le 2
        _ ≤ l ^ n := Nat.pow_le_pow_right hlpos hn
    nlinarith
  have htc : IsTotallyComplex L := IsCyclotomicExtension.Rat.isTotallyComplex (n := f * l ^ n) L hbig
  let ρF : Gal(L/CyclotomicField (f * l ^ ee l) ℚ) →* (L ≃+* L) :=
    { toFun := fun σ => σ.toRingEquiv, map_one' := rfl, map_mul' := fun _ _ => rfl }
  let ρQ : Gal(L/ℚ) →* (L ≃+* L) :=
    { toFun := fun σ => σ.toRingEquiv, map_one' := rfl, map_mul' := fun _ _ => rfl }
  have hgen : ∀ σ : Gal(L/CyclotomicField (f * l ^ ee l) ℚ), σ ∈ Subgroup.zpowers τ := by
    intro σ
    obtain ⟨t, ht, hσ⟩ := hall σ
    rw [hker] at ht
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
    refine Subgroup.mem_zpowers_iff.mpr ⟨-k, ?_⟩
    have e1 : ρF σ = ρQ (sg (f * l ^ n) L (γ ^ k)) := hσ
    have e2 : ρF τ = ρQ (sg (f * l ^ n) L γ⁻¹) := hτ
    have e3 : ρF σ = ρF (τ ^ (-k)) := by
      rw [e1, map_zpow ρF, e2, ← map_zpow, ← map_zpow, inv_zpow', neg_neg]
    exact AlgEquiv.ext fun x => (congrArg (fun r : L ≃+* L => r x) e3).symm
  have hcl : clA (f * l ^ n) L γ = clMap τ.toRingEquiv := by
    rw [hτ, map_inv]
    rfl
  rw [hcl]
  exact hB n L τ htc hgen
end
end
