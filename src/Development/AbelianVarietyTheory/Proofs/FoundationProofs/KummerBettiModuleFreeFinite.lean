module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Letter
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BettiKummerRelationPadicAddStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HsCodiscreteNeBot
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BettiKummerRelationPadicSmul
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqZeroOfBettiKummerRelationPadicZeroStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BinaryFormCoeffOfGamma1CapGamma0InvariantStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BinaryMonomialDegreeSubstExpansion
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPadicCocycleOfCompatiblePolyFamilyStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsKummerCharacterAtLevelAddZeroCongrStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsKummerCharacterAtLevelPadicIntSmulStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCharactersInvariantCompatibleFamilyStatement
public import Mathlib.GroupTheory.Schreier
public import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCompletionNoPrimeTorsionStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.BettiKummerRelationPadicSmulStatement

section

@[expose] public section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.BettiB

theorem _root_.GlobalTheory.T.bettiKummerRelationPadic_smul : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime] (r : ℤ_[l]) (b : X.Fn l) (c : Gam N l → MvPolynomial (Fin 2) ℤ_[l]), BtZ X N l b c → BtZ X N l (r • b) (r • c) := by
  first | exact @GlobalTheory.KZ.BettiB.btZ_smul | exact GlobalTheory.KZ.BettiB.btZ_smul | (intros; apply GlobalTheory.KZ.BettiB.btZ_smul <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBettiCocycleKummerRelation

section

@[expose] public section

noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.BettiB

namespace GlobalTheory.KZ.BettiEx

theorem kum_sum {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ)
    {ι : Type} (s : Finset ι) (r : ι → ℤ_[l]) (x : ι → X.Khat l) (χ : ι → SL(2, ℤ) → ZMod (l ^ n))
    (h : ∀ i, H3.Kum X l n (x i) (χ i)) :
    H3.Kum X l n (∑ i ∈ s, r i • x i) (fun δ => ∑ i ∈ s, PadicInt.toZModPow n (r i) * χ i δ) := by
  classical
  obtain ⟨hadd, hzero, -⟩ := GlobalTheory.T.isKummerCharacterAtLevel_add_zero_congr Ω ε X l n
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact hzero
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact hadd _ _ _ _ (GlobalTheory.T.isKummerCharacterAtLevel_padicInt_smul Ω ε X l n (r a) (x a) (χ a) (h a)) ih

theorem exists_betti_cocycle {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (_hε : Function.Injective ε) (hj : ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero))
    (N l w : ℕ) [Fact l.Prime] (hl : l ≠ 2) (hN : 5 ≤ N) (hc : Nat.Coprime N l) (hw : Odd w) :
    ∀ b ∈ X.BSet N l w, ∃ c ∈ Z1 N l w, BtZ X N l b c := by
  rintro b ⟨⟨c, hcA, hb⟩, hinv⟩
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hJ : H3.JHol X := by
    obtain ⟨φ, h1, h2⟩ := hj
    exact ⟨φ, h2, h1⟩
  have hlN : ¬ l ∣ N := (Nat.Prime.coprime_iff_not_dvd (Fact.out : l.Prime)).1 hc.symm
  obtain ⟨Φ, hΦ, hK⟩ := GlobalTheory.T.kummerCharacters_invariant_compatible_family Ω ε X l hJ N w c hcA
    (fun γ hγ => GlobalTheory.T.binaryForm_coeff_of_gamma1CapGamma0_invariant Ω ε X l N w b c hb γ hγ (hinv γ hγ))
  obtain ⟨z, hz, hnear⟩ := GlobalTheory.T.exists_padic_cocycle_of_compatible_poly_family N l w (by omega) hl hlN hw Φ hΦ
  refine ⟨fun δ => z δ, ⟨fun γ => hz.1 γ γ.2, fun γ δ => hz.2 γ γ.2 δ δ.2⟩, fun n u => ?_⟩
  obtain ⟨M, hM, hMn⟩ := hnear n
  have hk := kum_sum X l n Finset.univ (fun i : Fin (w + 1) => u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) c _ (hK n)
  rw [← hb u] at hk
  refine ⟨_, hk, M, hM, fun δ hδ => ?_⟩
  obtain ⟨-, hexp, -, hev, -⟩ := GlobalTheory.KZ.H3.mon_expand (ZMod (l ^ n)) w
  have e := hMn δ hδ
  simp only at e ⊢
  rw [e]
  conv_lhs => rw [hexp (Φ n δ) (hΦ.1 n δ)]

  simp only [map_sum, map_mul, map_pow, MvPolynomial.eval_C, hev]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

end GlobalTheory.KZ.BettiEx
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBettiCocycleKummerRelationStatement

section

@[expose] public section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.BettiB

theorem _root_.GlobalTheory.T.exists_betti_cocycle_kummer_relation : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ b ∈ X.BSet N l w, ∃ c ∈ Z1 N l w, BtZ X N l b c := by
  first | exact @GlobalTheory.KZ.BettiEx.exists_betti_cocycle | exact GlobalTheory.KZ.BettiEx.exists_betti_cocycle | (intros; apply GlobalTheory.KZ.BettiEx.exists_betti_cocycle <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.GammaOneGammaZeroHomogeneousCocyclesFinite

section

@[expose] public section

open scoped MatrixGroups TensorProduct Pointwise
open Matrix GlobalTheory.KZ GlobalTheory.KZ.BettiB

namespace GlobalTheory.KZ.BettiB

theorem gam_fg (N l : ℕ) [Fact l.Prime] (hN : 0 < N) : Group.FG (Gam N l) := by
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  haveI : Group.FG SL(2, ℤ) := by
    rw [Group.fg_iff]
    exact ⟨{ModularGroup.S, ModularGroup.T}, SpecialLinearGroup.SL2Z_generators, Set.toFinite _⟩
  haveI : (Gam N l).FiniteIndex := by unfold Gam; infer_instance
  exact Subgroup.fg_of_index_ne_zero _

theorem module_finite_z1_padicInt : ∀ (N l w : ℕ) [Fact l.Prime], 0 < N → Module.Finite ℤ_[l] (Z1 N l w) := by
  intro N l w _ hN
  obtain ⟨s, hs, hfin⟩ := Group.fg_iff.1 (gam_fg N l hN)
  let t : Set (Gam N l) := insert 1 (s ∪ s⁻¹)
  have ht : t.Finite := (hfin.union hfin.inv).insert 1
  haveI : Finite t := ht.to_subtype
  haveI : Module.Finite ℤ_[l] (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ_[l] w) :=
    Module.Finite.iff_fg.2 (MvPolynomial.homogeneousSubmodule_fg _ _ _)
  let L : Z1 N l w →ₗ[ℤ_[l]] (t → MvPolynomial.homogeneousSubmodule (Fin 2) ℤ_[l] w) :=
    { toFun := fun c i => ⟨c.1 i.1, c.2.1 i.1⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine Module.Finite.of_injective L ((injective_iff_map_eq_zero L).2 fun c hc => ?_)
  have h0 : ∀ γ ∈ t, c.1 γ = 0 := fun γ hγ => congrArg Subtype.val (congrFun hc ⟨γ, hγ⟩)
  apply Subtype.ext
  funext γ
  have hγ : γ ∈ Submonoid.closure (s ∪ s⁻¹) := by
    rw [← Subgroup.closure_toSubmonoid, hs]; trivial
  show c.1 γ = 0
  induction hγ using Submonoid.closure_induction with
  | mem x hx => exact h0 x (Set.mem_insert_of_mem _ hx)
  | one => exact h0 1 (Set.mem_insert _ _)
  | mul x y _ _ hx hy => rw [c.2.2 x y, hx, hy, map_zero, add_zero]

end GlobalTheory.KZ.BettiB
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.GammaOneGammaZeroHomogeneousCocyclesFiniteStatement

section

@[expose] public section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.BettiB

theorem _root_.GlobalTheory.T.gammaOneGammaZeroHomogeneousCocycles_finite : ∀ (N l w : ℕ) [Fact l.Prime], 0 < N → Module.Finite ℤ_[l] (Z1 N l w) := by
  first | exact @GlobalTheory.KZ.BettiB.module_finite_z1_padicInt | exact GlobalTheory.KZ.BettiB.module_finite_z1_padicInt | (intros; apply GlobalTheory.KZ.BettiB.module_finite_z1_padicInt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerBettiModuleFreeFinite

section

@[expose] public section

noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.BettiB

namespace GlobalTheory.KZ

theorem B_free_finite : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → Module.Free ℤ_[l] (X.B N l w) ∧ Module.Finite ℤ_[l] (X.B N l w) := by
  intro Ω _ _ _ ε X hε hj N l w _ hl2 hN hcop hw
  have L1 : ∀ x : X.Khat l, (l : ℤ_[l]) • x = 0 → x = 0 := fun x hx => GlobalTheory.T.kummerCompletion_no_prime_torsion X l x hx
  have Ladd : ∀ b b' c c', BtZ X N l b c → BtZ X N l b' c' → BtZ X N l (b + b') (c + c') := fun b b' c c' h h' => GlobalTheory.T.bettiKummerRelationPadic_add X N l b b' c c' h h'
  have Lsmul : ∀ (r : ℤ_[l]) b c, BtZ X N l b c → BtZ X N l (r • b) (r • c) := fun r b c h => GlobalTheory.T.bettiKummerRelationPadic_smul X N l r b c h
  have Lzero : BtZ X N l 0 0 := btZ_zero X N l
  have L3 : ∀ b, BtZ X N l b 0 → b = 0 := fun b h => GlobalTheory.T.eq_zero_of_bettiKummerRelationPadic_zero ε X hε hj N l (by omega) b h
  have L4 : Module.Finite ℤ_[l] (Z1 N l w) := GlobalTheory.T.gammaOneGammaZeroHomogeneousCocycles_finite N l w (by omega)
  have L5 : ∀ b ∈ X.BSet N l w, ∃ c ∈ Z1 N l w, BtZ X N l b c := GlobalTheory.T.exists_betti_cocycle_kummer_relation ε X hε hj N l w hl2 hN hcop hw

  let S : Submodule ℤ_[l] (X.Fn l × Z1 N l w) :=
    { carrier := {p | BtZ X N l p.1 (p.2 : Gam N l → MvPolynomial (Fin 2) ℤ_[l])}
      add_mem' := fun {p q} hp hq => by simpa using Ladd _ _ _ _ hp hq
      zero_mem' := by simpa using Lzero
      smul_mem' := fun r p hp => by simpa using Lsmul r _ _ hp }
  have hinj : Function.Injective ((LinearMap.snd ℤ_[l] (X.Fn l) (Z1 N l w)).comp S.subtype) := by
    intro p q hpq
    have hd : (p : X.Fn l × Z1 N l w) - q ∈ S := S.sub_mem p.2 q.2
    have h2 : ((p : X.Fn l × Z1 N l w) - q).2 = 0 := by simpa [sub_eq_zero] using hpq
    have h1 : ((p : X.Fn l × Z1 N l w) - q).1 = 0 := by
      apply L3
      have := hd
      simp only [S, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq] at this
      rwa [h2] at this
    apply Subtype.ext
    exact sub_eq_zero.mp (Prod.ext h1 h2)
  haveI : IsNoetherian ℤ_[l] (Z1 N l w) := inferInstance
  haveI hSf : Module.Finite ℤ_[l] S := Module.Finite.of_injective _ hinj
  have hle : X.B N l w ≤ S.map (LinearMap.fst ℤ_[l] (X.Fn l) (Z1 N l w)) := by
    refine Submodule.span_le.mpr ?_
    intro b hb
    obtain ⟨c, hc, hbc⟩ := L5 b hb
    exact ⟨(b, ⟨c, hc⟩), hbc, rfl⟩
  have hfg : (S.map (LinearMap.fst ℤ_[l] (X.Fn l) (Z1 N l w))).FG := by
    have e : S.map (LinearMap.fst ℤ_[l] (X.Fn l) (Z1 N l w)) =
        LinearMap.range ((LinearMap.fst ℤ_[l] (X.Fn l) (Z1 N l w)).comp S.subtype) := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
    rw [e]
    exact Module.Finite.iff_fg.mp inferInstance
  have hB : (X.B N l w).FG := by
    haveI : IsNoetherian ℤ_[l] (S.map (LinearMap.fst ℤ_[l] (X.Fn l) (Z1 N l w))) := isNoetherian_of_fg_of_noetherian _ hfg
    have := (isNoetherian_submodule.mp this) (X.B N l w) ?_
    · exact this
    · exact hle
  haveI hBf : Module.Finite ℤ_[l] (X.B N l w) := Module.Finite.iff_fg.mpr hB

  have Lpow : ∀ (k : ℕ) (x : X.Khat l), ((l : ℤ_[l]) ^ k) • x = 0 → x = 0 := by
    intro k
    induction k with
    | zero => intro x hx; simpa using hx
    | succ k ih =>
      intro x hx
      apply ih
      apply L1
      rw [← mul_smul, ← pow_succ']; exact hx
  haveI : NoZeroSMulDivisors ℤ_[l] (X.B N l w) := by
    refine ⟨fun {r b} h => ?_⟩
    by_cases hr : r = 0
    · exact Or.inl hr
    right
    have hrw := PadicInt.unitCoeff_spec hr
    apply Subtype.ext
    funext u
    have h' : (r • (b : X.Fn l)) u = 0 := by
      have := congrArg (fun y : X.B N l w => (y : X.Fn l) u) h
      simpa using this
    have h'' : ((l : ℤ_[l]) ^ r.valuation) • (((PadicInt.unitCoeff hr : ℤ_[l]ˣ) : ℤ_[l]) • (b : X.Fn l) u) = 0 := by
      rw [smul_smul, mul_comm, ← hrw]; simpa using h'
    have := Lpow _ _ h''
    simpa using this
  exact ⟨Module.free_of_finite_type_torsion_free', hBf⟩

end GlobalTheory.KZ
end
end
end
