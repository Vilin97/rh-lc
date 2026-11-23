module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BinaryMonomialDegreeSubstExpansion
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsKummerCharacterAtLevelOfMemKummerModuleStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralConjugateSL2IntLawsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsKummerCharacterAtLevelAddZeroCongrStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsKummerCharacterAtLevelIntegralMatrixConjStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsKummerCharacterAtLevelPadicIntSmulStatement
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
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlTwoPosRatMobiusBasicLawsStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneHolomorphicGermPropertiesStatement
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCharactersEqOnPrincipalCongruenceStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsKummerCharacterAtLevelSuccReduce

section

@[expose] public section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.KZ.H3

theorem exp_pow_reduce (l n v : ℕ) (hl : l ≠ 0) :
    Complex.exp (2 * Real.pi * Complex.I * (v : ℂ) / ((l : ℂ) ^ (n + 1))) ^ l =
      Complex.exp (2 * Real.pi * Complex.I * ((v % l ^ n : ℕ) : ℂ) / ((l : ℂ) ^ n)) := by
  rw [← Complex.exp_nat_mul]
  have hl' : (l : ℂ) ≠ 0 := by exact_mod_cast hl
  have hv : (v : ℂ) = ((v % l ^ n : ℕ) : ℂ) + (l : ℂ) ^ n * ((v / l ^ n : ℕ) : ℂ) := by
    exact_mod_cast (Nat.mod_add_div v (l ^ n)).symm
  have e : (l : ℂ) * (2 * Real.pi * Complex.I * (v : ℂ) / ((l : ℂ) ^ (n + 1))) =
      2 * Real.pi * Complex.I * ((v % l ^ n : ℕ) : ℂ) / ((l : ℂ) ^ n) +
        ((v / l ^ n : ℕ) : ℂ) * (2 * Real.pi * Complex.I) := by
    rw [hv]; field_simp; ring
  rw [e, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

theorem kum_succ_reduce : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime],
    ∀ n : ℕ, ∀ (x : X.Khat l) (χ : SL(2, ℤ) → ZMod (l ^ (n + 1))), Kum X l (n + 1) x χ →
      Kum X l n x (fun δ => ZMod.castHom (pow_dvd_pow l (Nat.le_succ n)) (ZMod (l ^ n)) (χ δ)) := by
  intro Ω _ _ ε X l _ n x χ ⟨f, a, b, M, hM, hx, ⟨ha, hb, hb0, hab⟩, hrel⟩
  have hl0 : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  haveI : NeZero (l ^ (n + 1)) := ⟨pow_ne_zero _ hl0⟩
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ hl0⟩
  refine ⟨f, fun z => a z ^ l, fun z => b z ^ l, M, hM, ?_, ⟨ha.pow l, hb.pow l, ?_, ?_⟩, ?_⟩
  · have h := AdicCompletion.transitionMap_comp_eval_apply (idl l) (X.Kl l) (Nat.le_succ n) x
    change x.val n = _
    rw [← h]
    change AdicCompletion.transitionMap (idl l) (X.Kl l) (Nat.le_succ n) (AdicCompletion.eval (idl l) (X.Kl l) (n + 1) x) = _
    rw [hx]
    rfl
  · intro h
    apply hb0
    rw [← Filter.Germ.coe_zero, Filter.Germ.coe_eq] at h ⊢
    exact h.mono fun z hz => (pow_eq_zero_iff hl0).1 hz
  · have e1 : ((fun z => b z ^ l : ℂ → ℂ) : Mero) = (b : Mero) ^ l := Filter.Germ.coe_pow b l
    have e2 : ((fun z => a z ^ l : ℂ → ℂ) : Mero) = (a : Mero) ^ l := Filter.Germ.coe_pow a l
    rw [e1, e2, ← pow_mul, ← pow_mul, ← pow_succ', hab]
  · intro δ hδ z hz
    have h1 := congrArg (fun t : ℂ => t ^ l) (hrel δ hδ z hz)
    simp only [mul_pow] at h1
    rw [exp_pow_reduce l n _ hl0] at h1
    have hv : (ZMod.castHom (pow_dvd_pow l (Nat.le_succ n)) (ZMod (l ^ n)) (χ δ)).val = (χ δ).val % l ^ n := by
      rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]
    rw [hv]
    simpa only [mul_pow, mul_assoc] using h1

end GlobalTheory.KZ.H3
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsKummerCharacterAtLevelSuccReduceStatement

section

@[expose] public section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

theorem _root_.GlobalTheory.T.isKummerCharacterAtLevel_succ_reduce : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], ∀ n : ℕ, ∀ (x : X.Khat l) (χ : SL(2, ℤ) → ZMod (l ^ (n + 1))), Kum X l (n + 1) x χ → Kum X l n x (fun δ => ZMod.castHom (pow_dvd_pow l (Nat.le_succ n)) (ZMod (l ^ n)) (χ δ)) := by
  first | exact @GlobalTheory.KZ.H3.kum_succ_reduce | exact GlobalTheory.KZ.H3.kum_succ_reduce | (intros; apply GlobalTheory.KZ.H3.kum_succ_reduce <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCharacterAdditiveOnCongruence

section

@[expose] public section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.KZ.H3.KumHom

theorem germ_zero_of_vanish {b : ℂ → ℂ} (hb : DifferentiableOn ℂ b Hs) (h : ∀ z ∈ Hs, b z = 0) :
    (b : Mero) = 0 :=
  (GlobalTheory.T.upperHalfPlane_holomorphic_germ_properties.1 b (fun _ => 0) hb (differentiableOn_const 0)).2 h

theorem vanish_of_comp {b : ℂ → ℂ} (g : GQ) (h : ∀ z ∈ Hs, b (mob g z) = 0) : ∀ z ∈ Hs, b z = 0 := by
  intro w hw
  have h1 := GlobalTheory.T.glTwoPosRatMobius_basic_laws.2.1 g g⁻¹ w hw
  rw [mul_inv_cancel, GlobalTheory.T.glTwoPosRatMobius_basic_laws.2.2.1] at h1
  rw [h1]
  exact h _ (GlobalTheory.T.glTwoPosRatMobius_basic_laws.1 _ w hw)

theorem diff_comp {b : ℂ → ℂ} (hb : DifferentiableOn ℂ b Hs) (g : GQ) :
    DifferentiableOn ℂ (fun z => b (mob g z)) Hs :=
  hb.comp (GlobalTheory.T.glTwoPosRatMobius_basic_laws.2.2.2.1 g) (fun z hz => GlobalTheory.T.glTwoPosRatMobius_basic_laws.1 g z hz)

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem num_not_vanish {X : Tower Ω ε} {m : ℕ} (hm : 0 < m) {f : X.Kˣ} {a b : ℂ → ℂ} (h : IsRoot X m f a b) :
    ¬ ∀ z ∈ Hs, a z = 0 := by
  intro ha
  obtain ⟨hda, hdb, hb0, he⟩ := h
  rw [germ_zero_of_vanish hda ha, zero_pow hm.ne'] at he
  have hbm : (b : Mero) ^ m = 0 := by
    have := congrArg (X.an ((f⁻¹ : X.Kˣ) : X.K) * ·) he
    simp only [mul_zero, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul] at this
    exact this
  have hdbm : DifferentiableOn ℂ (fun z => b z ^ m) Hs := hdb.pow m
  have h0 : ((fun z => b z ^ m : ℂ → ℂ) : Mero) = ((fun _ => 0 : ℂ → ℂ) : Mero) := hbm
  have hz := (GlobalTheory.T.upperHalfPlane_holomorphic_germ_properties.1 _ (fun _ => 0) hdbm (differentiableOn_const 0)).1 h0
  exact hb0 (germ_zero_of_vanish hdb fun z hz' => (pow_eq_zero_iff hm.ne').1 (hz z hz'))

end GlobalTheory.KZ.H3.KumHom

namespace GlobalTheory.KZ.H3.KumHom

theorem zmod_eq_of_exp {m : ℕ} [NeZero m] (u v w : ZMod m)
    (h : Complex.exp (2 * Real.pi * Complex.I * (u.val : ℂ) / (m : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I * (v.val : ℂ) / (m : ℂ)) *
        Complex.exp (2 * Real.pi * Complex.I * (w.val : ℂ) / (m : ℂ))) : u = v + w := by
  rw [← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int] at h
  obtain ⟨k, hk⟩ := h
  have hm : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne m)
  have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hc : ((u.val : ℤ) : ℂ) = ((v.val + w.val + k * m : ℤ) : ℂ) := by
    push_cast
    apply mul_left_cancel₀ h2
    field_simp at hk
    linear_combination (2 * (Real.pi : ℂ) * Complex.I) * hk
  have hi : (u.val : ℤ) = v.val + w.val + k * m := Int.cast_injective hc
  have := congrArg (Int.cast : ℤ → ZMod m) hi
  push_cast at this
  simpa [ZMod.natCast_val, ZMod.cast_id', ZMod.natCast_self] using this

theorem kum_hom : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], ∀ n : ℕ,
    ∀ (x : X.Khat l) (χ : SL(2, ℤ) → ZMod (l ^ n)), Kum X l n x χ → ∃ M : ℕ, 0 < M ∧
      ∀ δ ∈ CongruenceSubgroup.Gamma M, ∀ δ' ∈ CongruenceSubgroup.Gamma M, χ (δ * δ') = χ δ + χ δ' := by
  intro Ω _ _ ε X l _ n x χ hK
  obtain ⟨f, a, b, M, hM, -, hr, hrel⟩ := hK
  refine ⟨M, hM, fun δ hδ δ' hδ' => ?_⟩
  have hpos : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
  haveI : NeZero (l ^ n) := ⟨hpos.ne'⟩
  set E : ZMod (l ^ n) → ℂ := fun v => Complex.exp (2 * Real.pi * Complex.I * (v.val : ℂ) / ((l : ℂ) ^ n)) with hE
  obtain ⟨hda, hdb, hb0, -⟩ := id hr
  set g := ofSL δ
  set g' := ofSL δ'
  have key : ∀ z ∈ Hs, ((E (χ (δ * δ')) - E (χ δ) * E (χ δ')) * a z) * (b (mob g (mob g' z)) * b (mob g' z)) = 0 := by
    intro z hz
    have h1 := hrel (δ * δ') (Subgroup.mul_mem _ hδ hδ') z hz
    rw [map_mul, GlobalTheory.T.glTwoPosRatMobius_basic_laws.2.1 _ _ z hz] at h1
    have h2 := hrel δ hδ (mob g' z) (GlobalTheory.T.glTwoPosRatMobius_basic_laws.1 _ z hz)
    have h3 := hrel δ' hδ' z hz
    simp only [hE]
    linear_combination (-b (mob g' z)) * h1 + b z * h2 +
      Complex.exp (2 * Real.pi * Complex.I * ((χ δ).val : ℂ) / ((l : ℂ) ^ n)) * b (mob g (mob g' z)) * h3
  have hA : DifferentiableOn ℂ (fun z => (E (χ (δ * δ')) - E (χ δ) * E (χ δ')) * a z) Hs :=
    (differentiableOn_const _).mul hda
  have hB : DifferentiableOn ℂ (fun z => b (mob g (mob g' z)) * b (mob g' z)) Hs := by
    refine DifferentiableOn.mul ?_ (diff_comp hdb g')
    have := diff_comp hdb (g * g')
    refine this.congr fun z hz => ?_
    simp only [GlobalTheory.T.glTwoPosRatMobius_basic_laws.2.1 g g' z hz]
  have hc : E (χ (δ * δ')) - E (χ δ) * E (χ δ') = 0 := by
    rcases GlobalTheory.T.upperHalfPlane_holomorphic_germ_properties.2.1 _ _ hA hB key with h | h
    · by_contra hne
      exact num_not_vanish hpos hr fun z hz => (mul_eq_zero.1 (h z hz)).resolve_left hne
    · exfalso
      rcases GlobalTheory.T.upperHalfPlane_holomorphic_germ_properties.2.1 _ _ (diff_comp (diff_comp hdb g) g') (diff_comp hdb g') h with h' | h'
      · exact hb0 (germ_zero_of_vanish hdb (vanish_of_comp g (vanish_of_comp g' h')))
      · exact hb0 (germ_zero_of_vanish hdb (vanish_of_comp g' h'))
  have := sub_eq_zero.1 hc
  simp only [hE] at this
  exact zmod_eq_of_exp _ _ _ (by exact_mod_cast this)

end GlobalTheory.KZ.H3.KumHom
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCharacterAdditiveOnCongruenceStatement

section

@[expose] public section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

theorem _root_.GlobalTheory.T.kummerCharacter_additive_on_congruence : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], ∀ n : ℕ, ∀ (x : X.Khat l) (χ : SL(2, ℤ) → ZMod (l ^ n)), Kum X l n x χ → ∃ M : ℕ, 0 < M ∧ ∀ δ ∈ CongruenceSubgroup.Gamma M, ∀ δ' ∈ CongruenceSubgroup.Gamma M, χ (δ * δ') = χ δ + χ δ' := by
  first | exact @GlobalTheory.KZ.H3.KumHom.kum_hom | exact GlobalTheory.KZ.H3.KumHom.kum_hom | (intros; apply GlobalTheory.KZ.H3.KumHom.kum_hom <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCharactersInvariantCompatibleFamily

section

@[expose] public section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

noncomputable section

namespace GlobalTheory.KZ.H3.KumFam

theorem gamma_dvd {M N : ℕ} (h : M ∣ N) {δ : SL(2, ℤ)} (hδ : δ ∈ CongruenceSubgroup.Gamma N) :
    δ ∈ CongruenceSubgroup.Gamma M := by
  rw [CongruenceSubgroup.Gamma_mem] at hδ ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hδ
  have e : ∀ x : ℤ, ZMod.castHom h (ZMod M) (x : ZMod N) = (x : ZMod M) := fun x => map_intCast _ x
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← e, h1, map_one]
  · rw [← e, h2, map_zero]
  · rw [← e, h3, map_zero]
  · rw [← e, h4, map_one]

theorem common_level {k : ℕ} (Q : Fin k → ℕ → Prop) (hmono : ∀ i M M', M ∣ M' → Q i M → Q i M')
    (h : ∀ i, ∃ M, 0 < M ∧ Q i M) : ∃ M, 0 < M ∧ ∀ i, Q i M := by
  choose M hM hQ using h
  exact ⟨∏ i, M i, Finset.prod_pos fun i _ => hM i,
    fun i => hmono i _ _ (Finset.dvd_prod_of_mem M (Finset.mem_univ i)) (hQ i)⟩

theorem near_fin {V : Type} {k : ℕ} (φ ψ : Fin k → SL(2, ℤ) → V) (h : ∀ i, Near (φ i) (ψ i)) :
    ∃ M, 0 < M ∧ ∀ δ ∈ CongruenceSubgroup.Gamma M, ∀ i, φ i δ = ψ i δ := by
  obtain ⟨M, hM, hQ⟩ := common_level (fun i M => ∀ δ ∈ CongruenceSubgroup.Gamma M, φ i δ = ψ i δ)
    (fun _ _ _ hd hq δ hδ => hq δ (gamma_dvd hd hδ)) h
  exact ⟨M, hM, fun δ hδ i => hQ i δ hδ⟩

theorem kum_sum {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ)
    {ι : Type} [DecidableEq ι] (s : Finset ι) (x : ι → X.Khat l) (χ : ι → SL(2, ℤ) → ZMod (l ^ n))
    (h : ∀ k ∈ s, Kum X l n (x k) (χ k)) : Kum X l n (∑ k ∈ s, x k) (∑ k ∈ s, χ k) := by
  induction s using Finset.induction_on with
  | empty => simpa using (GlobalTheory.T.isKummerCharacterAtLevel_add_zero_congr Ω ε X l n).2.1
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (GlobalTheory.T.isKummerCharacterAtLevel_add_zero_congr Ω ε X l n).1 _ _ _ _ (h a (Finset.mem_insert_self a s))
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

theorem map_mon {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (w : ℕ) (i : Fin (w + 1)) :
    MvPolynomial.map f (mon R w i) = mon S w i := by
  simp [mon]

end GlobalTheory.KZ.H3.KumFam


open GlobalTheory.KZ.H3.KumFam in
theorem GlobalTheory.KZ.H3.kum_family : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], [IsAlgClosed Ω] → JHol X → ∀ (N w : ℕ) (c : Fin (w + 1) → X.Khat l), (∀ i, c i ∈ X.A l) → (∀ γ ∈ Gam N l, ∀ i, c i = ∑ k, (cf w (γ : Matrix (Fin 2) (Fin 2) ℤ) i k : ℤ_[l]) • X.kmap l (X.sl (ofSL γ)).toRingEquiv (c k)) → ∃ Φ, IsFam l w (Gam N l) Φ ∧ ∀ n i, Kum X l n (c i) (fun δ => AddMonoidAlgebra.coeff (Φ n δ) (Finsupp.single 0 (i : ℕ) + Finsupp.single 1 (w - (i : ℕ)))) := by
  intro Ω _ _ ε X l _ _ hj N w c hA hinv
  choose χ hχ using fun n i => GlobalTheory.T.exists_kummerCharacterAtLevel_of_mem_kummerModule Ω ε X l hj n (c i) (hA i)
  refine ⟨fun n δ => ∑ i, MvPolynomial.C (χ n i δ) * mon (ZMod (l ^ n)) w i, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro n δ
    refine MvPolynomial.IsHomogeneous.sum _ _ _ fun i _ => ?_
    have h := (MvPolynomial.isHomogeneous_C (Fin 2) (χ n i δ)).mul ((mon_expand (ZMod (l ^ n)) w).2.2.1 i)
    rwa [zero_add] at h
  · intro n
    obtain ⟨M, hM, hQ⟩ := GlobalTheory.KZ.H3.KumFam.common_level (k := w + 1)
      (fun i M => ∀ δ ∈ CongruenceSubgroup.Gamma M, ∀ δ' ∈ CongruenceSubgroup.Gamma M,
        χ n i (δ * δ') = χ n i δ + χ n i δ')
      (fun _ _ _ hd hq δ hδ δ' hδ' => hq δ (GlobalTheory.KZ.H3.KumFam.gamma_dvd hd hδ) δ' (GlobalTheory.KZ.H3.KumFam.gamma_dvd hd hδ'))
      (fun i => GlobalTheory.T.kummerCharacter_additive_on_congruence Ω ε X l n (c i) (χ n i) (hχ n i))
    refine ⟨M, hM, fun δ hδ δ' hδ' => ?_⟩
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hQ i δ hδ δ' hδ', map_add (f := _), add_mul]
  · intro n γ hγ
    have hdet : (0 : ℤ) < (γ : Matrix (Fin 2) (Fin 2) ℤ).det := by rw [γ.det_coe]; exact one_pos
    have hK : ∀ i, Kum X l n (c i)
        (fun δ => ∑ k, ((cf w (γ : Matrix (Fin 2) (Fin 2) ℤ) i k : ℤ) : ZMod (l ^ n)) * χ n k (γ * δ * γ⁻¹)) := by
      intro i
      have hk : ∀ k, Kum X l n ((cf w (γ : Matrix (Fin 2) (Fin 2) ℤ) i k : ℤ_[l]) •
          X.kmap l (X.sl (ofSL γ)).toRingEquiv (c k))
          (fun δ => PadicInt.toZModPow n (cf w (γ : Matrix (Fin 2) (Fin 2) ℤ) i k : ℤ_[l]) *
            χ n k (cj (γ : Matrix (Fin 2) (Fin 2) ℤ) δ)) := by
        intro k
        have h1 := GlobalTheory.T.isKummerCharacterAtLevel_integral_matrix_conj Ω ε X l n γ (c k) (χ n k) hdet (hχ n k)
        rw [Betti.toGQ_sl] at h1
        exact GlobalTheory.T.isKummerCharacterAtLevel_padicInt_smul Ω ε X l n _ _ _ h1
      have hs := GlobalTheory.KZ.H3.KumFam.kum_sum X l n Finset.univ _ _ (fun k _ => hk k)
      rw [← hinv γ hγ i] at hs
      refine (GlobalTheory.T.isKummerCharacterAtLevel_add_zero_congr Ω ε X l n).2.2 _ _ _ hs ⟨1, one_pos, fun δ _ => ?_⟩
      rw [Finset.sum_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [GlobalTheory.T.integralConjugateSL2Int_laws.2.1, map_intCast]
    obtain ⟨M, hM, hQ⟩ := GlobalTheory.KZ.H3.KumFam.near_fin (k := w + 1) _ _ fun i => GlobalTheory.T.kummerCharacters_eqOn_principalCongruence Ω ε X l n (c i) _ _ (hK i) (hχ n i)
    refine ⟨M, hM, fun δ hδ => ?_⟩

    simp only [map_sum, map_mul, MvPolynomial.algHom_C, (mon_expand (ZMod (l ^ n)) w).1, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_

    rw [← hQ δ hδ i, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, MvPolynomial.algebraMap_eq]; ring
  · intro n
    obtain ⟨M, hM, hQ⟩ := GlobalTheory.KZ.H3.KumFam.near_fin (k := w + 1) _ _ fun i => GlobalTheory.T.kummerCharacters_eqOn_principalCongruence Ω ε X l n (c i) _ _
      (GlobalTheory.T.isKummerCharacterAtLevel_succ_reduce Ω ε X l n (c i) (χ (n + 1) i) (hχ (n + 1) i)) (hχ n i)
    refine ⟨M, hM, fun δ hδ => ?_⟩

    simp only [map_sum, map_mul, MvPolynomial.map_C, GlobalTheory.KZ.H3.KumFam.map_mon]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hQ δ hδ i]
  · intro n i
    convert hχ n i using 1
    funext δ
    exact MonExp.coeff_sum_mon _ w (fun j => χ n j δ) i
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCharactersInvariantCompatibleFamilyStatement

section

@[expose] public section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

theorem _root_.GlobalTheory.T.kummerCharacters_invariant_compatible_family : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], [IsAlgClosed Ω] → JHol X → ∀ (N w : ℕ) (c : Fin (w + 1) → X.Khat l), (∀ i, c i ∈ X.A l) → (∀ γ ∈ Gam N l, ∀ i, c i = ∑ k, (cf w (γ : Matrix (Fin 2) (Fin 2) ℤ) i k : ℤ_[l]) • X.kmap l (X.sl (ofSL γ)).toRingEquiv (c k)) → ∃ Φ, IsFam l w (Gam N l) Φ ∧ ∀ n i, Kum X l n (c i) (fun δ => AddMonoidAlgebra.coeff (Φ n δ) (Finsupp.single 0 (i : ℕ) + Finsupp.single 1 (w - (i : ℕ)))) := by
  first | exact @GlobalTheory.KZ.H3.kum_family | exact GlobalTheory.KZ.H3.kum_family | (intros; apply GlobalTheory.KZ.H3.kum_family <;> assumption)
end
end
