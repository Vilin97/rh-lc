module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.EsStmt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerShimuraKummerFunctionUniformExceptionalPrStatement
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpecialLinearGroupIntMapZmodSurjective
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
import Development.AbelianVarietyTheory.Definitions.Foundations.ExpUpper
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.CoeffSlD
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.FrobeniusConjugateInertia.FrobConjIne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.OfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SCls
public import Development.AbelianVarietyTheory.Definitions.Foundations.OpLDOneSubMemTriv
public import Development.AbelianVarietyTheory.Definitions.Foundations.Letter
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisCommutesHeckeAction
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagMod
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlMulToRingEquiv
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KatoTwistedClassNormCompatibleCyclotomic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpecialLinearGroupIntMapZmodSurjectiveStatement

section

@[expose] public section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.specialLinearGroup_int_map_zmod_surjective : ∀ (M : ℕ), Function.Surjective (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) : SL(2, ℤ) →* Matrix.SpecialLinearGroup (Fin 2) (ZMod M)) := by
  first | exact @GlobalTheory.specialLinearGroup_map_intCast_zmod_surjective | exact GlobalTheory.specialLinearGroup_map_intCast_zmod_surjective | (intros; apply GlobalTheory.specialLinearGroup_map_intCast_zmod_surjective <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.EsFrob

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KZ.ES
open scoped Matrix MatrixGroups Pointwise

theorem UpperTheory.V.Z.Kato.Nb.sEsFrob : UpperTheory.V.Z.Kato.Nb.SEsFrob := by
  intro Ω _ _ _ l _ v B σ hq hql hB hF
  obtain ⟨hσ, hfr⟩ := hF
  have hmem : ∀ g : Gal(Ω/ℚ), g ∈ ValuationSubring.decompositionSubgroup ℚ B → ∀ y ∈ B, g y ∈ B :=
    fun g hg y hy => (B.subMulAction ℚ).smul_mem' ⟨g, hg⟩ hy
  refine ⟨⟨?_, fun y hy => ⟨hmem σ hσ y hy, hmem σ⁻¹ (inv_mem hσ) y hy,
    hfr y ((B.valuation_le_one_iff y).mpr hy)⟩⟩, ?_⟩
  · rw [ValuationSubring.mem_nonunits_iff]
    have h := (hB ((normV v : ℕ) : 𝓞 ℚ)).mpr ((UpperTheory.V.Z.Kato.Nb.mem_place_iff v _).mpr dvd_rfl)
    simpa using h
  · have hl : ((l : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := by
      rw [UpperTheory.V.Z.Kato.Nb.mem_place_iff]
      intro hd
      exact hql ((Nat.prime_dvd_prime_iff_eq hq Fact.out).mp hd)
    exact cycZ_of_isFrob hl hB ⟨hσ, hfr⟩
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisCommutesHeckeActionStatement

section

@[expose] public section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

theorem _root_.GlobalTheory.T.galois_commutes_hecke_action : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), ∀ (N l w : ℕ) [Fact l.Prime], 1 ≤ N → ∀ b ∈ X.BSet N l w, ∀ δ ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l, ∀ s : Ω ≃ₐ[ℚ] Ω, X.act l (δ : Matrix (Fin 2) (Fin 2) ℤ) (X.galB l s b) = X.galB l s (X.act l (δ : Matrix (Fin 2) (Fin 2) ℤ) b) := by
  first | exact @GlobalTheory.KZ.GamComm.act_galB_comm | exact GlobalTheory.KZ.GamComm.act_galB_comm | (intros; apply GlobalTheory.KZ.GamComm.act_galB_comm <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SEsT

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KZ.ES
open scoped Matrix MatrixGroups Pointwise

theorem UpperTheory.V.Z.Kato.Nb.sEsT : UpperTheory.V.Z.Kato.Nb.SEsT := by
  intro Ω _ _ _ ε X l _ N w q M hN hq hqlN hqM hM γ hγ b hb
  have hb' : ∀ g ∈ Gam N l, X.act l ↑g b = b := by
    unfold Tower.BSet at hb
    exact hb.2
  have hN0 : N ≠ 0 := by omega
  have hl0 : l ≠ 0 := (Fact.out : Nat.Prime l).ne_zero
  have hqN : q.Coprime N := (Nat.coprime_mul_iff_right.mp hqlN).2
  have hSD := Betti.isDiam_sgD (l := l) hN0 hl0 hqN
  unfold IsDiam at hSD
  obtain ⟨hSmem, hSq⟩ := hSD
  obtain ⟨hS0N, hS0l⟩ := Subgroup.mem_inf.mp hSmem
  rw [CongruenceSubgroup.Gamma0_mem] at hS0N hS0l
  unfold en at hSq
  unfold DiagMod at hγ
  obtain ⟨-, hγc, hγd⟩ := hγ
  unfold en at hγc hγd
  have hNM : N ∣ M := (dvd_mul_left N l).trans hM
  have hlM : l ∣ M := (dvd_mul_right l N).trans hM
  have hcN : (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod N) = 0 := by
    simpa using congrArg (ZMod.castHom hNM (ZMod N)) hγc
  have hcl : (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod l) = 0 := by
    simpa using congrArg (ZMod.castHom hlM (ZMod l)) hγc
  have hdN : (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod N) = q := by
    simpa using congrArg (ZMod.castHom hNM (ZMod N)) hγd
  have hδ : sgD N l q * γ⁻¹ ∈ Gam N l := by
    have hS := congrArg (Int.cast : ℤ → ZMod N) (Matrix.SpecialLinearGroup.det_coe (sgD N l q))
    have hG := congrArg (Int.cast : ℤ → ZMod N) (Matrix.SpecialLinearGroup.det_coe γ)
    rw [Matrix.det_fin_two] at hS hG
    push_cast at hS hG
    unfold Gam
    rw [Subgroup.mem_inf, CongruenceSubgroup.Gamma1_mem, CongruenceSubgroup.Gamma0_mem,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    simp
    push_cast
    generalize (sgD N l q : Matrix (Fin 2) (Fin 2) ℤ) = S at *
    generalize (γ : Matrix (Fin 2) (Fin 2) ℤ) = G at *
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · linear_combination (↑(S 0 0) : ZMod N) * hdN - (↑(S 0 0) : ZMod N) * hSq + hS
        + (↑(S 0 1) : ZMod N) * hS0N - (↑(S 0 1) : ZMod N) * hcN
    · linear_combination (↑(G 0 0) : ZMod N) * hSq - (↑(G 0 0) : ZMod N) * hdN + hG
        + (↑(G 0 1) : ZMod N) * hcN - (↑(G 0 1) : ZMod N) * hS0N
    · linear_combination (↑(G 1 1) : ZMod N) * hS0N - (↑(S 1 1) : ZMod N) * hcN
    · linear_combination (↑(G 1 1) : ZMod l) * hS0l - (↑(S 1 1) : ZMod l) * hcl
  have hAct : X.act l ↑γ b = X.act l ↑(sgD N l q) b := by
    conv_lhs => rw [← hb' _ hδ]
    rw [Tower.act_act Ω ε X l _ _ (by rw [Matrix.SpecialLinearGroup.det_coe]; norm_num)
      (by rw [Matrix.SpecialLinearGroup.det_coe]; norm_num), ← Matrix.SpecialLinearGroup.coe_mul,
      inv_mul_cancel_right]
  have hdq : (0 : ℤ) < Matrix.det !![(q : ℤ), 0; 0, 1] := by
    simpa [Matrix.det_fin_two] using hq.pos
  refine ⟨?_, fun s => ?_⟩
  · unfold Tower.heckeT
    simp only [LinearMap.add_apply, LinearMap.sum_apply]
    congr 1
    · symm
      have hinj : ∀ a ∈ Finset.range q, ∀ a' ∈ Finset.range q, a * M % q = a' * M % q → a = a' := by
        intro a ha a' ha' h
        rw [Finset.mem_range] at ha ha'
        have h' : a ≡ a' [MOD q] := Nat.ModEq.cancel_right_of_coprime hqM h
        unfold Nat.ModEq at h'
        rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt ha'] at h'
      refine Finset.sum_nbij (fun j => j * M % q) (fun a _ => Finset.mem_range.mpr (Nat.mod_lt _ hq.pos))
        (fun a ha a' ha' h => hinj a (Finset.mem_coe.mp ha) a' (Finset.mem_coe.mp ha') h) ?_ ?_
      · intro k hk
        obtain ⟨a, ha, h⟩ := Finset.surj_on_of_inj_on_of_card_le (fun a _ => a * M % q)
          (fun a _ => Finset.mem_range.mpr (Nat.mod_lt _ hq.pos)) (fun a a' ha ha' h => hinj a ha a' ha' h)
          le_rfl k (Finset.mem_coe.mp hk)
        exact ⟨a, Finset.mem_coe.mpr ha, h.symm⟩
      · intro a _
        have hdm := Nat.mod_add_div (a * M) q
        generalize a * M % q = r at hdm ⊢
        generalize a * M / q = t at hdm
        let T : SL(2, ℤ) := ⟨!![1, (t : ℤ); 0, 1], by simp [Matrix.det_fin_two]⟩
        have hT : T ∈ Gam N l := by
          unfold Gam
          rw [Subgroup.mem_inf, CongruenceSubgroup.Gamma1_mem, CongruenceSubgroup.Gamma0_mem]
          simp [T]
        have hz : (a : ℤ) * M = r + q * t := by exact_mod_cast hdm.symm
        have hm : !![1, (a : ℤ) * M; 0, (q : ℤ)] = (T : Matrix (Fin 2) (Fin 2) ℤ) * !![1, (r : ℤ); 0, (q : ℤ)] := by
          ext i j
          fin_cases i <;> fin_cases j <;> simp [T, Matrix.mul_apply, Fin.sum_univ_two] <;> linear_combination hz
        rw [hm, ← Tower.act_act Ω ε X l _ _ (by rw [Matrix.SpecialLinearGroup.det_coe]; norm_num)
          (by simpa [Matrix.det_fin_two] using hq.pos), hb' T hT]
    · rw [← Tower.act_act Ω ε X l _ _ (by rw [Matrix.SpecialLinearGroup.det_coe]; norm_num) hdq,
        ← Tower.act_act Ω ε X l _ _ (by rw [Matrix.SpecialLinearGroup.det_coe]; norm_num) hdq, hAct]
  · unfold Tower.diam
    rw [GlobalTheory.T.galois_commutes_hecke_action ε X N l w hN b hb _ hSmem s, hAct]
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.EsOf

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KZ.ES UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb
open scoped Matrix MatrixGroups

private theorem dvd2 {R : Type} [CommRing R] {d a b x y z : R} (ha : d ∣ a) (hb : d ∣ b) (h : z = a * x + b * y) : d ∣ z :=
  h ▸ dvd_add (ha.mul_right x) (hb.mul_right y)

private theorem es_of (h1 : SEsLev) (h2 : SEsFrob) (h3 : SEsT)
    (hU : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (l M₀ : ℕ), l.Prime → 0 < M₀ → l ∣ M₀ → ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ (V : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω), FrobV V q s → ∀ (n k : ℕ) (f : X.Kˣ), f ∈ X.Un (l ^ n) → ES.Lev X (M₀ * l ^ k) f → ∀ γ : SL(2, ℤ), DiagMod (M₀ * l ^ k) q γ → ∃ g : X.Kˣ, Nq X (M₀ * l ^ k) q f * X.sl (toGQ ((γ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) (f : X.K) = X.gal s (f : X.K) * (X.gal s.symm (X.sl (ofSL γ) (f : X.K))) ^ q * (g : X.K) ^ (l ^ n)) :
    SEs := by
  intro l hl Ω _ _ _ ε X ho N w hN
  have hM0 : 0 < 6 * l * N := by have := hl.out.pos; positivity
  obtain ⟨φ, hφ1, hφ2⟩ := X.j_hol
  obtain ⟨S, hS⟩ := hU ε X ⟨φ, hφ2, hφ1⟩ l (6 * l * N) hl.out hM0 ⟨6 * N, by ring⟩
  refine ⟨S ∪ (6 * l * N).primeFactors, fun v B σ hv hq hB hσ b hb => ?_⟩
  set q := normV v with hqdef
  rw [Finset.mem_union, not_or] at hv
  have hc : Nat.Coprime q (6 * l * N) := (Nat.Prime.coprime_iff_not_dvd hq).2 fun h =>
    hv.2 (Nat.mem_primeFactors.2 ⟨hq, h, hM0.ne'⟩)
  have hcl : Nat.Coprime q l := hc.coprime_dvd_right ⟨6 * N, by ring⟩
  have hql : q ≠ l := fun h => by
    rw [h, Nat.coprime_self] at hcl
    exact hl.out.ne_one hcl
  obtain ⟨hF, hχ⟩ := h2 Ω l v B σ hq hql hB hσ
  induction hb using Submodule.span_induction with
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add (f := _), hx, hy, smul_add]; abel
  | smul a x _ hx => simp only [map_smul, hx, smul_add, smul_comm a]
  | mem b hb =>
  funext u
  rw [← sub_eq_zero]
  have sep : ∀ x : X.Khat l, (∀ n, AdicCompletion.eval (idl l) (X.Kl l) n x = 0) → x = 0 := fun x h =>
    AdicCompletion.ext fun n => by simpa [AdicCompletion.eval_apply] using h n
  refine sep _ fun n => ?_
  obtain ⟨c1, c2, c3⟩ := h1 Ω ε X l N w hN b hb n
  obtain ⟨k, F, hk, hFu, hFl, hR⟩ := c3 ![u 0, (q : ℤ_[l]) * u 1]
  set M := 6 * l * N * l ^ k with hM
  have hMpos : 0 < M := by have := hl.out.pos; positivity
  have hcM : Nat.Coprime q M := Nat.Coprime.mul_right hc (hcl.pow_right k)
  obtain ⟨γ, hγ⟩ : ∃ γ : SL(2, ℤ), DiagMod M q γ := by
    haveI : NeZero M := ⟨hMpos.ne'⟩
    let t := ZMod.unitOfCoprime q hcM
    obtain ⟨γ, hγ⟩ := GlobalTheory.T.specialLinearGroup_int_map_zmod_surjective M (⟨!![((t⁻¹ : (ZMod M)ˣ) : ZMod M), 0; 0, (t : ZMod M)], by simp [Matrix.det_fin_two_of]⟩ : SL(2, ZMod M))
    have e := fun i j => congrArg (fun m : SL(2, ZMod M) => (m : Matrix (Fin 2) (Fin 2) (ZMod M)) i j) hγ
    exact ⟨γ, by simpa [en] using e 0 1, by simpa [en] using e 1 0, by simpa [en, t] using e 1 1⟩
  obtain ⟨g, hg⟩ := hS q hq hv.1 B σ hF n k F hFu hFl γ hγ
  obtain ⟨t1, t2⟩ := h3 Ω ε X l N w q M hN hq (hc.coprime_dvd_right ⟨6, by ring⟩) hcM ⟨6 * l ^ k, by rw [hM]; ring⟩ γ hγ b hb
  obtain ⟨-, r2, r3, r4, r5, -, -⟩ := sCls Ω ε X l n
  have hd : ∀ z : ℤ, (M : ℤ) ∣ z → (l : ℤ_[l]) ^ n ∣ (z : ℤ_[l]) := fun z hz => by
    have : ((l ^ n : ℕ) : ℤ) ∣ z := (Int.natCast_dvd_natCast.2 ((pow_dvd_pow l hk).mul_left _)).trans hz
    simpa using (Int.castRingHom ℤ_[l]).map_dvd this
  have d01 := hd _ ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hγ.1)
  have d10 := hd _ ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hγ.2.1)
  have d11 := hd (en γ 1 1 - q) ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (by push_cast; rw [hγ.2.2, sub_self]))
  have dM := hd M dvd_rfl
  have hdet : ((en γ 0 0 : ℤ) : ℤ_[l]) * (en γ 1 1 : ℤ) - (en γ 0 1 : ℤ) * (en γ 1 0 : ℤ) = 1 := by
    have := γ.det_coe
    rw [Matrix.det_fin_two] at this
    exact_mod_cast congrArg (Int.cast : ℤ → ℤ_[l]) this
  push_cast at d11 dM
  have d00 : (l : ℤ_[l]) ^ n ∣ ((en γ 0 0 : ℤ) : ℤ_[l]) * q - 1 :=
    dvd2 (x := -((en γ 0 0 : ℤ) : ℤ_[l])) (y := ((en γ 1 0 : ℤ) : ℤ_[l])) d11 d01 (by linear_combination hdet)
  have near : ∀ u' : Fin 2 → ℤ_[l], (l : ℤ_[l]) ^ n ∣ u' 0 - u 0 → (l : ℤ_[l]) ^ n ∣ u' 1 - q * u 1 →
      Rep X l n F ((4 : ℤ_[l]) • b u') := fun u' a0 a1 => by
    have := c1 u' ![u 0, (q : ℤ_[l]) * u 1] (Fin.forall_fin_two.2 ⟨a0, a1⟩)
    rw [map_sub, sub_eq_zero] at this
    unfold UpperTheory.Kd.K4.Rep at hR ⊢
    rw [map_smul, this, ← map_smul, hR]
  have one : Rep X l n 1 0 := by simpa using (r2 _ _ _ _ hR hR).2
  have A : ∀ s : Finset ℕ, Rep X l n (∏ j ∈ s, Units.map ((X.sl (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)])).toRingEquiv : X.K →* X.K) F)
      (∑ j ∈ s, (4 : ℤ_[l]) • X.act l !![1, (j * M : ℤ); 0, (q : ℤ)] b u) := fun s => by
    induction s using Finset.induction_on with
    | empty => simpa using one
    | insert j s hj ih =>
      rw [Finset.prod_insert hj, Finset.sum_insert hj]
      refine (r2 _ _ _ _ ?_ ih).1
      have := r5 (X.sl (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)])).toRingEquiv _ _
        (near (mZl l !![1, (j * M : ℤ); 0, (q : ℤ)] *ᵥ u)
          (dvd2 (x := j * u 1) (y := 0) dM dM (by simp [mZl, Matrix.mulVec, dotProduct, Fin.sum_univ_two]; ring))
          (by simp [mZl, Matrix.mulVec, dotProduct, Fin.sum_univ_two]))
      rwa [map_smul] at this
  have Bq := r5 (X.sl (toGQ ((γ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1]))).toRingEquiv _ _
    (near (mZl l ((γ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1]) *ᵥ u)
      (dvd2 (x := u 0) (y := u 1) d00 d01 (by simp [mZl, en, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.mul_apply]; ring))
      (dvd2 (x := q * u 0) (y := u 1) d10 d11 (by simp [mZl, en, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.mul_apply]; ring)))
  have Cq := r5 (X.gal σ) _ _ hR
  set χ' : ℤ_[l] := (cyclotomicCharacter Ω l (σ⁻¹).toRingEquiv : ℤ_[l]) with hχ'
  have hχq : (q : ℤ_[l]) * χ' = 1 := by
    rw [← hχ, hχ', ← Units.val_mul, ← map_mul]
    have : σ.toRingEquiv * (σ⁻¹).toRingEquiv = 1 := by
      ext z; exact σ.apply_symm_apply z
    rw [this, map_one, Units.val_one]
  have D0 := near ((q : ℤ_[l]) • (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ ![u 0, χ' * u 1]))
    (dvd2 (x := u 0) (y := q * χ' * u 1) d00 d01 (by simp [mZl, en, Matrix.mulVec, dotProduct, Fin.sum_univ_two]; ring))
    (dvd2 (x := q * u 0) (y := u 1) d10 d11 (by
      simp [mZl, en, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      linear_combination (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ℤ_[l]) * u 1 * hχq))
  rw [c2] at D0
  have D := r3 _ _ q (r5 (X.gal σ⁻¹) _ _ (r5 (X.sl (toGQ (γ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv _ _ D0))
  have fin := r4 _ _ _ _ (r2 _ _ _ _ (A (Finset.range q)) Bq).1 (r2 _ _ _ _ Cq D).1 ⟨g, Units.ext (by
    rw [(sSlD Ω ε X N hN).2.2.1 γ]
    have hg' : Nq X M q F * _ = X.gal σ F * (X.gal σ⁻¹ _) ^ q * _ := hg
    clear_value M
    simpa [Nq, Units.coe_prod] using hg')⟩
  have h4 : IsUnit (4 : ℤ_[l]) := by
    have : IsUnit ((4 : ℕ) : ℤ_[l]) := by
      rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
      exact ((Nat.coprime_primes hl.out Nat.prime_two).2 ho).pow_right 2
    simpa using this
  rw [← h4.smul_eq_zero, ← map_smul, ← fin, t1, t2]
  congr 1
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_sub, smul_add, Finset.smul_sum, map_smul]
  congr 1
  change _ + (4 : ℤ_[l]) • (q : ℤ_[l]) ^ (w + 1) • X.kmap l (X.gal σ⁻¹) (X.kmap l _ (b _)) = _
  rw [smul_smul, smul_smul, smul_smul]
  congr 1
  · change (4 : ℤ_[l]) • X.kmap l (X.gal σ) (b _) = _
    rw [hχ]
  · congr 1
    ring

theorem UpperTheory.V.Z.Kato.Nb.sEs : UpperTheory.V.Z.Kato.Nb.SEs := es_of sEsLev sEsFrob sEsT @GlobalTheory.T.eichlerShimura_kummer_function_uniform_exceptional_primes
end
end
