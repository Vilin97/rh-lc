module

public import Development.AbelianVarietyTheory.Definitions.Foundations.LiftApplyOfMemAdmissibleSubalgebra
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEichlerShimuraPotentialOfMemKummerStatement
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
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerPotentialRelationLinearHeckeStableStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerRelatedPairFstEqZeroOfTrivialStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SemisimpleHeckePolyTransportRingEquivStatement
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEichlerShimuraPotentialOfMemVB

section

@[expose] public section

noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ.H3

theorem polySlash_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (m : Matrix (Fin 2) (Fin 2) ℤ)
    (p : MvPolynomial (Fin 2) R) : slP m (MvPolynomial.map φ p) = MvPolynomial.map φ (slP m p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [slP]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp, Betti.slP_X, MvPolynomial.smul_eq_C_mul]

theorem map_mem_pot {E : Type} [CommRing E] {l : ℕ} [Fact l.Prime] [Algebra ℤ_[l] E] {w : ℕ}
    {Γ : Subgroup SL(2, ℤ)} {F : ℂ → MvPolynomial (Fin 2) ℤ_[l]} (hF : F ∈ Pot ℤ_[l] w Γ) :
    (fun z => MvPolynomial.map (algebraMap ℤ_[l] E) (F z)) ∈ Pot E w Γ := by
  obtain ⟨h1, h2⟩ := hF
  refine ⟨fun z => (h1 z).map _, fun γ hγ => ?_⟩
  obtain ⟨p, hp⟩ := h2 γ hγ
  refine ⟨MvPolynomial.map (algebraMap ℤ_[l] E) p, fun z hz => ?_⟩
  rw [← hp z hz, map_sub, polySlash_map]

theorem exists_pot_of_mem_VB : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (N l w : ℕ)
    [Fact l.Prime] {E : Type} [Field E] [Algebra ℤ_[l] E],
    (∀ b ∈ X.BSet N l w, ∃ F ∈ Pot ℤ_[l] w (Gam N l), H3.Rel X l b F) →
      ∀ x ∈ X.VB N l w E, ∃ G ∈ Pot E w (Gam N l), (x, G) ∈ H3.abelian₂ X l E := by
  intro Ω _ _ ε X N l w _ E _ _ hB
  let S : Submodule E (E ⊗[ℤ_[l]] X.Fn l) :=
    { carrier := {x | ∃ G ∈ Pot E w (Gam N l), (x, G) ∈ abelian₂ X l E}
      add_mem' := by
        rintro x y ⟨G, hG, hx⟩ ⟨G', hG', hy⟩
        exact ⟨G + G', (Betti.potSub E w (Gam N l)).add_mem hG hG', (abelian₂ X l E).add_mem hx hy⟩
      zero_mem' := ⟨0, (Betti.potSub E w (Gam N l)).zero_mem, (abelian₂ X l E).zero_mem⟩
      smul_mem' := by
        rintro c x ⟨G, hG, hx⟩
        exact ⟨c • G, (Betti.potSub E w (Gam N l)).smul_mem c hG, (abelian₂ X l E).smul_mem c hx⟩ }
  have h1 : ∀ b ∈ X.B N l w, (1 : E) ⊗ₜ[ℤ_[l]] b ∈ S := by
    intro b hb
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨F, hF, hR⟩ := hB b hb
      exact ⟨_, map_mem_pot hF, Submodule.subset_span ⟨b, F, hR, rfl⟩⟩
    | zero => simpa using S.zero_mem
    | add b b' _ _ h h' => simpa [TensorProduct.tmul_add] using S.add_mem h h'
    | smul r b _ h =>
      rw [TensorProduct.tmul_smul, ← algebraMap_smul E r]
      exact S.smul_mem _ h
  intro x hx
  obtain ⟨y, rfl⟩ := hx
  show _ ∈ S
  induction y using TensorProduct.induction_on with
  | zero => simpa using S.zero_mem
  | tmul c b =>
    rw [LinearMap.baseChange_tmul, Submodule.subtype_apply]
    have : c ⊗ₜ[ℤ_[l]] (b : X.Fn l) = c • ((1 : E) ⊗ₜ[ℤ_[l]] (b : X.Fn l)) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this]; exact S.smul_mem c (h1 b b.2)
  | add y y' h h' => rw [map_add (f := _)]; exact S.add_mem h h'

end GlobalTheory.KZ.H3
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEichlerShimuraPotentialOfMemVBStatement

section

@[expose] public section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.exists_eichlerShimuraPotential_of_mem_VB : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (N l w : ℕ) [Fact l.Prime] {E : Type} [Field E] [Algebra ℤ_[l] E], (∀ b ∈ X.BSet N l w, ∃ F ∈ Pot ℤ_[l] w (Gam N l), H3.Rel X l b F) → ∀ x ∈ X.VB N l w E, ∃ G ∈ Pot E w (Gam N l), (x, G) ∈ H3.abelian₂ X l E := by
  first | exact @GlobalTheory.KZ.H3.exists_pot_of_mem_VB | exact GlobalTheory.KZ.H3.exists_pot_of_mem_VB | (intros; apply GlobalTheory.KZ.H3.exists_pot_of_mem_VB <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerPotentialSpanHeckeLetterStable

section

@[expose] public section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

noncomputable section

namespace GlobalTheory.KZ.H3.LamStab

theorem polySlash_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (m : Matrix (Fin 2) (Fin 2) ℤ)
    (p : MvPolynomial (Fin 2) R) : slP m (MvPolynomial.map φ p) = MvPolynomial.map φ (slP m p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [slP]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, MvPolynomial.map_X, Betti.slP_X, map_add (f := _), map_smul]
    simp [MvPolynomial.smul_eq_C_mul]

theorem opP_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (m : Matrix (Fin 2) (Fin 2) ℤ)
    (F : ℂ → MvPolynomial (Fin 2) R) :
    opP S m (fun z => MvPolynomial.map φ (F z)) = fun z => MvPolynomial.map φ (opP R m F z) := by
  funext z
  simp only [opP, LinearMap.coe_mk, AddHom.coe_mk, polySlash_map]

theorem sum_opP_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {ι : Type} (s : Finset ι)
    (m : ι → Matrix (Fin 2) (Fin 2) ℤ) (F : ℂ → MvPolynomial (Fin 2) R) :
    (∑ j ∈ s, opP S (m j)) (fun z => MvPolynomial.map φ (F z)) =
      fun z => MvPolynomial.map φ ((∑ j ∈ s, opP R (m j)) F z) := by
  funext z

  simp only [LinearMap.sum_apply, Finset.sum_apply, opP_map, map_sum]

theorem opL_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (N l : ℕ) (T : Letter)
    (F : ℂ → MvPolynomial (Fin 2) R) :
    opL S N l T (fun z => MvPolynomial.map φ (F z)) = fun z => MvPolynomial.map φ (opL R N l T F z) := by
  cases T with
  | T q =>
    simp only [opL, LinearMap.add_apply, sum_opP_map, opP_map]
    funext z; simp
  | U => simp only [opL, sum_opP_map]
  | D d => simp only [opL, opP_map]

end GlobalTheory.KZ.H3.LamStab


open GlobalTheory.KZ.H3 GlobalTheory.KZ.H3.LamStab in
theorem GlobalTheory.KZ.H3.lam_stable : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime]
    {E : Type} [Field E] [Algebra ℤ_[l] E] (T : Letter) (p : (E ⊗[ℤ_[l]] X.Fn l) × (ℂ → MvPolynomial (Fin 2) E)),
    p ∈ H3.abelian₂ X l E → (X.opV N l E T p.1, opL E N l T p.2) ∈ H3.abelian₂ X l E := by
  intro Ω _ _ ε X N l _ E _ _ T p hp
  let Φ : ((E ⊗[ℤ_[l]] X.Fn l) × (ℂ → MvPolynomial (Fin 2) E)) →ₗ[E]
      ((E ⊗[ℤ_[l]] X.Fn l) × (ℂ → MvPolynomial (Fin 2) E)) :=
    LinearMap.prodMap (X.opV N l E T) (opL E N l T)
  have key : abelian₂ X l E ≤ (abelian₂ X l E).comap Φ := by
    unfold abelian₂
    rw [Submodule.span_le]
    rintro q ⟨b, F, hR, rfl⟩
    refine Submodule.subset_span ⟨X.op N l T b, opL ℤ_[l] N l T F,
      (GlobalTheory.T.kummerPotentialRelation_linear_hecke_stable Ω ε X l).2.2.2.2 N T b F hR, ?_⟩
    simp only [Φ, LinearMap.prodMap_apply, Tower.opV, LinearMap.baseChange_tmul, opL_map]
  exact key hp
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerPotentialSpanHeckeLetterStableStatement

section

@[expose] public section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.kummerPotentialSpan_hecke_letter_stable : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime] {E : Type} [Field E] [Algebra ℤ_[l] E] (T : Letter) (p : (E ⊗[ℤ_[l]] X.Fn l) × (ℂ → MvPolynomial (Fin 2) E)), p ∈ H3.abelian₂ X l E → (X.opV N l E T p.1, opL E N l T p.2) ∈ H3.abelian₂ X l E := by
  first | exact @GlobalTheory.KZ.H3.lam_stable | exact GlobalTheory.KZ.H3.lam_stable | (intros; apply GlobalTheory.KZ.H3.lam_stable <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.SemisimpleTensorOfSemisimplePotentials

section

@[expose] public section

noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ.Comp

theorem lift_mem_lam {Ω : Type} [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime]
    {E : Type} [Field E] [Algebra ℤ_[l] E] (P : FreeAlgebra E Letter) :
    ∀ p ∈ H3.abelian₂ X l E,
      (FreeAlgebra.lift E (X.opV N l E) P p.1, FreeAlgebra.lift E (opL E N l) P p.2) ∈ H3.abelian₂ X l E := by
  induction P using FreeAlgebra.induction with
  | grade0 r =>
    intro p hp
    convert (H3.abelian₂ X l E).smul_mem r hp using 1
    ext <;> simp [Algebra.algebraMap_eq_smul_one]
  | grade1 T =>
    intro p hp
    simpa using GlobalTheory.T.kummerPotentialSpan_hecke_letter_stable ε X N l T p hp
  | mul a b ha hb =>
    intro p hp
    simpa using ha _ (hb p hp)
  | add a b ha hb =>
    intro p hp
    simpa using (H3.abelian₂ X l E).add_mem (ha p hp) (hb p hp)

theorem ssbb_of_ssPotB : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ {E : Type} [Field E] [Algebra ℤ_[l] E] (ι : E ≃+* ℂ) (lam : Letter → E), SSPotB N l w (fun T => ι (lam T)) → X.SSBB N l w E lam := by
  intro Ω _ _ _ ε X hε hj N l w _ hl2 hN hNl hw E _ _ ι lam hSS
  haveI : CharZero E := RingHom.charZero ι.toRingHom
  obtain ⟨P, hPA, hP1, hP⟩ := GlobalTheory.T.semisimpleHeckePoly_transport_ringEquiv N l w ι lam hSS
  refine ⟨P, hPA, hP1, fun x hx T hT => ?_⟩
  obtain ⟨G, hG, hxG⟩ := GlobalTheory.T.exists_eichlerShimuraPotential_of_mem_VB ε X N l w (GlobalTheory.T.exists_eichlerShimuraPotential_of_mem_kummer ε X hε hj N l w hl2 hN hNl hw) x hx
  have h1 := lift_mem_lam ε X N l P (x, G) hxG
  have h2 := GlobalTheory.T.kummerPotentialSpan_hecke_letter_stable ε X N l T _ h1
  have h3 := (H3.abelian₂ X l E).sub_mem h2 ((H3.abelian₂ X l E).smul_mem (lam T) h1)
  have h4 : ((X.opV N l E T - lam T • (1 : Module.End E (E ⊗[ℤ_[l]] X.Fn l)))
        (FreeAlgebra.lift E (X.opV N l E) P x),
      (opL E N l T - lam T • (1 : Module.End E (ℂ → MvPolynomial (Fin 2) E)))
        (FreeAlgebra.lift E (opL E N l) P G)) ∈ H3.abelian₂ X l E := by
    simpa using h3
  exact GlobalTheory.T.kummerRelatedPair_fst_eq_zero_of_trivial ε X hε hj N l w (by omega) inferInstance _ _ h4 (hP G hG T hT)

end GlobalTheory.KZ.Comp
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.SemisimpleTensorOfSemisimplePotentialsStatement

section

@[expose] public section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.semisimple_tensor_of_semisimple_potentials : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ {E : Type} [Field E] [Algebra ℤ_[l] E] (ι : E ≃+* ℂ) (lam : Letter → E), SSPotB N l w (fun T => ι (lam T)) → X.SSBB N l w E lam := by
  first | exact @GlobalTheory.KZ.Comp.ssbb_of_ssPotB | exact GlobalTheory.KZ.Comp.ssbb_of_ssPotB | (intros; apply GlobalTheory.KZ.Comp.ssbb_of_ssPotB <;> assumption)
end
end
