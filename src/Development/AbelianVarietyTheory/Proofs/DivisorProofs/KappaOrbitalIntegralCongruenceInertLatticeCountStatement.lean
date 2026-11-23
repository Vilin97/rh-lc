module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjRelEquiv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyEqOfHermitianMultiplicationModelStatement
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianMultiplicationModelNonsplitStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryModelOfSelfDualLatticeCountNeZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianModelsConjUnitaryDifferByNormStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceKernelSignEqEtaGramDetStatement
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralCongruenceLevelEqCountStatement
import Mathlib.RingTheory.PiTensorProduct

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjUnitaryOfSameHermitianMultiplicationModel

section

@[expose] public section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

namespace GlobalTheory.KapLat

theorem models_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E) (B : GlobalTheory.UnitLemma.InvAlg K) (u x : B.A) (n : ℕ) (γ γ' : GLw n w), IsModel w e B u x γ → IsModel w e B u x γ' → ∃ y ∈ UL n w, γ' = y⁻¹ * γ * y := by
  intro E _ _ _ w hw K e B u x n γ γ' hγ hγ'
  obtain ⟨ψ, hψl, hψu, hψh⟩ := hγ
  obtain ⟨ψ', hψ'l, hψ'u, hψ'h⟩ := hγ'
  let f : (Fin n → w.adicCompletion E) →ₗ[w.adicCompletion E] (Fin n → w.adicCompletion E) :=
    { toFun := fun v => ψ (ψ'.symm v)
      map_add' := by intro a b; simp
      map_smul' := by
        intro t v
        obtain ⟨c, rfl⟩ : ∃ c, e c = t := ⟨e.symm t, e.apply_symm_apply t⟩
        obtain ⟨a, rfl⟩ : ∃ a, ψ' a = v := ⟨ψ'.symm v, ψ'.apply_symm_apply v⟩
        simp only [RingHom.id_apply]
        rw [← hψ'l, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply, hψl] }
  let g : (Fin n → w.adicCompletion E) →ₗ[w.adicCompletion E] (Fin n → w.adicCompletion E) :=
    { toFun := fun v => ψ' (ψ.symm v)
      map_add' := by intro a b; simp
      map_smul' := by
        intro t v
        obtain ⟨c, rfl⟩ : ∃ c, e c = t := ⟨e.symm t, e.apply_symm_apply t⟩
        obtain ⟨a, rfl⟩ : ∃ a, ψ a = v := ⟨ψ.symm v, ψ.apply_symm_apply v⟩
        simp only [RingHom.id_apply]
        rw [← hψl, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply, hψ'l] }
  have hfg : f ∘ₗ g = LinearMap.id := LinearMap.ext fun v => by simp [f, g]
  have hgf : g ∘ₗ f = LinearMap.id := LinearMap.ext fun v => by simp [f, g]
  let y : GLw n w := ⟨LinearMap.toMatrix' f, LinearMap.toMatrix' g,
    by rw [← LinearMap.toMatrix'_comp, hfg, LinearMap.toMatrix'_id],
    by rw [← LinearMap.toMatrix'_comp, hgf, LinearMap.toMatrix'_id]⟩
  have hy : ∀ v, (y : Matrix (Fin n) (Fin n) (w.adicCompletion E)) *ᵥ v = f v := fun v =>
    LinearMap.toMatrix'_mulVec f v

  have hinv : ∀ v v', stdH w (f v) (f v') = stdH w v v' := by
    intro v v'
    obtain ⟨a, rfl⟩ : ∃ a, ψ' a = v := ⟨ψ'.symm v, ψ'.apply_symm_apply v⟩
    obtain ⟨b, rfl⟩ : ∃ b, ψ' b = v' := ⟨ψ'.symm v', ψ'.apply_symm_apply v'⟩
    simp only [f, LinearMap.coe_mk, AddHom.coe_mk, AddEquiv.symm_apply_apply]
    rw [hψh, hψ'h]
  refine ⟨y, ?_, ?_⟩
  · unfold UL
    rw [if_neg hw]
    change Formalism.UG.cT (cj w) (y : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * 1 *
      (y : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = 1
    set M : Matrix (Fin n) (Fin n) (w.adicCompletion E) := (y : Matrix (Fin n) (Fin n) (w.adicCompletion E)) with hM
    have key : Mᵀ * M.map (cj w) = 1 := by
      refine Matrix.ext fun i j => ?_
      have h1 := hinv (Pi.single i 1) (Pi.single j 1)
      rw [← hy, ← hy] at h1
      simp only [stdH, Matrix.mulVec_single_one] at h1
      have h2 : (if i = j then (1 : w.adicCompletion E) else 0) = ∑ k, M k i * cj w (M k j) := by
        simpa [Pi.single_apply, eq_comm] using h1
      rw [Matrix.mul_apply, Matrix.one_apply]
      simp only [Matrix.transpose_apply, Matrix.map_apply]
      exact h2.symm
    have key2 := congrArg Matrix.transpose key
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at key2
    rw [Matrix.mul_one]
    exact key2
  ·
    have hc : (y : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * γ'.val = γ.val * y := by
      apply Matrix.toLin'.injective
      apply LinearMap.ext
      intro v
      obtain ⟨a, rfl⟩ : ∃ a, ψ' a = v := ⟨ψ'.symm v, ψ'.apply_symm_apply v⟩
      simp only [Matrix.toLin'_apply]
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hψ'u, hy, hy]
      simp only [f, LinearMap.coe_mk, AddHom.coe_mk, AddEquiv.symm_apply_apply]
      rw [hψu]
    have hc' : y * γ' = γ * y := Units.ext hc
    rw [mul_assoc, ← hc', ← mul_assoc, inv_mul_cancel, one_mul]

end GlobalTheory.KapLat
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjUnitaryOfSameHermitianMultiplicationModelStatement

section

@[expose] public section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

theorem _root_.GlobalTheory.T.conj_unitary_of_same_hermitianMultiplicationModel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E) (B : GlobalTheory.UnitLemma.InvAlg K) (u x : B.A) (n : ℕ) (γ γ' : GLw n w), IsModel w e B u x γ → IsModel w e B u x γ' → ∃ y ∈ UL n w, γ' = y⁻¹ * γ * y := by
  first | exact @GlobalTheory.KapLat.models_conj | exact GlobalTheory.KapLat.models_conj | (intros; apply GlobalTheory.KapLat.models_conj <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdAdjoinRootAlgebrasGeneratedByPair

section

@[expose] public section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

namespace GlobalTheory.KapLat

theorem fits_prod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ)
    (e : K.E ≃+* w.adicCompletion E) (Q₁ Q₂ : (w.adicCompletion E)[X]) (B₁ B₂ : GlobalTheory.UnitLemma.InvAlg K)
    (u₁ : B₁.A) (u₂ : B₂.A), (Q₁ * Q₂).Separable → Fits w e B₁ Q₁ u₁ → Fits w e B₂ Q₂ u₂ →
    Fits w e (B₁.prod B₂) (Q₁ * Q₂) ((u₁, u₂) : B₁.A × B₂.A) := by
  intro E _ _ _ w K e Q₁ Q₂ B₁ B₂ u₁ u₂ hsep h₁ h₂
  obtain ⟨ha₁, hr₁, hd₁, hs₁⟩ := h₁
  obtain ⟨ha₂, hr₂, hd₂, hs₂⟩ := h₂
  have hne : Q₁ * Q₂ ≠ 0 := hsep.ne_zero
  have hQ₁ : Q₁ ≠ 0 := left_ne_zero_of_mul hne
  have hQ₂ : Q₂ ≠ 0 := right_ne_zero_of_mul hne
  have hcop : IsCoprime (Q₁.map e.symm.toRingHom) (Q₂.map e.symm.toRingHom) :=
    hsep.isCoprime.map (Polynomial.mapRingHom e.symm.toRingHom)
  have hfst : ∀ p : K.E[X], (aeval ((u₁, u₂) : B₁.A × B₂.A) p).1 = aeval u₁ p := fun p => by
    simpa using (Polynomial.aeval_algHom_apply (AlgHom.fst K.E B₁.A B₂.A) ((u₁, u₂) : B₁.A × B₂.A) p).symm
  have hsnd : ∀ p : K.E[X], (aeval ((u₁, u₂) : B₁.A × B₂.A) p).2 = aeval u₂ p := fun p => by
    simpa using (Polynomial.aeval_algHom_apply (AlgHom.snd K.E B₁.A B₂.A) ((u₁, u₂) : B₁.A × B₂.A) p).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · show Algebra.adjoin K.E {((u₁, u₂) : B₁.A × B₂.A)} = ⊤
    obtain ⟨a, b, hab⟩ := hcop
    have e₁ : aeval u₁ b * aeval u₁ (Q₂.map e.symm.toRingHom) = 1 := by
      have := congrArg (aeval u₁) hab
      rw [map_add (f := _), map_mul, map_mul, hr₁, mul_zero, zero_add, map_one] at this
      exact this
    have e₂ : aeval u₂ a * aeval u₂ (Q₁.map e.symm.toRingHom) = 1 := by
      have := congrArg (aeval u₂) hab
      rw [map_add (f := _), map_mul, map_mul, hr₂, mul_zero, add_zero, map_one] at this
      exact this
    rw [eq_top_iff]
    rintro ⟨y, z⟩ -
    have hy : y ∈ (aeval u₁ : K.E[X] →ₐ[K.E] B₁.A).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval, ha₁]; trivial
    have hz : z ∈ (aeval u₂ : K.E[X] →ₐ[K.E] B₂.A).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval, ha₂]; trivial
    obtain ⟨p, rfl⟩ := hy
    obtain ⟨r, rfl⟩ := hz
    have key : ((aeval u₁ p, aeval u₂ r) : B₁.A × B₂.A) =
        aeval ((u₁, u₂) : B₁.A × B₂.A) (b * Q₂.map e.symm.toRingHom * p + a * Q₁.map e.symm.toRingHom * r) := by
      refine Prod.ext ?_ ?_
      · rw [hfst, map_add (f := _), map_mul, map_mul, map_mul, map_mul, hr₁, mul_zero, zero_mul, add_zero, e₁, one_mul]
      · rw [hsnd, map_add (f := _), map_mul, map_mul, map_mul, map_mul, hr₂, mul_zero, zero_mul, zero_add, e₂, one_mul]
    exact key ▸ Polynomial.aeval_mem_adjoin_singleton K.E _
  · show aeval ((u₁, u₂) : B₁.A × B₂.A) ((Q₁ * Q₂).map e.symm.toRingHom) = 0
    rw [Polynomial.map_mul]
    refine Prod.ext ?_ ?_
    · rw [hfst, map_mul, hr₁, zero_mul]; rfl
    · rw [hsnd, map_mul, hr₂, mul_zero]; rfl
  · show Module.finrank K.E (B₁.A × B₂.A) = (Q₁ * Q₂).natDegree
    rw [Module.finrank_prod, hd₁, hd₂, natDegree_mul hQ₁ hQ₂]
  · exact Prod.ext hs₁ hs₂

end GlobalTheory.KapLat
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdAdjoinRootAlgebrasGeneratedByPairStatement

section

@[expose] public section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

theorem _root_.GlobalTheory.T.prod_adjoinRootAlgebras_generated_by_pair : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E) (Q₁ Q₂ : (w.adicCompletion E)[X]) (B₁ B₂ : GlobalTheory.UnitLemma.InvAlg K) (u₁ : B₁.A) (u₂ : B₂.A), (Q₁ * Q₂).Separable → Fits w e B₁ Q₁ u₁ → Fits w e B₂ Q₂ u₂ → Fits w e (B₁.prod B₂) (Q₁ * Q₂) ((u₁, u₂) : B₁.A × B₂.A) := by
  first | exact @GlobalTheory.KapLat.fits_prod | exact GlobalTheory.KapLat.fits_prod | (intros; apply GlobalTheory.KapLat.fits_prod <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaOrbitalIntegralCongruenceInertLatticeCount

section

@[expose] public section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

namespace GlobalTheory.KapLat

theorem model_mul_norm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E) (B : GlobalTheory.UnitLemma.InvAlg K) (u x : B.A) (n : ℕ) (γ : GLw n w), IsModel w e B u x γ → ∀ c : B.Aˣ, IsModel w e B u (x * ((c : B.A) * B.σ (c : B.A))) γ := by
  intro E _ _ _ w K e B u x n γ hM c
  obtain ⟨ψ, h1, h2, h3⟩ := hM
  let φ : B.A ≃+ (Fin n → w.adicCompletion E) :=
    { toFun := fun y => ψ ((c : B.A) * y)
      invFun := fun v => ((c⁻¹ : B.Aˣ) : B.A) * ψ.symm v
      left_inv := fun y => by simp [← mul_assoc]
      right_inv := fun v => by simp [← mul_assoc]
      map_add' := fun y z => by simp [mul_add] }
  refine ⟨φ, fun a y => ?_, fun y => ?_, fun y z => ?_⟩
  · show ψ ((c : B.A) * (a • y)) = e a • ψ ((c : B.A) * y)
    rw [mul_smul_comm, h1]
  · show ψ ((c : B.A) * (u * y)) = γ.val *ᵥ ψ ((c : B.A) * y)
    rw [show (c : B.A) * (u * y) = u * ((c : B.A) * y) by ring, h2]
  · show stdH w (ψ ((c : B.A) * y)) (ψ ((c : B.A) * z)) = _
    rw [h3]
    unfold GlobalTheory.UnitLemma.InvAlg.herm
    congr 2
    rw [map_mul]
    ring

theorem kapOrb_eq_kapSum_of_fits {E : Type} [Field E] [NumberField E] [IsCMField E] {w : Pl E} (hw : ¬ IsSplitAt w)
    {K : GlobalTheory.UnitLemma.UQ} {e : K.E ≃+* w.adicCompletion E} (hBr : Bridge w K e) {k : ℕ} {t : K.O} (ht : K.Small t)
    (htk : GlobalTheory.UnitLemma.val K.O (algebraMap K.O K.E t) = k) {n : ℕ} {Q₁ Q₂ : (w.adicCompletion E)[X]}
    {B₁ B₂ : GlobalTheory.UnitLemma.InvAlg K} {u₁ : B₁.A} {u₂ : B₂.A} (hsep : (Q₁ * Q₂).Separable) (hmon : (Q₁ * Q₂).Monic)
    (hdeg : (Q₁ * Q₂).natDegree = n) (hF₁ : Fits w e B₁ Q₁ u₁) (hF₂ : Fits w e B₂ Q₂ u₂)
    (hg : 1 + algebraMap K.O (B₁.prod B₂).A t * (B₁.prod B₂).g = (u₁, u₂)) :
    kapOrb n w Q₁ Q₂ (({γ : UL n w | γ.1 ∈ congSet w n k} : Set (UL n w)).indicator 1) =
      ((GlobalTheory.UnitLemma.InvAlg.kapSum B₁ B₂ : ℚ) : ℂ) := by
  have hcl : Equivalence (fun x y : {x : (B₁.prod B₂).Aˣ // (B₁.prod B₂).σ (x : (B₁.prod B₂).A) = x} =>
      ∃ u : (B₁.prod B₂).Aˣ, (y.1 : (B₁.prod B₂).A) = x.1 * (u * (B₁.prod B₂).σ (u : (B₁.prod B₂).A))) := by
    refine ⟨?_, ?_, ?_⟩
    · intro x; exact ⟨1, by simp⟩
    · rintro x y ⟨u, hu⟩
      refine ⟨u⁻¹, ?_⟩
      have h1 : ((u : (B₁.prod B₂).A) * ((u⁻¹ : (B₁.prod B₂).Aˣ) : (B₁.prod B₂).A)) *
          ((B₁.prod B₂).σ (u : (B₁.prod B₂).A) * (B₁.prod B₂).σ ((u⁻¹ : (B₁.prod B₂).Aˣ) : (B₁.prod B₂).A)) = 1 := by
        rw [← map_mul, Units.mul_inv, map_one, one_mul]
      rw [hu]
      calc (x.1 : (B₁.prod B₂).A) = x.1 * (((u : (B₁.prod B₂).A) * ((u⁻¹ : (B₁.prod B₂).Aˣ) : (B₁.prod B₂).A)) *
          ((B₁.prod B₂).σ (u : (B₁.prod B₂).A) * (B₁.prod B₂).σ ((u⁻¹ : (B₁.prod B₂).Aˣ) : (B₁.prod B₂).A))) := by rw [h1, mul_one]
        _ = _ := by ring
    · rintro x y z ⟨u, hu⟩ ⟨v, hv⟩
      exact ⟨u * v, by rw [hv, hu, Units.val_mul, map_mul]; ring⟩
  have hconj : Equivalence (fun x y : UL n w => ∃ g, y = g⁻¹ * x * (MonoidHom.id (UL n w)) g) := by
    refine ⟨?_, ?_, ?_⟩
    · intro x; exact ⟨1, by simp⟩
    · rintro x y ⟨g, rfl⟩; exact ⟨g⁻¹, by simp [mul_assoc]⟩
    · rintro x y z ⟨g, rfl⟩ ⟨h, rfl⟩; exact ⟨g * h, by simp [mul_assoc]⟩
  have hF := GlobalTheory.T.prod_adjoinRootAlgebras_generated_by_pair E w K e Q₁ Q₂ B₁ B₂ u₁ u₂ hsep hF₁ hF₂
  unfold kapOrb clSum GlobalTheory.UnitLemma.InvAlg.kapSum
  rw [cast_finsum]
  set S' : Set (TwCl (MonoidHom.id (UL n w))) := {c | c.rep.1.val.charpoly = Q₁ * Q₂} with hS'
  have hex : ∀ c : TwCl (MonoidHom.id (UL n w)), c ∈ S' → ∃ x : (B₁.prod B₂).A, (B₁.prod B₂).σ x = x ∧ IsUnit x ∧
      IsModel w e (B₁.prod B₂) (u₁, u₂) x c.rep.1 := fun c hc =>
    GlobalTheory.T.exists_hermitianMultiplicationModel_nonsplit E w hw K e hBr n (Q₁ * Q₂) (B₁.prod B₂) (u₁, u₂) hsep hF c.rep.1 c.rep.2 hc
  let Φ : TwCl (MonoidHom.id (UL n w)) → (B₁.prod B₂).Cl := fun c =>
    if h : ∃ x : (B₁.prod B₂).A, (B₁.prod B₂).σ x = x ∧ IsUnit x ∧ IsModel w e (B₁.prod B₂) (u₁, u₂) x c.rep.1 then
      Quot.mk _ ⟨h.choose_spec.2.1.unit, by simpa using h.choose_spec.1⟩ else Quot.mk _ ⟨1, by simp⟩
  have hrep : ∀ c ∈ S', IsModel w e (B₁.prod B₂) (u₁, u₂) (GlobalTheory.UnitLemma.InvAlg.Cl.rep (Φ c)) c.rep.1 := by
    intro c hc
    have h := hex c hc
    have hΦ : Φ c = Quot.mk _ ⟨h.choose_spec.2.1.unit, by simpa using h.choose_spec.1⟩ := dif_pos h
    have hq := Quot.eqvGen_exact ((Quot.out_eq (Φ c)).trans hΦ)
    obtain ⟨v, hv⟩ := hcl.symm (hcl.eqvGen_iff.1 hq)
    have hr : GlobalTheory.UnitLemma.InvAlg.Cl.rep (Φ c) = h.choose * ((v : (B₁.prod B₂).A) * (B₁.prod B₂).σ (v : (B₁.prod B₂).A)) := by
      unfold GlobalTheory.UnitLemma.InvAlg.Cl.rep
      rw [hv]
      simp
    rw [hr]
    exact model_mul_norm E w K e (B₁.prod B₂) _ _ n _ h.choose_spec.2.2 v
  let G : (B₁.prod B₂).Cl → ℂ := fun κ =>
    ((K.eta (B₁.gramDet (GlobalTheory.UnitLemma.InvAlg.Cl.rep κ).1) * (B₁.prod B₂).N κ.rep : ℚ) : ℂ)
  have hterm : ∀ c ∈ S', kapSign n w Q₁ c.rep.1 * twOrb (MonoidHom.id (UL n w)) (KL n w) c.rep
      (({γ : UL n w | γ.1 ∈ congSet w n k} : Set (UL n w)).indicator 1) = G (Φ c) := by
    intro c hc
    have hm := hrep c hc
    have h7 := GlobalTheory.T.twisted_orbitalIntegral_congruence_level_eq_count E w hw K e hBr k t ht htk n (Q₁ * Q₂) (B₁.prod B₂) _ _ hsep hF hg.symm c.rep.1 c.rep.2 hm
    simp only [Subtype.coe_eta] at h7
    rw [GlobalTheory.T.inertPlace_kernelSign_eq_eta_gramDet E w hw K e hBr n Q₁ Q₂ B₁ B₂ u₁ u₂ hsep hF₁ hF₂ _ _ hm, h7]
    simp [G]
  have hinj : Set.InjOn Φ S' := by
    intro c₁ hc₁ c₂ hc₂ h12
    have m₁ := hrep c₁ hc₁
    have m₂ := hrep c₂ hc₂
    rw [h12] at m₁
    obtain ⟨y, hy, hyc⟩ := GlobalTheory.T.conj_unitary_of_same_hermitianMultiplicationModel E w hw K e (B₁.prod B₂) _ _ n _ _ m₁ m₂
    rw [← Quot.out_eq c₁, ← Quot.out_eq c₂]
    exact Quot.sound ⟨⟨y, hy⟩, Subtype.ext (by simpa [TwCl.rep] using hyc)⟩
  have hsupp : Function.support G ⊆ Φ '' S' := by
    intro κ hκ
    have hN : (B₁.prod B₂).N κ.rep ≠ 0 := by
      intro h0; apply hκ; simp [G, h0]
    have hfix : (B₁.prod B₂).σ (GlobalTheory.UnitLemma.InvAlg.Cl.rep κ) = GlobalTheory.UnitLemma.InvAlg.Cl.rep κ := (Quot.out κ).2
    have hunit : IsUnit (GlobalTheory.UnitLemma.InvAlg.Cl.rep κ) := (Quot.out κ).1.isUnit
    obtain ⟨γ, hγ, hmγ⟩ := GlobalTheory.T.exists_unitary_model_of_selfDualLatticeCount_ne_zero E w hw K e hBr n (Q₁ * Q₂) (B₁.prod B₂) _ _ hF hdeg hfix hunit hN
    have hcp : γ.val.charpoly = Q₁ * Q₂ := GlobalTheory.T.charpoly_eq_of_hermitianMultiplicationModel E w K e n (Q₁ * Q₂) (B₁.prod B₂) _ _ γ hmon hF hmγ
    let c : TwCl (MonoidHom.id (UL n w)) := Quot.mk _ ⟨γ, hγ⟩
    obtain ⟨g, hg'⟩ := hconj.symm
      (hconj.eqvGen_iff.1 (Quot.eqvGen_exact (Quot.out_eq c)))
    have hcrep : c.rep.1 = g.1⁻¹ * γ * g.1 := by
      have := congrArg Subtype.val hg'
      simpa [TwCl.rep] using this
    have hc : c ∈ S' := by
      show c.rep.1.val.charpoly = Q₁ * Q₂
      rw [hcrep, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj', hcp]
    refine ⟨c, hc, ?_⟩
    have m := hrep c hc
    rw [hcrep] at m
    obtain ⟨v, hv⟩ := GlobalTheory.T.hermitianModels_conj_unitary_differ_by_norm E w hw K e n (Q₁ * Q₂) (B₁.prod B₂) _ _ _ hsep hF γ g.1 g.2 hmγ m
    exact (Quot.out_eq (Φ c)).symm.trans ((Quot.sound (hcl.symm ⟨v, hv⟩)).trans (Quot.out_eq κ))
  calc _ = ∑ᶠ c, S'.indicator (fun c => G (Φ c)) c := finsum_congr fun c => by
          by_cases hc : c ∈ S'
          · rw [Set.indicator_of_mem hc, ← hterm c hc]
            exact if_pos hc
          · rw [Set.indicator_of_notMem hc]
            exact if_neg hc
    _ = ∑ᶠ c ∈ S', G (Φ c) := (finsum_mem_def _ _).symm
    _ = ∑ᶠ κ ∈ Φ '' S', G κ := (finsum_mem_image hinj).symm
    _ = ∑ᶠ κ, G κ := by
      exact (finsum_mem_inter_support_eq G (Φ '' S') Set.univ (by rw [Set.univ_inter, Set.inter_eq_right.2 hsupp])).trans
        (finsum_mem_univ G)

theorem kapOrb_congruence_eq_kapSum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → qV E w = K.q ^ 2 → ∀ (k : ℕ) (t : K.O), K.Small t → GlobalTheory.UnitLemma.val K.O (algebraMap K.O K.E t) = k → ∀ (n a b : ℕ) (Q₁ Q₂ : (w.adicCompletion E)[X]) (B₁ B₂ : GlobalTheory.UnitLemma.InvAlg K), a + b = n → Q₁.Monic → Q₂.Monic → Q₁.natDegree = a → Q₂.natDegree = b → (Q₁ * Q₂).Separable → IsCsr w Q₁ → IsCsr w Q₂ → Algebra.adjoin K.E {(1 + algebraMap K.O B₁.A t * B₁.g)} = ⊤ → aeval (1 + algebraMap K.O B₁.A t * B₁.g) (Q₁.map e.symm.toRingHom) = 0 → Module.finrank K.E B₁.A = Q₁.natDegree → (1 + algebraMap K.O B₁.A t * B₁.g) * B₁.σ (1 + algebraMap K.O B₁.A t * B₁.g) = 1 → Algebra.adjoin K.E {(1 + algebraMap K.O B₂.A t * B₂.g)} = ⊤ → aeval (1 + algebraMap K.O B₂.A t * B₂.g) (Q₂.map e.symm.toRingHom) = 0 → Module.finrank K.E B₂.A = Q₂.natDegree → (1 + algebraMap K.O B₂.A t * B₂.g) * B₂.σ (1 + algebraMap K.O B₂.A t * B₂.g) = 1 → kapOrb n w Q₁ Q₂ ((({γ : UL n w | γ.1 ∈ {g : GLw n w | g ∈ GlobalTheory.LFun.KGL w (n := n) ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))}} : Set (UL n w))).indicator 1) = ((GlobalTheory.UnitLemma.InvAlg.kapSum B₁ B₂ : ℚ) : ℂ) := by
  intro E _ _ _ hU w hw K e he1 he2 he3 he4 k t ht htk n a b Q₁ Q₂ B₁ B₂ hab hm₁ hm₂ hd₁ hd₂ hsep hc₁ hc₂
    hadj₁ hae₁ hfr₁ hu₁ hadj₂ hae₂ hfr₂ hu₂
  exact kapOrb_eq_kapSum_of_fits hw ⟨he1, he2, he3, he4⟩ ht htk hsep (hm₁.mul hm₂)
    (by rw [hm₁.natDegree_mul hm₂, hd₁, hd₂, hab]) ⟨hadj₁, hae₁, hfr₁, hu₁⟩ ⟨hadj₂, hae₂, hfr₂, hu₂⟩ (Prod.ext rfl rfl)

end GlobalTheory.KapLat
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaOrbitalIntegralCongruenceInertLatticeCountStatement

section

@[expose] public section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

theorem _root_.GlobalTheory.T.kappaOrbitalIntegral_congruence_inert_latticeCount : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → qV E w = K.q ^ 2 → ∀ (k : ℕ) (t : K.O), K.Small t → GlobalTheory.UnitLemma.val K.O (algebraMap K.O K.E t) = k → ∀ (n a b : ℕ) (Q₁ Q₂ : (w.adicCompletion E)[X]) (B₁ B₂ : GlobalTheory.UnitLemma.InvAlg K), a + b = n → Q₁.Monic → Q₂.Monic → Q₁.natDegree = a → Q₂.natDegree = b → (Q₁ * Q₂).Separable → IsCsr w Q₁ → IsCsr w Q₂ → Algebra.adjoin K.E {(1 + algebraMap K.O B₁.A t * B₁.g)} = ⊤ → aeval (1 + algebraMap K.O B₁.A t * B₁.g) (Q₁.map e.symm.toRingHom) = 0 → Module.finrank K.E B₁.A = Q₁.natDegree → (1 + algebraMap K.O B₁.A t * B₁.g) * B₁.σ (1 + algebraMap K.O B₁.A t * B₁.g) = 1 → Algebra.adjoin K.E {(1 + algebraMap K.O B₂.A t * B₂.g)} = ⊤ → aeval (1 + algebraMap K.O B₂.A t * B₂.g) (Q₂.map e.symm.toRingHom) = 0 → Module.finrank K.E B₂.A = Q₂.natDegree → (1 + algebraMap K.O B₂.A t * B₂.g) * B₂.σ (1 + algebraMap K.O B₂.A t * B₂.g) = 1 → kapOrb n w Q₁ Q₂ ((({γ : UL n w | γ.1 ∈ {g : GLw n w | g ∈ GlobalTheory.LFun.KGL w (n := n) ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))}} : Set (UL n w))).indicator 1) = ((GlobalTheory.UnitLemma.InvAlg.kapSum B₁ B₂ : ℚ) : ℂ) := by
  first | exact @GlobalTheory.KapLat.kapOrb_congruence_eq_kapSum | exact GlobalTheory.KapLat.kapOrb_congruence_eq_kapSum | (intros; apply GlobalTheory.KapLat.kapOrb_congruence_eq_kapSum <;> assumption)
end
end
