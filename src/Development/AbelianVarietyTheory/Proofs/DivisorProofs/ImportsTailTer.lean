module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicPlacesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemClosureRationalPointsUnitaryGroupStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemClosureSpecialUnitarySupportedAtPlaces
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialUnitaryFixingPlaneComplementMemClosureStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureDivMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiReflectionPairTruncationMemClosureStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncMemSUAdelic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumTwistByHeckeCharactersTrivialBase
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermForm
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryMatrixEqProdQuasiReflections
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryQuasiReflectionLaws
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemClosureSpecialUnitarySupportedAtPlacesStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct

theorem _root_.GlobalTheory.T.mem_closure_specialUnitarySupportedAtPlaces : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ g ∈ SUAdelic σ J, g ∈ closure {x : HA (AF F) σ J | ∃ (T₁ : Finset (InfinitePlace F)) (T₂ : Finset (HeightOneSpectrum (𝓞 F))) (η : AF F), IsPlacesIdem T₁ T₂ η ∧ x ∈ SUSupp σ J η} := by
  first | exact @GlobalTheory.SUTrunc.mem_closure_supp | exact GlobalTheory.SUTrunc.mem_closure_supp | (intros; apply GlobalTheory.SUTrunc.mem_closure_supp <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialUnitaryEqProdQuasiReflectionPairs

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.SUGenPairs

open GlobalTheory.UnRep Matrix

section Refl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {c : E ≃ₐ[F] E} {n : ℕ} {G : Matrix (Fin n) (Fin n) E}

theorem refl_conj {k : Matrix (Fin n) (Fin n) E} (hk : IsUnE c G k) (x : Fin n → E) (u : E) :
    k * refl c G x u = refl c G (k *ᵥ x) u * k := by
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun v => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    ReflLaws.refl_mulVec, ReflLaws.refl_mulVec, hk, hk, Matrix.mulVec_add, Matrix.mulVec_smul]

theorem refl_conj' {k : Matrix (Fin n) (Fin n) E} (hk : IsUnE c G k) (x : Fin n → E) (u : E)
    (X : Matrix (Fin n) (Fin n) E) : k * (refl c G x u * X) = refl c G (k *ᵥ x) u * (k * X) := by
  rw [← mul_assoc, refl_conj hk, mul_assoc]

theorem det_refl (x : Fin n → E) (u : E) (hx : hermE c G x x ≠ 0) : (refl c G x u).det = u := by
  rw [GlobalTheory.UnRep.refl, ← smul_vecMulVec, vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, dotProduct_smul,
    smul_eq_mul, ← ReflLaws.hermE_eq_dot, div_mul_cancel₀ _ hx]
  ring

theorem det_prod (l : List ((Fin n → E) × E)) (hl : ∀ p ∈ l, hermE c G p.1 p.1 ≠ 0) :
    (l.map fun p => refl c G p.1 p.2).prod.det = (l.map Prod.snd).prod := by
  induction l with
  | nil => simp
  | cons p l ih =>
    simp only [List.map_cons, List.prod_cons, Matrix.det_mul]
    rw [det_refl _ _ (hl p List.mem_cons_self), ih fun q hq => hl q (List.mem_cons_of_mem _ hq)]

theorem prod_conj {k : Matrix (Fin n) (Fin n) E} (hk : IsUnE c G k) (P : List ((Fin n → E) × (Fin n → E) × E)) :
    k * (P.map fun p => refl c G p.1 p.2.2 * refl c G p.2.1 (c p.2.2)).prod =
      ((P.map fun p => (k *ᵥ p.1, k *ᵥ p.2.1, p.2.2)).map
        fun p => refl c G p.1 p.2.2 * refl c G p.2.1 (c p.2.2)).prod * k := by
  induction P with
  | nil => simp
  | cons p P ih =>
    simp only [List.map_cons, List.prod_cons, mul_assoc, refl_conj' hk, ih]

theorem tele (hG : IsHermForm c G) (x₀ : Fin n → E) (h₀ : hermE c G x₀ x₀ ≠ 0) :
    ∀ l : List ((Fin n → E) × E), (∀ p ∈ l, hermE c G p.1 p.1 ≠ 0 ∧ p.2 * c p.2 = 1) →
    ∃ P : List ((Fin n → E) × (Fin n → E) × E),
      (∀ p ∈ P, hermE c G p.1 p.1 ≠ 0 ∧ hermE c G p.2.1 p.2.1 ≠ 0 ∧ p.2.2 * c p.2.2 = 1) ∧
      (l.map fun p => refl c G p.1 p.2).prod =
        (P.map fun p => refl c G p.1 p.2.2 * refl c G p.2.1 (c p.2.2)).prod * refl c G x₀ (l.map Prod.snd).prod := by
  have L := ReflLaws.refl_laws F E c n G hG x₀ h₀
  intro l
  induction l with
  | nil => intro _; exact ⟨[], by simp, by simp [L.2.1]⟩
  | cons q l ih =>
    intro hl
    obtain ⟨P, hP, e⟩ := ih fun p hp => hl p (List.mem_cons_of_mem _ hp)
    obtain ⟨hq1, hq2⟩ := hl q List.mem_cons_self
    have hk : IsUnE c G (refl c G x₀ q.2) := L.2.2.2 q.2 hq2
    refine ⟨(q.1, x₀, q.2) :: P.map (fun p => (refl c G x₀ q.2 *ᵥ p.1, refl c G x₀ q.2 *ᵥ p.2.1, p.2.2)), ?_, ?_⟩
    · intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact ⟨hq1, h₀, hq2⟩
      · obtain ⟨p', hp', rfl⟩ := List.mem_map.1 hp
        obtain ⟨a1, a2, a3⟩ := hP p' hp'
        exact ⟨by rw [hk]; exact a1, by rw [hk]; exact a2, a3⟩
    · have hcu : refl c G x₀ (c q.2) * refl c G x₀ q.2 = 1 := by
        rw [L.2.2.1, mul_comm, hq2, L.2.1]
      have hc := prod_conj hk P
      simp only [List.map_cons, List.prod_cons]
      rw [e, ← L.2.2.1 q.2]
      calc refl c G q.1 q.2 * ((P.map fun p => refl c G p.1 p.2.2 * refl c G p.2.1 (c p.2.2)).prod *
              refl c G x₀ (l.map Prod.snd).prod)
          = refl c G q.1 q.2 * ((refl c G x₀ (c q.2) * refl c G x₀ q.2) *
              (P.map fun p => refl c G p.1 p.2.2 * refl c G p.2.1 (c p.2.2)).prod) *
              refl c G x₀ (l.map Prod.snd).prod := by rw [hcu, one_mul, mul_assoc]
        _ = refl c G q.1 q.2 * refl c G x₀ (c q.2) * (refl c G x₀ q.2 *
              (P.map fun p => refl c G p.1 p.2.2 * refl c G p.2.1 (c p.2.2)).prod) *
              refl c G x₀ (l.map Prod.snd).prod := by simp only [mul_assoc]
        _ = _ := by rw [hc]; simp only [mul_assoc]

end Refl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem conjE_apply (hcm : IsCMExt F E σ) (x : E) : GlobalTheory.WeilTwistF.conjE hcm x = σ x := rfl

theorem hermE_transpose (hcm : IsCMExt F E σ) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    hermE (GlobalTheory.WeilTwistF.conjE hcm) Jᵀ x y = (fun b => σ (y b)) ⬝ᵥ J *ᵥ x := by
  simp only [hermE, conjE_apply, dotProduct, mulVec, transpose_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem hermE_eq_hE (hcm : IsCMExt F E σ) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    hermE (GlobalTheory.WeilTwistF.conjE hcm) Jᵀ x y = hE σ J y x := by
  rw [hermE_transpose]
  simp only [hE, Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc]
  rfl

theorem isUnE_of (hcm : IsCMExt F E σ) {n : ℕ} (J m : Matrix (Fin n) (Fin n) E) (h : (m.map σ)ᵀ * J * m = J) :
    IsUnE (GlobalTheory.WeilTwistF.conjE hcm) Jᵀ m := by
  have e1 : ∀ y : Fin n → E, (fun b => σ ((m *ᵥ y) b)) = m.map σ *ᵥ (fun b => σ (y b)) := fun y => by
    funext i

    simp [mulVec, dotProduct, map_sum, map_mul]
  intro x y
  have e : (fun b => σ ((m *ᵥ y) b)) ⬝ᵥ J *ᵥ (m *ᵥ x) = (fun b => σ (y b)) ⬝ᵥ ((m.map σ)ᵀ * J * m) *ᵥ x := by
    rw [e1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_transpose, dotProduct_comm,
      Matrix.dotProduct_mulVec, dotProduct_comm]
  rw [hermE_transpose, hermE_transpose, e, h]

theorem qr_eq_refl (hcm : IsCMExt F E σ) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E) (u : E) :
    GlobalTheory.SUAssemble.qr σ J x u = GlobalTheory.UnRep.refl (GlobalTheory.WeilTwistF.conjE hcm) Jᵀ x u := by
  rw [GlobalTheory.SUAssemble.qr, GlobalTheory.UnRep.refl, hermE_eq_hE, Matrix.mulVec_transpose]
  rfl

end GlobalTheory.SUGenPairs


open GlobalTheory.UnRep GlobalTheory.SUGenPairs in
theorem GlobalTheory.SUGenPairs.eq_prod_pairs : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ g ∈ Formalism.UG.UJ (σ : E →+* E) J, (g : Matrix (Fin M) (Fin M) E).det = 1 → ∃ l : List ((Fin M → E) × (Fin M → E) × E), (∀ p ∈ l, hE σ J p.1 p.1 ≠ 0 ∧ hE σ J p.2.1 p.2.1 ≠ 0 ∧ p.2.2 * σ p.2.2 = 1) ∧ (g : Matrix (Fin M) (Fin M) E) = (l.map fun p => GlobalTheory.SUAssemble.qr σ J p.1 p.2.2 * GlobalTheory.SUAssemble.qr σ J p.2.1 (σ p.2.2)).prod := by
  intro F E _ _ _ _ _ σ hcm M J hJ g hg hdet
  have hG : IsHermForm (GlobalTheory.WeilTwistF.conjE hcm) Jᵀ :=
    ⟨fun x => (GlobalTheory.WeilTwistF.conjE hcm).apply_symm_apply x, GlobalTheory.WeilTwistF.conjE_ne hcm, fun a b => hJ.1 a b,
      by rw [Matrix.det_transpose]; exact hJ.2⟩
  have hu : Formalism.UG.cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E) = J := hg
  obtain ⟨l, hl, hgl⟩ := GlobalTheory.UnRep.isUnE_eq_prod_refl F E _ M Jᵀ hG _ (isUnE_of hcm J _ hu)
  have hne : ∀ x : Fin M → E, hermE (GlobalTheory.WeilTwistF.conjE hcm) Jᵀ x x ≠ 0 → hE σ J x x ≠ 0 := fun x hx => by
    rwa [← hermE_eq_hE hcm]
  cases l with
  | nil => exact ⟨[], by simp, by simpa using hgl⟩
  | cons q l' =>
    obtain ⟨P, hP, e⟩ := tele hG q.1 (hl q List.mem_cons_self).1 (q :: l') hl
    have ha : ((q :: l').map Prod.snd).prod = 1 := by
      rw [← det_prod _ (fun p hp => (hl p hp).1), ← hgl, hdet]
    rw [ha, (ReflLaws.refl_laws F E _ M Jᵀ hG q.1 (hl q List.mem_cons_self).1).2.1, mul_one] at e
    refine ⟨P, fun p hp => ⟨hne _ (hP p hp).1, hne _ (hP p hp).2.1, (hP p hp).2.2⟩, ?_⟩
    rw [hgl, e]
    congr 2
    funext p
    rw [qr_eq_refl hcm, qr_eq_refl hcm]
    rfl
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialUnitaryEqProdQuasiReflectionPairsStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct

theorem _root_.GlobalTheory.T.specialUnitary_eq_prod_quasiReflectionPairs : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ g ∈ Formalism.UG.UJ (σ : E →+* E) J, (g : Matrix (Fin M) (Fin M) E).det = 1 → ∃ l : List ((Fin M → E) × (Fin M → E) × E), (∀ p ∈ l, hE σ J p.1 p.1 ≠ 0 ∧ hE σ J p.2.1 p.2.1 ≠ 0 ∧ p.2.2 * σ p.2.2 = 1) ∧ (g : Matrix (Fin M) (Fin M) E) = (l.map fun p => GlobalTheory.SUAssemble.qr σ J p.1 p.2.2 * GlobalTheory.SUAssemble.qr σ J p.2.1 (σ p.2.2)).prod := by
  first | exact @GlobalTheory.SUGenPairs.eq_prod_pairs | exact GlobalTheory.SUGenPairs.eq_prod_pairs | (intros; apply GlobalTheory.SUGenPairs.eq_prod_pairs <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncationSpecialUnitaryMemClosureStrongApprox

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct

namespace GlobalTheory.SUAssemble


open GlobalTheory.SUAssemble in
theorem assemble : (∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → ∀ e₁ e₂ : Fin M → E, hE σ J e₁ e₂ = 0 → hE σ J e₁ e₁ ≠ 0 → hE σ J e₂ e₂ ≠ 0 → (∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε * (t * sigR (AF F) σ t + inclR (AF F) (hE σ J e₁ e₁ / hE σ J e₂ e₂)) = 0) → ∀ g ∈ SUAdelic σ J, (∀ v : Fin M → E, hE σ J e₁ v = 0 → hE σ J e₂ v = 0 → Matrix.mulVec ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) (fun i => inclR (AF F) (v i)) = (fun i => inclR (AF F) (v i))) → g ∈ closure {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε, x = γ * h}) → (∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), 2 ≤ M → IsHermND σ J → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → ¬ IsCompact (SUSupp σ J ε) → ∃ (S₁' : Finset (InfinitePlace F)) (S₂' : Finset (HeightOneSpectrum (𝓞 F))) (ε' : AF F), S₁' ⊆ S₁ ∧ S₂' ⊆ S₂ ∧ (S₁'.Nonempty ∨ S₂'.Nonempty) ∧ IsPlacesIdem S₁' S₂' ε' ∧ ∀ x y : Fin M → E, hE σ J x x ≠ 0 → hE σ J y y ≠ 0 → ∃ z : Fin M → E, hE σ J z z ≠ 0 ∧ (hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x) ≠ 0 ∧ ∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε' * (t * sigR (AF F) σ t + inclR (AF F) (hE σ J x x / hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x))) = 0) ∧ (hE σ J (y - (hE σ J z y / hE σ J z z) • z) (y - (hE σ J z y / hE σ J z z) • z) ≠ 0 ∧ ∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε' * (t * sigR (AF F) σ t + inclR (AF F) (hE σ J z z / hE σ J (y - (hE σ J z y / hE σ J z z) • z) (y - (hE σ J z y / hE σ J z z) • z))) = 0)) → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), 2 ≤ M → IsHermND σ J → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → ¬ IsCompact (SUSupp σ J ε) → ∀ (T₁ : Finset (InfinitePlace F)) (T₂ : Finset (HeightOneSpectrum (𝓞 F))) (η : AF F), IsPlacesIdem T₁ T₂ η → ∀ γ ∈ SURat σ J, ∀ x : HA (AF F) σ J, (∀ i j, ((HA.mat (AF F) σ J x).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j = (1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j + algebraMap (AF F) (AF F ⊗[F] E) η * (((HA.mat (AF F) σ J γ).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) - 1) i j) → x ∈ closure {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε, x = γ * h} := by
  intro H1 H2 F E _ _ _ _ _ σ hcm M J hM hJ S₁ S₂ ε hε hnc T₁ T₂ η hη γ hγ x hx
  obtain ⟨S₁', S₂', ε', hs1, hs2, hne, hε', hz⟩ := H2 F E σ hcm M J hM hJ S₁ S₂ ε hε hnc
  have hηη : η * η = η := idem_sq hη
  have hεε : ε * ε' = ε' := idem_mul_of_sub hε hε' hs1 hs2
  set S := {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε, x = γ * h} with hS
  have hdiv := GlobalTheory.SUSuppSub.closure_div_mem F E σ hcm M J hJ S₁ S₂ ε hε
  have h1 : (1 : HA (AF F) σ J) ∈ closure S := subset_closure ⟨1, (SURat σ J).one_mem, 1,
    (GlobalTheory.SUSuppSub.mem_SUSupp_iff σ J).2 ⟨(SUAdelic σ J).one_mem, by
      rw [GlobalTheory.SUSuppSub.mv_one, sub_self, smul_zero]⟩, by simp⟩
  let Cg : Subgroup (HA (AF F) σ J) := Subgroup.ofDiv (closure S) ⟨1, h1⟩ hdiv
  have hmono : closure {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε', x = γ * h} ⊆ closure S :=
    closure_mono (by
      rintro _ ⟨g, hg, h, hh, rfl⟩
      exact ⟨g, hg, h, SUSupp_mono σ J hεε hh, rfl⟩)
  let K := Cg.comap (trunc σ J η hηη)
  have hlist : ∀ l : List ((Fin M → E) × (Fin M → E) × E),
      (∀ p ∈ l, hE σ J p.1 p.1 ≠ 0 ∧ hE σ J p.2.1 p.2.1 ≠ 0 ∧ p.2.2 * σ p.2.2 = 1) →
      ∃ p ∈ K, (p.1 : Matrix (Fin M) (Fin M) E) =
        (l.map fun p => qr σ J p.1 p.2.2 * qr σ J p.2.1 (σ p.2.2)).prod := by
    intro l
    induction l with
    | nil =>
      intro _
      exact ⟨1, K.one_mem, by simp⟩
    | cons q l ih =>
      intro hl
      obtain ⟨p₂, hp₂, e₂⟩ := ih (fun p hp => hl p (List.mem_cons_of_mem _ hp))
      obtain ⟨hx, hy, hu⟩ := hl q List.mem_cons_self
      obtain ⟨z, hzz, c1, c2⟩ := hz q.1 q.2.1 hx hy
      obtain ⟨p₁, e₁, hp₁⟩ := GlobalTheory.T.quasiReflectionPair_truncation_mem_closure H1 F E σ hcm M J hJ S₁' S₂' ε' hε' hne η hηη q.1 q.2.1 z q.2.2 hu hx hy
        hzz c1 c2
      refine ⟨p₁ * p₂, K.mul_mem (hmono hp₁) hp₂, ?_⟩
      rw [List.map_cons, List.prod_cons, ← e₁, ← e₂]
      rfl
  obtain ⟨hγa, hγr⟩ := hγ
  change HA.mat (AF F) σ J γ ∈ (Formalism.UG.UJ (σ : E →+* E) J).map (Formalism.UG.bc (inclR (AF F))) at hγr
  obtain ⟨g0, hg0, hg0e⟩ := Subgroup.mem_map.1 hγr
  have hmat : ((HA.mat (AF F) σ J γ).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) =
      RingHom.mapMatrix (inclR (AF F)) (g0 : Matrix (Fin M) (Fin M) E) := by
    rw [← hg0e]
    rfl
  have hdet : (g0 : Matrix (Fin M) (Fin M) E).det = 1 := by
    have h := StrongApprox.mem_SUAdelic.1 hγa
    rw [hmat, ← RingHom.map_det] at h
    haveI : Nontrivial (AF F) := inferInstanceAs (Nontrivial (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))
    have hinj : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
      Algebra.TensorProduct.includeRight_injective (algebraMap F (AF F)).injective
    exact hinj (h.trans (map_one _).symm)
  obtain ⟨l, hl, hle⟩ := GlobalTheory.T.specialUnitary_eq_prod_quasiReflectionPairs F E σ hcm M J hJ g0 hg0 hdet
  obtain ⟨p, hp, hpe⟩ := hlist l hl
  have hpg : p = ⟨g0, hg0⟩ := Subtype.ext (Units.ext (hpe.trans hle.symm))
  have hxe : x = trunc σ J η hηη ⟨g0, hg0⟩ := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    refine (hx i j).trans ?_
    change _ = (1 + algebraMap (AF F) (AF F ⊗[F] E) η • (rmat (F := F) g0 - 1)) i j
    rw [hmat]
    simp [rmat]
  rw [hxe, ← hpg]
  exact hp

end GlobalTheory.SUAssemble

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncationSpecialUnitaryMemClosureStrongApproxStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct

theorem _root_.GlobalTheory.T.truncation_specialUnitary_mem_closure_strongApprox : (∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → ∀ e₁ e₂ : Fin M → E, hE σ J e₁ e₂ = 0 → hE σ J e₁ e₁ ≠ 0 → hE σ J e₂ e₂ ≠ 0 → (∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε * (t * sigR (AF F) σ t + inclR (AF F) (hE σ J e₁ e₁ / hE σ J e₂ e₂)) = 0) → ∀ g ∈ SUAdelic σ J, (∀ v : Fin M → E, hE σ J e₁ v = 0 → hE σ J e₂ v = 0 → Matrix.mulVec ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) (fun i => inclR (AF F) (v i)) = (fun i => inclR (AF F) (v i))) → g ∈ closure {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε, x = γ * h}) → (∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), 2 ≤ M → IsHermND σ J → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → ¬ IsCompact (SUSupp σ J ε) → ∃ (S₁' : Finset (InfinitePlace F)) (S₂' : Finset (HeightOneSpectrum (𝓞 F))) (ε' : AF F), S₁' ⊆ S₁ ∧ S₂' ⊆ S₂ ∧ (S₁'.Nonempty ∨ S₂'.Nonempty) ∧ IsPlacesIdem S₁' S₂' ε' ∧ ∀ x y : Fin M → E, hE σ J x x ≠ 0 → hE σ J y y ≠ 0 → ∃ z : Fin M → E, hE σ J z z ≠ 0 ∧ (hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x) ≠ 0 ∧ ∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε' * (t * sigR (AF F) σ t + inclR (AF F) (hE σ J x x / hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x))) = 0) ∧ (hE σ J (y - (hE σ J z y / hE σ J z z) • z) (y - (hE σ J z y / hE σ J z z) • z) ≠ 0 ∧ ∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε' * (t * sigR (AF F) σ t + inclR (AF F) (hE σ J z z / hE σ J (y - (hE σ J z y / hE σ J z z) • z) (y - (hE σ J z y / hE σ J z z) • z))) = 0)) → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), 2 ≤ M → IsHermND σ J → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → ¬ IsCompact (SUSupp σ J ε) → ∀ (T₁ : Finset (InfinitePlace F)) (T₂ : Finset (HeightOneSpectrum (𝓞 F))) (η : AF F), IsPlacesIdem T₁ T₂ η → ∀ γ ∈ SURat σ J, ∀ x : HA (AF F) σ J, (∀ i j, ((HA.mat (AF F) σ J x).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j = (1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j + algebraMap (AF F) (AF F ⊗[F] E) η * (((HA.mat (AF F) σ J γ).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) - 1) i j) → x ∈ closure {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε, x = γ * h} := by
  first | exact @GlobalTheory.SUAssemble.assemble | exact GlobalTheory.SUAssemble.assemble | (intros; apply GlobalTheory.SUAssemble.assemble <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsTailTer

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct

namespace GlobalTheory.StrongApproxSUProof

theorem strongApproxSU : StrongApproxSU := by
  intro F E _ _ _ _ _ σ hcm M J hM hJ S₁ S₂ ε hε hnc g hg
  have h3 := GlobalTheory.T.truncation_specialUnitary_mem_closure_strongApprox GlobalTheory.T.specialUnitary_fixing_plane_complement_mem_closure GlobalTheory.T.exists_isotropic_places_alt F E σ hcm M J hM hJ S₁ S₂ ε hε hnc
  refine closure_minimal ?_ isClosed_closure (GlobalTheory.T.mem_closure_specialUnitarySupportedAtPlaces F E σ hcm M J hJ g hg)
  rintro x ⟨T₁, T₂, η, hη, hx⟩
  refine closure_minimal ?_ isClosed_closure (GlobalTheory.T.mem_closure_rational_points_unitary_group F E σ hcm M J hJ T₁ T₂ η hη x hx)
  rintro y ⟨γ, hγ, hy⟩
  exact h3 T₁ T₂ η hη γ hγ y hy

end GlobalTheory.StrongApproxSUProof
end
end
