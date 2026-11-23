module

public import Mathlib.NumberTheory.Padics.Complex
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KbIsAlgClosedAndConj
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
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Invariant.Profinite
import Mathlib.RingTheory.PicardGroup
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
public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
public import Mathlib.RingTheory.Invariant.Defs
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.Style
import Mathlib.Topology.Sheaves.Init

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgEquivLiftResiduePadicAlgCl

section

@[expose] public section

open IsLocalRing

namespace GlobalTheory.ZJ

theorem exists_algEquiv_lift_residue (l : ℕ) [Fact l.Prime] (L : IntermediateField ℚ_[l] (PadicAlgCl l))
    (φ : kb l ≃+* kb l)
    (hφ : ∀ x : OO l, (x : PadicAlgCl l) ∈ L → φ (residue (OO l) x) = residue (OO l) x) :
    ∃ g : PadicAlgCl l ≃ₐ[L] PadicAlgCl l, ∀ x y : OO l,
      residue (OO l) y = φ (residue (OO l) x) → ‖g (x : PadicAlgCl l) - y‖ < 1 := by
  classical
  haveI : IsAlgClosure L (PadicAlgCl l) :=
    ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ_[l]) L⟩
  haveI : IsGalois L (PadicAlgCl l) := {}
  have hmem : ∀ (g : PadicAlgCl l ≃ₐ[L] PadicAlgCl l) {x : PadicAlgCl l}, x ∈ OO l → g x ∈ OO l :=
    fun g _ hx => algEquiv_mem_OO (g.restrictScalars ℚ_[l]) hx
  letI : MulSemiringAction (PadicAlgCl l ≃ₐ[L] PadicAlgCl l) (OO l) :=
    { smul := fun g x => ⟨g x, hmem g x.2⟩
      one_smul := fun _ => Subtype.ext rfl
      mul_smul := fun _ _ _ => Subtype.ext rfl
      smul_zero := fun g => Subtype.ext (map_zero g)
      smul_add := fun g _ _ => Subtype.ext (map_add g _ _)
      smul_one := fun g => Subtype.ext (map_one g)
      smul_mul := fun g _ _ => Subtype.ext (map_mul g _ _) }
  have hsmul : ∀ (g : PadicAlgCl l ≃ₐ[L] PadicAlgCl l) (x : OO l),
      ((g • x : OO l) : PadicAlgCl l) = g x := fun _ _ => rfl
  let A : Subring (OO l) := L.toSubalgebra.toSubring.comap (OO l).subtype
  have hA : ∀ a : A, (((a : OO l) : PadicAlgCl l)) ∈ L := fun a => a.2
  haveI : SMulCommClass (PadicAlgCl l ≃ₐ[L] PadicAlgCl l) A (OO l) := ⟨fun g a b => by
    apply Subtype.ext
    change g (((a : OO l) : PadicAlgCl l) * b) = ((a : OO l) : PadicAlgCl l) * g b
    rw [map_mul]
    congr 1
    exact g.commutes (⟨_, hA a⟩ : L)⟩
  letI : TopologicalSpace (OO l) := ⊥
  haveI : DiscreteTopology (OO l) := ⟨rfl⟩
  haveI : ContinuousSMul (PadicAlgCl l ≃ₐ[L] PadicAlgCl l) (OO l) := by
    rw [continuousSMul_iff_stabilizer_isOpen]
    intro x
    have := stabilizer_isOpen_of_isIntegral (K := L) (x : PadicAlgCl l)
    convert this using 1
    ext g
    simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    exact Subtype.ext_iff
  haveI : Algebra.IsInvariant A (OO l) (PadicAlgCl l ≃ₐ[L] PadicAlgCl l) := by
    constructor
    intro b hb
    obtain ⟨k, hk⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := L) (b : PadicAlgCl l)).2
      fun g => congrArg Subtype.val (hb g)
    have hbL : (b : PadicAlgCl l) ∈ L := hk ▸ k.2
    exact ⟨⟨b, hbL⟩, rfl⟩
  set Q := maximalIdeal (OO l) with hQ
  let φ' : ((OO l) ⧸ Q) ≃ₐ[A ⧸ Q.under A] ((OO l) ⧸ Q) :=
    AlgEquiv.ofRingEquiv (f := (φ : ((OO l) ⧸ Q) ≃+* ((OO l) ⧸ Q))) (by
      intro x
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact hφ (a : OO l) (hA a))
  obtain ⟨⟨σ, hσQ⟩, hσ⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite
    (G := PadicAlgCl l ≃ₐ[L] PadicAlgCl l) (Q.under A) Q φ'
  refine ⟨σ, fun x y hxy => ?_⟩
  have h1 : Ideal.Quotient.mk Q (σ • x) = φ (residue (OO l) x) :=
    DFunLike.congr_fun hσ (Ideal.Quotient.mk Q x)
  have h2 : residue (OO l) (σ • x - y) = 0 := by
    rw [map_sub, hxy]
    exact sub_eq_zero.2 h1
  have h3 : ¬ IsUnit (σ • x - y) := by
    rw [residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff] at h2
    exact h2
  have h4 := (GlobalTheory.ZH.not_isUnit_OO_iff _).1 h3
  simpa [hsmul] using h4

end GlobalTheory.ZJ
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgEquivLiftResiduePadicAlgClStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.exists_algEquiv_lift_residue_padicAlgCl : ∀ (l : ℕ) [Fact l.Prime] (L : IntermediateField ℚ_[l] (PadicAlgCl l)) (φ : GlobalTheory.ZJ.kb l ≃+* GlobalTheory.ZJ.kb l), (∀ x : GlobalTheory.ZJ.OO l, (x : PadicAlgCl l) ∈ L → φ (IsLocalRing.residue (GlobalTheory.ZJ.OO l) x) = IsLocalRing.residue (GlobalTheory.ZJ.OO l) x) → ∃ g : PadicAlgCl l ≃ₐ[L] PadicAlgCl l, ∀ x y : GlobalTheory.ZJ.OO l, IsLocalRing.residue (GlobalTheory.ZJ.OO l) y = φ (IsLocalRing.residue (GlobalTheory.ZJ.OO l) x) → ‖g (x : PadicAlgCl l) - y‖ < 1 := by
  first | exact @GlobalTheory.ZJ.exists_algEquiv_lift_residue | exact GlobalTheory.ZJ.exists_algEquiv_lift_residue | (intros; apply GlobalTheory.ZJ.exists_algEquiv_lift_residue <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingEquivExtendingOfKerLe

section

@[expose] public section

namespace GlobalTheory

def FieldCopy (k : Type) : Type := k

instance FieldCopy.instField (k : Type) [h : Field k] : Field (FieldCopy k) := h

instance FieldCopy.instIsAlgClosed (k : Type) [Field k] [h : IsAlgClosed k] :
    IsAlgClosed (FieldCopy k) := h

theorem exists_ringEquiv_extending_of_ker_le :
    ∀ (k : Type) [Field k] [IsAlgClosed k], (∀ x : k, x ≠ 0 → ∃ n : ℕ, 1 ≤ n ∧ x ^ n = 1) →
      ∀ (R : Subring k) (J : Type) (α β : J → k),
        (∀ p : MvPolynomial J R, MvPolynomial.aeval α p = 0 → MvPolynomial.aeval β p = 0) →
        ∃ φ : k ≃+* k, (∀ r ∈ R, φ r = r) ∧ ∀ j, φ (α j) = β j := by
  intro k _ _ hroot R J α β hker
  let eα : MvPolynomial J R →ₐ[R] k := MvPolynomial.aeval α
  let eβ : MvPolynomial J R →ₐ[R] k := MvPolynomial.aeval β
  let S : Subalgebra R k := eα.range
  have hle : ∀ p ∈ RingHom.ker eα.rangeRestrict, eβ p = 0 := by
    intro p hp
    rw [RingHom.mem_ker] at hp
    apply hker
    have := congrArg Subtype.val hp
    simpa using this
  let ψ0 : S →ₐ[R] k := (Ideal.Quotient.liftₐ (RingHom.ker eα.rangeRestrict) eβ hle).comp
    (Ideal.quotientKerAlgEquivOfSurjective (AlgHom.rangeRestrict_surjective eα)).symm.toAlgHom
  have hψ0 : ∀ p, ψ0 (eα.rangeRestrict p) = eβ p := by
    intro p
    have h1 : (Ideal.quotientKerAlgEquivOfSurjective (AlgHom.rangeRestrict_surjective eα)).symm
        (eα.rangeRestrict p) = Ideal.Quotient.mk _ p := by
      rw [AlgEquiv.symm_apply_eq]
      rfl
    simp only [ψ0, AlgHom.comp_apply]
    erw [h1]
    rfl
  let ψ : S →+* FieldCopy k := ψ0.toRingHom
  have hψinj : Function.Injective ψ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro s hs
    by_contra hne
    have hne' : (s : k) ≠ 0 := fun h => hne (Subtype.ext h)
    obtain ⟨n, hn, hsn⟩ := hroot _ hne'
    have hsn' : s ^ n = 1 := Subtype.ext (by simpa using hsn)
    have : ψ s ^ n = 1 := by rw [← map_pow, hsn', map_one]
    rw [hs, zero_pow (by omega)] at this
    exact zero_ne_one this
  letI : Algebra S (FieldCopy k) := ψ.toAlgebra
  haveI : Module.IsTorsionFree S (FieldCopy k) := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r m h => ?_
    rw [Algebra.smul_def, mul_eq_zero] at h
    rcases h with h | h
    · left
      exact hψinj (h.trans (map_zero ψ).symm)
    · exact Or.inr h
  haveI : Algebra.IsIntegral S k := by
    constructor
    intro x
    by_cases hx : x = 0
    · rw [hx]; exact isIntegral_zero
    · obtain ⟨n, hn, hxn⟩ := hroot x hx
      refine ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 (by omega), ?_⟩
      simp [hxn]
  let θ' : k →ₐ[S] FieldCopy k := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let θ : k →+* k := θ'.toRingHom
  have hθS : ∀ s : S, θ (s : k) = ψ0 s := by
    intro s
    have := θ'.commutes s
    exact this
  have hθinj : Function.Injective θ := θ.injective
  have hθsurj : Function.Surjective θ := by
    intro y
    by_cases hy : y = 0
    · exact ⟨0, by rw [hy, map_zero]⟩
    obtain ⟨n, hn, hyn⟩ := hroot y hy
    let T := Polynomial.nthRootsFinset n (1 : k)
    have hmem : ∀ x : k, x ∈ T ↔ x ^ n = 1 := fun x => Polynomial.mem_nthRootsFinset (by omega) 1
    let f : T → T := fun t => ⟨θ t, (hmem _).2 (by rw [← map_pow, (hmem _).1 t.2, map_one])⟩
    have hf : Function.Injective f := by
      intro a b hab
      exact Subtype.ext (hθinj (congrArg Subtype.val hab))
    obtain ⟨t, ht⟩ := Finite.injective_iff_surjective.1 hf ⟨y, (hmem y).2 hyn⟩
    exact ⟨t, congrArg Subtype.val ht⟩
  refine ⟨RingEquiv.ofBijective θ ⟨hθinj, hθsurj⟩, ?_, ?_⟩
  · intro r hr
    have hrS : (r : k) ∈ S := ⟨MvPolynomial.C ⟨r, hr⟩, by simp [eα]; rfl⟩
    show θ r = r
    have h2 : (⟨r, hrS⟩ : S) = eα.rangeRestrict (MvPolynomial.C ⟨r, hr⟩) :=
      Subtype.ext (by simp [eα]; rfl)
    rw [show r = ((⟨r, hrS⟩ : S) : k) from rfl, hθS, h2, hψ0]
    simp [eβ]
  · intro j
    show θ (α j) = β j
    have h2 : (⟨α j, ⟨MvPolynomial.X j, by simp [eα]⟩⟩ : S) = eα.rangeRestrict (MvPolynomial.X j) :=
      Subtype.ext (by simp [eα])
    rw [show α j = ((⟨α j, ⟨MvPolynomial.X j, by simp [eα]⟩⟩ : S) : k) from rfl, hθS, h2, hψ0]
    simp [eβ]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingEquivExtendingOfKerLeStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.exists_ringEquiv_extending_of_ker_le' : ∀ (k : Type) [Field k] [IsAlgClosed k], (∀ x : k, x ≠ 0 → ∃ n : ℕ, 1 ≤ n ∧ x ^ n = 1) → ∀ (R : Subring k) (J : Type) (α β : J → k), (∀ p : MvPolynomial J R, MvPolynomial.aeval α p = 0 → MvPolynomial.aeval β p = 0) → ∃ φ : k ≃+* k, (∀ r ∈ R, φ r = r) ∧ ∀ j, φ (α j) = β j := by
  first | exact @GlobalTheory.exists_ringEquiv_extending_of_ker_le | exact GlobalTheory.exists_ringEquiv_extending_of_ker_le | (intros; apply GlobalTheory.exists_ringEquiv_extending_of_ker_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisLiftResidueCongruencePadic

section

@[expose] public section

namespace GlobalTheory.ResidueLift

open IsLocalRing

theorem res_eq_zero_iff {l : ℕ} [Fact l.Prime] (x : GlobalTheory.ZJ.OO l) :
    residue (GlobalTheory.ZJ.OO l) x = 0 ↔ ‖(x : PadicAlgCl l)‖ < 1 := by
  rw [residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff, GlobalTheory.ZH.not_isUnit_OO_iff]

theorem main : ∀ (l : ℕ) [Fact l.Prime] (L : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] L] (J : Type) (a b : J → PadicAlgCl l), (∀ j, ‖a j‖ ≤ 1) → (∀ j, ‖b j‖ ≤ 1) → (∀ p : MvPolynomial J (PadicAlgCl l), (∀ n, p.coeff n ∈ L ∧ ‖p.coeff n‖ ≤ 1) → (‖MvPolynomial.eval a p‖ < 1 ↔ ‖MvPolynomial.eval b p‖ < 1)) → ∃ g : PadicAlgCl l ≃ₐ[L] PadicAlgCl l, ∀ j, ‖g (a j) - b j‖ < 1 := by
  intro l _ L _ J a b ha hb hab
  let K := PadicAlgCl l
  let O := GlobalTheory.ZJ.OO l
  let a' : J → O := fun j => ⟨a j, (GlobalTheory.ZH.mem_OO_iff _).2 (ha j)⟩
  let b' : J → O := fun j => ⟨b j, (GlobalTheory.ZH.mem_OO_iff _).2 (hb j)⟩
  let As : Subring O := L.toSubalgebra.toSubring.comap O.subtype
  let f : As →+* GlobalTheory.ZJ.kb l := (residue O).comp As.subtype
  let R := f.range
  have key : ∀ (c : J → O) (q : MvPolynomial J As),
      MvPolynomial.aeval (fun j => residue O (c j)) (MvPolynomial.map f.rangeRestrict q) = 0 ↔
      ‖MvPolynomial.eval (fun j => (c j : K)) (MvPolynomial.map (O.subtype.comp As.subtype) q)‖ < 1 := by
    intro c q
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map, MvPolynomial.eval_map]
    have h1 : MvPolynomial.eval₂ ((algebraMap R (GlobalTheory.ZJ.kb l)).comp f.rangeRestrict) (fun j => residue O (c j)) q
        = residue O (MvPolynomial.eval₂ As.subtype c q) := by
      rw [MvPolynomial.eval₂_comp_left]; rfl
    have h2 : MvPolynomial.eval₂ (O.subtype.comp As.subtype) (fun j => (c j : K)) q
        = ((MvPolynomial.eval₂ As.subtype c q : O) : K) :=
      (MvPolynomial.eval₂_comp_left O.subtype As.subtype c q).symm
    rw [h1, h2, res_eq_zero_iff]
  have hII : ∀ p : MvPolynomial J R, MvPolynomial.aeval (fun j => residue O (a' j)) p = 0 →
      MvPolynomial.aeval (fun j => residue O (b' j)) p = 0 := by
    intro p hp
    obtain ⟨q, rfl⟩ := MvPolynomial.map_surjective f.rangeRestrict f.rangeRestrict_surjective p
    rw [key] at hp ⊢
    refine (hab _ fun n => ?_).1 hp
    rw [MvPolynomial.coeff_map]
    exact ⟨(AddMonoidAlgebra.coeff q n).2, (GlobalTheory.ZH.mem_OO_iff _).1 (((AddMonoidAlgebra.coeff q n : As) : O).2)⟩
  haveI := GlobalTheory.ZJ.isAlgClosed_kb (p := l)
  obtain ⟨φ, hφR, hφ⟩ := GlobalTheory.T.exists_ringEquiv_extending_of_ker_le' _ GlobalTheory.ZJ.exists_pow_eq_one_kb R J _ _ hII
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_algEquiv_lift_residue_padicAlgCl l L φ fun x hx => hφR _ ⟨⟨x, hx⟩, rfl⟩
  exact ⟨g, fun j => hg (a' j) (b' j) (hφ j).symm⟩

end GlobalTheory.ResidueLift
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisLiftResidueCongruencePadicStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.exists_galois_lift_residue_congruence_padic : ∀ (l : ℕ) [Fact l.Prime] (L : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] L] (J : Type) (a b : J → PadicAlgCl l), (∀ j, ‖a j‖ ≤ 1) → (∀ j, ‖b j‖ ≤ 1) → (∀ p : MvPolynomial J (PadicAlgCl l), (∀ n, p.coeff n ∈ L ∧ ‖p.coeff n‖ ≤ 1) → (‖MvPolynomial.eval a p‖ < 1 ↔ ‖MvPolynomial.eval b p‖ < 1)) → ∃ g : PadicAlgCl l ≃ₐ[L] PadicAlgCl l, ∀ j, ‖g (a j) - b j‖ < 1 := by
  first | exact @GlobalTheory.ResidueLift.main | exact GlobalTheory.ResidueLift.main | (intros; apply GlobalTheory.ResidueLift.main <;> assumption)
end
end
