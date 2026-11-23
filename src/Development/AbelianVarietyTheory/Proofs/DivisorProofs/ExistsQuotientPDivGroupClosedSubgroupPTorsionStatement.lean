module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
public import Mathlib.RingTheory.Bialgebra.Hom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BialgHomFactorThroughSplitInjection
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRetractionMulP
import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsCounitDerivationCounitComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotPDivGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientFiniteCommGroupSchemeClosedSubgrouStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRetractionMulP
public import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.FibreRankCompOfSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonOfResidueFieldFibres
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.HaveILetI
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.BialgHomFactorThroughSplitInjectionStatement

section

@[expose] public section

open CategoryTheory Coalgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.HTPair
open scoped TensorProduct

theorem _root_.GlobalTheory.T.bialgHom_factor_through_split_injection : ∀ (O : Type) [CommRing O] (A B D : Type) [CommRing A] [CommRing B] [CommRing D] [Bialgebra O A] [Bialgebra O B] [Bialgebra O D] (j : B →ₐc[O] A) (ρ : A →ₗ[O] B) (f : D →ₐc[O] A), (∀ b, ρ (j b) = b) → (∀ d, f d ∈ Set.range j) → ∃ g : D →ₐc[O] B, ∀ d, j (g d) = f d := by
  first | exact @GlobalTheory.bialgHom_factor_through_split | exact GlobalTheory.bialgHom_factor_through_split | (intros; apply GlobalTheory.bialgHom_factor_through_split <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivSubgroupQuotientTowerRSEqSRes

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Coalgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.HTPair
open scoped TensorProduct

namespace GlobalTheory.HTPair.QuotIsog

variable {p : ℕ} {O : Type} [CommRing O] {G H : PDivGroup p O} (τ : QuotTower G)

theorem j_injective (m : ℕ) : Function.Injective (τ.j m) := fun a b h => by
  rw [← τ.ρ_j m a, ← τ.ρ_j m b, h]

theorem pDivSubgroupQuotientTower_r_s_eq_s_res (m : ℕ) (a : G.A (m + 1)) : τ.r m (τ.s (m + 1) a) = τ.s m (G.res m a) := by
  apply j_injective τ m
  rw [τ.j_r, τ.j_s, τ.j_s, G.res_mulP, G.mulP_res]

theorem s_res_j (m : ℕ) (b : τ.B m) : τ.s m (G.res m (τ.j m b)) = mulBy O _ p b := by
  apply j_injective τ m
  rw [τ.j_s, G.mulP_res, map_mulBy]

theorem ker_le (m : ℕ) : torsionIdeal (R := O) (A := τ.B m) (p ^ m) ≤
    RingHom.ker (((G.res m).comp (τ.j m) : τ.B m →ₐc[O] G.A m) : τ.B m →ₐ[O] G.A m) := by
  refine (kerIdeal_le_ker_iff _ _).2 fun c => ?_
  change ((G.res m).comp (τ.j m)) (mulBy O _ (p ^ m) c) = _
  rw [map_mulBy, G.mulBy_pow_self, CoalgHomClass.counit_comp_apply]

variable [Fact p.Prime]

def toQuot (q : ∀ m, τ.B m →ₐc[O] H.A m) (hs : ∀ m, Function.Surjective (q m))
    (hk : ∀ m, RingHom.ker (q m) = torsionIdeal (R := O) (A := τ.B m) (p ^ m))
    (hc : ∀ m b, H.res m (q (m + 1) b) = q m (τ.r m b)) : G ⟶ H where
  app m := liftSurj (q m) (hs m) ((G.res m).comp (τ.j m)) ((hk m).le.trans (ker_le τ m))
  comm n := BialgHom.ext fun c => by
    obtain ⟨b, rfl⟩ := hs (n + 1) c
    rw [BialgHom.comp_apply, BialgHom.comp_apply, hc, liftSurj_apply, liftSurj_apply,
      BialgHom.comp_apply, BialgHom.comp_apply, ← τ.j_r]

theorem toQuot_app_q (q : ∀ m, τ.B m →ₐc[O] H.A m) (hs : ∀ m, Function.Surjective (q m))
    (hk : ∀ m, RingHom.ker (q m) = torsionIdeal (R := O) (A := τ.B m) (p ^ m))
    (hc : ∀ m b, H.res m (q (m + 1) b) = q m (τ.r m b)) (m : ℕ) (b : τ.B m) :
    (toQuot τ q hs hk hc).app m (q m b) = G.res m (τ.j m b) :=
  liftSurj_apply ..

def fromQuot (q : ∀ m, τ.B m →ₐc[O] H.A m)
    (hc : ∀ m b, H.res m (q (m + 1) b) = q m (τ.r m b)) : H ⟶ G where
  app m := (q m).comp (τ.s m)
  comm n := BialgHom.ext fun a => by
    change H.res n (q (n + 1) (τ.s (n + 1) a)) = q n (τ.s n (G.res n a))
    rw [hc, pDivSubgroupQuotientTower_r_s_eq_s_res]

end GlobalTheory.HTPair.QuotIsog
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientTransitionSurjectiveSameSubgroup

section

@[expose] public section

open CategoryTheory Coalgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.HTPair
open scoped TensorProduct

namespace GlobalTheory.QuotTransition

theorem transition_surjective : ∀ (O : Type) [CommRing O] (A₁ : Type) [CommRing A₁] [HopfAlgebra O A₁] [IsCocomm O A₁] [Module.Finite O A₁] [Module.Projective O A₁] (A₂ : Type) [CommRing A₂] [HopfAlgebra O A₂] [IsCocomm O A₂] [Module.Finite O A₂] [Module.Projective O A₂] (B₁ : Type) [CommRing B₁] [HopfAlgebra O B₁] [IsCocomm O B₁] [Module.Finite O B₁] [Module.Projective O B₁] (B₂ : Type) [CommRing B₂] [HopfAlgebra O B₂] [IsCocomm O B₂] [Module.Finite O B₂] [Module.Projective O B₂] (π : A₂ →ₐc[O] A₁) (j₁ : B₁ →ₐc[O] A₁) (j₂ : B₂ →ₐc[O] A₂) (r : B₂ →ₐc[O] B₁) (ρ : A₁ →ₗ[O] B₁), (∀ b, ρ (j₁ b) = b) → (∀ b, j₁ (r b) = π (j₂ b)) → kerIdeal j₁ = Ideal.map (π : A₂ →ₐ[O] A₁) (kerIdeal j₂) → Function.Surjective r := by
  intro O _ A₁ _ _ _ _ _ A₂ _ _ _ _ _ B₁ _ _ _ _ _ B₂ _ _ _ _ _ π j₁ j₂ r ρ hρ hsq hker
  let j₁' : B₁ →ₗ[O] A₁ := (j₁ : B₁ →ₐ[O] A₁).toLinearMap
  let r' : B₂ →ₗ[O] B₁ := (r : B₂ →ₐ[O] B₁).toLinearMap
  have hcomp : j₁' ∘ₗ r' = ((π.comp j₂ : B₂ →ₐc[O] A₁) : B₂ →ₐ[O] A₁).toLinearMap := by
    ext b
    exact hsq b
  have hs : Function.Surjective r' := by
    refine GlobalTheory.surjective_of_fibre_rank O B₂ B₁ r' fun q => ?_
    have hinj : Function.Injective (j₁'.baseChange q.asIdeal.ResidueField) := by
      apply Function.LeftInverse.injective (g := ρ.baseChange q.asIdeal.ResidueField)
      intro x
      rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
      have hid : ρ ∘ₗ j₁' = LinearMap.id := LinearMap.ext hρ
      rw [hid, LinearMap.baseChange_id, LinearMap.id_apply]
    have h1 : fibreRank (j₁' ∘ₗ r') q = fibreRank r' q := by
      rw [fibreRank, fibreRank, LinearMap.baseChange_comp, LinearMap.range_comp]
      exact (Submodule.equivMapOfInjective _ hinj _).finrank_eq.symm
    have h2 : fibreRank j₁' q = fibreDim B₁ q := LinearMap.finrank_range_of_inj hinj
    have h3 := fibreDim_eq_ker_mul_range (π.comp j₂) q
    have h4 := fibreDim_eq_ker_mul_range j₁ q
    rw [kerIdeal_comp, ← hker, ← hcomp] at h3
    have h5 : fibreDim (A₁ ⧸ kerIdeal j₁) q ≠ 0 := fun h0 =>
      fibreDim_ne_zero (A := A₁) q (by rw [h4, h0, zero_mul])
    have h6 : fibreRank (j₁' ∘ₗ r') q = fibreRank j₁' q :=
      Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero h5) (h3.symm.trans h4)
    have h7 : fibreRank r' q = fibreDim B₁ q := by rw [← h1, h6, h2]
    exact h7
  exact hs

end GlobalTheory.QuotTransition
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientTransitionSurjectiveSameSubgroupStatement

section

@[expose] public section

open CategoryTheory Coalgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.HTPair
open scoped TensorProduct

theorem _root_.GlobalTheory.T.quotientTransition_surjective_same_subgroup : ∀ (O : Type) [CommRing O] (A₁ : Type) [CommRing A₁] [HopfAlgebra O A₁] [IsCocomm O A₁] [Module.Finite O A₁] [Module.Projective O A₁] (A₂ : Type) [CommRing A₂] [HopfAlgebra O A₂] [IsCocomm O A₂] [Module.Finite O A₂] [Module.Projective O A₂] (B₁ : Type) [CommRing B₁] [HopfAlgebra O B₁] [IsCocomm O B₁] [Module.Finite O B₁] [Module.Projective O B₁] (B₂ : Type) [CommRing B₂] [HopfAlgebra O B₂] [IsCocomm O B₂] [Module.Finite O B₂] [Module.Projective O B₂] (π : A₂ →ₐc[O] A₁) (j₁ : B₁ →ₐc[O] A₁) (j₂ : B₂ →ₐc[O] A₂) (r : B₂ →ₐc[O] B₁) (ρ : A₁ →ₗ[O] B₁), (∀ b, ρ (j₁ b) = b) → (∀ b, j₁ (r b) = π (j₂ b)) → kerIdeal j₁ = Ideal.map (π : A₂ →ₐ[O] A₁) (kerIdeal j₂) → Function.Surjective r := by
  first | exact @GlobalTheory.QuotTransition.transition_surjective | exact GlobalTheory.QuotTransition.transition_surjective | (intros; apply GlobalTheory.QuotTransition.transition_surjective <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientPDivGroupClosedSubgroupPTorsion

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.HTPair

namespace GlobalTheory.QuotField

variable {p : ℕ} {O : Type} [CommRing O] (G : PDivGroup p O)

def levelRes (m : ℕ) : G.A (m + 1) →ₐc[O] G.A 1 :=
  Nat.rec (motive := fun m => G.A (m + 1) →ₐc[O] G.A 1) (BialgHom.id O _)
    (fun m f => f.comp (G.res (m + 1))) m

theorem levelRes_surjective (m : ℕ) : Function.Surjective (levelRes G m) := by
  induction m with
  | zero => exact Function.surjective_id
  | succ m ih =>
    intro c
    obtain ⟨a, rfl⟩ := ih c
    obtain ⟨b, rfl⟩ := G.res_surjective (m + 1) a
    exact ⟨b, rfl⟩

theorem ker_succ {C : Type} [CommRing C] [Bialgebra O C] (π : G.A 1 →ₐc[O] C) (m : ℕ) :
    RingHom.ker (π.comp (levelRes G (m + 1))) =
      Ideal.comap (G.res (m + 1) : G.A (m + 2) →ₐ[O] G.A (m + 1))
        (RingHom.ker (π.comp (levelRes G m))) :=
  Ideal.ext fun _ => Iff.rfl

theorem torsion_le {C : Type} [CommRing C] [Bialgebra O C] (π : G.A 1 →ₐc[O] C) (m : ℕ) :
    torsionIdeal (R := O) (A := G.A (m + 1)) p ≤ RingHom.ker (π.comp (levelRes G m)) := by
  refine (kerIdeal_le_ker_iff _
    ((π.comp (levelRes G m) : G.A (m + 1) →ₐc[O] C) : G.A (m + 1) →ₐ[O] C)).2 fun c => ?_
  change π (levelRes G m (mulBy (R := O) (A := G.A (m + 1)) p c)) = _
  have h := G.mulBy_pow_self 1 (levelRes G m c)
  rw [pow_one] at h
  rw [map_mulBy, h, AlgHomClass.commutes, CoalgHomClass.counit_comp_apply]

end GlobalTheory.QuotField


open GlobalTheory.QuotField GlobalTheory.HTPair.QuotIsog in
theorem GlobalTheory.HTPair.exists_quot_field : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    (G : PDivGroup p k) (C : Type) [CommRing C] [HopfAlgebra k C] [IsCocomm k C]
    [Module.Finite k C] (π : G.A 1 →ₐc[k] C), Function.Surjective π →
    ∃ (Q : PDivGroup p k) (q : G ⟶ Q) (q' : Q ⟶ G), q ≫ q' = (p : ℤ_[p]) • 𝟙 G ∧
      q' ≫ q = (p : ℤ_[p]) • 𝟙 Q ∧ kerIdeal (q.app 1) = RingHom.ker π := by
  intro p _ k _ _ G C _ _ _ _ π hπ
  have hsurj : ∀ m, Function.Surjective (π.comp (levelRes G m)) := fun m =>
    hπ.comp (levelRes_surjective G m)
  choose B iR iH iC iF j hinj hker huniv using
    fun m => GlobalTheory.T.exists_quotient_finiteCommGroupScheme_closedSubgroup k (G.A (m + 1)) C (π.comp (levelRes G m)) (hsurj m)
  letI := iR
  letI := iH
  letI := iC
  letI := iF
  have hρ : ∀ m, ∃ ρ : G.A (m + 1) →ₗ[k] B m, ∀ b, ρ (j m b) = b := fun m => by
    obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective
      ((j m : B m →ₐ[k] G.A (m + 1)).toLinearMap) (LinearMap.ker_eq_bot.2 (hinj m))
    exact ⟨g, fun b => LinearMap.congr_fun hg b⟩
  choose ρ hρ using hρ
  have hfac : ∀ m (D : Type) [CommRing D] [Bialgebra k D] (f : D →ₐc[k] G.A (m + 1)),
      kerIdeal f ≤ RingHom.ker (π.comp (levelRes G m)) →
        ∃ g : D →ₐc[k] B m, ∀ d, j m (g d) = f d := fun m D _ _ f hf =>
    GlobalTheory.T.bialgHom_factor_through_split_injection k (G.A (m + 1)) (B m) D (j m) (ρ m) f (hρ m) (huniv m D f hf)
  choose r hr using fun m => hfac m (B (m + 1)) ((G.res (m + 1)).comp (j (m + 1))) (by
    rw [kerIdeal_comp, hker (m + 1), ker_succ]
    exact Ideal.map_comap_le)
  choose s hs using fun m => hfac m (G.A m) (G.mulP m) (by
    rw [← kerIdeal_comp_of_surjective _ (G.res_surjective m), G.mulP_comp_res]
    exact torsion_le G π m)
  have hkr : ∀ m, kerIdeal (j m) =
      Ideal.map (G.res (m + 1) : G.A (m + 2) →ₐ[k] G.A (m + 1)) (kerIdeal (j (m + 1))) := by
    intro m
    rw [hker, hker, ker_succ]
    exact (Ideal.map_comap_of_surjective (G.res (m + 1) : G.A (m + 2) →ₐ[k] G.A (m + 1))
      (G.res_surjective (m + 1)) _).symm
  let τ : QuotTower G :=
    { B := B
      commRing := iR
      hopf := iH
      cocomm := iC
      finite := iF
      projective := fun _ => inferInstance
      j := j
      ρ := ρ
      r := r
      s := s
      ρ_j := hρ
      r_surjective := fun m => GlobalTheory.T.quotientTransition_surjective_same_subgroup k (G.A (m + 1)) (G.A (m + 2)) (B m) (B (m + 1))
        (G.res (m + 1)) (j m) (j (m + 1)) (r m) (ρ m) (hρ m) (fun b => hr m b) (hkr m)
      j_r := fun m b => hr m b
      j_s := hs
      tors_le := fun m => (hker m).symm ▸ torsion_le G π m }
  obtain ⟨H, q, hqs, hqk, hqc⟩ := GlobalTheory.HTPair.exists_quotPDivGroup p k G τ
  refine ⟨H, toQuot τ q hqs hqk hqc, fromQuot τ q hqc, ?_, ?_, ?_⟩
  · refine PDivGroup.Hom.ext (funext fun n => ?_)
    rw [natCast_smul_id_app, comp_app]
    refine BialgHom.ext fun a => ?_
    change (toQuot τ q hqs hqk hqc).app n (q n (τ.s n a)) = _
    rw [toQuot_app_q, τ.j_s, G.res_mulP]
  · refine PDivGroup.Hom.ext (funext fun n => ?_)
    rw [natCast_smul_id_app, comp_app]
    refine BialgHom.ext fun c => ?_
    obtain ⟨b, rfl⟩ := hqs n c
    change q n (τ.s n ((toQuot τ q hqs hqk hqc).app n (q n b))) = _
    rw [toQuot_app_q, s_res_j, map_mulBy]
  · have h1 : ((toQuot τ q hqs hqk hqc).app 1).comp (q 1) = (G.res 1).comp (τ.j 1) :=
      BialgHom.ext fun b => toQuot_app_q τ q hqs hqk hqc 1 b
    rw [← kerIdeal_comp_of_surjective _ (hqs 1), h1, kerIdeal_comp]
    exact (τ.map_res_kerIdeal 0).trans ((hker 0).trans (Ideal.ext fun _ => Iff.rfl))
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientPDivGroupClosedSubgroupPTorsionStatement

section

@[expose] public section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

theorem _root_.GlobalTheory.T.exists_quotient_pDivGroup_closedSubgroup_pTorsion : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (G : PDivGroup p k) (C : Type) [CommRing C] [HopfAlgebra k C] [IsCocomm k C] [Module.Finite k C] (π : G.A 1 →ₐc[k] C), Function.Surjective π → ∃ (Q : PDivGroup p k) (q : G ⟶ Q) (q' : Q ⟶ G), q ≫ q' = (p : ℤ_[p]) • 𝟙 G ∧ q' ≫ q = (p : ℤ_[p]) • 𝟙 Q ∧ kerIdeal (q.app 1) = RingHom.ker π := by
  first | exact @GlobalTheory.HTPair.exists_quot_field | exact GlobalTheory.HTPair.exists_quot_field | (intros; apply GlobalTheory.HTPair.exists_quot_field <;> assumption)
end
end
