module

public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseDefs
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseFormal
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseInv
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseLocal
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
import Mathlib.Tactic.TypeStar
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseReverse
import Mathlib.Topology.Sheaves.Init

-- Source module: GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseLocalDual

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open IsDedekindDomain NumberField CategoryTheory MonoidalCategory GroundTheory.Global

noncomputable section

attribute [local instance 2000] Rep.hV2

section CompLinear

variable {n : ℕ} {R : Type*} [CommRing R]

theorem bijective_of_bijective_comp_linear {X X' Y Y' : Type*} {_ : AddCommGroup Y} {_ : AddCommGroup Y'}
    {_ : Module R Y} {_ : Module R Y'} {F : X → (Y →+ ZMod n)} (hF : Function.Bijective F) {α : X' → X}
    (hα : Function.Bijective α) {γ : Y' →ₗ[R] Y} (hγ : Function.Bijective γ) {F' : X' → (Y' →+ ZMod n)}
    (hF' : ∀ x' y', F' x' y' = F (α x') (γ y')) : Function.Bijective F' :=
  bijective_of_bijective_comp hF hα (γ := γ.toAddMonoidHom) hγ hF'

theorem neg_apply_bilin_eq {X X₀ Y Z : Type*} [AddCommGroup X] [AddCommGroup X₀] [AddCommGroup Y] [AddCommGroup Z]
    {_ : Module R X} {_ : Module R Y} {_ : Module R Z} {_ : Module R X₀} (t : Z →+ ZMod n)
    (B : X →ₗ[R] Y →ₗ[R] Z) (f : X₀ →ₗ[R] X) (x : X₀) (y : Y) :
    -t (B (f x) y) = (t.comp (bilinAddHom B (f (-x)))) y := by
  rw [AddMonoidHom.comp_apply, bilinAddHom_apply, map_neg, map_neg, LinearMap.neg_apply, map_neg]

end CompLinear

section LocalZMod

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  [TotallyDisconnectedSpace H] {m : ℕ} [NeZero m] {Dl : Rep.{0} (ULift.{0} ℤ) H} [IsDiscreteRep Dl]
  (Hd : DualityHypotheses m Dl) (hDl : ∀ d : Dl, m • d = 0)

theorem bijective_zmodMulPairing_tTop {r s : ℕ} (h : r + s = 2) :
    Function.Bijective fun x : cohomology (zmodRep.{0} H m) r =>
      Hd.tTop.comp (bilinAddHom (cupPairing (zmodMulPairing m Dl hDl) h) x) := by
  have hM : ∀ a : zmodRep.{0} H m, m • a = 0 := nsmul_zmodRep_eq_zero H m
  have : Finite (zmodRep.{0} H m) := inferInstanceAs (Finite (ULift.{0} (ZMod m)))
  have : IsDiscreteRep (dualRep Dl (zmodRep.{0} H m)) := isDiscreteRep_dualRep _ _
  refine bijective_of_bijective_comp (Hd.bijective_dualityMap_of_group (zmodRep.{0} H m) hM h)
    Function.bijective_id (γ := (cohomologyMap (zmodDualIso m Dl hDl).inv s).hom.toAddMonoidHom)
    (bijective_cohomologyMap_of_comp_eq_id _ _ (zmodDualIso m Dl hDl).inv_hom_id
      (zmodDualIso m Dl hDl).hom_inv_id s) fun x ω => ?_
  change Hd.tTop (cupPairing (zmodMulPairing m Dl hDl) h x ω) =
    Hd.tTop (cupPairing (evalPairing Dl (zmodRep.{0} H m)) h x ((cohomologyMap (zmodDualIso m Dl hDl).inv s).hom ω))
  congr 1
  have e := cupPairing_cohomologyMap (evalPairing Dl (zmodRep.{0} H m)) (𝟙 _) (zmodDualIso m Dl hDl).inv h x ω
  rw [cohomologyMap_id] at e
  refine Eq.trans ?_ e.symm
  rw [← tensorHom_zmodDualIso_zmodMulPairing m Dl hDl, ← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom,
    Category.id_comp, Iso.inv_hom_id, MonoidalCategory.id_tensorHom_id, Category.id_comp]


omit [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H] [TotallyDisconnectedSpace H] [IsDiscreteRep Dl]
  [NeZero m] in
theorem comp_eq_tensorHom_zmodMulPairing {M Dm : Rep.{0} (ULift.{0} ℤ) H} (μ : M ⊗ Dm ⟶ Dm) (ρ : Dm ⟶ Dl)
    (ι : M ⟶ zmodRep.{0} H m)
    (hμ : ∀ (a : M) (d : Dm), μ.hom (a ⊗ₜ[ULift.{0} ℤ] d) = (ZMod.cast (ι.hom a).down : ℤ) • d) :
    μ ≫ ρ = (ι ⊗ₘ ρ) ≫ zmodMulPairing m Dl hDl := by
  refine Rep.hom_ext (Representation.IntertwiningMap.ext (TensorProduct.ext' fun a d => ?_))
  change ρ.hom (μ.hom (a ⊗ₜ[ULift.{0} ℤ] d)) = (zmodMulPairing m Dl hDl).hom (ι.hom a ⊗ₜ[ULift.{0} ℤ] ρ.hom d)
  rw [hμ, map_zsmul]
  obtain ⟨b⟩ := ι.hom a
  rw [zmodMulPairing_tmul]


omit [CompactSpace H] [TotallyDisconnectedSpace H] [NeZero m] in
theorem cohomologyMap_cupPairing_of_comp_eq {M Dm M' : Rep.{0} (ULift.{0} ℤ) H} [IsDiscreteRep M]
    [IsDiscreteRep Dm] [IsDiscreteRep M'] (μ : M ⊗ Dm ⟶ Dm) (μ' : M' ⊗ Dl ⟶ Dl) (ρ : Dm ⟶ Dl) (ι : M ⟶ M')
    (hμ : μ ≫ ρ = (ι ⊗ₘ ρ) ≫ μ') {r s q : ℕ} (h : r + s = q) (x : cohomology M r) (y : cohomology Dm s) :
    (cohomologyMap ρ q).hom (cupPairing μ h x y) =
      cupPairing μ' h ((cohomologyMap ι r).hom x) ((cohomologyMap ρ s).hom y) := by
  rw [cupPairing_cohomologyMap, ← hμ, ← cohomologyMap_cupPairing]

end LocalZMod

local notation "ℚ̄" => AlgebraicClosure ℚ

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) (n : ℕ)
  [NeZero n]


omit [NeZero n] in
theorem nsmul_galRootsOfUnity_local (v : S)
    (ω : galRootsOfUnity.{0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
      (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n) : n • ω = 0 := by
  apply Additive.toMul.injective
  apply Subtype.ext
  change ((Additive.toMul ω : rootsOfUnity n
    (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))) :
      (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))ˣ) ^ n = 1
  exact (mem_rootsOfUnity n _).1 (Additive.toMul ω).2

def zmodResToLocal (v : S) :
    Rep.res (gsFinFamily S ιs v).toMonoidHom (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) ⟶
      zmodRep.{0} (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) ≃ₐ[
        (v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1]
          AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

omit [NeZero n] in
theorem bijective_zmodResToLocal (v : S) : Function.Bijective (zmodResToLocal S ιs n v).hom :=
  Function.bijective_id


omit [NeZero n] in
theorem pairingRes_zmodMulPairing_comp_gsRootsLocalMor (v : S) :
    pairingRes (gsFinFamily S ιs v).toMonoidHom (zmodMulPairing n (gsRoots S n) (nsmul_gsRoots S n)) ≫
        gsRootsLocalMor S ιs n v =
      (zmodResToLocal S ιs n v ⊗ₘ gsRootsLocalMor S ιs n v) ≫
        zmodMulPairing n (galRootsOfUnity.{0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
          (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n) (nsmul_galRootsOfUnity_local S n v) := by
  refine comp_eq_tensorHom_zmodMulPairing (nsmul_galRootsOfUnity_local S n v) _ _ _ fun a d => ?_
  obtain ⟨a⟩ := a
  exact zmodMulPairing_tmul n (gsRoots S n) (nsmul_gsRoots S n) a d



theorem gsLocalInvRoots_cupPairing (v : S) {r s : ℕ} (h : r + s = 2)
    (ξ : cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n)) r)
    (η : cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) s) :
    gsLocalInvRoots S ιs n v (cupPairing (pairingRes (gsFinFamily S ιs v).toMonoidHom
        (zmodMulPairing n (gsRoots S n) (nsmul_gsRoots S n))) h ξ η) =
      (localDualityHypotheses (Ksep := AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
        (natCast_ne_zero_adicCompletion S n v)).tTop
        (cupPairing (zmodMulPairing n (galRootsOfUnity.{0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
          (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n) (nsmul_galRootsOfUnity_local S n v)) h
          ((cohomologyMap (zmodResToLocal S ιs n v) r).hom ξ) ((cohomologyMap (gsRootsLocalMor S ιs n v) s).hom η)) := by
  refine (gsLocalInvRoots_eq S ιs n v _).trans (congrArg
    (localDualityHypotheses (Ksep := AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
      (natCast_ne_zero_adicCompletion S n v)).tTop ?_)
  exact cohomologyMap_cupPairing_of_comp_eq _ _ _ _
    (pairingRes_zmodMulPairing_comp_gsRootsLocalMor S ιs n v) h ξ η

variable (hμ : ∀ ζ : ℚ̄, ζ ^ n = 1 → ζ ∈ K.1)
include hμ

theorem bijective_gsLocalPairing_two (v : S) :
    Function.Bijective fun ξ : cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom
        (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n)) 2 =>
      (gsLocalInvRoots S ιs n v).comp ((bilinAddHom (cupPairing (pairingRes (gsFinFamily S ιs v).toMonoidHom
        (zmodMulPairingRight n (gsRoots S n) (nsmul_gsRoots S n))) (show 0 + 2 = 2 from rfl))).flip ξ) := by
  refine bijective_of_bijective_comp_linear (bijective_zmodMulPairing_tTop
    (localDualityHypotheses (Ksep := AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
      (natCast_ne_zero_adicCompletion S n v)) (nsmul_galRootsOfUnity_local S n v) (show 2 + 0 = 2 from rfl))
    (bijective_cohomologyMap_of_bijective _ (bijective_zmodResToLocal S ιs n v) 2)
    (γ := (cohomologyMap (gsRootsLocalMor S ιs n v) 0).hom)
    (bijective_cohomologyMap_of_bijective _ (bijective_gsRootsLocalMor S ιs n hμ v) 0) fun ξ η => ?_
  change gsLocalInvRoots S ιs n v (cupPairing (pairingRes (gsFinFamily S ιs v).toMonoidHom
    (zmodMulPairingRight n (gsRoots S n) (nsmul_gsRoots S n))) (show 0 + 2 = 2 from rfl) η ξ) = _
  refine (congrArg (gsLocalInvRoots S ιs n v) (cupPairing_pairingRes_zmodMulPairing_two_zero
    (gsFinFamily S ιs v).toMonoidHom (gsRoots S n) (nsmul_gsRoots S n) (show 2 + 0 = 2 from rfl)
    (show 0 + 2 = 2 from rfl) ξ η).symm).trans ?_
  exact gsLocalInvRoots_cupPairing S ιs n v _ ξ η

theorem bijective_gsLocalPairing_one (v : S) :
    Function.Bijective fun ξ : cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom
        (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n)) 1 =>
      (gsLocalInvRoots S ιs n v).comp ((bilinAddHom (cupPairing (pairingRes (gsFinFamily S ιs v).toMonoidHom
        (zmodMulPairingRight n (gsRoots S n) (nsmul_gsRoots S n))) (show 1 + 1 = 2 from rfl))).flip ξ) := by
  refine bijective_of_bijective_comp_linear (bijective_zmodMulPairing_tTop
    (localDualityHypotheses (Ksep := AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
      (natCast_ne_zero_adicCompletion S n v)) (nsmul_galRootsOfUnity_local S n v) (show 1 + 1 = 2 from rfl))
    ((bijective_cohomologyMap_of_bijective _ (bijective_zmodResToLocal S ιs n v) 1).comp neg_bijective)
    (γ := (cohomologyMap (gsRootsLocalMor S ιs n v) 1).hom)
    (bijective_cohomologyMap_of_bijective _ (bijective_gsRootsLocalMor S ιs n hμ v) 1) fun ξ η => ?_
  change gsLocalInvRoots S ιs n v (cupPairing (pairingRes (gsFinFamily S ιs v).toMonoidHom
    (zmodMulPairingRight n (gsRoots S n) (nsmul_gsRoots S n))) (show 1 + 1 = 2 from rfl) η ξ) = _
  have e := cupPairing_pairingRes_zmodMulPairing_one (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)
    (nsmul_gsRoots S n) (show 1 + 1 = 2 from rfl) ξ η
  refine (congrArg (gsLocalInvRoots S ιs n v) (neg_eq_iff_eq_neg.2 e).symm).trans ?_
  refine (map_neg _ _).trans ?_
  refine (congrArg Neg.neg (gsLocalInvRoots_cupPairing S ιs n v _ ξ η)).trans ?_
  exact neg_apply_bilin_eq _ _ _ _ _

end

end GroundTheory.ProfCoh
end
end

-- Source module: GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseSwap

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory

universe u

attribute [local instance 2000] Rep.hV2

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {n : ℕ} (D : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep D] (hD : ∀ d : D, n • d = 0)

theorem neg_one_pow_one_mul_two_smul {R M : Type*} [Ring R] {_ : AddCommGroup M} {_ : Module R M} (x : M) :
    ((-1 : R) ^ (1 * 2)) • x = x := by
  rw [show (1 * 2 : ℕ) = 2 from rfl, neg_one_sq, one_smul]

omit [TopologicalSpace G] [IsTopologicalGroup G] [IsDiscreteRep D] in
theorem braiding_comp_zmodMulPairingRight :
    (β_ (zmodRep.{u} G n) D).hom ≫ zmodMulPairingRight n D hD = zmodMulPairing n D hD := by
  rw [zmodMulPairingRight, ← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]

theorem compactCupRes_zmodMulPairingRight_swap
    (hsurj : Function.Surjective
      (localToCompact φ D (fun v => Rep.res (φ v).toMonoidHom D) (fun _ => 𝟙 _) 2).hom)
    (yc : compactCohomologyRes φ D 1) (xc : compactCohomologyRes φ (zmodRep.{u} G n) 2) :
    compactCupRes φ (zmodMulPairingRight n D hD) (show 1 + 2 = 3 from rfl) yc
        ((compactToGlobal φ _ (fun v => Rep.res (φ v).toMonoidHom (zmodRep.{u} G n)) (fun _ => 𝟙 _) 2).hom xc) =
      compactCupRes φ (zmodMulPairing n D hD) (show 2 + 1 = 3 from rfl) xc
        ((compactToGlobal φ D (fun v => Rep.res (φ v).toMonoidHom D) (fun _ => 𝟙 _) 1).hom yc) := by
  refine (compactCupRes_eq_neg_one_pow_smul_compactCupRightRes φ (zmodMulPairingRight n D hD) hsurj
    (show 1 + 2 = 3 from rfl) (show 2 + 1 = 3 from rfl) le_rfl (by norm_num) yc _).trans ?_
  refine (neg_one_pow_one_mul_two_smul _).trans ?_
  refine (congrArg (fun μ => compactCupRightRes φ μ (show 2 + 1 = 3 from rfl)
    ((compactToGlobal φ _ (fun v => Rep.res (φ v).toMonoidHom (zmodRep.{u} G n)) (fun _ => 𝟙 _) 2).hom xc) yc)
    (braiding_comp_zmodMulPairingRight D hD)).trans ?_
  exact (compactCup_eq_compactCupRight (Aᵥ := fun v => Rep.res (φ v).toMonoidHom (zmodRep.{u} G n))
    (Bᵥ := fun v => Rep.res (φ v).toMonoidHom D) (Cᵥ := fun v => Rep.res (φ v).toMonoidHom D)
    (a := fun _ => 𝟙 _) (b := fun _ => 𝟙 _) (c := fun _ => 𝟙 _) φ (zmodMulPairing n D hD)
    (fun v => pairingRes (φ v).toMonoidHom (zmodMulPairing n D hD))
    (fun v => pairingRes (φ v).toMonoidHom (zmodMulPairing n D hD))
    (fun v => pairingRes (φ v).toMonoidHom (zmodMulPairing n D hD))
    (fun v => resFunctor_map_comp_id (φ v).toMonoidHom (zmodMulPairing n D hD))
    (fun v => resFunctor_map_comp_id (φ v).toMonoidHom (zmodMulPairing n D hD))
    (fun _ => by rw [MonoidalCategory.id_tensorHom_id, Category.id_comp])
    (fun _ => by rw [MonoidalCategory.id_tensorHom_id, Category.id_comp])
    (show 2 + 1 = 3 from rfl) xc yc).symm

end GroundTheory.ProfCoh
end
end

-- Source module: GroundTheory.ProfiniteCohomology.RestrictedRamification.BijectiveGsCompactZmodDualityMap

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open IsDedekindDomain NumberField CategoryTheory GroundTheory.Global

noncomputable section

local notation "ℚ̄" => AlgebraicClosure ℚ

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1))) [Fintype S] [Nonempty S]
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
  (n : ℕ) [NeZero n] (ℓ k : ℕ) (hℓ : ℓ.Prime) (hnk : n = ℓ ^ k)
  (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
  (hμ : ∀ ζ : ℚ̄, ζ ^ n = 1 → ζ ∈ K.1) (hodd : Odd n ∨ IsTotallyComplex K.1)
  (h3 : Subsingleton (cohomology (gsRoots S n) 3))


include ℓ k hℓ hnk hS hμ in
theorem BaseDualityHypotheses.of_gs
    (h3Z : Subsingleton (cohomology (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 3))
    (hfin1 : Finite (cohomology (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1))
    (hfin2 : Finite (compactCohomologyRes (gsFinFamily S ιs) (gsRoots S n) 2))
    (hleft : ∀ x : cohomology (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1,
      (∀ y : compactCohomologyRes (gsFinFamily S ιs) (gsRoots S n) 2,
        gsCompactInv S ιs n hodd h3 (compactCupRes (gsFinFamily S ιs) (zmodMulPairingRight n (gsRoots S n)
          (nsmul_gsRoots S n)) (show 2 + 1 = 3 from rfl) y x) = 0) → x = 0)
    (hright : ∀ y : compactCohomologyRes (gsFinFamily S ιs) (gsRoots S n) 2,
      (∀ x : cohomology (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1,
        gsCompactInv S ιs n hodd h3 (compactCupRes (gsFinFamily S ιs) (zmodMulPairingRight n (gsRoots S n)
          (nsmul_gsRoots S n)) (show 2 + 1 = 3 from rfl) y x) = 0) → y = 0) :
    BaseDualityHypotheses (gsFinFamily S ιs) (gsRoots S n) (nsmul_gsRoots S n) (gsLocalInvRoots S ιs n)
      (gsCompactInv S ιs n hodd h3) := by
  exact
    { triv := gsRoots_ρ_apply_of_mem S n hμ
      nonempty_addEquiv := nonempty_addEquiv_gsRoots S n hμ
      loc_one v := (bijective_gsLocalPairing_one S ιs n hμ v).2
      loc_two v := bijective_gsLocalPairing_two S ιs n hμ v
      bijective_alt := bijective_gsCompactInv_of_mem S n ιs ℓ k hℓ hnk hS hμ hodd h3
      T_localToCompact := gsCompactInv_localToCompact S ιs n hodd h3
      three_zmod := h3Z
      three_D := h3
      finite_one := hfin1
      finite_two := hfin2
      ker_left := hleft
      ker_right := hright
      swap yc xc := congrArg (gsCompactInv S ιs n hodd h3)
        (compactCupRes_zmodMulPairingRight_swap (gsFinFamily S ιs) (gsRoots S n) (nsmul_gsRoots S n)
          (_root_.GroundTheory.ProfCoh.localToCompact_two_surjective S ιs n h3) yc xc) }


include ℓ k hℓ hnk hS hμ in
theorem bijective_gs_compactZmodDualityMap
    (h3Z : Subsingleton (cohomology (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 3))
    (hfin1 : Finite (cohomology (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1))
    (hfin2 : Finite (compactCohomologyRes (gsFinFamily S ιs) (gsRoots S n) 2))
    (hleft : ∀ x : cohomology (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1,
      (∀ y : compactCohomologyRes (gsFinFamily S ιs) (gsRoots S n) 2,
        gsCompactInv S ιs n hodd h3 (compactCupRes (gsFinFamily S ιs) (zmodMulPairingRight n (gsRoots S n)
          (nsmul_gsRoots S n)) (show 2 + 1 = 3 from rfl) y x) = 0) → x = 0)
    (hright : ∀ y : compactCohomologyRes (gsFinFamily S ιs) (gsRoots S n) 2,
      (∀ x : cohomology (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1,
        gsCompactInv S ιs n hodd h3 (compactCupRes (gsFinFamily S ιs) (zmodMulPairingRight n (gsRoots S n)
          (nsmul_gsRoots S n)) (show 2 + 1 = 3 from rfl) y x) = 0) → y = 0)
    {r s : ℕ} (h : r + s = 3) :
    Function.Bijective (compactZmodDualityMap (gsFinFamily S ιs) (gsRoots S n) (nsmul_gsRoots S n)
      (gsCompactInv S ιs n hodd h3) h) :=
  (BaseDualityHypotheses.of_gs S ιs n ℓ k hℓ hnk hS hμ hodd h3 h3Z hfin1 hfin2 hleft hright).bijective_compactZmodDualityMap h

end

end GroundTheory.ProfCoh
end
end
